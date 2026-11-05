import RBM8D.SelfEnergy.VR1Graph

/-!
# [I, Lemma 8.5]: the row sums of the self-energies on the torus against `ℤ^d`

* `VR1.v2`: [I, (8.10)], `|Σ_x Σ^{(r)}_n(0, x)(z) − Σ'_v Σ^{(r),∞}_n(v)(E)| ≤ L^τ η W^{-(n-2)d/2}`,
  on the whole domain `𝐃(κ, ε)` and uniformly in `|E| < 2 − κ`, `E = Re z`.

The file also contains the comparison of the chains of labelled `Θ` edges on the torus with their
values on `ℤ^d` used for it: the chain comparison uses a cut `R = ⌊L/(12(k+1))⌋` of all factors:
the factors `Σ̊_{oᵢ}` of the torus are cut at `R` (beyond `R`,
`|Σ̊_{oᵢ}| ≤ η W^σ W^{-(oᵢ-2)d/2} W ⟨·⟩^{-(d+1)}`), the factors `Θ` are cut at `R` (their tails
beyond the range `η^{-1/2} W^{1+τ}` are `⟨·⟩^{-D}`); the product of the cut factors is the
convolution on `ℤ^d` of their lifts; on `ℤ^d` the lifted factors are compared with `Θ_∞` and
`Σ̊^∞_{oᵢ}`, the difference of a `Θ` factor next to a product `Θ Σ̊`, the difference of a `Σ̊`
factor between two chains.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

open private sum_wt_le sum_wt_sub_le sumC sumC_nonneg rpow_mul_rpow_le zdInf_le_sub convZ_assoc
  summable_triple chain_step mem_boxZ_iff exists_W0_list from RBM8D.Bound.ChainInf
open private VR1Graph_zcast_add VR1Graph_zcast_neg VR1Graph_zcast_sub VR1Graph_zcast_zero
  VR1Graph_zcast_zlift VR1Graph_zlift_zcast VR1Graph_zdInf_zlift VR1Graph_zlift_zero
  from RBM8D.SelfEnergy.VR1Graph
open private Chain_sumAll Chain_brk_tri Chain_brk_pos Chain_le_brk Chain_brk_comm Chain_sumLe
  Chain_tailSum Chain_bB_eq Chain_bB_sq Chain_brk_le Chain_Theta_translate from RBM8D.Bound.Chain
open private RenormDiff_W_of_L RenormDiff_chainDiff RenormDiff_chain_cons RenormDiff_foldl
  RenormDiff_ord_cons RenormDiff_telescope RenormDiff_term_eq RenormDiff_val_theta
  RenormDiff_val_dotc
  RenormDiff_val_xdotLoop RenormDiff_val_ne RenormDiff_val_diag RenormDiff_detKind
  RenormDiff_sigMat_rec RenormDiff_brk_pos
  from RBM8D.SelfEnergy.RenormDiff
open private VR1Graph_adm VR1Graph_eta_ge VR1Graph_cut_small VR1Graph_R_ge VR1Graph_chainZ_bound
  VR1Graph_infKernel_mono VR1Graph_symbolClose_mono VR1Graph_brk_zlift VR1Graph_wT VR1Graph_wZ
  VR1Graph_wv VR1Graph_wv_eq VR1Graph_wavedZ VR1Graph_coeff VR1Graph_zlift_inj
  from RBM8D.SelfEnergy.VR1Graph
open private InfBound_term_ne InfBound_term_cons InfBound_compVal_dot InfBound_fin_zero
  from RBM8D.SelfEnergy.InfBound
open private latSum from RBM8D.Bound.AuxTreeZ
open private ValZ_uniform ValZ_shape from RBM8D.SelfEnergy.ValZ

variable {d : ℕ}

/-! ## Convolutions of power laws on `ℤ^d` and on the torus -/

section Conv

/-- **Two power laws on `ℤ^d`.** For `0 ≤ m ≤ min(u, v)` and `n = u + v − m > d`, with
`⟨z⟩ = |z|_∞ + w`, `w ≥ 1`: `α ↦ ⟨α⟩^{-u} ⟨x − α⟩^{-v}` is summable with sum at most
`2^{m+1} C_n w^{d-n} ⟨x⟩^{-m}`. -/
private theorem VR1_plsum (hd : 1 ≤ d) {w u v m : ℝ} (hw : 1 ≤ w)
    (hm : 0 ≤ m) (hmu : m ≤ u) (hmv : m ≤ v) (hn : (d : ℝ) < u + v - m) (x : Fin d → ℤ) :
    Summable (fun α : Fin d → ℤ => ((zdInf α : ℝ) + w) ^ (-u) * ((zdInf (x - α) : ℝ) + w) ^ (-v)) ∧
      ∑' α : Fin d → ℤ, ((zdInf α : ℝ) + w) ^ (-u) * ((zdInf (x - α) : ℝ) + w) ^ (-v) ≤
        (2 ^ m * (2 * (sumC d (u + v - m) * w ^ ((d : ℝ) - (u + v - m))))) *
          ((zdInf x : ℝ) + w) ^ (-m) := by
  have hw0 : 0 < w := by linarith
  set n := u + v - m with hndef
  set C₀ : ℝ := 2 ^ m * ((zdInf x : ℝ) + w) ^ (-m) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hpt : ∀ α : Fin d → ℤ, ((zdInf α : ℝ) + w) ^ (-u) * ((zdInf (x - α) : ℝ) + w) ^ (-v) ≤
      C₀ * (((zdInf α : ℝ) + w) ^ (-n) + ((zdInf (x - α) : ℝ) + w) ^ (-n)) := by
    intro α
    have hR : (zdInf x : ℝ) + w ≤ ((zdInf α : ℝ) + w) + ((zdInf (x - α) : ℝ) + w) := by
      have h := zdInf_le_sub x α
      have : (zdInf x : ℝ) ≤ zdInf α + zdInf (x - α) := by exact_mod_cast h
      linarith
    exact rpow_mul_rpow_le (u := u) (v := v) (m := m)
      (by positivity : (0 : ℝ) < (zdInf α : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf (x - α) : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf x : ℝ) + w) hR hm hmu hmv
  obtain ⟨hs1, ht1⟩ := sum_wt_le hd hn hw
  obtain ⟨hs2, ht2⟩ := sum_wt_sub_le hd hn hw x
  have hS := (hs1.add hs2).mul_left C₀
  have hnS := Summable.of_nonneg_of_le (fun α => by positivity) hpt hS
  refine ⟨hnS, ?_⟩
  calc _ ≤ ∑' α, C₀ * (((zdInf α : ℝ) + w) ^ (-n) + ((zdInf (x - α) : ℝ) + w) ^ (-n)) :=
        hnS.tsum_le_tsum hpt hS
    _ = C₀ * (∑' α, ((zdInf α : ℝ) + w) ^ (-n) + ∑' α, ((zdInf (x - α) : ℝ) + w) ^ (-n)) := by
        rw [tsum_mul_left, hs1.tsum_add hs2]
    _ ≤ C₀ * (sumC d n * w ^ ((d : ℝ) - n) + sumC d n * w ^ ((d : ℝ) - n)) := by gcongr
    _ = _ := by rw [hC₀]; ring

/-- **A power law against a power law with a point term.** If `|f(z)| ≤ c_f ⟨z⟩^{-u}` and
`|g(z)| ≤ c_g ⟨z⟩^{-v} + J 1_{z=0}`, `0 ≤ m ≤ min(u, v)` and `n = u + v − m > d`, then
`α ↦ f(α) g(x − α)` is absolutely summable and
`|(f ∗ g)(x)| ≤ c_f c_g 2^{m+1} C_n w^{d-n} ⟨x⟩^{-m} + J c_f ⟨x⟩^{-u}`. -/
private theorem VR1_conv2 (hd : 1 ≤ d) {w u v m cf cg J : ℝ} (hw : 1 ≤ w)
    (f g : (Fin d → ℤ) → ℂ) (hcf : 0 ≤ cf) (hcg : 0 ≤ cg)
    (hf : ∀ z, ‖f z‖ ≤ cf * ((zdInf z : ℝ) + w) ^ (-u))
    (hg : ∀ z, ‖g z‖ ≤ cg * ((zdInf z : ℝ) + w) ^ (-v) + (if z = 0 then J else 0))
    (hm : 0 ≤ m) (hmu : m ≤ u) (hmv : m ≤ v) (hn : (d : ℝ) < u + v - m) (x : Fin d → ℤ) :
    Summable (fun α => ‖f α * g (x - α)‖) ∧
      ‖convZ f g x‖ ≤ cf * cg * (2 ^ m * (2 * (sumC d (u + v - m) *
        w ^ ((d : ℝ) - (u + v - m))))) * ((zdInf x : ℝ) + w) ^ (-m) +
        J * (cf * ((zdInf x : ℝ) + w) ^ (-u)) := by
  classical
  have hw0 : 0 < w := by linarith
  obtain ⟨hs, ht⟩ := VR1_plsum hd hw hm hmu hmv hn x
  set G : (Fin d → ℤ) → ℝ := fun α =>
    cf * cg * (((zdInf α : ℝ) + w) ^ (-u) * ((zdInf (x - α) : ℝ) + w) ^ (-v)) +
      (if α = x then J * (cf * ((zdInf x : ℝ) + w) ^ (-u)) else 0) with hG
  have hpt : ∀ α, ‖f α * g (x - α)‖ ≤ G α := by
    intro α
    rw [norm_mul]
    have h1 := hf α
    have h2 := hg (x - α)
    have hfa : 0 ≤ cf * ((zdInf α : ℝ) + w) ^ (-u) := by positivity
    calc ‖f α‖ * ‖g (x - α)‖ ≤ (cf * ((zdInf α : ℝ) + w) ^ (-u)) *
          (cg * ((zdInf (x - α) : ℝ) + w) ^ (-v) + (if x - α = 0 then J else 0)) :=
          mul_le_mul h1 h2 (norm_nonneg _) hfa
      _ = G α := by
          simp only [hG, sub_eq_zero, eq_comm (a := x)]
          split_ifs with h
          · subst h; ring
          · ring
  have hGs : Summable G :=
    (hs.mul_left (cf * cg)).add (summable_of_ne_finset_zero (s := {x}) fun α hα => by
      rw [Finset.mem_singleton] at hα; simp [hα])
  have hnS := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hGs
  refine ⟨hnS, ?_⟩
  calc ‖convZ f g x‖ = ‖∑' α, f α * g (x - α)‖ := rfl
    _ ≤ ∑' α, ‖f α * g (x - α)‖ := norm_tsum_le_tsum_norm hnS
    _ ≤ ∑' α, G α := hnS.tsum_le_tsum hpt hGs
    _ = cf * cg * ∑' α : Fin d → ℤ, ((zdInf α : ℝ) + w) ^ (-u) * ((zdInf (x - α) : ℝ) + w) ^ (-v) +
          J * (cf * ((zdInf x : ℝ) + w) ^ (-u)) := by
        rw [hG, (hs.mul_left _).tsum_add (summable_of_ne_finset_zero (s := {x}) fun α hα => by
          rw [Finset.mem_singleton] at hα; simp [hα]), tsum_mul_left, tsum_ite_eq]
    _ ≤ _ := by
        rw [mul_assoc (cf * cg) (2 ^ m * _)]
        exact add_le_add_left (mul_le_mul_of_nonneg_left ht (by positivity)) _

/-- A pure power-law bound in the form with a point term `0`. -/
private theorem VR1_pl0 {w c v : ℝ} {g : (Fin d → ℤ) → ℂ}
    (hg : ∀ z, ‖g z‖ ≤ c * ((zdInf z : ℝ) + w) ^ (-v)) :
    ∀ z, ‖g z‖ ≤ c * ((zdInf z : ℝ) + w) ^ (-v) + (if z = 0 then (0 : ℝ) else 0) := fun z => by
  rw [ite_self, add_zero]; exact hg z

/-- A convolution of two power laws with exponents of sum `> d` is summable. -/
private theorem VR1_summable_conv (hd : 1 ≤ d) {w u v cf cg : ℝ} (hw : 1 ≤ w)
    (f g : (Fin d → ℤ) → ℂ) (hcf : 0 ≤ cf) (hcg : 0 ≤ cg)
    (hf : ∀ z, ‖f z‖ ≤ cf * ((zdInf z : ℝ) + w) ^ (-u))
    (hg : ∀ z, ‖g z‖ ≤ cg * ((zdInf z : ℝ) + w) ^ (-v)) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : (d : ℝ) < u + v) (x : Fin d → ℤ) : Summable (fun α => f α * g (x - α)) := by
  exact Summable.of_norm (VR1_conv2 (J := 0) hd hw f g hcf hcg hf (VR1_pl0 hg) le_rfl hu hv
    (by linarith) x).1

/-- The constant `2^{m+1} C_n w^{d-n}`, `n = u + v − m`, of `VR1_conv2`. -/
private def VR1_K (d : ℕ) (w u v m : ℝ) : ℝ :=
  2 ^ m * (2 * (sumC d (u + v - m) * w ^ ((d : ℝ) - (u + v - m))))

private theorem VR1_K_nonneg {w u v m : ℝ} (hw : 0 ≤ w) (hn : (d : ℝ) < u + v - m) :
    0 ≤ VR1_K d w u v m := by
  have := sumC_nonneg d hn
  unfold VR1_K; positivity

/-- A power law with a point term at `0` is a power law: `c ⟨z⟩^{-Q} + J 1_{z=0} ≤
(c + J w^Q) ⟨z⟩^{-Q}`. -/
private theorem VR1_point_le {w c J Q : ℝ} (hw : 1 ≤ w) (hJ : 0 ≤ J) (z : Fin d → ℤ) :
    c * ((zdInf z : ℝ) + w) ^ (-Q) + (if z = 0 then J else 0) ≤
      (c + J * w ^ Q) * ((zdInf z : ℝ) + w) ^ (-Q) := by
  have hw0 : 0 < w := by linarith
  have hb : 0 < (zdInf z : ℝ) + w := by positivity
  split_ifs with h
  · subst h
    have : (zdInf (0 : Fin d → ℤ) : ℝ) = 0 := by simp [zdInf]
    rw [this, zero_add, add_mul, mul_assoc J, ← Real.rpow_add hw0, add_neg_cancel, Real.rpow_zero,
      mul_one]
  · have : 0 ≤ J * w ^ Q * ((zdInf z : ℝ) + w) ^ (-Q) := by positivity
    nlinarith

/-- `⟨z⟩^{-a} ≤ ⟨z⟩^{-b}` for `b ≤ a`, `⟨z⟩ ≥ 1`. -/
private theorem VR1_br_anti {w a b : ℝ} (hw : 1 ≤ w) (hab : b ≤ a) (z : Fin d → ℤ) :
    ((zdInf z : ℝ) + w) ^ (-a) ≤ ((zdInf z : ℝ) + w) ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf z)])
    (by linarith)

/-- **One step of the chain comparison on `ℤ^d`.** Let `X ≈ Y` be two chains, `X' = (X ∗ t) ∗ θ`
and `Y' = (Y ∗ T) ∗ Θ`, with power-law bounds (`⟨α⟩ = |α|_∞ + w`, `0 < δ ≤ 1/8`, `d ≥ 8`):
`|X| ≤ c_X ⟨·⟩^{-(d-2)}`, `|Y| ≤ c_Y ⟨·⟩^{-(d-2-δ)}`, `|X − Y| ≤ c_D ⟨·⟩^{-(d-4)}`,
`|X ∗ t| ≤ c_A ⟨·⟩^{-(d-δ)}`, `|t − T| ≤ c_h ⟨·⟩^{-(2d-6-δ)} + J_h 1_0`,
`|T| ≤ c_T ⟨·⟩^{-(2d-4-δ)} + J_T 1_0`, `|θ − Θ| ≤ c_θ ⟨·⟩^{-(d-4-δ)}`, `|Θ| ≤ c_Θ ⟨·⟩^{-(d-2-δ)}`,
`|Θ ∗ T| ≤ c_H ⟨·⟩^{-(d-δ)}`. Then
`X' − Y' = (X ∗ t) ∗ (θ − Θ) + (X ∗ (t − T)) ∗ Θ + ((X − Y) ∗ T) ∗ Θ` and
`|X' − Y'| ≤ (K c_A c_θ + c_X c_Θ (K' c_h + J_h) + c_D c_H) ⟨·⟩^{-(d-4-3δ)}`: the difference of a
`Θ` factor sits next to the product `X ∗ t` (decay `d − δ`), the difference of a `Σ̊` factor
between two chains, and the difference of the chains next to `T ∗ Θ` (decay `d − δ`). -/
private theorem VR1_stepZ (hd : 8 ≤ d) {w δ : ℝ} (hw : 1 ≤ w) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (habs : 2 ^ (d + 1) * sumC d ((d : ℝ) + 2 * δ) ≤ w ^ (2 * δ))
    (X Y t T θ Θ : (Fin d → ℤ) → ℂ) {cX cY cD cA ch Jh cT JT cθ cΘ cH : ℝ}
    (hcX : 0 ≤ cX) (hcY : 0 ≤ cY) (hcD : 0 ≤ cD) (hcA : 0 ≤ cA) (hch : 0 ≤ ch) (hJh : 0 ≤ Jh)
    (hcT : 0 ≤ cT) (hJT : 0 ≤ JT) (hcθ : 0 ≤ cθ) (hcΘ : 0 ≤ cΘ) (hcH : 0 ≤ cH)
    (hX : ∀ α, ‖X α‖ ≤ cX * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 2)))
    (hY : ∀ α, ‖Y α‖ ≤ cY * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 2 - δ)))
    (hD : ∀ α, ‖X α - Y α‖ ≤ cD * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 4)))
    (hA : ∀ α, ‖convZ X t α‖ ≤ cA * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - δ)))
    (hh : ∀ α, ‖t α - T α‖ ≤ ch * ((zdInf α : ℝ) + w) ^ (-(2 * (d : ℝ) - 6 - δ)) +
      (if α = 0 then Jh else 0))
    (hT : ∀ α, ‖T α‖ ≤ cT * ((zdInf α : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)) +
      (if α = 0 then JT else 0))
    (hθ : ∀ α, ‖θ α - Θ α‖ ≤ cθ * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 4 - δ)))
    (hΘ : ∀ α, ‖Θ α‖ ≤ cΘ * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 2 - δ)))
    (hH : ∀ α, ‖convZ Θ T α‖ ≤ cH * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - δ))) (x : Fin d → ℤ) :
    ‖convZ (convZ X t) θ x - convZ (convZ Y T) Θ x‖ ≤
      (VR1_K d w ((d : ℝ) - δ) ((d : ℝ) - 4 - δ) ((d : ℝ) - 4 - 3 * δ) * cA * cθ +
        cX * (cΘ * (ch * VR1_K d w ((d : ℝ) - 2 - δ) (2 * (d : ℝ) - 6 - δ)
          ((d : ℝ) - 2 - δ) + Jh)) + cD * cH) *
        ((zdInf x : ℝ) + w) ^ (-((d : ℝ) - 4 - 3 * δ)) := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hw0 : 0 < w := by linarith
  set h : (Fin d → ℤ) → ℂ := fun α => t α - T α with hhdef
  set D : (Fin d → ℤ) → ℂ := fun α => X α - Y α with hDdef
  set Qh : ℝ := 2 * (d : ℝ) - 6 - δ with hQh
  set QT : ℝ := 2 * (d : ℝ) - 4 - δ with hQT
  -- pure power laws for `h`, `T`, `t`, `θ`
  have hh' : ∀ α, ‖h α‖ ≤ (ch + Jh * w ^ Qh) * ((zdInf α : ℝ) + w) ^ (-Qh) :=
    fun α => (hh α).trans (VR1_point_le hw hJh α)
  have hT' : ∀ α, ‖T α‖ ≤ (cT + JT * w ^ QT) * ((zdInf α : ℝ) + w) ^ (-QT) :=
    fun α => (hT α).trans (VR1_point_le hw hJT α)
  have ht' : ∀ α, ‖t α‖ ≤ ((ch + Jh * w ^ Qh) + (cT + JT * w ^ QT)) *
      ((zdInf α : ℝ) + w) ^ (-Qh) := by
    intro α
    have e : t α = h α + T α := by simp [hhdef]
    rw [e, add_mul]
    refine (norm_add_le _ _).trans (add_le_add (hh' α) ((hT' α).trans ?_))
    exact mul_le_mul_of_nonneg_left (VR1_br_anti hw (by linarith) α) (by positivity)
  have hθ' : ∀ α, ‖θ α‖ ≤ (cθ + cΘ) * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 4 - δ)) := by
    intro α
    have e : θ α = (θ α - Θ α) + Θ α := by ring
    rw [e, add_mul]
    refine (norm_add_le _ _).trans (add_le_add (hθ α) ((hΘ α).trans ?_))
    exact mul_le_mul_of_nonneg_left (VR1_br_anti hw (by linarith) α) hcΘ
  have hcK0 : 0 ≤ ch + Jh * w ^ Qh := by positivity
  have hcT0 : 0 ≤ cT + JT * w ^ QT := by positivity
  -- the convolutions `A = X ∗ t`, `B = Y ∗ T`
  set A := convZ X t with hAdef
  set B := convZ Y T with hBdef
  have hB : ∀ α, ‖B α‖ ≤ (cY * cT * VR1_K d w ((d : ℝ) - 2 - δ) QT ((d : ℝ) - 2 - δ) +
      JT * cY) * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 2 - δ)) := by
    intro α
    have := (VR1_conv2 hd1 hw Y T hcY hcT hY hT (by linarith) le_rfl (by linarith)
      (by rw [hQT]; linarith) α).2
    refine this.trans (le_of_eq ?_)
    unfold VR1_K; ring
  have hB0 : 0 ≤ cY * cT * VR1_K d w ((d : ℝ) - 2 - δ) QT ((d : ℝ) - 2 - δ) + JT * cY := by
    have := VR1_K_nonneg (d := d) (u := (d : ℝ) - 2 - δ) (v := QT) (m := (d : ℝ) - 2 - δ) hw0.le
      (by rw [hQT]; linarith)
    positivity
  -- summability
  have S1 : Summable fun α => A α * θ (x - α) :=
    VR1_summable_conv hd1 hw A θ hcA (by positivity) hA hθ' (by linarith) (by linarith)
      (by linarith) x
  have S2 : Summable fun α => A α * Θ (x - α) :=
    VR1_summable_conv hd1 hw A Θ hcA hcΘ hA hΘ (by linarith) (by linarith) (by linarith) x
  have S3 : Summable fun α => B α * Θ (x - α) :=
    VR1_summable_conv hd1 hw B Θ hB0 hcΘ hB hΘ (by linarith) (by linarith) (by linarith) x
  have S456 : ∀ α, convZ X t α - convZ Y T α = convZ X h α + convZ D T α := by
    intro α
    have S4 : Summable fun β => X β * t (α - β) :=
      VR1_summable_conv hd1 hw X t hcX (by positivity) hX ht' (by linarith) (by linarith)
        (by rw [hQh]; linarith) α
    have S5 : Summable fun β => X β * T (α - β) :=
      VR1_summable_conv hd1 hw X T hcX hcT0 hX hT' (by linarith) (by linarith)
        (by rw [hQT]; linarith) α
    have S6 : Summable fun β => Y β * T (α - β) :=
      VR1_summable_conv hd1 hw Y T hcY hcT0 hY hT' (by linarith) (by linarith)
        (by rw [hQT]; linarith) α
    unfold convZ
    calc ∑' β, X β * t (α - β) - ∑' β, Y β * T (α - β)
        = ∑' β, (X β * t (α - β) - Y β * T (α - β)) := (S4.tsum_sub S6).symm
      _ = ∑' β, ((X β * t (α - β) - X β * T (α - β)) + (X β * T (α - β) - Y β * T (α - β))) :=
          tsum_congr fun β => by ring
      _ = ∑' β, (X β * t (α - β) - X β * T (α - β)) +
            ∑' β, (X β * T (α - β) - Y β * T (α - β)) := (S4.sub S5).tsum_add (S5.sub S6)
      _ = _ := by
          congr 1 <;> exact tsum_congr fun β => by simp only [hhdef, hDdef]; ring
  -- bounds for `X ∗ h` and `D ∗ T`
  have hXh : ∀ α, ‖convZ X h α‖ ≤ (cX * (ch + Jh * w ^ Qh) *
      VR1_K d w ((d : ℝ) - 2) Qh ((d : ℝ) - 2)) * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 2)) := by
    intro α
    have := (VR1_conv2 (J := 0) hd1 hw X h hcX hcK0 hX (VR1_pl0 hh') (by linarith) le_rfl
      (by rw [hQh]; linarith) (by rw [hQh]; linarith) α).2
    refine this.trans (le_of_eq ?_)
    unfold VR1_K; ring
  have hDT : ∀ α, ‖convZ D T α‖ ≤ (cD * (cT + JT * w ^ QT) *
      VR1_K d w ((d : ℝ) - 4) QT ((d : ℝ) - 4)) * ((zdInf α : ℝ) + w) ^ (-((d : ℝ) - 4)) := by
    intro α
    have := (VR1_conv2 (J := 0) hd1 hw D T hcD hcT0 hD (VR1_pl0 hT') (by linarith) le_rfl
      (by rw [hQT]; linarith) (by rw [hQT]; linarith) α).2
    refine this.trans (le_of_eq ?_)
    unfold VR1_K; ring
  have hK1 := VR1_K_nonneg (d := d) (u := (d : ℝ) - 2) (v := Qh) (m := (d : ℝ) - 2) hw0.le
    (by rw [hQh]; linarith)
  have hK2 := VR1_K_nonneg (d := d) (u := (d : ℝ) - 4) (v := QT) (m := (d : ℝ) - 4) hw0.le
    (by rw [hQT]; linarith)
  have S7 : Summable fun α => convZ X h α * Θ (x - α) :=
    VR1_summable_conv hd1 hw _ Θ (by positivity) hcΘ hXh hΘ (by linarith) (by linarith)
      (by linarith) x
  have S8 : Summable fun α => convZ D T α * Θ (x - α) :=
    VR1_summable_conv hd1 hw _ Θ (by positivity) hcΘ hDT hΘ (by linarith) (by linarith)
      (by linarith) x
  -- the decomposition
  have hdec : convZ (convZ X t) θ x - convZ (convZ Y T) Θ x =
      convZ A (fun α => θ α - Θ α) x + convZ (convZ X h) Θ x + convZ (convZ D T) Θ x := by
    change convZ A θ x - convZ B Θ x = _
    rw [show convZ A θ x = ∑' α, A α * θ (x - α) from rfl,
      show convZ B Θ x = ∑' α, B α * Θ (x - α) from rfl,
      show convZ A (fun α => θ α - Θ α) x = ∑' α, A α * (θ (x - α) - Θ (x - α)) from rfl,
      show convZ (convZ X h) Θ x = ∑' α, convZ X h α * Θ (x - α) from rfl,
      show convZ (convZ D T) Θ x = ∑' α, convZ D T α * Θ (x - α) from rfl, add_assoc,
      ← S1.tsum_sub S3, ← S7.tsum_add S8]
    have e1 : ∀ α, A α * θ (x - α) - B α * Θ (x - α) =
        A α * (θ (x - α) - Θ (x - α)) + (convZ X h α * Θ (x - α) + convZ D T α * Θ (x - α)) := by
      intro α
      have := S456 α
      rw [← hAdef, ← hBdef] at this
      rw [← add_mul, ← this]
      ring
    simp_rw [e1]
    have S9 : Summable fun α => A α * (θ (x - α) - Θ (x - α)) := by
      have := S1.sub S2
      refine this.congr fun α => ?_
      ring
    rw [S9.tsum_add (S7.add S8)]
  rw [hdec]
  -- the three terms
  have hm0 : (0 : ℝ) ≤ (d : ℝ) - 4 - 3 * δ := by linarith
  have tA := (VR1_conv2 (J := 0) hd1 hw A (fun α => θ α - Θ α) hcA hcθ hA
    (VR1_pl0 hθ) hm0 (by linarith) (by linarith)
    (by linarith) x).2
  rw [zero_mul, add_zero] at tA
  have hHB : ∀ z, ‖convZ Θ h z‖ ≤ (cΘ * (ch * VR1_K d w ((d : ℝ) - 2 - δ) Qh ((d : ℝ) - 2 - δ) +
      Jh)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - δ)) := by
    intro z
    have := (VR1_conv2 hd1 hw Θ h hcΘ hch hΘ hh (by linarith) le_rfl (by rw [hQh]; linarith)
      (by rw [hQh]; linarith) z).2
    refine this.trans (le_of_eq ?_)
    unfold VR1_K; ring
  have hK3 := VR1_K_nonneg (d := d) (u := (d : ℝ) - 2 - δ) (v := Qh) (m := (d : ℝ) - 2 - δ) hw0.le
    (by rw [hQh]; linarith)
  have e2 : (d : ℝ) - 2 + ((d : ℝ) - 2 - δ) - ((d : ℝ) - 4 - 3 * δ) - d = 2 * δ := by ring
  have e3 : (d : ℝ) - 4 + ((d : ℝ) - δ) - ((d : ℝ) - 4 - 3 * δ) - d = 2 * δ := by ring
  have e2' : (d : ℝ) - 2 + ((d : ℝ) - 2 - δ) - ((d : ℝ) - 4 - 3 * δ) = d + 2 * δ := by ring
  have e3' : (d : ℝ) - 4 + ((d : ℝ) - δ) - ((d : ℝ) - 4 - 3 * δ) = d + 2 * δ := by ring
  have tB := chain_step hd1 hw X h Θ hcX hcK0 hcΘ (by positivity) hX hh' hΘ hHB
    (u := (d : ℝ) - 2) (v := (d : ℝ) - 2 - δ) (p := (d : ℝ) - 2 - δ) (Q := Qh)
    (m := (d : ℝ) - 4 - 3 * δ) (by linarith) (by linarith) (by rw [hQh]; linarith)
    (by rw [hQh]; linarith) (by linarith) hm0 (by linarith) (by linarith) (by linarith)
    (by linarith) (by rw [e2, e2']; exact habs) x
  have tC := chain_step hd1 hw D T Θ hcD hcT0 hcΘ hcH hD hT' hΘ hH
    (u := (d : ℝ) - 4) (v := (d : ℝ) - δ) (p := (d : ℝ) - 2 - δ) (Q := QT)
    (m := (d : ℝ) - 4 - 3 * δ) (by linarith) (by linarith) (by rw [hQT]; linarith)
    (by rw [hQT]; linarith) (by linarith) hm0 (by linarith) (by linarith) (by linarith)
    (by linarith) (by rw [e3, e3']; exact habs) x
  have tA' : ‖convZ A (fun α => θ α - Θ α) x‖ ≤
      VR1_K d w ((d : ℝ) - δ) ((d : ℝ) - 4 - δ) ((d : ℝ) - 4 - 3 * δ) * cA * cθ *
        ((zdInf x : ℝ) + w) ^ (-((d : ℝ) - 4 - 3 * δ)) := by
    refine tA.trans (le_of_eq ?_)
    unfold VR1_K; ring
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [add_mul, add_mul]
  linarith [tA', tB, tC]

end Conv

/-! ## Products of short kernels on the torus and convolutions on `ℤ^d` -/

section Lift

/-- A matrix on `Z_L^d` is translation invariant: `A_{xy} = A_{0, y - x}`. -/
private def VR1_TI {L : ℕ} (A : Matrix (Zd d L) (Zd d L) ℂ) : Prop :=
  ∀ x y, A x y = A 0 (y - x)

/-- The row `A_{0·}` of a matrix on `Z_L^d` vanishes beyond `‖y‖_L > ρ`. -/
private def VR1_Supp {L : ℕ} (A : Matrix (Zd d L) (Zd d L) ℂ) (ρ : ℕ) : Prop :=
  ∀ y, ρ < zdistInf d L y → A 0 y = 0

/-- The lift to `ℤ^d` of the row `A_{0·}`: `a ↦ A_{0, [a]_L}` for `|a|_∞ ≤ L/5`, and `0`
beyond. -/
private def VR1_lift (L : ℕ) (A : Matrix (Zd d L) (Zd d L) ℂ) (a : Fin d → ℤ) : ℂ :=
  if zdInf a ≤ L / 5 then A 0 (zcast L a) else 0

/-- `‖[a]_L‖_L = |a|_∞` for `2 |a|_∞ < L`. -/
private theorem VR1_zdistInf_zcast {L : ℕ} [NeZero L] (a : Fin d → ℤ) (ha : 2 * zdInf a < L) :
    zdistInf d L (zcast L a) = zdInf a := by
  rw [← VR1Graph_zdInf_zlift, VR1Graph_zlift_zcast a ha]

/-- The lift of a row supported in `‖y‖_L ≤ ρ ≤ L/5` vanishes beyond `|a|_∞ > ρ`. -/
private theorem VR1_lift_eq_zero {L : ℕ} [NeZero L] {A : Matrix (Zd d L) (Zd d L) ℂ} {ρ : ℕ}
    (hA : VR1_Supp A ρ) (a : Fin d → ℤ) (ha : ρ < zdInf a) : VR1_lift L A a = 0 := by
  unfold VR1_lift
  split_ifs with h
  · refine hA _ ?_
    rw [VR1_zdistInf_zcast a (by omega)]
    exact ha
  · rfl

/-- The lift of a row supported in `ρ ≤ L/5` is finitely supported. -/
private theorem VR1_lift_supp {L : ℕ} [NeZero L] {A : Matrix (Zd d L) (Zd d L) ℂ} {ρ : ℕ}
    (hA : VR1_Supp A ρ) (a : Fin d → ℤ) (ha : a ∉ boxZ d ρ) : VR1_lift L A a = 0 :=
  VR1_lift_eq_zero hA a (by rw [mem_boxZ_iff] at ha; omega)

/-- The lift at a point of the lift window: `A_{0, [a]_L}`. -/
private theorem VR1_lift_of_le {L : ℕ} (A : Matrix (Zd d L) (Zd d L) ℂ) {a : Fin d → ℤ}
    (ha : zdInf a ≤ L / 5) : VR1_lift L A a = A 0 (zcast L a) := by
  rw [VR1_lift, if_pos ha]

/-- **The lift of a product.** For translation invariant `A`, `B` with rows supported in
`ρ₁`, `ρ₂` and `ρ₁ + ρ₂ ≤ L/5`, the product `A B` is translation invariant with row supported in
`ρ₁ + ρ₂`, and its lift is the convolution on `ℤ^d` of the lifts. -/
private theorem VR1_lift_mul {L : ℕ} [NeZero L] {A B : Matrix (Zd d L) (Zd d L) ℂ} {ρ₁ ρ₂ : ℕ}
    (hA : VR1_TI A) (hB : VR1_TI B) (hsA : VR1_Supp A ρ₁) (hsB : VR1_Supp B ρ₂)
    (hρ : ρ₁ + ρ₂ ≤ L / 5) :
    VR1_TI (A * B) ∧ VR1_Supp (A * B) (ρ₁ + ρ₂) ∧
      VR1_lift L (A * B) = convZ (VR1_lift L A) (VR1_lift L B) := by
  classical
  have hL5 : 2 * (L / 5) + 2 * (L / 5) < L := by
    have := Nat.div_mul_le_self L 5
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    omega
  have hrow : ∀ y, (A * B) 0 y = ∑ w, A 0 w * B 0 (y - w) := by
    intro y
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun w _ => by rw [hB w y]
  refine ⟨fun x y => ?_, fun y hy => ?_, funext fun a => ?_⟩
  · simp only [Matrix.mul_apply]
    rw [← Fintype.sum_equiv (Equiv.addRight x) (fun w => A 0 w * B w (y - x)) _ (fun w => ?_)]
    simp only [Equiv.coe_addRight]
    rw [hA x (w + x), hB (w + x) y, hB w (y - x), add_sub_cancel_right]
    congr 2; abel
  · rw [hrow]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases h1 : zdistInf d L w ≤ ρ₁
    · have h2 : ρ₂ < zdistInf d L (y - w) := by
        have := zdistInf_add_le d L w (y - w)
        rw [add_sub_cancel] at this
        omega
      rw [hsB _ h2, mul_zero]
    · rw [hsA _ (by omega), zero_mul]
  · -- the convolution is a finite sum over `|α| ≤ ρ₁`
    have hconv : convZ (VR1_lift L A) (VR1_lift L B) a =
        ∑ α ∈ boxZ d ρ₁, VR1_lift L A α * VR1_lift L B (a - α) := by
      unfold convZ
      exact tsum_eq_sum fun α hα => by rw [VR1_lift_supp hsA α hα, zero_mul]
    rw [hconv]
    by_cases ha : zdInf a ≤ L / 5
    · rw [VR1_lift_of_le _ ha, hrow]
      have hsum : ∑ w, A 0 w * B 0 (zcast L a - w) =
          ∑ w ∈ Finset.univ.filter (fun w : Zd d L => zdistInf d L w ≤ ρ₁),
            A 0 w * B 0 (zcast L a - w) := by
        rw [Finset.sum_filter_of_ne fun w _ hw => by
          by_contra h
          exact hw (by rw [hsA w (by omega), zero_mul])]
      rw [hsum]
      refine (Finset.sum_nbij' (zcast L) zlift (fun α hα => ?_) (fun w hw => ?_)
        (fun α hα => ?_) (fun w _ => VR1Graph_zcast_zlift w) (fun α hα => ?_)).symm
      · rw [mem_boxZ_iff] at hα
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [VR1_zdistInf_zcast α (by omega)]
        exact hα
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rw [mem_boxZ_iff, VR1Graph_zdInf_zlift]
        exact hw
      · rw [mem_boxZ_iff] at hα
        exact VR1Graph_zlift_zcast α (by omega)
      · rw [mem_boxZ_iff] at hα
        rw [VR1_lift_of_le _ (by omega)]
        unfold VR1_lift
        split_ifs with h
        · rw [VR1Graph_zcast_sub]
        · have h2 : 2 * zdInf (a - α) < L := by
            have := zdInf_le_sub a α
            have := zdInf_le_sub (a - α) (-α)
            have h3 : zdInf (a - α) ≤ zdInf a + zdInf α := by
              have := zdInf_add_le a (-α)
              rwa [zdInf_neg, ← sub_eq_add_neg] at this
            omega
          have h4 : ρ₂ < zdistInf d L (zcast L a - zcast L α) := by
            rw [← VR1Graph_zcast_sub, VR1_zdistInf_zcast _ h2]
            omega
          rw [hsB _ h4, mul_zero]
    · rw [VR1_lift, if_neg ha]
      refine (Finset.sum_eq_zero fun α hα => ?_).symm
      rw [mem_boxZ_iff] at hα
      by_cases h2 : zdInf (a - α) ≤ ρ₂
      · exfalso
        have := zdInf_le_sub a α
        omega
      · rw [VR1_lift_eq_zero hsB _ (by omega), mul_zero]

/-- The cut of a matrix on `Z_L^d` at `‖y − x‖_L ≤ R`. -/
private def VR1_cut {L : ℕ} (R : ℕ) (A : Matrix (Zd d L) (Zd d L) ℂ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun x y => if zdistInf d L (y - x) ≤ R then A x y else 0

private theorem VR1_cut_TI {L : ℕ} (R : ℕ) {A : Matrix (Zd d L) (Zd d L) ℂ} (hA : VR1_TI A) :
    VR1_TI (VR1_cut R A) := by
  intro x y
  simp only [VR1_cut, Matrix.of_apply, sub_zero, hA x y]

private theorem VR1_cut_supp {L : ℕ} (R : ℕ) (A : Matrix (Zd d L) (Zd d L) ℂ) :
    VR1_Supp (VR1_cut R A) R := by
  intro y hy
  simp only [VR1_cut, Matrix.of_apply, sub_zero]
  rw [if_neg (by omega)]

/-- The chain `Θ_c K_{o₁} Θ_c ⋯ K_{o_k} Θ_c` of matrices on `Z_L^d`. -/
private def VR1_chainR {L : ℕ} [NeZero L] (Θc : Matrix (Zd d L) (Zd d L) ℂ)
    (Kc : ℕ → Matrix (Zd d L) (Zd d L) ℂ) (o : List ℕ) : Matrix (Zd d L) (Zd d L) ℂ :=
  o.foldl (fun A l => A * Kc l * Θc) Θc

/-- **The lift of a chain of short factors.** If `Θ_c` and the `K_l` are translation invariant
with rows supported in `R` and `(2k + 1) R ≤ L/5`, `k = |o|`, the chain is translation invariant
with row supported in `(2k + 1) R`, and its lift is the chain on `ℤ^d` of the lifts. -/
private theorem VR1_lift_chain {L : ℕ} [NeZero L] {Θc : Matrix (Zd d L) (Zd d L) ℂ}
    {Kc : ℕ → Matrix (Zd d L) (Zd d L) ℂ} {R : ℕ} (hΘ : VR1_TI Θc) (hΘs : VR1_Supp Θc R)
    (hK : ∀ l, VR1_TI (Kc l)) (hKs : ∀ l, VR1_Supp (Kc l) R) :
    ∀ (o : List ℕ) (A : Matrix (Zd d L) (Zd d L) ℂ) (ρ : ℕ), VR1_TI A → VR1_Supp A ρ →
      ρ + 2 * o.length * R ≤ L / 5 →
      VR1_TI (o.foldl (fun A l => A * Kc l * Θc) A) ∧
        VR1_Supp (o.foldl (fun A l => A * Kc l * Θc) A) (ρ + 2 * o.length * R) ∧
        VR1_lift L (o.foldl (fun A l => A * Kc l * Θc) A) =
          o.foldl (fun F l => convZ (convZ F (VR1_lift L (Kc l))) (VR1_lift L Θc))
            (VR1_lift L A) := by
  intro o
  induction o with
  | nil => intro A ρ hA hsA _; simpa using ⟨hA, hsA⟩
  | cons l o ih =>
    intro A ρ hA hsA hρ
    simp only [List.length_cons] at hρ
    obtain ⟨h1, h2, h3⟩ := VR1_lift_mul hA (hK l) hsA (hKs l) (by nlinarith)
    obtain ⟨h4, h5, h6⟩ := VR1_lift_mul h1 hΘ h2 hΘs (by nlinarith)
    have := ih (A * Kc l * Θc) (ρ + R + R) h4 h5 (by nlinarith)
    simp only [List.foldl_cons, List.length_cons]
    rw [h6, h3] at this
    refine ⟨this.1, ?_, this.2.2⟩
    have e : ρ + R + R + 2 * o.length * R = ρ + 2 * (o.length + 1) * R := by ring
    rw [← e]; exact this.2.1

end Lift

/-! ## The family `Σ̊` cut at `R = ⌊L/M⌋` -/

section CutFam

/-- The kernel family `K` cut at `‖y − x‖_L ≤ ⌊L/M⌋`. -/
private def VR1_cutFam (K : KerFamily d) (M : ℕ) : KerFamily d :=
  fun l W L _ z => VR1_cut (L / M) (K l W L z)

/-- [I, (1.25)] passes to the cut family. -/
private theorem VR1_kerSymm_cut {K : KerFamily d} {l : ℕ} (hK : KerSymm K l) (M : ℕ) :
    KerSymm (VR1_cutFam K M) l := by
  intro W L _ z hz x a
  obtain ⟨h1, h2⟩ := hK W L z hz x a
  simp only [VR1_cutFam, VR1_cut, Matrix.of_apply, add_sub_cancel_left, sub_zero, h1, h2,
    zdistInf_neg]
  exact ⟨trivial, trivial⟩

/-- The row sum of `Σ̊_l` on the torus is `0` on `adm(c₀, c₁)` for `L ≥ L₀`, where `S` has row
sums `1` ([I, (8.3)]). -/
private theorem VR1_rowSum_zero (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) : ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L →
      (W, L) ∈ adm c₀ c₁ → ∀ z : ℂ,
        ∑ x, sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 x = 0 := by
  obtain ⟨W₁, hW₁⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, hW₂⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨L₂, hL₂⟩ := RenormDiff_W_of_L (c₀ := c₀) hc₁ (max W₁ W₂)
  refine ⟨L₂, fun W L _ hL hadm z => ?_⟩
  have hW := hL₂ W L hL hadm
  have hrow : ∑ x, (smatVar P W L 0 x : ℂ) = 1 := by
    rw [hW₂ W L hadm (le_trans (le_max_right _ _) hW)]
    have := (hW₁ W L hadm (le_trans (le_max_left _ _) hW)).rowSum 0
    exact_mod_cast this
  change ∑ x, sigMat (Renorm.sig Sig) (smatVar P W L) z l 0 x = 0
  simp_rw [Renorm.sigMat_eq Sig (smatVar P W L) z l 0]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, mul_one, sub_self]

/-- **[I, (1.26)–(1.27)] for the cut family** `Σ̊_l 1(‖y − x‖_L ≤ ⌊L/M⌋)`: the entries are those of
`Σ̊_l` or `0` (`G13.entrywise` for `Σ̊`), and the row sum is minus the tail of `Σ̊_l` beyond
`⌊L/M⌋` (the row sum of `Σ̊_l` is `0`), at most `L^τ W^{-(l-4)d/2} W^{-4} C ⌊L/M⌋^{-(d-4)}`. -/
private theorem VR1_kerBound_cut (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (M : ℕ) (hM : 1 ≤ M) (l : ℕ) (hl4 : 4 ≤ l)
    (hlN : l ≤ N) (hle : Even l) :
    KerSymm (VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) M) l ∧
      KerBound (VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) M) l := by
  have hR := Renorm.selfEnergiesUpTo d hd P N Sig hSig
  refine ⟨VR1_kerSymm_cut (kerSymm_sigKer_smatVar d P _ l) M, ?_⟩
  intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hlow : SelfEnergiesUpTo d (smatVar P) (Renorm.sig Sig) (l - 1) :=
    fun j hj4 hjl hje => hR j hj4 (by omega) hje
  have hsh : SelfEnergyShape l (Renorm.sig Sig l) := (hR l hl4 hlN hle).1
  obtain ⟨L₁, hL₁⟩ := G13.entrywise d hd P l (Renorm.sig Sig) hl4 hlow hsh κ ε c₀ c₁ hκ hε hc₀
    hc₁ hc τ hτ
  obtain ⟨L₂, hL₂⟩ := VR1_rowSum_zero P Sig l hc₀ hc₁
  obtain ⟨C, hC0, hC⟩ := Chain_tailSum d (2 * (d : ℝ) - 4) (by linarith)
  set A : ℝ := C * (2 * (M : ℝ)) ^ ((d : ℝ) - 4) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max L₁ L₂) (max (2 * M) ⌈(A + 1) ^ (1 / ε)⌉₊),
    fun W L _ hL hadm z hz => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLM : 2 * M ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLA : ⌈(A + 1) ^ (1 / ε)⌉₊ ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have hW1 : (1 : ℝ) ≤ W := le_trans (Real.one_le_rpow (by
    have : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this) hc₁.le) hLW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hent := hL₁ W L hL1 hadm z hz
  set R := L / M with hRdef
  -- entrywise: the cut entries are entries of `Σ̊_l` or `0`
  have hcut : ∀ x, ‖VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) M l W L z 0 x‖ ≤
      ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 x‖ := by
    intro x
    simp only [VR1_cutFam, VR1_cut, Matrix.of_apply]
    split_ifs <;> simp
  have hbd : ∀ x, 0 ≤ (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
      (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) := by
    intro x; split_ifs <;> positivity
  refine ⟨fun x => (hcut x).trans (hent x), ?_⟩
  -- the row sum is minus the tail
  have hsplit : ∑ x, VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) M l W L z 0 x =
      -∑ x ∈ Finset.univ.filter (fun x : Zd d L => R < zdistInf d L x),
        sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 x := by
    have h0 := hL₂ W L hL2 hadm z
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Zd d L => R < zdistInf d L x)] at h0
    simp only [VR1_cutFam, VR1_cut, Matrix.of_apply, sub_zero]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Zd d L => R < zdistInf d L x)]
    rw [Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [if_neg (by omega)], zero_add]
    rw [Finset.sum_congr rfl fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [if_pos (by omega)]]
    linear_combination h0
  rw [hsplit, norm_neg]
  -- the tail of `Σ̊_l`
  have hRM : (L : ℝ) / (2 * M) ≤ R := by
    have h1 : L / M * M + M > L := by
      have := Nat.lt_div_mul_add (a := L) (b := M) (by omega)
      linarith
    have h2 : (L : ℝ) < (R : ℝ) * M + M := by
      have : ((L / M * M + M : ℕ) : ℝ) > L := by exact_mod_cast h1
      push_cast at this; linarith
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have h3 : (2 * (M : ℝ)) ≤ L := by exact_mod_cast hLM
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hR1 : (1 : ℝ) ≤ R := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have h3 : (2 * (M : ℝ)) ≤ L := by exact_mod_cast hLM
    have : (1 : ℝ) ≤ (L : ℝ) / (2 * M) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have htail : ∑ x ∈ Finset.univ.filter (fun x : Zd d L => R < zdistInf d L x),
      ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 x‖ ≤
      (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) *
        (C * (R : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4))) := by
    have hsub : Finset.univ.filter (fun x : Zd d L => R < zdistInf d L x) ⊆
        Finset.univ.filter (fun x : Zd d L => (R : ℝ) ≤ brk d L W x 0) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      unfold brk
      rw [sub_zero]
      have : (R : ℝ) < zdistInf d L x := by exact_mod_cast hx
      linarith
    calc ∑ x ∈ Finset.univ.filter (fun x : Zd d L => R < zdistInf d L x),
          ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 x‖
        ≤ ∑ x ∈ Finset.univ.filter (fun x : Zd d L => R < zdistInf d L x),
            (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) *
              brk d L W x 0 ^ (-(2 * (d : ℝ) - 4)) := by
          refine Finset.sum_le_sum fun x hx => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hx0 : x ≠ 0 := by
            rintro rfl; rw [(zdistInf_eq_zero_iff d L).2 rfl] at hx
            exact absurd hx (Nat.not_lt_zero _)
          refine (hent x).trans (le_of_eq ?_)
          rw [if_neg hx0, add_zero, Chain_bB_sq d L W hWn, Chain_brk_comm d L W 0 x]
          ring
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Zd d L => (R : ℝ) ≤ brk d L W x 0),
            (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) *
              brk d L W x 0 ^ (-(2 * (d : ℝ) - 4)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by
            have := Chain_brk_pos d L W hWn x 0
            positivity
      _ = (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) *
            ∑ x ∈ Finset.univ.filter (fun x : Zd d L => (R : ℝ) ≤ brk d L W x 0),
              brk d L W x 0 ^ (-(2 * (d : ℝ) - 4)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          exact hC L W hWn 0 R (by linarith)
  refine (norm_sum_le _ _).trans (htail.trans ?_)
  -- `C W^{d-4} R^{-(d-4)} ≤ η`
  have hη : (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im := hz.2.1
  have hLε : A + 1 ≤ (L : ℝ) ^ ε := by
    have h1 : (A + 1) ^ (1 / ε) ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLA)
    calc A + 1 = ((A + 1) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ (L : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
  have hRp : (R : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)) ≤
      (2 * (M : ℝ)) ^ ((d : ℝ) - 4) * (L : ℝ) ^ (-((d : ℝ) - 4)) := by
    have e1 : (d : ℝ) - (2 * (d : ℝ) - 4) = -((d : ℝ) - 4) := by ring
    rw [e1]
    calc (R : ℝ) ^ (-((d : ℝ) - 4)) ≤ ((L : ℝ) / (2 * M)) ^ (-((d : ℝ) - 4)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hRM (by linarith)
      _ = _ := by
          rw [Real.div_rpow hL0.le (by positivity), Real.rpow_neg hL0.le,
            Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * M), div_inv_eq_mul]
          ring
  have hkey : C * (R : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)) * (W : ℝ) ^ ((d : ℝ) - 4) ≤ z.im := by
    have hWLd : (W : ℝ) ^ ((d : ℝ) - 6) ≤ (L : ℝ) ^ ((d : ℝ) - 6) :=
      Real.rpow_le_rpow hW0.le hWL (by linarith)
    calc C * (R : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)) * (W : ℝ) ^ ((d : ℝ) - 4)
        ≤ C * ((2 * (M : ℝ)) ^ ((d : ℝ) - 4) * (L : ℝ) ^ (-((d : ℝ) - 4))) *
            (W : ℝ) ^ ((d : ℝ) - 4) := by gcongr
      _ = A * ((W : ℝ) ^ (2 : ℝ) * (W : ℝ) ^ ((d : ℝ) - 6)) * (L : ℝ) ^ (-((d : ℝ) - 4)) := by
          rw [← Real.rpow_add hW0, hA]; ring_nf
      _ ≤ (L : ℝ) ^ ε * ((W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ ((d : ℝ) - 6)) *
            (L : ℝ) ^ (-((d : ℝ) - 4)) := by gcongr; linarith
      _ = (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by
          rw [Real.rpow_two, div_eq_mul_inv, ← Real.rpow_neg hL0.le]
          have : (L : ℝ) ^ ε * (L : ℝ) ^ ((d : ℝ) - 6) * (L : ℝ) ^ (-((d : ℝ) - 4)) =
              (L : ℝ) ^ (-(2 - ε)) := by
            rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; ring_nf
          rw [← this]; ring
      _ ≤ z.im := hη
  have e2 : (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) =
      (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ ((d : ℝ) - 4) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
  calc (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) *
        (C * (R : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)))
      = (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
          (C * (R : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)) * (W : ℝ) ^ ((d : ℝ) - 4)) := by
        rw [mul_assoc ((L : ℝ) ^ τ), e2]; ring
    _ ≤ (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * z.im := by gcongr
    _ = _ := by ring

end CutFam

/-! ## Products of power laws on the torus -/

section Torus

/-- **Two power laws on the torus.** For `0 ≤ m ≤ min(a, b)` and `n = a + b − m > d`: if
`|A_{uw}| ≤ c_a ⟨u − w⟩^{-a}` and `|B_{wv}| ≤ c_b ⟨w − v⟩^{-b}`, then
`|(A B)_{uv}| ≤ c_a c_b C W^{d-n} ⟨u − v⟩^{-m}`, with `C` depending on `d, a, b, m` only. -/
private theorem VR1_convT (d : ℕ) {a b m : ℝ} (hm : 0 ≤ m) (hma : m ≤ a) (hmb : m ≤ b)
    (hn : (d : ℝ) < a + b - m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W →
      ∀ (A B : Matrix (Zd d L) (Zd d L) ℂ) (ca cb : ℝ), 0 ≤ ca → 0 ≤ cb →
        (∀ u w, ‖A u w‖ ≤ ca * brk d L W u w ^ (-a)) →
        (∀ w v, ‖B w v‖ ≤ cb * brk d L W w v ^ (-b)) →
        ∀ u v, ‖(A * B) u v‖ ≤
          ca * cb * C * (W : ℝ) ^ ((d : ℝ) - (a + b - m)) * brk d L W u v ^ (-m) := by
  obtain ⟨C₀, hC₀, hsum⟩ := Chain_sumAll d (a + b - m) hn
  refine ⟨2 ^ m * 2 * C₀, by positivity, fun L W _ hW A B ca cb hca hcb hA hB u v => ?_⟩
  set n := a + b - m with hndef
  have hpos : ∀ x y : Zd d L, 0 < brk d L W x y := fun x y => Chain_brk_pos d L W hW x y
  have hpt : ∀ w, ‖A u w * B w v‖ ≤ ca * cb * (2 ^ m * brk d L W u v ^ (-m) *
      (brk d L W w u ^ (-n) + brk d L W w v ^ (-n))) := by
    intro w
    rw [norm_mul]
    have hR : brk d L W u v ≤ brk d L W u w + brk d L W w v := by
      have := Chain_brk_tri d L W w u v
      rw [Chain_brk_comm d L W w u] at this
      have : (0 : ℝ) ≤ W := Nat.cast_nonneg _
      linarith
    have h := rpow_mul_rpow_le (u := a) (v := b) (m := m) (hpos u w) (hpos w v) (hpos u v) hR hm
      hma hmb
    rw [Chain_brk_comm d L W u w] at h
    calc ‖A u w‖ * ‖B w v‖ ≤ (ca * brk d L W u w ^ (-a)) * (cb * brk d L W w v ^ (-b)) :=
          mul_le_mul (hA u w) (hB w v) (norm_nonneg _) (by have := hpos u w; positivity)
      _ = ca * cb * (brk d L W w u ^ (-a) * brk d L W w v ^ (-b)) := by
          rw [Chain_brk_comm d L W u w]; ring
      _ ≤ _ := by gcongr
  have hs1 := hsum L W hW u
  have hs2 := hsum L W hW v
  rw [Matrix.mul_apply]
  calc ‖∑ w, A u w * B w v‖ ≤ ∑ w, ‖A u w * B w v‖ := norm_sum_le _ _
    _ ≤ ∑ w, ca * cb * (2 ^ m * brk d L W u v ^ (-m) *
          (brk d L W w u ^ (-n) + brk d L W w v ^ (-n))) := Finset.sum_le_sum fun w _ => hpt w
    _ = ca * cb * (2 ^ m * brk d L W u v ^ (-m)) *
          (∑ w, brk d L W w u ^ (-n) + ∑ w, brk d L W w v ^ (-n)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ ≤ ca * cb * (2 ^ m * brk d L W u v ^ (-m)) *
          (C₀ * (W : ℝ) ^ ((d : ℝ) - n) + C₀ * (W : ℝ) ^ ((d : ℝ) - n)) := by
        have := hpos u v
        gcongr
    _ = _ := by ring

/-- `μ_{l :: o} = μ_l μ_o` for `μ_o = W^{-(k(o)-2)d/2}`. -/
private theorem VR1_mu_cons {W : ℝ} (hW : 0 < W) (l : ℕ) (o : List ℕ) :
    W ^ (-((((Kind.theta (l :: o)).ord : ℤ) : ℝ) - 2) * d / 2) =
      W ^ (-(((l : ℝ) - 2) * d / 2)) * W ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) := by
  rw [← Real.rpow_add hW, RenormDiff_ord_cons]; ring_nf

/-- `μ_{[]} = 1`. -/
private theorem VR1_mu_nil {W : ℝ} :
    W ^ (-((((Kind.theta ([] : List ℕ)).ord : ℤ) : ℝ) - 2) * d / 2) = 1 := by
  simp [Kind.ord]

/-- `⟨u − v⟩^{-a} ≤ ⟨u − v⟩^{-b}` for `b ≤ a`, `W ≥ 1`. -/
private theorem VR1_brk_anti {L W : ℕ} [NeZero L] (hW : 1 ≤ W) {a b : ℝ} (hab : b ≤ a)
    (u v : Zd d L) : brk d L W u v ^ (-a) ≤ brk d L W u v ^ (-b) := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Chain_le_brk d L W u v]) (by linarith)

/-- **[I, Lemma 6.2, (6.1)] for a chain followed by a kernel**: for a family `K` with
[I, (1.25)–(1.27)] at `l` and at the entries of `o`,
`|(Θ K_{o₁} Θ ⋯ K_{o_k} Θ K_l)_{uv}| ≤ W^σ W^{-(k(o)-2)d/2} W^{-(l-2)d/2} ⟨u − v⟩^{-(d-σ)}`: the
product is `(Θ K_{o₁}) ⋯ (Θ K_{o_k}) (Θ K_l)`, each factor of decay `⟨·⟩^{-d}` (`thetaSigma`). -/
private theorem VR1_chainK (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (K : KerFamily d) (l : ℕ)
    (hl : KerSymm K l ∧ KerBound K l) :
    ∀ o : List ℕ, (∀ j ∈ o, KerSymm K j ∧ KerBound K j) → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ,
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ u v : Zd d L,
          ‖((detData (Smat P.ψ W L) z (fun l => K l W L z)).chain o * K l W L z) u v‖ ≤
            (W : ℝ) ^ σ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) * brk d L W u v ^ (-((d : ℝ) - σ)) := by
  have hd6 : 6 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  -- it suffices to treat `σ ≤ 1`
  suffices h : ∀ o : List ℕ, (∀ j ∈ o, KerSymm K j ∧ KerBound K j) → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ u v : Zd d L,
          ‖((detData (Smat P.ψ W L) z (fun l => K l W L z)).chain o * K l W L z) u v‖ ≤
            (W : ℝ) ^ σ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) * brk d L W u v ^ (-((d : ℝ) - σ)) by
    intro o ho σ hσ
    obtain ⟨W₀, hW₀⟩ := h o ho (min σ 1) (lt_min hσ one_pos) (min_le_right _ _)
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz u v => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
    have hWn : 1 ≤ W := by exact_mod_cast hW1
    refine (hW₀ W L hadm ((le_max_left _ _).trans hW) z hz u v).trans ?_
    have h1 : (W : ℝ) ^ min σ 1 ≤ (W : ℝ) ^ σ :=
      Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)
    have h2 := VR1_brk_anti (d := d) (L := L) hWn (a := (d : ℝ) - min σ 1) (b := (d : ℝ) - σ)
      (by linarith [min_le_left σ 1]) u v
    have h0 : 0 ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by positivity
    have h3 : 0 ≤ brk d L W u v ^ (-((d : ℝ) - min σ 1)) := by
      have := Chain_brk_pos d L W hWn u v; positivity
    calc _ ≤ (W : ℝ) ^ σ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) * brk d L W u v ^ (-((d : ℝ) - min σ 1)) := by
          gcongr
      _ ≤ _ := by gcongr
  intro o
  induction o with
  | nil =>
    intro _ σ hσ _
    obtain ⟨W₀, h⟩ := thetaSigma d hd6 P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K l hl.1 hl.2 σ hσ
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz u v => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
    have hWn : 1 ≤ W := by exact_mod_cast hW1
    have := h W L hadm ((le_max_left _ _).trans hW) z hz u v
    rw [VR1_mu_nil, one_mul]
    exact this.trans (mul_le_mul_of_nonneg_left (VR1_brk_anti hWn (a := (d : ℝ))
      (b := (d : ℝ) - σ) (by linarith) u v) (by positivity))
  | cons j o ih =>
    intro ho σ hσ hσ1
    have hj := ho j List.mem_cons_self
    have ho' : ∀ j' ∈ o, KerSymm K j' ∧ KerBound K j' :=
      fun j' h => ho j' (List.mem_cons_of_mem _ h)
    obtain ⟨W₁, h₁⟩ := ih ho' (σ / 2) (by positivity) (by linarith)
    obtain ⟨W₂, h₂⟩ := thetaSigma d hd6 P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K j hj.1 hj.2 (σ / 4)
      (by positivity)
    obtain ⟨C, hC0, hconv⟩ := VR1_convT d (a := (d : ℝ)) (b := (d : ℝ) - σ / 2)
      (m := (d : ℝ) - σ) (by linarith) (by linarith) (by linarith) (by linarith)
    refine ⟨max (max W₁ W₂) (max 1 ((C + 1) ^ (4 / σ))), fun W L _ hadm hW z hz u v => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
    have hWn : 1 ≤ W := by exact_mod_cast hW1
    have hW0 : (0 : ℝ) < W := by linarith
    have hWC : (C + 1) ^ (4 / σ) ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
    set D := detData (Smat P.ψ W L) z (fun l => K l W L z) with hD
    have heq : D.chain (j :: o) * K l W L z = (D.Theta * D.Sig j) * (D.chain o * K l W L z) := by
      rw [RenormDiff_chain_cons, Matrix.mul_assoc]
    rw [heq]
    set μj := (W : ℝ) ^ (-(((j : ℝ) - 2) * d / 2)) with hμj
    set μo := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hμo
    set μl := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hμl
    have hA : ∀ x y, ‖(D.Theta * D.Sig j) x y‖ ≤ ((W : ℝ) ^ (σ / 4) * μj) *
        brk d L W x y ^ (-(d : ℝ)) := fun x y =>
      h₂ W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans hW)) z hz x y
    have hB : ∀ x y, ‖(D.chain o * K l W L z) x y‖ ≤ ((W : ℝ) ^ (σ / 2) * (μo * μl)) *
        brk d L W x y ^ (-((d : ℝ) - σ / 2)) := fun x y =>
      h₁ W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) z hz x y
    have := hconv L W hWn _ _ _ _ (by positivity) (by positivity) hA hB u v
    refine this.trans (le_of_eq_of_le rfl ?_)
    rw [VR1_mu_cons hW0, ← hμj, ← hμo]
    have e1 : (d : ℝ) - ((d : ℝ) + ((d : ℝ) - σ / 2) - ((d : ℝ) - σ)) = -(σ / 2) := by ring
    rw [e1, show -((d : ℝ) - σ) = -(d : ℝ) + σ by ring,
      show -(d : ℝ) + σ = -((d : ℝ) - σ) by ring]
    have hCW : C ≤ (W : ℝ) ^ (σ / 4) := by
      calc C ≤ C + 1 := by linarith
        _ = ((C + 1) ^ (4 / σ)) ^ (σ / 4) := by
          rw [← Real.rpow_mul (by linarith), show 4 / σ * (σ / 4) = 1 by field_simp,
            Real.rpow_one]
        _ ≤ (W : ℝ) ^ (σ / 4) := Real.rpow_le_rpow (by positivity) hWC (by positivity)
    have hb : 0 ≤ brk d L W u v ^ (-((d : ℝ) - σ)) := by
      have := Chain_brk_pos d L W hWn u v; positivity
    have hWs : (W : ℝ) ^ (σ / 4) * (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 4) * (W : ℝ) ^ (-(σ / 2)) ≤
        (W : ℝ) ^ σ := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    calc (W : ℝ) ^ (σ / 4) * μj * ((W : ℝ) ^ (σ / 2) * (μo * μl)) * C * (W : ℝ) ^ (-(σ / 2)) *
          brk d L W u v ^ (-((d : ℝ) - σ))
        ≤ (W : ℝ) ^ (σ / 4) * μj * ((W : ℝ) ^ (σ / 2) * (μo * μl)) * (W : ℝ) ^ (σ / 4) *
          (W : ℝ) ^ (-(σ / 2)) * brk d L W u v ^ (-((d : ℝ) - σ)) := by gcongr
      _ = ((W : ℝ) ^ (σ / 4) * (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 4) * (W : ℝ) ^ (-(σ / 2))) *
          (μj * μo * μl) * brk d L W u v ^ (-((d : ℝ) - σ)) := by ring
      _ ≤ (W : ℝ) ^ σ * (μj * μo * μl) * brk d L W u v ^ (-((d : ℝ) - σ)) := by gcongr
      _ = _ := by ring

/-- A chain `o.foldl (A ↦ A K_l Θ)` started from `X Y` is `X` times the chain started from `Y`. -/
private theorem VR1_foldl_mul {ι : Type*} [Fintype ι] (K : ℕ → Matrix ι ι ℂ)
    (Θ X Y : Matrix ι ι ℂ) (o : List ℕ) :
    o.foldl (fun A l => A * K l * Θ) (X * Y) = X * o.foldl (fun A l => A * K l * Θ) Y := by
  induction o generalizing Y with
  | nil => rfl
  | cons l o ih =>
    simp only [List.foldl_cons]
    rw [show X * Y * K l * Θ = X * (Y * K l * Θ) by simp only [Matrix.mul_assoc]]
    exact ih _

/-- `|(A B)_{xy}| ≤ N a b` for entries bounded by `a`, `b`, `N = |ι|`. -/
private theorem VR1_norm_mul_le {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ} {a b : ℝ}
    (hA : ∀ x y, ‖A x y‖ ≤ a) (hB : ∀ x y, ‖B x y‖ ≤ b) (x y : ι) :
    ‖(A * B) x y‖ ≤ (Fintype.card ι : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA x y)
  calc ‖∑ w, A x w * B w y‖ ≤ ∑ w, ‖A x w * B w y‖ := norm_sum_le _ _
    _ ≤ ∑ _w : ι, a * b := Finset.sum_le_sum fun w _ => by
        rw [norm_mul]; exact mul_le_mul (hA x w) (hB w y) (norm_nonneg _) ha
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **A crude comparison of two chains** whose `Θ` factors differ by at most `e` entrywise, all
entries being at most `1`: the chains differ by at most `(k + 1) N^{2k} e`, `k = |o|`,
`N = |ι|`. -/
private theorem VR1_crude {ι : Type*} [Fintype ι] (K : ℕ → Matrix ι ι ℂ)
    (Θ Θc : Matrix ι ι ℂ) {e : ℝ} (hN : 1 ≤ (Fintype.card ι : ℝ))
    (hΘ : ∀ x y, ‖Θ x y‖ ≤ 1) (hΘc : ∀ x y, ‖Θc x y‖ ≤ 1) (hdiff : ∀ x y, ‖Θ x y - Θc x y‖ ≤ e) :
    ∀ o : List ℕ, (∀ l ∈ o, ∀ x y, ‖K l x y‖ ≤ 1) →
      (∀ x y, ‖(o.foldl (fun A l => A * K l * Θc) Θc) x y‖ ≤
        (Fintype.card ι : ℝ) ^ (2 * o.length)) ∧
      ∀ x y, ‖(o.foldl (fun A l => A * K l * Θ) Θ) x y -
          (o.foldl (fun A l => A * K l * Θc) Θc) x y‖ ≤
        ((o.length : ℝ) + 1) * (Fintype.card ι : ℝ) ^ (2 * o.length) * e := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN0 : 0 ≤ N := by linarith
  intro o
  induction o with
  | nil =>
    intro _
    refine ⟨fun x y => ?_, fun x y => ?_⟩
    · simpa using hΘc x y
    · simpa using hdiff x y
  | cons l o ih =>
    intro hK
    obtain ⟨ih1, ih2⟩ := ih fun l' hl' => hK l' (List.mem_cons_of_mem _ hl')
    have hKl := hK l List.mem_cons_self
    have hcons : ∀ M : Matrix ι ι ℂ, (l :: o).foldl (fun A l => A * K l * M) M =
        (M * K l) * o.foldl (fun A l => A * K l * M) M := by
      intro M
      simp only [List.foldl_cons]
      exact VR1_foldl_mul K M (M * K l) M o
    rw [hcons Θ, hcons Θc]
    set P := o.foldl (fun A l => A * K l * Θ) Θ with hP
    set Pc := o.foldl (fun A l => A * K l * Θc) Θc with hPc
    have hΘcK : ∀ x y, ‖(Θc * K l) x y‖ ≤ N * (1 * 1) := VR1_norm_mul_le hΘc hKl
    have hΘK : ∀ x y, ‖(Θ * K l) x y‖ ≤ N * (1 * 1) := VR1_norm_mul_le hΘ hKl
    simp only [List.length_cons]
    have epow : N ^ (2 * (o.length + 1)) = N * (N * N ^ (2 * o.length)) := by ring
    refine ⟨fun x y => ?_, fun x y => ?_⟩
    · refine (VR1_norm_mul_le hΘcK ih1 x y).trans (le_of_eq ?_)
      rw [epow]; ring
    · have e1 : (Θ * K l * P) x y - (Θc * K l * Pc) x y =
          (Θ * K l * (P - Pc)) x y + ((Θ - Θc) * K l * Pc) x y := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]; ring
      rw [e1]
      have hsub : ∀ x y, ‖(Θ - Θc) x y‖ ≤ e := fun x y => by
        rw [Matrix.sub_apply]; exact hdiff x y
      have hsub' : ∀ x y, ‖(P - Pc) x y‖ ≤ ((o.length : ℝ) + 1) * N ^ (2 * o.length) * e :=
        fun x y => by rw [Matrix.sub_apply]; exact ih2 x y
      have hD : ∀ x y, ‖((Θ - Θc) * K l) x y‖ ≤ N * (e * 1) := VR1_norm_mul_le hsub hKl
      have h1 := VR1_norm_mul_le hΘK hsub' x y
      have h2 := VR1_norm_mul_le hD ih1 x y
      refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
      rw [epow]; push_cast; ring

end Torus

/-! ## The factors of the chains: `Θ` and `Σ̊` against `Θ_∞` and `Σ̊^∞` -/

section Factors

/-- [I, Lemma 7.4, (7.10)] for label kernels `K(E)` on `ℤ^d` with `ValZ.SelUnif κ N K`, with `W₀`
uniform in `|E| < 2 − κ`: `|(Θ_∞ ∗ K(E)_l)(v)| ≤ W^{-(l-2)d/2} ⟨v⟩^{-(d-σ)}`. -/
private theorem VR1_thetaSigmaZ (hd : 8 ≤ d) (P : Profile d) {κ : ℝ} (N : ℕ) (KI : ℝ → KerInf d)
    (hKI : ValZ.SelUnif κ N KI) (l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N) (hle : Even l) (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ v : Fin d → ℤ,
      ‖convZ (ThetaInf (Sinf P.ψ W)) (KI E l W) v‖ ≤
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - σ)) := by
  obtain ⟨C, Ws, hs⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  refine ValZ_uniform (κ := κ) (fun E W => ∀ v : Fin d → ℤ,
      ‖convZ (ThetaInf (Sinf P.ψ W)) (KI E l W) v‖ ≤
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - σ)))
    fun Esel hsel => ?_
  have hK : KerInfHyp (fun l W => KI (Esel W) l W) l := hKI Esel hsel l hl4 hlN hle
  obtain ⟨W₀, h⟩ := thetaSigmaInf d (by omega) P.ψ P.cψ (ValZ_shape P) C _ l hK σ hσ
  exact ⟨max W₀ Ws, fun W hW v => h W ((le_max_left _ _).trans hW) _
    (hs W ((le_max_right _ _).trans hW)) v⟩

/-- `x^s ≤ W^t` on `adm(c₀, c₁)` for `0 ≤ x ≤ 2L`, `0 ≤ s ≤ c₁ t / 4`, `W ≥ 2`. -/
private theorem VR1_Lpow {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) (hW : 2 ≤ W) {x s t : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 * L)
    (hs : 0 ≤ s) (hst : s ≤ c₁ * t / 4) : x ^ s ≤ (W : ℝ) ^ t := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hL2 : (2 : ℝ) ≤ L := hW2.trans hWL
  have hL0 : (0 : ℝ) < L := by linarith
  have hxL : x ≤ (L : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
  have hLc : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
    calc (L : ℝ) = ((L : ℝ) ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul hL0.le, mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ (1 / c₁) := Real.rpow_le_rpow (by positivity) hLW (by positivity)
  calc x ^ s ≤ ((L : ℝ) ^ (2 : ℝ)) ^ s := Real.rpow_le_rpow hx0 hxL hs
    _ = (L : ℝ) ^ (2 * s) := by rw [← Real.rpow_mul hL0.le]
    _ ≤ ((W : ℝ) ^ (1 / c₁)) ^ (2 * s) := Real.rpow_le_rpow hL0.le hLc (by positivity)
    _ = (W : ℝ) ^ (2 * s / c₁) := by rw [← Real.rpow_mul (by positivity)]; ring_nf
    _ ≤ (W : ℝ) ^ t := by
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        rw [div_le_iff₀ hc₁]; nlinarith

/-- `⟨[a]_L⟩ = ⟨a⟩` on the torus for `2 |a|_∞ < L`. -/
private theorem VR1_brk_zcast {L W : ℕ} [NeZero L] (a : Fin d → ℤ) (ha : 2 * zdInf a < L) :
    brk d L W 0 (zcast L a) = (zdInf a : ℝ) + W := by
  unfold brk
  rw [zero_sub, zdistInf_neg, VR1_zdistInf_zcast a ha]

/-- `[a]_L = 0` iff `a = 0`, for `2 |a|_∞ < L`. -/
private theorem VR1_zcast_eq_zero {L : ℕ} [NeZero L] (a : Fin d → ℤ) (ha : 2 * zdInf a < L) :
    zcast L a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← VR1Graph_zlift_zcast a ha, h, VR1Graph_zlift_zero]
  · rintro rfl; exact VR1Graph_zcast_zero L

/-- The torus `Θ` is translation invariant. -/
private theorem VR1_theta_TI (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) :
    VR1_TI (cmat (Theta (msc z) (Smat P.ψ W L))) := by
  intro x y
  simp only [cmat, Matrix.map_apply]
  rw [Chain_Theta_translate _ (Smat_transInv d L P.ψ W) (msc z) x y]

/-- `A ≤ L` and `A² ≤ L^{ε/2}` on `adm(c₀, c₁)` once `W ≥ max(A, (A²)^{2/ε})`. -/
private theorem VR1_win {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hW : max A ((A ^ (2 : ℝ)) ^ (2 / ε)) ≤ W) : A ≤ L ∧ A ^ (2 : ℝ) ≤ (L : ℝ) ^ (ε / 2) := by
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  refine ⟨(le_max_left _ _).trans (hW.trans hWL), ?_⟩
  have h1 : (A ^ (2 : ℝ)) ^ (2 / ε) ≤ L := (le_max_right _ _).trans (hW.trans hWL)
  calc A ^ (2 : ℝ) = ((A ^ (2 : ℝ)) ^ (2 / ε)) ^ (ε / 2) := by
        rw [← Real.rpow_mul (by positivity), show 2 / ε * (ε / 2) = 1 by field_simp,
          Real.rpow_one]
    _ ≤ (L : ℝ) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- `b^{-D} ≤ η W^{-4} W^{-1} b^{-(d-4)}` for `b ≥ W ≥ 1`, `W^{-2/c₁} ≤ η` and
`D = d + 2/c₁ + 1`. -/
private theorem VR1_tailD {c₁ η b : ℝ} {W : ℝ} (hc₁ : 0 < c₁) (hW : 1 ≤ W) (hbW : W ≤ b)
    (hη : W ^ (-(2 / c₁)) ≤ η) :
    b ^ (-((d : ℝ) + 2 / c₁ + 1)) ≤ η * W ^ (-4 : ℝ) * W ^ (-1 : ℝ) * b ^ (-((d : ℝ) - 4)) := by
  have hW0 : 0 < W := by linarith
  have hb0 : 0 < b := by linarith
  have e : b ^ (-((d : ℝ) + 2 / c₁ + 1)) = b ^ (-((d : ℝ) - 4)) * b ^ (-(2 / c₁ + 5)) := by
    rw [← Real.rpow_add hb0]; ring_nf
  have hc2 : 0 < 2 / c₁ := by positivity
  have h1 : b ^ (-(2 / c₁ + 5)) ≤ W ^ (-(2 / c₁ + 5)) :=
    Real.rpow_le_rpow_of_nonpos hW0 hbW (by linarith)
  have h2 : W ^ (-(2 / c₁ + 5)) = W ^ (-(2 / c₁)) * W ^ (-4 : ℝ) * W ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
  rw [e]
  calc b ^ (-((d : ℝ) - 4)) * b ^ (-(2 / c₁ + 5)) ≤
        b ^ (-((d : ℝ) - 4)) * (W ^ (-(2 / c₁)) * W ^ (-4 : ℝ) * W ^ (-1 : ℝ)) := by
        rw [← h2]; gcongr
    _ ≤ b ^ (-((d : ℝ) - 4)) * (η * W ^ (-4 : ℝ) * W ^ (-1 : ℝ)) := by gcongr
    _ = _ := by ring

/-- **The `Θ` factor.** The lift `θ` of the torus `Θ` cut at `R = ⌊L/(4(n+2))⌋` against `Θ_∞`:
`|θ(α) − Θ_∞(α)| ≤ 2 η W^{-4} ⟨α⟩^{-(d-4-δ)}` and `≤ η W^δ W^{-4} ⟨α⟩^{-(d-4)}` for all
`α ∈ ℤ^d` (for `|α| ≤ R` by [I, Lemma 7.2], beyond by `|Θ_∞(α)| ≤ W^{-2} ⟨α⟩^{-(d-2-δ')}` and
`W² R^{δ'-2} ≤ η`). -/
private theorem VR1_thetaDiff (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ α : Fin d → ℤ,
        ‖VR1_lift L (VR1_cut (L / (4 * (n + 2))) (cmat (Theta (msc z) (Smat P.ψ W L)))) α -
            ThetaInf (Sinf P.ψ W) α‖ ≤
          2 * z.im * (W : ℝ) ^ (-4 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 4 - δ)) ∧
        ‖VR1_lift L (VR1_cut (L / (4 * (n + 2))) (cmat (Theta (msc z) (Smat P.ψ W L)))) α -
            ThetaInf (Sinf P.ψ W) α‖ ≤
          z.im * (W : ℝ) ^ δ * (W : ℝ) ^ (-4 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 4)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨Ci, Wi, hi⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  obtain ⟨Ws, hsym⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  set Cm : ℕ → ℝ := fun k => max (C k) (Ci k) with hCm
  set δ' : ℝ := min (c₁ * δ / 8) (ε / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'1 : δ' ≤ c₁ * δ / 8 := min_le_left _ _
  have hδ'2 : δ' ≤ ε / 2 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := by nlinarith
  set D : ℝ := (d : ℝ) + 2 / c₁ + 1 with hD
  obtain ⟨W₂, h₂⟩ := Theta_sub_ThetaInf d (by omega) c₀ c₁ hc₀ hc₁ P.ψ P.cψ
    (profileShape_of_profile d P) Cm κ ε δ' D hκ hε hδ'0 (by positivity)
  obtain ⟨W₃, h₃⟩ := chainInf d (by omega) P.ψ P.cψ (ValZ_shape P) Cm (fun _ _ _ => 0) []
    (fun _ h => absurd h List.not_mem_nil) δ' hδ'0
  set A : ℝ := 8 * ((n : ℝ) + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max (max W₂ W₃) (max Wi Ws)) (max (max A ((A ^ (2 : ℝ)) ^ (2 / ε)))
    ((4 : ℝ) ^ (2 / δ))), fun W L _ hadm hW z hz α => ?_⟩
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hWi : Wi ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hWs : Ws ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hWA : max A ((A ^ (2 : ℝ)) ^ (2 / ε)) ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW4 : (4 : ℝ) ^ (2 / δ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  obtain ⟨hLA, hLε⟩ := VR1_win hc₀ hadm hA0 hε hWA
  have hW1 : (2 : ℝ) ≤ W := by
    have : (2 : ℝ) ≤ A := by rw [hA]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact this.trans ((le_max_left _ _).trans hWA)
  have hWn : 2 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hη := VR1Graph_eta_ge hc₀ hc₁ hε hadm (by omega) hz
  have hηpos : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hLn : 8 * (n + 2) ≤ L := by
    have : (8 * ((n : ℝ) + 2)) ≤ L := hLA
    exact_mod_cast this
  have hLε' : (8 * ((n : ℝ) + 2)) ^ (2 : ℝ) ≤ (L : ℝ) ^ (ε / 2) := hLε
  set R := L / (4 * (n + 2)) with hRdef
  have hcut0 := VR1Graph_cut_small hε hz hLn hLε' le_rfl (by linarith) (by norm_num)
  have hcut1 := VR1Graph_cut_small hε hz hLn hLε' hδ'0.le hδ'2 (by linarith)
  have hR5 : R ≤ L / 5 := Nat.div_le_div_left (by omega) (by norm_num)
  have hRpos : (0 : ℝ) < R := by
    have := VR1Graph_R_ge n L hLn
    have : (0 : ℝ) < (L : ℝ) / (8 * ((n : ℝ) + 2)) := by
      have : (0 : ℝ) < L := by linarith
      positivity
    linarith
  set b : ℝ := (zdInf α : ℝ) + W with hb
  have hbW : (W : ℝ) ≤ b := by rw [hb]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf α)]
  have hb0 : 0 < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hS := hsym W L hadm hWs
  have hCl := VR1Graph_symbolClose_mono (fun k => le_max_left (C k) (Ci k)) (hC W L hadm)
  have hIn := VR1Graph_infKernel_mono (fun k => le_max_right (C k) (Ci k)) (hi W hWi)
  have hWδ : 2 ≤ (W : ℝ) ^ (δ / 2) := by
    calc (2 : ℝ) = ((4 : ℝ) ^ (2 / δ)) ^ (δ / 4) := by
          rw [← Real.rpow_mul (by norm_num), show 2 / δ * (δ / 4) = 1 / 2 by field_simp; ring,
            show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ (W : ℝ) ^ (δ / 4) := Real.rpow_le_rpow (by positivity) hW4 (by positivity)
      _ ≤ (W : ℝ) ^ (δ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  by_cases hα : zdInf α ≤ R
  · -- inside the cut: [I, Lemma 7.2]
    have h2α : 2 * zdInf α < L := by
      have := Nat.div_mul_le_self L 5
      omega
    have hlift : VR1_lift L (VR1_cut R (cmat (Theta (msc z) (Smat P.ψ W L)))) α =
        (Theta (msc z) (Smat P.ψ W L) 0 (zcast L α) : ℂ) := by
      rw [VR1_lift_of_le _ (hα.trans hR5)]
      simp only [VR1_cut, Matrix.of_apply, sub_zero, VR1_zdistInf_zcast α h2α, if_pos hα, cmat,
        Matrix.map_apply]
    have hT := h₂ W L hadm hW2 _ hS hCl _ hIn z hz (zcast L α)
    rw [VR1Graph_zlift_zcast α h2α, VR1_zdistInf_zcast α h2α, ← hb] at hT
    rw [hlift, norm_sub_rev]
    have e1 : z.im / ((W : ℝ) ^ 4 * b ^ ((d : ℝ) - 4 - δ')) =
        z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4 - δ')) := by
      rw [Real.rpow_neg hb0.le, show (W : ℝ) ^ (-4 : ℝ) = ((W : ℝ) ^ 4)⁻¹ by
        rw [Real.rpow_neg hW0.le]; norm_num, div_eq_mul_inv, mul_inv]
      ring
    rw [e1] at hT
    have hDt := VR1_tailD (d := d) hc₁ (by linarith) hbW hη
    have hW1' : (W : ℝ) ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by norm_num)
    have hbd : b ^ (-((d : ℝ) - 4)) ≤ b ^ (-((d : ℝ) - 4 - δ)) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have hbd' : b ^ (-((d : ℝ) - 4 - δ')) ≤ b ^ (-((d : ℝ) - 4 - δ)) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have hηW : 0 ≤ z.im * (W : ℝ) ^ (-4 : ℝ) := by positivity
    have hbpow : b ^ δ' ≤ (W : ℝ) ^ (δ / 2) := by
      refine VR1_Lpow hc₀ hc₁ hadm hWn hb0.le ?_ hδ'0.le (by nlinarith)
      have : (zdInf α : ℝ) ≤ L := by
        have : zdInf α ≤ L := by omega
        exact_mod_cast this
      rw [hb]; linarith
    have e2 : b ^ (-((d : ℝ) - 4 - δ')) = b ^ δ' * b ^ (-((d : ℝ) - 4)) := by
      rw [← Real.rpow_add hb0]; ring_nf
    constructor
    · refine hT.trans ?_
      have : b ^ (-D) ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4 - δ)) := by
        refine hDt.trans ?_
        calc z.im * (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-1 : ℝ) * b ^ (-((d : ℝ) - 4))
            ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * 1 * b ^ (-((d : ℝ) - 4 - δ)) := by gcongr
          _ = _ := by ring
      have : z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4 - δ')) ≤
          z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4 - δ)) := by gcongr
      linarith
    · refine hT.trans ?_
      rw [e2]
      have h3 : z.im * (W : ℝ) ^ (-4 : ℝ) * (b ^ δ' * b ^ (-((d : ℝ) - 4))) ≤
          z.im * (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (δ / 2) * b ^ (-((d : ℝ) - 4))) := by gcongr
      have h4 : b ^ (-D) ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4)) := by
        refine hDt.trans ?_
        calc z.im * (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-1 : ℝ) * b ^ (-((d : ℝ) - 4))
            ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * 1 * b ^ (-((d : ℝ) - 4)) := by gcongr
          _ = _ := by ring
      have h5 : (W : ℝ) ^ (δ / 2) + 1 ≤ (W : ℝ) ^ δ := by
        have e5 : (W : ℝ) ^ δ = (W : ℝ) ^ (δ / 2) * (W : ℝ) ^ (δ / 2) := by
          rw [← Real.rpow_add hW0]; ring_nf
        have e6 : 2 * (W : ℝ) ^ (δ / 2) ≤ (W : ℝ) ^ (δ / 2) * (W : ℝ) ^ (δ / 2) :=
          mul_le_mul_of_nonneg_right hWδ (by positivity)
        rw [e5]; linarith
      have h6 : 0 ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4)) := by positivity
      calc _ ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (δ / 2) * b ^ (-((d : ℝ) - 4))) +
            z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4)) := add_le_add h3 h4
        _ = ((W : ℝ) ^ (δ / 2) + 1) * (z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by
            ring
        _ ≤ (W : ℝ) ^ δ * (z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by gcongr
        _ = _ := by ring
  · -- beyond the cut: `|Θ_∞(α)| ≤ W^{-2} ⟨α⟩^{-(d-2-δ')}`
    rw [not_le] at hα
    rw [VR1_lift_eq_zero (VR1_cut_supp R _) α hα, zero_sub, norm_neg]
    have hTi := h₃ W hW3 _ hIn α
    rw [VR1_mu_nil, one_mul] at hTi
    change ‖ThetaInf (Sinf P.ψ W) α‖ ≤ _ at hTi
    rw [← hb] at hTi
    have hRb : (R : ℝ) ≤ b := by
      rw [hb]
      have : (R : ℝ) < zdInf α := by exact_mod_cast hα
      linarith
    have hW2b : (W : ℝ) ^ (2 : ℝ) * b ^ ((0 : ℝ) - 2) ≤ z.im := by
      refine le_trans ?_ hcut0
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hRpos hRb (by norm_num))
        (by positivity)
    have hW2b' : (W : ℝ) ^ (2 : ℝ) * b ^ (δ' - 2) ≤ z.im := by
      refine le_trans ?_ hcut1
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hRpos hRb
        (show δ' - 2 ≤ 0 by linarith)) (by positivity)
    have eW : (W : ℝ) ^ (-2 : ℝ) = (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hW0]; norm_num
    constructor
    · refine hTi.trans ?_
      have e3 : b ^ (-((d : ℝ) - 2 - δ')) = b ^ ((0 : ℝ) - 2) * b ^ (-((d : ℝ) - 4 - δ')) := by
        rw [← Real.rpow_add hb0]; ring_nf
      rw [e3, eW]
      have hbd' : b ^ (-((d : ℝ) - 4 - δ')) ≤ b ^ (-((d : ℝ) - 4 - δ)) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
      calc (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (2 : ℝ) * (b ^ ((0 : ℝ) - 2) *
            b ^ (-((d : ℝ) - 4 - δ')))
          = (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (2 : ℝ) * b ^ ((0 : ℝ) - 2)) *
              b ^ (-((d : ℝ) - 4 - δ')) := by ring
        _ ≤ (W : ℝ) ^ (-4 : ℝ) * z.im * b ^ (-((d : ℝ) - 4 - δ)) := by gcongr
        _ ≤ 2 * z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4 - δ)) := by
            have : 0 ≤ z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4 - δ)) := by positivity
            linarith
    · refine hTi.trans ?_
      have e3 : b ^ (-((d : ℝ) - 2 - δ')) = b ^ (δ' - 2) * b ^ (-((d : ℝ) - 4)) := by
        rw [← Real.rpow_add hb0]; ring_nf
      rw [e3, eW]
      have h1δ : (1 : ℝ) ≤ (W : ℝ) ^ δ := Real.one_le_rpow (by linarith) hδ.le
      calc (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (2 : ℝ) * (b ^ (δ' - 2) * b ^ (-((d : ℝ) - 4)))
          = (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (2 : ℝ) * b ^ (δ' - 2)) * b ^ (-((d : ℝ) - 4)) := by
            ring
        _ ≤ (W : ℝ) ^ (-4 : ℝ) * z.im * b ^ (-((d : ℝ) - 4)) := by gcongr
        _ = 1 * (z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by ring
        _ ≤ (W : ℝ) ^ δ * (z.im * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by
            gcongr
        _ = z.im * (W : ℝ) ^ δ * (W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4)) := by ring

/-- The comparison `(V3)` of `Σ̊_l` on the torus with `Σ̊^∞_l` on `ℤ^d` at the order `l` (the
analogue of [I, (2.15)] for `Σ̊`): for every `τ > 0` there is `W₀` such that on the window
`|Σ̊_l(0, y)(z) − Σ̊^∞_l([y])(E)| ≤ η W^{-(l-4)d/2} W^{-6} ⟨y⟩^{-(2d-6-τ)}
  + 1_{y=0} L^τ η W^{-(l-2)d/2}`. -/
private def VR1_V3 (P : Profile d) (Sig : ℕ → Expansion 2) (c₀ c₁ κ ε : ℝ) (l : ℕ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
    ∀ z ∈ specDom κ ε W L, ∀ y : Zd d L,
      ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 y -
          ValZ.sigKer Sig P.ψ z.re l W (zlift y)‖ ≤
        z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            brk d L W 0 y ^ (-(2 * (d : ℝ) - 6 - τ)) +
          (if y = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)

/-- **The `Σ̊` factor.** Under `(V3)` at `l`, the lift `t` of `Σ̊_l` cut at `R = ⌊L/(4(n+2))⌋`
against `Σ̊^∞_l`: `|t(α) − Σ̊^∞_l(α)| ≤ η W^{-(l-4)d/2} W^{-6} ⟨α⟩^{-(2d-6-δ)}
  + 1_{α=0} L^δ η W^{-(l-2)d/2}`
for all `α` (for `|α| > R` from [I, (8.7)] for `Σ̊^∞_l` and `W² R^{-2} ≤ η`). -/
private theorem VR1_hDiff (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSh : SelfEnergyShapesUpTo Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hκ : 0 < κ) (hε : 0 < ε) (n l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N) (hle : Even l)
    (hV3 : VR1_V3 P Sig c₀ c₁ κ ε l) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ α : Fin d → ℤ,
        ‖VR1_lift L (VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) (4 * (n + 2)) l W L z) α -
            ValZ.sigKer Sig P.ψ z.re l W α‖ ≤
          z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              ((zdInf α : ℝ) + W) ^ (-(2 * (d : ℝ) - 6 - δ)) +
            (if α = 0 then (L : ℝ) ^ δ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨W₁, h₁⟩ := hV3 δ hδ
  obtain ⟨W₂, h₂⟩ := InfBound.sigKerBound (by omega) P Sig N hSh hκ l hl4 hlN hle δ hδ
  set A : ℝ := 8 * ((n : ℝ) + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max W₁ W₂) (max A ((A ^ (2 : ℝ)) ^ (2 / ε))), fun W L _ hadm hW z hz α => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWA : max A ((A ^ (2 : ℝ)) ^ (2 / ε)) ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨hLA, hLε⟩ := VR1_win hc₀ hadm hA0 hε hWA
  have hW1' : (2 : ℝ) ≤ W := by
    have : (2 : ℝ) ≤ A := by rw [hA]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact this.trans ((le_max_left _ _).trans hWA)
  have hW0 : (0 : ℝ) < W := by linarith
  have hLn : 8 * (n + 2) ≤ L := by
    have : (8 * ((n : ℝ) + 2)) ≤ L := hLA
    exact_mod_cast this
  have hcut0 := VR1Graph_cut_small hε hz hLn hLε le_rfl (by linarith) (by norm_num)
  set R := L / (4 * (n + 2)) with hRdef
  have hR5 : R ≤ L / 5 := Nat.div_le_div_left (by omega) (by norm_num)
  have hRpos : (0 : ℝ) < R := by
    have := VR1Graph_R_ge n L hLn
    have : (0 : ℝ) < (L : ℝ) / (8 * ((n : ℝ) + 2)) := by
      have : (0 : ℝ) < L := by
        have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        exact_mod_cast this
      positivity
    linarith
  set b : ℝ := (zdInf α : ℝ) + W with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  by_cases hα : zdInf α ≤ R
  · have h2α : 2 * zdInf α < L := by
      have := Nat.div_mul_le_self L 5
      omega
    have hlift : VR1_lift L (VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) (4 * (n + 2)) l W L z)
        α = sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 (zcast L α) := by
      rw [VR1_lift_of_le _ (hα.trans hR5)]
      simp only [VR1_cutFam, VR1_cut, Matrix.of_apply, sub_zero, VR1_zdistInf_zcast α h2α]
      exact if_pos hα
    have h := h₁ W L hadm hW1 z hz (zcast L α)
    rw [VR1Graph_zlift_zcast α h2α, VR1_brk_zcast α h2α, ← hb] at h
    rw [hlift]
    refine h.trans (le_of_eq ?_)
    congr 1
    by_cases h0 : α = 0
    · subst h0; simp [VR1Graph_zcast_zero]
    · rw [if_neg h0, if_neg (fun h' => h0 ((VR1_zcast_eq_zero α h2α).1 h'))]
  · rw [not_le] at hα
    have hα0 : α ≠ 0 := by
      rintro rfl
      simp [zdInf] at hα
    have hz0 : VR1_lift L (VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) (4 * (n + 2)) l W L z)
        α = 0 := VR1_lift_eq_zero (VR1_cut_supp _ _) α hα
    rw [hz0, zero_sub, norm_neg, if_neg hα0, add_zero]
    have h := (h₂ W hW2 z.re hz.1).1 α
    rw [if_neg hα0, add_zero, ← hb] at h
    refine h.trans ?_
    have hRb : (R : ℝ) ≤ b := by
      rw [hb]
      have : (R : ℝ) < zdInf α := by exact_mod_cast hα
      linarith
    have hW2b : (W : ℝ) ^ (2 : ℝ) * b ^ ((0 : ℝ) - 2) ≤ z.im :=
      le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hRpos hRb (by norm_num))
        (by positivity)) hcut0
    have e1 : (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
        b ^ (-(2 * (d : ℝ) - 4 - δ)) = (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          ((W : ℝ) ^ (2 : ℝ) * b ^ ((0 : ℝ) - 2)) * b ^ (-(2 * (d : ℝ) - 6 - δ)) := by
      have e2 : b ^ (-(2 * (d : ℝ) - 4 - δ)) =
          b ^ ((0 : ℝ) - 2) * b ^ (-(2 * (d : ℝ) - 6 - δ)) := by
        rw [← Real.rpow_add hb0]; ring_nf
      have e3 : (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) =
          (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) * (W : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
      rw [e2, ← mul_assoc, e3]; ring
    rw [e1]
    calc (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          ((W : ℝ) ^ (2 : ℝ) * b ^ ((0 : ℝ) - 2)) * b ^ (-(2 * (d : ℝ) - 6 - δ))
        ≤ (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) * z.im *
            b ^ (-(2 * (d : ℝ) - 6 - δ)) := by gcongr
      _ = _ := by ring

end Factors

/-! ## The cut chains on the torus -/

section CutChain

/-- The family `Σ̊` cut at `R = ⌊L/(4(n+2))⌋`. -/
private def VR1_KT (P : Profile d) (Sig : ℕ → Expansion 2) (n : ℕ) : KerFamily d :=
  VR1_cutFam (sigKer (smatVar P) (Renorm.sig Sig)) (4 * (n + 2))

/-- The torus `Θ` cut at `R = ⌊L/(4(n+2))⌋`. -/
private def VR1_Θc (P : Profile d) (n W L : ℕ) [NeZero L] (z : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  VR1_cut (L / (4 * (n + 2))) (cmat (Theta (msc z) (Smat P.ψ W L)))

/-- The chain of the cut factors. -/
private def VR1_CR (P : Profile d) (Sig : ℕ → Expansion 2) (n W L : ℕ) [NeZero L] (z : ℂ)
    (o : List ℕ) : Matrix (Zd d L) (Zd d L) ℂ :=
  VR1_chainR (VR1_Θc P n W L z) (fun l => VR1_KT P Sig n l W L z) o

/-- The chain of the cut `Σ̊` factors with the uncut `Θ`. -/
private def VR1_CK (P : Profile d) (Sig : ℕ → Expansion 2) (n W L : ℕ) [NeZero L] (z : ℂ)
    (o : List ℕ) : Matrix (Zd d L) (Zd d L) ℂ :=
  (detData (Smat P.ψ W L) z (fun l => VR1_KT P Sig n l W L z)).chain o

/-- `|Σ̊_l(x, y)| ≤ 1` on the window for `L ≥ L₀` ([I, (1.26)] for `Σ̊`, `G13.entrywise`). -/
private theorem VR1_KL_le_one (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N)
    (hle : Even l) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x y : Zd d L, ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z x y‖ ≤ 1 := by
  have hR := Renorm.selfEnergiesUpTo d hd P N Sig hSig
  have hlow : SelfEnergiesUpTo d (smatVar P) (Renorm.sig Sig) (l - 1) :=
    fun j hj4 hjl hje => hR j hj4 (by omega) hje
  obtain ⟨L₁, hL₁⟩ := G13.entrywise d hd P l (Renorm.sig Sig) hl4 hlow (hR l hl4 hlN hle).1 κ ε
    c₀ c₁ hκ hε hc₀ hc₁ hc c₁ hc₁
  refine ⟨max (L₁ : ℝ) 2, fun W L _ hadm hW z hz x y => ?_⟩
  have hW2 : (2 : ℝ) ≤ W := (le_max_right _ _).trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast (show (1 : ℝ) ≤ W by linarith)
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hLL : L₁ ≤ L := by
    have : (L₁ : ℝ) ≤ L := ((le_max_left _ _).trans hW).trans hWL
    exact_mod_cast this
  have hL0' : (0 : ℝ) < L := by linarith
  have hz' : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  obtain ⟨hs1, -⟩ := kerSymm_sigKer_smatVar d P (Renorm.sig Sig) l W L z hz' x (y - x)
  rw [add_sub_cancel] at hs1
  rw [hs1]
  have h := hL₁ W L hLL hadm z hz (y - x)
  refine h.trans ?_
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hl' : (4 : ℝ) ≤ l := by exact_mod_cast hl4
  have hB : bB d L W 0 (y - x) ≤ (W : ℝ) ^ (-(d : ℝ)) := by
    unfold bB
    have hb : (W : ℝ) ≤ (zdistInf d L (0 - (y - x)) : ℝ) + W := by
      linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (0 - (y - x)))]
    calc (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (0 - (y - x)) : ℝ) + W) ^ (2 - (d : ℝ))
        ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hW0 hb (by linarith))
            (by positivity)
      _ = _ := by rw [← Real.rpow_add hW0]; ring_nf
  have hB0 : 0 ≤ bB d L W 0 (y - x) := by unfold bB; positivity
  have h1 : (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by nlinarith)
  have h2 : (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) ≤ (W : ℝ) ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  have h3 : (W : ℝ) * (W : ℝ) ^ (-(d : ℝ)) ≤ 1 / 2 := by
    have : (W : ℝ) * (W : ℝ) ^ (-(d : ℝ)) = (W : ℝ) ^ (-((d : ℝ) - 1)) := by
      rw [show -((d : ℝ) - 1) = 1 + -(d : ℝ) by ring, Real.rpow_add hW0, Real.rpow_one]
    rw [this]
    calc (W : ℝ) ^ (-((d : ℝ) - 1)) ≤ (W : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / W := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := by gcongr
  have hBsq : bB d L W 0 (y - x) ^ 2 ≤ (W : ℝ) ^ (-(d : ℝ)) := by
    have hWd1 : (W : ℝ) ^ (-(d : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc bB d L W 0 (y - x) ^ 2 ≤ ((W : ℝ) ^ (-(d : ℝ))) ^ 2 := by gcongr
      _ ≤ (W : ℝ) ^ (-(d : ℝ)) := by
          rw [sq]; exact mul_le_of_le_one_left (by positivity) hWd1
  have hJ : (if y - x = 0 then (L : ℝ) ^ c₁ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) ≤
      (W : ℝ) * (W : ℝ) ^ (-(d : ℝ)) := by
    split_ifs
    · exact mul_le_mul hLW h2 (by positivity) (by positivity)
    · positivity
  have hM : (L : ℝ) ^ c₁ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 (y - x) ^ 2 ≤
      (W : ℝ) * (W : ℝ) ^ (-(d : ℝ)) := by
    calc (L : ℝ) ^ c₁ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 (y - x) ^ 2
        ≤ (W : ℝ) * 1 * (W : ℝ) ^ (-(d : ℝ)) := by gcongr
      _ = _ := by ring
  linarith

/-- `𝐃(κ, ε)` is empty for `ε ≥ 2` and `W ≥ 2`: there `W²/L^{2-ε} ≥ 4 > 1 ≥ η`. -/
private theorem VR1_eps_lt {κ ε : ℝ} {W L : ℕ} [NeZero L] (hW : (2 : ℝ) ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) : ε < 2 := by
  by_contra h
  push_neg at h
  have hL : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  have h1 : (L : ℝ) ^ (2 - ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have h2 : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) :=
    le_div_self (by positivity) (by positivity) h1
  have h3 := hz.2.1
  have h4 := hz.2.2
  nlinarith

/-- The torus `Θ` on the window: `|Θ_{xy}| ≤ 1`, and `|Θ_{xy}| ≤ R^{-D}` beyond the cut
`R = ⌊L/(4(n+2))⌋` (its range is `η^{-1/2} W^{1+ε/4} ≤ L^{1-ε/4} < R`; [I, (1.17)]). -/
private theorem VR1_theta_tail (P : Profile d) (hd : 8 ≤ d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε) (n : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x y : Zd d L, ‖cmat (Theta (msc z) (Smat P.ψ W L)) x y‖ ≤ 1 ∧
        (L / (4 * (n + 2)) < zdistInf d L (y - x) →
          ‖cmat (Theta (msc z) (Smat P.ψ W L)) x y‖ ≤ ((L / (4 * (n + 2)) : ℕ) : ℝ) ^ (-D)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨Ws, hsym⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₁, h₁⟩ := Theta_decay d (by omega) c₀ c₁ hc₀ hc₁ P.ψ P.cψ
    (profileShape_of_profile d P) C κ ε (ε / 4) D hκ hε (by positivity) (by linarith)
  set A : ℝ := 8 * ((n : ℝ) + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max W₁ Ws) (max (max A ((A ^ (2 : ℝ)) ^ (2 / ε))) (A ^ (4 / ε))),
    fun W L _ hadm hW z hz x y => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWs : Ws ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWA : max A ((A ^ (2 : ℝ)) ^ (2 / ε)) ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWA' : A ^ (4 / ε) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  obtain ⟨hLA, -⟩ := VR1_win hc₀ hadm hA0 hε hWA
  have hA2 : (2 : ℝ) ≤ A := by rw [hA]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hW2 : (2 : ℝ) ≤ W := hA2.trans ((le_max_left _ _).trans hWA)
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hL0 : (0 : ℝ) < L := by linarith
  have hLn : 8 * (n + 2) ≤ L := by
    have : (8 * ((n : ℝ) + 2)) ≤ L := hLA
    exact_mod_cast this
  have hθ := h₁ W L hadm hW1 _ (hsym W L hadm hWs) (hC W L hadm) z hz x y
  have hη : (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im := hz.2.1
  have hηpos : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hε2 : ε < 2 := VR1_eps_lt hW2 hz
  have hnorm : ‖cmat (Theta (msc z) (Smat P.ψ W L)) x y‖ = |Theta (msc z) (Smat P.ψ W L) x y| := by
    simp [cmat, Complex.norm_real]
  rw [hnorm]
  unfold thetaBound at hθ
  have hb : (W : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + W := by
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]
  have htail : ((zdistInf d L (x - y) : ℝ) + W) ^ (-D) ≤ 1 / 2 := by
    calc ((zdistInf d L (x - y) : ℝ) + W) ^ (-D) ≤ (W : ℝ) ^ (-D) :=
          Real.rpow_le_rpow_of_nonpos hW0 hb (by linarith)
      _ ≤ (W : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / W := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := by gcongr
  constructor
  · refine hθ.trans ?_
    have hfirst : (if (zdistInf d L (x - y) : ℝ) ≤ z.im ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + ε / 4)
        then (W : ℝ) ^ (ε / 4) * bB d L W x y else 0) ≤ 1 / 2 := by
      split_ifs
      · have hB : bB d L W x y ≤ (W : ℝ) ^ (-(d : ℝ)) := by
          unfold bB
          calc (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))
              ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hW0 hb (by linarith))
                  (by positivity)
            _ = _ := by rw [← Real.rpow_add hW0]; ring_nf
        calc (W : ℝ) ^ (ε / 4) * bB d L W x y ≤ (W : ℝ) ^ (ε / 4) * (W : ℝ) ^ (-(d : ℝ)) := by
              gcongr
          _ = (W : ℝ) ^ (ε / 4 - d) := by rw [← Real.rpow_add hW0]; ring_nf
          _ ≤ (W : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hε2])
          _ = 1 / W := by rw [Real.rpow_neg_one, one_div]
          _ ≤ 1 / 2 := by gcongr
      · norm_num
    linarith
  · intro hR
    refine hθ.trans ?_
    have hxy : zdistInf d L (x - y) = zdistInf d L (y - x) := by
      rw [← neg_sub, zdistInf_neg]
    rw [hxy]
    set R := L / (4 * (n + 2)) with hRdef
    have hRge := VR1Graph_R_ge n L hLn
    have hRgt : (R : ℝ) < zdistInf d L (y - x) := by exact_mod_cast hR
    -- the range of `Θ` is below the cut
    have hrange : z.im ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + ε / 4) < zdistInf d L (y - x) := by
      have h1 : z.im ^ (-(1 / 2 : ℝ)) ≤ ((W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hη (by norm_num)
      have h2 : ((W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε)) ^ (-(1 / 2 : ℝ)) =
          (W : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (1 - ε / 2) := by
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hW0.le, ← Real.rpow_mul hL0.le, div_eq_mul_inv, ← Real.rpow_neg hL0.le]
        have e1 : ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 := by norm_num
        have e2 : -((2 - ε) * -(1 / 2 : ℝ)) = 1 - ε / 2 := by ring
        rw [e1, e2]
      have h3 : (W : ℝ) ^ (ε / 4) ≤ (L : ℝ) ^ (ε / 4) :=
        Real.rpow_le_rpow hW0.le hWL (by positivity)
      have h4 : A * (L : ℝ) ^ (1 - ε / 4) ≤ L := by
        have hAL : A ≤ (L : ℝ) ^ (ε / 4) := by
          calc A = (A ^ (4 / ε)) ^ (ε / 4) := by
                rw [← Real.rpow_mul (by positivity), show 4 / ε * (ε / 4) = 1 by field_simp,
                  Real.rpow_one]
            _ ≤ (W : ℝ) ^ (ε / 4) := Real.rpow_le_rpow (by positivity) hWA' (by positivity)
            _ ≤ _ := h3
        calc A * (L : ℝ) ^ (1 - ε / 4) ≤ (L : ℝ) ^ (ε / 4) * (L : ℝ) ^ (1 - ε / 4) := by gcongr
          _ = L := by rw [← Real.rpow_add hL0]; norm_num
      have h5 : z.im ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + ε / 4) ≤ (L : ℝ) ^ (1 - ε / 4) := by
        calc z.im ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + ε / 4)
            ≤ (W : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (1 - ε / 2) * (W : ℝ) ^ (1 + ε / 4) := by
              rw [← h2]; gcongr
          _ = (L : ℝ) ^ (1 - ε / 2) * (W : ℝ) ^ (ε / 4) := by
              rw [mul_comm ((W : ℝ) ^ (-1 : ℝ)), mul_assoc, ← Real.rpow_add hW0]; ring_nf
          _ ≤ (L : ℝ) ^ (1 - ε / 2) * (L : ℝ) ^ (ε / 4) := by gcongr
          _ = (L : ℝ) ^ (1 - ε / 4) := by rw [← Real.rpow_add hL0]; ring_nf
      have h6 : (L : ℝ) ^ (1 - ε / 4) ≤ L / A := by
        rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    rw [if_neg (not_le.2 hrange), zero_add]
    have hRpos : (0 : ℝ) < R := by
      have : (0 : ℝ) < (L : ℝ) / (8 * ((n : ℝ) + 2)) := by positivity
      linarith
    calc ((zdistInf d L (y - x) : ℝ) + W) ^ (-D) ≤ (R : ℝ) ^ (-D) :=
          Real.rpow_le_rpow_of_nonpos hRpos (by linarith) (by linarith)
      _ = _ := rfl

/-- `(2K + 2) ⌊L/(4(3K + 3))⌋ ≤ ⌊L/5⌋`. -/
private theorem VR1_R_mul (K L : ℕ) : (2 * K + 2) * (L / (4 * (3 * K + 1 + 2))) ≤ L / 5 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 := Nat.div_mul_le_self L (4 * (3 * K + 1 + 2))
  have h2 : (2 * K + 2) * 5 ≤ 4 * (3 * K + 1 + 2) := by omega
  calc (2 * K + 2) * (L / (4 * (3 * K + 1 + 2))) * 5
      = (2 * K + 2) * 5 * (L / (4 * (3 * K + 1 + 2))) := by ring
    _ ≤ 4 * (3 * K + 1 + 2) * (L / (4 * (3 * K + 1 + 2))) := Nat.mul_le_mul_right _ h2
    _ = L / (4 * (3 * K + 1 + 2)) * (4 * (3 * K + 1 + 2)) := by ring
    _ ≤ L := h1

/-- The cut `Σ̊` factor is translation invariant with row supported in the cut. -/
private theorem VR1_KT_TI (P : Profile d) (Sig : ℕ → Expansion 2) (n l W L : ℕ) [NeZero L]
    (z : ℂ) (hz : 0 < z.im) :
    VR1_TI (VR1_KT P Sig n l W L z) ∧ VR1_Supp (VR1_KT P Sig n l W L z) (L / (4 * (n + 2))) := by
  refine ⟨VR1_cut_TI _ fun x y => ?_, VR1_cut_supp _ _⟩
  obtain ⟨h, -⟩ := kerSymm_sigKer_smatVar d P (Renorm.sig Sig) l W L z hz x (y - x)
  rwa [add_sub_cancel] at h

/-- `|Σ̊_l 1(cut)| ≤ 1` on the window, from `VR1_KL_le_one`. -/
private theorem VR1_KT_le_one (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (n l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N)
    (hle : Even l) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ (L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L, ‖VR1_KT P Sig n l W L z x y‖ ≤ 1 := by
  obtain ⟨W₀, h⟩ := VR1_KL_le_one hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l hl4 hlN hle
  refine ⟨W₀, fun W hW L _ hadm z hz x y => ?_⟩
  simp only [VR1_KT, VR1_cutFam, VR1_cut, Matrix.of_apply]
  split_ifs
  · exact h W L hadm hW z hz x y
  · simp

/-- **The crude comparison of the cut chains.** For `|o| ≤ K` and `B ≥ 0`, on the window for
`W ≥ W₀`: the chains with the uncut and with the cut `Θ` (both with the cut `Σ̊`) differ by at most
`L^{-B}` entrywise (`VR1_crude`: `Θ` beyond the cut is at most `R^{-D}`). -/
private theorem VR1_crudeCR (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (K : ℕ) (o : List ℕ)
    (ho : ∀ j ∈ o, 4 ≤ j ∧ j ≤ N ∧ Even j) (hoK : o.length ≤ K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x y, ‖VR1_CK P Sig (3 * K + 1) W L z o x y - VR1_CR P Sig (3 * K + 1) W L z o x y‖ ≤
        (L : ℝ) ^ (-B) := by
  set n := 3 * K + 1 with hn
  set D : ℝ := B + 2 * d * K + 1 with hD
  have hD1 : 1 ≤ D := by
    have : (0 : ℝ) ≤ 2 * d * K := by positivity
    rw [hD]; linarith
  obtain ⟨W₁, h₁⟩ := VR1_theta_tail P hd c₀ c₁ κ ε hc₀ hc₁ hκ hε n D hD1
  obtain ⟨W₂, h₂⟩ := exists_W0_list (P := fun l W => ∀ (L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L, ‖VR1_KT P Sig n l W L z x y‖ ≤ 1) o
    (fun l hl => VR1_KT_le_one hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n l (ho l hl).1
      (ho l hl).2.1 (ho l hl).2.2)
  set A : ℝ := 8 * ((n : ℝ) + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max (max W₁ W₂) (max A (((K : ℝ) + 1) * A ^ D)), fun W L _ hadm hW z hz x y => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWA : A ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWK : ((K : ℝ) + 1) * A ^ D ≤ W :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hA2 : (2 : ℝ) ≤ A := by rw [hA]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hL2 : (2 : ℝ) ≤ L := hA2.trans (hWA.trans hWL)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLn : 8 * (n + 2) ≤ L := by
    have : (8 * ((n : ℝ) + 2)) ≤ L := hWA.trans hWL
    exact_mod_cast this
  set R := L / (4 * (n + 2)) with hRdef
  have hRge := VR1Graph_R_ge n L hLn
  have hRpos : (0 : ℝ) < R := by
    have : (0 : ℝ) < (L : ℝ) / A := by positivity
    rw [hA] at this; linarith
  set Θm := cmat (Theta (msc z) (Smat P.ψ W L)) with hΘm
  have hΘ : ∀ x y, ‖Θm x y‖ ≤ 1 := fun x y => (h₁ W L hadm hW1 z hz x y).1
  have hΘc : ∀ x y, ‖VR1_Θc P n W L z x y‖ ≤ 1 := by
    intro x y
    simp only [VR1_Θc, VR1_cut, Matrix.of_apply]
    split_ifs
    · exact hΘ x y
    · simp
  have hdiff : ∀ x y, ‖Θm x y - VR1_Θc P n W L z x y‖ ≤ (R : ℝ) ^ (-D) := by
    intro x y
    simp only [VR1_Θc, VR1_cut, Matrix.of_apply]
    split_ifs with h
    · rw [sub_self, norm_zero]; positivity
    · rw [sub_zero]; exact (h₁ W L hadm hW1 z hz x y).2 (by omega)
  have hN : (1 : ℝ) ≤ (Fintype.card (Zd d L) : ℝ) := by
    rw [card_Zd]; push_cast; exact one_le_pow₀ (by linarith)
  obtain ⟨-, hc'⟩ := VR1_crude (fun l => VR1_KT P Sig n l W L z) Θm (VR1_Θc P n W L z)
    hN hΘ hΘc hdiff o (fun l hl => h₂ W hW2 l hl L hadm z hz)
  refine (hc' x y).trans ?_
  rw [card_Zd]
  push_cast
  -- `(k + 1) L^{2dk} R^{-D} ≤ L^{-B}`
  have hRD : (R : ℝ) ^ (-D) ≤ A ^ D * (L : ℝ) ^ (-D) := by
    calc (R : ℝ) ^ (-D) ≤ ((L : ℝ) / A) ^ (-D) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by rw [hA]; exact hRge)
            (show -D ≤ 0 by linarith [hD1])
      _ = A ^ D * (L : ℝ) ^ (-D) := by
          rw [Real.div_rpow hL0.le hA0, Real.rpow_neg hL0.le, Real.rpow_neg hA0, div_inv_eq_mul]
          ring
  have hoK' : (o.length : ℝ) ≤ K := by exact_mod_cast hoK
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hLk : ((L : ℝ) ^ d) ^ (2 * o.length) ≤ (L : ℝ) ^ (2 * (d : ℝ) * K) := by
    rw [← pow_mul, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    push_cast
    nlinarith
  have hk : ((o.length : ℝ) + 1) ≤ (K : ℝ) + 1 := by
    have : (o.length : ℝ) ≤ K := by exact_mod_cast hoK
    linarith
  have hfin : ((K : ℝ) + 1) * A ^ D ≤ L := hWK.trans hWL
  calc ((o.length : ℝ) + 1) * ((L : ℝ) ^ d) ^ (2 * o.length) * (R : ℝ) ^ (-D)
      ≤ ((K : ℝ) + 1) * (L : ℝ) ^ (2 * (d : ℝ) * K) * (A ^ D * (L : ℝ) ^ (-D)) := by
        gcongr
    _ = (((K : ℝ) + 1) * A ^ D) * ((L : ℝ) ^ (2 * (d : ℝ) * K) * (L : ℝ) ^ (-D)) := by ring
    _ ≤ (L : ℝ) * ((L : ℝ) ^ (2 * (d : ℝ) * K) * (L : ℝ) ^ (-D)) := by gcongr
    _ = (L : ℝ) ^ (-B) := by
        rw [← Real.rpow_add hL0, mul_comm, ← Real.rpow_add_one hL0.ne']
        congr 1; rw [hD]; ring

/-- `L^{-B} ≤ W^{-a} b^{-e}` for `2 ≤ W ≤ L`, `1 ≤ b ≤ 2L`, `a, e ≥ 0`, `B ≥ a + 2e`. -/
private theorem VR1_small {W L b a e B : ℝ} (hW : 2 ≤ W) (hWL : W ≤ L) (hb : 1 ≤ b)
    (hbL : b ≤ 2 * L) (ha : 0 ≤ a) (he : 0 ≤ e) (hB : a + 2 * e ≤ B) :
    L ^ (-B) ≤ W ^ (-a) * b ^ (-e) := by
  have hL0 : 0 < L := by linarith
  have hW0 : 0 < W := by linarith
  have h1 : L ^ (-a) ≤ W ^ (-a) := Real.rpow_le_rpow_of_nonpos hW0 hWL (by linarith)
  have h2 : (L ^ (2 : ℝ)) ^ (-e) ≤ b ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by rw [Real.rpow_two]; nlinarith) (by linarith)
  have h3 : L ^ (-B) ≤ L ^ (-a) * (L ^ (2 : ℝ)) ^ (-e) := by
    rw [← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact h3.trans (mul_le_mul h1 h2 (by positivity) (by positivity))

/-- The scaling order of a label with entries `≥ 2` is at least `2`. -/
private theorem VR1_ord_ge (o : List ℕ) (ho : ∀ j ∈ o, 2 ≤ j) :
    (2 : ℝ) ≤ (((Kind.theta o).ord : ℤ) : ℝ) := by
  induction o with
  | nil => simp [Kind.ord]
  | cons j o ih =>
    have h1 := RenormDiff_ord_cons j o
    have h2 := ih fun j' h => ho j' (List.mem_cons_of_mem _ h)
    have h3 : (2 : ℝ) ≤ j := by exact_mod_cast ho j List.mem_cons_self
    linarith

/-- `B_{0,[α]} = W^{-2} ⟨α⟩^{-(d-2)}` for `2|α| < L`. -/
private theorem VR1_bB_zcast {L W : ℕ} [NeZero L] (α : Fin d → ℤ) (hα : 2 * zdInf α < L) :
    bB d L W 0 (zcast L α) = (W : ℝ) ^ (-2 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 2)) := by
  unfold bB
  rw [zero_sub, zdistInf_neg, VR1_zdistInf_zcast α hα]
  congr 2; ring

/-- **The cut chains on `ℤ^d`.** For `|o| + 1 ≤ K` and `0 < σ ≤ 1`, on the window for `W ≥ W₀`:
the lift of the cut chain `Θ_c Σ̊_{o₁} ⋯ Θ_c` is at most
`2 W^σ W^{-(k(o)-2)d/2} W^{-2} ⟨α⟩^{-(d-2)}`
(`chain` for the cut family), and the lift of the cut chain times the cut `Σ̊_l` is at most
`2 W^σ W^{-(k(o)-2)d/2} W^{-(l-2)d/2} ⟨α⟩^{-(d-σ)}` (`VR1_chainK`). -/
private theorem VR1_TB (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (K : ℕ) (o : List ℕ) (l : ℕ)
    (ho : ∀ j ∈ o, 4 ≤ j ∧ j ≤ N ∧ Even j) (hl : 4 ≤ l ∧ l ≤ N ∧ Even l)
    (hoK : o.length + 1 ≤ K) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      (∀ α, ‖VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o) α‖ ≤
        2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          (W : ℝ) ^ (-2 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 2))) ∧
      (∀ α, ‖VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o * VR1_KT P Sig (3 * K + 1) l W L z) α‖ ≤
        2 * (W : ℝ) ^ σ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - σ))) := by
  set n := 3 * K + 1 with hn
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hKT : ∀ j, 4 ≤ j → j ≤ N → Even j →
      KerSymm (VR1_KT P Sig n) j ∧ KerBound (VR1_KT P Sig n) j :=
    fun j h4 hN he => VR1_kerBound_cut hd P Sig N hSig (4 * (n + 2)) (by omega) j h4 hN he
  obtain ⟨W₁, h₁⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (VR1_KT P Sig n) o
    (fun j hj => hKT j (ho j hj).1 (ho j hj).2.1 (ho j hj).2.2) σ hσ
  obtain ⟨W₂, h₂⟩ := VR1_chainK hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (VR1_KT P Sig n) l
    (hKT l hl.1 hl.2.1 hl.2.2) o (fun j hj => hKT j (ho j hj).1 (ho j hj).2.1 (ho j hj).2.2) σ hσ
  have hord := VR1_ord_ge o fun j hj => by have := (ho j hj).1; omega
  set B : ℝ := (((Kind.theta o).ord : ℤ) : ℝ) * d + (l : ℝ) * d + 3 * d + 10 with hB
  have hl4 : (4 : ℝ) ≤ l := by exact_mod_cast hl.1
  have hB0 : 0 ≤ B := by rw [hB]; nlinarith
  obtain ⟨W₃, h₃⟩ := VR1_crudeCR hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K o ho
    (by omega) B hB0
  obtain ⟨W₄, h₄⟩ := VR1_KT_le_one hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n l hl.1 hl.2.1
    hl.2.2
  refine ⟨max (max (max W₁ W₂) (max W₃ W₄)) 2, fun W L _ hadm hW z hz => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hW4 : W₄ ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hW
  have hW2' : (2 : ℝ) ≤ W := (le_max_right _ _).trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWσ : (1 : ℝ) ≤ (W : ℝ) ^ σ := Real.one_le_rpow (by linarith) hσ.le
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hL0 : (0 : ℝ) < L := by linarith
  set μo := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hμo
  set μl := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hμl
  have hcr := h₃ W L hadm hW3 z hz
  have hkt := h₄ W hW4 L hadm z hz
  have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  constructor
  · intro α
    by_cases hα : zdInf α ≤ L / 5
    · have h2α : 2 * zdInf α < L := by
        have := Nat.div_mul_le_self L 5
        have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        omega
      rw [VR1_lift_of_le _ hα]
      have hc1 := h₁ W L hadm hW1 z hz 0 (zcast L α)
      change ‖VR1_CK P Sig n W L z o 0 (zcast L α)‖ ≤ _ at hc1
      rw [VR1_bB_zcast α h2α] at hc1
      have hb1 : (1 : ℝ) ≤ (zdInf α : ℝ) + W := by
        linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf α)]
      have hbL : (zdInf α : ℝ) + W ≤ 2 * L := by
        have : (zdInf α : ℝ) ≤ L := by
          have : zdInf α ≤ L := by omega
          exact_mod_cast this
        linarith
      have hsm := VR1_small (a := (((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) + 2)
        (e := (d : ℝ) - 2) (B := B) hW2' hWL hb1 hbL (by nlinarith) (by linarith) (by
          rw [hB]; nlinarith)
      have e1 : (W : ℝ) ^ (-((((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) + 2)) = μo *
          (W : ℝ) ^ (-2 : ℝ) := by
        rw [hμo, ← Real.rpow_add hW0]; ring_nf
      rw [e1] at hsm
      have htri : ‖VR1_CR P Sig n W L z o 0 (zcast L α)‖ ≤
          ‖VR1_CK P Sig n W L z o 0 (zcast L α)‖ +
            ‖VR1_CK P Sig n W L z o 0 (zcast L α) - VR1_CR P Sig n W L z o 0 (zcast L α)‖ := by
        have := norm_sub_le (VR1_CK P Sig n W L z o 0 (zcast L α))
          (VR1_CK P Sig n W L z o 0 (zcast L α) - VR1_CR P Sig n W L z o 0 (zcast L α))
        rwa [sub_sub_cancel] at this
      have hX0 : 0 ≤ μo * (W : ℝ) ^ (-2 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 2)) := by
        positivity
      calc _ ≤ _ := htri
        _ ≤ (W : ℝ) ^ σ * μo * ((W : ℝ) ^ (-2 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 2))) +
            (L : ℝ) ^ (-B) := add_le_add hc1 (hcr 0 (zcast L α))
        _ ≤ (W : ℝ) ^ σ * μo * ((W : ℝ) ^ (-2 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 2))) +
            (W : ℝ) ^ σ * (μo * (W : ℝ) ^ (-2 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 2))) := by
            gcongr
            exact hsm.trans (le_mul_of_one_le_left hX0 hWσ)
        _ = _ := by ring
    · rw [VR1_lift, if_neg hα, norm_zero]; positivity
  · intro α
    by_cases hα : zdInf α ≤ L / 5
    · have h2α : 2 * zdInf α < L := by
        have := Nat.div_mul_le_self L 5
        have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        omega
      rw [VR1_lift_of_le _ hα]
      have hc2 := h₂ W L hadm hW2 z hz 0 (zcast L α)
      change ‖(VR1_CK P Sig n W L z o * VR1_KT P Sig n l W L z) 0 (zcast L α)‖ ≤ _ at hc2
      rw [VR1_brk_zcast α h2α] at hc2
      have hb1 : (1 : ℝ) ≤ (zdInf α : ℝ) + W := by
        linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf α)]
      have hbL : (zdInf α : ℝ) + W ≤ 2 * L := by
        have : (zdInf α : ℝ) ≤ L := by
          have : zdInf α ≤ L := by omega
          exact_mod_cast this
        linarith
      have hsm := VR1_small (a := (((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) +
        (((l : ℝ) - 2) * d / 2)) (e := (d : ℝ) - σ) (B := B - d) hW2' hWL hb1 hbL (by nlinarith)
        (by linarith) (by rw [hB]; nlinarith)
      have e1 : (W : ℝ) ^ (-((((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) +
          (((l : ℝ) - 2) * d / 2))) = μo * μl := by
        rw [hμo, hμl, ← Real.rpow_add hW0]; ring_nf
      rw [e1] at hsm
      have hmul : ∀ x y, ‖((VR1_CK P Sig n W L z o - VR1_CR P Sig n W L z o) *
          VR1_KT P Sig n l W L z) x y‖ ≤ (Fintype.card (Zd d L) : ℝ) * ((L : ℝ) ^ (-B) * 1) :=
        VR1_norm_mul_le (fun x y => by rw [Matrix.sub_apply]; exact hcr x y) hkt
      have hN : (Fintype.card (Zd d L) : ℝ) * ((L : ℝ) ^ (-B) * 1) = (L : ℝ) ^ (-(B - d)) := by
        rw [card_Zd, mul_one]; push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_add hL0]; ring_nf
      have htri : ‖(VR1_CR P Sig n W L z o * VR1_KT P Sig n l W L z) 0 (zcast L α)‖ ≤
          ‖(VR1_CK P Sig n W L z o * VR1_KT P Sig n l W L z) 0 (zcast L α)‖ +
            ‖((VR1_CK P Sig n W L z o - VR1_CR P Sig n W L z o) *
              VR1_KT P Sig n l W L z) 0 (zcast L α)‖ := by
        rw [Matrix.sub_mul, Matrix.sub_apply]
        have := norm_sub_le ((VR1_CK P Sig n W L z o * VR1_KT P Sig n l W L z) 0 (zcast L α))
          ((VR1_CK P Sig n W L z o * VR1_KT P Sig n l W L z) 0 (zcast L α) -
            (VR1_CR P Sig n W L z o * VR1_KT P Sig n l W L z) 0 (zcast L α))
        rwa [sub_sub_cancel] at this
      have hX0 : 0 ≤ μo * μl * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - σ)) := by positivity
      calc _ ≤ _ := htri
        _ ≤ (W : ℝ) ^ σ * (μo * μl) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - σ)) +
            (L : ℝ) ^ (-(B - d)) := by rw [← hN]; exact add_le_add hc2 (hmul _ _)
        _ ≤ (W : ℝ) ^ σ * (μo * μl) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - σ)) +
            (W : ℝ) ^ σ * (μo * μl * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - σ))) := by
            gcongr
            exact hsm.trans (le_mul_of_one_le_left hX0 hWσ)
        _ = _ := by ring
    · rw [VR1_lift, if_neg hα, norm_zero]; positivity

/-- `μ_{o ++ [l]} = μ_o μ_l`. -/
private theorem VR1_mu_append {W : ℝ} (hW : 0 < W) (o : List ℕ) (l : ℕ) :
    W ^ (-((((Kind.theta (o ++ [l])).ord : ℤ) : ℝ) - 2) * d / 2) =
      W ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) * W ^ (-(((l : ℝ) - 2) * d / 2)) := by
  rw [← Real.rpow_add hW]
  congr 1
  simp only [Kind.ord, List.sum_append, List.sum_cons, List.sum_nil, List.length_append,
    List.length_cons, List.length_nil]
  push_cast
  ring

/-- The labels with entries even in `[4, N]` satisfy `labelOK N`. -/
private theorem VR1_labelOK {N : ℕ} {o : List ℕ} (ho : ∀ j ∈ o, 4 ≤ j ∧ j ≤ N ∧ Even j) :
    labelOK N o = true := by
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro j hj
  obtain ⟨h4, hN, he⟩ := ho j hj
  exact ⟨⟨h4, hN⟩, Nat.even_iff.1 he⟩

/-- The cut chains are translation invariant with rows supported in `(2k + 1) R`, and their
lifts are the chains on `ℤ^d` of the lifts: `X_{o ++ [l]} = (X_o ∗ t_l) ∗ θ` and
`lift(CR_o Σ̊_l) = X_o ∗ t_l`. -/
private theorem VR1_X_append (P : Profile d) (Sig : ℕ → Expansion 2) (K W L : ℕ) [NeZero L]
    (z : ℂ) (hz : 0 < z.im) (o : List ℕ) (l : ℕ) (hoK : o.length + 1 ≤ K) :
    VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z (o ++ [l])) =
      convZ (convZ (VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o))
        (VR1_lift L (VR1_KT P Sig (3 * K + 1) l W L z))) (VR1_lift L (VR1_Θc P (3 * K + 1) W L z)) ∧
    VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o * VR1_KT P Sig (3 * K + 1) l W L z) =
      convZ (VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o))
        (VR1_lift L (VR1_KT P Sig (3 * K + 1) l W L z)) := by
  set n := 3 * K + 1 with hn
  set R := L / (4 * (n + 2)) with hR
  have hΘ : VR1_TI (VR1_Θc P n W L z) := VR1_cut_TI _ (VR1_theta_TI P W L z)
  have hΘs : VR1_Supp (VR1_Θc P n W L z) R := VR1_cut_supp _ _
  have hK : ∀ j, VR1_TI (VR1_KT P Sig n j W L z) := fun j => (VR1_KT_TI P Sig n j W L z hz).1
  have hKs : ∀ j, VR1_Supp (VR1_KT P Sig n j W L z) R := fun j => (VR1_KT_TI P Sig n j W L z hz).2
  have hRK : (2 * K + 2) * R ≤ L / 5 := VR1_R_mul K L
  have hm1 : (2 * o.length + 3) * R ≤ (2 * K + 2) * R := Nat.mul_le_mul_right R (by omega)
  have h1 := VR1_lift_chain hΘ hΘs hK hKs (o ++ [l]) _ R hΘ hΘs (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    have : R + 2 * (o.length + (0 + 1)) * R = (2 * o.length + 3) * R := by ring
    omega)
  have h2 := VR1_lift_chain hΘ hΘs hK hKs o _ R hΘ hΘs (by
    have : R + 2 * o.length * R ≤ (2 * o.length + 3) * R := by nlinarith
    omega)
  have h3 := VR1_lift_mul h2.1 (hK l) h2.2.1 (hKs l) (by
    have : R + 2 * o.length * R + R ≤ (2 * o.length + 3) * R := by nlinarith
    omega)
  refine ⟨?_, h3.2.2⟩
  change VR1_lift L ((o ++ [l]).foldl (fun A j => A * VR1_KT P Sig n j W L z * VR1_Θc P n W L z)
    (VR1_Θc P n W L z)) = _
  rw [h1.2.2, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change convZ (convZ (o.foldl _ _) _) _ = _
  rw [← h2.2.2]
  rfl

end CutChain

/-! ## The chain comparison on `ℤ^d` -/

section ChainZ

/-- `C ≤ W^t` once `W ≥ (C + 1)^{1/t}`. -/
private theorem VR1_const_le {C t W : ℝ} (hC : 0 ≤ C) (ht : 0 < t) (hW : (C + 1) ^ (1 / t) ≤ W) :
    C + 1 ≤ W ^ t := by
  calc C + 1 = ((C + 1) ^ (1 / t)) ^ t := by
        rw [← Real.rpow_mul (by linarith), one_div_mul_cancel ht.ne', Real.rpow_one]
    _ ≤ W ^ t := Real.rpow_le_rpow (by positivity) hW ht.le

set_option maxHeartbeats 1000000 in
-- One induction with thirteen thresholds and the bookkeeping of the four terms of a step.
/-- **The chain comparison on `ℤ^d`** ([I, (2.15)] for the labelled `Θ` edges, on `ℤ^d`). For a
label `o` with `|o| ≤ K` whose entries are even in `[4, N]` and satisfy `(V3)`: the lift `X_o` of
the cut chain on the torus and the chain `Θ_∞ Σ̊^∞_{o₁} ⋯ Θ_∞` on `ℤ^d` differ by at most
`η W^σ W^{-(k(o)-2)d/2} W^{-4} ⟨α⟩^{-(d-4)}` at every `α ∈ ℤ^d`. By induction on `o`
(`VR1_stepZ`); beyond the lift window `X_o = 0` and `|Y_o| ≤ W^{-(k-2)d/2} W^{-2} ⟨α⟩^{-(d-2-δ)}`
with `W² ⟨α⟩^{δ-2} ≤ η`. -/
private theorem VR1_zchain (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (K : ℕ) :
    ∀ o : List ℕ, o.length ≤ K →
      (∀ j ∈ o, (4 ≤ j ∧ j ≤ N ∧ Even j) ∧ VR1_V3 P Sig c₀ c₁ κ ε j) →
      ∀ σ : ℝ, 0 < σ → σ ≤ 1 → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z ∈ specDom κ ε W L, ∀ α : Fin d → ℤ,
          ‖VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o) α -
              chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o α‖ ≤
            z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              ((W : ℝ) ^ (-4 : ℝ) * ((zdInf α : ℝ) + W) ^ (-((d : ℝ) - 4))) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hShN : SelfEnergyShapesUpTo Sig N := fun k h4 hk he => (hSig k h4 hk he).1
  have hKI : ValZ.SelUnif κ N (ValZ.sigKer Sig P.ψ) := InfBound.selUnif (by omega) P Sig N hShN hκ
  intro o
  induction o using List.reverseRecOn with
  | nil =>
    intro _ _ σ hσ hσ1
    obtain ⟨W₀, h⟩ := VR1_thetaDiff hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (3 * K + 1) σ hσ hσ1
    refine ⟨W₀, fun W L _ hadm hW z hz α => ?_⟩
    rw [VR1_mu_nil, mul_one]
    have := (h W L hadm hW z hz α).2
    change ‖VR1_lift L (VR1_Θc P (3 * K + 1) W L z) α - ThetaInf (Sinf P.ψ W) α‖ ≤ _
    refine this.trans (le_of_eq ?_)
    ring
  | append_singleton o l ih =>
    intro hlen ho σ hσ hσ1
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have ho' : ∀ j ∈ o, (4 ≤ j ∧ j ≤ N ∧ Even j) ∧ VR1_V3 P Sig c₀ c₁ κ ε j :=
      fun j hj => ho j (List.mem_append_left _ hj)
    have hl := ho l (List.mem_append_right _ List.mem_cons_self)
    have hoN : ∀ j ∈ o, 4 ≤ j ∧ j ≤ N ∧ Even j := fun j hj => (ho' j hj).1
    have hoN' : ∀ j ∈ o ++ [l], 4 ≤ j ∧ j ≤ N ∧ Even j := fun j hj => (ho j hj).1
    -- the parameters
    set δ : ℝ := min (c₁ * σ / 100) (ε / 2) with hδdef
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδ1 : δ ≤ c₁ * σ / 100 := min_le_left _ _
    have hδε : δ ≤ ε / 2 := min_le_right _ _
    have hc₁1 : c₁ < 1 := by linarith
    have hδσ : δ ≤ σ / 100 := by nlinarith
    have hδ8 : δ ≤ 1 / 8 := by linarith
    have hcs : 0 < c₁ * σ := mul_pos hc₁ hσ
    have hδ32 : δ ≤ c₁ * (σ / 8) / 4 := hδ1.trans (by linarith)
    have hδ32' : 3 * δ ≤ c₁ * (σ / 8) / 4 := by linarith
    obtain ⟨W₁, h₁⟩ := ih (by omega) ho' (σ / 2) (by positivity) (by linarith)
    obtain ⟨W₂, h₂⟩ := VR1_TB hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K o l hoN hl.1
      (by omega) δ hδ0 (by linarith)
    obtain ⟨W₃, h₃⟩ := VR1Graph_chainZ_bound hd P N (ValZ.sigKer Sig P.ψ) hKI o (VR1_labelOK hoN)
      δ hδ0
    obtain ⟨W₄, h₄⟩ := VR1Graph_chainZ_bound hd P N (ValZ.sigKer Sig P.ψ) hKI (o ++ [l])
      (VR1_labelOK hoN') δ hδ0
    obtain ⟨W₅, h₅⟩ := VR1Graph_chainZ_bound hd P N (ValZ.sigKer Sig P.ψ) hKI [] rfl δ hδ0
    obtain ⟨W₆, h₆⟩ := VR1_hDiff hd P Sig N hShN c₀ c₁ κ ε hc₀ hκ hε (3 * K + 1) l hl.1.1 hl.1.2.1
      hl.1.2.2 hl.2 δ hδ0
    obtain ⟨W₇, h₇⟩ := InfBound.sigKerBound (by omega) P Sig N hShN hκ l hl.1.1 hl.1.2.1 hl.1.2.2
      δ hδ0
    obtain ⟨W₈, h₈⟩ := VR1_thetaDiff hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (3 * K + 1) δ hδ0 (by linarith)
    obtain ⟨W₉, h₉⟩ := VR1_thetaSigmaZ hd P N (ValZ.sigKer Sig P.ψ) hKI l hl.1.1 hl.1.2.1
      hl.1.2.2 δ hδ0
    set CA : ℝ := 2 ^ ((d : ℝ) - 4 - 3 * δ) * (2 * sumC d ((d : ℝ) + δ)) with hCA
    set CB : ℝ := 2 ^ ((d : ℝ) - 2 - δ) * (2 * sumC d (2 * (d : ℝ) - 6 - δ)) with hCB
    have hCA0 : 0 ≤ CA := by
      have := sumC_nonneg d (n := (d : ℝ) + δ) (by linarith); positivity
    have hCB0 : 0 ≤ CB := by
      have := sumC_nonneg d (n := 2 * (d : ℝ) - 6 - δ) (by linarith); positivity
    set Cab : ℝ := 2 ^ (d + 1) * sumC d ((d : ℝ) + 2 * δ) with hCab
    have hCab0 : 0 ≤ Cab := by
      have := sumC_nonneg d (n := (d : ℝ) + 2 * δ) (by linarith); positivity
    set A : ℝ := 8 * (((3 * K + 1 : ℕ) : ℝ) + 2) with hA
    have hA0 : 0 ≤ A := by positivity
    refine ⟨max (max (max (max W₁ W₂) (max W₃ W₄)) (max (max W₅ W₆) (max W₇ W₈)))
      (max (max W₉ (max A ((A ^ (2 : ℝ)) ^ (2 / ε)))) (max (max ((Cab + 1) ^ (1 / (2 * δ)))
        ((4 * CA + 1) ^ (1 / (σ / 2)))) (max ((2 * CB + 1) ^ (1 / (σ / 4)))
          ((4 + 1) ^ (1 / (σ / 4)))))), fun W L _ hadm hW z hz α => ?_⟩
    simp only [max_le_iff] at hW
    obtain ⟨⟨⟨⟨hW1, hW2⟩, hW3, hW4⟩, ⟨hW5, hW6⟩, hW7, hW8⟩, ⟨hW9, hWA, hWA2⟩, ⟨hWab, hWCA⟩, hWCB,
      hW4'⟩ := hW
    have hA2 : (2 : ℝ) ≤ A := by rw [hA]; push_cast; nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    have hW2' : (2 : ℝ) ≤ W := hA2.trans hWA
    have hW2n : 2 ≤ W := by exact_mod_cast hW2'
    have hW0 : (0 : ℝ) < W := by linarith
    obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
    have hL0 : (0 : ℝ) < L := by linarith
    have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
    obtain ⟨hLA, hLε⟩ := VR1_win hc₀ hadm hA0 hε (max_le hWA hWA2)
    have hLn : 8 * (3 * K + 1 + 2) ≤ L := by
      have : A ≤ L := hLA
      rw [hA] at this
      exact_mod_cast this
    have hcut := VR1Graph_cut_small hε hz hLn hLε hδ0.le hδε (by linarith)
    set μo := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hμo
    set μl := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hμl
    rw [VR1_mu_append hW0 o l, ← hμo, ← hμl]
    set b : ℝ := (zdInf α : ℝ) + W with hb
    have hb0 : 0 < b := by rw [hb]; positivity
    have hb1 : (1 : ℝ) ≤ b := by rw [hb]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf α)]
    by_cases hα : zdInf α ≤ L / 5
    · -- inside the lift window: one step on `ℤ^d`
      obtain ⟨hXA, hXB⟩ := VR1_X_append P Sig K W L z hzpos o l (by omega)
      rw [hXA]
      have hY : chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W (o ++ [l]) =
          convZ (convZ (chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o)
            (ValZ.sigKer Sig P.ψ z.re l W)) (ThetaInf (Sinf P.ψ W)) := by
        unfold chainZ
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hY]
      obtain ⟨hTB1, hTB2⟩ := h₂ W L hadm hW2 z hz
      have habs : Cab ≤ (W : ℝ) ^ (2 * δ) := by
        have := VR1_const_le hCab0 (by positivity) hWab; linarith
      have hstep := VR1_stepZ (w := (W : ℝ)) (δ := δ) hd (by linarith) hδ0 hδ8 habs
        (VR1_lift L (VR1_CR P Sig (3 * K + 1) W L z o))
        (chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o)
        (VR1_lift L (VR1_KT P Sig (3 * K + 1) l W L z)) (ValZ.sigKer Sig P.ψ z.re l W)
        (VR1_lift L (VR1_Θc P (3 * K + 1) W L z)) (ThetaInf (Sinf P.ψ W))
        (cX := 2 * (W : ℝ) ^ δ * μo * (W : ℝ) ^ (-2 : ℝ)) (cY := μo * (W : ℝ) ^ (-2 : ℝ))
        (cD := z.im * (W : ℝ) ^ (σ / 2) * μo * (W : ℝ) ^ (-4 : ℝ))
        (cA := 2 * (W : ℝ) ^ δ * (μo * μl))
        (ch := z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ))
        (Jh := (L : ℝ) ^ δ * z.im * μl)
        (cT := (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4))
        (JT := μl * (W : ℝ) ^ δ) (cθ := 2 * z.im * (W : ℝ) ^ (-4 : ℝ)) (cΘ := (W : ℝ) ^ (-2 : ℝ))
        (cH := μl) (by positivity) (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) hTB1
        (fun v => (h₃ W hW3 z.re hz.1 v).trans (le_of_eq (by ring)))
        (fun v => (h₁ W L hadm hW1 z hz v).trans (le_of_eq (by ring)))
        (fun v => by rw [← hXB]; exact hTB2 v)
        (h₆ W L hadm hW6 z hz) ((h₇ W hW7 z.re hz.1).1) (fun v => (h₈ W L hadm hW8 z hz v).1)
        (fun v => (h₅ W hW5 z.re hz.1 v).trans (le_of_eq (by rw [VR1_mu_nil]; ring)))
        (h₉ W hW9 z.re hz.1) α
      refine hstep.trans ?_
      have hb2L : b ≤ 2 * L := by
        have : (zdInf α : ℝ) ≤ L := by
          have : zdInf α ≤ L := le_trans hα (Nat.div_le_self _ _)
          exact_mod_cast this
        rw [hb]; linarith
      have eKA : VR1_K d W ((d : ℝ) - δ) ((d : ℝ) - 4 - δ) ((d : ℝ) - 4 - 3 * δ) =
          CA * (W : ℝ) ^ (-δ) := by
        unfold VR1_K
        rw [show (d : ℝ) - δ + ((d : ℝ) - 4 - δ) - ((d : ℝ) - 4 - 3 * δ) = (d : ℝ) + δ by ring,
          show (d : ℝ) - ((d : ℝ) + δ) = -δ by ring, hCA]
        ring
      have eKB : VR1_K d W ((d : ℝ) - 2 - δ) (2 * (d : ℝ) - 6 - δ) ((d : ℝ) - 2 - δ) =
          CB * (W : ℝ) ^ (-((d : ℝ) - 6 - δ)) := by
        unfold VR1_K
        rw [show (d : ℝ) - 2 - δ + (2 * (d : ℝ) - 6 - δ) - ((d : ℝ) - 2 - δ) =
          2 * (d : ℝ) - 6 - δ by ring,
          show (d : ℝ) - (2 * (d : ℝ) - 6 - δ) = -((d : ℝ) - 6 - δ) by ring, hCB]
        ring
      rw [eKA, eKB]
      have k1 : (W : ℝ) ^ (-δ) * (W : ℝ) ^ δ = 1 := by
        rw [← Real.rpow_add hW0]; simp
      have k2 : (W : ℝ) ^ δ * (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ) *
          (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            (W : ℝ) ^ (-((d : ℝ) - 6 - δ)) = (W : ℝ) ^ (2 * δ) * (W : ℝ) ^ (-4 : ℝ) * μl := by
        rw [hμl, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0,
          ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        congr 1; ring
      have k3 : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ) = (W : ℝ) ^ (-4 : ℝ) := by
        rw [← Real.rpow_add hW0]; norm_num
      have hsum : CA * (W : ℝ) ^ (-δ) * (2 * (W : ℝ) ^ δ * (μo * μl)) *
            (2 * z.im * (W : ℝ) ^ (-4 : ℝ)) +
          2 * (W : ℝ) ^ δ * μo * (W : ℝ) ^ (-2 : ℝ) * ((W : ℝ) ^ (-2 : ℝ) *
            (z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              (CB * (W : ℝ) ^ (-((d : ℝ) - 6 - δ))) + (L : ℝ) ^ δ * z.im * μl)) +
          z.im * (W : ℝ) ^ (σ / 2) * μo * (W : ℝ) ^ (-4 : ℝ) * μl =
          z.im * μo * μl * (W : ℝ) ^ (-4 : ℝ) * (4 * CA + 2 * CB * (W : ℝ) ^ (2 * δ) +
            2 * (W : ℝ) ^ δ * (L : ℝ) ^ δ + (W : ℝ) ^ (σ / 2)) := by
        have e1 : CA * (W : ℝ) ^ (-δ) * (2 * (W : ℝ) ^ δ * (μo * μl)) *
            (2 * z.im * (W : ℝ) ^ (-4 : ℝ)) =
            4 * CA * ((W : ℝ) ^ (-δ) * (W : ℝ) ^ δ) * (z.im * μo * μl * (W : ℝ) ^ (-4 : ℝ)) := by
          ring
        have e2 : 2 * (W : ℝ) ^ δ * μo * (W : ℝ) ^ (-2 : ℝ) * ((W : ℝ) ^ (-2 : ℝ) *
            (z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              (CB * (W : ℝ) ^ (-((d : ℝ) - 6 - δ))) + (L : ℝ) ^ δ * z.im * μl)) =
            2 * CB * z.im * μo * ((W : ℝ) ^ δ * (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ) *
              (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                (W : ℝ) ^ (-((d : ℝ) - 6 - δ))) +
            2 * (W : ℝ) ^ δ * (L : ℝ) ^ δ * z.im * μo * μl *
              ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ)) := by ring
        rw [e1, e2, k1, k2, k3]
        ring
      rw [hsum]
      -- the four terms
      have t1 : 4 * CA ≤ (W : ℝ) ^ (σ / 2) := by
        have := VR1_const_le (by positivity : 0 ≤ 4 * CA) (by positivity) hWCA; linarith
      have hCBW : 2 * CB + 1 ≤ (W : ℝ) ^ (σ / 4) :=
        VR1_const_le (by positivity) (by positivity) hWCB
      have h5 : (4 : ℝ) + 1 ≤ (W : ℝ) ^ (σ / 4) := VR1_const_le (by norm_num) (by positivity) hW4'
      have hW1' : (1 : ℝ) ≤ W := by linarith
      have hWδ4 : (W : ℝ) ^ (2 * δ) ≤ (W : ℝ) ^ (σ / 4) :=
        Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
      have hWδ8 : (W : ℝ) ^ δ ≤ (W : ℝ) ^ (σ / 8) :=
        Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
      have hLδ : (L : ℝ) ^ δ ≤ (W : ℝ) ^ (σ / 8) :=
        VR1_Lpow hc₀ hc₁ hadm hW2n hL0.le (by linarith) hδ0.le hδ32
      have e48 : (W : ℝ) ^ (σ / 4) * (W : ℝ) ^ (σ / 4) = (W : ℝ) ^ (σ / 2) := by
        rw [← Real.rpow_add hW0]; ring_nf
      have e488 : (W : ℝ) ^ (σ / 4) * ((W : ℝ) ^ (σ / 8) * (W : ℝ) ^ (σ / 8)) =
          (W : ℝ) ^ (σ / 2) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
      have t2 : 2 * CB * (W : ℝ) ^ (2 * δ) ≤ (W : ℝ) ^ (σ / 2) := by
        rw [← e48]
        exact mul_le_mul (by linarith) hWδ4 (by positivity) (by positivity)
      have t3 : 2 * (W : ℝ) ^ δ * (L : ℝ) ^ δ ≤ (W : ℝ) ^ (σ / 2) := by
        rw [← e488, mul_assoc]
        exact mul_le_mul (by linarith) (mul_le_mul hWδ8 hLδ (by positivity) (by positivity))
          (by positivity) (by positivity)
      have hbr : 4 * CA + 2 * CB * (W : ℝ) ^ (2 * δ) + 2 * (W : ℝ) ^ δ * (L : ℝ) ^ δ +
          (W : ℝ) ^ (σ / 2) ≤ 4 * (W : ℝ) ^ (σ / 2) := by linarith
      have hbδ : b ^ (-((d : ℝ) - 4 - 3 * δ)) ≤ (W : ℝ) ^ (σ / 8) * b ^ (-((d : ℝ) - 4)) := by
        have e : b ^ (-((d : ℝ) - 4 - 3 * δ)) = b ^ (3 * δ) * b ^ (-((d : ℝ) - 4)) := by
          rw [← Real.rpow_add hb0]; ring_nf
        rw [e]
        exact mul_le_mul_of_nonneg_right (VR1_Lpow hc₀ hc₁ hadm hW2n hb0.le hb2L (by positivity)
          hδ32') (by positivity)
      have hfin : 4 * (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 8) ≤ (W : ℝ) ^ σ := by
        have h38 : (W : ℝ) ^ (σ / 4) ≤ (W : ℝ) ^ (3 * σ / 8) :=
          Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
        have e : (W : ℝ) ^ (3 * σ / 8) * (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 8) = (W : ℝ) ^ σ := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
        rw [← e]
        gcongr
        linarith
      have hP : 0 ≤ z.im * μo * μl * (W : ℝ) ^ (-4 : ℝ) := by positivity
      calc z.im * μo * μl * (W : ℝ) ^ (-4 : ℝ) * (4 * CA + 2 * CB * (W : ℝ) ^ (2 * δ) +
            2 * (W : ℝ) ^ δ * (L : ℝ) ^ δ + (W : ℝ) ^ (σ / 2)) * b ^ (-((d : ℝ) - 4 - 3 * δ))
          ≤ z.im * μo * μl * (W : ℝ) ^ (-4 : ℝ) * (4 * (W : ℝ) ^ (σ / 2)) *
              ((W : ℝ) ^ (σ / 8) * b ^ (-((d : ℝ) - 4))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hbr hP) hbδ (by positivity) (by positivity)
        _ = z.im * (4 * (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 8)) * (μo * μl) *
              ((W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by ring
        _ ≤ z.im * (W : ℝ) ^ σ * (μo * μl) * ((W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfin hzpos.le) (by positivity)) (by positivity)
    · -- beyond the lift window: `X = 0`
      rw [VR1_lift, if_neg hα, zero_sub, norm_neg]
      have hY := h₄ W hW4 z.re hz.1 α
      rw [VR1_mu_append hW0 o l, ← hμo, ← hμl, ← hb] at hY
      refine hY.trans ?_
      set R := L / (4 * (3 * K + 1 + 2)) with hR
      have hR5 : R ≤ L / 5 := Nat.div_le_div_left (by omega) (by norm_num)
      have hRpos : (0 : ℝ) < R := by
        have := VR1Graph_R_ge (3 * K + 1) L hLn
        have : (0 : ℝ) < (L : ℝ) / (8 * (((3 * K + 1 : ℕ) : ℝ) + 2)) := by positivity
        linarith
      have hRb : (R : ℝ) ≤ b := by
        rw [hb]
        have : (R : ℝ) < zdInf α := by
          have : R < zdInf α := by omega
          exact_mod_cast this
        linarith
      have hWb : (W : ℝ) ^ (2 : ℝ) * b ^ (δ - 2) ≤ z.im :=
        le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hRpos hRb
          (show δ - 2 ≤ 0 by linarith)) (by positivity)) hcut
      have e : (W : ℝ) ^ (-2 : ℝ) * b ^ (-((d : ℝ) - 2 - δ)) =
          (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (2 : ℝ) * b ^ (δ - 2)) * b ^ (-((d : ℝ) - 4)) := by
        rw [show (W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (2 : ℝ) * b ^ (δ - 2)) * b ^ (-((d : ℝ) - 4)) =
          ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (2 : ℝ)) * (b ^ (δ - 2) * b ^ (-((d : ℝ) - 4))) by ring,
          ← Real.rpow_add hW0, ← Real.rpow_add hb0]
        congr 1 <;> congr 1 <;> ring
      have hWσ : (1 : ℝ) ≤ (W : ℝ) ^ σ := Real.one_le_rpow (by linarith) hσ.le
      calc μo * μl * ((W : ℝ) ^ (-2 : ℝ) * b ^ (-((d : ℝ) - 2 - δ)))
          = μo * μl * ((W : ℝ) ^ (-4 : ℝ) * ((W : ℝ) ^ (2 : ℝ) * b ^ (δ - 2)) *
              b ^ (-((d : ℝ) - 4))) := by rw [e]
        _ ≤ μo * μl * ((W : ℝ) ^ (-4 : ℝ) * z.im * b ^ (-((d : ℝ) - 4))) := by gcongr
        _ = z.im * 1 * (μo * μl) * ((W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by ring
        _ ≤ z.im * (W : ℝ) ^ σ * (μo * μl) * ((W : ℝ) ^ (-4 : ℝ) * b ^ (-((d : ℝ) - 4))) := by
            gcongr

/-- **The tail of `Σ̊_l` beyond the cut** in the form of [I, Lemma 8.3]'s chain difference:
`|Σ̊_l(u, v) − Σ̊_l(u, v) 1(‖v − u‖ ≤ R)| ≤ η W^σ W^{-(l-2)d/2} W ⟨u − v⟩^{-(d+1)}`, from
`|Σ̊_l(u, v)| ≤ L^τ W^{-(l-4)d/2} B²_{uv}` beyond `R ≥ L/A` and `W² L^{-(2-ε)} ≤ η`. -/
private theorem VR1_tailΔ (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (n l : ℕ) (hl4 : 4 ≤ l) (hlN : l ≤ N)
    (hle : Even l) (σ : ℝ) (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ u v : Zd d L,
        ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z u v - VR1_KT P Sig n l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hR := Renorm.selfEnergiesUpTo d hd P N Sig hSig
  have hlow : SelfEnergiesUpTo d (smatVar P) (Renorm.sig Sig) (l - 1) :=
    fun j hj4 hjl hje => hR j hj4 (by omega) hje
  obtain ⟨L₁, hL₁⟩ := G13.entrywise d hd P l (Renorm.sig Sig) hl4 hlow (hR l hl4 hlN hle).1 κ ε
    c₀ c₁ hκ hε hc₀ hc₁ hc (ε / 2) (by positivity)
  set A : ℝ := 8 * ((n : ℝ) + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  set A' : ℝ := A ^ ((d : ℝ) - 5) with hA'
  refine ⟨max (max (L₁ : ℝ) A) (max ((A' + 1) ^ (1 / (ε / 2))) 1),
    fun W L _ hadm hW z hz u v => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWL₁, hWA⟩, hWA', hW1⟩ := hW
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hLL : L₁ ≤ L := by
    have : (L₁ : ℝ) ≤ L := hWL₁.trans hWL
    exact_mod_cast this
  have hLn : 8 * (n + 2) ≤ L := by
    have : (8 * ((n : ℝ) + 2)) ≤ L := hWA.trans hWL
    exact_mod_cast this
  set R := L / (4 * (n + 2)) with hRdef
  have hRge := VR1Graph_R_ge n L hLn
  have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  have hη : (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im := hz.2.1
  have hKT : VR1_KT P Sig n l W L z u v = if zdistInf d L (v - u) ≤ R then
      sigKer (smatVar P) (Renorm.sig Sig) l W L z u v else 0 := rfl
  rw [hKT]
  by_cases hcut : zdistInf d L (v - u) ≤ R
  · rw [if_pos hcut, sub_self, norm_zero]
    have : 0 ≤ (if u = v then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have := Chain_brk_pos d L W hWn u v
    positivity
  · rw [if_neg hcut, sub_zero]
    rw [not_le] at hcut
    have huv : u ≠ v := by
      rintro rfl
      rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl] at hcut
      exact absurd hcut (Nat.not_lt_zero _)
    rw [if_neg huv, add_zero]
    obtain ⟨hs1, -⟩ := kerSymm_sigKer_smatVar d P (Renorm.sig Sig) l W L z hzpos u (v - u)
    rw [add_sub_cancel] at hs1
    rw [hs1]
    have hvu0 : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
    have h := hL₁ W L hLL hadm z hz (v - u)
    rw [if_neg hvu0, add_zero, Chain_bB_sq d L W hWn] at h
    have hb : brk d L W 0 (v - u) = brk d L W u v := by
      unfold brk; rw [zero_sub, neg_sub]
    rw [hb] at h
    refine h.trans ?_
    set β := brk d L W u v with hβ
    have hβ0 : 0 < β := Chain_brk_pos d L W hWn u v
    have hRβ : (R : ℝ) ≤ β := by
      rw [hβ]; unfold brk
      have : (R : ℝ) < zdistInf d L (u - v) := by
        rw [← neg_sub, zdistInf_neg]; exact_mod_cast hcut
      linarith
    have hRA : (L : ℝ) / A ≤ R := by rw [hA]; exact hRge
    have hLAβ : (L : ℝ) / A ≤ β := hRA.trans hRβ
    -- `L^{ε/2} W^{d-5} β^{-(d-5)} ≤ η W^σ W^{-?}`
    have hLε : A' + 1 ≤ (L : ℝ) ^ (ε / 2) :=
      (VR1_const_le (by positivity) (by positivity) hWA').trans
        (Real.rpow_le_rpow hW0.le hWL (by positivity))
    have hWβ : (W : ℝ) ^ ((d : ℝ) - 5) * β ^ (-((d : ℝ) - 5)) ≤
        A' * ((W : ℝ) / L) ^ ((d : ℝ) - 5) := by
      have h1 : β ^ (-((d : ℝ) - 5)) ≤ ((L : ℝ) / A) ^ (-((d : ℝ) - 5)) :=
        Real.rpow_le_rpow_of_nonpos (by have : 0 < A := by rw [hA]; positivity
                                        positivity) hLAβ (by linarith)
      have h2 : ((L : ℝ) / A) ^ (-((d : ℝ) - 5)) = A' * (L : ℝ) ^ (-((d : ℝ) - 5)) := by
        rw [Real.div_rpow hL0.le hA0, Real.rpow_neg hL0.le, Real.rpow_neg hA0, div_inv_eq_mul,
          hA']; ring
      rw [Real.div_rpow hW0.le hL0.le, div_eq_mul_inv, ← Real.rpow_neg hL0.le]
      calc (W : ℝ) ^ ((d : ℝ) - 5) * β ^ (-((d : ℝ) - 5))
          ≤ (W : ℝ) ^ ((d : ℝ) - 5) * (A' * (L : ℝ) ^ (-((d : ℝ) - 5))) := by rw [← h2]; gcongr
        _ = _ := by ring
    have hkey : (L : ℝ) ^ (ε / 2) * ((W : ℝ) ^ ((d : ℝ) - 5) * β ^ (-((d : ℝ) - 5))) ≤
        z.im * (W : ℝ) ^ σ := by
      have hWL7 : ((W : ℝ) / L) ^ ((d : ℝ) - 7) ≤ 1 :=
        Real.rpow_le_one (by positivity) (by rw [div_le_one hL0]; exact hWL) (by linarith)
      have e1 : ((W : ℝ) / L) ^ ((d : ℝ) - 5) = (W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ (-(2 : ℝ)) *
          ((W : ℝ) / L) ^ ((d : ℝ) - 7) := by
        rw [Real.div_rpow hW0.le hL0.le, Real.div_rpow hW0.le hL0.le, Real.rpow_neg hL0.le]
        rw [show (d : ℝ) - 5 = 2 + ((d : ℝ) - 7) by ring, Real.rpow_add hW0, Real.rpow_add hL0]
        field_simp
      have e2 : (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) =
          (W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ (-(2 : ℝ)) * (L : ℝ) ^ ε := by
        rw [Real.rpow_two, div_eq_mul_inv, ← Real.rpow_neg hL0.le, mul_assoc,
          ← Real.rpow_add hL0]; ring_nf
      have hWσ : (1 : ℝ) ≤ (W : ℝ) ^ σ := Real.one_le_rpow (by linarith) hσ.le
      have e3 : (L : ℝ) ^ (ε / 2) * (L : ℝ) ^ (ε / 2) = (L : ℝ) ^ ε := by
        rw [← Real.rpow_add hL0]; ring_nf
      calc (L : ℝ) ^ (ε / 2) * ((W : ℝ) ^ ((d : ℝ) - 5) * β ^ (-((d : ℝ) - 5)))
          ≤ (L : ℝ) ^ (ε / 2) * (A' * ((W : ℝ) / L) ^ ((d : ℝ) - 5)) := by gcongr
        _ = (W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ (-(2 : ℝ)) * ((L : ℝ) ^ (ε / 2) * A' *
              ((W : ℝ) / L) ^ ((d : ℝ) - 7)) := by rw [e1]; ring
        _ ≤ (W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ (-(2 : ℝ)) * ((L : ℝ) ^ (ε / 2) * (L : ℝ) ^ (ε / 2) *
              1) := by gcongr; linarith
        _ = (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by rw [mul_one, e3, e2]
        _ ≤ z.im := hη
        _ = z.im * 1 := (mul_one _).symm
        _ ≤ z.im * (W : ℝ) ^ σ := by gcongr
    have ew : (W : ℝ) * (W : ℝ) ^ ((d : ℝ) - 5) = (W : ℝ) ^ ((d : ℝ) - 4) := by
      rw [show (d : ℝ) - 4 = 1 + ((d : ℝ) - 5) by ring, Real.rpow_add hW0, Real.rpow_one]
    have ea : (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ) =
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((W : ℝ) * (W : ℝ) ^ ((d : ℝ) - 5)) := by
      rw [ew, ← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
    have eb : β ^ (-(2 * (d : ℝ) - 4)) = β ^ (-((d : ℝ) + 1)) * β ^ (-((d : ℝ) - 5)) := by
      rw [← Real.rpow_add hβ0]; congr 1; ring
    calc (L : ℝ) ^ (ε / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * ((W : ℝ) ^ (-4 : ℝ) *
          β ^ (-(2 * (d : ℝ) - 4)))
        = (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((W : ℝ) * β ^ (-((d : ℝ) + 1))) *
            ((L : ℝ) ^ (ε / 2) * ((W : ℝ) ^ ((d : ℝ) - 5) * β ^ (-((d : ℝ) - 5)))) := by
          rw [eb, show (L : ℝ) ^ (ε / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) *
            ((W : ℝ) ^ (-4 : ℝ) * (β ^ (-((d : ℝ) + 1)) * β ^ (-((d : ℝ) - 5)))) =
            (L : ℝ) ^ (ε / 2) * ((W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-4 : ℝ)) *
              (β ^ (-((d : ℝ) + 1)) * β ^ (-((d : ℝ) - 5))) by ring, ea]
          ring
      _ ≤ (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((W : ℝ) * β ^ (-((d : ℝ) + 1))) *
            (z.im * (W : ℝ) ^ σ) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = _ := by ring

/-- **The chain comparison** (the analogue of [I, (2.15)] for the labelled `Θ` edges, the
hypothesis `(chain)` of `VR1Graph.graphCompare`): for a label `o` whose entries are even in
`[4, N]` and satisfy `(V3)`, for every `σ > 0` there is `W₀` such that on the window
`|(Θ Σ̊_{o₁} Θ ⋯ Σ̊_{o_k} Θ)_{uv}(z) − (Θ_∞ Σ̊^∞_{o₁} Θ_∞ ⋯ Θ_∞)([v − u])(E)|
  ≤ η W^σ W^{-(k(o)-2)d/2} W^{-4} ⟨u − v⟩^{-(d-4)}`.
The factors `Σ̊` are cut at `R` (the tails, [I, Lemma 8.3]'s chain difference), the factors `Θ`
are cut at `R` (`VR1_crudeCR`), the cut chain is the convolution of its lifts (`VR1_lift_chain`),
and the lifts are compared on `ℤ^d` (`VR1_zchain`). -/
private theorem VR1_chainCmp (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (o : List ℕ)
    (ho : ∀ j ∈ o, (4 ≤ j ∧ j ≤ N ∧ Even j) ∧ VR1_V3 P Sig c₀ c₁ κ ε j) (σ : ℝ) (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ u v : Zd d L,
        ‖(detData (Smat P.ψ W L) z (fun l => sigKer (smatVar P) (Renorm.sig Sig) l W L z)).chain o
            u v - chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o (zlift (v - u))‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4))) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  -- it suffices to treat `σ ≤ 1`
  wlog hσ1 : σ ≤ 1 generalizing σ
  · obtain ⟨W₀, h⟩ := this 1 one_pos le_rfl
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz u v => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
    refine (h W L hadm ((le_max_left _ _).trans hW) z hz u v).trans ?_
    have : (W : ℝ) ^ (1 : ℝ) ≤ (W : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hzpos : 0 ≤ z.im := le_trans (by positivity) hz.2.1
    have := Chain_brk_pos d L W (by exact_mod_cast hW1) u v
    gcongr
  set K := o.length with hK
  set n := 3 * K + 1 with hn
  have hoN : ∀ j ∈ o, 4 ≤ j ∧ j ≤ N ∧ Even j := fun j hj => (ho j hj).1
  have hKL : ∀ l ∈ o, KerSymm (sigKer (smatVar P) (Renorm.sig Sig)) l ∧
      KerBound (sigKer (smatVar P) (Renorm.sig Sig)) l := fun l hl =>
    Renorm.kerSymm_kerBound d hd P N Sig hSig l (hoN l hl).1 (hoN l hl).2.1 (hoN l hl).2.2
  have hKT : ∀ l ∈ o, KerSymm (VR1_KT P Sig n) l ∧ KerBound (VR1_KT P Sig n) l := fun l hl =>
    VR1_kerBound_cut hd P Sig N hSig (4 * (n + 2)) (by omega) l (hoN l hl).1 (hoN l hl).2.1
      (hoN l hl).2.2
  -- the tails of `Σ̊` beyond the cut
  obtain ⟨W₁, h₁⟩ := RenormDiff_chainDiff d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε
    (sigKer (smatVar P) (Renorm.sig Sig)) (VR1_KT P Sig n) o hKL hKT
    (fun l hl σ' hσ' => VR1_tailΔ hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n l (hoN l hl).1
      (hoN l hl).2.1 (hoN l hl).2.2 σ' hσ') (σ / 2) (by positivity)
  -- the tails of `Θ` beyond the cut
  have hord := VR1_ord_ge o fun j hj => by have := (hoN j hj).1; omega
  set B : ℝ := 2 / c₁ + (((Kind.theta o).ord : ℤ) : ℝ) * d + 2 * d + 10 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨W₂, h₂⟩ := VR1_crudeCR hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K o hoN le_rfl B hB0
  -- the comparison on `ℤ^d`
  obtain ⟨W₃, h₃⟩ := VR1_zchain hd P Sig N hSig c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K o le_rfl ho
    (σ / 2) (by positivity) (by linarith)
  refine ⟨max (max W₁ W₂) (max W₃ (max 2 ((2 + 1) ^ (1 / (σ / 2))))),
    fun W L _ hadm hW z hz u v => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3, hW2', hW3'⟩ := hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 2 ≤ W := by exact_mod_cast hW2'
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hL0 : (0 : ℝ) < L := by linarith
  have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  set μ := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hμ
  set Bt := (W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)) with hBt
  have hA := h₁ W L hadm hW1 z hz u v
  have hBB := h₂ W L hadm hW2 z hz u v
  -- the cut chain at `(u, v)` is the lift at `[v - u]`
  have hR : (2 * K + 2) * (L / (4 * (n + 2))) ≤ L / 5 := VR1_R_mul K L
  have hlc := VR1_lift_chain (VR1_cut_TI (L / (4 * (n + 2))) (VR1_theta_TI P W L z))
    (VR1_cut_supp (L / (4 * (n + 2))) _) (fun j => (VR1_KT_TI P Sig n j W L z hzpos).1)
    (fun j => (VR1_KT_TI P Sig n j W L z hzpos).2) o _ (L / (4 * (n + 2)))
    (VR1_cut_TI (L / (4 * (n + 2))) (VR1_theta_TI P W L z)) (VR1_cut_supp (L / (4 * (n + 2))) _)
    (by
      have e : L / (4 * (n + 2)) + 2 * o.length * (L / (4 * (n + 2))) =
          (2 * K + 1) * (L / (4 * (n + 2))) := by rw [hK]; ring
      rw [e]
      exact le_trans (Nat.mul_le_mul_right _ (by omega)) hR)
  have hTI : VR1_TI (VR1_CR P Sig n W L z o) := hlc.1
  have hSp : VR1_Supp (VR1_CR P Sig n W L z o)
      (L / (4 * (n + 2)) + 2 * o.length * (L / (4 * (n + 2)))) := hlc.2.1
  have hsp5 : L / (4 * (n + 2)) + 2 * o.length * (L / (4 * (n + 2))) ≤ L / 5 := by
    have e : L / (4 * (n + 2)) + 2 * o.length * (L / (4 * (n + 2))) =
        (2 * K + 1) * (L / (4 * (n + 2))) := by rw [hK]; ring
    rw [e]
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) hR
  have hCR : VR1_CR P Sig n W L z o u v = VR1_lift L (VR1_CR P Sig n W L z o) (zlift (v - u)) := by
    rw [hTI u v]
    unfold VR1_lift
    rw [VR1Graph_zdInf_zlift, VR1Graph_zcast_zlift]
    split_ifs with h
    · rfl
    · exact hSp _ (by omega)
  have hZ := h₃ W L hadm hW3 z hz (zlift (v - u))
  rw [VR1Graph_brk_zlift u v] at hZ
  change ‖VR1_lift L (VR1_CR P Sig n W L z o) (zlift (v - u)) -
    chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o (zlift (v - u))‖ ≤
      z.im * (W : ℝ) ^ (σ / 2) * μ * Bt at hZ
  rw [← hCR] at hZ
  -- `L^{-B} ≤ η W^{σ/2} μ B̃`
  have hsmall : (L : ℝ) ^ (-B) ≤ z.im * (W : ℝ) ^ (σ / 2) * μ * Bt := by
    have hη := VR1Graph_eta_ge hc₀ hc₁ hε hadm (by omega) hz
    have hb1 : (1 : ℝ) ≤ brk d L W u v := by
      have := Chain_le_brk d L W u v; linarith
    have hb2 : brk d L W u v ≤ 2 * L := by
      have := Chain_brk_le d L W u v; linarith
    have hs := VR1_small (a := 2 / c₁ + ((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2 + 4)
      (e := (d : ℝ) - 4) (B := B) hW2' hWL hb1 hb2 (by
        have : 0 ≤ ((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2 := by nlinarith
        positivity) (by linarith) (by rw [hB]; nlinarith)
    have e : (W : ℝ) ^ (-(2 / c₁ + ((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2 + 4)) =
        (W : ℝ) ^ (-(2 / c₁)) * μ * (W : ℝ) ^ (-4 : ℝ) := by
      rw [hμ, ← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
    rw [e] at hs
    have hWσ : (1 : ℝ) ≤ (W : ℝ) ^ (σ / 2) := Real.one_le_rpow (by linarith) (by positivity)
    have hμBt : 0 ≤ μ * Bt := mul_nonneg (by rw [hμ]; positivity) (by
      rw [hBt]; exact mul_nonneg (by positivity)
        (Real.rpow_nonneg (Chain_brk_pos d L W (by omega) u v).le _))
    calc (L : ℝ) ^ (-B) ≤ (W : ℝ) ^ (-(2 / c₁)) * μ * (W : ℝ) ^ (-4 : ℝ) *
          brk d L W u v ^ (-((d : ℝ) - 4)) := hs
      _ = (W : ℝ) ^ (-(2 / c₁)) * (μ * Bt) := by rw [hBt]; ring
      _ ≤ z.im * (μ * Bt) := mul_le_mul_of_nonneg_right hη hμBt
      _ = z.im * 1 * (μ * Bt) := by ring
      _ ≤ z.im * (W : ℝ) ^ (σ / 2) * (μ * Bt) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWσ hzpos.le) hμBt
      _ = z.im * (W : ℝ) ^ (σ / 2) * μ * Bt := by ring
  have h3 : (3 : ℝ) ≤ (W : ℝ) ^ (σ / 2) := by
    have := VR1_const_le (by norm_num : (0 : ℝ) ≤ 2) (by positivity) hW3'; linarith
  have hσ2 : (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 2) = (W : ℝ) ^ σ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hP : 0 ≤ z.im * (W : ℝ) ^ (σ / 2) * μ * Bt := by
    have : 0 ≤ μ * Bt := mul_nonneg (by rw [hμ]; positivity) (by
      rw [hBt]; exact mul_nonneg (by positivity)
        (Real.rpow_nonneg (Chain_brk_pos d L W (by omega) u v).le _))
    have h2 : 0 ≤ z.im * (W : ℝ) ^ (σ / 2) := mul_nonneg hzpos.le (by positivity)
    calc (0 : ℝ) ≤ z.im * (W : ℝ) ^ (σ / 2) * (μ * Bt) := mul_nonneg h2 this
      _ = _ := by ring
  have hsplit : (detData (Smat P.ψ W L) z
      (fun l => sigKer (smatVar P) (Renorm.sig Sig) l W L z)).chain
      o u v - chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o (zlift (v - u)) =
      ((detData (Smat P.ψ W L) z
        (fun l => sigKer (smatVar P) (Renorm.sig Sig) l W L z)).chain o u v -
        VR1_CK P Sig n W L z o u v) + (VR1_CK P Sig n W L z o u v - VR1_CR P Sig n W L z o u v) +
      (VR1_CR P Sig n W L z o u v - chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o
        (zlift (v - u))) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  calc ‖(detData (Smat P.ψ W L) z (fun l => sigKer (smatVar P) (Renorm.sig Sig) l W L z)).chain
        o u v - VR1_CK P Sig n W L z o u v‖ + ‖VR1_CK P Sig n W L z o u v -
          VR1_CR P Sig n W L z o u v‖ + ‖VR1_CR P Sig n W L z o u v -
          chainZ (Sinf P.ψ W) (ValZ.sigKer Sig P.ψ z.re) W o (zlift (v - u))‖
      ≤ z.im * (W : ℝ) ^ (σ / 2) * μ * Bt + z.im * (W : ℝ) ^ (σ / 2) * μ * Bt +
          z.im * (W : ℝ) ^ (σ / 2) * μ * Bt := add_le_add (add_le_add hA (hBB.trans hsmall)) hZ
    _ = 3 * (z.im * (W : ℝ) ^ (σ / 2) * μ * Bt) := by ring
    _ ≤ (W : ℝ) ^ (σ / 2) * (z.im * (W : ℝ) ^ (σ / 2) * μ * Bt) := by gcongr
    _ = z.im * ((W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 2)) * μ * Bt := by ring
    _ = _ := by rw [hσ2]

end ChainZ

/-! ## One graph of `Σ_l` on the torus and on `ℤ^d` -/

section OneGraph

/-- The chain comparison `(chain)` of `VR1Graph.graphCompare` for one label `o` and the kernel
families `KL` (torus) and `KI` (`ℤ^d`). -/
private def VR1_Cmp (P : Profile d) (c₀ c₁ κ ε : ℝ) (KL : KerFamily d) (KI : ℝ → KerInf d)
    (o : List ℕ) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
    ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
      ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v -
          chainZ (Sinf P.ψ W) (KI z.re) W o (zlift (v - u))‖ ≤
        z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))

/-- One threshold `W₀` for finitely many statements monotone in `W`. -/
private theorem VR1_W0_fin {m : ℕ} {Q : Fin m → ℕ → Prop}
    (h : ∀ i, ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → Q i W) : ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ i, Q i W := by
  choose f hf using h
  refine ⟨∑ i, |f i|, fun W hW i => hf i W (le_trans ?_ hW)⟩
  calc f i ≤ |f i| := le_abs_self _
    _ ≤ ∑ j, |f j| := Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)

/-- The summand of a graph on `ℤ^d` as a product over the indices of its components. -/
private theorem VR1_termZ_eq {k n : ℕ} (Γ : Graph k n) (D : ValZ.Rec d)
    (σ : Atom k n → Fin d → ℤ) :
    ValZ.term Γ D σ = Γ.coeff.eval D.m * ∏ i : Fin Γ.comps.length, ValZ.compVal D σ Γ.comps[i] := by
  unfold ValZ.term
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- The value on `ℤ^d` of a graph without internal atoms is its summand. -/
private theorem VR1_valZ_zero (Γ : Graph 2 0) (D : ValZ.Rec d) (e : Fin 2 → Fin d → ℤ) :
    ValZ.val Γ D e = ValZ.term Γ D (Sum.elim e Fin.elim0) := by
  unfold ValZ.val
  rw [tsum_eq_single Fin.elim0 fun s hs => (hs (Subsingleton.elim _ _)).elim]

/-- A graph with a `×`-dotted loop has value `0` on `ℤ^d`. -/
private theorem VR1_valZ_xdotLoop {n : ℕ} (Γ : Graph 2 n) (h : Renorm.HasXdotLoop Γ)
    (D : ValZ.Rec d) (e : Fin 2 → Fin d → ℤ) : ValZ.val Γ D e = 0 := by
  obtain ⟨c, hc, hk, hxy⟩ := h
  unfold ValZ.val
  refine (tsum_congr fun s => ?_).trans tsum_zero
  unfold ValZ.term
  rw [List.prod_eq_zero, mul_zero]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk hxy
  simp [ValZ.compVal]

/-- A graph with a dotted edge between `x` and `y` has value `0` on `ℤ^d` at `x ≠ y`. -/
private theorem VR1_valZ_ne {n : ℕ} (Γ : Graph 2 n) (c : Comp (Atom 2 n)) (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0)
    (D : ValZ.Rec d) {x y : Fin d → ℤ} (hne : x ≠ y) : ValZ.val Γ D ![x, y] = 0 := by
  unfold ValZ.val
  exact (tsum_congr fun s => InfBound_term_ne Γ hc hk hxy D hne s).trans tsum_zero


/-- A waved edge with both ends at `0`: its factor on the torus is the waved kernel at `0`. -/
private theorem VR1_val_waved0 (P : Profile d) {W L : ℕ} [NeZero L] (z : ℂ)
    (M : ℕ → Matrix (Zd d L) (Zd d L) ℂ) {V : Type*} (σ : V → Zd d L) (c : Comp V) (w : Wave)
    (hc : c.kind = .waved w) (hx : σ c.x = 0) (hy : σ c.y = 0) :
    Comp.val (detData (Smat P.ψ W L) z M) σ c = VR1Graph_wT P W L z w 0 := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at hc hx hy
  subst hc
  cases w <;> simp [Comp.val, detData, VR1Graph_wT, hx, hy]

/-- A waved edge with both ends at `0`: its factor on `ℤ^d` is the waved kernel at `0`. -/
private theorem VR1_compVal_waved0 (P : Profile d) (W : ℕ) (K : KerInf d) (E : ℝ) {V : Type*}
    (σ : V → Fin d → ℤ) (c : Comp V) (w : Wave) (hc : c.kind = .waved w) (hx : σ c.x = 0)
    (hy : σ c.y = 0) :
    ValZ.compVal (ValZ.rec (Sinf P.ψ W) K W E) σ c = VR1Graph_wZ P W E w 0 := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at hc hx hy
  subst hc
  cases w <;> simp [ValZ.compVal, ValZ.rec, VR1Graph_wZ, hx, hy]

/-- **A diagonal graph without internal atom** on the torus and on `ℤ^d`: its value at `x = y = 0`
is the coefficient times the product of its factors at offset `0`; with the factor comparisons
(waved: `VR1Graph_wavedZ`; `Θ` edges: `(chain)` at `u = v = 0`; the coefficient: `m(z) → m(E)`),
each factor at most `K W^σ W^{-ord·d/2}` and the dotted edge `1`, the difference of the values is
at most `η W^τ W^{-(n-2)d/2}` ([I, Def 2.13 (i)]). -/
private theorem VR1_diagZero (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (KL : KerFamily d)
    (KI : ℝ → KerInf d) (hKL : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KL l ∧ KerBound KL l)
    (hKI : ValZ.SelUnif κ N KI) (hcmp : ∀ o, labelOK N o = true → VR1_Cmp P c₀ c₁ κ ε KL KI o)
    (Γ : Graph 2 0) (i₀ : ℕ) (hi₀ : i₀ < Γ.comps.length) (hk : Γ.comps[i₀].kind = .dot)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i₀, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, 0] -
          ValZ.val Γ (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, 0]‖ ≤
        z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
  classical
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set len := Γ.comps.length with hlen
  set j₀ : Fin len := ⟨i₀, hi₀⟩ with hj₀
  have hother : ∀ i : Fin len, i ≠ j₀ → Γ.comps[i].minor = [] ∧ Γ.comps[i].label = none ∧
      ((∃ w, Γ.comps[i].kind = .waved w) ∨
        ∃ o, Γ.comps[i].kind = .theta o ∧ labelOK N o = true) := by
    intro i hi
    refine hrest _ (List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun h => hi (Fin.ext h), rfl⟩)
  set σ₁ : ℝ := τ / (2 * ((len : ℝ) + 1)) with hσ₁
  have hσ₁0 : 0 < σ₁ := by positivity
  have hσ₁len : (len : ℝ) * σ₁ ≤ τ / 2 := by
    rw [hσ₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the bounds of the `Θ` factors, uniformly over the components
  have hlab : ∀ i : Fin len, ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ o, Γ.comps[i].kind = .theta o →
      ∀ (L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → ∀ z ∈ specDom κ ε W L,
        ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o 0 0‖ ≤
          (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) * bB d L W 0 0 ∧
        ‖chainZ (Sinf P.ψ W) (KI z.re) W o 0‖ ≤
          (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-2 : ℝ) * ((zdInf (0 : Fin d → ℤ) : ℝ) + W) ^ (-((d : ℝ) - 2 - σ₁))) ∧
        ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o 0 0 -
            chainZ (Sinf P.ψ W) (KI z.re) W o (zlift ((0 : Zd d L) - 0))‖ ≤
          z.im * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W 0 0 ^ (-((d : ℝ) - 4))) := by
    intro i
    by_cases hi : ∃ o, Γ.comps[i].kind = .theta o ∧ labelOK N o = true
    · obtain ⟨o, ho, hok⟩ := hi
      have hoK : ∀ l ∈ o, KerSymm KL l ∧ KerBound KL l := by
        intro l hl
        simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at hok
        obtain ⟨⟨h4, hN⟩, h2⟩ := hok l hl
        exact hKL l h4 hN (Nat.even_iff.2 h2)
      obtain ⟨W₁, h₁⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KL o hoK σ₁ hσ₁0
      obtain ⟨W₂, h₂⟩ := VR1Graph_chainZ_bound hd P N KI hKI o hok σ₁ hσ₁0
      obtain ⟨W₃, h₃⟩ := hcmp o hok σ₁ hσ₁0
      refine ⟨max (max W₁ W₂) W₃, fun W hW o' ho' L _ hadm z hz => ?_⟩
      rw [ho] at ho'
      cases ho'
      refine ⟨h₁ W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) z hz 0 0,
        h₂ W ((le_max_right _ _).trans ((le_max_left _ _).trans hW)) z.re hz.1 0,
        h₃ W L hadm ((le_max_right _ _).trans hW) z hz 0 0⟩
    · refine ⟨0, fun W _ o ho L _ _ z _ => ?_⟩
      exfalso
      by_cases hij : i = j₀
      · subst hij
        have hk' : Γ.comps[j₀].kind = .dot := hk
        rw [hk'] at ho; cases ho
      · rcases (hother i hij).2.2 with ⟨w, hw⟩ | h
        · rw [hw] at ho; cases ho
        · exact hi h
  obtain ⟨W₁, h₁⟩ := VR1_W0_fin hlab
  obtain ⟨K, Ww, hK0, hw⟩ := VR1Graph_wavedZ hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε σ₁ hσ₁0
  obtain ⟨Cc, hCc0, hCc⟩ := VR1Graph_coeff hκ Γ.coeff
  set K' : ℝ := 2 * K + 2 with hK'
  have hK'1 : 1 ≤ K' := by rw [hK']; linarith
  set Q : ℝ := Cc * ((len : ℝ) + 1) * K' ^ len + 1 with hQ
  refine ⟨max (max W₁ Ww) (max 1 (Q ^ (2 / τ))), fun W L _ hadm hW z hz => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hWw⟩, hW1', hWQ⟩ := hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hWn hz
  set η := z.im with hη
  set DL := detData (Smat P.ψ W L) z (fun l => KL l W L z) with hDL
  set DZ := ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re with hDZ
  set σL : Atom 2 0 → Zd d L := Sum.elim ![0, 0] Fin.elim0 with hσL
  set σZ : Atom 2 0 → Fin d → ℤ := Sum.elim ![0, 0] Fin.elim0 with hσZ
  have hσL0 : ∀ u, σL u = 0 := by
    rintro (a | a)
    · fin_cases a <;> rfl
    · exact a.elim0
  have hσZ0 : ∀ u, σZ u = 0 := by
    rintro (a | a)
    · fin_cases a <;> rfl
    · exact a.elim0
  set a : Fin len → ℂ := fun i => Comp.val DL σL Γ.comps[i] with hadef
  set b : Fin len → ℂ := fun i => ValZ.compVal DZ σZ Γ.comps[i] with hbdef
  set e : Fin len → ℝ := fun i => (((Γ.comps[i].kind.ord : ℤ) : ℝ)) - if i = j₀ then 2 else 0
    with hedef
  set F : Fin len → ℝ := fun i => K' * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(e i * d / 2)) with hFdef
  have hWσ : 1 ≤ (W : ℝ) ^ σ₁ := Real.one_le_rpow hW1' hσ₁0.le
  have hF0 : ∀ i, 0 ≤ F i := fun i => by simp only [hFdef]; positivity
  have hz0 : zdInf (0 : Fin d → ℤ) = 0 :=
    le_antisymm (Finset.sup_le fun i _ => by simp) (Nat.zero_le _)
  have hWd : ∀ t : ℝ, ((zdInf (0 : Fin d → ℤ) : ℝ) + W) ^ t = (W : ℝ) ^ t := by
    intro t; rw [hz0]; simp
  have hbrk0 : brk d L W 0 0 = W := by simp [brk, (zdistInf_eq_zero_iff d L).2 rfl]
  -- the factor bounds
  have hfac : ∀ i : Fin len, ‖a i‖ ≤ F i ∧ ‖b i‖ ≤ F i ∧ ‖a i - b i‖ ≤ η * F i := by
    intro i
    by_cases hi : i = j₀
    · rw [hi]
      have ha : a j₀ = 1 := by
        simp only [hadef]
        change Comp.val DL σL Γ.comps[i₀] = 1
        rw [RenormDiff_val_dotc DL σL _ hk, hσL0, hσL0, if_pos rfl]
      have hb : b j₀ = 1 := by
        simp only [hbdef]
        change ValZ.compVal DZ σZ Γ.comps[i₀] = 1
        rcases h : Γ.comps[i₀] with ⟨κ', x', y', mi', lb'⟩
        have hk' : κ' = .dot := by rw [h] at hk; exact hk
        subst hk'
        simp [ValZ.compVal, hσZ0]
      have hF1 : 1 ≤ F j₀ := by
        simp only [hFdef, hedef, if_true]
        have : (((Γ.comps[j₀].kind.ord : ℤ) : ℝ)) - 2 = 0 := by
          simp only [hj₀, Fin.getElem_fin, hk, Kind.ord]; norm_num
        rw [this, zero_mul, zero_div, neg_zero, Real.rpow_zero, mul_one]
        nlinarith
      refine ⟨by rw [ha]; simpa using hF1, by rw [hb]; simpa using hF1, ?_⟩
      rw [ha, hb, sub_self, norm_zero]; exact mul_nonneg him.le (hF0 _)
    · rcases (hother i hi).2.2 with ⟨w, hw'⟩ | ⟨o, ho, hok⟩
      · have he : e i = 2 := by
          simp only [hedef, hi, if_false, hw', Kind.ord]; norm_num
        have hFw : F i = K' * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) := by
          simp only [hFdef, he]; congr 2; ring
        have ha : a i = VR1Graph_wT P W L z w 0 :=
          VR1_val_waved0 P z _ σL _ w hw' (hσL0 _) (hσL0 _)
        have hb : b i = VR1Graph_wZ P W z.re w 0 :=
          VR1_compVal_waved0 P W (KI z.re) z.re σZ _ w hw' (hσZ0 _) (hσZ0 _)
        obtain ⟨hw1, hw2, -⟩ := hw W L hadm hWw z hz
        have hv0 : VR1Graph_wv W (0 : Fin d → ℤ) = (W : ℝ) ^ (-(d : ℝ)) := by
          rw [VR1Graph_wv_eq hWn, hWd, ← Real.rpow_add hW0]; ring_nf
        have h1 := hw1 w 0
        have h2 := hw2 w 0 (by rw [hz0]; exact Nat.pos_of_ne_zero (NeZero.ne L))
        rw [hv0] at h1 h2
        rw [VR1Graph_zcast_zero] at h2
        set X := (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) with hX
        have hX0 : 0 ≤ X := by rw [hX]; positivity
        have hKX : 0 ≤ K * X := mul_nonneg hK0 hX0
        have hη1 : η ≤ 1 := hz.2.2
        have e1 : K * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) = K * X := by rw [hX]; ring
        have e2 : η * K * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) = η * (K * X) := by rw [hX]; ring
        have e3 : K' * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) = K' * X := by rw [hX]; ring
        rw [e1] at h1
        rw [e2] at h2
        have hKK : K * X ≤ K' * X := mul_le_mul_of_nonneg_right (by rw [hK']; linarith) hX0
        refine ⟨?_, ?_, ?_⟩
        · rw [ha, hFw, e3]
          calc ‖VR1Graph_wT P W L z w 0‖ ≤ ‖VR1Graph_wZ P W z.re w 0‖ +
                ‖VR1Graph_wT P W L z w 0 - VR1Graph_wZ P W z.re w 0‖ := by
                have := norm_add_le (VR1Graph_wZ P W z.re w 0)
                  (VR1Graph_wT P W L z w 0 - VR1Graph_wZ P W z.re w 0)
                rwa [add_sub_cancel] at this
            _ ≤ K * X + η * (K * X) := add_le_add h1 h2
            _ ≤ K * X + 1 * (K * X) := by gcongr
            _ = (2 * K) * X := by ring
            _ ≤ K' * X := mul_le_mul_of_nonneg_right (by rw [hK']; linarith) hX0
        · rw [hb, hFw, e3]
          exact h1.trans hKK
        · rw [ha, hb, hFw, e3]
          exact h2.trans (mul_le_mul_of_nonneg_left hKK him.le)
      · have he : e i = (((Kind.theta o).ord : ℤ) : ℝ) := by
          simp only [hedef, hi, if_false, ho, sub_zero]
        set μo := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hμo
        have hFt : F i = K' * (W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ))) := by
          simp only [hFdef, he]
          rw [hμo, ← Real.rpow_add hW0]; congr 2; ring
        obtain ⟨h1, h2, h3⟩ := h₁ W hW1 i o ho L hadm z hz
        have ha : a i = DL.chain o 0 0 := by
          simp only [hadef]
          rw [RenormDiff_val_theta _ _ _ o ho, hσL0, hσL0]
        have hb : b i = chainZ (Sinf P.ψ W) (KI z.re) W o 0 := by
          simp only [hbdef]
          rcases h : Γ.comps[i] with ⟨κ', x', y', mi', lb'⟩
          have hk' : κ' = .theta o := by rw [h] at ho; exact ho
          subst hk'
          simp [ValZ.compVal, hσZ0, hDZ, ValZ.rec]
        have hB0 : bB d L W 0 0 = (W : ℝ) ^ (-(d : ℝ)) := by
          unfold bB; rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl]; push_cast
          rw [zero_add, ← Real.rpow_add hW0]; ring_nf
        rw [hB0] at h1
        have e5 : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 2 - σ₁)) =
            (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
        have e6 : (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4)) = (W : ℝ) ^ (-(d : ℝ)) := by
          rw [← Real.rpow_add hW0]; ring_nf
        rw [hWd, e5] at h2
        rw [hbrk0, sub_self, VR1Graph_zlift_zero, e6] at h3
        have hμ0 : 0 ≤ μo := by rw [hμo]; positivity
        have hP : 0 ≤ (W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ))) := by positivity
        refine ⟨?_, ?_, ?_⟩
        · rw [ha, hFt]
          calc ‖DL.chain o 0 0‖ ≤ (W : ℝ) ^ σ₁ * μo * (W : ℝ) ^ (-(d : ℝ)) := h1
            _ = 1 * ((W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ)))) := by ring
            _ ≤ K' * ((W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ)))) := by gcongr
            _ = _ := by ring
        · rw [hb, hFt]
          calc ‖chainZ (Sinf P.ψ W) (KI z.re) W o 0‖ ≤ μo * ((W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ))) :=
                h2
            _ = 1 * ((W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ)))) := by ring
            _ ≤ K' * ((W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ)))) := by gcongr
            _ = _ := by ring
        · rw [ha, hb, hFt]
          calc ‖DL.chain o 0 0 - chainZ (Sinf P.ψ W) (KI z.re) W o 0‖
              ≤ η * (W : ℝ) ^ σ₁ * μo * (W : ℝ) ^ (-(d : ℝ)) := h3
            _ = η * (1 * ((W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ))))) := by ring
            _ ≤ η * (K' * ((W : ℝ) ^ σ₁ * (μo * (W : ℝ) ^ (-(d : ℝ))))) := by gcongr
            _ = _ := by ring
  -- the values as products
  have hvL : Γ.val DL ![0, 0] = Γ.coeff.eval (msc z) * ∏ i, a i := by
    unfold Graph.val
    rw [Fintype.sum_unique, RenormDiff_term_eq]
    have e : ∀ s : Fin 0 → Zd d L, Sum.elim ![0, 0] s = σL := fun s => by
      rw [hσL]; congr 1; exact Subsingleton.elim _ _
    simp only [e]
    rfl
  have hvZ : ValZ.val Γ DZ ![0, 0] = Γ.coeff.eval (mE z.re) * ∏ i, b i := by
    rw [VR1_valZ_zero, VR1_termZ_eq]
    rfl
  have hval : Γ.val DL ![0, 0] - ValZ.val Γ DZ ![0, 0] =
      (Γ.coeff.eval (msc z) - Γ.coeff.eval (mE z.re)) * ∏ i, a i +
        Γ.coeff.eval (mE z.re) *
          ∑ j, ∏ i, (if i < j then a i else if i = j then a i - b i else b i) := by
    rw [hvL, hvZ, ← RenormDiff_telescope]; ring
  have hmm : ∀ j i, ‖(if i < j then a i else if i = j then a i - b i else b i)‖ ≤
      (if i = j then η else 1) * F i := by
    intro j i
    obtain ⟨h1, h2, h3⟩ := hfac i
    split_ifs with hij hij' <;> first
      | (rw [one_mul]; assumption)
      | exact absurd hij' (ne_of_lt hij)
      | exact h3
  have hprod : ∀ j, ∏ i, (if i = j then η else 1) * F i = η * ∏ i, F i := by
    intro j
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hsumF : ∑ i : Fin len, -(e i * d / 2) = -(((Γ.ord : ℝ) - 2) * d / 2) := by
    have h1 : ∑ i : Fin len, e i = (Γ.ord : ℝ) - 2 := by
      simp only [hedef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      unfold Graph.ord
      rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
      push_cast
      simp only [Fin.getElem_fin]
      ring
    rw [← h1, Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  have hFprod : ∏ i, F i =
      (K' * (W : ℝ) ^ σ₁) ^ len * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
    simp only [hFdef]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.rpow_sum_of_pos hW0, hsumF]
  obtain ⟨hcz, hcE, hcd⟩ := hCc z him hz.1 hz.2.2
  have hKpow : (K' * (W : ℝ) ^ σ₁) ^ len ≤ K' ^ len * (W : ℝ) ^ (τ / 2) := by
    rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ σ₁), ← Real.rpow_mul hW0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1' ?_) (by positivity)
    rw [mul_comm]; exact hσ₁len
  have hQW : Q ≤ (W : ℝ) ^ (τ / 2) := by
    have hCK : 0 ≤ Cc * ((len : ℝ) + 1) * K' ^ len := by positivity
    calc Q = (Q ^ (2 / τ)) ^ (τ / 2) := by
          rw [← Real.rpow_mul (by rw [hQ]; linarith)]; field_simp; simp
      _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow (by rw [hQ]; positivity) hWQ (by positivity)
  have hWτ : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hE0 : 0 ≤ (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by positivity
  have hPF : 0 ≤ ∏ i, F i := Finset.prod_nonneg fun i _ => hF0 i
  have hA : ‖∏ i, a i‖ ≤ ∏ i, F i := by
    rw [norm_prod]; exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => (hfac i).1
  rw [hval]
  calc ‖(Γ.coeff.eval (msc z) - Γ.coeff.eval (mE z.re)) * ∏ i, a i +
        Γ.coeff.eval (mE z.re) *
          ∑ j, ∏ i, (if i < j then a i else if i = j then a i - b i else b i)‖
      ≤ Cc * η * ∏ i, F i + Cc * ∑ j : Fin len, η * ∏ i, F i := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; exact mul_le_mul hcd hA (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          refine mul_le_mul hcE ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
            (norm_nonneg _) hCc0
          rw [norm_prod, ← hprod j]
          exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hmm j i
    _ = η * ((Cc * ((len : ℝ) + 1)) * (K' * (W : ℝ) ^ σ₁) ^ len) *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hFprod]; ring
    _ ≤ η * ((W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2)) *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ him.le) hE0
        calc Cc * ((len : ℝ) + 1) * (K' * (W : ℝ) ^ σ₁) ^ len ≤
              Cc * ((len : ℝ) + 1) * (K' ^ len * (W : ℝ) ^ (τ / 2)) :=
              mul_le_mul_of_nonneg_left hKpow (by positivity)
          _ = (Cc * ((len : ℝ) + 1) * K' ^ len) * (W : ℝ) ^ (τ / 2) := by ring
          _ ≤ Q * (W : ℝ) ^ (τ / 2) := mul_le_mul_of_nonneg_right (by rw [hQ]; linarith)
              (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hQW (by positivity)
    _ = _ := by rw [hWτ]

/-- A component without minor and label that is a waved edge or a `Θ` edge with a label of
entries even in `[4, N]` is of a deterministic kind. -/
private theorem VR1_isDetKind_of {V : Type*} {N : ℕ} (c : Comp V) (h1 : c.minor = [])
    (h2 : c.label = none)
    (h3 : (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true) :
    c.isDetKind N = true := by
  rcases c with ⟨κ, x, y, mi, lb⟩
  simp only at h1 h2 h3
  subst h1 h2
  rcases h3 with ⟨w, rfl⟩ | ⟨o, rfl, ho⟩
  · simp [Comp.isDetKind]
  · simp [Comp.isDetKind, ho]

/-- At `x = y`, the value on `ℤ^d` of a graph with a dotted edge between `x` and `y` is the sum
over `b` of the value of `Diag.graph Γ i` at `(x, b)`, when the summand is absolutely summable. -/
private theorem VR1_valZ_diag {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inl 0 ∧ Γ.comps[i].y = .inl 1 ∨
      Γ.comps[i].x = .inl 1 ∧ Γ.comps[i].y = .inl 0)
    (D : ValZ.Rec d) (x : Fin d → ℤ)
    (hs : Summable (fun p : (Fin d → ℤ) × (Fin m → Fin d → ℤ) =>
      ‖ValZ.term (Diag.graph Γ i) D (Sum.elim ![x, p.1] p.2)‖)) :
    ValZ.val Γ D ![x, x] = ∑' b, ValZ.val (Diag.graph Γ i) D ![x, b] := by
  unfold ValZ.val
  rw [← (Fin.consEquiv fun _ => Fin d → ℤ).tsum_eq]
  have he : ∀ p : (Fin d → ℤ) × (Fin m → Fin d → ℤ),
      ValZ.term Γ D (Sum.elim ![x, x] ((Fin.consEquiv fun _ => Fin d → ℤ) p)) =
        ValZ.term (Diag.graph Γ i) D (Sum.elim ![x, p.1] p.2) := by
    rintro ⟨b, t⟩
    simp only [Fin.consEquiv_apply]
    exact InfBound_term_cons Γ i hi hk hxy D x b t
  simp_rw [he]
  exact (Summable.of_norm hs).tsum_prod

/-- **A diagonal graph with an internal atom** on the torus and on `ℤ^d` at `x = y = 0`: the
atoms `x`, `y` are identified and the internal atom `0` becomes the external atom `y`
(`Diag.graph`); the values at `(0, 0)` are the sums over `b` of the values of that graph at
`(0, b)` (torus) and `(0, b)` (`ℤ^d`), and the summation step `VR1Graph.sumLemma` (with
`VR1Graph.graphCompare` and `ValZ.corBound` for that graph) bounds the difference by
`L^τ η W^{-(l-2)d/2}`, `l` the scaling order. -/
private theorem VR1_diagSucc (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (KL : KerFamily d)
    (KI : ℝ → KerInf d) (hKL : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KL l ∧ KerBound KL l)
    (hKI : ValZ.SelUnif κ N KI) (hcmp : ∀ o, labelOK N o = true → VR1_Cmp P c₀ c₁ κ ε KL KI o)
    {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot) (hD : G13.IsDiag Γ) (hDC : Γ.internalize.DoublyConnected)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (l : ℕ) (hl : Γ.ord = l) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, 0] -
          ValZ.val Γ (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, 0]‖ ≤
        (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hrest' : ∀ c ∈ Γ.comps.eraseIdx i,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := by
    intro c hc
    rcases (hrest c hc).2.2 with ⟨w, hw⟩ | ⟨o, ho, -⟩
    · rw [hw]; simp [Kind.isSolid]
    · rw [ho]; simp [Kind.isSolid]
  obtain ⟨hN, hDC'⟩ := Diag.internal Γ i hi hk hD hrest' hDC
  set G := Diag.graph Γ i with hGdef
  have hK' : ∀ c ∈ G.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true) := by
    intro c hc
    simp only [hGdef, Diag.graph, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨h1, h2, h3⟩ := hrest c' hc'
    exact ⟨by simp [Comp.map, h1], by simp [Comp.map, h2], h3⟩
  have hdet : G.comps.all (Comp.isDetKind N) = true :=
    List.all_eq_true.2 fun c hc => VR1_isDetKind_of c (hK' c hc).1 (hK' c hc).2.1 (hK' c hc).2.2
  have hOG : (G.ord : ℝ) = (l : ℝ) := by
    rw [hGdef, Diag.ord_eq Γ i hi hk, hl]; push_cast; ring
  have hOGr : (((G.ord : ℤ) : ℝ)) = ((l : ℕ) : ℝ) := hOG
  -- the summation step for `G`
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨Ci, Wi, hSi⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  have hsum := VR1Graph.sumLemma hd c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l
    (fun W L _ z x => G.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x])
    (fun W E v => ValZ.val G (ValZ.rec (Sinf P.ψ W) (KI E) W E) ![0, v]) ?_ ?_ τ hτ
  rotate_left
  · intro τ' hτ'
    obtain ⟨W₀, h⟩ := VR1Graph.graphCompare hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N KL KI hKL hKI G
      hN hDC' hK' (fun c hc o ho σ hσ => hcmp o (by
        rcases (hK' c hc).2.2 with ⟨w, hw⟩ | ⟨o', ho', hok⟩
        · rw [hw] at ho; cases ho
        · rw [ho'] at ho; cases ho; exact hok) σ hσ) τ' hτ'
    refine ⟨W₀, fun W L _ hadm hW z hz x => ?_⟩
    have := h W L hadm hW z hz x
    rw [hOG] at this
    exact this
  · intro τ' hτ'
    set τ'' : ℝ := min τ' 1 with hτ''
    have hτ''0 : 0 < τ'' := lt_min hτ' one_pos
    have hτ''1 : τ'' ≤ 1 := min_le_right _ _
    obtain ⟨Wc, hcB⟩ := ValZ.corBound d (by omega) P.ψ P.cψ c' (ValZ_shape P) hc' Ci κ hκ N KI
      hKI m _ G hN hDC' hdet τ'' hτ''0
    obtain ⟨Cl, hCl0, hCl⟩ := latSum d (2 * (d : ℝ) - 4 - τ'') (by linarith)
    refine ⟨max (max Wc Wi) 1, fun W hW E hE => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
    have hWn : 1 ≤ W := by exact_mod_cast hW1
    have hs := hSi W ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
    have hpt : ∀ v : Fin d → ℤ, ‖ValZ.val G (ValZ.rec (Sinf P.ψ W) (KI E) W E) ![0, v]‖ ≤
        (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ'')) := by
      intro v
      obtain ⟨hsm, hab⟩ := hcB W ((le_max_left _ _).trans ((le_max_left _ _).trans hW))
        (Sinf P.ψ W) hs E hE 0 v
      refine (ValZ.norm_val_le _ _ _ hsm).trans (hab.trans (le_of_eq ?_))
      rw [hOGr, zero_sub, zdInf_neg]
    refine ⟨fun v => ?_, ?_⟩
    · refine (hpt v).trans ?_
      have hb : (1 : ℝ) ≤ (zdInf v : ℝ) + W := by
        linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf v)]
      have h1 : ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ'')) ≤
          ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ')) :=
        Real.rpow_le_rpow_of_exponent_le hb (by linarith [min_le_left τ' 1])
      have h2 : 0 ≤ (if v = 0 then (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ' else 0) := by
        split_ifs <;> positivity
      have h3 : 0 ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) := by positivity
      calc _ ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
            ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ')) := by gcongr
        _ ≤ _ := le_add_of_nonneg_right h2
    · obtain ⟨hl', -⟩ := hCl W hWn
      exact Summable.of_nonneg_of_le (fun v => norm_nonneg _) hpt (hl'.mul_left _)
  obtain ⟨L₀, hL₀⟩ := hsum
  -- the joint summability on `ℤ^d`
  obtain ⟨Wc, hcB⟩ := ValZ.corBound d (by omega) P.ψ P.cψ c' (ValZ_shape P) hc' Ci κ hκ N KI
    hKI m _ G hN hDC' hdet 1 one_pos
  obtain ⟨Cl, hCl0, hCl⟩ := latSum d (2 * (d : ℝ) - 4 - 1) (by linarith)
  refine ⟨max (max (L₀ : ℝ) (max Wc Wi)) 1, fun W L _ hadm hW z hz => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWL₀, hWc, hWi⟩, hW1⟩ := hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hLL : L₀ ≤ L := by
    have : (L₀ : ℝ) ≤ L := hWL₀.trans hWL
    exact_mod_cast this
  have hs := hSi W hWi
  set DZ := ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re with hDZ
  have hjoint : Summable (fun p : (Fin d → ℤ) × (Fin m → Fin d → ℤ) =>
      ‖ValZ.term G DZ (Sum.elim ![0, p.1] p.2)‖) := by
    refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).2 ⟨fun b =>
      (hcB W hWc (Sinf P.ψ W) hs z.re hz.1 0 b).1, ?_⟩
    refine Summable.of_nonneg_of_le (fun b => tsum_nonneg fun t => norm_nonneg _)
      (fun b => (hcB W hWc (Sinf P.ψ W) hs z.re hz.1 0 b).2) ?_
    obtain ⟨hl', -⟩ := hCl W hWn
    refine ((Equiv.neg (Fin d → ℤ)).summable_iff.2 (hl'.mul_left
      ((W : ℝ) ^ (-((G.ord : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4)))).congr fun b => ?_
    simp [zero_sub, zdInf_neg]
  rw [RenormDiff_val_diag Γ i hi hk hxy, VR1_valZ_diag Γ i hi hk hxy DZ 0 hjoint]
  exact hL₀ W L hLL hadm z hz

/-- **One graph of `Σ_l`** on the torus and on `ℤ^d`: after the contraction `G13.dotContract'`
(same values on both records) the graph has a `×`-dotted loop (value `0` on both records), is
normal regular with `x`, `y` internal (`VR1Graph.graphCompare`), or is diagonal (`0` at `x ≠ 0`
on both records; at `x = 0` `VR1_diagZero` or `VR1_diagSucc`, at most `L^τ η W^{-(l-2)d/2}`). -/
private theorem VR1_graph (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ) (KL : KerFamily d)
    (KI : ℝ → KerInf d) (hKL : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' → KerSymm KL l' ∧ KerBound KL l')
    (hKI : ValZ.SelUnif κ (l - 1) KI)
    (hcmp : ∀ o, labelOK (l - 1) o = true → VR1_Cmp P c₀ c₁ κ ε KL KI o)
    (g : Σ m, Graph 2 m) (hg : SelfEnergyShape l [g]) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x : Zd d L,
        ‖g.2.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
            ValZ.val g.2 (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, zlift x]‖ ≤
          z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
            (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) := by
  obtain ⟨n', Γ, hsh, hvalL, hvalZ, hcase⟩ := G13.dotContract' l g.1 g.2 hg
  suffices h : ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
            ValZ.val Γ (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, zlift x]‖ ≤
          z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
            (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) by
    obtain ⟨W₀, h₀⟩ := h
    refine ⟨W₀, fun W L _ hadm hW z hz x => ?_⟩
    rw [← hvalL, ← (hvalZ d _ _).1]
    exact h₀ W L hadm hW z hz x
  obtain ⟨⟨C', hNo, hDA⟩, hK, hO, hDC⟩ := hsh ⟨n', Γ⟩ (List.mem_singleton_self _)
  have hK : Γ.comps.all (Comp.isDetKind (l - 1)) = true := hK
  have hO : Γ.ord = (l : ℤ) := hO
  have hDC : Γ.internalize.DoublyConnected := hDC
  have hordR : (Γ.ord : ℝ) = l := by rw [hO]; simp
  have hKc : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧ ((∃ w, c.kind = .waved w) ∨
      (∃ o, c.kind = .theta o ∧ labelOK (l - 1) o = true) ∨ c.kind = .dot ∨ c.kind = .xdot) :=
    fun c hc => RenormDiff_detKind c (List.all_eq_true.1 hK c hc)
  -- the nonnegative right-hand side
  have hR0 : ∀ (W L : ℕ) [NeZero L], 1 ≤ W → ∀ z : ℂ, 0 < z.im → ∀ x : Zd d L,
      0 ≤ z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
        (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) := by
    intro W L _ hW z hz x
    have := RenormDiff_brk_pos (d := d) (L := L) hW 0 x
    have h1 : 0 ≤ (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))
        else 0) := by split_ifs <;> positivity
    positivity
  by_cases hX : Renorm.HasXdotLoop Γ
  · refine ⟨1, fun W L _ hadm hW z hz x => ?_⟩
    have hWn : 1 ≤ W := by exact_mod_cast hW
    rw [RenormDiff_val_xdotLoop Γ hX, VR1_valZ_xdotLoop Γ hX, sub_self, norm_zero]
    exact hR0 W L hWn z (im_pos_of_specDom hWn hz) x
  have hnox : ∀ c ∈ Γ.comps, c.kind ≠ .xdot := by
    intro c hc hk
    refine hX ⟨c, hc, hk, ?_⟩
    by_contra hne
    obtain ⟨c', hc', hs', -⟩ := (hNo.2.2 c.x c.y hne).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    rcases (hKc c' hc').2.2 with ⟨w, hw⟩ | ⟨o, ho, -⟩ | h | h
    · rw [hw] at hs'; simp [Kind.isSolid] at hs'
    · rw [ho] at hs'; simp [Kind.isSolid] at hs'
    · rw [h] at hs'; simp [Kind.isSolid] at hs'
    · rw [h] at hs'; simp [Kind.isSolid] at hs'
  rcases hcase with ⟨C, hN⟩ | hD
  · -- normal regular with `x`, `y` internal: no dotted edge
    have hnod : ∀ c ∈ Γ.comps, c.kind ≠ .dot := by
      intro c hc hk
      have hmem : c.map (Sum.elim (fun a => Sum.inr (Fin.castAdd n' a))
          (fun b => Sum.inr (Fin.natAdd 2 b))) ∈ Γ.internalize.comps :=
        List.mem_map.2 ⟨c, hc, rfl⟩
      have := hN.1.noIntDot _ hmem hk
      rcases c with ⟨κ, a, b, mi, lb⟩
      rcases a with a | a <;> rcases b with b | b <;> simp [Comp.map] at this
    have hK' : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
        ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK (l - 1) o = true) := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := hKc c hc
      refine ⟨h1, h2, ?_⟩
      rcases h3 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hnod c hc)
      · exact absurd h (hnox c hc)
    obtain ⟨W₀, h₀⟩ := VR1Graph.graphCompare hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (l - 1) KL KI hKL
      hKI Γ hN hDC hK' (fun c hc o ho σ hσ => hcmp o (by
        rcases (hK' c hc).2.2 with ⟨w, hw⟩ | ⟨o', ho', hok⟩
        · rw [hw] at ho; cases ho
        · rw [ho'] at ho; cases ho; exact hok) σ hσ) τ hτ
    refine ⟨W₀, fun W L _ hadm hW z hz x => ?_⟩
    have h1 := h₀ W L hadm hW z hz x
    rw [hordR] at h1
    exact h1
  · -- diagonal
    obtain ⟨i, hi, hdot, hrest⟩ := Diag.dot_unique Γ hD hDA
    have hxy := hD.2 _ (List.getElem_mem hi) hdot
    have hrest' : ∀ c ∈ Γ.comps.eraseIdx i, c.minor = [] ∧ c.label = none ∧
        ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK (l - 1) o = true) := by
      intro c hc
      have hcm := List.mem_of_mem_eraseIdx hc
      obtain ⟨h1, h2, h3⟩ := hKc c hcm
      refine ⟨h1, h2, ?_⟩
      rcases h3 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hrest c hc)
      · exact absurd h (hnox c hcm)
    have hdiag : ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z ∈ specDom κ ε W L,
          ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, 0] -
              ValZ.val Γ (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, 0]‖ ≤
            (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
      cases n' with
      | zero =>
        obtain ⟨W₀, h₀⟩ := VR1_diagZero hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (l - 1) KL KI hKL hKI hcmp
          Γ i hi hdot hrest' τ hτ
        refine ⟨max W₀ 1, fun W L _ hadm hW z hz => ?_⟩
        have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
        obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
        have hz0 : 0 ≤ z.im := (im_pos_of_specDom (by exact_mod_cast hW1) hz).le
        refine (h₀ W L hadm ((le_max_left _ _).trans hW) z hz).trans ?_
        rw [hordR]
        have : (W : ℝ) ^ τ ≤ (L : ℝ) ^ τ := Real.rpow_le_rpow (by linarith) hWL hτ.le
        calc z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) ≤
            z.im * (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by gcongr
          _ = _ := by ring
      | succ m =>
        exact VR1_diagSucc hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (l - 1) KL KI hKL hKI hcmp Γ i hi
          hdot hD hDC hrest' l hO τ hτ
    obtain ⟨W₀, h₀⟩ := hdiag
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz x => ?_⟩
    have hWn : 1 ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
    have him := im_pos_of_specDom hWn hz
    have hmain0 : 0 ≤ z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by
      have := RenormDiff_brk_pos (d := d) (L := L) hWn 0 x
      positivity
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl, VR1Graph_zlift_zero]
      exact (h₀ W L hadm ((le_max_left _ _).trans hW) z hz).trans (le_add_of_nonneg_left hmain0)
    · have hzx : zlift x ≠ 0 := fun h => hx (by
        have := congrArg (zcast L) h
        rwa [VR1Graph_zcast_zlift, VR1Graph_zcast_zero] at this)
      rw [RenormDiff_val_ne Γ _ (List.getElem_mem hi) hdot hxy _ (Ne.symm hx),
        VR1_valZ_ne Γ _ (List.getElem_mem hi) hdot hxy _ (Ne.symm hzx), sub_self, norm_zero]
      exact hR0 W L hWn z him x

/-- **The formal sum**: the bound of `VR1_graph` for every graph of a formal sum with the shape
of an `l`-th order self-energy, times the number of graphs. -/
private theorem VR1_exp (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ) (KL : KerFamily d)
    (KI : ℝ → KerInf d) (hKL : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' → KerSymm KL l' ∧ KerBound KL l')
    (hKI : ValZ.SelUnif κ (l - 1) KI)
    (hcmp : ∀ o, labelOK (l - 1) o = true → VR1_Cmp P c₀ c₁ κ ε KL KI o) (τ : ℝ) (hτ : 0 < τ) :
    ∀ E : Expansion 2, SelfEnergyShape l E →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ x : Zd d L,
          ‖E.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
              ValZ.expVal E (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, zlift x]‖ ≤
            E.length * (z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
              (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))
                else 0)) := by
  intro E
  induction E with
  | nil =>
    intro _
    exact ⟨0, fun W L _ _ _ z _ x => by simp [Expansion.val, ValZ.expVal]⟩
  | cons g E ih =>
    intro hE
    obtain ⟨W₁, h₁⟩ := VR1_graph hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l KL KI hKL hKI hcmp g
      (fun g' hg' => hE g' (by rw [List.mem_singleton] at hg'; rw [hg']; exact List.mem_cons_self))
      τ hτ
    obtain ⟨W₂, h₂⟩ := ih (fun g' hg' => hE g' (List.mem_cons_of_mem _ hg'))
    refine ⟨max W₁ W₂, fun W L _ hadm hW z hz x => ?_⟩
    have e1 : ∀ D : Data (Zd d L), Expansion.val (g :: E) D ![0, x] =
        g.2.val D ![0, x] + Expansion.val E D ![0, x] := fun D => by
      simp [Expansion.val]
    have e2 : ∀ D : ValZ.Rec d, ValZ.expVal (g :: E) D ![0, zlift x] =
        ValZ.val g.2 D ![0, zlift x] + ValZ.expVal E D ![0, zlift x] := fun D => by
      simp [ValZ.expVal]
    rw [e1, e2, add_sub_add_comm, List.length_cons]
    push_cast
    refine (norm_add_le _ _).trans ?_
    have h1 := h₁ W L hadm ((le_max_left _ _).trans hW) z hz x
    have h2 := h₂ W L hadm ((le_max_right _ _).trans hW) z hz x
    linarith

end OneGraph

/-! ## The comparisons `(V1)`, `(V2)`, `(V3)` at one order -/

section Orders

/-- The comparison `(V1)` = [I, (8.9)] with a term at `x = 0` at the order `l`, with a threshold
`W₀` (the form of the hypothesis of `VR1Graph.sumLemma`). -/
private def VR1_V1 (P : Profile d) (Sig : ℕ → Expansion 2) (c₀ c₁ κ ε : ℝ) (l : ℕ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
    ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
      ‖sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l 0 x -
          ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift x)‖ ≤
        z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
          (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)

/-- **`(V1)` at the order `l`** from the chain comparisons at the labels of `Σ_l`: the value of
`Σ_l` on the record of `Σ̊` below `l` is the sum over its graphs (`VR1_exp`), on the torus
(`smatVar P = S` on the window) and on `ℤ^d` (`ValZ.sigR_eq`); the number of graphs is absorbed
by running at `τ/2`. -/
private theorem VR1_v1At (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ)
    (hl4 : 4 ≤ l) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (l - 1))
    (hsh : SelfEnergyShape l (Sig l))
    (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (hcmp : ∀ o, labelOK (l - 1) o = true → VR1_Cmp P c₀ c₁ κ ε
      (sigKer (smatVar P) (Renorm.sig Sig)) (ValZ.sigKer Sig P.ψ) o) :
    VR1_V1 P Sig c₀ c₁ κ ε l := by
  intro τ hτ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hKL : ∀ l', 4 ≤ l' → l' ≤ l - 1 → Even l' →
      KerSymm (sigKer (smatVar P) (Renorm.sig Sig)) l' ∧
        KerBound (sigKer (smatVar P) (Renorm.sig Sig)) l' := fun l' h4 hl he =>
    Renorm.kerSymm_kerBound d hd P (l - 1) Sig hSig l' h4 hl he
  have hKI : ValZ.SelUnif κ (l - 1) (ValZ.sigKer Sig P.ψ) :=
    InfBound.selUnif (by omega) P Sig (l - 1) (fun k h4 hk he => (hSig k h4 hk he).1) hκ
  obtain ⟨W₁, h₁⟩ := VR1_exp hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l _ _ hKL hKI hcmp (τ / 2)
    (by positivity) (Sig l) hsh
  obtain ⟨W₂, h₂⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  set m : ℝ := ((Sig l).length : ℝ) with hm
  refine ⟨max (max W₁ W₂) (max 1 ((m + 1) ^ (1 / (τ / 2)))), fun W L _ hadm hW z hz x => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW1', hWm⟩ := hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hz0 : 0 < z.im := im_pos_of_specDom hWn hz
  have hdet : ∀ g ∈ Sig l, g.2.comps.all (Comp.isDetKind (l - 1)) = true :=
    fun g hg => (hsh g hg).2.1
  have hrec := RenormDiff_sigMat_rec P (Function.update (Renorm.sig Sig) l (Sig l))
    (Renorm.sig Sig) l (fun k hk => Function.update_of_ne (by omega) _ _)
    (by rw [Function.update_self]; exact hdet) W L (h₂ W L hadm hW2) z x
  rw [Function.update_self] at hrec
  rw [hrec, ValZ.sigR_eq Sig P.ψ W z.re (by omega) hdet (zlift x)]
  refine (h₁ W L hadm hW1 z hz x).trans ?_
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmW : m + 1 ≤ (W : ℝ) ^ (τ / 2) := VR1_const_le hm0 (by positivity) hWm
  have hb := RenormDiff_brk_pos (d := d) (L := L) hWn 0 x
  have hbW : (W : ℝ) ≤ brk d L W 0 x := Chain_le_brk d L W 0 x
  have hmb : m ≤ brk d L W 0 x ^ (τ / 2) :=
    (by linarith : m ≤ m + 1).trans (hmW.trans (Real.rpow_le_rpow hW0.le hbW (by positivity)))
  have hmL : m ≤ (L : ℝ) ^ (τ / 2) :=
    (by linarith : m ≤ m + 1).trans (hmW.trans (Real.rpow_le_rpow hW0.le hWL (by positivity)))
  have hA : m * (z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
      brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ / 2))) ≤
      z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by
    have e : brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) =
        brk d L W 0 x ^ (τ / 2) * brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
      rw [← Real.rpow_add hb]; ring_nf
    rw [e]
    have : 0 ≤ z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by positivity
    calc m * (z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ / 2)))
        ≤ brk d L W 0 x ^ (τ / 2) * (z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) *
            (W : ℝ) ^ (-6 : ℝ) * brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ / 2))) :=
          mul_le_mul_of_nonneg_right hmb this
      _ = _ := by ring
  have hJ : m * (if x = 0 then (L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))
      else 0) ≤
        (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0) := by
    split_ifs
    · have hL0 : (0 : ℝ) < L := by linarith
      have e : (L : ℝ) ^ τ = (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_add hL0]; ring_nf
      rw [e]
      have : 0 ≤ (L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by positivity
      calc m * ((L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)))
          ≤ (L : ℝ) ^ (τ / 2) * ((L : ℝ) ^ (τ / 2) * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) :=
            mul_le_mul_of_nonneg_right hmL this
        _ = _ := by ring
    · simp
  rw [mul_add]
  exact add_le_add hA hJ

/-- **`(V2)` = [I, (8.10)] at the order `l`** from `(V1)` at `l` and [I, (8.7)] for
`Σ^{(r),∞}_l` (`InfBound.sigRBound`), by the summation step `VR1Graph.sumLemma`. -/
private theorem VR1_v2At (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ)
    (hl4 : 4 ≤ l) (hle : Even l) (hSh : SelfEnergyShapesUpTo Sig l) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (hV1 : VR1_V1 P Sig c₀ c₁ κ ε l) :
    ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L,
        ‖∑ x : Zd d L, sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l 0 x -
            ValZ.rowSum Sig P.ψ l z.re W‖ ≤
          (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) :=
  VR1Graph.sumLemma hd c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l
    (fun W L _ z x => sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l 0 x)
    (fun W E v => ValZ.sigR Sig (Sinf P.ψ W) W E l v) hV1
    (fun τ hτ => by
      obtain ⟨W₀, h⟩ := InfBound.sigRBound (by omega) P Sig l hSh hκ l hl4 le_rfl hle τ hτ
      exact ⟨W₀, fun W hW E hE => ⟨(h W hW E hE).1, (h W hW E hE).2.1⟩⟩)

/-- `|S_{uv}| ≤ C W^{d-4} ⟨u − v⟩^{-(2d-4)}` on `adm(c₀, c₁)` ([I, (1.8)]; `subpoly_adm` with
`k = 2d − 4` and `k = 0`). -/
private theorem VR1_S_bound (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → 1 ≤ W → ∀ u v : Zd d L,
      |Smat P.ψ W L u v| ≤ C * (W : ℝ) ^ ((d : ℝ) - 4) * brk d L W u v ^ (-(2 * (d : ℝ) - 4)) := by
  set k : ℕ := 2 * d - 4 with hk
  have hkR : (k : ℝ) = 2 * (d : ℝ) - 4 := by rw [hk]; push_cast [show 4 ≤ 2 * d by omega]; ring
  obtain ⟨C₁, hC₁⟩ := subpoly_adm d P c₀ c₁ hc₀ k
  obtain ⟨C₀, hC₀⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  refine ⟨2 ^ k * (max C₀ 0 + max C₁ 0), by positivity, fun W L _ hadm hW u v => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set r : ℝ := (zdistInf d L (u - v) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  set f : ℝ := |fWL P.ψ W L (u - v)| with hf
  have hf0 : 0 ≤ f := abs_nonneg _
  have h1 := hC₁ W L hadm (u - v)
  have h0 := hC₀ W L hadm (u - v)
  simp only [pow_zero, one_mul] at h0
  change (r / W) ^ k * f ≤ C₁ / (W : ℝ) ^ d at h1
  change f ≤ C₀ / (W : ℝ) ^ d at h0
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have hpow : (r + W) ^ k ≤ 2 ^ k * (r ^ k + (W : ℝ) ^ k) := by
    rcases le_total r W with h | h
    · calc (r + W) ^ k ≤ (2 * (W : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 2 ^ k * (W : ℝ) ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by have := pow_nonneg hr0 k; linarith) (by positivity)
    · calc (r + W) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 2 ^ k * r ^ k := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by have := pow_nonneg hW0.le k; linarith)
            (by positivity)
  have hWk : (W : ℝ) ^ k / (W : ℝ) ^ d = (W : ℝ) ^ ((d : ℝ) - 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hW0, hkR]; ring_nf
  have hfr : f * r ^ k ≤ max C₁ 0 * (W : ℝ) ^ ((d : ℝ) - 4) := by
    have e : (r / W) ^ k * f * (W : ℝ) ^ k = f * r ^ k := by rw [div_pow]; field_simp
    rw [← e, ← hWk]
    calc (r / W) ^ k * f * (W : ℝ) ^ k ≤ C₁ / (W : ℝ) ^ d * (W : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C₁ * ((W : ℝ) ^ k / (W : ℝ) ^ d) := by ring
      _ ≤ max C₁ 0 * ((W : ℝ) ^ k / (W : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hfW : f * (W : ℝ) ^ k ≤ max C₀ 0 * (W : ℝ) ^ ((d : ℝ) - 4) := by
    rw [← hWk]
    calc f * (W : ℝ) ^ k ≤ C₀ / (W : ℝ) ^ d * (W : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right h0 (by positivity)
      _ = C₀ * ((W : ℝ) ^ k / (W : ℝ) ^ d) := by ring
      _ ≤ max C₀ 0 * ((W : ℝ) ^ k / (W : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hkey : f * (r + W) ^ k ≤ 2 ^ k * (max C₀ 0 + max C₁ 0) * (W : ℝ) ^ ((d : ℝ) - 4) := by
    calc f * (r + W) ^ k ≤ f * (2 ^ k * (r ^ k + (W : ℝ) ^ k)) := mul_le_mul_of_nonneg_left hpow hf0
      _ = 2 ^ k * (f * r ^ k + f * (W : ℝ) ^ k) := by ring
      _ ≤ 2 ^ k * (max C₁ 0 * (W : ℝ) ^ ((d : ℝ) - 4) + max C₀ 0 * (W : ℝ) ^ ((d : ℝ) - 4)) := by
          gcongr
      _ = _ := by ring
  have hb : brk d L W u v = r + W := rfl
  have hbpos : 0 < r + W := by linarith
  change f ≤ _
  rw [hb, ← hkR, Real.rpow_neg hbpos.le, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  exact hkey

set_option maxHeartbeats 1000000 in
-- One estimate with the three terms of [I, (8.3)] and their bookkeeping.
/-- **`(V3)` at the order `l`** (the analogue of [I, (2.15)] for `Σ̊`, with the term at
`y = 0`): `Σ̊_l(0, y) − Σ̊^∞_l([y]) = [Σ^{(r)}_l(0, y) − Σ^{(r),∞}_l([y])] − (c_l − c^∞_l) S_{0y}
− c^∞_l (S_{0y} − S_∞([y]))` ([I, (8.3)] on the torus and on `ℤ^d`); the first term is `(V1)`, the
second is `(V2)` times `|S_{0y}| ≤ C W^{d-4} ⟨y⟩^{-(2d-4)}`, the third is
`|c^∞_l| ≤ W^{-(l-2)d/2} W^{τ}` ([I, (8.7)]) times
`|S_{0y} − S_∞([y])| ≤ η K W^{τ} W^{d-4} ⟨y⟩^{-(2d-4)}`
(for `2‖y‖_L = L` both `S_{0y}` and `S_∞([y])` are at most `W^{d-4} L^{-(2d-4)}`, and
`W²/L² ≤ η`). -/
private theorem VR1_v3At (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ)
    (hl4 : 4 ≤ l) (hle : Even l) (hSh : SelfEnergyShapesUpTo Sig l) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (hV1 : VR1_V1 P Sig c₀ c₁ κ ε l) : VR1_V3 P Sig c₀ c₁ κ ε l := by
  intro τ hτ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨W₁, h₁⟩ := hV1 (τ / 2) (by positivity)
  obtain ⟨L₂, h₂⟩ := VR1_v2At hd P Sig l hl4 hle hSh c₀ c₁ κ ε hc₀ hc₁ hc hκ hε hV1 (c₁ * τ / 4)
    (by positivity)
  obtain ⟨W₃, h₃⟩ := InfBound.sigRBound (by omega) P Sig l hSh hκ l hl4 le_rfl hle (τ / 8)
    (by positivity)
  obtain ⟨CS, hCS0, hCS⟩ := VR1_S_bound P c₀ c₁ hc₀ (by omega)
  obtain ⟨K, W₄, hK0, hw⟩ := VR1Graph_wavedZ hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε (τ / 8) (by positivity)
  obtain ⟨W₅, h₅⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨Ci, Wi, hSi⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  set Q : ℝ := 8 * (CS + K) + 1 with hQ
  refine ⟨max (max (max W₁ (L₂ : ℝ)) (max W₃ W₄))
    (max (max W₅ Wi) (max 2 ((Q + 1) ^ (1 / (τ / 4))))),
    fun W L _ hadm hW z hz y => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW1, hWL₂⟩, hW3, hW4⟩, ⟨hW5, hWi⟩, hW2, hWQ⟩ := hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 2 ≤ W := by exact_mod_cast hW2
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hL0 : (0 : ℝ) < L := by linarith
  have hLL : L₂ ≤ L := by
    have : (L₂ : ℝ) ≤ L := hWL₂.trans hWL
    exact_mod_cast this
  have hz0 : 0 < z.im := im_pos_of_specDom (by omega) hz
  have hS : smatVar P W L = Smat P.ψ W L := h₅ W L hadm hW5
  have hsum1 : ∑' v, Sinf P.ψ W v = 1 := (hSi W hWi).sum_one
  have hQW : Q + 1 ≤ (W : ℝ) ^ (τ / 4) := VR1_const_le (by rw [hQ]; positivity) (by positivity) hWQ
  set A' : ℝ := (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) with hA'
  set μl : ℝ := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hμl
  set b : ℝ := brk d L W 0 y with hb
  have hb0 : 0 < b := RenormDiff_brk_pos (d := d) (L := L) (by omega) 0 y
  have hbW : (W : ℝ) ≤ b := Chain_le_brk d L W 0 y
  have hA'0 : 0 ≤ A' := by rw [hA']; positivity
  set B : ℝ := b ^ (-(2 * (d : ℝ) - 6 - τ / 2)) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set G : ℝ := A' * B * (W : ℝ) ^ (-(τ / 2)) with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  -- `μ_l W^{d-4} b^{-(2d-4)} = A' B (W² b^{-2}) b^{-τ/2}`
  have key : μl * (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)) =
      A' * B * (((W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ))) * b ^ (-(τ / 2))) := by
    have e1 : μl * (W : ℝ) ^ ((d : ℝ) - 4) = A' * (W : ℝ) ^ (2 : ℝ) := by
      rw [hμl, hA', ← Real.rpow_add hW0, mul_assoc, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      congr 1; ring
    have e2 : b ^ (-(2 * (d : ℝ) - 4)) = B * (b ^ (-(2 : ℝ)) * b ^ (-(τ / 2))) := by
      rw [hB, ← Real.rpow_add hb0, ← Real.rpow_add hb0]; congr 1; ring
    rw [e1, e2]; ring
  have hWb1 : (W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hb0.le, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact Real.rpow_le_rpow hW0.le hbW (by norm_num)
  have hbτ : b ^ (-(τ / 2)) ≤ (W : ℝ) ^ (-(τ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hW0 hbW (by linarith)
  have hXle : μl * (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)) ≤ G := by
    rw [key, hG]
    have : ((W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ))) * b ^ (-(τ / 2)) ≤ 1 * (W : ℝ) ^ (-(τ / 2)) :=
      mul_le_mul hWb1 hbτ (by positivity) (by norm_num)
    rw [one_mul] at this
    calc A' * B * (((W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ))) * b ^ (-(τ / 2))) ≤
        A' * B * (W : ℝ) ^ (-(τ / 2)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := rfl
  have hWτ4 : (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (-(τ / 2)) = 1 / (W : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_add hW0, show τ / 4 + -(τ / 2) = -(τ / 4) by ring, Real.rpow_neg hW0.le,
      one_div]
  have hW4pos : 0 < (W : ℝ) ^ (τ / 4) := by positivity
  have hW8 : (W : ℝ) ^ (τ / 8) * (W : ℝ) ^ (τ / 8) = (W : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hsmall : ∀ C : ℝ, 0 ≤ C → 2 * C + 1 ≤ Q + 1 →
      C * ((W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (-(τ / 2))) ≤ 1 / 2 := by
    intro C hC0 hC
    rw [hWτ4, mul_one_div, div_le_iff₀ hW4pos]
    linarith
  -- the three terms
  set Sr := sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l with hSr
  set c : ℂ := ∑ u, Sr 0 u with hcdef
  set cI : ℂ := ∑' v, ValZ.sigR Sig (Sinf P.ψ W) W z.re l v with hcI
  have hT : sigKer (smatVar P) (Renorm.sig Sig) l W L z 0 y =
      Sr 0 y - c * (smatVar P W L 0 y : ℂ) :=
    Renorm.sigMat_smatVar P Sig l W L z hz0 0 y
  have hTI : ValZ.sigKer Sig P.ψ z.re l W (zlift y) =
      ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift y) -
      cI * (Sinf P.ψ W (zlift y) : ℂ) := ValZ.sigKer_of_tsum Sig P.ψ z.re l W hsum1 (zlift y)
  rw [hT, hTI, hS]
  have hsplit : Sr 0 y - c * (Smat P.ψ W L 0 y : ℂ) -
      (ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift y) - cI * (Sinf P.ψ W (zlift y) : ℂ)) =
      (Sr 0 y - ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift y)) - (c - cI) * (Smat P.ψ W L 0 y : ℂ) -
        cI * ((Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ)) := by ring
  rw [hsplit]
  have t1 := h₁ W L hadm hW1 z hz y
  have t2c : ‖c - cI‖ ≤ (L : ℝ) ^ (c₁ * τ / 4) * z.im * μl := h₂ W L hLL hadm z hz
  have t3c : ‖cI‖ ≤ μl * (W : ℝ) ^ (τ / 8) := by
    obtain ⟨-, hs, ht⟩ := h₃ W hW3 z.re hz.1
    exact (norm_tsum_le_tsum_norm hs).trans ht
  have hSb : |Smat P.ψ W L 0 y| ≤ CS * (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)) :=
    hCS W L hadm (by omega) 0 y
  set X : ℝ := μl * (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- the second term
  have hL4 : (L : ℝ) ^ (c₁ * τ / 4) ≤ (W : ℝ) ^ (τ / 4) := by
    obtain ⟨-, hLW⟩ := VR1Graph_adm hc₀ hadm
    rw [show c₁ * τ / 4 = c₁ * (τ / 4) by ring, Real.rpow_mul hL0.le]
    exact Real.rpow_le_rpow (by positivity) hLW (by positivity)
  have hGW : ∀ C : ℝ, 0 ≤ C → 2 * C + 1 ≤ Q + 1 → C * (W : ℝ) ^ (τ / 4) * G ≤ A' * B / 2 := by
    intro C hC0 hC
    have hs := hsmall C hC0 hC
    calc C * (W : ℝ) ^ (τ / 4) * G = A' * B * (C * ((W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (-(τ / 2)))) := by
          rw [hG]; ring
      _ ≤ A' * B * (1 / 2) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = A' * B / 2 := by ring
  have t2 : ‖(c - cI) * (Smat P.ψ W L 0 y : ℂ)‖ ≤ z.im * (A' * B / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖c - cI‖ * |Smat P.ψ W L 0 y| ≤ ((L : ℝ) ^ (c₁ * τ / 4) * z.im * μl) *
          (CS * (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4))) :=
          mul_le_mul t2c hSb (abs_nonneg _) (by positivity)
      _ = z.im * ((L : ℝ) ^ (c₁ * τ / 4) * CS * X) := by rw [hX]; ring
      _ ≤ z.im * ((W : ℝ) ^ (τ / 4) * CS * G) := by gcongr
      _ = z.im * (CS * (W : ℝ) ^ (τ / 4) * G) := by ring
      _ ≤ z.im * (A' * B / 2) :=
          mul_le_mul_of_nonneg_left (hGW CS hCS0 (by rw [hQ]; linarith)) hz0.le
  -- the third term
  have t3 : ‖cI * ((Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ))‖ ≤ z.im * (A' * B / 2) := by
    rw [norm_mul]
    obtain ⟨hw1, hw2, -⟩ := hw W L hadm hW4 z hz
    have hzl : (zdInf (zlift y) : ℝ) + W = b := by
      rw [hb, VR1Graph_zdInf_zlift]; unfold brk; rw [zero_sub, zdistInf_neg]
    have hwv : VR1Graph_wv W (zlift y) = (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)) := by
      rw [VR1Graph_wv_eq (by omega), hzl]
    by_cases hint : 2 * zdInf (zlift y) < L
    · have h2 := hw2 .s (zlift y) hint
      rw [VR1Graph_zcast_zlift, hwv] at h2
      change ‖(Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ)‖ ≤ _ at h2
      calc ‖cI‖ * ‖(Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ)‖
          ≤ (μl * (W : ℝ) ^ (τ / 8)) * (z.im * K * (W : ℝ) ^ (τ / 8) *
              ((W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)))) :=
            mul_le_mul t3c h2 (norm_nonneg _) (by positivity)
        _ = z.im * (K * ((W : ℝ) ^ (τ / 8) * (W : ℝ) ^ (τ / 8)) * X) := by rw [hX]; ring
        _ = z.im * (K * (W : ℝ) ^ (τ / 4) * X) := by rw [hW8]
        _ ≤ z.im * (K * (W : ℝ) ^ (τ / 4) * G) := by gcongr
        _ ≤ z.im * (A' * B / 2) :=
            mul_le_mul_of_nonneg_left (hGW K hK0 (by rw [hQ]; linarith)) hz0.le
    · -- the boundary `2 ‖y‖_L = L`
      rw [not_lt] at hint
      have h1 := hw1 .s (zlift y)
      rw [hwv] at h1
      change ‖(Sinf P.ψ W (zlift y) : ℂ)‖ ≤ _ at h1
      have hbL : (L : ℝ) ≤ 2 * b := by
        rw [← hzl]
        have : (L : ℝ) ≤ 2 * (zdInf (zlift y) : ℝ) := by exact_mod_cast hint
        linarith
      have hη : (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im := hz.2.1
      have hW2b : (W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ)) ≤ 4 * z.im := by
        have hLε : (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
        have h4 : (W : ℝ) ^ 2 ≤ z.im * (L : ℝ) ^ (2 - ε) := by
          rwa [div_le_iff₀ (by positivity)] at hη
        rw [Real.rpow_neg hb0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity),
          Real.rpow_two, Real.rpow_two]
        calc (W : ℝ) ^ 2 ≤ z.im * (L : ℝ) ^ (2 - ε) := h4
          _ ≤ z.im * (L : ℝ) ^ (2 : ℕ) := by gcongr
          _ ≤ z.im * (2 * b) ^ 2 := by gcongr
          _ = 4 * z.im * b ^ 2 := by ring
      have hXb : X ≤ 4 * z.im * G := by
        rw [key, hG]
        have : ((W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ))) * b ^ (-(τ / 2)) ≤
            (4 * z.im) * (W : ℝ) ^ (-(τ / 2)) := mul_le_mul hW2b hbτ (by positivity) (by positivity)
        calc A' * B * (((W : ℝ) ^ (2 : ℝ) * b ^ (-(2 : ℝ))) * b ^ (-(τ / 2))) ≤
            A' * B * ((4 * z.im) * (W : ℝ) ^ (-(τ / 2))) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      have hdiff : ‖(Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ)‖ ≤
          (CS + K * (W : ℝ) ^ (τ / 8)) * ((W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4))) := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        calc |Smat P.ψ W L 0 y| + ‖(Sinf P.ψ W (zlift y) : ℂ)‖ ≤
            CS * (W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)) +
              K * (W : ℝ) ^ (τ / 8) * ((W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4))) :=
            add_le_add hSb h1
          _ = _ := by ring
      have h1W : (1 : ℝ) ≤ (W : ℝ) ^ (τ / 8) := Real.one_le_rpow (by linarith) (by positivity)
      have hCK : (W : ℝ) ^ (τ / 8) * (CS + K * (W : ℝ) ^ (τ / 8)) ≤
          (CS + K) * (W : ℝ) ^ (τ / 4) := by
        rw [← hW8]
        have : CS * (W : ℝ) ^ (τ / 8) ≤ CS * ((W : ℝ) ^ (τ / 8) * (W : ℝ) ^ (τ / 8)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) h1W) hCS0
        calc (W : ℝ) ^ (τ / 8) * (CS + K * (W : ℝ) ^ (τ / 8)) =
            CS * (W : ℝ) ^ (τ / 8) + K * ((W : ℝ) ^ (τ / 8) * (W : ℝ) ^ (τ / 8)) := by ring
          _ ≤ CS * ((W : ℝ) ^ (τ / 8) * (W : ℝ) ^ (τ / 8)) +
              K * ((W : ℝ) ^ (τ / 8) * (W : ℝ) ^ (τ / 8)) := by linarith
          _ = _ := by ring
      calc ‖cI‖ * ‖(Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ)‖
          ≤ (μl * (W : ℝ) ^ (τ / 8)) * ((CS + K * (W : ℝ) ^ (τ / 8)) *
              ((W : ℝ) ^ ((d : ℝ) - 4) * b ^ (-(2 * (d : ℝ) - 4)))) :=
            mul_le_mul t3c hdiff (norm_nonneg _) (by positivity)
        _ = (W : ℝ) ^ (τ / 8) * (CS + K * (W : ℝ) ^ (τ / 8)) * X := by rw [hX]; ring
        _ ≤ (CS + K) * (W : ℝ) ^ (τ / 4) * (4 * z.im * G) :=
            mul_le_mul hCK hXb hX0 (by positivity)
        _ = z.im * ((4 * (CS + K)) * (W : ℝ) ^ (τ / 4) * G) := by ring
        _ ≤ z.im * (A' * B / 2) :=
            mul_le_mul_of_nonneg_left (hGW (4 * (CS + K)) (by positivity) (by rw [hQ]; linarith))
              hz0.le
  -- the sum
  have hτ2 : (2 : ℝ) ≤ b ^ (τ / 2) := by
    have h1 : (2 : ℝ) ≤ (W : ℝ) ^ (τ / 4) := by
      have : (2 : ℝ) ≤ Q + 1 := by rw [hQ]; linarith [hCS0, hK0]
      linarith
    calc (2 : ℝ) ≤ (W : ℝ) ^ (τ / 4) := h1
      _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ b ^ (τ / 2) := Real.rpow_le_rpow hW0.le hbW (by positivity)
  have hBτ : 2 * B ≤ b ^ (-(2 * (d : ℝ) - 6 - τ)) := by
    have e : b ^ (-(2 * (d : ℝ) - 6 - τ)) = b ^ (τ / 2) * B := by
      rw [hB, ← Real.rpow_add hb0]; ring_nf
    rw [e]; exact mul_le_mul_of_nonneg_right hτ2 hB0
  have hJ : (if y = 0 then (L : ℝ) ^ (τ / 2) * z.im * μl else 0) ≤
      (if y = 0 then (L : ℝ) ^ τ * z.im * μl else 0) := by
    split_ifs
    · have : (L : ℝ) ^ (τ / 2) ≤ (L : ℝ) ^ τ :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      gcongr
    · exact le_rfl
  have t1' : ‖Sr 0 y - ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift y)‖ ≤
      z.im * A' * B + (if y = 0 then (L : ℝ) ^ (τ / 2) * z.im * μl else 0) := by
    refine t1.trans (le_of_eq ?_)
    rw [hA', hB, hb, hμl]; ring
  have hfin : z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
      b ^ (-(2 * (d : ℝ) - 6 - τ)) = z.im * A' * b ^ (-(2 * (d : ℝ) - 6 - τ)) := by
    rw [hA']; ring
  rw [hfin]
  calc ‖(Sr 0 y - ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift y)) -
        (c - cI) * (Smat P.ψ W L 0 y : ℂ) -
          cI * ((Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ))‖
      ≤ ‖Sr 0 y - ValZ.sigR Sig (Sinf P.ψ W) W z.re l (zlift y)‖ +
          ‖(c - cI) * (Smat P.ψ W L 0 y : ℂ)‖ +
          ‖cI * ((Smat P.ψ W L 0 y : ℂ) - (Sinf P.ψ W (zlift y) : ℂ))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (z.im * A' * B + (if y = 0 then (L : ℝ) ^ (τ / 2) * z.im * μl else 0)) +
          z.im * (A' * B / 2) + z.im * (A' * B / 2) := add_le_add (add_le_add t1' t2) t3
    _ = z.im * A' * (2 * B) + (if y = 0 then (L : ℝ) ^ (τ / 2) * z.im * μl else 0) := by ring
    _ ≤ z.im * A' * b ^ (-(2 * (d : ℝ) - 6 - τ)) + (if y = 0 then (L : ℝ) ^ τ * z.im * μl else 0) :=
        add_le_add (mul_le_mul_of_nonneg_left hBτ (by positivity)) hJ

end Orders

/-! ## The joint induction of [I, Lemma 8.5] -/

section Joint

/-- **The joint induction** of [I, Lemma 8.5] over the even orders `4 ≤ l ≤ n`: `(V1)` and `(V3)`
at `l`. The labels of `Σ_l` have entries even in `[4, l − 1]`; the chain comparison at those
labels (`VR1_chainCmp`) reads `(V3)` below `l`; `(V1)` at `l` is `VR1_v1At`, `(V2)` at `l` is
`VR1_v2At` and `(V3)` at `l` is `VR1_v3At`. -/
private theorem VR1_joint (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig (n - 1)) (hsh : SelfEnergyShape n (Sig n))
    (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ l, 4 ≤ l → l ≤ n → Even l → VR1_V1 P Sig c₀ c₁ κ ε l ∧ VR1_V3 P Sig c₀ c₁ κ ε l := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro hl4 hln hle
  have hSigl : SelfEnergiesUpTo d (smatVar P) Sig (l - 1) :=
    fun k h4 hk he => hSig k h4 (by omega) he
  have hshl : SelfEnergyShape l (Sig l) := by
    by_cases h : l = n
    · subst h; exact hsh
    · exact (hSig l hl4 (by omega) hle).1
  have hShl : SelfEnergyShapesUpTo Sig l := by
    intro k h4 hk he
    by_cases h : k = l
    · subst h; exact hshl
    · exact (hSigl k h4 (by omega) he).1
  have hcmp : ∀ o, labelOK (l - 1) o = true → VR1_Cmp P c₀ c₁ κ ε
      (sigKer (smatVar P) (Renorm.sig Sig)) (ValZ.sigKer Sig P.ψ) o := by
    intro o ho σ hσ
    refine VR1_chainCmp hd P Sig (l - 1) hSigl c₀ c₁ κ ε hc₀ hc₁ hc hκ hε o (fun j hj => ?_) σ hσ
    simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho
    obtain ⟨⟨h4, hj1⟩, h2⟩ := ho j hj
    have hje : Even j := Nat.even_iff.2 h2
    exact ⟨⟨h4, hj1, hje⟩, (ih j (by omega) h4 (by omega) hje).2⟩
  have hV1 := VR1_v1At hd P Sig l hl4 hSigl hshl c₀ c₁ κ ε hc₀ hc₁ hc hκ hε hcmp
  exact ⟨hV1, VR1_v3At hd P Sig l hl4 hle hShl c₀ c₁ κ ε hc₀ hc₁ hc hκ hε hV1⟩

/-- For odd `n` the formal sum `Σ_n` is empty. -/
private theorem VR1_odd_nil {n : ℕ} {Sig : ℕ → Expansion 2} (hsh : SelfEnergyShape n (Sig n))
    (hodd : ¬ Even n) : Sig n = [] :=
  G13.shape_odd_nil (Nat.not_even_iff_odd.1 hodd) hsh

end Joint

/-! ## [I, Lemma 8.5] -/

section Main

/-- `W > 0` on `adm(c₀, c₁)`. -/
private theorem VR1_W_pos {c₀ c₁ : ℝ} {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) : (0 : ℝ) < W := by
  have hL : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact_mod_cast this
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) c₁) hadm.1

/-- `W ≥ 1` on `adm(c₀, c₁)`, as a natural number. -/
private theorem VR1_W_one {c₀ c₁ : ℝ} {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) : 1 ≤ W := by
  have h := VR1_W_pos hadm
  have : 0 < W := by exact_mod_cast h
  omega

/-- **[I, Lemma 8.5], (8.10)**, under the hypotheses of [I, (8.9)]: for all `κ, ε, c₀, c₁ > 0` with
`c₀ + c₁ < 1` and every `τ > 0` there is `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` and
`z ∈ 𝐃(κ, ε)`,
`|Σ_{x ∈ Z_L^d} Σ^{(r)}_n(0, x)(z) − R(E, W)| ≤ L^τ η W^{-(n-2)d/2}`, with
`R(E, W) = Σ'_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)(E)` the number of [I, (8.8)] (`ValZ.rowSum`) at
`E = Re z`. The bound holds on all of `𝐃(κ, ε)`, without `η ≤ L^{-ε}`. -/
theorem VR1.v2 (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2) (hn : 4 ≤ n)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig (n - 1)) (hsh : SelfEnergyShape n (Sig n)) :
    ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L,
          ‖∑ x : Zd d L, sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n
                0 x -
              ValZ.rowSum Sig P.ψ n z.re W‖ ≤
            (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := by
  intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  by_cases hev : Even n
  · have hSh : SelfEnergyShapesUpTo Sig n := by
      intro k h4 hk he
      by_cases h : k = n
      · subst h; exact hsh
      · exact (hSig k h4 (by omega) he).1
    exact VR1_v2At hd P Sig n hn hev hSh c₀ c₁ κ ε hc₀ hc₁ hc hκ hε
      (VR1_joint hd P n Sig hSig hsh c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n hn le_rfl hev).1 τ hτ
  · refine ⟨0, fun W L _ _ hadm z hz => ?_⟩
    have h0 := VR1_odd_nil hsh hev
    have e1 : ∀ x : Zd d L,
        sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x = 0 := by
      intro x; simp [sigMat, h0, Expansion.val]
    have e2 : ValZ.rowSum Sig P.ψ n z.re W = 0 := by
      simp [ValZ.rowSum, ValZ.sigR, h0, ValZ.expVal]
    simp only [e1, Finset.sum_const_zero, e2, sub_zero, norm_zero]
    have hz0 : 0 < z.im := im_pos_of_specDom (VR1_W_one hadm) hz
    have := VR1_W_pos hadm
    positivity

end Main

section Instances

end Instances

end RBM8D
