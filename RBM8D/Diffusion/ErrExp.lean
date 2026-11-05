import RBM8D.Diffusion.Defs
import RBM8D.Diffusion.Fourier
import RBM8D.SelfEnergy.MainCancel
import Batteries.Tactic.OpenPrivate

/-!
# The expectation of a graph of `Err` from the local law

* `ErrExp.entryBound`: [II, (8.1)] with `Φ = 0` from the local law [I, Theorem 1.4, (1.19)]:
  `T_{xy} ≺ B_{xy}`, uniformly in `x, y` and in a family of spectral parameters in `𝐃(κ, ε)`,
  along `W → ∞` inside `adm(c₀, c₁)`.
* `ErrExp.expBound`: the expectation step of [I, (8.17)] for one graph `Γ` with the kinds of
  `Err` ([II, Claim 8.6], (8.24), and [II, Claim 8.7], read in expectation): if `β` bounds the
  label-free path graphs of `Γ` at every single matrix `G̃` with `|G̃ − m δ| ≤ W^{τ'} B^{1/2}`,
  then `E|Γ_{𝔞,𝔟𝔟}| ≤ W^τ β + W^{−D'}` on `adm(c₀, c₁)` for `L ≥ L₀`.

The proof of `ErrExp.entryBound` writes `T_{xy} = |m|² Σ_α s_{xα} |G_{αy}|²`, bounds
`|G_{αy}|² ≤ 2 |G_{αy} − m δ_{αy}|² + 2 δ_{αy}`, and uses the convolution
`(|S| B)_{xy} ≤ C B_{xy}` on `adm(c₀, c₁)`, from the decay [I, (1.8)] of the profile and
`B_{αy} ≤ B_{xy}(1 + |x − α|/W)^{d−2}`.
The proof of `ErrExp.expBound` applies the label removal `labelRemovalErr` at `Φ = 0`, with
[II, (7.7)], [II, (7.8)] and [II, (8.1)] from the local law, and splits the expectation on the
exceptional event with the a priori bound polynomial in `W` and in the norm of the sample.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

open private Lem512Zero_h77 Lem512Zero_h78 Lem512Zero_integral_le Lem512Zero_sq_le
  from RBM8D.SelfEnergy.Lem512Zero
open private MainCancel_apriori from RBM8D.SelfEnergy.MainCancel
open private Entrywise_S_le_bB from RBM8D.LocalLaw.Entrywise
open private LabelRemoval_coordVar_le LabelRemoval_card_coord from RBM8D.LocalLaw.LabelRemoval
open private ThetaMSymbol.sum_zdist_inv_sq from RBM8D.Diffusion.Fourier

/-! ## The filter `W → ∞` inside `adm(c₀, c₁)` -/

/-- Eventually along `admFilterL c₀ c₁`, `(W, L) ∈ adm(c₀, c₁)`. -/
private theorem ErrExp_ev_adm (c₀ c₁ : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  rw [admFilterL, eventually_comap]
  filter_upwards [h] with q hq p hp
  rw [hp]
  exact hq

/-- Eventually along `admFilterL c₀ c₁`, `W ≥ M`. -/
private theorem ErrExp_ev_W (c₀ c₁ M : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, M ≤ sizeW p :=
  (tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_ge_atTop M)

/-- `W ≤ L` on `adm(c₀, c₁)` with `c₀ > 0`. -/
private theorem ErrExp_W_le_L {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (p : SizeL) (hp : p.1 ∈ adm c₀ c₁) :
    (p.1.1 : ℝ) ≤ p.1.2 := by
  have hL1 : (1 : ℝ) ≤ p.1.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  calc (p.1.1 : ℝ) ≤ (p.1.2 : ℝ) ^ (1 - c₀) := hp.2
    _ ≤ (p.1.2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = p.1.2 := Real.rpow_one _

/-- [II, (3.15)] holds on `adm(c₀, c₁)` with `W ≥ 1` when `2/c₁ − 2 ≤ (n − 1)d/2 − c₀ᵀ`, since
`L ≤ W^{1/c₁}` there. -/
private theorem ErrExp_thr {d n : ℕ} {c₀ c₁ c₀T : ℝ} (hc₁ : 0 < c₁)
    (he : 2 / c₁ - 2 ≤ ((n : ℝ) - 1) * d / 2 - c₀T) :
    ∀ p : SizeL, p.1 ∈ adm c₀ c₁ → 1 ≤ sizeW p → p ∈ thrSet d n c₀T := by
  intro p hp hW
  change (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ (((n : ℝ) - 1) * d / 2 - c₀T)
  change (1 : ℝ) ≤ p.1.1 at hW
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have hL1 : (1 : ℝ) ≤ p.1.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hLW : (p.1.2 : ℝ) ≤ (p.1.1 : ℝ) ^ (1 / c₁) := by
    calc (p.1.2 : ℝ) = ((p.1.2 : ℝ) ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (p.1.1 : ℝ) ^ (1 / c₁) := Real.rpow_le_rpow (by positivity) hp.1 (by positivity)
  calc (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ ((p.1.1 : ℝ) ^ (1 / c₁)) ^ 2 / (p.1.1 : ℝ) ^ 2 := by
        gcongr
    _ = (p.1.1 : ℝ) ^ (2 / c₁ - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_natCast (p.1.1 : ℝ) 2,
          ← Real.rpow_sub hW0]
        congr 1
        push_cast
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW he

/-- The filter of [II, Theorem 3.6] is `admFilterL c₀ c₁` when [II, (3.15)] holds on
`adm(c₀, c₁)` for `W ≥ 1`. -/
private theorem ErrExp_llFilter_eq {d n : ℕ} {c₀ c₁ c₀T : ℝ}
    (h : ∀ p : SizeL, p.1 ∈ adm c₀ c₁ → 1 ≤ sizeW p → p ∈ thrSet d n c₀T) :
    llFilter d n c₀ c₁ c₀T = admFilterL c₀ c₁ := by
  refine le_antisymm inf_le_left (le_inf le_rfl (le_principal_iff.2 ?_))
  filter_upwards [ErrExp_ev_adm c₀ c₁, ErrExp_ev_W c₀ c₁ 1] with p hp hW
  exact h p hp hW

/-- An eventual statement along `admFilterL c₀ c₁` in the explicit form: it holds for `L ≥ L₀`
and `(W, L) ∈ adm(c₀, c₁)`. -/
private theorem ErrExp_explicit {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) {Q : SizeL → Prop}
    (h : ∀ᶠ p in admFilterL c₀ c₁, Q p) :
    ∃ L₀ : ℕ, ∀ p : SizeL, L₀ ≤ p.1.2 → p.1 ∈ adm c₀ c₁ → Q p := by
  rw [admFilterL, eventually_comap, admFilter, inf_comm, eventually_inf_principal,
    eventually_comap, eventually_atTop] at h
  obtain ⟨W₀, hW₀⟩ := h
  refine ⟨max 1 ⌈(W₀ : ℝ) ^ (1 / c₁)⌉₊, fun p hL hp => ?_⟩
  have hLc : (W₀ : ℝ) ^ (1 / c₁) ≤ (p.1.2 : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hL)
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hL
  have hW : (W₀ : ℝ) ≤ (p.1.1 : ℝ) := by
    calc (W₀ : ℝ) = ((W₀ : ℝ) ^ (1 / c₁)) ^ c₁ := by
          rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (p.1.2 : ℝ) ^ c₁ := Real.rpow_le_rpow (by positivity) hLc hc₁.le
      _ ≤ p.1.1 := hp.1
  exact hW₀ p.1.1 (by exact_mod_cast hW) p.1 rfl hp p rfl

/-! ## The local law along `admFilterL` -/

/-- [I, Theorem 1.4, (1.19)] as `|G_{xy} − m δ_{xy}|² ≺ B_{xy}` along `admFilterL c₀ c₁`, uniformly
in `x, y` and in a family `z_u ∈ 𝐃(κ, ε)`: a union bound over the `L^{2d}` pairs `(x, y)`, with the
exceptional probability `L^{−D−2d}` of the local law at each pair and `W ≤ L`. -/
private theorem ErrExp_ll (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε)
    (U : SizeL → Type) (z : ∀ p, U p → ℂ) (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) :
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => ‖entryErr (green (hmat ω) (z p v.1)) (msc (z p v.1)) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) := by
  intro τ hτ D hD
  obtain ⟨L₀, hL₀⟩ := hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ ε τ (D + 2 * d) hε hτ (by positivity)
  filter_upwards [ErrExp_ev_adm c₀ c₁, ErrExp_ev_W c₀ c₁ (max 1 L₀)] with p hp hW
  change max 1 (L₀ : ℝ) ≤ (p.1.1 : ℝ) at hW
  have hW1 : (1 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have hWL := ErrExp_W_le_L hc₀ p hp
  have hL0 : (0 : ℝ) < p.1.2 := by linarith
  have hLL₀ : L₀ ≤ p.1.2 := by
    have : (L₀ : ℝ) ≤ p.1.2 := ((le_max_right _ _).trans hW).trans hWL
    exact_mod_cast this
  have hsub : {ω | ∃ v : U p × Zd d p.1.2 × Zd d p.1.2,
      sizeW p ^ τ * bB d p.1.2 p.1.1 v.2.1 v.2.2 <
        ‖entryErr (green (hmat ω) (z p v.1)) (msc (z p v.1)) v.2.1 v.2.2‖ ^ 2} ⊆
      ⋃ x : Zd d p.1.2, ⋃ y : Zd d p.1.2, {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧
        ∃ η : ℝ, (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
          (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 x y <
            ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * Complex.I))
              (msc ((E : ℂ) + (η : ℂ) * Complex.I)) x y‖ ^ 2} := by
    rintro ω ⟨⟨u, x, y⟩, hω⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, ?_⟩⟩
    obtain ⟨h1, h2, h3⟩ := hz p u
    refine ⟨(z p u).re, ⟨by linarith [neg_abs_le (z p u).re], by linarith [le_abs_self (z p u).re]⟩,
      (z p u).im, h2, h3, ?_⟩
    rw [Complex.re_add_im]
    exact hω
  refine (measure_mono hsub).trans ?_
  calc rbmLaw d P p (⋃ x : Zd d p.1.2, ⋃ y : Zd d p.1.2, _)
      ≤ ∑ x : Zd d p.1.2, rbmLaw d P p (⋃ y : Zd d p.1.2, _) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ x : Zd d p.1.2, ∑ y : Zd d p.1.2,
          ENNReal.ofReal ((p.1.2 : ℝ) ^ (-(D + 2 * d))) :=
        Finset.sum_le_sum fun x _ => (measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun y _ => hL₀ p hLL₀ hp x y)
    _ = ENNReal.ofReal ((p.1.2 : ℝ) ^ (d : ℝ) * ((p.1.2 : ℝ) ^ (d : ℝ) *
          (p.1.2 : ℝ) ^ (-(D + 2 * d)))) := by
        simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          Real.rpow_natCast, ← Nat.cast_pow, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (sizeW p ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0,
          show (d : ℝ) + ((d : ℝ) + -(D + 2 * d)) = -D by ring]
        exact Real.rpow_le_rpow_of_nonpos hW0 hWL (by linarith)

/-! ## The convolution `(|S| B)_{xy} ≤ C B_{xy}` -/

/-- `(1 + t)^M ≤ 2^M (1 + t^M)` for `t ≥ 0`. -/
private theorem ErrExp_one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (M : ℕ) :
    (1 + t) ^ M ≤ 2 ^ M * (1 + t ^ M) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ ≤ 2 ^ M * (1 + t ^ M) := by
          have : 0 ≤ t ^ M := pow_nonneg ht M
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) M]
  · calc (1 + t) ^ M ≤ (2 * t) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ = 2 ^ M * t ^ M := mul_pow _ _ _
      _ ≤ 2 ^ M * (1 + t ^ M) := by
          have := pow_pos (by norm_num : (0 : ℝ) < 2) M
          nlinarith

/-- `B_{αy} ≤ B_{xy} (1 + |x − α|_L/W)^{d−2}`, from `|x − y|_L ≤ |x − α|_L + |α − y|_L`. -/
private theorem ErrExp_bB_shift {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : (1 : ℝ) ≤ W)
    (x α y : Zd d L) :
    bB d L W α y ≤ bB d L W x y * (1 + (zdistInf d L (x - α) : ℝ) / W) ^ (d - 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  set r₁ : ℝ := (zdistInf d L (x - α) : ℝ) with hr₁
  set r₂ : ℝ := (zdistInf d L (α - y) : ℝ) with hr₂
  set r : ℝ := (zdistInf d L (x - y) : ℝ) with hr
  have hr₁0 : 0 ≤ r₁ := Nat.cast_nonneg _
  have hr₂0 : 0 ≤ r₂ := Nat.cast_nonneg _
  have htri : r ≤ r₁ + r₂ := by
    have h := zdistInf_add_le d L (x - α) (α - y)
    rw [sub_add_sub_cancel] at h
    rw [hr, hr₁, hr₂]
    exact_mod_cast h
  set c : ℝ := 1 + r₁ / W with hc
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 ≤ r₁ / W := by positivity
                         linarith
  have hab : r + W ≤ (r₂ + W) * c := by
    have e : (r₂ + W) * c = r₂ + W + r₁ * ((r₂ + W) / W) := by rw [hc]; field_simp
    have h1 : 1 ≤ (r₂ + W) / W := by rw [le_div_iff₀ hW0]; linarith
    have h2 : r₁ ≤ r₁ * ((r₂ + W) / W) := le_mul_of_one_le_right hr₁0 h1
    rw [e]
    linarith
  have hapos : 0 < r + W := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
                               linarith
  have he : (2 : ℝ) - d ≤ 0 := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                                  linarith
  have h1 : ((r₂ + W) * c) ^ ((2 : ℝ) - d) ≤ (r + W) ^ ((2 : ℝ) - d) :=
    Real.rpow_le_rpow_of_nonpos hapos hab he
  rw [Real.mul_rpow (by linarith) (by linarith)] at h1
  have hcc : c ^ ((2 : ℝ) - d) * c ^ (d - 2) = 1 := by
    rw [← Real.rpow_natCast, Nat.cast_sub hd, ← Real.rpow_add (by linarith)]
    push_cast
    rw [show (2 : ℝ) - d + (d - 2) = 0 by ring, Real.rpow_zero]
  have hcpos : 0 < c ^ (d - 2) := pow_pos (by linarith) _
  have key : (r₂ + W) ^ ((2 : ℝ) - d) ≤ (r + W) ^ ((2 : ℝ) - d) * c ^ (d - 2) := by
    calc (r₂ + W) ^ ((2 : ℝ) - d) = (r₂ + W) ^ ((2 : ℝ) - d) * c ^ ((2 : ℝ) - d) * c ^ (d - 2) := by
          rw [mul_assoc, hcc, mul_one]
      _ ≤ (r + W) ^ ((2 : ℝ) - d) * c ^ (d - 2) := mul_le_mul_of_nonneg_right h1 hcpos.le
  unfold bB
  rw [← hr₂, ← hr, mul_assoc]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- [I, (1.8)] in the form `(|S| B)_{xy} ≤ C B_{xy}` on `adm(c₀, c₁)`: with
`t = |u|_L/W`, `|f_{W,L}(u)| (1 + t)^{d−2} ≤ C' W^{−d} Π_i (1 + |u_i|/W)^{−2}` by the decay of the
profile at orders `0` and `3d`, and `Σ_{u ∈ Z_L} (1 + |u|/W)^{−2} ≤ 4W`. -/
private theorem ErrExp_conv {d : ℕ} (hd : 2 ≤ d) (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : SizeL, p.1 ∈ adm c₀ c₁ → 1 ≤ sizeW p → ∀ x y : Zd d p.1.2,
      ∑ α, |Smat P.ψ p.1.1 p.1.2 x α| * bB d p.1.2 p.1.1 α y ≤ C * bB d p.1.2 p.1.1 x y := by
  obtain ⟨C₀, h0⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨CM, hM⟩ := subpoly_adm d P c₀ c₁ hc₀ (3 * d)
  set K : ℝ := 2 ^ (3 * d) * (|C₀| + |CM|) with hK
  refine ⟨K * 4 ^ d, by positivity, fun p hp hW1 x y => ?_⟩
  change (1 : ℝ) ≤ p.1.1 at hW1
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  set g : ZMod p.1.2 → ℝ := fun v => ((1 + (zdist p.1.2 v : ℝ) / W) ^ 2)⁻¹ with hg
  -- the pointwise bound
  have hpt : ∀ u : Zd d p.1.2, |fWL P.ψ p.1.1 p.1.2 u| *
      (1 + (zdistInf d p.1.2 u : ℝ) / W) ^ (d - 2) ≤ K / W ^ d * ∏ i, g (u i) := by
    intro u
    set t : ℝ := (zdistInf d p.1.2 u : ℝ) / W with ht
    have ht0 : 0 ≤ t := by positivity
    have hti : ∀ i, 0 < (1 + (zdist p.1.2 (u i) : ℝ) / W) ^ 2 := fun i => by positivity
    have hprod : ∏ i, (1 + (zdist p.1.2 (u i) : ℝ) / W) ^ 2 ≤ (1 + t) ^ (2 * d) := by
      calc ∏ i, (1 + (zdist p.1.2 (u i) : ℝ) / W) ^ 2 ≤ ∏ _i : Fin d, (1 + t) ^ 2 := by
            refine Finset.prod_le_prod₀ (fun i _ => (hti i).le) fun i _ => ?_
            have : (zdist p.1.2 (u i) : ℝ) ≤ zdistInf d p.1.2 u := by
              exact_mod_cast zdist_le_zdistInf d p.1.2 u i
            have : (zdist p.1.2 (u i) : ℝ) / W ≤ t := div_le_div_of_nonneg_right this hW0.le
            gcongr
        _ = (1 + t) ^ (2 * d) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    have hP0 : 0 < ∏ i, (1 + (zdist p.1.2 (u i) : ℝ) / W) ^ 2 :=
      Finset.prod_pos fun i _ => hti i
    have hgprod : ∏ i, g (u i) = (∏ i, (1 + (zdist p.1.2 (u i) : ℝ) / W) ^ 2)⁻¹ := by
      simp only [hg]
      exact Finset.prod_inv_distrib _
    rw [hgprod, ← div_eq_mul_inv, le_div_iff₀ hP0]
    have hf0 := h0 p.1.1 p.1.2 hp u
    have hfM := hM p.1.1 p.1.2 hp u
    rw [pow_zero, one_mul] at hf0
    have hfa : 0 ≤ |fWL P.ψ p.1.1 p.1.2 u| := abs_nonneg _
    have h1t : 1 ≤ 1 + t := by linarith
    calc |fWL P.ψ p.1.1 p.1.2 u| * (1 + t) ^ (d - 2) *
          ∏ i, (1 + (zdist p.1.2 (u i) : ℝ) / W) ^ 2
        ≤ |fWL P.ψ p.1.1 p.1.2 u| * (1 + t) ^ (d - 2) * (1 + t) ^ (2 * d) := by gcongr
      _ = |fWL P.ψ p.1.1 p.1.2 u| * (1 + t) ^ (d - 2 + 2 * d) := by rw [mul_assoc, ← pow_add]
      _ ≤ |fWL P.ψ p.1.1 p.1.2 u| * (1 + t) ^ (3 * d) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1t (by omega)) hfa
      _ ≤ |fWL P.ψ p.1.1 p.1.2 u| * (2 ^ (3 * d) * (1 + t ^ (3 * d))) :=
          mul_le_mul_of_nonneg_left (ErrExp_one_add_pow_le ht0 _) hfa
      _ = 2 ^ (3 * d) * (|fWL P.ψ p.1.1 p.1.2 u| + t ^ (3 * d) * |fWL P.ψ p.1.1 p.1.2 u|) := by
          ring
      _ ≤ 2 ^ (3 * d) * (C₀ / W ^ d + CM / W ^ d) := by gcongr
      _ ≤ K / W ^ d := by
          rw [hK, mul_div_assoc, ← add_div]
          gcongr
          · exact le_abs_self _
          · exact le_abs_self _
  -- the sum over one coordinate
  have hg1 : ∑ v : ZMod p.1.2, g v ≤ 4 * W := by
    have h := ThetaMSymbol.sum_zdist_inv_sq p.1.2 W hW1
    have e : ∀ v : ZMod p.1.2, g v = W ^ 2 * (((zdist p.1.2 v : ℝ) + W) ^ 2)⁻¹ := by
      intro v
      rw [hg]
      simp only
      have : (0 : ℝ) < (zdist p.1.2 v : ℝ) + W := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl fun v _ => e v, ← Finset.mul_sum]
    calc W ^ 2 * ∑ v : ZMod p.1.2, (((zdist p.1.2 v : ℝ) + W) ^ 2)⁻¹ ≤ W ^ 2 * (4 / W) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * W := by field_simp
  have hg0 : ∀ v, 0 ≤ g v := fun v => by rw [hg]; positivity
  have hsumg : ∑ u : Zd d p.1.2, ∏ i, g (u i) ≤ (4 * W) ^ d := by
    rw [← Fintype.prod_sum (fun (_ : Fin d) (v : ZMod p.1.2) => g v)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun v _ => hg0 v) hg1 d
  have hB0 : 0 ≤ bB d p.1.2 p.1.1 x y := by unfold bB; positivity
  calc ∑ α, |Smat P.ψ p.1.1 p.1.2 x α| * bB d p.1.2 p.1.1 α y
      ≤ ∑ α, |fWL P.ψ p.1.1 p.1.2 (x - α)| *
          (bB d p.1.2 p.1.1 x y * (1 + (zdistInf d p.1.2 (x - α) : ℝ) / W) ^ (d - 2)) := by
        refine Finset.sum_le_sum fun α _ => ?_
        have hS : Smat P.ψ p.1.1 p.1.2 x α = fWL P.ψ p.1.1 p.1.2 (x - α) := by simp [Smat]
        rw [hS]
        exact mul_le_mul_of_nonneg_left (ErrExp_bB_shift hd hW1 x α y) (abs_nonneg _)
    _ = bB d p.1.2 p.1.1 x y * ∑ α, |fWL P.ψ p.1.1 p.1.2 (x - α)| *
          (1 + (zdistInf d p.1.2 (x - α) : ℝ) / W) ^ (d - 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => by ring
    _ ≤ bB d p.1.2 p.1.1 x y * ∑ α : Zd d p.1.2, K / W ^ d * ∏ i, g ((x - α) i) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => hpt (x - α)) hB0
    _ = bB d p.1.2 p.1.1 x y * (K / W ^ d * ∑ u : Zd d p.1.2, ∏ i, g (u i)) := by
        rw [← Finset.mul_sum]
        congr 2
        exact (Equiv.subLeft x).sum_comp (fun u => ∏ i, g (u i))
    _ ≤ bB d p.1.2 p.1.1 x y * (K / W ^ d * (4 * W) ^ d) := by gcongr
    _ = K * 4 ^ d * bB d p.1.2 p.1.1 x y := by
        rw [mul_pow]
        field_simp

/-! ## [II, (8.1)] with `Φ = 0` -/

/-- **[II, (8.1)] with `Φ = 0` from the local law**: for `d ≥ 8`, a profile `P`, `c₀, c₁, κ, ε > 0`
and a family of spectral parameters `z_u ∈ 𝐃(κ, ε)`, the local law [I, Theorem 1.4, (1.19)] gives
`T_{xy}(z_u) = |m|² Σ_α s_{xα} |G_{αy}(z_u)|² ≺ B_{xy}` uniformly in `(u, x, y)`, along `W → ∞`
inside `adm(c₀, c₁)`. -/
theorem ErrExp.entryBound : LocalLawStmt → ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ,
    0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∀ (U : SizeL → Type) (z : ∀ p, U p → ℂ), (∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) →
      StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
        (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
        (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) (msc (z p v.1))
          v.2.1 v.2.2)
        (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) := by
  intro hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε U z hz τ hτ D hD
  obtain ⟨CS, hCS⟩ := Entrywise_S_le_bB (by omega : 2 ≤ d) P c₀ c₁ hc₀
  obtain ⟨CB, hCB0, hCB⟩ := ErrExp_conv (by omega : 2 ≤ d) P c₀ c₁ hc₀
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  have hll := ErrExp_ll hLL hd P hc₀ hc₁ hκ hε U z hz (τ / 2) (by positivity) D hD
  filter_upwards [hll, ErrExp_ev_adm c₀ c₁, ErrExp_ev_W c₀ c₁ (max 1 W₂),
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τ / 2)).comp
      (tendsto_sizeW_admFilterL c₀ c₁)).eventually
      (eventually_ge_atTop (2 * CB + 2 * |CS|))] with p hp hadm hW hWτ
  refine le_trans (measure_mono ?_) hp
  rintro ω ⟨⟨u, x, y⟩, hω⟩
  by_contra hcon
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hcon
  change max 1 W₂ ≤ (p.1.1 : ℝ) at hW
  change 2 * CB + 2 * |CS| ≤ (p.1.1 : ℝ) ^ (τ / 2) at hWτ
  change (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 x y <
    Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) (msc (z p u)) x y at hω
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW1 : 1 ≤ W := (le_max_left _ _).trans hW
  have hW0 : 0 < W := by linarith
  have hds' := hds p.1.1 p.1.2 hadm ((le_max_right _ _).trans hW)
  set S := Smat P.ψ p.1.1 p.1.2 with hSdef
  have hS0 : ∀ a b, 0 ≤ S a b := fun a b => nonneg_of_mem_doublyStochastic hds'
  have him : 0 < (z p u).im := by
    refine lt_of_lt_of_le ?_ (hz p u).2.1
    exact div_pos (by positivity)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero p.2) _)
  set G := green (hmat ω) (z p u) with hG
  set m := msc (z p u) with hm
  have hm1 : ‖m‖ ≤ 1 := (norm_msc_lt_one him).le
  have hE : ∀ a b, ‖entryErr G m a b‖ ^ 2 ≤ W ^ (τ / 2) * bB d p.1.2 p.1.1 a b :=
    fun a b => hcon (u, a, b)
  have hB0 : ∀ a b, 0 ≤ bB d p.1.2 p.1.1 a b := fun a b => by unfold bB; positivity
  have hτ1 : 1 ≤ W ^ (τ / 2) := Real.one_le_rpow hW1 (by positivity)
  have hsum : ∑ α, S x α * ‖G α y‖ ^ 2 ≤
      2 * W ^ (τ / 2) * (CB * bB d p.1.2 p.1.1 x y) + 2 * (|CS| * bB d p.1.2 p.1.1 x y) := by
    have hpt : ∀ α, S x α * ‖G α y‖ ^ 2 ≤
        2 * W ^ (τ / 2) * (|S x α| * bB d p.1.2 p.1.1 α y) +
          2 * (S x α * (if α = y then 1 else 0)) := by
      intro α
      have h1 := Lem512Zero_sq_le G m hm1 α y
      have h2 := hE α y
      rw [abs_of_nonneg (hS0 x α)]
      have := hS0 x α
      nlinarith
    have hδ : ∑ α, S x α * (if α = y then (1 : ℝ) else 0) = S x y := by simp
    have hSxy : S x y ≤ |CS| * bB d p.1.2 p.1.1 x y :=
      (hCS p hadm hW1 x y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hB0 x y))
    calc ∑ α, S x α * ‖G α y‖ ^ 2
        ≤ ∑ α, (2 * W ^ (τ / 2) * (|S x α| * bB d p.1.2 p.1.1 α y) +
            2 * (S x α * (if α = y then 1 else 0))) := Finset.sum_le_sum fun α _ => hpt α
      _ = 2 * W ^ (τ / 2) * ∑ α, |S x α| * bB d p.1.2 p.1.1 α y +
            2 * ∑ α, S x α * (if α = y then 1 else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * W ^ (τ / 2) * (CB * bB d p.1.2 p.1.1 x y) + 2 * (|CS| * bB d p.1.2 p.1.1 x y) := by
          rw [hδ]
          gcongr
          exact hCB p hadm hW1 x y
  have hs0 : 0 ≤ ∑ α, S x α * ‖G α y‖ ^ 2 :=
    Finset.sum_nonneg fun α _ => mul_nonneg (hS0 x α) (sq_nonneg _)
  have hm2 : ‖m‖ ^ 2 ≤ 1 := by
    have := norm_nonneg m
    nlinarith
  have hT : Tvar S G m x y ≤ W ^ τ * bB d p.1.2 p.1.1 x y := by
    unfold Tvar
    have hWτ2 : W ^ τ = W ^ (τ / 2) * W ^ (τ / 2) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have hB := hB0 x y
    have hCS0 := abs_nonneg CS
    calc ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2 ≤ 1 * ∑ α, S x α * ‖G α y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hm2 hs0
      _ ≤ 2 * W ^ (τ / 2) * (CB * bB d p.1.2 p.1.1 x y) + 2 * (|CS| * bB d p.1.2 p.1.1 x y) := by
          rw [one_mul]; exact hsum
      _ ≤ W ^ (τ / 2) * ((2 * CB + 2 * |CS|) * bB d p.1.2 p.1.1 x y) := by
          have : 2 * (|CS| * bB d p.1.2 p.1.1 x y) ≤
              W ^ (τ / 2) * (2 * (|CS| * bB d p.1.2 p.1.1 x y)) :=
            le_mul_of_one_le_left (by positivity) hτ1
          nlinarith
      _ ≤ W ^ (τ / 2) * (W ^ (τ / 2) * bB d p.1.2 p.1.1 x y) := by gcongr
      _ = W ^ τ * bB d p.1.2 p.1.1 x y := by rw [hWτ2]; ring
  exact absurd hω (not_lt.2 hT)

/-! ## The expectation step of [I, (8.17)] -/

/-- The absolute-value graph is nonnegative. -/
private theorem ErrExp_absVal_nonneg {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (D : Data ι) (e : Fin k → ι) : 0 ≤ Γ.absVal D e := by
  unfold Graph.absVal
  refine Finset.sum_nonneg fun s _ => mul_nonneg (norm_nonneg _) (List.prod_nonneg ?_)
  intro a ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
  exact norm_nonneg _

set_option maxHeartbeats 1000000 in
-- the expectation split instantiates several eventual statements at once
set_option linter.unusedVariables false in
-- the first argument of `β` is the size `W`
/-- **The expectation step of [I, (8.17)]** ([II, Claim 8.6], (8.24), and [II, Claim 8.7], read in
expectation) for one graph with the kinds of `Err`: for `d ≥ 8`, a profile `P`, `c₀, c₁ > 0` with
`c₀ + c₁ < 1`, `κ, ε > 0`, the self-energies `Σ_k` of the even orders `4 ≤ k ≤ N`, a graph `Γ`
with `nI` internal atoms and the kinds of `Err` with labels in `[4, N]`, `τ' > 0` and a
deterministic `β(W, L, z, 𝔞, 𝔟)` that bounds, for `W ≥ W₀`, the sum over the sets `S` of the
absolute-value graphs of the label-free graphs `Γ_S` of the light-weight graph of `Γ` at every
single matrix `G̃` with `|G̃_{xy} − m δ_{xy}| ≤ W^{τ'} B_{xy}^{1/2}`: under the local law
[I, Theorem 1.4, (1.19)], for all `τ, D' > 0` there is `L₀` with
`E|Γ_{𝔞,𝔟𝔟}(z)| ≤ W^τ β + W^{−D'}` for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)` and all
`𝔞, 𝔟`. -/
theorem ErrExp.expBound : LocalLawStmt → ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ,
    0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 → 0 < κ → 0 < ε →
    ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    ∀ (nI : ℕ) (Γ : Graph 3 nI), Γ.TKindsErr N →
    ∀ τ' : ℝ, 0 < τ' → ∀ β : ∀ W L : ℕ, ℂ → Zd d L → Zd d L → ℝ,
      (∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z ∈ specDom κ ε W L, ∀ (a b : Zd d L) (G : Matrix (Zd d L) (Zd d L) ℂ),
          (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
          ∑ S ∈ Γ.wDLights.pathElig.powerset, (Γ.wDLights.pathRepl S).absVal
            (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤ β W L z a b) →
    ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ a b : Zd d L,
          ∫ ω, ‖Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω‖
              ∂(rbmLaw d P (sizeOf W L)) ≤
            (W : ℝ) ^ τ * β W L z a b + (W : ℝ) ^ (-D') := by
  intro hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE nI Γ hΓ τ' hτ' β hβ τ hτ D' hD'
  obtain ⟨W₀, hW₀⟩ := hβ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  -- the order of the filter of the label removal: [II, (3.15)] holds on `adm(c₀, c₁)`
  obtain ⟨nF, hnF⟩ : ∃ nF : ℕ, nF = ⌈2 / c₁⌉₊ + 2 := ⟨_, rfl⟩
  have hc₁' : 0 < 2 / c₁ := by positivity
  have hnF1 : 2 / c₁ + 1 ≤ (nF : ℝ) - 1 := by
    rw [hnF]; push_cast; linarith [Nat.le_ceil (2 / c₁)]
  have hthrF : ∀ p : SizeL, p.1 ∈ adm c₀ c₁ → 1 ≤ sizeW p → p ∈ thrSet d nF 1 := by
    refine ErrExp_thr hc₁ ?_
    have h0 : 0 ≤ (nF : ℝ) - 1 := by linarith
    have : ((nF : ℝ) - 1) * 8 ≤ ((nF : ℝ) - 1) * d := mul_le_mul_of_nonneg_left hd' h0
    nlinarith
  have hFeq := ErrExp_llFilter_eq hthrF
  -- the loss `ε₀` of the label removal
  have hnF2 : (2 : ℝ) ≤ nF := by linarith
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ, ε₀ = 1 / (2 * nF) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; positivity
  have hε₀n : ((nF : ℝ) - 1) * ε₀ < 1 := by
    rw [hε₀def, mul_one_div, div_lt_one (by positivity)]; linarith
  have hε₀d : ε₀ < (d : ℝ) / 20 := by
    rw [hε₀def, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- the a priori bound, along a filter equal to `admFilterL c₀ c₁`
  have hFa : llFilter d N c₀ c₁ (((N : ℝ) - 1) * d / 2 - (2 / c₁ - 2)) = admFilterL c₀ c₁ :=
    ErrExp_llFilter_eq (ErrExp_thr hc₁ (by linarith))
  obtain ⟨Ka, q, hKa0, hap⟩ := MainCancel_apriori d hd P c₀ c₁ κ ε
    (((N : ℝ) - 1) * d / 2 - (2 / c₁ - 2)) hc₀ hc₁ hc hκ hε N Sig hSE Γ hΓ
  rw [hFa] at hap
  -- [II, (7.7)], [II, (7.8)] and [II, (8.1)] at `Φ = 0` from the local law
  have hLLn : StochDom (llFilter d nF c₀ c₁ 1) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) := by
    rw [hFeq]
    exact ErrExp_ll hLL hd P hc₀ hc₁ hκ hε (fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2})
      (fun _ u => u.1) (fun _ u => u.2)
  have h77 := Lem512Zero_h77 (by omega) P hLLn ε₀ hε₀.le
  have h78 := Lem512Zero_h78 (by omega) P hLLn ε₀ hε₀.le
  have h81 : StochDom (llFilter d nF c₀ c₁ 1) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2 + (0 : ℝ) ^ 2) := by
    have hT := ErrExp.entryBound hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε
      (fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2}) (fun _ u => u.1) (fun _ u => u.2)
    rw [hFeq]
    intro τ₁ hτ₁ D₁ hD₁
    filter_upwards [hT τ₁ hτ₁ D₁ hD₁] with p hp
    refine le_trans (measure_mono ?_) hp
    rintro ω ⟨v, hv⟩
    exact ⟨v, by simpa using hv⟩
  have hΦ : ∀ᶠ p in llFilter d nF c₀ c₁ 1, ∀ _u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2},
      0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (p.1.1 : ℝ) ^ (-(1 : ℝ)) :=
    Eventually.of_forall fun p _ => ⟨le_rfl, Real.rpow_nonneg (Nat.cast_nonneg _) _⟩
  -- the bound `β` of the label-free graphs
  have hβLR : ∀ᶠ p in llFilter d nF c₀ c₁ 1, ∀ (u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2})
      (a b : Zd d p.1.2) (G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ),
      weakNorm d p.1.2 p.1.1 1 2 (errAbs G u.1) ≤ (p.1.1 : ℝ) ^ (ε₀ + τ') →
      (∀ x y, ‖entryErr G (msc u.1) x y‖ ≤
        (p.1.1 : ℝ) ^ τ' * (Real.sqrt (bB d p.1.2 p.1.1 x y) + 0)) →
      ∑ S ∈ Γ.wDLights.pathElig.powerset, (Γ.wDLights.pathRepl S).absVal
          (gData (Smat P.ψ p.1.1 p.1.2) u.1 Sig G) ![a, b, b] ≤ β p.1.1 p.1.2 u.1 a b := by
    rw [hFeq]
    filter_upwards [ErrExp_ev_adm c₀ c₁, ErrExp_ev_W c₀ c₁ W₀] with p hp hW u a b G _ he
    exact hW₀ p.1.1 p.1.2 hp hW u.1 u.2 a b G fun x y => (he x y).trans_eq (by rw [add_zero])
  -- the label removal
  have hLR := labelRemovalErr d hd P c₀ c₁ κ ε 1 hc₀ hc₁ hc hκ hε one_pos nF Sig ε₀ hε₀ hε₀n
    hε₀d (fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2}) (fun _ u => u.1) (fun _ u => u.2)
    h77 h78 (fun _ _ => 0) 1 one_pos hΦ h81 N nI Γ hΓ τ' hτ'
    (fun p u a b => β p.1.1 p.1.2 u.1 a b) hβLR (τ + D' + 1) (by positivity)
  rw [hFeq] at hLR
  -- the exponents of the exceptional event and of the tail
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈Ka + 2 * d / c₁ + D' + 2⌉₊ := ⟨_, rfl⟩
  have hjge : Ka + 2 * d / c₁ + D' + 2 ≤ (j : ℝ) := by rw [hj]; exact Nat.le_ceil _
  obtain ⟨Cq, hCq⟩ : ∃ Cq : ℝ, Cq = 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) :=
    ⟨_, rfl⟩
  have hgm : 0 ≤ LabelRemoval.gaussMoment (q + j) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hCq0 : 0 ≤ Cq := by rw [hCq]; positivity
  have hDd : 0 < Ka + 2 * q + D' + 1 := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  have hev : ∀ᶠ p in admFilterL c₀ c₁, ∀ (u : {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2})
      (a b : Zd d p.1.2),
      ∫ ω, ‖Γ.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1) ![a, b, b] ω‖
          ∂(rbmLaw d P p) ≤
        (p.1.1 : ℝ) ^ τ * β p.1.1 p.1.2 u.1 a b + (p.1.1 : ℝ) ^ (-D') := by
    filter_upwards [hLR τ hτ (Ka + 2 * q + D' + 1) hDd, hap, ErrExp_ev_adm c₀ c₁,
      ErrExp_ev_W c₀ c₁ (max 3 (max W₂ (max W₀ (3 * Cq + 1))))] with p hbad happ hadm hW u a b
    change max 3 (max W₂ (max W₀ (3 * Cq + 1))) ≤ (p.1.1 : ℝ) at hW
    have hW3 : (3 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
    have hW₂ : W₂ ≤ (p.1.1 : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
    have hW₀' : W₀ ≤ (p.1.1 : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
    have hCqW : 3 * Cq + 1 ≤ (p.1.1 : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
    have hS1 : ∀ c', coordVar (Smat P.ψ p.1.1 p.1.2) c' ≤ 1 :=
      LabelRemoval_coordVar_le _ (hds p.1.1 p.1.2 hadm hW₂)
    -- `β ≥ 0`, from its premise at `G̃ = m`
    have hβ0 : 0 ≤ β p.1.1 p.1.2 u.1 a b := by
      refine le_trans ?_ (hW₀ p.1.1 p.1.2 hadm hW₀' u.1 u.2 a b
        (Matrix.of fun x y => if x = y then msc u.1 else 0) fun x y => ?_)
      · exact Finset.sum_nonneg fun S _ => ErrExp_absVal_nonneg _ _ _
      · have h0 : entryErr (Matrix.of fun x y => if x = y then msc u.1 else 0) (msc u.1) x y =
            0 := by
          unfold entryErr; simp
        rw [h0, norm_zero]
        positivity
    set W : ℝ := (p.1.1 : ℝ) with hWdef
    have hW0 : 0 < W := by linarith
    have hW1 : 1 ≤ W := by linarith
    have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
    -- the expectation of one entry
    set R₂ : ℝ := W ^ τ * W ^ (-(τ + D' + 1)) +
      W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + D' + 1)) +
      W ^ Ka * ((1 + W) ^ j)⁻¹ *
        (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
          Fintype.card (Coord (Zd d p.1.2))) with hR₂
    have hent : ∫ ω, ‖Γ.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1)
        ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤ W ^ τ * β p.1.1 p.1.2 u.1 a b + R₂ := by
      have h := Lem512Zero_integral_le (Smat P.ψ p.1.1 p.1.2) hS1
        (fun ω => ‖Γ.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1)
          ![a, b, b] ω‖)
        {ω | ∃ v : {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2,
          sizeW p ^ τ * (β p.1.1 p.1.2 v.1.1 v.2.1 v.2.2 + sizeW p ^ (-(τ + D' + 1))) <
          ‖Γ.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 v.1.1)
            ![v.2.1, v.2.2, v.2.2] ω‖}
        (W ^ τ * (β p.1.1 p.1.2 u.1 a b + W ^ (-(τ + D' + 1)))) (W ^ Ka) W
        (W ^ (-(Ka + 2 * q + D' + 1))) q j
        (mul_nonneg (by positivity) (add_nonneg hβ0 (by positivity))) (by positivity)
        hW0.le (by positivity) hbad (fun ω => norm_nonneg _)
        (fun ω hω => by
          by_contra hcon
          exact hω ⟨(u, a, b), lt_of_not_ge hcon⟩)
        (fun ω => happ u a b ω)
      refine h.trans (le_of_eq ?_)
      rw [hR₂]
      ring
    -- the small terms
    have hR₂le : R₂ ≤ W ^ (-D') := by
      have t1 : W ^ τ * W ^ (-(τ + D' + 1)) = W ^ (-(D' + 1)) := by
        rw [← Real.rpow_add hW0]; congr 1; ring
      have h1W : 1 + W ≤ W ^ 2 := by nlinarith
      have t2 : W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + D' + 1)) ≤ W ^ (-(D' + 1)) := by
        have : (1 + W) ^ q ≤ W ^ ((2 * q : ℕ) : ℝ) := by
          rw [Real.rpow_natCast, pow_mul]
          exact pow_le_pow_left₀ (by linarith) h1W q
        calc W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + D' + 1))
            ≤ W ^ Ka * W ^ ((2 * q : ℕ) : ℝ) * W ^ (-(Ka + 2 * q + D' + 1)) := by gcongr
          _ = W ^ (-(D' + 1)) := by
              rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; push_cast; ring
      have hcard : (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * W ^ (2 * (d : ℝ) / c₁) := by
        refine LabelRemoval_card_coord.trans ?_
        have h0 : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) :=
          card_Zd_le_adm d c₀ c₁ hc₁ p hadm
        have h2 : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
          calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) h0 2
            _ = W ^ (2 * (d : ℝ) / c₁) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
        linarith
      have hX1 : 1 ≤ W ^ (2 * (d : ℝ) / c₁) := Real.one_le_rpow hW1 (by positivity)
      have hMq : 1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
          (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ W ^ (2 * (d : ℝ) / c₁ + 1) := by
        rw [Real.rpow_add hW0, Real.rpow_one, ← hCq]
        have e1 : Cq * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤
            3 * Cq * W ^ (2 * (d : ℝ) / c₁) := by nlinarith
        nlinarith
      have t3 : W ^ Ka * ((1 + W) ^ j)⁻¹ *
          (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
            Fintype.card (Coord (Zd d p.1.2))) ≤ W ^ (-(D' + 1)) := by
        have hinv : ((1 + W) ^ j)⁻¹ ≤ W ^ (-(j : ℝ)) := by
          rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hW0.le (by linarith) j)
        calc W ^ Ka * ((1 + W) ^ j)⁻¹ *
              (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
                Fintype.card (Coord (Zd d p.1.2)))
            ≤ W ^ Ka * W ^ (-(j : ℝ)) * W ^ (2 * (d : ℝ) / c₁ + 1) := by gcongr
          _ = W ^ (Ka - j + (2 * (d : ℝ) / c₁ + 1)) := by
              rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
          _ ≤ W ^ (-(D' + 1)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      have hsum3 : 3 * W ^ (-(D' + 1)) ≤ W ^ (-D') := by
        have e' : W ^ (-D') = W ^ (-(D' + 1)) * W := by
          rw [← Real.rpow_add_one hW0.ne']; congr 1; ring
        rw [e']
        have : 0 ≤ W ^ (-(D' + 1)) := Real.rpow_nonneg hW0.le _
        nlinarith
      rw [hR₂]
      linarith
    linarith
  obtain ⟨L₀, hL₀⟩ := ErrExp_explicit hc₁ hev
  refine ⟨L₀, fun W L _ hL hadm z hz a b => ?_⟩
  exact hL₀ (sizeOf W L) hL hadm ⟨z, hz⟩ a b

end RBM8D
