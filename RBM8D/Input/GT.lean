module

public import RBM8D.Prob.Model
public import RBM8D.Prob.StochDom
public import RBM8D.Prob.Partial
public import RBM8D.Basic.Minor
public import RBM8D.Basic.Domain
public import RBM8D.Basic.Semicircle
public import RBM8D.Profile.Basic
public import RBM8D.Input.Sizes
public import RBM8D.Input.Entry
public import RBM8D.Input.EntryDiag
public import RBM8D.Input.LDEDom

@[expose] public section

/-!
# The off-diagonal input estimate [I, (5.2)]

The parameters and the hypothesis [I, (5.1)] of [I, Lemma 5.1] = [II, Lemma 7.1], and the bound
[I, (5.2)] with its column form.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

/-- The parameters of [I, Lemma 5.1]: eventually along the filter, `z(W, L, u) ∈ 𝐃(κ, ε)` and
`W^{−d/2} ≤ Φ(W, L, u) ≤ W^{−δ₀}` for every `u`. -/
def GTParams (d : ℕ) (c₀ c₁ κ ε δ₀ : ℝ) (U : SizeL → Type) (z : ∀ p, U p → ℂ)
    (Φ : ∀ p, U p → ℝ) : Prop :=
  ∀ᶠ p in admFilterL c₀ c₁, ∀ u, z p u ∈ specDom κ ε p.1.1 p.1.2 ∧
    sizeW p ^ (-(d : ℝ) / 2) ≤ Φ p u ∧ Φ p u ≤ sizeW p ^ (-δ₀)

/-- [I, (5.1)]: `‖G(z) − m(z)‖_max ≺ W^{−δ₀}` and `‖T(z)‖_max ≺ Φ²`, uniformly in
`z = z(W, L, u)`. -/
def InitialGT (d : ℕ) (P : Profile d) (c₀ c₁ δ₀ : ℝ) (U : SizeL → Type) (z : ∀ p, U p → ℂ)
    (Φ : ∀ p, U p → ℝ) : Prop :=
  StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => ‖entryErr (green (hmat ω) (z p v.1)) (msc (z p v.1)) v.2.1 v.2.2‖)
      (fun p _ _ => sizeW p ^ (-δ₀)) ∧
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) (msc (z p v.1))
        v.2.1 v.2.2)
      (fun p v _ => Φ p v.1 ^ 2)

/-! ## Two good events and the exponents -/

/-- If eventually `S ⊆ A ∪ B` and `P(A), P(B) ≤ size^{−D−1}`, then eventually
`P(S) ≤ size^{−D}`. -/
private theorem gt_two_union_bound {Par : Type*} {Ω : Par → Type*} [∀ p, MeasurableSpace (Ω p)]
    (F : Filter Par) (size : Par → ℝ) (P : ∀ p, Measure (Ω p)) (hsize : Tendsto size F atTop)
    (S A B : ∀ p, Set (Ω p)) (D : ℝ) (hS : ∀ᶠ p in F, S p ⊆ A p ∪ B p)
    (hA : ∀ᶠ p in F, P p (A p) ≤ ENNReal.ofReal (size p ^ (-(D + 1))))
    (hB : ∀ᶠ p in F, P p (B p) ≤ ENNReal.ofReal (size p ^ (-(D + 1)))) :
    ∀ᶠ p in F, P p (S p) ≤ ENNReal.ofReal (size p ^ (-D)) := by
  filter_upwards [hsize.eventually (eventually_ge_atTop 2), hS, hA, hB] with p h2 hSp hAp hBp
  have hs : 0 < size p := by linarith
  have hnn : 0 ≤ size p ^ (-(D + 1)) := (Real.rpow_pos_of_pos hs _).le
  have hexp : size p ^ (-(D + 1)) = size p ^ (-D) * (size p)⁻¹ := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hs, Real.rpow_neg_one]
  have hinv : (size p)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
  have hle : size p ^ (-(D + 1)) + size p ^ (-(D + 1)) ≤ size p ^ (-D) := by
    have h0 : 0 ≤ size p ^ (-D) := (Real.rpow_pos_of_pos hs _).le
    rw [hexp]; nlinarith
  calc P p (S p) ≤ P p (A p ∪ B p) := measure_mono hSp
    _ ≤ P p (A p) + P p (B p) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (size p ^ (-(D + 1))) + ENNReal.ofReal (size p ^ (-(D + 1))) :=
        add_le_add hAp hBp
    _ = ENNReal.ofReal (size p ^ (-(D + 1)) + size p ^ (-(D + 1))) :=
        (ENNReal.ofReal_add hnn hnn).symm
    _ ≤ ENNReal.ofReal (size p ^ (-D)) := ENNReal.ofReal_le_ofReal hle

/-- `ξ ≺ ζ` from `ξ_A ≺ ζ_A` and `ξ_B ≺ ζ_B`, if for each `τ > 0` there is `τ' > 0` such that,
eventually, `ξ_A ≤ size^{τ'} ζ_A` and `ξ_B ≤ size^{τ'} ζ_B` for all `u` imply
`ξ ≤ size^τ ζ` for all `u`. -/
private theorem gt_of_two {Par : Type*} {Ω : Par → Type*} [∀ p, MeasurableSpace (Ω p)]
    {U : Par → Type*} (F : Filter Par) (size : Par → ℝ) (P : ∀ p, Measure (Ω p))
    (ξ ζ ξA ζA ξB ζB : ∀ p, U p → Ω p → ℝ) (hsize : Tendsto size F atTop)
    (hA : StochDom F size P ξA ζA) (hB : StochDom F size P ξB ζB)
    (hdet : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ p in F, ∀ ω,
      (∀ u, ξA p u ω ≤ size p ^ τ' * ζA p u ω) → (∀ u, ξB p u ω ≤ size p ^ τ' * ζB p u ω) →
        ∀ u, ξ p u ω ≤ size p ^ τ * ζ p u ω) :
    StochDom F size P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hd⟩ := hdet τ hτ
  refine gt_two_union_bound F size P hsize (fun p => {ω | ∃ u, size p ^ τ * ζ p u ω < ξ p u ω})
    (fun p => {ω | ∃ u, size p ^ τ' * ζA p u ω < ξA p u ω})
    (fun p => {ω | ∃ u, size p ^ τ' * ζB p u ω < ξB p u ω}) D ?_
    (hA τ' hτ' (D + 1) (by linarith)) (hB τ' hτ' (D + 1) (by linarith))
  filter_upwards [hd] with p hp ω hω
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hc
  obtain ⟨u, hu⟩ := hω
  exact absurd (hp ω hc.1 hc.2 u) (not_le.2 hu)

/-- With `τ' = min(τ, δ₀)/2`, eventually as `W → ∞`: `W ≥ 1`, `δ = W^{τ'} W^{−δ₀} ≤ 1/4`,
`W^{τ'} δ ≤ 1` and `16 W^{τ'} ≤ W^τ`. -/
private theorem gt_rows (τ δ₀ : ℝ) (hτ : 0 < τ) (hδ₀ : 0 < δ₀) :
    ∀ᶠ W : ℝ in atTop, 1 ≤ W ∧ W ^ (min τ δ₀ / 2) * W ^ (-δ₀) ≤ 1 / 4 ∧
      W ^ (min τ δ₀ / 2) * (W ^ (min τ δ₀ / 2) * W ^ (-δ₀)) ≤ 1 ∧
      16 * W ^ (min τ δ₀ / 2) ≤ W ^ τ := by
  have h1 : min τ δ₀ / 2 ≤ τ / 2 := by have := min_le_left τ δ₀; linarith
  have h2 : min τ δ₀ / 2 ≤ δ₀ / 2 := by have := min_le_right τ δ₀; linarith
  have hpos : 0 < min τ δ₀ / 2 := by have := lt_min hτ hδ₀; linarith
  have hA : ∀ᶠ W : ℝ in atTop, W ^ (-(δ₀ - min τ δ₀ / 2)) < 1 / 4 :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < δ₀ - min τ δ₀ / 2)).eventually
      (gt_mem_nhds (by norm_num))
  have hB : ∀ᶠ W : ℝ in atTop, 16 < W ^ (τ - min τ δ₀ / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < τ - min τ δ₀ / 2)).eventually (eventually_gt_atTop 16)
  filter_upwards [hA, hB, eventually_ge_atTop 1] with W hWA hWB hW1
  have hW0 : 0 < W := by linarith
  have e1 : W ^ (min τ δ₀ / 2) * W ^ (-δ₀) = W ^ (-(δ₀ - min τ δ₀ / 2)) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have e2 : W ^ (min τ δ₀ / 2) * W ^ (-(δ₀ - min τ δ₀ / 2)) = W ^ (2 * (min τ δ₀ / 2) - δ₀) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have e3 : W ^ (min τ δ₀ / 2) * W ^ (τ - min τ δ₀ / 2) = W ^ τ := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  refine ⟨hW1, by rw [e1]; linarith, ?_, ?_⟩
  · rw [e1, e2]; exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  · rw [← e3]; have := Real.rpow_pos_of_pos hW0 (min τ δ₀ / 2); nlinarith

/-- Eventually along `admFilterL c₀ c₁`, `(W, L) ∈ adm(c₀, c₁)`. -/
private theorem gt_eventually_adm (c₀ c₁ : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  exact tendsto_comap.eventually h

/-- For `W ≥ 1`, `L ≠ 0` and `0 < κ`, every `z ∈ 𝐃(κ, ε)` has `Im z > 0`, `|z| ≤ 3` and
`|m(z)| ≥ 1/4`. -/
private theorem gt_specDom {κ ε : ℝ} (hκ : 0 < κ) (p : SizeL) (hW : 1 ≤ sizeW p) (z : ℂ)
    (hz : z ∈ specDom κ ε p.1.1 p.1.2) : 0 < z.im ∧ 1 / 4 ≤ ‖msc z‖ := by
  obtain ⟨hre, him, him1⟩ := hz
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hW1 : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW
  have hpos : 0 < (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) :=
    div_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
  have hzim : 0 < z.im := lt_of_lt_of_le hpos him
  refine ⟨hzim, norm_msc_ge_quarter z hzim ?_⟩
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hzim] at this
  linarith

/-- Eventually along `admFilterL c₀ c₁`: `W ≥ 1`, `s_{xy} ≥ 0`, `Σ_y s_{xy} = 1`, and every
`z(W, L, u)` has `Im z > 0` and `|m(z)| ≥ 1/4`, under the parameter clause of [I, Lemma 5.1]. -/
private theorem gt_eventually {d : ℕ} (P : Profile d) {c₀ c₁ κ ε δ₀ : ℝ} (hc₀ : 0 < c₀)
    (hκ : 0 < κ) (U : SizeL → Type) (z : ∀ p, U p → ℂ) (Φ : ∀ p, U p → ℝ)
    (hpar : GTParams d c₀ c₁ κ ε δ₀ U z Φ) :
    ∀ᶠ p in admFilterL c₀ c₁, 1 ≤ sizeW p ∧ (∀ a b, 0 ≤ Smat P.ψ p.1.1 p.1.2 a b) ∧
      (∀ a, ∑ b, Smat P.ψ p.1.1 p.1.2 a b ≤ 1) ∧
      ∀ u, 0 < (z p u).im ∧ 1 / 4 ≤ ‖msc (z p u)‖ := by
  obtain ⟨W₀, hW₀⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  filter_upwards [gt_eventually_adm c₀ c₁, hpar,
    (tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_ge_atTop (max 1 W₀))] with p hp hz hW
  have hds := hW₀ p.1.1 p.1.2 hp ((le_max_right _ _).trans hW)
  have hW1 : 1 ≤ sizeW p := (le_max_left _ _).trans hW
  exact ⟨hW1, fun a b => nonneg_of_mem_doublyStochastic hds,
    fun a => (sum_row_of_mem_doublyStochastic hds a).le,
    fun u => gt_specDom hκ p hW1 (z p u) (hz u).1⟩

/-- `4 Φ δ² ≤ 1` from `0 ≤ δ ≤ 1/4` and `Φ δ ≤ 1`. -/
private theorem gt_absorb {Φ δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hΦδ : Φ * δ ≤ 1) :
    4 * Φ * δ ^ 2 ≤ 1 := by
  have : Φ * δ * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hΦδ hδ0
  nlinarith

/-! ## [I, (5.2)] and its column form -/

/-- **[I, Lemma 5.1, (5.2)]** = [II, Lemma 7.1, (7.2)]: under [I, (5.1)] for a family of at most
`W^{C_U}` spectral parameters in `𝐃(κ, ε)`, `1_{x≠y} |G_{xy}|² ≺ T_{xy}` uniformly in `x, y`
and `u`. -/
theorem offDiagGT :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ →
  ∀ (κ ε δ₀ CU : ℝ), 0 < κ → 0 < δ₀ →
  ∀ (U : SizeL → Type) [∀ p, Fintype (U p)] (z : ∀ p, U p → ℂ) (Φ : ∀ p, U p → ℝ),
    (∀ᶠ p in admFilterL c₀ c₁, (Fintype.card (U p) : ℝ) ≤ sizeW p ^ CU) →
    GTParams d c₀ c₁ κ ε δ₀ U z Φ → InitialGT d P c₀ c₁ δ₀ U z Φ →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => if v.2.1 = v.2.2 then 0 else ‖green (hmat ω) (z p v.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v ω => Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) (msc (z p v.1))
        v.2.1 v.2.2) := by
  intro d P c₀ c₁ hc₀ hc₁ κ ε δ₀ CU hκ hδ₀ U _ z Φ hU hpar hI
  have hev := gt_eventually P hc₀ hκ U z Φ hpar
  have him : ∀ᶠ p in admFilterL c₀ c₁, ∀ u, 0 < (z p u).im := hev.mono fun p hp u => (hp.2.2.2 u).1
  refine gt_of_two _ _ _ _ _ _ _ _ _ (tendsto_sizeW_admFilterL c₀ c₁) hI.1
    (ldeRowDom d P c₀ c₁ CU hc₀ hc₁ U z hU him) ?_
  intro τ hτ
  refine ⟨min τ δ₀ / 2, by have := lt_min hτ hδ₀; linarith, ?_⟩
  filter_upwards [hev, (tendsto_sizeW_admFilterL c₀ c₁).eventually (gt_rows τ δ₀ hτ hδ₀)] with
    p hp hr ω hA hB v
  obtain ⟨_, hS0, hS1, hz⟩ := hp
  obtain ⟨hW1, hδ, hΦδ, h16⟩ := hr
  obtain ⟨u, x, y⟩ := v
  have hW0 : 0 < sizeW p := by linarith
  have hT : 0 ≤ Tvar (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p u)) (msc (z p u)) x y :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun α _ => mul_nonneg (hS0 x α) (sq_nonneg _))
  have hδ0 : 0 ≤ sizeW p ^ (min τ δ₀ / 2) * sizeW p ^ (-δ₀) :=
    mul_nonneg (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _)
  dsimp only
  split_ifs with hxy
  · exact mul_nonneg (Real.rpow_nonneg hW0.le _) hT
  · have hdet := offDiagDet (hmat ω) (z p u) (msc (z p u)) (Smat P.ψ p.1.1 p.1.2)
      (sizeW p ^ (min τ δ₀ / 2) * sizeW p ^ (-δ₀)) (sizeW p ^ (min τ δ₀ / 2))
      (hmat_isHermitian ω) (hz u).1 (fun a b => hA (u, a, b)) (hδ.trans (hz u).2) hS0 hS1
      (Real.rpow_nonneg hW0.le _) (gt_absorb hδ0 hδ hΦδ) (fun a b => hB (u, a, b)) x y hxy
    exact hdet.trans (mul_le_mul_of_nonneg_right h16 hT)

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

section Instances

end Instances

end RBM8D
