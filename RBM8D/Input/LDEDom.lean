import RBM8D.Prob.Model
import RBM8D.Prob.StochDom
import RBM8D.Prob.Partial
import RBM8D.Basic.Minor
import RBM8D.Basic.Domain
import RBM8D.Basic.Semicircle
import RBM8D.Profile.Basic
import RBM8D.Input.Sizes
import RBM8D.Input.Entry
import RBM8D.Input.LDELin
import RBM8D.Input.LDEQuad

/-!
# Large deviation bounds as stochastic domination along `adm(c₀, c₁)`

The row, column, quadratic and diagonal large deviation bounds for the resolvent minors of the model
of [I, Assumption 1.1], as `≺` at scale `W` along `W → ∞` inside `adm(c₀, c₁)`, uniformly in the
indices and in a family of at most `W^{C_U}` spectral parameters.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

/-- The union bound behind `≺` ([I, Definition 2.3 (i)]) for a finite family of indices `u`: if
eventually in `F`, for every `q`, each event `{t ζ(u) < ξ(u)}` has probability at most `C_q t^{−q}`
uniformly in `u` and `t > 0`, and the number of indices is at most `size^N`, then `ξ ≺ ζ` uniformly
in `u`. It suffices to take `q = ⌈(D + 1 + N)/τ⌉` and `t = size^τ`. -/
private theorem ldeDom_stochDom_of_tail {Par : Type*} {Ω : Par → Type*}
    [∀ p, MeasurableSpace (Ω p)] {U : Par → Type*} [∀ p, Fintype (U p)] (F : Filter Par)
    (size : Par → ℝ) (μ : ∀ p, Measure (Ω p)) (ξ ζ : ∀ p, U p → Ω p → ℝ) (N : ℝ)
    (hsize : Tendsto size F atTop) (hcard : ∀ᶠ p in F, (Fintype.card (U p) : ℝ) ≤ size p ^ N)
    (htail : ∀ q : ℕ, ∃ C : ℝ, ∀ᶠ p in F, ∀ t : ℝ, 0 < t → ∀ u,
      μ p {ω | t * ζ p u ω < ξ p u ω} ≤ ENNReal.ofReal (C / t ^ q)) :
    StochDom F size μ ξ ζ := by
  intro τ hτ D hD
  obtain ⟨C, hC⟩ := htail ⌈(D + 1 + N) / τ⌉₊
  filter_upwards [hcard, hC, hsize.eventually (eventually_ge_atTop (max 1 C))] with p hp1 hp2 hp3
  set W := size p with hW
  set q := ⌈(D + 1 + N) / τ⌉₊ with hq
  have hW1 : 1 ≤ W := (le_max_left _ _).trans hp3
  have hWC : C ≤ W := (le_max_right _ _).trans hp3
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW1
  have hτq : D + 1 + N ≤ τ * q := by
    have h1 : (D + 1 + N) / τ ≤ q := Nat.le_ceil _
    rw [div_le_iff₀ hτ] at h1
    linarith
  have ht : 0 < W ^ τ := Real.rpow_pos_of_pos hW0 _
  have ha : (W ^ τ) ^ q = W ^ (τ * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hapos : 0 < W ^ (τ * q) := Real.rpow_pos_of_pos hW0 _
  have hset : {ω | ∃ u, W ^ τ * ζ p u ω < ξ p u ω} = ⋃ u, {ω | W ^ τ * ζ p u ω < ξ p u ω} := by
    ext ω; simp
  calc μ p {ω | ∃ u, W ^ τ * ζ p u ω < ξ p u ω}
      = μ p (⋃ u, {ω | W ^ τ * ζ p u ω < ξ p u ω}) := by rw [hset]
    _ ≤ ∑ u, μ p {ω | W ^ τ * ζ p u ω < ξ p u ω} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _u : U p, ENNReal.ofReal (C / (W ^ τ) ^ q) :=
        Finset.sum_le_sum fun u _ => hp2 _ ht u
    _ = ENNReal.ofReal ((Fintype.card (U p) : ℝ) * (C / (W ^ τ) ^ q)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (W ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        set C' := max C 0 with hC'
        have hC'0 : 0 ≤ C' := le_max_right _ _
        have hC'W : C' ≤ W := max_le hWC hW0.le
        have hexp : W ^ N / W ^ (τ * q) ≤ W ^ (-(D + 1)) := by
          rw [← Real.rpow_sub hW0]
          exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        have hneg : W ^ (-(D + 1)) = W ^ (-D) * W⁻¹ := by
          rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hW0, Real.rpow_neg_one]
        have hD0 : 0 < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
        rw [ha]
        calc (Fintype.card (U p) : ℝ) * (C / W ^ (τ * q))
            ≤ (Fintype.card (U p) : ℝ) * (C' / W ^ (τ * q)) :=
              mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right (le_max_left _ _) hapos.le) (Nat.cast_nonneg _)
          _ ≤ W ^ N * (C' / W ^ (τ * q)) :=
              mul_le_mul_of_nonneg_right hp1 (div_nonneg hC'0 hapos.le)
          _ = C' * (W ^ N / W ^ (τ * q)) := by ring
          _ ≤ C' * W ^ (-(D + 1)) := mul_le_mul_of_nonneg_left hexp hC'0
          _ = C' * W⁻¹ * W ^ (-D) := by rw [hneg]; ring
          _ ≤ W ^ (-D) := by
              have : C' * W⁻¹ ≤ 1 := by
                rw [← div_eq_mul_inv, div_le_one hW0]; exact hC'W
              nlinarith

section Coefficients

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `h_ab` depends only on the coordinates in `entryCoords a b`. -/
private lemma ldeDom_hmat_congr {ω ω' : Sample ι} (a b : ι)
    (h : ∀ c ∈ entryCoords a b, ω c = ω' c) : hmat ω a b = hmat ω' a b := by
  simp only [hmat, Matrix.of_apply]
  split_ifs with h1 h2
  · rw [h _ (by simp [entryCoords]), h _ (by simp [entryCoords])]
  · rw [h _ (by simp [entryCoords]), h _ (by simp [entryCoords])]
  · obtain rfl : a = b := idxKey_injective (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
    rw [h _ (by simp [entryCoords])]

/-- The coordinates of `h_kl` with `k, l ≠ x` are not coordinates of row `x`. -/
private lemma ldeDom_notMem_rowCoords {x k l : ι} (hk : k ≠ x) (hl : l ≠ x)
    {c : Coord ι} (hc : c ∈ entryCoords k l) : c ∉ rowCoords x := by
  intro hx
  simp only [rowCoords, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
  obtain ⟨y, hy⟩ := hx
  rcases c with w | ⟨e, β⟩
  · simp only [entryCoords, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      at hc hy
    exact hk (hc.1.symm.trans hy.1)
  · simp only [entryCoords, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      at hc hy
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hk (h1.symm.trans h3)
    · exact hl (h2.symm.trans h4)
    · exact hl (h1.symm.trans h3)
    · exact hk (h2.symm.trans h4)

/-- The resolvent minor entries `G^{(x)}_{ab}` do not depend on row and column `x` of `H`. -/
private lemma ldeDom_freeOf_greenMinor (z : ℂ) (hz : 0 < z.im) (x a b : ι) :
    FreeOf (rowCoords x) fun ω : Sample ι => greenMinor (green (hmat ω) z) x a b := by
  intro ω η
  have hzero : ∀ ω' : Sample ι, (a = x ∨ b = x) → greenMinor (green (hmat ω') z) x a b = 0 := by
    intro ω' hab
    have hne := green_diag_ne_zero (hmat_isHermitian ω') hz x
    rcases hab with rfl | rfl
    · unfold greenMinor
      field_simp
      ring
    · unfold greenMinor
      field_simp
      ring
  change greenMinor (green (hmat ((rowCoords x).piecewise η ω)) z) x a b =
    greenMinor (green (hmat ω) z) x a b
  by_cases hab : a = x ∨ b = x
  · rw [hzero _ hab, hzero _ hab]
  · obtain ⟨ha, hb⟩ := not_or.mp hab
    have key : ∀ ω' : Sample ι, greenMinor (green (hmat ω') z) x a b =
        (((hmat ω').submatrix Subtype.val Subtype.val -
          z • (1 : Matrix {k : ι // k ≠ x} {k : ι // k ≠ x} ℂ) :
            Matrix {k : ι // k ≠ x} {k : ι // k ≠ x} ℂ)⁻¹) ⟨a, ha⟩ ⟨b, hb⟩ := fun ω' => by
      rw [inv_minor_resolvent (hmat_isHermitian ω') hz x]
      rfl
    have hsub : (hmat ((rowCoords x).piecewise η ω)).submatrix
          (Subtype.val : {k : ι // k ≠ x} → ι) (Subtype.val : {k : ι // k ≠ x} → ι) =
        (hmat ω).submatrix (Subtype.val : {k : ι // k ≠ x} → ι)
          (Subtype.val : {k : ι // k ≠ x} → ι) := by
      ext k l
      exact ldeDom_hmat_congr k.1 l.1 fun c hc =>
        Finset.piecewise_eq_of_notMem _ _ _ (ldeDom_notMem_rowCoords k.2 l.2 hc)
    rw [key, key, hsub]

omit [DecidableEq ι] in
/-- Every entry of `H(ω)` is a continuous function of the sample. -/
private lemma ldeDom_continuous_hmat : Continuous fun ω : Sample ι => hmat ω := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [hmat, Matrix.of_apply]
  split_ifs <;> fun_prop

/-- The entries of the Green function are measurable functions of the sample. -/
private lemma ldeDom_measurable_green {z : ℂ} (a b : ι) :
    Measurable fun ω : Sample ι => green (hmat ω) z a b := by
  have h1 : Continuous fun ω : Sample ι => hmat ω - z • (1 : Matrix ι ι ℂ) :=
    ldeDom_continuous_hmat.sub continuous_const
  have h2 : Continuous fun ω : Sample ι => (hmat ω - z • (1 : Matrix ι ι ℂ)).det :=
    h1.matrix_det
  have h3 : Continuous fun ω : Sample ι => (hmat ω - z • (1 : Matrix ι ι ℂ)).adjugate :=
    h1.matrix_adjugate
  have h4 : Measurable fun ω : Sample ι => ((hmat ω - z • (1 : Matrix ι ι ℂ)).det)⁻¹ :=
    h2.measurable.inv
  have h5 : Measurable fun ω : Sample ι => (hmat ω - z • (1 : Matrix ι ι ℂ)).adjugate a b :=
    ((continuous_apply b).comp ((continuous_apply a).comp h3)).measurable
  have h6 : Measurable fun ω : Sample ι => ((hmat ω - z • (1 : Matrix ι ι ℂ)).det)⁻¹ *
      (hmat ω - z • (1 : Matrix ι ι ℂ)).adjugate a b := h4.mul h5
  have e : (fun ω : Sample ι => green (hmat ω) z a b) = fun ω : Sample ι =>
      ((hmat ω - z • (1 : Matrix ι ι ℂ)).det)⁻¹ *
        (hmat ω - z • (1 : Matrix ι ι ℂ)).adjugate a b := by
    funext ω
    rw [green, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [e]
  exact h6

/-- The resolvent minor entries are measurable functions of the sample. -/
private lemma ldeDom_measurable_greenMinor {z : ℂ} (x a b : ι) :
    Measurable fun ω : Sample ι => greenMinor (green (hmat ω) z) x a b := by
  have := ldeDom_measurable_green (ι := ι) (z := z)
  unfold greenMinor
  fun_prop

/-- For `Im z > 0`, `|G^{(x)}_{ab}| ≤ (Im z)⁻¹`: the entry vanishes if `a = x` or `b = x`, and is
otherwise an entry of the resolvent of the Hermitian minor `H^{(x)}`. -/
private lemma ldeDom_norm_greenMinor_le {z : ℂ} (hz : 0 < z.im) (ω : Sample ι) (x a b : ι) :
    ‖greenMinor (green (hmat ω) z) x a b‖ ≤ |z.im|⁻¹ := by
  have hxx := green_diag_ne_zero (hmat_isHermitian ω) hz x
  by_cases ha : a = x
  · subst ha
    simp only [greenMinor, mul_div_cancel_left₀ _ hxx, sub_self, norm_zero]
    positivity
  by_cases hb : b = x
  · subst hb
    simp only [greenMinor, mul_div_cancel_right₀ _ hxx, sub_self, norm_zero]
    positivity
  rw [← minorGreen_eq_greenMinor _ x ⟨a, ha⟩ ⟨b, hb⟩,
    ← inv_minor_resolvent (hmat_isHermitian ω) hz x]
  exact norm_green_entry_le ((hmat_isHermitian ω).submatrix _) hz.ne' _ _

/-- The column sum `Σ_{k≠x} G^{(x)}_{yk} h_{kx}` has the modulus of the row sum with the conjugated
coefficients `conj G^{(x)}_{yk}`, since `h_{kx} = conj h_{xk}`. -/
private lemma ldeDom_colLHS_eq (ω : Sample ι) (G : Matrix ι ι ℂ) (x y : ι) :
    ldeColLHS (hmat ω) G x y =
      ‖∑ k : {a : ι // a ≠ x}, hmat ω x k.1 * (starRingEnd ℂ) (greenMinor G x y k.1)‖ ^ 2 := by
  unfold ldeColLHS
  congr 1
  rw [← Complex.norm_conj (∑ k : {a : ι // a ≠ x}, greenMinor G x y k.1 * hmat ω k.1 x)]
  congr 1
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (starRingEnd ℂ) (hmat ω k.1 x) = hmat ω x k.1 := (hmat_isHermitian ω).apply x k.1
  rw [e, mul_comm]

/-- The variance of the column sum is that of the row sum with the conjugated coefficients. -/
private lemma ldeDom_colRHS_eq (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (x y : ι) :
    ldeColRHS S G x y =
      ∑ k : {a : ι // a ≠ x}, S x k.1 * ‖(starRingEnd ℂ) (greenMinor G x y k.1)‖ ^ 2 := by
  unfold ldeColRHS
  simp only [Complex.norm_conj]

end Coefficients

/-! ## The filter, the variance matrix and the number of indices -/

/-- Along `admFilterL c₀ c₁`, eventually `(W, L) ∈ adm(c₀, c₁)`. -/
private lemma ldeDom_eventually_adm (c₀ c₁ : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  exact tendsto_comap.eventually h

/-- Eventually along `admFilterL c₀ c₁`, `S = (s_{xy})` is symmetric with nonnegative entries. -/
private lemma ldeDom_eventually_S {d : ℕ} (P : Profile d) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) :
    ∀ᶠ p in admFilterL c₀ c₁,
      (Smat P.ψ p.1.1 p.1.2).IsSymm ∧ ∀ a b, 0 ≤ Smat P.ψ p.1.1 p.1.2 a b := by
  obtain ⟨W₀, hW₀⟩ := P.f_symm c₀ c₁ hc₀ hc₁
  filter_upwards [ldeDom_eventually_adm c₀ c₁,
    (tendsto_sizeW_admFilterL c₀ c₁).eventually
      (eventually_ge_atTop (((max 1 W₀ : ℕ)) : ℝ))] with p hp hW
  have hW' : max 1 W₀ ≤ p.1.1 := by
    have : ((max 1 W₀ : ℕ) : ℝ) ≤ (p.1.1 : ℝ) := hW
    exact_mod_cast this
  refine ⟨?_, fun a b => P.f_nonneg p.1.1 p.1.2 ((le_max_left _ _).trans hW') (a - b)⟩
  ext a b
  simp only [Matrix.transpose_apply, Smat, Matrix.of_apply]
  rw [← neg_sub a b]
  exact hW₀ p.1.1 p.1.2 hp ((le_max_right _ _).trans hW') (a - b)

/-- Eventually along `admFilterL c₀ c₁`, `s_{xy} ≥ 0`. -/
private lemma ldeDom_eventually_nonneg {d : ℕ} (P : Profile d) (c₀ c₁ : ℝ) :
    ∀ᶠ p in admFilterL c₀ c₁, ∀ a b, 0 ≤ Smat P.ψ p.1.1 p.1.2 a b := by
  filter_upwards [(tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_ge_atTop 1)] with p hW
  have hW' : 1 ≤ p.1.1 := by
    have : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW
    exact_mod_cast this
  exact fun a b => P.f_nonneg p.1.1 p.1.2 hW' (a - b)

/-- `#(U × Z_L^d × Z_L^d) ≤ W^{C_U + 2d/c₁}` on `adm(c₀, c₁)`, given `#U ≤ W^{C_U}`. -/
private lemma ldeDom_card_two (d : ℕ) (c₀ c₁ CU : ℝ) (hc₁ : 0 < c₁) (U : SizeL → Type)
    [∀ p, Fintype (U p)]
    (hU : ∀ᶠ p in admFilterL c₀ c₁, (Fintype.card (U p) : ℝ) ≤ sizeW p ^ CU) :
    ∀ᶠ p in admFilterL c₀ c₁,
      (Fintype.card (U p × Zd d p.1.2 × Zd d p.1.2) : ℝ) ≤
        sizeW p ^ (CU + ((d : ℝ) / c₁ + (d : ℝ) / c₁)) := by
  filter_upwards [hU, ldeDom_eventually_adm c₀ c₁,
    (tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_gt_atTop 0)] with p h1 h2 h3
  have h4 := card_Zd_le_adm d c₀ c₁ hc₁ p h2
  rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul, Real.rpow_add h3,
    Real.rpow_add h3]
  exact mul_le_mul h1 (mul_le_mul h4 h4 (Nat.cast_nonneg _) (Real.rpow_nonneg h3.le _))
    (by positivity) (Real.rpow_nonneg h3.le _)

/-- `#(U × Z_L^d) ≤ W^{C_U + d/c₁}` on `adm(c₀, c₁)`, given `#U ≤ W^{C_U}`. -/
private lemma ldeDom_card_one (d : ℕ) (c₀ c₁ CU : ℝ) (hc₁ : 0 < c₁) (U : SizeL → Type)
    [∀ p, Fintype (U p)]
    (hU : ∀ᶠ p in admFilterL c₀ c₁, (Fintype.card (U p) : ℝ) ≤ sizeW p ^ CU) :
    ∀ᶠ p in admFilterL c₀ c₁,
      (Fintype.card (U p × Zd d p.1.2) : ℝ) ≤ sizeW p ^ (CU + (d : ℝ) / c₁) := by
  filter_upwards [hU, ldeDom_eventually_adm c₀ c₁,
    (tendsto_sizeW_admFilterL c₀ c₁).eventually (eventually_gt_atTop 0)] with p h1 h2 h3
  have h4 := card_Zd_le_adm d c₀ c₁ hc₁ p h2
  rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_add h3]
  exact mul_le_mul h1 h4 (Nat.cast_nonneg _) (Real.rpow_nonneg h3.le _)

/-- `|Σ_{k≠x} h_{xk} G^{(x)}_{ky}|² ≺ Σ_{k≠x} s_{xk} |G^{(x)}_{ky}|²` uniformly in `x, y` and
`u ∈ U(W, L)`, for spectral parameters `z(W, L, u) ∈ ℂ₊` and `#U(W, L) ≤ W^{C_U}`. -/
theorem ldeRowDom :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ CU : ℝ), 0 < c₀ → 0 < c₁ →
  ∀ (U : SizeL → Type) [∀ p, Fintype (U p)] (z : ∀ p, U p → ℂ),
    (∀ᶠ p in admFilterL c₀ c₁, (Fintype.card (U p) : ℝ) ≤ sizeW p ^ CU) →
    (∀ᶠ p in admFilterL c₀ c₁, ∀ u, 0 < (z p u).im) →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => ldeRowLHS (hmat ω) (green (hmat ω) (z p v.1)) v.2.1 v.2.2)
      (fun p v ω => ldeRowRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) v.2.1 v.2.2) := by
  intro d P c₀ c₁ CU hc₀ hc₁ U _ z hU hz
  refine ldeDom_stochDom_of_tail (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2) _ _ _ _ _
    (CU + ((d : ℝ) / c₁ + (d : ℝ) / c₁)) (tendsto_sizeW_admFilterL c₀ c₁)
    (ldeDom_card_two d c₀ c₁ CU hc₁ U hU) ?_
  intro q
  obtain ⟨C, hC⟩ := ldeLinTail q
  refine ⟨C, ?_⟩
  filter_upwards [ldeDom_eventually_S P hc₀ hc₁, hz] with p hS hzp t ht v
  obtain ⟨u, x, y⟩ := v
  exact hC (Smat P.ψ p.1.1 p.1.2) hS.1 hS.2 x
    (fun ω k => greenMinor (green (hmat ω) (z p u)) x k.1 y)
    (fun k => ldeDom_measurable_greenMinor _ _ _)
    (fun k => ldeDom_freeOf_greenMinor _ (hzp u) _ _ _)
    ⟨|(z p u).im|⁻¹, fun ω k => ldeDom_norm_greenMinor_le (hzp u) ω _ _ _⟩ t ht

/-- The column sum, as `ldeRowDom`. -/
theorem ldeColDom :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ CU : ℝ), 0 < c₀ → 0 < c₁ →
  ∀ (U : SizeL → Type) [∀ p, Fintype (U p)] (z : ∀ p, U p → ℂ),
    (∀ᶠ p in admFilterL c₀ c₁, (Fintype.card (U p) : ℝ) ≤ sizeW p ^ CU) →
    (∀ᶠ p in admFilterL c₀ c₁, ∀ u, 0 < (z p u).im) →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P)
      (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2)
      (fun p v ω => ldeColLHS (hmat ω) (green (hmat ω) (z p v.1)) v.2.1 v.2.2)
      (fun p v ω => ldeColRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) v.2.1 v.2.2) := by
  intro d P c₀ c₁ CU hc₀ hc₁ U _ z hU hz
  refine ldeDom_stochDom_of_tail (U := fun p => U p × Zd d p.1.2 × Zd d p.1.2) _ _ _ _ _
    (CU + ((d : ℝ) / c₁ + (d : ℝ) / c₁)) (tendsto_sizeW_admFilterL c₀ c₁)
    (ldeDom_card_two d c₀ c₁ CU hc₁ U hU) ?_
  intro q
  obtain ⟨C, hC⟩ := ldeLinTail q
  refine ⟨C, ?_⟩
  filter_upwards [ldeDom_eventually_S P hc₀ hc₁, hz] with p hS hzp t ht v
  obtain ⟨u, x, y⟩ := v
  have key := hC (Smat P.ψ p.1.1 p.1.2) hS.1 hS.2 x
    (fun ω k => (starRingEnd ℂ) (greenMinor (green (hmat ω) (z p u)) x y k.1))
    (fun k => Complex.continuous_conj.measurable.comp (ldeDom_measurable_greenMinor _ _ _))
    (fun k ω η => congrArg (starRingEnd ℂ) (ldeDom_freeOf_greenMinor _ (hzp u) x y k.1 ω η))
    ⟨|(z p u).im|⁻¹, fun ω k => by
      rw [Complex.norm_conj]; exact ldeDom_norm_greenMinor_le (hzp u) ω _ _ _⟩ t ht
  simp only [ldeDom_colLHS_eq, ldeDom_colRHS_eq]
  exact key

/-- The quadratic form: `|Σ_{k,l≠x} h_{xk} G^{(x)}_{kl} h_{lx} − Σ_{k≠x} s_{xk} G^{(x)}_{kk}|² ≺
Σ_{k,l≠x} s_{xk} |G^{(x)}_{kl}|² s_{lx}` uniformly in `x` and `u`. -/
theorem ldeQuadDom :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ CU : ℝ), 0 < c₀ → 0 < c₁ →
  ∀ (U : SizeL → Type) [∀ p, Fintype (U p)] (z : ∀ p, U p → ℂ),
    (∀ᶠ p in admFilterL c₀ c₁, (Fintype.card (U p) : ℝ) ≤ sizeW p ^ CU) →
    (∀ᶠ p in admFilterL c₀ c₁, ∀ u, 0 < (z p u).im) →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => U p × Zd d p.1.2)
      (fun p v ω => ldeQuadLHS (hmat ω) (green (hmat ω) (z p v.1)) (Smat P.ψ p.1.1 p.1.2) v.2)
      (fun p v ω => ldeQuadRHS (Smat P.ψ p.1.1 p.1.2) (green (hmat ω) (z p v.1)) v.2) := by
  intro d P c₀ c₁ CU hc₀ hc₁ U _ z hU hz
  refine ldeDom_stochDom_of_tail (U := fun p => U p × Zd d p.1.2) _ _ _ _ _
    (CU + (d : ℝ) / c₁) (tendsto_sizeW_admFilterL c₀ c₁)
    (ldeDom_card_one d c₀ c₁ CU hc₁ U hU) ?_
  intro q
  obtain ⟨C, hC⟩ := ldeQuadTail q
  refine ⟨C, ?_⟩
  filter_upwards [ldeDom_eventually_S P hc₀ hc₁, hz] with p hS hzp t ht v
  obtain ⟨u, x⟩ := v
  exact hC (Smat P.ψ p.1.1 p.1.2) hS.1 hS.2 x
    (fun ω k l => greenMinor (green (hmat ω) (z p u)) x k.1 l.1)
    (fun k l => ldeDom_measurable_greenMinor _ _ _)
    (fun k l => ldeDom_freeOf_greenMinor _ (hzp u) _ _ _)
    ⟨|(z p u).im|⁻¹, fun ω k l => ldeDom_norm_greenMinor_le (hzp u) ω _ _ _⟩ t ht

/-- The diagonal entry: `|h_{xx}|² ≺ s_{xx}` uniformly in `x`. -/
theorem ldeDiagDom :
  ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ →
    StochDom (admFilterL c₀ c₁) sizeW (rbmLaw d P) (U := fun p => Zd d p.1.2)
      (fun _ x ω => ‖hmat ω x x‖ ^ 2) (fun p x _ => Smat P.ψ p.1.1 p.1.2 x x) := by
  intro d P c₀ c₁ hc₀ hc₁
  refine ldeDom_stochDom_of_tail (Ω := fun p => Sample (Zd d p.1.2)) (U := fun p => Zd d p.1.2)
    (admFilterL c₀ c₁) sizeW (rbmLaw d P) _ _ ((d : ℝ) / c₁)
    (tendsto_sizeW_admFilterL c₀ c₁) ?_ ?_
  · filter_upwards [ldeDom_eventually_adm c₀ c₁] with p hp
    exact card_Zd_le_adm d c₀ c₁ hc₁ p hp
  · intro q
    obtain ⟨C, hC⟩ := ldeDiagTail q
    refine ⟨C, ?_⟩
    filter_upwards [ldeDom_eventually_nonneg P c₀ c₁] with p hS t ht x
    exact hC (Smat P.ψ p.1.1 p.1.2) hS x t ht

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

section Instances

end Instances

end RBM8D
