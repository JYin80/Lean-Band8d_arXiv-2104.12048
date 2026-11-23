module

public import RBM8D.LocalLaw.Cutoff.Defs

@[expose] public section

/-!
# The local law from the cutoff moment bound

`localLawTExp_cutoff_of`: the improvement on the cutoff event (`cutImproveStmt`) and the moment
bound for the cutoff variables `Z_{ab} = C(H) X_{ab}` (`cutMomentStmt`) give the local law
[II, Theorem 3.6] in the form `localLawTExpStmt'`: `|G_{xy}(z) − m(z) δ_{xy}|² ≺ B_{xy}` uniformly
in `z ∈ 𝐃(κ, ε)` and `x, y`.

The proof is a bootstrap in `η = Im z` on a grid of spacing `h = (10 (2L)^{d+6})⁻¹`:

* at the top edge `η = 1` the local law [II, Lemma 7.2] gives `Y ≤ W^β` and, with the
  convolution bounds `S ≤ W^ρ B` and `S B ≤ W^ρ B`, `max_{ab} X_{ab} ≤ W^{α/2}`;
* at a grid point with `Y ≤ W^β` and `max_{ab} X_{ab} ≤ W^{α/2}` the soft maximum satisfies
  `M ≤ (L^d)^{2/l} (1 + W^{α/2}) ≤ W^α`, so `C(H) = 1` and `Z = X`; outside an event of small
  probability (Markov's inequality on `E Z^q`, and the improvement event) this gives
  `max_{ab} X_{ab} < W^{α/4}` and `Y ≤ W^{α/2 + γ}`;
* `Y` and `X_{ab}` change by at most `1` between points at distance `2h` in `𝐃(κ, ε)`, so the two
  bounds pass to the next grid point below and to every point of `𝐃(κ, ε)`.

The exponents are `β = min(β₀, τ/2, d/200)`, `α = β/10`, `γ = β/4`, `ν = α/64`,
`l ≥ 64d/(c₁α)` and `q` large in terms of `D`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D

/-! ## Lipschitz bounds in the spectral parameter -/

section Lip

/-- `|G_{ij}(z) − G_{ij}(w)| ≤ |z − w| / (Im z · Im w)`. -/
private theorem Bootstrap_green_lip {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (i j : ι) :
    ‖green H z i j - green H w i j‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) (green_sub_green hH hz.ne' hw.ne')
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
  rw [h, norm_mul]
  have hrow := sum_norm_sq_green_row hH hz i
  have hcol := sum_norm_sq_green_col hH hw j
  have hgi : (green H z i i).im ≤ (z.im)⁻¹ := by
    have := norm_green_entry_le hH hz.ne' i i
    rw [abs_of_pos hz] at this
    exact (Complex.im_le_norm _).trans this
  have hgj : (green H w j j).im ≤ (w.im)⁻¹ := by
    have := norm_green_entry_le hH hw.ne' j j
    rw [abs_of_pos hw] at this
    exact (Complex.im_le_norm _).trans this
  have hA : ∑ k, ‖green H z i k‖ ^ 2 ≤ (z.im)⁻¹ ^ 2 := by
    rw [hrow, div_eq_mul_inv, sq]
    exact mul_le_mul_of_nonneg_right hgi (inv_nonneg.2 hz.le)
  have hB : ∑ k, ‖green H w k j‖ ^ 2 ≤ (w.im)⁻¹ ^ 2 := by
    rw [hcol, div_eq_mul_inv, sq]
    exact mul_le_mul_of_nonneg_right hgj (inv_nonneg.2 hw.le)
  have hsum : ‖∑ k, green H z i k * green H w k j‖ ≤ (z.im)⁻¹ * (w.im)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul]
    refine le_of_sq_le_sq ?_ (by positivity)
    calc (∑ k, ‖green H z i k‖ * ‖green H w k j‖) ^ 2
        ≤ (∑ k, ‖green H z i k‖ ^ 2) * ∑ k, ‖green H w k j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (z.im)⁻¹ ^ 2 * (w.im)⁻¹ ^ 2 :=
          mul_le_mul hA hB (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
      _ = ((z.im)⁻¹ * (w.im)⁻¹) ^ 2 := by ring
  calc ‖z - w‖ * ‖∑ k, green H z i k * green H w k j‖
      ≤ ‖z - w‖ * ((z.im)⁻¹ * (w.im)⁻¹) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ‖z - w‖ / (z.im * w.im) := by field_simp

/-- `1 − |m(z)| ≥ Im z / 4` for `0 < Im z ≤ 1`. -/
private theorem Bootstrap_one_sub_norm_msc {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im / 4 ≤ 1 - ‖msc z‖ := by
  have him := msc_im_pos hz
  have hlt := norm_msc_lt_one hz
  have hm0 : msc z ≠ 0 := msc_ne_zero z
  have hinv : msc z + z = -(msc z)⁻¹ := msc_add_eq_neg_inv z
  have hN : 0 < Complex.normSq (msc z) := Complex.normSq_pos.mpr hm0
  have key : ((msc z).im + z.im) * Complex.normSq (msc z) = (msc z).im := by
    have := congrArg Complex.im hinv
    simp only [Complex.add_im, Complex.neg_im, Complex.inv_im, neg_div, neg_neg] at this
    rw [this]
    field_simp
  rw [Complex.normSq_eq_norm_sq] at key
  have hle : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have hn0 := norm_nonneg (msc z)
  nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (sub_nonneg.2 hlt.le)]

/-- `|m(z) − m(w)| ≤ 4 |z − w| / Im z` for `0 < Im z ≤ 1` and `Im w > 0`. -/
private theorem Bootstrap_msc_lip {z w : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hw : 0 < w.im) :
    ‖msc z - msc w‖ ≤ 4 * ‖z - w‖ / z.im := by
  have hm := msc_mul z
  have hm' := msc_mul w
  have key : (msc z - msc w) * (1 - msc z * msc w) = (z - w) * (msc z * msc w) := by
    linear_combination (-msc w) * hm + msc z * hm'
  have h1 := Bootstrap_one_sub_norm_msc hz hz1
  have hl := norm_msc_lt_one hz
  have hl' := norm_msc_lt_one hw
  have hn0 := norm_nonneg (msc z)
  have hn0' := norm_nonneg (msc w)
  have hlow : z.im / 4 ≤ ‖1 - msc z * msc w‖ := by
    have : 1 - ‖msc z * msc w‖ ≤ ‖1 - msc z * msc w‖ := by
      have := norm_sub_norm_le (1 : ℂ) (msc z * msc w)
      simpa using this
    rw [norm_mul] at this
    nlinarith
  have hn := congrArg norm key
  rw [norm_mul, norm_mul, norm_mul] at hn
  have hprod : ‖msc z‖ * ‖msc w‖ ≤ 1 := by nlinarith
  have hzw := norm_nonneg (z - w)
  have hle : ‖msc z - msc w‖ * (z.im / 4) ≤ ‖z - w‖ := by
    calc ‖msc z - msc w‖ * (z.im / 4) ≤ ‖msc z - msc w‖ * ‖1 - msc z * msc w‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖z - w‖ * (‖msc z‖ * ‖msc w‖) := hn
      _ ≤ ‖z - w‖ * 1 := mul_le_mul_of_nonneg_left hprod hzw
      _ = ‖z - w‖ := mul_one _
  rw [le_div_iff₀ hz]
  nlinarith

end Lip

/-! ## The variables `X`, `Y`, `M`, `C` of the cutoff -/

section Vars

variable {d L : ℕ} [NeZero L]

/-- Each normalized entry is at most `Y`. -/
private theorem Bootstrap_le_cutY (W : ℕ) (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) (i j : Zd d L) :
    ‖entryErr G m i j‖ / Real.sqrt (bB d L W i j) ≤ cutY W G m := by
  unfold cutY
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i)
  exact le_ciSup (f := fun j => ‖entryErr G m i j‖ / Real.sqrt (bB d L W i j))
    (Set.finite_range _).bddAbove j

omit [NeZero L] in
/-- `Y ≤ t` when every normalized entry is at most `t`. -/
private theorem Bootstrap_cutY_le {W : ℕ} {G : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} {t : ℝ}
    (h : ∀ i j, ‖entryErr G m i j‖ / Real.sqrt (bB d L W i j) ≤ t) : cutY W G m ≤ t :=
  ciSup_le fun i => ciSup_le fun j => h i j

/-- `|G_{ij} − m δ_{ij}|² ≤ Y² B_{ij}`. -/
private theorem Bootstrap_entry_le_cutY {W : ℕ} (hW : 1 ≤ W) (G : Matrix (Zd d L) (Zd d L) ℂ)
    (m : ℂ) (i j : Zd d L) :
    ‖entryErr G m i j‖ ^ 2 ≤ cutY W G m ^ 2 * bB d L W i j := by
  have hB := bB_pos₁ (d := d) (L := L) hW i j
  have hs : 0 < Real.sqrt (bB d L W i j) := Real.sqrt_pos.2 hB
  have h1 := Bootstrap_le_cutY W G m i j
  rw [div_le_iff₀ hs] at h1
  have h0 : 0 ≤ cutY W G m := le_trans (by positivity) (Bootstrap_le_cutY W G m i j)
  calc ‖entryErr G m i j‖ ^ 2 ≤ (cutY W G m * Real.sqrt (bB d L W i j)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = cutY W G m ^ 2 * bB d L W i j := by rw [mul_pow, Real.sq_sqrt hB.le]

/-- `0 ≤ X_{ab}` for `S ≥ 0`. -/
private theorem Bootstrap_cutX_nonneg {W : ℕ} (hW : 1 ≤ W) {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS0 : ∀ i j, 0 ≤ S i j) (G : Matrix (Zd d L) (Zd d L) ℂ) (a b : Zd d L) :
    0 ≤ cutX W S G a b := by
  unfold cutX cutD
  have hB := bB_pos₁ (d := d) (L := L) hW a b
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) hB.le
  have := hS0 a i
  have := hS0 j b
  positivity

/-- For a doubly stochastic `S ≥ 0`, if `|G'_{ij}|² ≤ |G_{ij}|² + δ` for all `i, j`, then
`X_{ab}(G') ≤ X_{ab}(G) + δ / B_{ab}`. -/
private theorem Bootstrap_cutX_lip {W : ℕ} (hW : 1 ≤ W) {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS0 : ∀ i j, 0 ≤ S i j) (hS1 : ∀ i, ∑ j, S i j = 1) (hS2 : ∀ j, ∑ i, S i j = 1)
    {G G' : Matrix (Zd d L) (Zd d L) ℂ} {δ : ℝ} (hδ : ∀ i j, ‖G' i j‖ ^ 2 ≤ ‖G i j‖ ^ 2 + δ)
    (a b : Zd d L) :
    cutX W S G' a b ≤ cutX W S G a b + δ / bB d L W a b := by
  unfold cutX cutD
  have hB := bB_pos₁ (d := d) (L := L) hW a b
  rw [← add_div, div_le_div_iff_of_pos_right hB]
  have hsum : ∑ i, ∑ j, S a i * δ * S j b = δ := by
    calc ∑ i, ∑ j, S a i * δ * S j b = ∑ i, S a i * δ * ∑ j, S j b := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = δ := by
          simp_rw [hS2 b, mul_one]
          rw [← Finset.sum_mul, hS1 a, one_mul]
  calc ∑ i, ∑ j, S a i * ‖G' i j‖ ^ 2 * S j b
      ≤ ∑ i, ∑ j, (S a i * ‖G i j‖ ^ 2 * S j b + S a i * δ * S j b) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h1 := hS0 a i
        have h2 := hS0 j b
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hδ i j) h1) h2
        linarith [this]
    _ = ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b + ∑ i, ∑ j, S a i * δ * S j b := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b + δ := by rw [hsum]

/-- The bound at the top edge: for `S ≥ 0` symmetric with `S ≤ c B` and `S B ≤ c' B` entrywise,
`|m| ≤ 1` and `|G_{ij} − m δ_{ij}|² ≤ t B_{ij}`, `X_{ab} ≤ 2 c c' + 2 t c'²`. -/
private theorem Bootstrap_cutX_top {W : ℕ} (hW : 1 ≤ W) {S : Matrix (Zd d L) (Zd d L) ℝ}
    (hS0 : ∀ i j, 0 ≤ S i j) (hSs : ∀ i j, S i j = S j i) {c c' t : ℝ} (hc' : 0 ≤ c')
    (ht : 0 ≤ t) (hSB : ∀ i j, S i j ≤ c * bB d L W i j)
    (hconv : ∀ i j, ∑ k, S i k * bB d L W k j ≤ c' * bB d L W i j)
    {G : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} (hm : ‖m‖ ≤ 1)
    (he : ∀ i j, ‖entryErr G m i j‖ ^ 2 ≤ t * bB d L W i j) (a b : Zd d L) :
    cutX W S G a b ≤ 2 * c * c' + 2 * t * c' ^ 2 := by
  have hB := bB_pos₁ (d := d) (L := L) hW a b
  have hG : ∀ i j, ‖G i j‖ ^ 2 ≤ 2 * t * bB d L W i j + 2 * (if i = j then 1 else 0) := by
    intro i j
    have e : G i j = entryErr G m i j + (if i = j then m else 0) := by
      unfold entryErr; ring
    have h1 : ‖G i j‖ ≤ ‖entryErr G m i j‖ + ‖(if i = j then m else 0 : ℂ)‖ := by
      rw [e]; exact norm_add_le _ _
    have h2 : ‖(if i = j then m else 0 : ℂ)‖ ^ 2 ≤ (if i = j then 1 else 0) := by
      split_ifs
      · have := norm_nonneg m
        nlinarith
      · simp
    have h3 := he i j
    have h4 : ‖G i j‖ ^ 2 ≤ 2 * ‖entryErr G m i j‖ ^ 2 +
        2 * ‖(if i = j then m else 0 : ℂ)‖ ^ 2 := by
      have := norm_nonneg (G i j)
      nlinarith [sq_nonneg (‖entryErr G m i j‖ - ‖(if i = j then m else 0 : ℂ)‖)]
    linarith
  have hrow : ∀ i, ∑ j, bB d L W i j * S j b ≤ c' * bB d L W i b := by
    intro i
    have := hconv b i
    calc ∑ j, bB d L W i j * S j b = ∑ j, S b j * bB d L W j i := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [bB_comm' i j, hSs j b]; ring
      _ ≤ c' * bB d L W b i := this
      _ = c' * bB d L W i b := by rw [bB_comm' b i]
  have hD : cutD S G a b ≤ (2 * c * c' + 2 * t * c' ^ 2) * bB d L W a b := by
    unfold cutD
    calc ∑ i, ∑ j, S a i * ‖G i j‖ ^ 2 * S j b
        ≤ ∑ i, ∑ j, S a i * (2 * t * bB d L W i j + 2 * (if i = j then 1 else 0)) * S j b := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hG i j) (hS0 a i))
            (hS0 j b)
      _ = ∑ i, S a i * (2 * t * ∑ j, bB d L W i j * S j b + 2 * S i b) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hδ : ∑ j, (if i = j then (1 : ℝ) else 0) * S j b = S i b := by
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          calc ∑ j, S a i * (2 * t * bB d L W i j + 2 * (if i = j then 1 else 0)) * S j b
              = ∑ j, (S a i * (2 * t) * (bB d L W i j * S j b) +
                  S a i * 2 * ((if i = j then (1 : ℝ) else 0) * S j b)) :=
                Finset.sum_congr rfl fun j _ => by ring
            _ = S a i * (2 * t) * ∑ j, bB d L W i j * S j b +
                  S a i * 2 * ∑ j, (if i = j then (1 : ℝ) else 0) * S j b := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            _ = S a i * (2 * t * ∑ j, bB d L W i j * S j b + 2 * S i b) := by
                rw [hδ]; ring
      _ ≤ ∑ i, S a i * (2 * t * (c' * bB d L W i b) + 2 * (c * bB d L W i b)) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hS0 a i)
          have := hrow i
          have := hSB i b
          nlinarith
      _ = (2 * t * c' + 2 * c) * ∑ i, S a i * bB d L W i b := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (2 * t * c' + 2 * c) * (c' * bB d L W a b) := by
          refine mul_le_mul_of_nonneg_left (hconv a b) ?_
          have h0 : 0 ≤ c := by
            have := hSB a a
            have h1 := hS0 a a
            have h2 := bB_pos₁ (d := d) (L := L) hW a a
            by_contra hneg
            have hneg' := not_le.mp hneg
            nlinarith
          positivity
      _ = (2 * c * c' + 2 * t * c' ^ 2) * bB d L W a b := by ring
  unfold cutX
  rw [div_le_iff₀ hB]
  exact hD

/-- The soft maximum: if `0 ≤ X_{ab} ≤ x` for all `a, b`, then `M ≤ (L^d)^{2/l} (1 + x)`. -/
private theorem Bootstrap_cutM_le {l W : ℕ} (hl : 1 ≤ l) {S : Matrix (Zd d L) (Zd d L) ℝ}
    {G : Matrix (Zd d L) (Zd d L) ℂ} {x : ℝ}
    (hX : ∀ a b, 0 ≤ cutX W S G a b ∧ cutX W S G a b ≤ x) :
    cutM l W S G ≤ ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) * (1 + x) := by
  have hx : 0 ≤ x := by
    obtain ⟨a⟩ := (inferInstance : Nonempty (Zd d L))
    exact (hX a a).1.trans (hX a a).2
  have hl0 : (l : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ l := by exact_mod_cast hl
                               linarith
  have hsum : ∑ a : Zd d L, ∑ b : Zd d L, (1 + cutX W S G a b) ^ l ≤
      (((L : ℝ) ^ d) ^ 2) * (1 + x) ^ l := by
    calc ∑ a : Zd d L, ∑ b : Zd d L, (1 + cutX W S G a b) ^ l
        ≤ ∑ _a : Zd d L, ∑ _b : Zd d L, (1 + x) ^ l := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          exact pow_le_pow_left₀ (by linarith [(hX a b).1]) (by linarith [(hX a b).2]) l
      _ = (((L : ℝ) ^ d) ^ 2) * (1 + x) ^ l := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast; ring
  have h0 : 0 ≤ ∑ a : Zd d L, ∑ b : Zd d L, (1 + cutX W S G a b) ^ l :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      pow_nonneg (by linarith [(hX a b).1]) l
  unfold cutM
  calc (∑ a : Zd d L, ∑ b : Zd d L, (1 + cutX W S G a b) ^ l) ^ ((1 : ℝ) / l)
      ≤ ((((L : ℝ) ^ d) ^ 2) * (1 + x) ^ l) ^ ((1 : ℝ) / l) :=
        Real.rpow_le_rpow h0 hsum (by positivity)
    _ = ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) * (1 + x) := by
        rw [Real.mul_rpow (by positivity) (by positivity), one_div,
          Real.pow_rpow_inv_natCast (by linarith) (by omega), ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        congr 2

/-- `C(H) = 1`, hence `Z_{ab} = X_{ab}`, when `Y ≤ W^β` and `M ≤ W^α`. -/
private theorem Bootstrap_cutZ_eq {β α : ℝ} {l W : ℕ} {S : Matrix (Zd d L) (Zd d L) ℝ}
    {G : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ} (hW : 1 ≤ W) (hY : cutY W G m ≤ (W : ℝ) ^ β)
    (hM : cutM l W S G ≤ (W : ℝ) ^ α) (a b : Zd d L) :
    cutZ β α l W S G m a b = cutX W S G a b := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWα : 0 < (W : ℝ) ^ α := Real.rpow_pos_of_pos hW0 α
  have h1 : cutM l W S G / (W : ℝ) ^ α ≤ 1 := by rwa [div_le_one hWα]
  unfold cutZ cutC
  simp only [hY, ↓reduceIte]
  have : cutPhi (cutM l W S G / (W : ℝ) ^ α) = 1 := by
    unfold cutPhi
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  rw [this, one_mul]

/-- `0 ≤ C(H) ≤ 1`. -/
private theorem Bootstrap_cutC_mem (β α : ℝ) (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (G : Matrix (Zd d L) (Zd d L) ℂ) (m : ℂ) :
    0 ≤ cutC β α l W S G m ∧ cutC β α l W S G m ≤ 1 := by
  unfold cutC cutPhi
  split_ifs
  · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · exact ⟨le_rfl, zero_le_one⟩

end Vars

/-! ## Sizes on the window and on the spectral domain -/

section Sizes

/-- On `adm(c₀, c₁)` with `0 < c₀ < 1`, `c₁ > 0`: `W ≤ L`, `L ≤ W^{1/c₁}` and
`W^{1 + c₀/(1 − c₀)} ≤ L`. -/
private theorem Bootstrap_adm_facts {W L : ℕ} (hL : 1 ≤ L) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₀1 : c₀ < 1) (hc₁ : 0 < c₁) (hadm : (W, L) ∈ adm c₀ c₁) :
    (W : ℝ) ≤ L ∧ (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) ∧ (W : ℝ) ^ (1 + c₀ / (1 - c₀)) ≤ L := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (L : ℝ) ^ (1 - c₀) ≤ (L : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    rw [Real.rpow_one] at h2
    exact hadm.2.trans h2
  · have h1 := Real.rpow_le_rpow (by positivity) hadm.1 (by positivity : (0 : ℝ) ≤ 1 / c₁)
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hc₁.ne', Real.rpow_one] at h1
  · have h1 := Real.rpow_le_rpow (by positivity) hadm.2
      (by have : 0 < 1 - c₀ := by linarith
          positivity : (0 : ℝ) ≤ 1 / (1 - c₀))
    rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by linarith), Real.rpow_one] at h1
    have e : 1 + c₀ / (1 - c₀) = 1 / (1 - c₀) := by
      field_simp [show (1 : ℝ) - c₀ ≠ 0 by linarith]; ring
    rwa [e]

variable {d L : ℕ} [NeZero L]

/-- `B_{xy} ≥ (2L)^{−d}` for `1 ≤ W ≤ L` and `d ≥ 2`. -/
private theorem Bootstrap_bB_lower (hd : 2 ≤ d) {W : ℕ} (hW : 1 ≤ W) (hWL : (W : ℝ) ≤ L)
    (x y : Zd d L) : 1 / (2 * (L : ℝ)) ^ d ≤ bB d L W x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL2 : (W : ℝ) ≤ 2 * L := by linarith
  have hr : (zdistInf d L (x - y) : ℝ) ≤ L := by
    have h := zdistInf_le_half d L (x - y)
    have : zdistInf d L (x - y) ≤ L := h.trans (Nat.div_le_self _ _)
    exact_mod_cast this
  have hρ0 : 0 < (zdistInf d L (x - y) : ℝ) + W := by positivity
  have hρ : (zdistInf d L (x - y) : ℝ) + W ≤ 2 * L := by linarith
  have hd' : (2 : ℝ) - d ≤ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : (2 * (L : ℝ)) ^ ((2 : ℝ) - d) ≤ ((zdistInf d L (x - y) : ℝ) + W) ^ ((2 : ℝ) - d) :=
    Real.rpow_le_rpow_of_nonpos hρ0 hρ hd'
  have h2 : (2 * (L : ℝ)) ^ (-2 : ℝ) ≤ (W : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hW0 hL2 (by norm_num)
  have hΛ : 0 < 2 * (L : ℝ) := by linarith
  have e : 1 / (2 * (L : ℝ)) ^ d = (2 * (L : ℝ)) ^ (-2 : ℝ) * (2 * (L : ℝ)) ^ ((2 : ℝ) - d) := by
    rw [← Real.rpow_add hΛ, show (-2 : ℝ) + (2 - d) = -(d : ℝ) by ring, Real.rpow_neg hΛ.le,
      Real.rpow_natCast, one_div]
  rw [e]
  unfold bB
  exact mul_le_mul h2 h1 (by positivity) (by positivity)

omit [NeZero L] in
/-- `B_{xy} ≤ 1` for `W ≥ 1`, `d ≥ 2`. -/
private theorem Bootstrap_bB_le_one (hd : 2 ≤ d) {W : ℕ} (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ≤ 1 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  refine (bB_le_rpow hd hW x y).trans ?_
  exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
                                                     linarith)

/-- `Im z ≥ 1/L²` on `𝐃(κ, ε)` for `W ≥ 1` and `ε > 0`. -/
private theorem Bootstrap_im_lower {κ ε : ℝ} (hε : 0 < ε) {W : ℕ} (hW : 1 ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) : 1 / (L : ℝ) ^ 2 ≤ z.im := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  rw [Real.rpow_two] at h1
  have h0 : 0 < (L : ℝ) ^ (2 - ε) := by positivity
  calc 1 / (L : ℝ) ^ 2 ≤ 1 / (L : ℝ) ^ (2 - ε) := one_div_le_one_div_of_le h0 h1
    _ ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by
        refine div_le_div_of_nonneg_right ?_ h0.le
        nlinarith
    _ ≤ z.im := hz.2.1

/-- `B_{αy} ≤ B_{xy} (1 + |x − α|_L/W)^{d−2}`, from `|x − y|_L ≤ |x − α|_L + |α − y|_L`. -/
private theorem Bootstrap_bB_shift (hd : 2 ≤ d) {W : ℕ} (hW : (1 : ℝ) ≤ W) (x α y : Zd d L) :
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
  have hc1 : 1 ≤ c := by
    rw [hc]
    have : 0 ≤ r₁ / W := by positivity
    linarith
  have hab : r + W ≤ (r₂ + W) * c := by
    have e : (r₂ + W) * c = r₂ + W + r₁ * ((r₂ + W) / W) := by rw [hc]; field_simp
    have h1 : 1 ≤ (r₂ + W) / W := by rw [le_div_iff₀ hW0]; linarith
    have h2 : r₁ ≤ r₁ * ((r₂ + W) / W) := le_mul_of_one_le_right hr₁0 h1
    rw [e]
    linarith
  have hapos : 0 < r + W := by
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    linarith
  have he : (2 : ℝ) - d ≤ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
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
    calc (r₂ + W) ^ ((2 : ℝ) - d)
        = (r₂ + W) ^ ((2 : ℝ) - d) * c ^ ((2 : ℝ) - d) * c ^ (d - 2) := by
          rw [mul_assoc, hcc, mul_one]
      _ ≤ (r + W) ^ ((2 : ℝ) - d) * c ^ (d - 2) := mul_le_mul_of_nonneg_right h1 hcpos.le
  unfold bB
  rw [← hr₂, ← hr, mul_assoc]
  exact mul_le_mul_of_nonneg_left key (by positivity)

end Sizes

/-! ## The convolution bounds `S ≤ W^ρ B` and `S B ≤ W^ρ B` -/

section Conv

private theorem Bootstrap_ev_adm (c₀ c₁ : ℝ) : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁ := by
  have h : ∀ᶠ q in admFilter c₀ c₁, q ∈ adm c₀ c₁ :=
    inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _)
  exact tendsto_comap.eventually h

/-- [I, (1.8)–(1.9)] with a loss `W^ρ`: eventually along `adm(c₀, c₁)`, `S` is doubly stochastic,
symmetric and nonnegative, `S_{xy} ≤ W^ρ B_{xy}` and `Σ_k S_{xk} B_{ky} ≤ W^ρ B_{xy}`. -/
private theorem Bootstrap_conv {d : ℕ} (hd : 2 ≤ d) (P : Profile d) {c₀ c₁ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ p in admFilterL c₀ c₁,
      (∀ x y, 0 ≤ Smat P.ψ p.1.1 p.1.2 x y) ∧
      (∀ x y, Smat P.ψ p.1.1 p.1.2 x y = Smat P.ψ p.1.1 p.1.2 y x) ∧
      (∀ x, ∑ y, Smat P.ψ p.1.1 p.1.2 x y = 1) ∧ (∀ y, ∑ x, Smat P.ψ p.1.1 p.1.2 x y = 1) ∧
      (∀ x y, Smat P.ψ p.1.1 p.1.2 x y ≤ (p.1.1 : ℝ) ^ ρ * bB d p.1.2 p.1.1 x y) ∧
      ∀ x y, ∑ k, Smat P.ψ p.1.1 p.1.2 x k * bB d p.1.2 p.1.1 k y ≤
        (p.1.1 : ℝ) ^ ρ * bB d p.1.2 p.1.1 x y := by
  have hc₀1 : c₀ < 1 := by linarith
  have hd0 : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  set εb : ℝ := c₀ / (1 - c₀) with hεb
  have hεb0 : 0 < εb := div_pos hc₀ (by linarith)
  set τb : ℝ := ρ / (2 * d) with hτb
  have hτb0 : 0 < τb := by positivity
  set Db : ℝ := 2 * d / c₁ + d with hDb
  have hDb0 : 0 < Db := by positivity
  obtain ⟨K, W₁, hK1, hwave⟩ := wave_bound d hd P c₀ c₁ 1 hc₀ hc₁ one_pos (ρ / 2) (by positivity)
  obtain ⟨W₂, hband⟩ := banded d P εb τb Db hεb0 hτb0 hDb0
  obtain ⟨W₃, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  obtain ⟨W₄, hsym⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hρ2 : Tendsto (fun p : SizeL => sizeW p ^ (ρ / 2)) (admFilterL c₀ c₁) atTop :=
    (tendsto_rpow_atTop (by positivity)).comp hsz
  filter_upwards [Bootstrap_ev_adm c₀ c₁,
    hsz.eventually (eventually_ge_atTop (max (max W₁ W₂) (max (max W₃ W₄) 2))),
    hρ2.eventually (eventually_ge_atTop K), hρ2.eventually (eventually_ge_atTop (2 ^ d + 1))]
    with p hadm hWbig hKW h2W
  set W : ℕ := p.1.1 with hWdef
  set L : ℕ := p.1.2 with hLdef
  change K ≤ (W : ℝ) ^ (ρ / 2) at hKW
  change (2 : ℝ) ^ d + 1 ≤ (W : ℝ) ^ (ρ / 2) at h2W
  change max (max W₁ W₂) (max (max W₃ W₄) 2) ≤ (W : ℝ) at hWbig
  simp only [max_le_iff] at hWbig
  obtain ⟨⟨hWW₁, hWW₂⟩, ⟨hWW₃, hWW₄⟩, hW2⟩ := hWbig
  have hW1n : 1 ≤ W := by
    have : (1 : ℝ) ≤ W := by linarith
    exact_mod_cast this
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨hWL, hLW, hWLε⟩ := Bootstrap_adm_facts hL1 hc₀ hc₀1 hc₁ hadm
  have hDS := hds W L hadm hWW₃
  rw [mem_doublyStochastic_iff_sum] at hDS
  obtain ⟨hS0, hS1, hS2⟩ := hDS
  have hSY := (hsym W L hadm hWW₄).1
  have hSs : ∀ x y, Smat P.ψ W L x y = Smat P.ψ W L y x := fun x y => (hSY.apply y x)
  refine ⟨hS0, hSs, hS1, hS2, ?_, ?_⟩
  · -- `S ≤ W^ρ B` from the waved-edge bound
    intro x y
    have hw := (hwave W L hadm hWW₁ hW1n I (by simp) (by simp) x y).1
    have hn : ‖cmat (Smat P.ψ W L) x y‖ = |Smat P.ψ W L x y| := by
      simp [cmat, Matrix.map_apply]
    rw [hn] at hw
    have hB := bB_pos₁ (d := d) (L := L) hW1n x y
    have hs := rpow_mul_sqrt_bB_le hd hW1n x y (L := L)
    have hs0 : 0 ≤ (W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y) := by positivity
    calc Smat P.ψ W L x y ≤ |Smat P.ψ W L x y| := le_abs_self _
      _ ≤ K * (W : ℝ) ^ (ρ / 2) * (bB d L W x y *
            ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y))) := hw
      _ ≤ (W : ℝ) ^ (ρ / 2) * (W : ℝ) ^ (ρ / 2) * (bB d L W x y * 1) := by
          gcongr
      _ = (W : ℝ) ^ ρ * bB d L W x y := by
          rw [← Real.rpow_add hW0]; ring_nf
  · -- `S B ≤ W^ρ B`: the near part by the shift of `B`, the far part by the band structure
    intro x y
    have hB := bB_pos₁ (d := d) (L := L) hW1n x y
    set F : ℝ := (1 + (W : ℝ) ^ τb) ^ (d - 2) with hF
    have hF0 : 0 ≤ F := by positivity
    have hpt : ∀ k, Smat P.ψ W L x k * bB d L W k y ≤
        Smat P.ψ W L x k * (bB d L W x y * F) + (W : ℝ) ^ (-Db) := by
      intro k
      have hS := hS0 x k
      have hBk := bB_pos₁ (d := d) (L := L) hW1n k y
      have hWD : 0 ≤ (W : ℝ) ^ (-Db) := by positivity
      by_cases hnear : (zdistInf d L (x - k) : ℝ) < (W : ℝ) ^ (1 + τb)
      · have hsh := Bootstrap_bB_shift hd hW1 x k y (L := L)
        have hq : (zdistInf d L (x - k) : ℝ) / W ≤ (W : ℝ) ^ τb := by
          rw [div_le_iff₀ hW0, ← Real.rpow_add_one hW0.ne', add_comm]
          exact hnear.le
        have hpow : (1 + (zdistInf d L (x - k) : ℝ) / W) ^ (d - 2) ≤ F :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have : bB d L W k y ≤ bB d L W x y * F :=
          hsh.trans (mul_le_mul_of_nonneg_left hpow hB.le)
        nlinarith [mul_le_mul_of_nonneg_left this hS]
      · have hfar := hband W L hWW₂ hWLε x k (not_lt.mp hnear)
        have h1 : Smat P.ψ W L x k * bB d L W k y ≤ Smat P.ψ W L x k :=
          mul_le_of_le_one_right hS (Bootstrap_bB_le_one hd hW1n k y)
        have h2 : Smat P.ψ W L x k ≤ (W : ℝ) ^ (-Db) := (le_abs_self _).trans hfar
        have h3 : 0 ≤ Smat P.ψ W L x k * (bB d L W x y * F) := by positivity
        linarith
    have hsum : ∑ k, Smat P.ψ W L x k * bB d L W k y ≤
        bB d L W x y * F + (L : ℝ) ^ d * (W : ℝ) ^ (-Db) := by
      calc ∑ k, Smat P.ψ W L x k * bB d L W k y
          ≤ ∑ k, (Smat P.ψ W L x k * (bB d L W x y * F) + (W : ℝ) ^ (-Db)) :=
            Finset.sum_le_sum fun k _ => hpt k
        _ = bB d L W x y * F + (L : ℝ) ^ d * (W : ℝ) ^ (-Db) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hS1 x, one_mul]
            simp [Finset.sum_const, Finset.card_univ]
    -- the far part is at most `B_{xy}`
    have hfar : (L : ℝ) ^ d * (W : ℝ) ^ (-Db) ≤ bB d L W x y := by
      refine le_trans ?_ (Bootstrap_bB_lower hd hW1n hWL x y)
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
      have hLd : (L : ℝ) ^ d ≤ (W : ℝ) ^ ((d : ℝ) / c₁) := by
        calc (L : ℝ) ^ d ≤ ((W : ℝ) ^ (1 / c₁)) ^ d := pow_le_pow_left₀ hL0.le hLW d
          _ = (W : ℝ) ^ ((d : ℝ) / c₁) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
      have h2d : (2 : ℝ) ^ d ≤ (W : ℝ) ^ (d : ℝ) := by
        rw [Real.rpow_natCast]; exact pow_le_pow_left₀ (by norm_num) hW2 d
      have hkey : (2 * (L : ℝ)) ^ d * ((L : ℝ) ^ d * (W : ℝ) ^ (-Db)) ≤ 1 := by
        have e : (2 * (L : ℝ)) ^ d * ((L : ℝ) ^ d * (W : ℝ) ^ (-Db)) =
            (2 : ℝ) ^ d * (L : ℝ) ^ d * (L : ℝ) ^ d * (W : ℝ) ^ (-Db) := by ring
        have e2 : (W : ℝ) ^ (d : ℝ) * (W : ℝ) ^ ((d : ℝ) / c₁) * (W : ℝ) ^ ((d : ℝ) / c₁) *
            (W : ℝ) ^ (-Db) = 1 := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0, hDb]
          rw [show (d : ℝ) + d / c₁ + d / c₁ + -(2 * d / c₁ + d) = 0 by ring, Real.rpow_zero]
        rw [e, ← e2]
        have hWD : 0 ≤ (W : ℝ) ^ (-Db) := by positivity
        gcongr
      have hΛ : 0 < (2 * (L : ℝ)) ^ d := by positivity
      rw [le_div_iff₀ hΛ, mul_comm]
      exact hkey
    -- the near part: `F ≤ 2^d W^{ρ/2}`
    have hFle : F ≤ (2 : ℝ) ^ d * (W : ℝ) ^ (ρ / 2) := by
      have hWt : (1 : ℝ) ≤ (W : ℝ) ^ τb := Real.one_le_rpow hW1 hτb0.le
      calc F ≤ (2 * (W : ℝ) ^ τb) ^ (d - 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ (2 * (W : ℝ) ^ τb) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
        _ = (2 : ℝ) ^ d * (W : ℝ) ^ (ρ / 2) := by
            rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ τb), ← Real.rpow_mul hW0.le, hτb]
            congr 2
            field_simp
    calc ∑ k, Smat P.ψ W L x k * bB d L W k y
        ≤ bB d L W x y * F + (L : ℝ) ^ d * (W : ℝ) ^ (-Db) := hsum
      _ ≤ bB d L W x y * ((2 : ℝ) ^ d * (W : ℝ) ^ (ρ / 2)) + bB d L W x y * (W : ℝ) ^ (ρ / 2) := by
          have h1 : (1 : ℝ) ≤ (W : ℝ) ^ (ρ / 2) := Real.one_le_rpow hW1 (by positivity)
          have := mul_le_mul_of_nonneg_left hFle hB.le
          nlinarith
      _ = bB d L W x y * (((2 : ℝ) ^ d + 1) * (W : ℝ) ^ (ρ / 2)) := by ring
      _ ≤ bB d L W x y * ((W : ℝ) ^ (ρ / 2) * (W : ℝ) ^ (ρ / 2)) := by
          gcongr
      _ = (W : ℝ) ^ ρ * bB d L W x y := by
          rw [← Real.rpow_add hW0]; ring_nf

end Conv

/-! ## The grid -/

section Grid

/-- The number of grid steps per unit length, `N = 10 (2L)^{d+6}`. -/
private def Bootstrap_N (d L : ℕ) : ℕ := 10 * (2 * L) ^ (d + 6)

/-- The grid point `j/N + i (1 − k/N)`. -/
private def Bootstrap_pt (N : ℕ) (j : ℤ) (k : ℕ) : ℂ := ⟨(j : ℝ) / N, 1 - (k : ℝ) / N⟩

private theorem Bootstrap_N_pos (d L : ℕ) [NeZero L] : (0 : ℝ) < Bootstrap_N d L := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have : 0 < Bootstrap_N d L := by unfold Bootstrap_N; positivity
  exact_mod_cast this

/-- The grid point one step above a grid point of `𝐃(κ, ε)` is in `𝐃(κ, ε)`. -/
private theorem Bootstrap_pt_up {κ ε : ℝ} {W L N : ℕ} (hN : (0 : ℝ) < N) {j : ℤ} {k : ℕ}
    (h : Bootstrap_pt N j (k + 1) ∈ specDom κ ε W L) : Bootstrap_pt N j k ∈ specDom κ ε W L := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · have : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by gcongr; exact_mod_cast Nat.le_succ k
    change (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ 1 - ((k + 1 : ℕ) : ℝ) / N at h2
    change (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ 1 - (k : ℝ) / N
    linarith
  · change 1 - (k : ℝ) / N ≤ 1
    have : 0 ≤ (k : ℝ) / N := by positivity
    linarith

/-- Consecutive grid points on a vertical line are at distance `1/N ≤ 2/N`. -/
private theorem Bootstrap_pt_step {N : ℕ} (hN : (0 : ℝ) < N) (j : ℤ) (k : ℕ) :
    ‖Bootstrap_pt N j k - Bootstrap_pt N j (k + 1)‖ ≤ 2 / N := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (Bootstrap_pt N j k - Bootstrap_pt N j (k + 1)).re = 0 := by
    simp [Bootstrap_pt]
  have him : (Bootstrap_pt N j k - Bootstrap_pt N j (k + 1)).im = 1 / N := by
    simp only [Bootstrap_pt, Complex.sub_im]
    field_simp
    push_cast
    ring
  rw [hre, him, abs_zero, zero_add, abs_of_pos (by positivity)]
  gcongr
  norm_num

/-- Every point of `𝐃(κ, ε)` is within `2/N` of a grid point of `𝐃(κ, ε)` with the same or a
larger imaginary part. -/
private theorem Bootstrap_pt_cover {κ ε : ℝ} {W L N : ℕ} (hN : (0 : ℝ) < N) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) :
    ∃ j : ℤ, ∃ k : ℕ, Bootstrap_pt N j k ∈ specDom κ ε W L ∧ ‖z - Bootstrap_pt N j k‖ ≤ 2 / N := by
  obtain ⟨h1, h2, h3⟩ := hz
  set x : ℝ := z.re * N with hx
  obtain ⟨j, hj1, hj2⟩ : ∃ j : ℤ, |(j : ℝ)| ≤ |x| ∧ |x - j| ≤ 1 := by
    rcases le_or_gt 0 x with hx0 | hx0
    · refine ⟨⌊x⌋, ?_, ?_⟩
      · have h4 := Int.floor_le x
        have h5 : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.2 hx0
        rw [abs_of_nonneg h5, abs_of_nonneg hx0]
        exact h4
      · have h4 := Int.floor_le x
        have h5 := Int.lt_floor_add_one x
        rw [abs_le]; constructor <;> linarith
    · refine ⟨⌈x⌉, ?_, ?_⟩
      · have h4 := Int.le_ceil x
        have h5 : (⌈x⌉ : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by simpa using hx0.le)
        rw [abs_of_nonpos h5, abs_of_neg hx0]
        linarith
      · have h4 := Int.le_ceil x
        have h5 := Int.ceil_lt_add_one x
        rw [abs_le]; constructor <;> linarith
  set t : ℝ := (1 - z.im) * N with ht
  have ht0 : 0 ≤ t := mul_nonneg (by linarith) hN.le
  set k : ℕ := ⌊t⌋₊ with hk
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have htk : t < (k : ℝ) + 1 := Nat.lt_floor_add_one t
  have hkN : (k : ℝ) / N ≤ 1 - z.im := by
    rw [div_le_iff₀ hN]; linarith
  have hkN' : 1 - z.im - (k : ℝ) / N ≤ 1 / N := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN]; nlinarith
  refine ⟨j, k, ⟨?_, ?_, ?_⟩, ?_⟩
  · change |(j : ℝ) / N| < 2 - κ
    rw [abs_div, abs_of_pos hN, div_lt_iff₀ hN]
    calc |(j : ℝ)| ≤ |x| := hj1
      _ = |z.re| * N := by rw [hx, abs_mul, abs_of_pos hN]
      _ < (2 - κ) * N := mul_lt_mul_of_pos_right h1 hN
  · change (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ 1 - (k : ℝ) / N
    linarith
  · change 1 - (k : ℝ) / N ≤ 1
    have : 0 ≤ (k : ℝ) / N := by positivity
    linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : (z - Bootstrap_pt N j k).re = (x - j) / N := by
      simp only [Complex.sub_re, Bootstrap_pt]
      rw [hx]; field_simp
    have him : (z - Bootstrap_pt N j k).im = -(1 - z.im - (k : ℝ) / N) := by
      simp only [Complex.sub_im, Bootstrap_pt]; ring
    rw [hre, him, abs_neg, abs_div, abs_of_pos hN]
    have : |x - j| / N ≤ 1 / N := div_le_div_of_nonneg_right hj2 hN.le
    have hIm : |1 - z.im - (k : ℝ) / N| ≤ 1 / N := abs_le.2 ⟨by
      have : (0 : ℝ) ≤ 1 / N := by positivity
      linarith, hkN'⟩
    have e : (2 : ℝ) / N = 1 / N + 1 / N := by ring
    linarith

/-- A grid point of `𝐃(κ, ε)` has `|j| ≤ 2N` and `k ≤ N`. -/
private theorem Bootstrap_pt_mem {κ ε : ℝ} (hκ : 0 < κ) {W L N : ℕ} [NeZero L] (hW : 1 ≤ W)
    (hN : (0 : ℝ) < N) {j : ℤ} {k : ℕ} (h : Bootstrap_pt N j k ∈ specDom κ ε W L) :
    (j, k) ∈ Finset.Icc (-(2 * N : ℤ)) (2 * N) ×ˢ Finset.range (N + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  change |(j : ℝ) / N| < 2 - κ at h1
  change (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ 1 - (k : ℝ) / N at h2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hpos : 0 < (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by positivity
  rw [abs_div, abs_of_pos hN, div_lt_iff₀ hN] at h1
  have hj : |(j : ℝ)| < 2 * N := by nlinarith
  have hk : (k : ℝ) < N := by
    have : (k : ℝ) / N < 1 := by linarith
    rwa [div_lt_one hN] at this
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  rw [abs_lt] at hj
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : (-(2 * N : ℤ) : ℝ) ≤ (j : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (j : ℝ) ≤ ((2 * N : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : k < N := by exact_mod_cast hk
    omega

end Grid

/-! ## The deterministic bootstrap -/

section Core

variable {d L : ℕ} [NeZero L]

/-- Between two points of `𝐃(κ, ε)` at distance at most `2/N`, `Y` and every `X_{ab}` increase by
at most `1`. -/
private theorem Bootstrap_transfer (hd : 2 ≤ d) {W : ℕ} (hW : 1 ≤ W) (hWL : (W : ℝ) ≤ L)
    {κ ε : ℝ} (hε : 0 < ε) {S : Matrix (Zd d L) (Zd d L) ℝ} (hS0 : ∀ i j, 0 ≤ S i j)
    (hS1 : ∀ i, ∑ j, S i j = 1) (hS2 : ∀ j, ∑ i, S i j = 1)
    {H : Matrix (Zd d L) (Zd d L) ℂ} (hH : H.IsHermitian) {z w : ℂ}
    (hz : z ∈ specDom κ ε W L) (hw : w ∈ specDom κ ε W L)
    (hzw : ‖z - w‖ ≤ 2 / (Bootstrap_N d L : ℝ)) :
    cutY W (green H w) (msc w) ≤ cutY W (green H z) (msc z) + 1 ∧
      ∀ a b, cutX W S (green H w) a b ≤ cutX W S (green H z) a b + 1 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set Λ : ℝ := 2 * (L : ℝ) with hΛ
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hN : (Bootstrap_N d L : ℝ) = 10 * Λ ^ (d + 6) := by
    unfold Bootstrap_N; push_cast; ring
  set u : ℝ := ‖z - w‖ with hu_def
  have hu0 : 0 ≤ u := norm_nonneg _
  have hu : u * Λ ^ (d + 6) ≤ 1 / 5 := by
    rw [hN, le_div_iff₀ (by positivity)] at hzw
    linarith
  set P : ℝ := Λ ^ (d + 6) with hP
  have hP1 : Λ ^ 2 * Λ ^ 2 * Λ ^ d ≤ P := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hΛ1 (by omega)
  have hP2 : Λ ^ 2 * Λ ^ d ≤ P := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hΛ1 (by omega)
  have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) (Bootstrap_im_lower hε hW hz)
  have hw0 : 0 < w.im := lt_of_lt_of_le (by positivity) (Bootstrap_im_lower hε hW hw)
  have hinv : ∀ v : ℂ, v ∈ specDom κ ε W L → 0 < v.im → v.im⁻¹ ≤ Λ ^ 2 := by
    intro v hv hv0
    have h1 := Bootstrap_im_lower hε hW hv
    have h2 : v.im⁻¹ ≤ (L : ℝ) ^ 2 := by
      rw [inv_le_comm₀ hv0 (by positivity)]
      simpa [one_div] using h1
    calc v.im⁻¹ ≤ (L : ℝ) ^ 2 := h2
      _ ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hiz := hinv z hz hz0
  have hiw := hinv w hw hw0
  have hiz0 : 0 ≤ z.im⁻¹ := inv_nonneg.2 hz0.le
  have hiw0 : 0 ≤ w.im⁻¹ := inv_nonneg.2 hw0.le
  have hz1 : z.im ≤ 1 := hz.2.2
  have hBinv : ∀ i j : Zd d L, (bB d L W i j)⁻¹ ≤ Λ ^ d := by
    intro i j
    have hB := bB_pos₁ (d := d) (L := L) hW i j
    have h1 := Bootstrap_bB_lower hd hW hWL i j
    rw [inv_le_comm₀ hB (by positivity)]
    simpa [one_div] using h1
  have hG : ∀ i j, ‖green H w i j - green H z i j‖ ≤ u * (z.im⁻¹ * w.im⁻¹) := by
    intro i j
    rw [norm_sub_rev]
    have := Bootstrap_green_lip hH hz0 hw0 i j
    rw [div_eq_mul_inv, mul_inv] at this
    exact this
  constructor
  · -- `Y`
    apply Bootstrap_cutY_le
    intro i j
    have hB := bB_pos₁ (d := d) (L := L) hW i j
    have hs0 : 0 < Real.sqrt (bB d L W i j) := Real.sqrt_pos.2 hB
    have hsB : (Real.sqrt (bB d L W i j))⁻¹ ≤ Λ ^ d := by
      have hle : bB d L W i j ≤ Real.sqrt (bB d L W i j) := by
        rw [Real.le_sqrt hB.le hB.le]
        have := Bootstrap_bB_le_one hd hW i j (L := L)
        nlinarith
      exact (inv_anti₀ hB hle).trans (hBinv i j)
    have hm : ‖msc w - msc z‖ ≤ 4 * u * z.im⁻¹ := by
      rw [norm_sub_rev]
      have := Bootstrap_msc_lip hz0 hz1 hw0
      rwa [div_eq_mul_inv] at this
    set δ : ℝ := u * (z.im⁻¹ * w.im⁻¹) + 4 * u * z.im⁻¹ with hδ
    have he : ‖entryErr (green H w) (msc w) i j‖ ≤ ‖entryErr (green H z) (msc z) i j‖ + δ := by
      have e : entryErr (green H w) (msc w) i j = entryErr (green H z) (msc z) i j +
          ((green H w i j - green H z i j) - (if i = j then msc w - msc z else 0)) := by
        unfold entryErr; split_ifs <;> ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
      refine (norm_sub_le _ _).trans (add_le_add (hG i j) ?_)
      split_ifs
      · exact hm
      · simp only [norm_zero]; positivity
    have hδs : δ * (Real.sqrt (bB d L W i j))⁻¹ ≤ 1 := by
      have h1 : δ ≤ u * (Λ ^ 2 * Λ ^ 2) + 4 * u * Λ ^ 2 := by
        have := mul_le_mul hiz hiw hiw0 (by positivity)
        rw [hδ]
        gcongr
      calc δ * (Real.sqrt (bB d L W i j))⁻¹ ≤ (u * (Λ ^ 2 * Λ ^ 2) + 4 * u * Λ ^ 2) * Λ ^ d :=
            mul_le_mul h1 hsB (by positivity) (by positivity)
        _ = u * (Λ ^ 2 * Λ ^ 2 * Λ ^ d) + 4 * u * (Λ ^ 2 * Λ ^ d) := by ring
        _ ≤ u * P + 4 * u * P := by gcongr
        _ ≤ 1 := by nlinarith
    calc ‖entryErr (green H w) (msc w) i j‖ / Real.sqrt (bB d L W i j)
        ≤ (‖entryErr (green H z) (msc z) i j‖ + δ) / Real.sqrt (bB d L W i j) :=
          div_le_div_of_nonneg_right he hs0.le
      _ = ‖entryErr (green H z) (msc z) i j‖ / Real.sqrt (bB d L W i j) +
            δ * (Real.sqrt (bB d L W i j))⁻¹ := by rw [add_div, div_eq_mul_inv δ]
      _ ≤ cutY W (green H z) (msc z) + 1 :=
          add_le_add (Bootstrap_le_cutY W _ _ i j) hδs
  · -- `X`
    intro a b
    set e : ℝ := u * (z.im⁻¹ * w.im⁻¹) with he
    set s : ℝ := w.im⁻¹ + z.im⁻¹ with hs
    have hδ : ∀ i j, ‖green H w i j‖ ^ 2 ≤ ‖green H z i j‖ ^ 2 + s * e := by
      intro i j
      have ha : ‖green H w i j‖ ≤ w.im⁻¹ := by
        have := norm_green_entry_le hH hw0.ne' i j
        rwa [abs_of_pos hw0] at this
      have hb : ‖green H z i j‖ ≤ z.im⁻¹ := by
        have := norm_green_entry_le hH hz0.ne' i j
        rwa [abs_of_pos hz0] at this
      have h1 : ‖green H w i j‖ - ‖green H z i j‖ ≤ e :=
        (norm_sub_norm_le _ _).trans (hG i j)
      have h2 : ‖green H w i j‖ + ‖green H z i j‖ ≤ s := by rw [hs]; linarith
      have h3 : 0 ≤ ‖green H w i j‖ + ‖green H z i j‖ := by positivity
      have he0 : 0 ≤ e := by positivity
      have h4 := mul_le_mul_of_nonneg_right h1 h3
      have h5 := mul_le_mul_of_nonneg_left h2 he0
      nlinarith
    refine (Bootstrap_cutX_lip hW hS0 hS1 hS2 hδ a b).trans (add_le_add le_rfl ?_)
    have hB := bB_pos₁ (d := d) (L := L) hW a b
    have hse : s * e ≤ (Λ ^ 2 + Λ ^ 2) * (u * (Λ ^ 2 * Λ ^ 2)) := by
      rw [hs, he]
      have := mul_le_mul hiz hiw hiw0 (by positivity)
      gcongr
    calc s * e / bB d L W a b = s * e * (bB d L W a b)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (Λ ^ 2 + Λ ^ 2) * (u * (Λ ^ 2 * Λ ^ 2)) * Λ ^ d :=
          mul_le_mul hse (hBinv a b) (inv_nonneg.2 hB.le) (by positivity)
      _ = 2 * u * P := by rw [hP]; ring
      _ ≤ 1 := by nlinarith

/-- **The deterministic bootstrap.** Let `S ≥ 0` be doubly stochastic, `H` Hermitian, and let the
four inequalities `(L^d)^{2/l} (1 + W^{α/2}) ≤ W^α`, `W^{α/4} ≤ 2 W^α`, `W^{α/2+γ} + 1 ≤ W^β` and
`W^{α/4} + 1 ≤ W^{α/2}` hold. If at every point of `𝐃(κ, ε)` with `Im z = 1` we have `Y ≤ W^β` and
`max_{ab} X_{ab} ≤ W^{α/2}`, and at every grid point of `𝐃(κ, ε)` the event of `cutImproveStmt`
fails and `max_{ab} Z_{ab} < W^{α/4}`, then `Y(z) ≤ W^β` on all of `𝐃(κ, ε)`. -/
private theorem Bootstrap_core (hd : 2 ≤ d) {W : ℕ} (hW : 1 ≤ W) (hWL : (W : ℝ) ≤ L)
    {κ ε : ℝ} (hε : 0 < ε) {S : Matrix (Zd d L) (Zd d L) ℝ} (hS0 : ∀ i j, 0 ≤ S i j)
    (hS1 : ∀ i, ∑ j, S i j = 1) (hS2 : ∀ j, ∑ i, S i j = 1)
    {H : Matrix (Zd d L) (Zd d L) ℂ} (hH : H.IsHermitian) {β α γ : ℝ} {l : ℕ} (hl : 1 ≤ l)
    (c1 : ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) * (1 + (W : ℝ) ^ (α / 2)) ≤ (W : ℝ) ^ α)
    (c2 : (W : ℝ) ^ (α / 4) ≤ 2 * (W : ℝ) ^ α)
    (c3 : (W : ℝ) ^ (α / 2 + γ) + 1 ≤ (W : ℝ) ^ β)
    (c4 : (W : ℝ) ^ (α / 4) + 1 ≤ (W : ℝ) ^ (α / 2))
    (hTop : ∀ z ∈ specDom κ ε W L, z.im = 1 →
      cutY W (green H z) (msc z) ≤ (W : ℝ) ^ β ∧
        ∀ a b, cutX W S (green H z) a b ≤ (W : ℝ) ^ (α / 2))
    (hE1 : ∀ (j : ℤ) (k : ℕ), Bootstrap_pt (Bootstrap_N d L) j k ∈ specDom κ ε W L →
      ¬ (cutY W (green H (Bootstrap_pt (Bootstrap_N d L) j k))
            (msc (Bootstrap_pt (Bootstrap_N d L) j k)) ≤ (W : ℝ) ^ β ∧
          (∀ a b, cutX W S (green H (Bootstrap_pt (Bootstrap_N d L) j k)) a b ≤
            2 * (W : ℝ) ^ α) ∧
          (W : ℝ) ^ (α / 2 + γ) < cutY W (green H (Bootstrap_pt (Bootstrap_N d L) j k))
            (msc (Bootstrap_pt (Bootstrap_N d L) j k))))
    (hE2 : ∀ (j : ℤ) (k : ℕ), Bootstrap_pt (Bootstrap_N d L) j k ∈ specDom κ ε W L →
      ∀ a b, cutZ β α l W S (green H (Bootstrap_pt (Bootstrap_N d L) j k))
        (msc (Bootstrap_pt (Bootstrap_N d L) j k)) a b < (W : ℝ) ^ (α / 4)) :
    ∀ z ∈ specDom κ ε W L, cutY W (green H z) (msc z) ≤ (W : ℝ) ^ β := by
  set N : ℕ := Bootstrap_N d L with hNdef
  have hN : (0 : ℝ) < N := Bootstrap_N_pos d L
  -- the improvement at a grid point
  have improve : ∀ (j : ℤ) (k : ℕ), Bootstrap_pt N j k ∈ specDom κ ε W L →
      cutY W (green H (Bootstrap_pt N j k)) (msc (Bootstrap_pt N j k)) ≤ (W : ℝ) ^ β →
      (∀ a b, cutX W S (green H (Bootstrap_pt N j k)) a b ≤ (W : ℝ) ^ (α / 2)) →
      cutY W (green H (Bootstrap_pt N j k)) (msc (Bootstrap_pt N j k)) ≤ (W : ℝ) ^ (α / 2 + γ) ∧
        ∀ a b, cutX W S (green H (Bootstrap_pt N j k)) a b < (W : ℝ) ^ (α / 4) := by
    intro j k hjk hY hX
    have hM : cutM l W S (green H (Bootstrap_pt N j k)) ≤ (W : ℝ) ^ α :=
      (Bootstrap_cutM_le hl fun a b => ⟨Bootstrap_cutX_nonneg hW hS0 _ a b, hX a b⟩).trans c1
    have hX' : ∀ a b, cutX W S (green H (Bootstrap_pt N j k)) a b < (W : ℝ) ^ (α / 4) := by
      intro a b
      rw [← Bootstrap_cutZ_eq hW hY hM a b]
      exact hE2 j k hjk a b
    refine ⟨?_, hX'⟩
    by_contra hcon
    exact hE1 j k hjk ⟨hY, fun a b => (hX' a b).le.trans c2, not_le.mp hcon⟩
  -- one step of size at most `2/N`
  have step : ∀ z w : ℂ, z ∈ specDom κ ε W L → w ∈ specDom κ ε W L → ‖z - w‖ ≤ 2 / N →
      cutY W (green H z) (msc z) ≤ (W : ℝ) ^ (α / 2 + γ) →
      (∀ a b, cutX W S (green H z) a b < (W : ℝ) ^ (α / 4)) →
      cutY W (green H w) (msc w) ≤ (W : ℝ) ^ β ∧
        ∀ a b, cutX W S (green H w) a b ≤ (W : ℝ) ^ (α / 2) := by
    intro z w hz hw hzw hY hX
    obtain ⟨hY', hX'⟩ := Bootstrap_transfer hd hW hWL hε hS0 hS1 hS2 hH hz hw hzw
    exact ⟨by linarith, fun a b => by linarith [hX' a b, hX a b]⟩
  -- the induction down each vertical line
  have ind : ∀ (k : ℕ) (j : ℤ), Bootstrap_pt N j k ∈ specDom κ ε W L →
      cutY W (green H (Bootstrap_pt N j k)) (msc (Bootstrap_pt N j k)) ≤ (W : ℝ) ^ β ∧
        ∀ a b, cutX W S (green H (Bootstrap_pt N j k)) a b ≤ (W : ℝ) ^ (α / 2) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      exact hTop _ hj (by simp [Bootstrap_pt])
    | succ k ih =>
      intro j hj
      have hj' := Bootstrap_pt_up hN hj
      obtain ⟨hY, hX⟩ := ih j hj'
      obtain ⟨hY', hX'⟩ := improve j k hj' hY hX
      exact step _ _ hj' hj (Bootstrap_pt_step hN j k) hY' hX'
  intro z hz
  obtain ⟨j, k, hjk, hdist⟩ := Bootstrap_pt_cover hN hz (N := N)
  obtain ⟨hY, hX⟩ := ind k j hjk
  obtain ⟨hY', hX'⟩ := improve j k hjk hY hX
  exact (step _ _ hjk hz (by rwa [norm_sub_rev]) hY' hX').1

end Core

/-! ## Markov's inequality for `Z_{ab}` -/

section Markov

variable {d L : ℕ} [NeZero L]

/-- `ω ↦ Z_{ab}(z)` is measurable for `Im z ≠ 0`. -/
private theorem Bootstrap_measurable_cutZ (β α : ℝ) (l W : ℕ) (S : Matrix (Zd d L) (Zd d L) ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (a b : Zd d L) :
    Measurable fun ω : Sample (Zd d L) => cutZ β α l W S (green (hmat ω) z) (msc z) a b := by
  have hG : ∀ i j, Measurable fun ω : Sample (Zd d L) => green (hmat ω) z i j := fun i j =>
    (testFn_closed.2.2.2.2.2 _ (testFn_green z hz i j)).1
  have hX : ∀ a b, Measurable fun ω : Sample (Zd d L) => cutX W S (green (hmat ω) z) a b := by
    intro a b
    unfold cutX cutD
    fun_prop
  have hY : Measurable fun ω : Sample (Zd d L) => cutY W (green (hmat ω) z) (msc z) := by
    unfold cutY entryErr
    refine Measurable.iSup fun i => Measurable.iSup fun j => ?_
    fun_prop
  have hM : Measurable fun ω : Sample (Zd d L) => cutM l W S (green (hmat ω) z) := by
    unfold cutM
    fun_prop
  unfold cutZ cutC
  refine Measurable.mul (Measurable.ite (measurableSet_le hY measurable_const) ?_
    measurable_const) (hX a b)
  unfold cutPhi
  fun_prop

/-- Markov's inequality for `Z_{ab}(z)`: for a doubly stochastic `S ≥ 0`, `Im z > 0` and `t > 0`,
`E Z_{ab}^q ≤ M` gives `P(Z_{ab} ≥ t) ≤ M / t^q` (`Z_{ab}` is bounded, so `Z_{ab}^q` is
integrable). -/
private theorem Bootstrap_markov (W : ℕ) (hW : 1 ≤ W)
    {S : Matrix (Zd d L) (Zd d L) ℝ} (hS0 : ∀ i j, 0 ≤ S i j) (hS1 : ∀ i, ∑ j, S i j = 1)
    (hS2 : ∀ j, ∑ i, S i j = 1) {z : ℂ} (hz : 0 < z.im) (β α : ℝ) (l q : ℕ) (a b : Zd d L)
    {μ : Measure (Sample (Zd d L))} [IsProbabilityMeasure μ] {t M : ℝ} (ht : 0 < t)
    (hint : ∫ ω, cutZ β α l W S (green (hmat ω) z) (msc z) a b ^ q ∂μ ≤ M) :
    μ {ω | t ≤ cutZ β α l W S (green (hmat ω) z) (msc z) a b} ≤ ENNReal.ofReal (M / t ^ q) := by
  set Z : Sample (Zd d L) → ℝ := fun ω => cutZ β α l W S (green (hmat ω) z) (msc z) a b with hZ
  have hmeas : Measurable Z := Bootstrap_measurable_cutZ β α l W S hz.ne' a b
  have hB := bB_pos₁ (d := d) (L := L) hW a b
  set K : ℝ := (z.im⁻¹) ^ 2 / bB d L W a b with hK
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω =>
    mul_nonneg (Bootstrap_cutC_mem β α l W S _ _).1 (Bootstrap_cutX_nonneg hW hS0 _ a b)
  have hZK : ∀ ω, Z ω ≤ K := by
    intro ω
    have hX0 := Bootstrap_cutX_nonneg hW hS0 (green (hmat ω) z) a b
    have hC := Bootstrap_cutC_mem β α l W S (green (hmat ω) z) (msc z)
    have hδ : ∀ i j, ‖green (hmat ω) z i j‖ ^ 2 ≤ ‖(0 : Matrix (Zd d L) (Zd d L) ℂ) i j‖ ^ 2 +
        (z.im⁻¹) ^ 2 := by
      intro i j
      have := norm_green_entry_le (hmat_isHermitian ω) hz.ne' i j
      rw [abs_of_pos hz] at this
      simp only [Matrix.zero_apply, norm_zero, zero_pow two_ne_zero, zero_add]
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hX := Bootstrap_cutX_lip hW hS0 hS1 hS2 hδ a b
    have h0 : cutX W S (0 : Matrix (Zd d L) (Zd d L) ℂ) a b = 0 := by
      simp [cutX, cutD]
    rw [h0, zero_add] at hX
    calc Z ω = cutC β α l W S (green (hmat ω) z) (msc z) * cutX W S (green (hmat ω) z) a b := rfl
      _ ≤ 1 * cutX W S (green (hmat ω) z) a b := mul_le_mul_of_nonneg_right hC.2 hX0
      _ ≤ K := by rw [one_mul]; exact hX
  have hint' : Integrable (fun ω => Z ω ^ q) μ := by
    refine Integrable.of_bound (hmeas.pow_const q).aestronglyMeasurable (K ^ q)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hZ0 ω) q)]
    exact pow_le_pow_left₀ (hZ0 ω) (hZK ω) q
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => pow_nonneg (hZ0 ω) q)
    hint' (t ^ q)
  have htq : 0 < t ^ q := pow_pos ht q
  have hsub : {ω | t ≤ Z ω} ⊆ {ω | t ^ q ≤ Z ω ^ q} := fun ω hω =>
    pow_le_pow_left₀ ht.le hω q
  calc μ {ω | t ≤ Z ω} ≤ μ {ω | t ^ q ≤ Z ω ^ q} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | t ^ q ≤ Z ω ^ q}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (M / t ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ htq, mul_comm]
        exact hmk.trans hint

end Markov

/-! ## Asymptotics in `W` -/

/-- `K (1 + x^a) ≤ x^b` for large `x`, when `0 ≤ a < b`. -/
private theorem Bootstrap_ev_pow (K a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, K * (1 + x ^ a) ≤ x ^ b := by
  have h1 := (tendsto_rpow_atTop (sub_pos.2 hab)).eventually (eventually_ge_atTop (2 * |K|))
  filter_upwards [h1, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hxa : 1 ≤ x ^ a := Real.one_le_rpow hx1 ha
  have e : x ^ b = x ^ (b - a) * x ^ a := by rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  have hK := abs_nonneg K
  calc K * (1 + x ^ a) ≤ |K| * (1 + x ^ a) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * (2 * x ^ a) := by gcongr; linarith
    _ = (2 * |K|) * x ^ a := by ring
    _ ≤ x ^ (b - a) * x ^ a := mul_le_mul_of_nonneg_right hx (by positivity)

/-! ## Counting -/

/-- The index set of the grid, `{−2N, …, 2N} × {0, …, N}`, has at most `10 N²` elements. -/
private theorem Bootstrap_card_le (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.Icc (-(2 * N : ℤ)) (2 * N) ×ˢ Finset.range (N + 1)).card : ℝ) ≤ 10 * (N : ℝ) ^ 2 := by
  have h1 : (Finset.Icc (-(2 * N : ℤ)) (2 * N) ×ˢ Finset.range (N + 1)).card =
      (4 * N + 1) * (N + 1) := by
    rw [Finset.card_product, Int.card_Icc, Finset.card_range]
    congr 1
    omega
  have h2 : (4 * N + 1) * (N + 1) ≤ 10 * N ^ 2 := by nlinarith
  rw [h1]
  exact_mod_cast h2

/-- The number of grid points times `|Z_L^d|²` is at most `1000 · 2^{4d+12} W^{(4d+12)/c₁}` for
`L ≤ W^{1/c₁}`. -/
private theorem Bootstrap_count {d L W : ℕ} [NeZero L] (hW : (1 : ℝ) ≤ W) {c₁ : ℝ}
    (hLW : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁)) :
    ((Finset.Icc (-(2 * Bootstrap_N d L : ℤ)) (2 * Bootstrap_N d L) ×ˢ
        Finset.range (Bootstrap_N d L + 1)).card : ℝ) * ((L : ℝ) ^ d * (L : ℝ) ^ d) ≤
      1000 * 2 ^ (4 * d + 12) * (W : ℝ) ^ ((4 * (d : ℝ) + 12) / c₁) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hW0 : (0 : ℝ) < W := by linarith
  have hN4 : (Bootstrap_N d L : ℝ) = 10 * (2 * (L : ℝ)) ^ (d + 6) := by
    unfold Bootstrap_N; push_cast; ring
  have hN1 : 1 ≤ Bootstrap_N d L := by
    have : (1 : ℝ) ≤ Bootstrap_N d L := by
      rw [hN4]
      have : (1 : ℝ) ≤ (2 * (L : ℝ)) ^ (d + 6) := one_le_pow₀ (by linarith)
      linarith
    exact_mod_cast this
  have hcardT := Bootstrap_card_le (Bootstrap_N d L) hN1
  rw [hN4] at hcardT
  have hLe : (L : ℝ) ^ (4 * d + 12) ≤ (W : ℝ) ^ ((4 * (d : ℝ) + 12) / c₁) := by
    calc (L : ℝ) ^ (4 * d + 12) ≤ ((W : ℝ) ^ (1 / c₁)) ^ (4 * d + 12) :=
          pow_le_pow_left₀ (by positivity) hLW _
      _ = (W : ℝ) ^ ((4 * (d : ℝ) + 12) / c₁) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; push_cast; ring_nf
  have hLL : (L : ℝ) ^ d * (L : ℝ) ^ d ≤ (2 * (L : ℝ)) ^ d * (2 * (L : ℝ)) ^ d := by
    have : (L : ℝ) ^ d ≤ (2 * (L : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    exact mul_le_mul this this (by positivity) (by positivity)
  calc _ ≤ 10 * (10 * (2 * (L : ℝ)) ^ (d + 6)) ^ 2 * ((2 * (L : ℝ)) ^ d * (2 * (L : ℝ)) ^ d) :=
        mul_le_mul hcardT hLL (by positivity) (by positivity)
    _ = 1000 * 2 ^ (4 * d + 12) * (L : ℝ) ^ (4 * d + 12) := by
        rw [← pow_add, mul_pow, mul_pow, mul_pow]; ring_nf
    _ ≤ 1000 * 2 ^ (4 * d + 12) * (W : ℝ) ^ ((4 * (d : ℝ) + 12) / c₁) :=
        mul_le_mul_of_nonneg_left hLe (by positivity)

/-- The final sum of the three failure probabilities is at most `W^{−D}`. -/
private theorem Bootstrap_final {W cT LL r KT e D : ℝ} (hW : 1 ≤ W) (hcT : 0 ≤ cT)
    (hLL : 1 ≤ LL) (hKT : 0 ≤ KT) (hcount : cT * LL ≤ KT * W ^ e) (hr0 : 0 ≤ r)
    (hr : r ≤ W ^ (-(D + e + 2))) (h6 : (1 + 2 * KT) * (1 + W ^ (0 : ℝ)) ≤ W ^ (2 : ℝ)) :
    W ^ (-(D + 2)) + cT * W ^ (-(D + e + 2)) + cT * LL * r ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have he2 : W ^ e * W ^ (-(D + e + 2)) = W ^ (-(D + 2)) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hx : 0 ≤ W ^ (-(D + e + 2)) := by positivity
  have k1 : cT * W ^ (-(D + e + 2)) ≤ KT * W ^ (-(D + 2)) := by
    rw [← he2, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hx
    exact (le_mul_of_one_le_right hcT hLL).trans hcount
  have k2 : cT * LL * r ≤ KT * W ^ (-(D + 2)) := by
    rw [← he2, ← mul_assoc]
    exact mul_le_mul hcount hr hr0 (by positivity)
  have k3 : (1 + 2 * KT) * W ^ (-(D + 2)) ≤ W ^ (-D) := by
    rw [Real.rpow_zero] at h6
    have e3 : W ^ (-D) = W ^ (2 : ℝ) * W ^ (-(D + 2)) := by
      rw [← Real.rpow_add hW0]; ring_nf
    rw [e3]
    have hy : 0 ≤ W ^ (-(D + 2)) := by positivity
    have : 1 + 2 * KT ≤ W ^ (2 : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right this hy
  linarith

/-- The Markov bound `W^{qν} / (W^{α/4})^q ≤ W^{−(D+e+2)}` for `ν = α/64` and
`q · 15α/64 ≥ D + e + 2`. -/
private theorem Bootstrap_markov_exp {W α ν D e : ℝ} {q : ℕ} (hW : 1 ≤ W) (hν : ν = α / 64)
    (hq : D + e + 2 ≤ (q : ℝ) * (15 * α / 64)) :
    W ^ ((q : ℝ) * ν) / (W ^ (α / 4)) ^ q ≤ W ^ (-(D + e + 2)) := by
  have hW0 : 0 < W := by linarith
  rw [← Real.rpow_natCast (W ^ (α / 4)), ← Real.rpow_mul hW0.le, ← Real.rpow_sub hW0]
  refine Real.rpow_le_rpow_of_exponent_le hW ?_
  have e : (q : ℝ) * ν - α / 4 * q = -((q : ℝ) * (15 * α / 64)) := by rw [hν]; ring
  rw [e]
  linarith

/-- The union bound in `ℝ≥0∞`: `a + Σ_{t ∈ T} b + Σ_{t ∈ T} Σ_{x, y} c` as one real number. -/
private theorem Bootstrap_ennreal_sum {ι κ' : Type*} [Fintype κ'] (T : Finset ι) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a + ∑ _t ∈ T, ENNReal.ofReal b +
        ∑ _t ∈ T, ∑ _x : κ', ∑ _y : κ', ENNReal.ofReal c =
      ENNReal.ofReal (a + (T.card : ℝ) * b +
        (T.card : ℝ) * ((Fintype.card κ' : ℝ) * ((Fintype.card κ' : ℝ) * c))) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add ha (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-! ## The local law -/

/-- **[II, Theorem 3.6] from the cutoff bootstrap**: the improvement on the cutoff event
`cutImproveStmt` and the cutoff moment bound `cutMomentStmt` give `localLawTExpStmt'`:
`|G_{xy}(z) − m(z) δ_{xy}|² ≺ B_{xy}` uniformly in `z ∈ 𝐃(κ, ε)` and `x, y`, along `W → ∞` inside
`adm(c₀, c₁)` with `L²/W² ≤ W^{(n−1)d/2 − c₀ᵀ}`, from a family of `n`-th order `T`-expansions with
`D`-th order error for every `D ≥ n + 2` (the member `D = n + 4` is used). The local law at
`η = 1` ([II, Lemma 7.2]) enters through `eta1Step_of` and `dcWeakDom`. -/
theorem localLawTExp_cutoff_of : cutImproveStmt → cutMomentStmt → localLawTExpStmt' := by
  intro hImp hMom d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T n H τ hτ D hD
  have hd2 : 2 ≤ d := by omega
  have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hc₀1 : c₀ < 1 := by linarith
  obtain ⟨Sig, 𝒯, hT, hDef⟩ := H (n + 4) (by omega)
  obtain ⟨β₀, hβ₀, hmom⟩ :=
    hMom d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T n (n + 4) Sig 𝒯 le_rfl hT hDef
  -- the exponents
  set β : ℝ := min (min β₀ (τ / 2)) ((d : ℝ) / 200) with hβ
  have hβ0 : 0 < β := lt_min (lt_min hβ₀ (by linarith)) (by positivity)
  have hββ₀ : β ≤ β₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hβτ : β ≤ τ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hβd : β < (d : ℝ) / 100 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set α : ℝ := β / 10 with hα
  have hα0 : 0 < α := by positivity
  set γ : ℝ := β / 4 with hγ
  set ν : ℝ := α / 64 with hν
  set l : ℕ := ⌈64 * (d : ℝ) / (c₁ * α)⌉₊ + 1 with hl_def
  have hl : 1 ≤ l := by omega
  have hl_ge : 64 * (d : ℝ) / (c₁ * α) ≤ l := by
    rw [hl_def]; push_cast
    linarith [Nat.le_ceil (64 * (d : ℝ) / (c₁ * α))]
  set e : ℝ := (4 * (d : ℝ) + 12) / c₁ with he
  have he0 : 0 < e := by positivity
  set q : ℕ := ⌈(D + e + 2) / (15 * α / 64)⌉₊ + 1 with hq_def
  have hq : 1 ≤ q := by omega
  have hq_ge : (D + e + 2) / (15 * α / 64) ≤ q := by
    rw [hq_def]; push_cast
    linarith [Nat.le_ceil ((D + e + 2) / (15 * α / 64))]
  set KT : ℝ := 1000 * 2 ^ (4 * d + 12) with hKT
  -- the inputs
  have hmomE := hmom β hβ0 hββ₀ ν (by positivity) l q hl hq
  have hImpE := hImp d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε β α γ hβ0 hβd hα0 (by positivity)
    (D + e + 2) (by positivity)
  have hEta := eta1Step_of dcWeakDom d hd P c₀ c₁ κ hc₀ hc₁ hc hκ (α / 4) (by positivity) (D + 2)
    (by positivity)
  have hconv := Bootstrap_conv hd2 P hc₀ hc₁ hc (ρ := α / 32) (by positivity)
  have hsz := tendsto_sizeW_admFilterL c₀ c₁
  have hw1 := hsz.eventually (Bootstrap_ev_pow 1 (α / 2) (31 * α / 32) (by positivity)
    (by linarith))
  have hw3 := hsz.eventually (Bootstrap_ev_pow 1 (α / 2 + γ) β (by positivity) (by linarith))
  have hw4 := hsz.eventually (Bootstrap_ev_pow 1 (α / 4) (α / 2) (by positivity) (by linarith))
  have hw5 := hsz.eventually (Bootstrap_ev_pow 4 (5 * α / 16) (α / 2) (by positivity)
    (by linarith))
  have hw6 := hsz.eventually (Bootstrap_ev_pow (1 + 2 * KT) 0 2 le_rfl (by norm_num))
  have hw7 := hsz.eventually (eventually_ge_atTop (2 : ℝ))
  have hle : llFilter d n c₀ c₁ c₀T ≤ admFilterL c₀ c₁ := inf_le_left
  filter_upwards [hmomE, hle hImpE, hle hEta, hle hconv, hle (Bootstrap_ev_adm c₀ c₁), hle hw1,
    hle hw3, hle hw4, hle hw5, hle hw6, hle hw7] with p hmomp hImpp hEtap hconvp hadm hw1p hw3p
    hw4p hw5p hw6p hw7p
  set W : ℕ := p.1.1 with hWdef
  set L : ℕ := p.1.2 with hLdef
  change (2 : ℝ) ≤ (W : ℝ) at hw7p
  have hW1n : 1 ≤ W := by
    have : (1 : ℝ) ≤ W := by linarith
    exact_mod_cast this
  have hW0 : (0 : ℝ) < W := by linarith
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hL1n : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL1n
  obtain ⟨hWL, hLW, -⟩ := Bootstrap_adm_facts hL1n hc₀ hc₀1 hc₁ hadm
  obtain ⟨hS0, hSs, hS1, hS2, hSB, hSBB⟩ := hconvp
  set S := Smat P.ψ W L with hSdef
  set N : ℕ := Bootstrap_N d L with hNdef
  have hN : (0 : ℝ) < N := Bootstrap_N_pos d L
  set T : Finset (ℤ × ℕ) := Finset.Icc (-(2 * N : ℤ)) (2 * N) ×ˢ Finset.range (N + 1) with hTdef
  -- the conditions of the deterministic bootstrap
  have c1 : ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) * (1 + (W : ℝ) ^ (α / 2)) ≤ (W : ℝ) ^ α := by
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
    have hexp : 1 / c₁ * d * (2 / l) ≤ α / 32 := by
      have h1 : 64 * (d : ℝ) ≤ c₁ * α * l := by
        rw [div_le_iff₀ (by positivity)] at hl_ge; linarith
      rw [show 1 / c₁ * d * (2 / l) = 2 * d / (c₁ * l) by field_simp, div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) ≤ (W : ℝ) ^ (α / 32) := by
      calc ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) ≤ (((W : ℝ) ^ (1 / c₁)) ^ d) ^ ((2 : ℝ) / l) :=
            Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (by positivity) hLW d)
              (by positivity)
        _ = (W : ℝ) ^ (1 / c₁ * d * (2 / l)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_mul hW0.le]
        _ ≤ (W : ℝ) ^ (α / 32) := Real.rpow_le_rpow_of_exponent_le hW1 hexp
    have h2 : 1 * (1 + (W : ℝ) ^ (α / 2)) ≤ (W : ℝ) ^ (31 * α / 32) := hw1p
    calc ((L : ℝ) ^ d) ^ ((2 : ℝ) / l) * (1 + (W : ℝ) ^ (α / 2))
        ≤ (W : ℝ) ^ (α / 32) * (W : ℝ) ^ (31 * α / 32) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = (W : ℝ) ^ α := by rw [← Real.rpow_add hW0]; ring_nf
  have c2 : (W : ℝ) ^ (α / 4) ≤ 2 * (W : ℝ) ^ α := by
    have := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith : α / 4 ≤ α)
    have : 0 < (W : ℝ) ^ α := by positivity
    linarith
  have c3 : (W : ℝ) ^ (α / 2 + γ) + 1 ≤ (W : ℝ) ^ β := by
    have h : 1 * (1 + (W : ℝ) ^ (α / 2 + γ)) ≤ (W : ℝ) ^ β := hw3p
    linarith
  have c4 : (W : ℝ) ^ (α / 4) + 1 ≤ (W : ℝ) ^ (α / 2) := by
    have h : 1 * (1 + (W : ℝ) ^ (α / 4)) ≤ (W : ℝ) ^ (α / 2) := hw4p
    linarith
  -- the bound at the top edge from the entrywise bound
  have hTop : ∀ ω : Sample (Zd d L), ∀ z ∈ specDom κ ε W L, z.im = 1 →
      (∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ^ 2 ≤
        (W : ℝ) ^ (α / 4) * bB d L W x y) →
      cutY W (green (hmat ω) z) (msc z) ≤ (W : ℝ) ^ β ∧
        ∀ a b, cutX W S (green (hmat ω) z) a b ≤ (W : ℝ) ^ (α / 2) := by
    intro ω z hz hz1 hent
    constructor
    · refine Bootstrap_cutY_le fun i j => ?_
      have hB := bB_pos₁ (d := d) (L := L) hW1n i j
      have hs : 0 < Real.sqrt (bB d L W i j) := Real.sqrt_pos.2 hB
      have h1 : ‖entryErr (green (hmat ω) z) (msc z) i j‖ ≤
          (W : ℝ) ^ (α / 8) * Real.sqrt (bB d L W i j) := by
        have := Real.sqrt_le_sqrt (hent i j)
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow,
          ← Real.rpow_mul hW0.le, show α / 4 * (1 / 2) = α / 8 by ring] at this
      rw [div_le_iff₀ hs]
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hs.le)
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    · intro a b
      have hm : ‖msc z‖ ≤ 1 := (norm_msc_lt_one (by rw [hz1]; exact one_pos)).le
      have h := Bootstrap_cutX_top hW1n hS0 hSs (by positivity) (by positivity) hSB hSBB hm hent a b
      have h5 : 4 * (1 + (W : ℝ) ^ (5 * α / 16)) ≤ (W : ℝ) ^ (α / 2) := hw5p
      have e1 : (W : ℝ) ^ (α / 32) * (W : ℝ) ^ (α / 32) = (W : ℝ) ^ (α / 16) := by
        rw [← Real.rpow_add hW0]; ring_nf
      have e2 : (W : ℝ) ^ (α / 4) * ((W : ℝ) ^ (α / 32)) ^ 2 = (W : ℝ) ^ (5 * α / 16) := by
        rw [sq, e1, ← Real.rpow_add hW0]; ring_nf
      have h3 : (W : ℝ) ^ (α / 16) ≤ (W : ℝ) ^ (5 * α / 16) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      have h4 : 0 ≤ (W : ℝ) ^ (5 * α / 16) := by positivity
      calc cutX W S (green (hmat ω) z) a b
          ≤ 2 * (W : ℝ) ^ (α / 32) * (W : ℝ) ^ (α / 32) +
            2 * (W : ℝ) ^ (α / 4) * ((W : ℝ) ^ (α / 32)) ^ 2 := h
        _ = 2 * ((W : ℝ) ^ (α / 32) * (W : ℝ) ^ (α / 32)) +
            2 * ((W : ℝ) ^ (α / 4) * ((W : ℝ) ^ (α / 32)) ^ 2) := by ring
        _ ≤ (W : ℝ) ^ (α / 2) := by rw [e1, e2]; linarith
  -- the events
  set A3 : Set (Sample (Zd d L)) := {ω | ∃ u : {E : ℝ // |E| < 2 - κ} × Zd d L × Zd d L,
      sizeW p ^ (α / 4) * bB d L W u.2.1 u.2.2 <
        ‖entryErr (green (hmat ω) ((u.1.1 : ℂ) + I)) (msc ((u.1.1 : ℂ) + I)) u.2.1 u.2.2‖ ^ 2}
    with hA3
  set A1 : ℤ × ℕ → Set (Sample (Zd d L)) := fun t => {ω |
      Bootstrap_pt N t.1 t.2 ∈ specDom κ ε W L ∧
      (cutY W (green (hmat ω) (Bootstrap_pt N t.1 t.2)) (msc (Bootstrap_pt N t.1 t.2)) ≤
          (W : ℝ) ^ β ∧
        (∀ a b, cutX W S (green (hmat ω) (Bootstrap_pt N t.1 t.2)) a b ≤ 2 * (W : ℝ) ^ α) ∧
        (W : ℝ) ^ (α / 2 + γ) <
          cutY W (green (hmat ω) (Bootstrap_pt N t.1 t.2)) (msc (Bootstrap_pt N t.1 t.2)))}
    with hA1
  set A2 : ℤ × ℕ → Zd d L → Zd d L → Set (Sample (Zd d L)) := fun t a b => {ω |
      Bootstrap_pt N t.1 t.2 ∈ specDom κ ε W L ∧
      (W : ℝ) ^ (α / 4) ≤ cutZ β α l W S (green (hmat ω) (Bootstrap_pt N t.1 t.2))
        (msc (Bootstrap_pt N t.1 t.2)) a b} with hA2
  -- the deterministic inclusion
  have hsub : {ω | ∃ u : {z : ℂ // z ∈ specDom κ ε W L} × Zd d L × Zd d L,
      sizeW p ^ τ * bB d L W u.2.1 u.2.2 <
        ‖entryErr (green (hmat ω) u.1.1) (msc u.1.1) u.2.1 u.2.2‖ ^ 2} ⊆
      A3 ∪ (⋃ t ∈ T, A1 t) ∪ ⋃ t ∈ T, ⋃ a, ⋃ b, A2 t a b := by
    rintro ω ⟨⟨⟨z, hz⟩, x, y⟩, hlt⟩
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hn
    obtain ⟨⟨h3, h1⟩, h2⟩ := hn
    have hY := Bootstrap_core hd2 hW1n hWL hε hS0 hS1 hS2 (hmat_isHermitian ω) hl c1 c2 c3 c4
      (fun z hz hz1 => hTop ω z hz hz1 fun x y => by
        have hE : |z.re| < 2 - κ := hz.1
        have := not_lt.mp fun h => h3 ⟨(⟨z.re, hE⟩, x, y), h⟩
        have hzE : (((⟨z.re, hE⟩ : {E : ℝ // |E| < 2 - κ}) : ℝ) : ℂ) + I = z := by
          apply Complex.ext <;> simp [hz1]
        rw [hzE] at this
        exact this)
      (fun j k hjk hE1 => h1 (j, k) (Bootstrap_pt_mem hκ hW1n hN hjk) ⟨hjk, hE1⟩)
      (fun j k hjk a b => not_le.mp fun hle =>
        h2 (j, k) (Bootstrap_pt_mem hκ hW1n hN hjk) a b ⟨hjk, hle⟩) z hz
    have hent := Bootstrap_entry_le_cutY hW1n (green (hmat ω) z) (msc z) x y
    have hY0 : 0 ≤ cutY W (green (hmat ω) z) (msc z) :=
      le_trans (by positivity) (Bootstrap_le_cutY W (green (hmat ω) z) (msc z) x y)
    have hB := bB_pos₁ (d := d) (L := L) hW1n x y
    have hsq : cutY W (green (hmat ω) z) (msc z) ^ 2 ≤ (W : ℝ) ^ τ := by
      calc cutY W (green (hmat ω) z) (msc z) ^ 2 ≤ ((W : ℝ) ^ β) ^ 2 :=
            pow_le_pow_left₀ hY0 hY 2
        _ = (W : ℝ) ^ (2 * β) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
        _ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have : ‖entryErr (green (hmat ω) z) (msc z) x y‖ ^ 2 ≤ sizeW p ^ τ * bB d L W x y :=
      hent.trans (mul_le_mul_of_nonneg_right hsq hB.le)
    exact absurd hlt (not_lt.mpr this)
  -- the probabilities
  have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
  set μ := rbmLaw d P p with hμ
  have hP1 : ∀ t, μ (A1 t) ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + e + 2))) := by
    intro t
    by_cases ht : Bootstrap_pt N t.1 t.2 ∈ specDom κ ε W L
    · refine le_trans (measure_mono ?_) (hImpp _ ht)
      intro ω hω
      exact hω.2
    · refine le_trans (measure_mono (t := ∅) ?_) (by simp)
      intro ω hω
      exact (ht hω.1).elim
  set r : ℝ := (W : ℝ) ^ ((q : ℝ) * ν) / ((W : ℝ) ^ (α / 4)) ^ q with hr
  have hr0 : 0 ≤ r :=
    div_nonneg (Real.rpow_nonneg hW0.le _) (pow_nonneg (Real.rpow_nonneg hW0.le _) _)
  have hP2 : ∀ t a b, μ (A2 t a b) ≤ ENNReal.ofReal r := by
    intro t a b
    by_cases ht : Bootstrap_pt N t.1 t.2 ∈ specDom κ ε W L
    · have hz0 : 0 < (Bootstrap_pt N t.1 t.2).im :=
        lt_of_lt_of_le (by positivity) (Bootstrap_im_lower hε hW1n ht)
      refine le_trans (measure_mono ?_) (Bootstrap_markov W hW1n hS0 hS1 hS2 hz0 β α l q a b
        (by positivity) (hmomp _ ht a b))
      intro ω hω
      exact hω.2
    · refine le_trans (measure_mono (t := ∅) ?_) (by simp)
      intro ω hω
      exact (ht hω.1).elim
  -- the counting
  have hcount := Bootstrap_count (d := d) (L := L) hW1 hLW
  have hLd1 : 1 ≤ (L : ℝ) ^ d * (L : ℝ) ^ d := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hL1) (one_le_pow₀ hL1)
  have hq15 : D + e + 2 ≤ (q : ℝ) * (15 * α / 64) := by
    have h15 : (0 : ℝ) < 15 * α / 64 := by positivity
    rw [div_le_iff₀ h15] at hq_ge
    exact hq_ge
  have hr_le : r ≤ (W : ℝ) ^ (-(D + e + 2)) := Bootstrap_markov_exp hW1 hν hq15
  have hfin := Bootstrap_final hW1 (Nat.cast_nonneg T.card) hLd1 (by positivity) hcount
    hr0 hr_le hw6p
  -- the union bound
  refine (measure_mono hsub).trans ?_
  calc μ (A3 ∪ (⋃ t ∈ T, A1 t) ∪ ⋃ t ∈ T, ⋃ a, ⋃ b, A2 t a b)
      ≤ μ A3 + μ (⋃ t ∈ T, A1 t) + μ (⋃ t ∈ T, ⋃ a, ⋃ b, A2 t a b) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((W : ℝ) ^ (-(D + 2))) +
          ∑ _t ∈ T, ENNReal.ofReal ((W : ℝ) ^ (-(D + e + 2))) +
          ∑ _t ∈ T, ∑ _a : Zd d L, ∑ _b : Zd d L, ENNReal.ofReal r := by
        refine add_le_add (add_le_add hEtap ?_) ?_
        · exact (measure_biUnion_finset_le T A1).trans (Finset.sum_le_sum fun t _ => hP1 t)
        · refine (measure_biUnion_finset_le T _).trans (Finset.sum_le_sum fun t _ => ?_)
          refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun b _ => hP2 t a b)
    _ = ENNReal.ofReal ((W : ℝ) ^ (-(D + 2)) + (T.card : ℝ) * (W : ℝ) ^ (-(D + e + 2)) +
          (T.card : ℝ) * ((Fintype.card (Zd d L) : ℝ) * ((Fintype.card (Zd d L) : ℝ) * r))) :=
        Bootstrap_ennreal_sum T (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg hW0.le _) hr0
    _ ≤ ENNReal.ofReal (sizeW p ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le ?_ hfin)
        rw [card_Zd, Nat.cast_pow]
        ring

end RBM8D
