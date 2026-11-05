import RBM8D.SelfEnergy.Renorm
import RBM8D.AvgBound.GhostSize

/-!
# [I, Lemma 8.3]: the renormalized self-energies are close to the self-energies

In [I, Def 8.2] the labels of the `Θ` edges of `Σ^{(r)}_n` read, at every lower order `l`, the
matrix `Σ̊_l = Σ^{(r)}_l − [Σ_x Σ^{(r)}_l(0, x)] S` ([I, (8.3)]); here `Σ̊` is `Renorm.sig Σ` and
`Σ^{(r)}_n = sigMat (Function.update (Renorm.sig Σ) n (Σ n)) S z n`.

* [I, (8.4)] with a term at `x = 0`,
  `|Σ^{(r)}_n(0, x) − Σ_n(0, x)| ≤ η W^{-nd/2} W^{2d-6} ⟨x⟩^{-(2d-6-τ)} + L^τ η W^{-(n-2)d/2} 1_{x=0}`,
  for `d ≥ 8`, lower orders of `Σ` that are self-energies and `Σ_n` of the shape of an `n`-th order
  self-energy, on all of `𝐃(κ, ε)`, proved here as an intermediate step.
* `RenormDiff.rowSum`: [I, (8.5)], `|Σ_x Σ^{(r)}_n(0, x) − Σ_x Σ_n(0, x)| ≤ L^τ η W^{-(n-2)d/2}`,
  with the quantifiers of the second conjunct of `SelfEnergyBound`.

The proof is the induction on the order of [I, Lemma 8.3]. At an order `l < n`,
`Σ̊_l − Σ_l = (Σ^{(r)}_l − Σ_l) − c_l S` is at most `η W^σ W^{-(l-2)d/2} (W ⟨u - v⟩^{-(d+1)} + 1_{u=v})`
by (8.4)–(8.5) at `l`, [I, (1.27)] and [I, (1.8)]. A labelled `Θ` edge is telescoped over its label;
each term `Θ Σ̊ ⋯ Θ (Σ̊_l − Σ_l) Θ Σ ⋯ Θ` is at most `η W^σ W^{-(k-2)d/2} B̃` ([I, Lemma 6.2] for the
two chains, convolutions on the torus). A graph of `Σ_n` is contracted (`G13.dotContract`); if it is
normal regular with `x`, `y` internal, its value is telescoped over its `Θ` edges and every term is a
graph of [I, Cor 6.13] with one marked auxiliary edge (`detAuxTilde`); if it is diagonal
([I, Def 2.13 (i)]), the difference lives at `x = 0`: with an internal atom it is the sum over that
atom of the previous bound (`Diag.graph`), without one it is a product of loops.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Sums of powers of `⟨x - y⟩` on the torus -/

section Sums

variable {d L W : ℕ} [NeZero L]

private theorem RenormDiff_brk_comm (x y : Zd d L) : brk d L W x y = brk d L W y x := by
  unfold brk
  rw [← neg_sub, zdistInf_neg]

private theorem RenormDiff_brk_tri (x u y : Zd d L) :
    brk d L W x y ≤ brk d L W x u + brk d L W u y := by
  unfold brk
  have h := zdistInf_add_le d L (x - u) (u - y)
  rw [sub_add_sub_cancel] at h
  have h' : ((zdistInf d L (x - y) : ℕ) : ℝ) ≤ zdistInf d L (x - u) + zdistInf d L (u - y) := by
    exact_mod_cast h
  linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]

omit [NeZero L] in
private theorem RenormDiff_brk_pos (hW : 1 ≤ W) (x y : Zd d L) : 0 < brk d L W x y :=
  brk_pos₁ hW x y

omit [NeZero L] in
private theorem RenormDiff_le_brk (x y : Zd d L) : (W : ℝ) ≤ brk d L W x y := le_brk₁ x y

omit [NeZero L] in
/-- `B_{xy} = W^{-2} ⟨x - y⟩^{-(d-2)}`. -/
private theorem RenormDiff_bB_eq (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 2)) := by
  unfold bB brk
  congr 2
  ring

/-- `x^{-a} ≤ 2^a y^{-a}` for `0 < y ≤ 2 x`, `a ≥ 0`. -/
private theorem RenormDiff_rpow_half {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) (hyx : y ≤ 2 * x)
    (ha : 0 ≤ a) : x ^ (-a) ≤ 2 ^ a * y ^ (-a) := by
  have h1 : (2 * x) ^ (-a) ≤ y ^ (-a) := Real.rpow_le_rpow_of_nonpos hy hyx (by linarith)
  rw [Real.mul_rpow (by norm_num) hx.le] at h1
  have h2 : (2 : ℝ) ^ a * (2 : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  calc x ^ (-a) = (2 : ℝ) ^ a * ((2 : ℝ) ^ (-a) * x ^ (-a)) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ a * y ^ (-a) := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The splitting of a product of two powers at the nearer end: for `t ≤ s` and
`R ≤ A + B`, `A^{-s} B^{-t} ≤ 2^t R^{-t} (A^{-s} + B^{-s})`. -/
private theorem RenormDiff_minTrick {A B R s t : ℝ} (hA : 0 < A) (hB : 0 < B) (hR : 0 < R)
    (hRAB : R ≤ A + B) (ht : 0 ≤ t) (hst : t ≤ s) :
    A ^ (-s) * B ^ (-t) ≤ 2 ^ t * R ^ (-t) * (A ^ (-s) + B ^ (-s)) := by
  have hAs : 0 ≤ A ^ (-s) := by positivity
  have hBs : 0 ≤ B ^ (-s) := by positivity
  have hRt : 0 ≤ 2 ^ t * R ^ (-t) := by positivity
  rcases le_total A B with h | h
  · have hB2 := RenormDiff_rpow_half hB hR (by linarith) ht
    calc A ^ (-s) * B ^ (-t) ≤ A ^ (-s) * (2 ^ t * R ^ (-t)) := mul_le_mul_of_nonneg_left hB2 hAs
      _ ≤ 2 ^ t * R ^ (-t) * (A ^ (-s) + B ^ (-s)) := by nlinarith
  · have hA2 := RenormDiff_rpow_half hA hR (by linarith) ht
    have hsplit : A ^ (-s) = A ^ (-t) * A ^ (-(s - t)) := by
      rw [← Real.rpow_add hA]; ring_nf
    have hAB : A ^ (-(s - t)) ≤ B ^ (-(s - t)) := Real.rpow_le_rpow_of_nonpos hB h (by linarith)
    have hBsplit : B ^ (-(s - t)) * B ^ (-t) = B ^ (-s) := by
      rw [← Real.rpow_add hB]; ring_nf
    calc A ^ (-s) * B ^ (-t) = A ^ (-t) * A ^ (-(s - t)) * B ^ (-t) := by rw [hsplit]
      _ ≤ (2 ^ t * R ^ (-t)) * B ^ (-(s - t)) * B ^ (-t) := by gcongr
      _ = 2 ^ t * R ^ (-t) * B ^ (-s) := by rw [mul_assoc, hBsplit]
      _ ≤ 2 ^ t * R ^ (-t) * (A ^ (-s) + B ^ (-s)) := by nlinarith

/-- `Σ_u ⟨x - u⟩^{-s} ≤ W^{d-s} 6^d (log₂(L/W) + 2)` for `s ≥ d`, `W ≥ 1`, `L ≥ 2 W`. -/
private theorem RenormDiff_tail (hW : 1 ≤ W) (hWL : 2 * W ≤ L) (s : ℝ) (hs : (d : ℝ) ≤ s)
    (x : Zd d L) :
    ∑ u, brk d L W x u ^ (-s) ≤ (W : ℝ) ^ ((d : ℝ) - s) * (6 ^ d * logF L W) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := brkSum_le d L W hW hWL x
  have hpt : ∀ u, brk d L W x u ^ (-s) ≤ (W : ℝ) ^ ((d : ℝ) - s) * (brk d L W x u ^ d)⁻¹ := by
    intro u
    have hb := RenormDiff_brk_pos (d := d) (L := L) hW x u
    have e1 : brk d L W x u ^ (-s) = brk d L W x u ^ (-((s : ℝ) - d)) * (brk d L W x u ^ d)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hb.le, ← Real.rpow_add hb]; ring_nf
    rw [e1]
    have : brk d L W x u ^ (-((s : ℝ) - d)) ≤ (W : ℝ) ^ ((d : ℝ) - s) := by
      rw [show (d : ℝ) - s = -(s - d) by ring]
      exact Real.rpow_le_rpow_of_nonpos hW0 (RenormDiff_le_brk x u) (by linarith)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  calc ∑ u, brk d L W x u ^ (-s) ≤ ∑ u, (W : ℝ) ^ ((d : ℝ) - s) * (brk d L W x u ^ d)⁻¹ :=
        Finset.sum_le_sum fun u _ => hpt u
    _ = (W : ℝ) ^ ((d : ℝ) - s) * ∑ u, (brk d L W x u ^ d)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- `Σ_u ⟨x - u⟩^{-s} ⟨u - y⟩^{-t} ≤ 2^{t+1} ⟨x - y⟩^{-t} W^{d-s} 6^d (log₂(L/W) + 2)` for
`0 ≤ t ≤ s`, `s ≥ d`, `W ≥ 1`, `L ≥ 2 W`. -/
private theorem RenormDiff_conv (hW : 1 ≤ W) (hWL : 2 * W ≤ L) (s t : ℝ) (ht : 0 ≤ t)
    (hts : t ≤ s) (hds : (d : ℝ) ≤ s) (x y : Zd d L) :
    ∑ u, brk d L W x u ^ (-s) * brk d L W u y ^ (-t) ≤
      2 ^ t * brk d L W x y ^ (-t) * (2 * ((W : ℝ) ^ ((d : ℝ) - s) * (6 ^ d * logF L W))) := by
  have hpt : ∀ u, brk d L W x u ^ (-s) * brk d L W u y ^ (-t) ≤
      2 ^ t * brk d L W x y ^ (-t) * (brk d L W x u ^ (-s) + brk d L W y u ^ (-s)) := by
    intro u
    rw [RenormDiff_brk_comm y u]
    exact RenormDiff_minTrick (RenormDiff_brk_pos hW x u) (RenormDiff_brk_pos hW u y)
      (RenormDiff_brk_pos hW x y) (RenormDiff_brk_tri x u y) ht hts
  have h1 := RenormDiff_tail hW hWL s hds x
  have h2 := RenormDiff_tail hW hWL s hds y
  calc _ ≤ ∑ u, 2 ^ t * brk d L W x y ^ (-t) * (brk d L W x u ^ (-s) + brk d L W y u ^ (-s)) :=
        Finset.sum_le_sum fun u _ => hpt u
    _ = 2 ^ t * brk d L W x y ^ (-t) *
          (∑ u, brk d L W x u ^ (-s) + ∑ u, brk d L W y u ^ (-s)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by
          have := RenormDiff_brk_pos (d := d) (L := L) hW x y; positivity)
        linarith

end Sums

/-! ## Sizes along `adm(c₀, c₁)` -/

/-- On `adm(c₀, c₁)`, `log₂(L/W) + 2 ≤ W^σ` for `W ≥ W₀`. -/
private theorem RenormDiff_logF_le {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) (σ : ℝ) (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      logF L W ≤ (W : ℝ) ^ σ := by
  set A : ℝ := 2 / (c₁ * σ * Real.log 2) with hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 < A := by positivity
  refine ⟨max 1 ((A + 2) ^ (2 / σ)), fun W L _ hadm hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  -- `log L ≤ log W / c₁`
  have hlogL : Real.log L ≤ Real.log W / c₁ := by
    have h := Real.log_le_log (by positivity) hadm.1
    rw [Real.log_rpow hL0] at h
    rw [le_div_iff₀ hc₁]; linarith
  have hlogW : Real.log W ≤ (W : ℝ) ^ (σ / 2) / (σ / 2) := Real.log_le_rpow_div hW0.le (by positivity)
  have hX1 : 1 ≤ (W : ℝ) ^ (σ / 2) := Real.one_le_rpow hW1 (by positivity)
  have hXA : A + 2 ≤ (W : ℝ) ^ (σ / 2) := by
    have h := (le_max_right _ _).trans hW
    calc A + 2 = ((A + 2) ^ (2 / σ)) ^ (σ / 2) := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ (W : ℝ) ^ (σ / 2) := Real.rpow_le_rpow (by positivity) h (by positivity)
  have hlog : Real.logb 2 ((L : ℝ) / W) ≤ A * (W : ℝ) ^ (σ / 2) := by
    rw [Real.logb, Real.log_div hL0.ne' hW0.ne', div_le_iff₀ hl2]
    have hlW : 0 ≤ Real.log W := Real.log_nonneg hW1
    calc Real.log L - Real.log W ≤ Real.log W / c₁ := by linarith
      _ ≤ (W : ℝ) ^ (σ / 2) / (σ / 2) / c₁ := by gcongr
      _ = A * (W : ℝ) ^ (σ / 2) * Real.log 2 := by rw [hA]; field_simp
  have hsq : (W : ℝ) ^ σ = (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  unfold logF
  rw [hsq]
  nlinarith

/-- On `adm(c₀, c₁)` with `c₀ < 1`, `2 W ≤ L` for `W ≥ W₀`. -/
private theorem RenormDiff_two_le {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ < 1) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 2 * W ≤ L := by
  refine ⟨max 1 ((2 : ℝ) ^ (1 / c₀)), fun W L _ hadm hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hWL : (W : ℝ) ≤ L := hadm.2.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : 1 - c₀ ≤ 1)).trans_eq (Real.rpow_one _))
  have h2 : (2 : ℝ) ≤ (L : ℝ) ^ c₀ := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / c₀)) ^ c₀ := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ (L : ℝ) ^ c₀ :=
          Real.rpow_le_rpow (by positivity) (((le_max_right _ _).trans hW).trans hWL) hc₀.le
  have hsplit : (L : ℝ) = (L : ℝ) ^ c₀ * (L : ℝ) ^ (1 - c₀) := by
    rw [← Real.rpow_add hL0]; simp
  have : (2 * W : ℝ) ≤ L := by
    rw [hsplit]
    have := hadm.2
    nlinarith [Real.rpow_nonneg hL0.le (1 - c₀)]
  exact_mod_cast this

/-! ## Convolutions with `B` -/

section Conv

variable {d L W : ℕ} [NeZero L]

omit [NeZero L] in
/-- `‖(X Y)_{xy}‖ ≤ Σ_u ‖X_{xu}‖ ‖Y_{uy}‖`. -/
private theorem RenormDiff_norm_mul {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) (x y : ι) :
    ‖(X * Y) x y‖ ≤ ∑ u, ‖X x u‖ * ‖Y u y‖ := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun u _ => norm_mul _ _

/-- `Σ_v (W ⟨u - v⟩^{-(d+1)} + 1_{u=v}) B_{vy} ≤ (2^{d-1} 6^d (log₂(L/W) + 2) + 1) B_{uy}`. -/
private theorem RenormDiff_FB (hd : 2 ≤ d) (hW : 1 ≤ W) (hWL : 2 * W ≤ L) (u y : Zd d L) :
    ∑ v, ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0) * bB d L W v y ≤
      ((2 : ℝ) ^ ((d : ℝ) - 2) * 2 * 6 ^ d * logF L W + 1) * bB d L W u y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := RenormDiff_conv hW hWL ((d : ℝ) + 1) ((d : ℝ) - 2) (by linarith) (by linarith)
    (by linarith) u y
  have hsplit : ∑ v, ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0) *
      bB d L W v y = (W : ℝ) * (W : ℝ) ^ (-2 : ℝ) *
        ∑ v, brk d L W u v ^ (-((d : ℝ) + 1)) * brk d L W v y ^ (-((d : ℝ) - 2)) +
          bB d L W u y := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [RenormDiff_bB_eq]; ring
  rw [hsplit]
  have hWW : (W : ℝ) * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + 1)) = 1 := by
    rw [show (d : ℝ) - ((d : ℝ) + 1) = -1 by ring, Real.rpow_neg_one, mul_inv_cancel₀ hW0.ne']
  have hB := RenormDiff_bB_eq (d := d) (L := L) (W := W) u y
  calc (W : ℝ) * (W : ℝ) ^ (-2 : ℝ) *
        ∑ v, brk d L W u v ^ (-((d : ℝ) + 1)) * brk d L W v y ^ (-((d : ℝ) - 2)) + bB d L W u y
      ≤ (W : ℝ) * (W : ℝ) ^ (-2 : ℝ) * (2 ^ ((d : ℝ) - 2) * brk d L W u y ^ (-((d : ℝ) - 2)) *
          (2 * ((W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + 1)) * (6 ^ d * logF L W)))) + bB d L W u y :=
        add_le_add (mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ (W : ℝ) * (W : ℝ) ^ (-2 : ℝ))) le_rfl
    _ = (2 ^ ((d : ℝ) - 2) * 2 * 6 ^ d * logF L W) *
          ((W : ℝ) ^ (-2 : ℝ) * brk d L W u y ^ (-((d : ℝ) - 2))) *
          ((W : ℝ) * (W : ℝ) ^ ((d : ℝ) - ((d : ℝ) + 1))) + bB d L W u y := by ring
    _ = _ := by rw [hWW, ← hB]; ring

/-- `Σ_u ⟨x - u⟩^{-d} W^{-4} ⟨u - y⟩^{-(d-4)} ≤ 2^{d-3} 6^d (log₂(L/W) + 2) W^{-4}
⟨x - y⟩^{-(d-4)}`. -/
private theorem RenormDiff_dBt (hd : 4 ≤ d) (hW : 1 ≤ W) (hWL : 2 * W ≤ L) (x y : Zd d L) :
    ∑ u, brk d L W x u ^ (-(d : ℝ)) * ((W : ℝ) ^ (-4 : ℝ) * brk d L W u y ^ (-((d : ℝ) - 4))) ≤
      (2 : ℝ) ^ ((d : ℝ) - 4) * 2 * 6 ^ d * logF L W *
        ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) := by
  have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hc := RenormDiff_conv hW hWL (d : ℝ) ((d : ℝ) - 4) (by linarith) (by linarith) le_rfl x y
  rw [sub_self, Real.rpow_zero, one_mul] at hc
  calc _ = (W : ℝ) ^ (-4 : ℝ) *
        ∑ u, brk d L W x u ^ (-(d : ℝ)) * brk d L W u y ^ (-((d : ℝ) - 4)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
    _ ≤ (W : ℝ) ^ (-4 : ℝ) * (2 ^ ((d : ℝ) - 4) * brk d L W x y ^ (-((d : ℝ) - 4)) *
          (2 * (6 ^ d * logF L W))) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end Conv

/-! ## The difference of two labelled chains -/

section ChainDiff

/-- `Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ` started from `X Y` is `X` times the chain started from `Y`. -/
private theorem RenormDiff_foldl {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (X Y : Matrix ι ι ℂ) (o : List ℕ) :
    o.foldl (fun M l => M * D.Sig l * D.Theta) (X * Y) =
      X * o.foldl (fun M l => M * D.Sig l * D.Theta) Y := by
  induction o generalizing Y with
  | nil => rfl
  | cons l o ih =>
    simp only [List.foldl_cons]
    rw [show X * Y * D.Sig l * D.Theta = X * (Y * D.Sig l * D.Theta) by
      simp only [Matrix.mul_assoc]]
    exact ih _

/-- `(Θ Σ_l Θ ⋯) = (Θ Σ_l) (Θ ⋯)`: the chain with label `l :: o` is `Θ Σ_l` times the chain with
label `o`. -/
private theorem RenormDiff_chain_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (l : ℕ) (o : List ℕ) : D.chain (l :: o) = (D.Theta * D.Sig l) * D.chain o := by
  unfold Data.chain
  rw [List.foldl_cons, ← RenormDiff_foldl]

/-- The scaling order of the label `l :: o`: `k(l :: o) - 2 = (l - 2) + (k(o) - 2)`. -/
private theorem RenormDiff_ord_cons (l : ℕ) (o : List ℕ) :
    ((((Kind.theta (l :: o)).ord : ℤ) : ℝ) - 2) =
      ((l : ℝ) - 2) + ((((Kind.theta o).ord : ℤ) : ℝ) - 2) := by
  simp only [Kind.ord, List.sum_cons, List.length_cons]
  push_cast
  ring

/-- `log₂(L/W) + 2 ≥ 0` for `1 ≤ W`, `2 W ≤ L`. -/
private theorem RenormDiff_logF_nonneg {L W : ℕ} (hW : 1 ≤ W) (hWL : 2 * W ≤ L) :
    0 ≤ logF L W := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hle : (W : ℝ) ≤ L := by
    have : W ≤ L := by omega
    exact_mod_cast this
  unfold logF
  have : 0 ≤ Real.logb 2 ((L : ℝ) / W) :=
    Real.logb_nonneg (by norm_num) ((one_le_div hW0).2 hle)
  linarith


/-- **The difference of two labelled chains** (the finite-volume form of the bound on
`Θ Σ̊_{o₁} Θ ⋯ Θ − Θ Σ_{o₁} Θ ⋯ Θ` in the proof of [I, Lemma 8.3]): for kernel families `K_A`,
`K_B` with [I, (1.25)–(1.27)] at the entries of `o`, whose difference at each entry `l` is at most
`η W^σ W^{-(l-2)d/2} (W ⟨u - v⟩^{-(d+1)} + 1_{u=v})`, the difference of the chains is at most
`η W^σ W^{-(k-2)d/2} W^{-4} ⟨x - y⟩^{-(d-4)}`, `k` the scaling order of the label. -/
private theorem RenormDiff_chainDiff (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (o : List ℕ)
    (hA : ∀ l ∈ o, KerSymm KA l ∧ KerBound KA l) (hB : ∀ l ∈ o, KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l ∈ o, ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
      W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x y : Zd d L,
        ‖(detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain o x y -
            (detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain o x y‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) := by
  induction o generalizing σ with
  | nil =>
    refine ⟨1, fun W L _ hadm hW z hz x y => ?_⟩
    rw [show (detData (Smat P.ψ W L) z fun l => KA l W L z).chain [] =
      (detData (Smat P.ψ W L) z fun l => KB l W L z).chain [] from rfl, sub_self, norm_zero]
    have hWn : 1 ≤ W := by exact_mod_cast hW
    have him := im_pos_of_specDom hWn hz
    have := RenormDiff_brk_pos (d := d) (L := L) hWn x y
    positivity
  | cons l o ih =>
    have hl : l ∈ l :: o := List.mem_cons_self
    have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
    set a : ℝ := σ / 5 with ha
    have ha0 : 0 < a := by positivity
    obtain ⟨W₁, hW₁⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KB [] (by simp) a ha0
    obtain ⟨W₂, hW₂⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KB o
      (fun l' h => hB l' (List.mem_cons_of_mem _ h)) a ha0
    obtain ⟨W₃, hW₃⟩ := thetaSigma d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA l (hA l hl).1
      (hA l hl).2 a ha0
    obtain ⟨W₄, hW₄⟩ := ih (fun l' h => hA l' (List.mem_cons_of_mem _ h))
      (fun l' h => hB l' (List.mem_cons_of_mem _ h)) (fun l' h => hΔ l' (List.mem_cons_of_mem _ h))
      a ha0
    obtain ⟨W₅, hW₅⟩ := hΔ l hl a ha0
    obtain ⟨W₆, hW₆⟩ := RenormDiff_logF_le (c₀ := c₀) hc₁ a ha0
    obtain ⟨W₇, hW₇⟩ := RenormDiff_two_le (c₁ := c₁) hc₀ (by linarith)
    obtain ⟨CB, hCB⟩ := bSum.2 d (by omega)
    set c₁' : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) * 2 * 6 ^ d with hc₁'
    set c₂' : ℝ := (2 : ℝ) ^ ((d : ℝ) - 4) * 2 * 6 ^ d with hc₂'
    set K : ℝ := (c₁' + 1) * max CB 0 + c₂' with hK
    refine ⟨max (max (max W₁ W₂) (max W₃ W₄)) (max (max W₅ W₆) (max (max W₇ 1)
      ((max K 1) ^ (1 / a)))), fun W L _ hadm hW z hz x y => ?_⟩
    have hWa := le_trans (le_max_left _ _) hW
    have hWb := le_trans (le_max_right _ _) hW
    have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWa)
    have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWa)
    have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWa)
    have hW4 : W₄ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hWa)
    have hW5 : W₅ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWb)
    have hW6 : W₆ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWb)
    have hW7 : W₇ ≤ W :=
      (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hWb))
    have hW1' : (1 : ℝ) ≤ W :=
      (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hWb))
    have hWK : (max K 1) ^ (1 / a) ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hWb)
    have hWn : 1 ≤ W := by exact_mod_cast hW1'
    have hW0 : (0 : ℝ) < W := by linarith
    have him := im_pos_of_specDom hWn hz
    have hWL := hW₇ W L hadm hW7
    have hlog := hW₆ W L hadm hW6
    have hlog0 : 0 ≤ logF L W := RenormDiff_logF_nonneg hWn hWL
    set η := z.im with hη
    set A : ℝ := (W : ℝ) ^ a with hA
    have hA1 : 1 ≤ A := Real.one_le_rpow hW1' ha0.le
    have hKA : K ≤ A := by
      calc K ≤ max K 1 := le_max_left _ _
        _ = ((max K 1) ^ (1 / a)) ^ a := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
        _ ≤ A := Real.rpow_le_rpow (by positivity) hWK ha0.le
    set lam : ℝ := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hlam
    set mu : ℝ := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hmu
    set Bt : Zd d L → Zd d L → ℝ := fun p q => (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4))
      with hBt
    have hlam0 : 0 ≤ lam := by positivity
    have hmu0 : 0 ≤ mu := by positivity
    have hBt0 : ∀ p q, 0 ≤ Bt p q := fun p q => by
      have := RenormDiff_brk_pos (d := d) (L := L) hWn p q
      simp only [hBt]; positivity
    have hB0 : ∀ p q, 0 ≤ bB d L W p q := fun p q => (bB_pos₁ hWn p q).le
    set T : Matrix (Zd d L) (Zd d L) ℂ := cmat (Theta (msc z) (Smat P.ψ W L)) with hT
    set cA := (detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain o with hcA
    set cB := (detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain o with hcB
    have hcons : (detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain (l :: o) -
        (detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain (l :: o) =
        T * (KA l W L z - KB l W L z) * cB + (T * KA l W L z) * (cA - cB) := by
      rw [RenormDiff_chain_cons, RenormDiff_chain_cons]
      change T * KA l W L z * cA - T * KB l W L z * cB = _
      noncomm_ring
    -- the entry bounds
    have hTh : ∀ p q, ‖T p q‖ ≤ A * bB d L W p q := by
      intro p q
      have h := hW₁ W L hadm hW1 z hz p q
      simpa [Data.chain, Kind.ord, detData] using h
    have hcB' : ∀ p q, ‖cB p q‖ ≤ A * mu * bB d L W p q := fun p q => hW₂ W L hadm hW2 z hz p q
    have hTS : ∀ p q, ‖(T * KA l W L z) p q‖ ≤ A * lam * brk d L W p q ^ (-(d : ℝ)) :=
      fun p q => hW₃ W L hadm hW3 z hz p q
    have hD : ∀ p q, ‖(cA - cB) p q‖ ≤ η * A * mu * Bt p q := fun p q => hW₄ W L hadm hW4 z hz p q
    have hΔ' : ∀ p q, ‖(KA l W L z - KB l W L z) p q‖ ≤ η * A * lam *
        ((W : ℝ) * brk d L W p q ^ (-((d : ℝ) + 1)) + if p = q then 1 else 0) :=
      fun p q => hW₅ W L hadm hW5 z hz p q
    -- the first term
    have hFB := RenormDiff_FB (d := d) (L := L) (W := W) (by omega) hWn hWL
    have hT1 : ‖(T * (KA l W L z - KB l W L z) * cB) x y‖ ≤
        η * A ^ 3 * lam * mu * (c₁' * logF L W + 1) * (max CB 0 * Bt x y) := by
      rw [Matrix.mul_assoc]
      refine (RenormDiff_norm_mul _ _ x y).trans ?_
      have hin : ∀ u, ‖((KA l W L z - KB l W L z) * cB) u y‖ ≤
          η * A ^ 2 * lam * mu * (c₁' * logF L W + 1) * bB d L W u y := by
        intro u
        refine (RenormDiff_norm_mul _ _ u y).trans ?_
        calc ∑ v, ‖(KA l W L z - KB l W L z) u v‖ * ‖cB v y‖
            ≤ ∑ v, (η * A * lam * ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) +
                if u = v then 1 else 0)) * (A * mu * bB d L W v y) := by
              refine Finset.sum_le_sum fun v _ => mul_le_mul (hΔ' u v) (hcB' v y)
                (norm_nonneg _) ?_
              have := RenormDiff_brk_pos (d := d) (L := L) hWn u v
              positivity
          _ = η * A ^ 2 * lam * mu * ∑ v, ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) +
                if u = v then 1 else 0) * bB d L W v y := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
          _ ≤ η * A ^ 2 * lam * mu * ((c₁' * logF L W + 1) * bB d L W u y) :=
              mul_le_mul_of_nonneg_left (hFB u y) (by positivity)
          _ = _ := by ring
      have hbs := hCB L W hWn x y
      calc ∑ u, ‖T x u‖ * ‖((KA l W L z - KB l W L z) * cB) u y‖
          ≤ ∑ u, (A * bB d L W x u) *
              (η * A ^ 2 * lam * mu * (c₁' * logF L W + 1) * bB d L W u y) :=
            Finset.sum_le_sum fun u _ => mul_le_mul (hTh x u) (hin u) (norm_nonneg _)
              (by have := hB0 x u; positivity)
        _ = η * A ^ 3 * lam * mu * (c₁' * logF L W + 1) *
              ∑ u, bB d L W x u * bB d L W u y := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
        _ ≤ η * A ^ 3 * lam * mu * (c₁' * logF L W + 1) * (max CB 0 * Bt x y) := by
            refine mul_le_mul_of_nonneg_left (hbs.trans ?_) (by positivity)
            have := hBt0 x y
            simp only [hBt] at this ⊢
            have h2 : 0 ≤ (W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4)) := this
            calc CB * (W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))
                = CB * ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) := by ring
              _ ≤ max CB 0 * ((W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 4))) :=
                  mul_le_mul_of_nonneg_right (le_max_left _ _) h2
    -- the second term
    have hT2 : ‖((T * KA l W L z) * (cA - cB)) x y‖ ≤ η * A ^ 2 * lam * mu * (c₂' * logF L W) *
        Bt x y := by
      refine (RenormDiff_norm_mul _ _ x y).trans ?_
      have hdb := RenormDiff_dBt (d := d) (L := L) (W := W) (by omega) hWn hWL x y
      calc ∑ u, ‖(T * KA l W L z) x u‖ * ‖(cA - cB) u y‖
          ≤ ∑ u, (A * lam * brk d L W x u ^ (-(d : ℝ))) * (η * A * mu * Bt u y) :=
            Finset.sum_le_sum fun u _ => mul_le_mul (hTS x u) (hD u y) (norm_nonneg _)
              (by have := RenormDiff_brk_pos (d := d) (L := L) hWn x u; positivity)
        _ = η * A ^ 2 * lam * mu * ∑ u, brk d L W x u ^ (-(d : ℝ)) *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W u y ^ (-((d : ℝ) - 4))) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hBt]; ring
        _ ≤ η * A ^ 2 * lam * mu * (c₂' * logF L W * Bt x y) :=
            mul_le_mul_of_nonneg_left hdb (by positivity)
        _ = _ := by ring
    have hCB0 : 0 ≤ max CB 0 := le_max_right _ _
    have hc₁0 : 0 ≤ c₁' := by positivity
    have hc₂0 : 0 ≤ c₂' := by positivity
    have hBxy := hBt0 x y
    have hηA : 0 ≤ η * lam * mu * Bt x y := by positivity
    have hA5 : A ^ 5 = (W : ℝ) ^ σ := by
      rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      congr 1; rw [ha]; push_cast; ring
    have hexp : (W : ℝ) ^ (-((((Kind.theta (l :: o)).ord : ℤ) : ℝ) - 2) * d / 2) = lam * mu := by
      rw [RenormDiff_ord_cons, hlam, hmu, ← Real.rpow_add hW0]
      congr 1; ring
    have hsum : ‖(T * (KA l W L z - KB l W L z) * cB) x y + ((T * KA l W L z) * (cA - cB)) x y‖ ≤
        η * A ^ 5 * lam * mu * Bt x y := by
      refine (norm_add_le _ _).trans ?_
      clear_value A K c₁' c₂' lam mu
      have e1 : c₁' * logF L W + 1 ≤ (c₁' + 1) * A := by
        have := mul_le_mul_of_nonneg_left hlog hc₁0
        linarith
      have e3' : A ≤ A * A := le_mul_of_one_le_right (by linarith) hA1
      have e3 : logF L W ≤ A * A := le_trans hlog e3'
      have e2 : c₂' * logF L W ≤ c₂' * (A * A) := mul_le_mul_of_nonneg_left e3 hc₂0
      have hA0 : 0 ≤ A := by linarith
      have hX : A ^ 3 * ((c₁' * logF L W + 1) * max CB 0) + A ^ 2 * (c₂' * logF L W) ≤
          A ^ 4 * A := by
        have h1 : A ^ 3 * ((c₁' * logF L W + 1) * max CB 0) ≤ A ^ 3 * ((c₁' + 1) * A * max CB 0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e1 hCB0) (by positivity)
        have h2 : A ^ 2 * (c₂' * logF L W) ≤ A ^ 2 * (c₂' * (A * A)) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
        have h3 : A ^ 3 * ((c₁' + 1) * A * max CB 0) + A ^ 2 * (c₂' * (A * A)) = A ^ 4 * K := by
          rw [hK]; ring
        have h4 : A ^ 4 * K ≤ A ^ 4 * A := mul_le_mul_of_nonneg_left hKA (by positivity)
        linarith
      calc _ ≤ η * A ^ 3 * lam * mu * (c₁' * logF L W + 1) * (max CB 0 * Bt x y) +
            η * A ^ 2 * lam * mu * (c₂' * logF L W) * Bt x y := add_le_add hT1 hT2
        _ = (η * lam * mu * Bt x y) * (A ^ 3 * ((c₁' * logF L W + 1) * max CB 0) +
              A ^ 2 * (c₂' * logF L W)) := by ring
        _ ≤ (η * lam * mu * Bt x y) * (A ^ 4 * A) := mul_le_mul_of_nonneg_left hX hηA
        _ = η * A ^ 5 * lam * mu * Bt x y := by ring
    have hentry := congrArg (fun M : Matrix (Zd d L) (Zd d L) ℂ => M x y) hcons
    simp only [Matrix.sub_apply, Matrix.add_apply] at hentry
    rw [hentry, hexp]
    refine hsum.trans (le_of_eq ?_)
    rw [hA5]
    ring

end ChainDiff

/-! ## Changing the `Θ` edges into auxiliary edges -/

section Aux

/-- Two components with the same ends and the same kind data read by `Graph.Normal` and
`Graph.DoublyConnected`. -/
private def RenormDiff_Same {V : Type*} (c c' : Comp V) : Prop :=
  c'.x = c.x ∧ c'.y = c.y ∧ c'.kind.joinsMol = c.kind.joinsMol ∧
    c'.kind.isDiffusive = c.kind.isDiffusive ∧ c'.kind.isBlue = c.kind.isBlue ∧
    c'.kind.isSolid = c.kind.isSolid ∧ (c'.kind = .dot ↔ c.kind = .dot) ∧
    (c'.kind = .xdot ↔ c.kind = .xdot)

variable {k n : ℕ}

private theorem RenormDiff_exists_iff (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i])
    (P : Comp (Atom k n) → Prop) (hP : ∀ c c', RenormDiff_Same c c' → (P c ↔ P c')) :
    (∃ c ∈ G₁.comps, P c) ↔ ∃ c ∈ G₂.comps, P c := by
  constructor
  · rintro ⟨c, hc, hpc⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    exact ⟨_, List.getElem_mem _, (hP _ _ (hs ⟨i, hi⟩)).1 hpc⟩
  · rintro ⟨c, hc, hpc⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
    have h := hs ⟨j, hlen ▸ hj⟩
    exact ⟨_, List.getElem_mem _, (hP _ _ h).2 hpc⟩

private theorem RenormDiff_forall_iff (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i])
    (P : Comp (Atom k n) → Prop) (hP : ∀ c c', RenormDiff_Same c c' → (P c ↔ P c')) :
    (∀ c ∈ G₁.comps, P c) ↔ ∀ c ∈ G₂.comps, P c := by
  have := RenormDiff_exists_iff G₁ G₂ hlen hs (fun c => ¬ P c) (fun c c' h => not_congr (hP c c' h))
  constructor
  · intro h c hc
    by_contra hn
    obtain ⟨c', hc', hn'⟩ := this.2 ⟨c, hc, hn⟩
    exact hn' (h c' hc')
  · intro h c hc
    by_contra hn
    obtain ⟨c', hc', hn'⟩ := this.1 ⟨c, hc, hn⟩
    exact hn' (h c' hc')

private theorem RenormDiff_edgeGraph_eq (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i]) :
    G₁.edgeGraph = G₂.edgeGraph := by
  ext u v
  simp only [Graph.edgeGraph, SimpleGraph.fromRel_adj]
  rw [RenormDiff_exists_iff G₁ G₂ hlen hs (fun c => c.x = u ∧ c.y = v)
      (fun c c' h => by rw [h.1, h.2.1]),
    RenormDiff_exists_iff G₁ G₂ hlen hs (fun c => c.x = v ∧ c.y = u)
      (fun c c' h => by rw [h.1, h.2.1])]

private theorem RenormDiff_wavedThetaGraph_eq (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i]) :
    G₁.wavedThetaGraph = G₂.wavedThetaGraph := by
  ext u v
  simp only [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
  have hP : ∀ (a b : Atom k n) (c c' : Comp (Atom k n)), RenormDiff_Same c c' →
      (((c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧ c.x = a ∧
        c.y = b) ↔
      ((c'.kind.joinsMol = true ∧ c'.kind ≠ .dot ∨ c'.kind.isDiffusive = true) ∧ c'.x = a ∧
        c'.y = b)) := by
    intro a b c c' h
    obtain ⟨hx, hy, hj, hdf, -, -, hd, -⟩ := h
    rw [hx, hy, hj, hdf, Ne, Ne, hd]
  rw [RenormDiff_exists_iff G₁ G₂ hlen hs _ (hP u v), RenormDiff_exists_iff G₁ G₂ hlen hs _ (hP v u)]

private theorem RenormDiff_molGraph_eq (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i]) :
    G₁.molGraph = G₂.molGraph := by
  ext u v
  simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
  have hP : ∀ (a b : Atom k n) (c c' : Comp (Atom k n)), RenormDiff_Same c c' →
      ((c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b) ↔
        (c'.kind.joinsMol = true ∧ c'.x = a ∧ c'.y = b)) := by
    intro a b c c' h
    rw [h.1, h.2.1, h.2.2.1]
  rw [RenormDiff_exists_iff G₁ G₂ hlen hs _ (hP u v), RenormDiff_exists_iff G₁ G₂ hlen hs _ (hP v u)]

private theorem RenormDiff_sameMol_iff (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i])
    (u v : Atom k n) : G₁.SameMol u v ↔ G₂.SameMol u v := by
  unfold Graph.SameMol
  rw [RenormDiff_molGraph_eq G₁ G₂ hlen hs]

/-- `Graph.Normal` and `Graph.DoublyConnected` are read from the ends and the kind data of the
components. -/
private theorem RenormDiff_transfer (G₁ G₂ : Graph k n)
    (hlen : G₁.comps.length = G₂.comps.length)
    (hs : ∀ i : Fin G₁.comps.length, RenormDiff_Same G₁.comps[i] G₂.comps[Fin.cast hlen i]) :
    (∀ C, G₁.Normal C → G₂.Normal C) ∧ (G₁.DoublyConnected → G₂.DoublyConnected) := by
  have hE := RenormDiff_edgeGraph_eq G₁ G₂ hlen hs
  have hWT := RenormDiff_wavedThetaGraph_eq G₁ G₂ hlen hs
  refine ⟨fun C hN => ?_, fun hDC => ?_⟩
  · obtain ⟨⟨hsize, hconn, hint, hdot⟩, hsol, hxs⟩ := hN
    refine ⟨⟨by rw [← hlen]; exact hsize, by rw [← hE]; exact hconn,
      fun a b => by rw [← hWT]; exact hint a b, ?_⟩, ?_, fun u v huv => ?_⟩
    · refine (RenormDiff_forall_iff G₁ G₂ hlen hs
        (fun c => c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
        (fun c c' h => by rw [h.1, h.2.1, h.2.2.2.2.2.2.1])).1 hdot
    · refine (RenormDiff_forall_iff G₁ G₂ hlen hs (fun c => c.kind.isSolid = true → c.x ≠ c.y)
        (fun c c' h => by rw [h.1, h.2.1, h.2.2.2.2.2.1])).1 hsol
    · have h := hxs u v huv
      rw [RenormDiff_exists_iff G₁ G₂ hlen hs
          (fun c => c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))
          (fun c c' h => by rw [h.1, h.2.1, h.2.2.2.2.2.2.2]),
        RenormDiff_exists_iff G₁ G₂ hlen hs
          (fun c => c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))
          (fun c c' h => by rw [h.1, h.2.1, h.2.2.2.2.2.1])] at h
      exact h
  · obtain ⟨bl, bu, hdisj, hbl, hbu, hsl, hsu⟩ := hDC
    have hinj : Function.Injective (Fin.cast hlen) := fun a b h => by simpa using h
    have hnet : ∀ B : Finset (Fin G₁.comps.length),
        G₂.net (B.map ⟨Fin.cast hlen, hinj⟩) = G₁.net B := by
      intro B
      ext a b
      simp only [Graph.net, SimpleGraph.fromRel_adj, RenormDiff_sameMol_iff G₁ G₂ hlen hs]
      have hP : ∀ a b : Fin n, (∃ i ∈ B.map ⟨Fin.cast hlen, hinj⟩, G₂.comps[i].x = Sum.inr a ∧
          G₂.comps[i].y = Sum.inr b) ↔
          ∃ i ∈ B, G₁.comps[i].x = Sum.inr a ∧ G₁.comps[i].y = Sum.inr b := by
        intro a b
        constructor
        · rintro ⟨i, hi, h1, h2⟩
          obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
          have h := hs j
          exact ⟨j, hj, h.1 ▸ h1, h.2.1 ▸ h2⟩
        · rintro ⟨j, hj, h1, h2⟩
          have h := hs j
          exact ⟨Fin.cast hlen j, Finset.mem_map_of_mem _ hj, h.1.symm ▸ h1, h.2.1.symm ▸ h2⟩
      rw [hP a b, hP b a]
    refine ⟨bl.map ⟨Fin.cast hlen, hinj⟩, bu.map ⟨Fin.cast hlen, hinj⟩,
      (Finset.disjoint_map _).2 hdisj, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      change G₂.comps[Fin.cast hlen j].kind.isDiffusive = true
      rw [(hs j).2.2.2.1]; exact hbl j hj
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      change G₂.comps[Fin.cast hlen j].kind.isDiffusive = true ∨
        G₂.comps[Fin.cast hlen j].kind.isBlue = true
      rw [(hs j).2.2.2.1, (hs j).2.2.2.2.1]; exact hbu j hj
    · unfold Graph.Spans; rw [hnet]; exact hsl
    · unfold Graph.Spans; rw [hnet]; exact hsu

/-- A `Θ` edge, with any label, changed into the diffusive auxiliary edge of index `i` and
scaling order `2` between the same atoms; the other components are kept. -/
private def RenormDiff_auxComp {V : Type*} (i : ℕ) (c : Comp V) : Comp V :=
  match c.kind with
  | .theta _ => ⟨.aux i 2 true, c.x, c.y, c.minor, c.label⟩
  | _ => c

/-- The graph whose `i`-th component is the `i`-th component of `Γ` with a `Θ` edge changed
into the auxiliary edge of index `i` (`RenormDiff_auxComp`). -/
private def RenormDiff_toAux {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨List.ofFn fun i : Fin Γ.comps.length => RenormDiff_auxComp i Γ.comps[i], Γ.coeff⟩

/-- The label of a `Θ` edge; `[]` for the other components. -/
private def RenormDiff_lab {V : Type*} (c : Comp V) : List ℕ :=
  match c.kind with
  | .theta o => o
  | _ => []

private theorem RenormDiff_auxComp_same {V : Type*} (i : ℕ) (c : Comp V) :
    RenormDiff_Same c (RenormDiff_auxComp i c) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ <;> simp [RenormDiff_Same, RenormDiff_auxComp, Kind.joinsMol, Kind.isDiffusive,
    Kind.isBlue, Kind.isSolid]

private theorem RenormDiff_auxComp_map {V W : Type*} (f : V → W) (i : ℕ) (c : Comp V) :
    (RenormDiff_auxComp i c).map f = RenormDiff_auxComp i (c.map f) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ <;> rfl

private theorem RenormDiff_auxComp_waved {V : Type*} (i : ℕ) (c : Comp V) (w : Wave)
    (h : c.kind = .waved w) : RenormDiff_auxComp i c = c := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  rfl

private theorem RenormDiff_auxComp_theta {V : Type*} (i : ℕ) (c : Comp V) (o : List ℕ)
    (h : c.kind = .theta o) : RenormDiff_auxComp i c = ⟨.aux i 2 true, c.x, c.y, c.minor, c.label⟩ := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  rfl

private theorem RenormDiff_lab_waved {V : Type*} (c : Comp V) (w : Wave)
    (h : c.kind = .waved w) : RenormDiff_lab c = [] := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  rfl

private theorem RenormDiff_lab_theta {V : Type*} (c : Comp V) (o : List ℕ)
    (h : c.kind = .theta o) : RenormDiff_lab c = o := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  rfl

/-- The internal form of `RenormDiff_toAux Γ` is normal regular and doubly connected when that of
`Γ` is. -/
private theorem RenormDiff_toAux_internal {k n C : ℕ} (Γ : Graph k n)
    (hN : Γ.internalize.Normal C) (hDC : Γ.internalize.DoublyConnected) :
    (RenormDiff_toAux Γ).internalize.Normal C ∧
      (RenormDiff_toAux Γ).internalize.DoublyConnected := by
  have hlen : Γ.internalize.comps.length = (RenormDiff_toAux Γ).internalize.comps.length := by
    simp [Graph.internalize, Graph.mapAtoms, RenormDiff_toAux]
  have hs : ∀ i : Fin Γ.internalize.comps.length, RenormDiff_Same Γ.internalize.comps[i]
      (RenormDiff_toAux Γ).internalize.comps[Fin.cast hlen i] := by
    intro i
    simp only [Graph.internalize, Graph.mapAtoms, RenormDiff_toAux, List.getElem_map,
      List.getElem_ofFn, Fin.getElem_fin]
    change RenormDiff_Same (List.map _ Γ.comps)[(i : ℕ)] _
    rw [List.getElem_map, RenormDiff_auxComp_map]
    exact RenormDiff_auxComp_same _ _
  obtain ⟨h1, h2⟩ := RenormDiff_transfer _ _ hlen hs
  exact ⟨h1 C hN, h2 hDC⟩

/-- The components of `RenormDiff_toAux Γ` are waved edges and diffusive auxiliary edges of
order `2` when those of `Γ` are waved and `Θ` edges without minor and label. -/
private theorem RenormDiff_toAux_isBKind {k n : ℕ} (Γ : Graph k n)
    (h : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o)) :
    (RenormDiff_toAux Γ).comps.all Comp.isBKind = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [RenormDiff_toAux, List.mem_ofFn] at hc
  obtain ⟨i, rfl⟩ := hc
  simp only [Fin.getElem_fin]
  have hmem : Γ.comps[(i : ℕ)] ∈ Γ.comps := List.getElem_mem _
  obtain ⟨hm, hl, hk⟩ := h _ hmem
  rcases hk with ⟨w, hw⟩ | ⟨o, ho⟩
  · rw [RenormDiff_auxComp_waved _ _ w hw]
    simp [Comp.isBKind, hm, hl, hw]
  · rw [RenormDiff_auxComp_theta _ _ o ho]
    simp [Comp.isBKind, hm, hl]

private theorem RenormDiff_filter_ofFn {α : Type*} (p : α → Bool) :
    ∀ (m : ℕ) (f : Fin m → α),
      ((List.ofFn f).filter p).length = ∑ i, if p (f i) then 1 else 0 := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
    intro f
    rw [List.ofFn_succ, List.filter_cons, Fin.sum_univ_succ, ← ih]
    split_ifs with h <;> simp [h]; omega

/-- In `RenormDiff_toAux Γ` exactly one component is the auxiliary edge of index `j`, when the
components of `Γ` are waved and `Θ` edges and the `j`-th one is a `Θ` edge. -/
private theorem RenormDiff_toAux_filter {k n : ℕ} (Γ : Graph k n)
    (h : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o)
    (j : Fin Γ.comps.length) (o : List ℕ) (hj : Γ.comps[j].kind = .theta o) :
    ((RenormDiff_toAux Γ).comps.filter fun c => decide (c.kind = .aux j 2 true)).length = 1 := by
  simp only [RenormDiff_toAux]
  rw [RenormDiff_filter_ofFn, Finset.sum_eq_single j]
  · rw [RenormDiff_auxComp_theta _ _ o hj]; simp
  · intro i _ hij
    have : (RenormDiff_auxComp (↑i) Γ.comps[(i : ℕ)]).kind ≠ .aux j 2 true := by
      have hmem : Γ.comps[(i : ℕ)] ∈ Γ.comps := List.getElem_mem _
      rcases h _ hmem with ⟨w, hw⟩ | ⟨o', ho'⟩
      · rw [RenormDiff_auxComp_waved _ _ w hw, hw]; simp
      · rw [RenormDiff_auxComp_theta _ _ o' ho']
        simp only [ne_eq, Kind.aux.injEq, not_and]
        intro h'; exact absurd (Fin.ext h') hij
    simp [this]
  · simp

end Aux

/-! ## Telescoping a product over the components -/

section Tele

/-- `Π aᵢ − Π bᵢ = Σ_j (Π_{i<j} aᵢ) (a_j − b_j) (Π_{i>j} bᵢ)`. -/
private theorem RenormDiff_telescope {R : Type*} [CommRing R] :
    ∀ (m : ℕ) (a b : Fin m → R), ∏ i, a i - ∏ i, b i =
      ∑ j, ∏ i, (if i < j then a i else if i = j then a i - b i else b i) := by
  intro m
  induction m with
  | zero => intro a b; simp
  | succ m ih =>
    intro a b
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h0 : ∏ i : Fin (m + 1), (if i < 0 then a i else if i = 0 then a i - b i else b i) =
        (a 0 - b 0) * ∏ i : Fin m, b i.succ := by
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_ne_zero, Fin.not_lt_zero]
    have hs : ∀ j : Fin m, ∏ i : Fin (m + 1),
        (if i < j.succ then a i else if i = j.succ then a i - b i else b i) =
        a 0 * ∏ i : Fin m, (if i < j then a i.succ else if i = j then a i.succ - b i.succ
          else b i.succ) := by
      intro j
      rw [Fin.prod_univ_succ]
      simp [Fin.succ_pos, Fin.succ_lt_succ_iff, Fin.succ_inj, (Fin.succ_ne_zero j).symm]
    rw [h0]
    simp_rw [hs]
    rw [← Finset.mul_sum, ← ih]
    ring

/-- Bounds `W₀` for finitely many statements combine into one. -/
private theorem RenormDiff_uniform {ι : Type*} [Fintype ι] {c₀ c₁ : ℝ}
    (R : ι → ∀ (W L : ℕ) [NeZero L], Prop)
    (h : ∀ i, ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → R i W L) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ i, R i W L := by
  choose f hf using h
  refine ⟨∑ i, |f i|, fun W L _ hadm hW i => hf i W L hadm ?_⟩
  exact (le_abs_self _).trans ((Finset.single_le_sum (f := fun j => |f j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)).trans hW)

/-- The term of a graph as a product over the indices of its components. -/
private theorem RenormDiff_term_eq {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (D : Data ι) (σ : Atom k n → ι) :
    Γ.term D σ = Γ.coeff.eval D.m * ∏ i : Fin Γ.comps.length, Comp.val D σ Γ.comps[i] := by
  unfold Graph.term
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- The absolute value of `RenormDiff_toAux Γ` as a product over the indices of the components
of `Γ`. -/
private theorem RenormDiff_absVal_toAux {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (D : Data ι) (e : Fin k → ι) :
    (RenormDiff_toAux Γ).absVal D e = ∑ s : Fin n → ι, ‖Γ.coeff.eval D.m‖ *
      ∏ i : Fin Γ.comps.length, ‖Comp.val D (Sum.elim e s) (RenormDiff_auxComp i Γ.comps[i])‖ := by
  unfold Graph.absVal
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [RenormDiff_toAux, List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-- The scaling order of `RenormDiff_toAux Γ`: every `Θ` edge of label `o` loses
`k(o) - 2`. -/
private theorem RenormDiff_ord_toAux {k n : ℕ} (Γ : Graph k n)
    (h : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o) :
    ((RenormDiff_toAux Γ).ord : ℝ) + ∑ i : Fin Γ.comps.length,
      ((((Kind.theta (RenormDiff_lab Γ.comps[i])).ord : ℤ) : ℝ) - 2) = (Γ.ord : ℝ) := by
  have hΓ : (Γ.ord : ℝ) = ∑ i : Fin Γ.comps.length, ((Γ.comps[i].kind.ord : ℤ) : ℝ) - 2 * n := by
    unfold Graph.ord
    rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
    push_cast
    simp only [Fin.getElem_fin]
  have hH : ((RenormDiff_toAux Γ).ord : ℝ) = ∑ i : Fin Γ.comps.length,
      (((RenormDiff_auxComp i Γ.comps[i]).kind.ord : ℤ) : ℝ) - 2 * n := by
    unfold Graph.ord
    simp only [RenormDiff_toAux, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    push_cast; ring
  rw [hΓ, hH]
  have hpt : ∀ i : Fin Γ.comps.length,
      (((RenormDiff_auxComp i Γ.comps[i]).kind.ord : ℤ) : ℝ) +
        ((((Kind.theta (RenormDiff_lab Γ.comps[i])).ord : ℤ) : ℝ) - 2) =
          ((Γ.comps[i].kind.ord : ℤ) : ℝ) := by
    intro i
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases h _ hmem with ⟨w, hw⟩ | ⟨o, ho⟩
    · rw [RenormDiff_auxComp_waved _ _ w hw, RenormDiff_lab_waved _ w hw, hw]
      simp [Kind.ord]
    · rw [RenormDiff_auxComp_theta _ _ o ho, RenormDiff_lab_theta _ o ho, ho]
      simp [Kind.ord]
  rw [← Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib]
  ring

end Tele

/-! ## One normal regular graph -/

section GraphAux

/-- The bounds on the labelled chains of finitely many labels with entries even in `[4, N]`, with
one `W₀`: `chain` for `K_A` and `K_B`, and `RenormDiff_chainDiff` for their difference. -/
private theorem RenormDiff_labBounds (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (N : ℕ)
    (hA : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KA l ∧ KerBound KA l)
    (hB : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    {ι : Type} [Fintype ι] (lab : ι → List ℕ) (hlab : ∀ i, ∀ l ∈ lab i, 4 ≤ l ∧ l ≤ N ∧ Even l) :
    ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ →
      W₀ ≤ W → ∀ i : ι, ∀ z ∈ specDom κ ε W L, ∀ p q : Zd d L,
        ‖(detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain (lab i) p q‖ ≤
            (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2) *
              bB d L W p q ∧
          ‖(detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain (lab i) p q‖ ≤
            (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2) *
              bB d L W p q ∧
          ‖(detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain (lab i) p q -
              (detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain (lab i) p q‖ ≤
            z.im * (W : ℝ) ^ σ *
              (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2) *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4))) := by
  intro σ hσ
  refine RenormDiff_uniform (c₀ := c₀) (c₁ := c₁) (fun i W L [NeZero L] =>
    ∀ z ∈ specDom κ ε W L, ∀ p q : Zd d L,
      ‖(detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain (lab i) p q‖ ≤
          (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2) *
            bB d L W p q ∧
        ‖(detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain (lab i) p q‖ ≤
          (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2) *
            bB d L W p q ∧
        ‖(detData (Smat P.ψ W L) z (fun l => KA l W L z)).chain (lab i) p q -
            (detData (Smat P.ψ W L) z (fun l => KB l W L z)).chain (lab i) p q‖ ≤
          z.im * (W : ℝ) ^ σ *
            (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)))) (fun i => ?_) |>.imp
    fun W₀ h W L _ hadm hW i z hz p q => h W L hadm hW i z hz p q
  have hAi : ∀ l ∈ lab i, KerSymm KA l ∧ KerBound KA l := fun l hl =>
    hA l (hlab i l hl).1 (hlab i l hl).2.1 (hlab i l hl).2.2
  have hBi : ∀ l ∈ lab i, KerSymm KB l ∧ KerBound KB l := fun l hl =>
    hB l (hlab i l hl).1 (hlab i l hl).2.1 (hlab i l hl).2.2
  obtain ⟨W₁, h₁⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA (lab i) hAi σ hσ
  obtain ⟨W₂, h₂⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KB (lab i) hBi σ hσ
  obtain ⟨W₃, h₃⟩ := RenormDiff_chainDiff d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB (lab i) hAi hBi
    (fun l hl => hΔ l (hlab i l hl).1 (hlab i l hl).2.1 (hlab i l hl).2.2) σ hσ
  exact ⟨max W₁ (max W₂ W₃), fun W L _ hadm hW z hz p q =>
    ⟨h₁ W L hadm ((le_max_left _ _).trans hW) z hz p q,
      h₂ W L hadm ((le_max_left _ _).trans ((le_max_right _ _).trans hW)) z hz p q,
      h₃ W L hadm ((le_max_right _ _).trans ((le_max_right _ _).trans hW)) z hz p q⟩⟩


/-- A waved edge has the same factor on every deterministic record of `S`, `z`. -/
private theorem RenormDiff_val_waved_eq {ι V : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (z : ℂ) (Ms Ms' : ℕ → Matrix ι ι ℂ) (σ : V → ι) (c : Comp V) (w : Wave)
    (h : c.kind = .waved w) : Comp.val (detData S z Ms) σ c = Comp.val (detData S z Ms') σ c := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  cases w <;> rfl

/-- A waved edge has the same factor on the auxiliary record. -/
private theorem RenormDiff_val_waved_aux {ι V : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (z : ℂ) (Ms M : ℕ → Matrix ι ι ℂ) (σ : V → ι) (c : Comp V) (w : Wave)
    (h : c.kind = .waved w) : Comp.val (detData S z Ms) σ c = Comp.val (auxData S z M) σ c := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  cases w <;> rfl

/-- The factor of a `Θ` edge of label `o` is the entry of the chain of `o`. -/
private theorem RenormDiff_val_theta {ι V : Type} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : V → ι) (c : Comp V) (o : List ℕ) (h : c.kind = .theta o) :
    Comp.val D σ c = D.chain o (σ c.x) (σ c.y) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  rfl

/-- The factor of the auxiliary edge of index `i` is the entry of the `i`-th matrix. -/
private theorem RenormDiff_val_aux {ι V : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (z : ℂ) (M : ℕ → Matrix ι ι ℂ) (σ : V → ι) (i : ℕ) (x y : V) (mi : List V)
    (lb : Option (PQ × V)) :
    Comp.val (auxData S z M) σ ⟨.aux i 2 true, x, y, mi, lb⟩ = M i (σ x) (σ y) := rfl

/-- **One graph of `Σ_n`, normal regular with `x`, `y` internal**: for a graph of waved and
labelled `Θ` edges (labels with entries even in `[4, N]`) whose internal form is normal regular
and doubly connected, the difference of its values on the records of two kernel families as in
`RenormDiff_chainDiff` is at most `η W^{-(n-4)d/2} W^{-6} ⟨x - y⟩^{-(2d-6-τ)}`, `n` its scaling
order: the product of the components is telescoped over the `Θ` edges, and each term is a graph of
[I, Cor 6.13] with one edge bounded by `η W^{-(k-2)d/2} B̃` (`detAuxTilde`). -/
private theorem RenormDiff_graphAux (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (N : ℕ)
    (hA : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KA l ∧ KerBound KA l)
    (hB : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    {m C : ℕ} (Γ : Graph 2 m) (hN : Γ.internalize.Normal C)
    (hDC : Γ.internalize.DoublyConnected)
    (hK : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x y : Zd d L,
        ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![x, y] -
            Γ.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![x, y]‖ ≤
          z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ)) := by
  classical
  set len := Γ.comps.length with hlen
  set H := RenormDiff_toAux Γ with hH
  have hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o := by
    intro c hc
    rcases (hK c hc).2.2 with h | ⟨o, ho, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, ho⟩
  obtain ⟨hHN, hHDC⟩ := RenormDiff_toAux_internal Γ hN hDC
  have hHB := RenormDiff_toAux_isBKind Γ fun c hc => ⟨(hK c hc).1, (hK c hc).2.1, hWT c hc⟩
  set lab : Fin len → List ℕ := fun i => RenormDiff_lab Γ.comps[i] with hlabdef
  have hlab : ∀ i : Fin len, ∀ l ∈ lab i, 4 ≤ l ∧ l ≤ N ∧ Even l := by
    intro i l hl
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases (hK _ hmem).2.2 with ⟨w, hw⟩ | ⟨o, ho, hok⟩
    · simp only [hlabdef, RenormDiff_lab_waved _ w hw] at hl
      exact absurd hl (List.not_mem_nil)
    · simp only [hlabdef, RenormDiff_lab_theta _ o ho] at hl
      simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        at hok
      obtain ⟨⟨h4, hN'⟩, h2⟩ := hok l hl
      exact ⟨h4, hN', Nat.even_iff.2 h2⟩
  -- the bounds on the labelled chains, uniformly in the components
  have hbd := RenormDiff_labBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB N hA hB hΔ lab hlab
  -- [I, Cor 6.13, (6.43)] for `RenormDiff_toAux Γ` with the marked edge `j`
  have hdet : ∀ j : Fin len, ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, (∃ o, Γ.comps[j].kind = .theta o) →
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ M : ℕ → Matrix (Zd d L) (Zd d L) ℂ,
          (∀ (j' : ℕ) (u v : Zd d L), j' ≠ j → ‖M j' u v‖ ≤ (W : ℝ) ^ τ' * bB d L W u v) →
          (∀ u v : Zd d L, ‖M j u v‖ ≤
            (W : ℝ) ^ τ' * ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) →
          ∀ x y : Zd d L, H.absVal (auxData (Smat P.ψ W L) z M) ![x, y] ≤
            (W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
    intro j
    by_cases hj : ∃ o, Γ.comps[j].kind = .theta o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨τ', hτ', W₀, h⟩ := detAuxTilde d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε m C H j
        hHN hHDC hHB (RenormDiff_toAux_filter Γ hWT j o ho) (τ / 2) (by positivity)
      exact ⟨τ', hτ', W₀, fun _ => h⟩
    · exact ⟨1, one_pos, 0, fun h => absurd h hj⟩
  choose τ' hτ' Wd hWd using hdet
  have hbdj : ∀ j : Fin len, ∃ W₀ : ℝ, _ := fun j => hbd (τ' j) (hτ' j)
  choose Wb hWb using hbdj
  refine ⟨∑ j, (|Wd j| + |Wb j|) + max 1 (((len : ℝ) + 1) ^ (2 / τ)),
    fun W L _ hadm hW z hz x y => ?_⟩
  have hsumW : ∑ j, (|Wd j| + |Wb j|) ≤ W - max 1 (((len : ℝ) + 1) ^ (2 / τ)) := by linarith
  have hsum0 : 0 ≤ ∑ j, (|Wd j| + |Wb j|) := Finset.sum_nonneg fun j _ => by positivity
  have hWj : ∀ j : Fin len, Wd j ≤ W ∧ Wb j ≤ W := by
    intro j
    have hle := Finset.single_le_sum (f := fun j => |Wd j| + |Wb j|)
      (fun j _ => by positivity) (Finset.mem_univ j)
    have h1 : 0 ≤ max 1 (((len : ℝ) + 1) ^ (2 / τ)) := by positivity
    constructor
    · have := le_abs_self (Wd j); have := abs_nonneg (Wb j); linarith
    · have := le_abs_self (Wb j); have := abs_nonneg (Wd j); linarith
  have hW1' : (1 : ℝ) ≤ W := by
    have := le_max_left 1 (((len : ℝ) + 1) ^ (2 / τ)); linarith
  have hWlen : ((len : ℝ) + 1) ^ (2 / τ) ≤ W := by
    have := le_max_right 1 (((len : ℝ) + 1) ^ (2 / τ)); linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hWn hz
  set η := z.im with hη
  set DA := detData (Smat P.ψ W L) z (fun l => KA l W L z) with hDA
  set DB := detData (Smat P.ψ W L) z (fun l => KB l W L z) with hDB
  set A : Fin len → Matrix (Zd d L) (Zd d L) ℂ := fun i => DA.chain (lab i) with hAdef
  set B : Fin len → Matrix (Zd d L) (Zd d L) ℂ := fun i => DB.chain (lab i) with hBdef
  set mu : Fin len → ℝ := fun i => (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2)
    with hmudef
  have hmu0 : ∀ i, 0 < mu i := fun i => Real.rpow_pos_of_pos hW0 _
  set lam : Fin len → Fin len → ℝ := fun j i => (if i = j then η else 1) * mu i with hlamdef
  have hlam0 : ∀ j i, 0 < lam j i := fun j i => by
    simp only [hlamdef]; split_ifs <;> [exact mul_pos him (hmu0 i); simpa using hmu0 i]
  set X : Fin len → Fin len → Matrix (Zd d L) (Zd d L) ℂ := fun j i =>
    if i < j then A i else if i = j then A i - B i else B i with hXdef
  set M : Fin len → ℕ → Matrix (Zd d L) (Zd d L) ℂ := fun j i' =>
    if h : i' < len then (((lam j ⟨i', h⟩)⁻¹ : ℝ) : ℂ) • X j ⟨i', h⟩ else 0 with hMdef
  have hS0 : Smat P.ψ W L = Smat P.ψ W L := rfl
  set e : Fin 2 → Zd d L := ![x, y] with he
  set coeff : ℂ := Γ.coeff.eval (msc z) with hcoeff
  set a : (Fin m → Zd d L) → Fin len → ℂ := fun s i => Comp.val DA (Sum.elim e s) Γ.comps[i]
    with hadef
  set b : (Fin m → Zd d L) → Fin len → ℂ := fun s i => Comp.val DB (Sum.elim e s) Γ.comps[i]
    with hbdef
  set mm : (Fin m → Zd d L) → Fin len → Fin len → ℂ := fun s j i =>
    if i < j then a s i else if i = j then a s i - b s i else b s i with hmmdef
  -- the telescoping identity
  have hval : Γ.val DA e - Γ.val DB e = ∑ s, coeff * ∑ j, ∏ i, mm s j i := by
    unfold Graph.val
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [RenormDiff_term_eq, RenormDiff_term_eq]
    change coeff * _ - coeff * _ = _
    rw [← mul_sub, RenormDiff_telescope]
  -- each term
  have hterm : ∀ j : Fin len, ∑ s, ‖coeff‖ * ∏ i, ‖mm s j i‖ ≤
      η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
    intro j
    have hb0 : 0 ≤ η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
      have := RenormDiff_brk_pos (d := d) (L := L) hWn x y; positivity
    have hjmem : Γ.comps[j] ∈ Γ.comps := List.getElem_mem _
    rcases hWT _ hjmem with ⟨w, hw⟩ | ⟨o, ho⟩
    · -- a waved edge: the factor `a_j - b_j` is `0`
      have hz0 : ∀ s, mm s j j = 0 := by
        intro s
        simp only [hmmdef, lt_irrefl, if_false, if_true, hadef, hbdef]
        rw [RenormDiff_val_waved_eq (Smat P.ψ W L) z _ _ _ _ w hw, sub_self]
      have : ∀ s, ∏ i, ‖mm s j i‖ = 0 := fun s =>
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz0 s, norm_zero])
      simp only [this, mul_zero, Finset.sum_const_zero]
      exact hb0
    · -- a `Θ` edge: the term is a graph of [I, Cor 6.13] with the marked edge `j`
      have hpt : ∀ s i, ‖mm s j i‖ = lam j i * ‖Comp.val (auxData (Smat P.ψ W L) z (M j))
          (Sum.elim e s) (RenormDiff_auxComp i Γ.comps[i])‖ := by
        intro s i
        have himem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
        rcases hWT _ himem with ⟨w', hw'⟩ | ⟨o', ho'⟩
        · have hij : i ≠ j := by
            rintro rfl; rw [hw'] at ho; cases ho
          have hlab0 : lab i = [] := RenormDiff_lab_waved _ w' hw'
          have hmu1 : mu i = 1 := by simp [hmudef, hlab0, Kind.ord]
          have hlam1 : lam j i = 1 := by simp [hlamdef, hij, hmu1]
          rw [RenormDiff_auxComp_waved _ _ w' hw', hlam1, one_mul]
          have hab : a s i = b s i := RenormDiff_val_waved_eq _ _ _ _ _ _ w' hw'
          have hva : a s i = Comp.val (auxData (Smat P.ψ W L) z (M j)) (Sum.elim e s)
              Γ.comps[i] := RenormDiff_val_waved_aux _ _ _ _ _ _ w' hw'
          simp only [hmmdef, hij, if_false]
          split_ifs
          · rw [hva]
          · rw [← hab, hva]
        · have hlabo : lab i = o' := RenormDiff_lab_theta _ o' ho'
          rw [RenormDiff_auxComp_theta _ _ o' ho', RenormDiff_val_aux]
          have hMji : M j i = (((lam j i)⁻¹ : ℝ) : ℂ) • X j i := by
            simp only [hMdef, dif_pos i.2]
          rw [hMji, Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (hlam0 j i)), ← mul_assoc, mul_inv_cancel₀ (hlam0 j i).ne',
            one_mul]
          have ha : a s i = A i (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y) := by
            simp only [hadef, hAdef]; rw [RenormDiff_val_theta _ _ _ o' ho', hlabo]
          have hb : b s i = B i (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y) := by
            simp only [hbdef, hBdef]; rw [RenormDiff_val_theta _ _ _ o' ho', hlabo]
          simp only [hmmdef, hXdef]
          split_ifs <;> simp [ha, hb, Matrix.sub_apply]
      have hsum : ∑ s, ‖coeff‖ * ∏ i, ‖mm s j i‖ =
          (∏ i, lam j i) * H.absVal (auxData (Smat P.ψ W L) z (M j)) e := by
        rw [RenormDiff_absVal_toAux, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp_rw [hpt s]
        rw [Finset.prod_mul_distrib]
        change _ = _ * (‖Γ.coeff.eval (msc z)‖ * _)
        ring
      have hprod : ∏ i, lam j i = η * ∏ i, mu i := by
        simp only [hlamdef]
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
        simp
      have hmuprod : (∏ i, mu i) * (W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2)) =
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) := by
        simp only [hmudef]
        rw [← Real.rpow_sum_of_pos hW0, ← Real.rpow_add hW0]
        have hord := RenormDiff_ord_toAux Γ hWT
        congr 1
        rw [← hord]
        have h' : ∀ i : Fin len, -((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2 =
            ((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * (-(d : ℝ) / 2) := fun i => by ring
        simp_rw [h', ← Finset.sum_mul]
        simp only [hlabdef]
        ring
      have hM1 : ∀ (j' : ℕ) (u v : Zd d L), j' ≠ j →
          ‖M j j' u v‖ ≤ (W : ℝ) ^ τ' j * bB d L W u v := by
        intro j' u v hj'
        by_cases h : j' < len
        · set i : Fin len := ⟨j', h⟩ with hi
          have hij : i ≠ j := fun h' => hj' (congrArg Fin.val h')
          have hMji : M j j' = (((lam j i)⁻¹ : ℝ) : ℂ) • X j i := by
            simp only [hMdef, dif_pos h]
            rfl
          have hlam : lam j i = mu i := by simp [hlamdef, hij]
          obtain ⟨hA', hB', -⟩ := hWb j W L hadm (hWj j).2 i z hz u v
          rw [hMji, Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (hlam0 j i)), hlam]
          have hX : ‖X j i u v‖ ≤ (W : ℝ) ^ τ' j * mu i * bB d L W u v := by
            simp only [hXdef]
            split_ifs with h1 h2 <;> first | exact hA' | exact hB' | exact absurd h2 hij
          have hmi := (hmu0 i).ne'
          calc (mu i)⁻¹ * ‖X j i u v‖ ≤ (mu i)⁻¹ * ((W : ℝ) ^ τ' j * mu i * bB d L W u v) :=
                mul_le_mul_of_nonneg_left hX (inv_nonneg.2 (hmu0 i).le)
            _ = _ := by field_simp
        · simp only [hMdef, h, dite_false, Matrix.zero_apply, norm_zero]
          exact mul_nonneg (by positivity) (bB_pos₁ hWn u v).le
      have hM2 : ∀ u v : Zd d L, ‖M j j u v‖ ≤
          (W : ℝ) ^ τ' j * ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4))) := by
        intro u v
        have hMjj : M j j = (((lam j j)⁻¹ : ℝ) : ℂ) • (A j - B j) := by
          simp [hMdef, hXdef]
        have hlam : lam j j = η * mu j := by simp [hlamdef]
        obtain ⟨-, -, hD'⟩ := hWb j W L hadm (hWj j).2 j z hz u v
        rw [hMjj, Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 (hlam0 j j)), hlam]
        have hD'' : ‖(A j - B j) u v‖ ≤ η * (W : ℝ) ^ τ' j * mu j *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4))) := hD'
        have hpos : 0 < η * mu j := mul_pos him (hmu0 j)
        have hmj := (hmu0 j).ne'
        have hηne := him.ne'
        calc (η * mu j)⁻¹ * ‖(A j - B j) u v‖ ≤ (η * mu j)⁻¹ * (η * (W : ℝ) ^ τ' j * mu j *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) :=
            mul_le_mul_of_nonneg_left hD'' (inv_nonneg.2 hpos.le)
          _ = _ := by field_simp
      have habs := hWd j ⟨o, ho⟩ W L hadm (hWj j).1 z hz (M j) hM1 hM2 x y
      rw [hsum, hprod]
      have hmu0' : 0 ≤ ∏ i, mu i := Finset.prod_nonneg fun i _ => (hmu0 i).le
      calc η * (∏ i, mu i) * H.absVal (auxData (Smat P.ψ W L) z (M j)) e
          ≤ η * (∏ i, mu i) * ((W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2))) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = η * ((∏ i, mu i) * (W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2))) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by ring
        _ = _ := by rw [hmuprod]
  -- the sum over the marked edges
  have hbrk := RenormDiff_brk_pos (d := d) (L := L) hWn x y
  have hlenτ : (len : ℝ) * brk d L W x y ^ (-(τ / 2)) ≤ 1 := by
    have h1 : brk d L W x y ^ (-(τ / 2)) ≤ (W : ℝ) ^ (-(τ / 2)) :=
      Real.rpow_le_rpow_of_nonpos hW0 (RenormDiff_le_brk x y) (by linarith)
    have h2 : ((len : ℝ) + 1) ≤ (W : ℝ) ^ (τ / 2) := by
      calc ((len : ℝ) + 1) = (((len : ℝ) + 1) ^ (2 / τ)) ^ (τ / 2) := by
            rw [← Real.rpow_mul (by positivity)]; field_simp; simp
        _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow (by positivity) hWlen (by positivity)
    have h3 : (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ (τ / 2) = 1 := by
      rw [← Real.rpow_add hW0]; simp
    have h4 : 0 ≤ (W : ℝ) ^ (-(τ / 2)) := by positivity
    calc (len : ℝ) * brk d L W x y ^ (-(τ / 2)) ≤ (len : ℝ) * (W : ℝ) ^ (-(τ / 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ((len : ℝ) + 1) * (W : ℝ) ^ (-(τ / 2)) := by nlinarith
      _ ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(τ / 2)) := mul_le_mul_of_nonneg_right h2 h4
      _ = 1 := by rw [mul_comm, h3]
  have hsplit : brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) =
      brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ)) * brk d L W x y ^ (-(τ / 2)) := by
    rw [← Real.rpow_add hbrk]; ring_nf
  rw [hval]
  calc ‖∑ s, coeff * ∑ j, ∏ i, mm s j i‖ ≤ ∑ s, ‖coeff‖ * ∑ j, ∏ i, ‖mm s j i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq
          (Finset.sum_congr rfl fun j _ => norm_prod _ _))) (norm_nonneg _)
    _ = ∑ j, ∑ s, ‖coeff‖ * ∏ i, ‖mm s j i‖ := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _j : Fin len, η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := Finset.sum_le_sum fun j _ => hterm j
    _ = (η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ))) *
            ((len : ℝ) * brk d L W x y ^ (-(τ / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsplit]; ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hlenτ

end GraphAux

/-! ## Diagonal graphs -/

section Diagonal

private theorem RenormDiff_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

/-- The factor of a dotted edge between `x` and `y` is `1(x = y)`. -/
private theorem RenormDiff_val_dot {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (D : Data ι)
    (s : Fin n → ι) (x y : ι) (c : Comp (Atom 2 n)) (hk : c.kind = .dot)
    (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0) :
    Comp.val D (Sum.elim ![x, y] s) c = if x = y then 1 else 0 := by
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_cases h : x = y <;> simp [Comp.val, h]
  · by_cases h : x = y
    · simp [Comp.val, h]
    · simp [Comp.val, Ne.symm h, h]

/-- A graph with a dotted edge between `x` and `y` has value `0` at `x ≠ y`. -/
private theorem RenormDiff_val_ne {n : ℕ} (Γ : Graph 2 n) (c : Comp (Atom 2 n)) (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) {x y : ι} (hne : x ≠ y) :
    Γ.val D ![x, y] = 0 := by
  unfold Graph.val Graph.term
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [List.prod_eq_zero, mul_zero]
  exact List.mem_map.2 ⟨c, hc, by rw [RenormDiff_val_dot D s x y c hk hxy]; simp [hne]⟩

private theorem RenormDiff_elim_cons {ι : Type*} {m : ℕ} (x b : ι) (s : Fin m → ι) :
    Sum.elim ![x, x] (Fin.cons (α := fun _ => ι) b s) = Sum.elim ![x, b] s ∘ Diag.atomMap m := by
  funext u
  rcases u with a | u
  · fin_cases a <;> rfl
  · refine Fin.cases ?_ (fun i => ?_) u
    · simp [Diag.atomMap]
    · simp [Diag.atomMap]

/-- If the `i`-th component of `Γ` is a dotted edge between `x` and `y`, then at `x = y` the value
of `Γ` is the sum over the label `b` of the former internal atom `0` of the value of
`Diag.graph Γ i` at `(x, b)`. -/
private theorem RenormDiff_val_diag {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ)
    (hi : i < Γ.comps.length) (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inl 0 ∧ Γ.comps[i].y = .inl 1 ∨
      Γ.comps[i].x = .inl 1 ∧ Γ.comps[i].y = .inl 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) (x : ι) :
    Γ.val D ![x, x] = ∑ b, (Diag.graph Γ i).val D ![x, b] := by
  have hperm := List.getElem_cons_eraseIdx_perm hi
  have hterm : ∀ s : Fin (m + 1) → ι,
      (Γ.comps.map fun c => Comp.val D (Sum.elim ![x, x] s) c).prod =
        ((Γ.comps.eraseIdx i).map fun c => Comp.val D (Sum.elim ![x, x] s) c).prod := by
    intro s
    rw [← (hperm.map _).prod_eq, List.map_cons, List.prod_cons,
      RenormDiff_val_dot D s x x _ hk hxy]
    simp
  unfold Graph.val Graph.term
  simp_rw [hterm]
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [Fin.consEquiv_apply]
  rw [RenormDiff_elim_cons]
  simp only [Diag.graph, List.map_map]
  congr 2
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, RenormDiff_val_map]

/-- **A diagonal graph with an internal atom** ([I, Def 2.13 (i)]): `x` and `y` are identified
and the former internal atom `0` becomes the second external atom (`Diag.graph`); the difference
of the values at `(x, x)` is the sum over that atom of `RenormDiff_graphAux`, at most
`η W^τ W^{-(n-2)d/2}`. -/
private theorem RenormDiff_diagSucc (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (N : ℕ)
    (hA : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KA l ∧ KerBound KA l)
    (hB : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot) (hD : G13.IsDiag Γ) (hDC : Γ.internalize.DoublyConnected)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x : Zd d L,
        ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![x, x] -
            Γ.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![x, x]‖ ≤
          z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hrest' : ∀ c ∈ Γ.comps.eraseIdx i,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := by
    intro c hc
    rcases (hrest c hc).2.2 with ⟨w, hw⟩ | ⟨o, ho, -⟩
    · rw [hw]; simp [Kind.isSolid]
    · rw [ho]; simp [Kind.isSolid]
  obtain ⟨hN, hDC'⟩ := Diag.internal Γ i hi hk hD hrest' hDC
  have hK' : ∀ c ∈ (Diag.graph Γ i).comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true) := by
    intro c hc
    simp only [Diag.graph, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨h1, h2, h3⟩ := hrest c' hc'
    refine ⟨by simp [Comp.map, h1], by simp [Comp.map, h2], ?_⟩
    exact h3
  set τ₁ : ℝ := min τ 1 / 3 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁1 : τ₁ ≤ 1 / 3 := by rw [hτ₁]; linarith [min_le_right τ 1]
  have hτ₁τ : 3 * τ₁ ≤ τ := by rw [hτ₁]; linarith [min_le_left τ 1]
  obtain ⟨W₁, h₁⟩ := RenormDiff_graphAux d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB N hA hB hΔ
    (Diag.graph Γ i) hN hDC' hK' τ₁ hτ₁0
  obtain ⟨W₂, h₂⟩ := RenormDiff_two_le (c₁ := c₁) hc₀ (by linarith)
  obtain ⟨W₃, h₃⟩ := RenormDiff_logF_le (c₀ := c₀) hc₁ τ₁ hτ₁0
  refine ⟨max (max W₁ W₂) (max W₃ (max 1 (((6 : ℝ) ^ d) ^ (1 / τ₁)))),
    fun W L _ hadm hW z hz x => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW4 : max 1 (((6 : ℝ) ^ d) ^ (1 / τ₁)) ≤ W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hW1' : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW4
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have hWL := h₂ W L hadm hW2
  have hlog := h₃ W L hadm hW3
  have hlog0 := RenormDiff_logF_nonneg hWn hWL
  have h6 : (6 : ℝ) ^ d ≤ (W : ℝ) ^ τ₁ := by
    calc (6 : ℝ) ^ d = (((6 : ℝ) ^ d) ^ (1 / τ₁)) ^ τ₁ := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ (W : ℝ) ^ τ₁ := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hW4)
          hτ₁0.le
  have him := im_pos_of_specDom hWn hz
  have hord : ((Diag.graph Γ i).ord : ℝ) = (Γ.ord : ℝ) := by rw [Diag.ord_eq Γ i hi hk]
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  rw [RenormDiff_val_diag Γ i hi hk hxy, RenormDiff_val_diag Γ i hi hk hxy,
    ← Finset.sum_sub_distrib]
  have htail := RenormDiff_tail hWn hWL (2 * (d : ℝ) - 6 - τ₁) (by linarith) x
  calc ‖∑ b, ((Diag.graph Γ i).val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![x, b] -
        (Diag.graph Γ i).val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![x, b])‖
      ≤ ∑ b, z.im * (W : ℝ) ^ (-((((Diag.graph Γ i).ord : ℝ) - 4) * d / 2)) *
          (W : ℝ) ^ (-6 : ℝ) * brk d L W x b ^ (-(2 * (d : ℝ) - 6 - τ₁)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => h₁ W L hadm hW1 z hz x b)
    _ = z.im * (W : ℝ) ^ (-((((Diag.graph Γ i).ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          ∑ b, brk d L W x b ^ (-(2 * (d : ℝ) - 6 - τ₁)) := by rw [Finset.mul_sum]
    _ ≤ z.im * (W : ℝ) ^ (-((((Diag.graph Γ i).ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          ((W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁)) * (6 ^ d * logF L W)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁))) * (6 ^ d * logF L W) := by
        rw [hord]; ring
    _ = z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ₁) *
          (6 ^ d * logF L W) := by
        congr 2
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        congr 1; ring
    _ ≤ z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ₁) *
          ((W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁) := by
        gcongr
    _ = z.im * (W : ℝ) ^ (3 * τ₁) * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
        rw [show 3 * τ₁ = τ₁ + τ₁ + τ₁ by ring, Real.rpow_add hW0, Real.rpow_add hW0]; ring
    _ ≤ _ := by
        gcongr

/-- The factor of a dotted edge. -/
private theorem RenormDiff_val_dotc {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : V → ι) (c : Comp V) (h : c.kind = .dot) :
    Comp.val D σ c = if σ c.x = σ c.y then 1 else 0 := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  rfl

/-- The factor of a waved edge on a deterministic record is an entry of `S`, `S⁺` or `S⁻`. -/
private theorem RenormDiff_norm_waved {ι V : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (z : ℂ) (M : ℕ → Matrix ι ι ℂ) (σ : V → ι) (c : Comp V) (w : Wave) (h : c.kind = .waved w)
    (t : ℝ) (h1 : ‖cmat S (σ c.x) (σ c.y)‖ ≤ t) (h2 : ‖Splus (msc z) S (σ c.x) (σ c.y)‖ ≤ t)
    (h3 : ‖Sminus (msc z) S (σ c.x) (σ c.y)‖ ≤ t) : ‖Comp.val (detData S z M) σ c‖ ≤ t := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at h
  subst h
  cases w
  · exact h1
  · exact h2
  · exact h3

/-- The three bounds on a `Θ` factor of a graph without internal atom. -/
private theorem RenormDiff_thetaFac {η A μ K Wd β βt : ℝ} {a b : ℂ} (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hμ : 0 ≤ μ) (hK : 1 ≤ K) (hβ : 0 ≤ β) (hβWd : β ≤ Wd) (hβt0 : 0 ≤ βt) (hβt : βt ≤ Wd)
    (h1 : ‖a‖ ≤ A * μ * β) (h2 : ‖b‖ ≤ A * μ * β) (h3 : ‖a - b‖ ≤ η * A * μ * βt) :
    ‖a‖ ≤ K * A * (μ * Wd) ∧ ‖b‖ ≤ K * A * (μ * Wd) ∧ ‖a - b‖ ≤ η * (K * A * (μ * Wd)) := by
  have hAμ : 0 ≤ A * μ := mul_nonneg hA hμ
  have hKA : A * μ ≤ K * (A * μ) := le_mul_of_one_le_left hAμ hK
  have e1 : A * μ * β ≤ K * A * (μ * Wd) := by
    calc A * μ * β ≤ K * (A * μ) * Wd := mul_le_mul hKA hβWd hβ (by positivity)
      _ = _ := by ring
  have e2 : η * A * μ * βt ≤ η * (K * A * (μ * Wd)) := by
    calc η * A * μ * βt = η * (A * μ * βt) := by ring
      _ ≤ η * (K * (A * μ) * Wd) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hKA hβt hβt0 (by positivity)) hη
      _ = _ := by ring
  exact ⟨h1.trans e1, h2.trans e1, h3.trans e2⟩

/-- **A diagonal graph without internal atom**: its value is a product of factors at the two
external atoms; telescoping over the components, each factor is at most
`K W^σ W^{-ord·d/2}` (`W^{-d}` for a waved edge, `B_{xy} ≤ W^{-d}` and `B̃_{xy} ≤ W^{-d}` for a
`Θ` edge), with `η` for the marked one, and the dotted edge is `1`; the difference is at most
`η W^τ W^{-(n-2)d/2}`. -/
private theorem RenormDiff_diagZero (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (N : ℕ)
    (hA : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KA l ∧ KerBound KA l)
    (hB : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    (Γ : Graph 2 0) (i₀ : ℕ) (hi₀ : i₀ < Γ.comps.length) (hk : Γ.comps[i₀].kind = .dot)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i₀, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x y : Zd d L,
        ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![x, y] -
            Γ.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![x, y]‖ ≤
          z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
  classical
  set len := Γ.comps.length with hlen
  set j₀ : Fin len := ⟨i₀, hi₀⟩ with hj₀
  have hother : ∀ i : Fin len, i ≠ j₀ → Γ.comps[i].minor = [] ∧ Γ.comps[i].label = none ∧
      ((∃ w, Γ.comps[i].kind = .waved w) ∨
        ∃ o, Γ.comps[i].kind = .theta o ∧ labelOK N o = true) := by
    intro i hi
    refine hrest _ (List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun h => hi (Fin.ext h), rfl⟩)
  set lab : Fin len → List ℕ := fun i => RenormDiff_lab Γ.comps[i] with hlabdef
  have hlab : ∀ i : Fin len, ∀ l ∈ lab i, 4 ≤ l ∧ l ≤ N ∧ Even l := by
    intro i l hl
    by_cases hi : i = j₀
    · subst hi
      have : lab j₀ = [] := by
        simp only [hlabdef]
        rcases h : Γ.comps[i₀] with ⟨κ', x', y', mi', lb'⟩
        have hk' : κ' = .dot := by rw [h] at hk; exact hk
        subst hk'
        rfl
      rw [this] at hl
      exact absurd hl List.not_mem_nil
    · rcases (hother i hi).2.2 with ⟨w, hw⟩ | ⟨o, ho, hok⟩
      · simp only [hlabdef, RenormDiff_lab_waved _ w hw] at hl
        exact absurd hl List.not_mem_nil
      · simp only [hlabdef, RenormDiff_lab_theta _ o ho] at hl
        simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at hok
        obtain ⟨⟨h4, hN'⟩, h2⟩ := hok l hl
        exact ⟨h4, hN', Nat.even_iff.2 h2⟩
  set σ₁ : ℝ := τ / (2 * ((len : ℝ) + 1)) with hσ₁
  have hσ₁0 : 0 < σ₁ := by positivity
  have hσ₁len : (len : ℝ) * σ₁ ≤ τ / 2 := by
    rw [hσ₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨W₁, h₁⟩ := RenormDiff_labBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB N hA hB hΔ
    lab hlab σ₁ hσ₁0
  obtain ⟨K, Ww, hK1, hw⟩ := wave_bound d (by omega) P c₀ c₁ κ hc₀ hc₁ hκ σ₁ hσ₁0
  obtain ⟨Cc, hCc0, hCc⟩ := coeff_bound κ hκ Γ.coeff
  set Q : ℝ := Cc * len * K ^ len + 1 with hQ
  refine ⟨max (max W₁ Ww) (max 1 (Q ^ (2 / τ))), fun W L _ hadm hW z hz x y => ?_⟩
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWw : Ww ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW1' : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hWQ : Q ^ (2 / τ) ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hWn hz
  set η := z.im with hη
  set DA := detData (Smat P.ψ W L) z (fun l => KA l W L z) with hDA
  set DB := detData (Smat P.ψ W L) z (fun l => KB l W L z) with hDB
  set σ : Atom 2 0 → Zd d L := Sum.elim ![x, y] (default : Fin 0 → Zd d L) with hσ
  set a : Fin len → ℂ := fun i => Comp.val DA σ Γ.comps[i] with hadef
  set b : Fin len → ℂ := fun i => Comp.val DB σ Γ.comps[i] with hbdef
  set e : Fin len → ℝ := fun i => (((Γ.comps[i].kind.ord : ℤ) : ℝ)) - if i = j₀ then 2 else 0
    with hedef
  set F : Fin len → ℝ := fun i => K * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(e i * d / 2)) with hFdef
  have hWσ : 1 ≤ (W : ℝ) ^ σ₁ := Real.one_le_rpow hW1' hσ₁0.le
  have hF0 : ∀ i, 0 ≤ F i := fun i => by simp only [hFdef]; positivity
  have hKW : ∀ t : ℝ, 0 ≤ t → (W : ℝ) ^ σ₁ * t ≤ K * (W : ℝ) ^ σ₁ * t := by
    intro t ht
    have h0 : 0 ≤ (W : ℝ) ^ σ₁ * t := by positivity
    calc (W : ℝ) ^ σ₁ * t = 1 * ((W : ℝ) ^ σ₁ * t) := (one_mul _).symm
      _ ≤ K * ((W : ℝ) ^ σ₁ * t) := mul_le_mul_of_nonneg_right hK1 h0
      _ = K * (W : ℝ) ^ σ₁ * t := by ring
  have hBd : ∀ p q : Zd d L, bB d L W p q ≤ (W : ℝ) ^ (-(d : ℝ)) :=
    fun p q => bB_le_rpow (by omega) hWn p q
  have hBt : ∀ p q : Zd d L, (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) ≤
      (W : ℝ) ^ (-(d : ℝ)) := by
    intro p q
    have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast (show 4 ≤ d by omega)
    calc (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4))
        ≤ (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hW0 (RenormDiff_le_brk p q)
            (by linarith)) (by positivity)
      _ = (W : ℝ) ^ (-(d : ℝ)) := by rw [← Real.rpow_add hW0]; ring_nf
  have hBt0 : ∀ p q : Zd d L, 0 ≤ (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) :=
    fun p q => mul_nonneg (Real.rpow_nonneg hW0.le _)
      (Real.rpow_nonneg (RenormDiff_brk_pos hWn p q).le _)
  -- the factor bounds
  have hfac : ∀ i : Fin len, ‖a i‖ ≤ F i ∧ ‖b i‖ ≤ F i ∧ ‖a i - b i‖ ≤ η * F i := by
    intro i
    by_cases hi : i = j₀
    · rw [hi]
      have hd0 : ∀ D : Data (Zd d L), ‖Comp.val D σ Γ.comps[i₀]‖ ≤ 1 := by
        intro D
        rw [RenormDiff_val_dotc D σ _ hk]
        split_ifs <;> simp
      have hab : a j₀ = b j₀ := by
        simp only [hadef, hbdef]
        change Comp.val DA σ Γ.comps[i₀] = Comp.val DB σ Γ.comps[i₀]
        rw [RenormDiff_val_dotc DA σ _ hk, RenormDiff_val_dotc DB σ _ hk]
      have hF1 : 1 ≤ F j₀ := by
        simp only [hFdef, hedef, if_true]
        have : (((Γ.comps[j₀].kind.ord : ℤ) : ℝ)) - 2 = 0 := by
          simp only [hj₀, Fin.getElem_fin, hk, Kind.ord]; norm_num
        rw [this, zero_mul, zero_div, neg_zero, Real.rpow_zero, mul_one]
        nlinarith
      refine ⟨(hd0 DA).trans hF1, (hd0 DB).trans hF1, ?_⟩
      rw [hab, sub_self, norm_zero]; exact mul_nonneg him.le (hF0 _)
    · rcases (hother i hi).2.2 with ⟨w, hw'⟩ | ⟨o, ho, -⟩
      · have he : e i = 2 := by
          simp only [hedef, hi, if_false, hw', Kind.ord]; norm_num
        have hFw : F i = K * (W : ℝ) ^ σ₁ * (W : ℝ) ^ (-(d : ℝ)) := by
          simp only [hFdef, he]; congr 2; ring
        have hab : a i = b i := RenormDiff_val_waved_eq _ _ _ _ _ _ w hw'
        have hwa : ‖a i‖ ≤ F i := by
          obtain ⟨hs, hp, hm⟩ := hw W L hadm hWw hWn z him hz.1 (σ Γ.comps[i].x) (σ Γ.comps[i].y)
          have key : K * (W : ℝ) ^ σ₁ * (bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y) *
              ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W (σ Γ.comps[i].x)
                (σ Γ.comps[i].y)))) ≤ F i := by
            rw [hFw]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y) * ((W : ℝ) ^ ((d : ℝ) / 2) *
                  Real.sqrt (bB d L W (σ Γ.comps[i].x) (σ Γ.comps[i].y)))
                ≤ (W : ℝ) ^ (-(d : ℝ)) * 1 := mul_le_mul (hBd _ _)
                  (rpow_mul_sqrt_bB_le (by omega) hWn _ _) (by positivity) (by positivity)
              _ = _ := mul_one _
          exact RenormDiff_norm_waved _ _ _ σ _ w hw' _ (hs.trans key) (hp.trans key)
            (hm.trans key)
        refine ⟨hwa, by rw [← hab]; exact hwa, ?_⟩
        rw [hab, sub_self, norm_zero]; exact mul_nonneg him.le (hF0 _)
      · have hlabo : lab i = o := RenormDiff_lab_theta _ o ho
        have he : e i = (((Kind.theta o).ord : ℤ) : ℝ) := by
          simp only [hedef, hi, if_false, ho, sub_zero]
        have hFt : F i = K * (W : ℝ) ^ σ₁ *
            ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) * (W : ℝ) ^ (-(d : ℝ))) := by
          simp only [hFdef, he]
          rw [← Real.rpow_add hW0]; congr 2; ring
        obtain ⟨h1, h2, h3⟩ := h₁ W L hadm hW1 i z hz (σ Γ.comps[i].x) (σ Γ.comps[i].y)
        rw [hlabo] at h1 h2 h3
        have ha : a i = DA.chain o (σ Γ.comps[i].x) (σ Γ.comps[i].y) :=
          RenormDiff_val_theta _ _ _ o ho
        have hb : b i = DB.chain o (σ Γ.comps[i].x) (σ Γ.comps[i].y) :=
          RenormDiff_val_theta _ _ _ o ho
        have hmu0 : 0 ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) := by positivity
        rw [ha, hb, hFt]
        exact RenormDiff_thetaFac him.le (Real.rpow_nonneg hW0.le _) hmu0 hK1
          (bB_pos₁ hWn _ _).le (hBd _ _) (hBt0 _ _) (hBt _ _) h1 h2 h3
  -- the telescoping identity
  have hvA : Γ.val DA ![x, y] = Γ.coeff.eval (msc z) * ∏ i, a i := by
    unfold Graph.val
    rw [Fintype.sum_unique, RenormDiff_term_eq]
    have e : ∀ s : Fin 0 → Zd d L, Sum.elim ![x, y] s = σ := fun s => by
      rw [hσ]; congr 1; exact Subsingleton.elim _ _
    simp only [e]
    rfl
  have hvB : Γ.val DB ![x, y] = Γ.coeff.eval (msc z) * ∏ i, b i := by
    unfold Graph.val
    rw [Fintype.sum_unique, RenormDiff_term_eq]
    have e : ∀ s : Fin 0 → Zd d L, Sum.elim ![x, y] s = σ := fun s => by
      rw [hσ]; congr 1; exact Subsingleton.elim _ _
    simp only [e]
    rfl
  have hval : Γ.val DA ![x, y] - Γ.val DB ![x, y] = Γ.coeff.eval (msc z) *
      ∑ j, ∏ i, (if i < j then a i else if i = j then a i - b i else b i) := by
    rw [hvA, hvB, ← mul_sub, RenormDiff_telescope]
  have hmm : ∀ j i, ‖(if i < j then a i else if i = j then a i - b i else b i)‖ ≤
      (if i = j then η else 1) * F i := by
    intro j i
    obtain ⟨h1, h2, h3⟩ := hfac i
    split_ifs with hij hij' <;> first
      | (rw [one_mul]; assumption)
      | exact absurd hij' (ne_of_lt hij)
      | exact h3
      | (rw [one_mul]; exact h2)
      | (rw [one_mul]; exact h1)
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
  have hFprod : ∏ i, F i = (K * (W : ℝ) ^ σ₁) ^ len * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
    simp only [hFdef]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.rpow_sum_of_pos hW0, hsumF]
  have hcoeff : ‖Γ.coeff.eval (msc z)‖ ≤ Cc := hCc z him hz.1 hz.2.2
  have hKpow : (K * (W : ℝ) ^ σ₁) ^ len ≤ K ^ len * (W : ℝ) ^ (τ / 2) := by
    rw [mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ σ₁), ← Real.rpow_mul hW0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1' ?_) (by positivity)
    rw [mul_comm]; exact hσ₁len
  have hQW : Q ≤ (W : ℝ) ^ (τ / 2) := by
    have hCK : 0 ≤ Cc * len * K ^ len := by
      have : 0 ≤ K := by linarith
      positivity
    have hQ1 : 1 ≤ Q := by rw [hQ]; linarith
    calc Q = (Q ^ (2 / τ)) ^ (τ / 2) := by
          rw [← Real.rpow_mul (by linarith)]; field_simp; simp
      _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow (by positivity) hWQ (by positivity)
  have hWτ : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hE0 : 0 ≤ (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by positivity
  rw [hval, norm_mul]
  calc ‖Γ.coeff.eval (msc z)‖ * ‖∑ j, ∏ i, (if i < j then a i else if i = j then a i - b i
        else b i)‖
      ≤ Cc * ∑ j : Fin len, η * ∏ i, F i := by
        refine mul_le_mul hcoeff ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
          (norm_nonneg _) hCc0
        rw [norm_prod, ← hprod j]
        exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hmm j i
    _ = η * ((Cc * len) * (K * (W : ℝ) ^ σ₁) ^ len) *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hFprod]; ring
    _ ≤ η * ((W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2)) *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ him.le) hE0
        calc Cc * len * (K * (W : ℝ) ^ σ₁) ^ len ≤ Cc * len * (K ^ len * (W : ℝ) ^ (τ / 2)) :=
              mul_le_mul_of_nonneg_left hKpow (by positivity)
          _ = (Cc * len * K ^ len) * (W : ℝ) ^ (τ / 2) := by ring
          _ ≤ Q * (W : ℝ) ^ (τ / 2) := mul_le_mul_of_nonneg_right (by rw [hQ]; linarith)
              (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hQW (by positivity)
    _ = _ := by rw [hWτ]

end Diagonal

/-! ## One graph of `Σ_n` -/

section OneGraph

/-- The kinds of a component of a deterministic graph. -/
private theorem RenormDiff_detKind {V : Type*} {N : ℕ} (c : Comp V) (h : c.isDetKind N = true) :
    c.minor = [] ∧ c.label = none ∧ ((∃ w, c.kind = .waved w) ∨
      (∃ o, c.kind = .theta o ∧ labelOK N o = true) ∨ c.kind = .dot ∨ c.kind = .xdot) := by
  rcases c with ⟨κ, x, y, mi, lb⟩
  simp only [Comp.isDetKind, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hm, hl⟩, hk⟩ := h
  refine ⟨hm, hl, ?_⟩
  cases κ <;> simp_all

/-- A graph with a `×`-dotted loop has value `0`. -/
private theorem RenormDiff_val_xdotLoop {n : ℕ} (Γ : Graph 2 n) (h : Renorm.HasXdotLoop Γ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin 2 → ι) : Γ.val D e = 0 := by
  obtain ⟨c, hc, hk, hxy⟩ := h
  unfold Graph.val Graph.term
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [List.prod_eq_zero, mul_zero]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk hxy
  simp [Comp.val]

/-- **One graph of `Σ_n`** with the shape of an `n`-th order self-energy: after
`G13.dotContract` it is normal regular with `x`, `y` internal (`RenormDiff_graphAux`), diagonal
(`RenormDiff_diagSucc`, `RenormDiff_diagZero`; only at `x = 0`), or has a `×`-dotted loop (value
`0`). -/
private theorem RenormDiff_graphDiff (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (n : ℕ)
    (hA : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → KerSymm KA l ∧ KerBound KA l)
    (hB : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    (g : Σ m, Graph 2 m) (hg : SelfEnergyShape n [g]) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x : Zd d L,
        ‖g.2.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![0, x] -
            g.2.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![0, x]‖ ≤
          z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
            (if x = 0 then z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0) := by
  obtain ⟨hsh, hval, hcase⟩ := Renorm.contr_spec n g hg
  suffices h : ∀ (G : Σ m, Graph 2 m), SelfEnergyShape n [G] →
      ((∃ C, G.2.internalize.Normal C) ∨ G13.IsDiag G.2) →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
          ‖G.2.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![0, x] -
              G.2.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![0, x]‖ ≤
            z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
              (if x = 0 then z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))
                else 0) by
    obtain ⟨W₀, h₀⟩ := h _ hsh hcase
    refine ⟨W₀, fun W L _ hadm hW z hz x => ?_⟩
    rw [← hval, ← hval]
    exact h₀ W L hadm hW z hz x
  rintro ⟨m, Γ⟩ hsh hcase
  obtain ⟨⟨C', hNo, hDA⟩, hK, hO, hDC⟩ := hsh ⟨m, Γ⟩ (List.mem_singleton_self _)
  have hK : Γ.comps.all (Comp.isDetKind (n - 1)) = true := hK
  have hO : Γ.ord = (n : ℤ) := hO
  have hDC : Γ.internalize.DoublyConnected := hDC
  have hordR : (Γ.ord : ℝ) = n := by rw [hO]; simp
  have hKc : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧ ((∃ w, c.kind = .waved w) ∨
      (∃ o, c.kind = .theta o ∧ labelOK (n - 1) o = true) ∨ c.kind = .dot ∨ c.kind = .xdot) :=
    fun c hc => RenormDiff_detKind c (List.all_eq_true.1 hK c hc)
  -- the nonnegative right-hand side
  have hR0 : ∀ (W L : ℕ) [NeZero L], 1 ≤ W → ∀ z : ℂ, 0 < z.im → ∀ x : Zd d L,
      0 ≤ z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
        (if x = 0 then z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0) := by
    intro W L _ hW z hz x
    have := RenormDiff_brk_pos (d := d) (L := L) hW 0 x
    have h1 : 0 ≤ (if x = 0 then z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))
        else 0) := by split_ifs <;> positivity
    positivity
  by_cases hX : Renorm.HasXdotLoop Γ
  · refine ⟨1, fun W L _ hadm hW z hz x => ?_⟩
    have hWn : 1 ≤ W := by exact_mod_cast hW
    simp only
    rw [RenormDiff_val_xdotLoop Γ hX, RenormDiff_val_xdotLoop Γ hX, sub_self, norm_zero]
    exact hR0 W L hWn z (im_pos_of_specDom hWn hz) x
  -- no `×`-dotted edge at all
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
      have hmem : c.map (Sum.elim (fun a => Sum.inr (Fin.castAdd m a))
          (fun b => Sum.inr (Fin.natAdd 2 b))) ∈ Γ.internalize.comps :=
        List.mem_map.2 ⟨c, hc, rfl⟩
      have := hN.1.noIntDot _ hmem hk
      rcases c with ⟨κ, a, b, mi, lb⟩
      rcases a with a | a <;> rcases b with b | b <;> simp [Comp.map] at this
    have hK' : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
        ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK (n - 1) o = true) := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := hKc c hc
      refine ⟨h1, h2, ?_⟩
      rcases h3 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hnod c hc)
      · exact absurd h (hnox c hc)
    obtain ⟨W₀, h₀⟩ := RenormDiff_graphAux d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB (n - 1) hA hB
      hΔ Γ hN hDC hK' τ hτ
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz x => ?_⟩
    have hWn : 1 ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
    have h1 := h₀ W L hadm ((le_max_left _ _).trans hW) z hz 0 x
    rw [hordR] at h1
    have h2 : 0 ≤ (if x = 0 then z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))
        else 0) := by
      have := im_pos_of_specDom hWn hz
      split_ifs <;> positivity
    exact h1.trans (le_add_of_nonneg_right h2)
  · -- diagonal
    obtain ⟨i, hi, hdot, hrest⟩ := Diag.dot_unique Γ hD hDA
    have hxy := hD.2 _ (List.getElem_mem hi) hdot
    have hrest' : ∀ c ∈ Γ.comps.eraseIdx i, c.minor = [] ∧ c.label = none ∧
        ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK (n - 1) o = true) := by
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
          ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![0, 0] -
              Γ.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![0, 0]‖ ≤
            z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := by
      cases m with
      | zero =>
        obtain ⟨W₀, h₀⟩ := RenormDiff_diagZero d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB (n - 1)
          hA hB hΔ Γ i hi hdot hrest' τ hτ
        exact ⟨W₀, fun W L _ hadm hW z hz => by
          have := h₀ W L hadm hW z hz 0 0
          rwa [hordR] at this⟩
      | succ m =>
        obtain ⟨W₀, h₀⟩ := RenormDiff_diagSucc d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB (n - 1)
          hA hB hΔ Γ i hi hdot hD hDC hrest' τ hτ
        exact ⟨W₀, fun W L _ hadm hW z hz => by
          have := h₀ W L hadm hW z hz 0
          rwa [hordR] at this⟩
    obtain ⟨W₀, h₀⟩ := hdiag
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz x => ?_⟩
    have hWn : 1 ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
    have him := im_pos_of_specDom hWn hz
    have hmain0 : 0 ≤ z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by
      have := RenormDiff_brk_pos (d := d) (L := L) hWn 0 x
      positivity
    by_cases hx : x = 0
    · subst hx
      simp only [if_true]
      exact (h₀ W L hadm ((le_max_left _ _).trans hW) z hz).trans (le_add_of_nonneg_left hmain0)
    · rw [RenormDiff_val_ne Γ _ (List.getElem_mem hi) hdot hxy _ (Ne.symm hx),
        RenormDiff_val_ne Γ _ (List.getElem_mem hi) hdot hxy _ (Ne.symm hx), sub_self, norm_zero]
      exact hR0 W L hWn z him x

end OneGraph

/-! ## The bound on `Σ̊_l − Σ_l` -/

section Delta

/-- [I, (1.8)] in the form used for `Σ̊_l − Σ_l`: `|S_{uv}| ≤ C W ⟨u - v⟩^{-(d+1)}` on
`adm(c₀, c₁)` (`subpoly_adm` with `k = d + 1` and `k = 0`). -/
private theorem RenormDiff_S_bound {d : ℕ} (P : Profile d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → 1 ≤ W → ∀ u v : Zd d L,
      |Smat P.ψ W L u v| ≤ C * (W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) := by
  obtain ⟨C₁, hC₁⟩ := subpoly_adm d P c₀ c₁ hc₀ (d + 1)
  obtain ⟨C₀, hC₀⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  refine ⟨2 ^ (d + 1) * (max C₀ 0 + max C₁ 0), by positivity, fun W L _ hadm hW u v => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set r : ℝ := (zdistInf d L (u - v) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  set f : ℝ := |fWL P.ψ W L (u - v)| with hf
  have hf0 : 0 ≤ f := abs_nonneg _
  have h1 := hC₁ W L hadm (u - v)
  have h0 := hC₀ W L hadm (u - v)
  simp only [pow_zero, one_mul] at h0
  change (r / W) ^ (d + 1) * f ≤ C₁ / (W : ℝ) ^ d at h1
  change f ≤ C₀ / (W : ℝ) ^ d at h0
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  -- `f (r + W)^{d+1} ≤ 2^{d+1} (C₀ + C₁) W`
  have hpow : (r + W) ^ (d + 1) ≤ 2 ^ (d + 1) * (r ^ (d + 1) + (W : ℝ) ^ (d + 1)) := by
    rcases le_total r W with h | h
    · calc (r + W) ^ (d + 1) ≤ (2 * (W : ℝ)) ^ (d + 1) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 2 ^ (d + 1) * (W : ℝ) ^ (d + 1) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by have := pow_nonneg hr0 (d + 1); linarith)
            (by positivity)
    · calc (r + W) ^ (d + 1) ≤ (2 * r) ^ (d + 1) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 2 ^ (d + 1) * r ^ (d + 1) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (by have := pow_nonneg hW0.le (d + 1); linarith)
            (by positivity)
  have hfr : f * r ^ (d + 1) ≤ max C₁ 0 * W := by
    have e : (r / W) ^ (d + 1) * f * (W : ℝ) ^ (d + 1) = f * r ^ (d + 1) := by
      rw [div_pow]; field_simp
    rw [← e]
    calc (r / W) ^ (d + 1) * f * (W : ℝ) ^ (d + 1) ≤ C₁ / (W : ℝ) ^ d * (W : ℝ) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C₁ * W := by rw [pow_succ]; field_simp
      _ ≤ max C₁ 0 * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le
  have hfW : f * (W : ℝ) ^ (d + 1) ≤ max C₀ 0 * W := by
    calc f * (W : ℝ) ^ (d + 1) ≤ C₀ / (W : ℝ) ^ d * (W : ℝ) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right h0 (by positivity)
      _ = C₀ * W := by rw [pow_succ]; field_simp
      _ ≤ max C₀ 0 * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le
  have hkey : f * (r + W) ^ (d + 1) ≤ 2 ^ (d + 1) * (max C₀ 0 + max C₁ 0) * W := by
    calc f * (r + W) ^ (d + 1) ≤ f * (2 ^ (d + 1) * (r ^ (d + 1) + (W : ℝ) ^ (d + 1))) :=
          mul_le_mul_of_nonneg_left hpow hf0
      _ = 2 ^ (d + 1) * (f * r ^ (d + 1) + f * (W : ℝ) ^ (d + 1)) := by ring
      _ ≤ 2 ^ (d + 1) * (max C₁ 0 * W + max C₀ 0 * W) := by gcongr
      _ = _ := by ring
  have hb : brk d L W u v = r + W := rfl
  have hbpos : 0 < r + W := by linarith
  change f ≤ _
  rw [hb, show (-((d : ℝ) + 1)) = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg hbpos.le,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact hkey

/-- The two bounds of [I, Lemma 8.3] at order `n`, (8.4) with the term at `x = 0` and (8.5), with
the quantifiers of `SelfEnergyBound`. -/
private def RenormDiff_claim (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (n : ℕ) : Prop :=
  ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L,
        (∀ x : Zd d L,
          ‖sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x -
              sigMat Sig (smatVar P W L) z n 0 x‖ ≤
            z.im * (W : ℝ) ^ (-((n : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
                brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
              (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))
                else 0)) ∧
        ‖∑ x, sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x -
            ∑ x, sigMat Sig (smatVar P W L) z n 0 x‖ ≤
          (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))

/-- On `adm(c₀, c₁)` with `W ≥ 1`: `W ≤ L` and `L^t ≤ W^{t/c₁}` for `t ≥ 0`. -/
private theorem RenormDiff_adm_LW {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) (t : ℝ) (ht : 0 ≤ t) :
    (W : ℝ) ≤ L ∧ (L : ℝ) ^ t ≤ (W : ℝ) ^ (t / c₁) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨hadm.2.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)).trans_eq
    (Real.rpow_one _)), ?_⟩
  calc (L : ℝ) ^ t = ((L : ℝ) ^ c₁) ^ (t / c₁) := by
        rw [← Real.rpow_mul (by positivity)]; congr 1; field_simp
    _ ≤ (W : ℝ) ^ (t / c₁) := Real.rpow_le_rpow (by positivity) hadm.1 (by positivity)

/-- **`Σ̊_l − Σ_l`** in the proof of [I, Lemma 8.3]: from (8.4)–(8.5) at order `l` and [I, (1.27)]
for `Σ_l`, `|Σ̊_l(u, v) − Σ_l(u, v)| ≤ η W^σ W^{-(l-2)d/2} (W ⟨u - v⟩^{-(d+1)} + 1_{u=v})`:
`Σ̊_l − Σ_l = (Σ^{(r)}_l − Σ_l) − c_l S` ([I, (8.3)]) with
`|c_l| ≤ |Σ_x Σ_l(0, x)| + |Σ_x (Σ^{(r)}_l − Σ_l)(0, x)| ≤ 2 L^τ η W^{-(l-2)d/2}`, the term at
`x = 0` of (8.4) kept apart, and `|S_{uv}| ≲ W ⟨u - v⟩^{-(d+1)}` ([I, (1.8)]). -/
private theorem RenormDiff_delta (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2)
    (l : ℕ) (hcl : RenormDiff_claim d P Sig l) (hbd : SelfEnergyBound d (smatVar P) Sig l)
    (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ)
    (hε : 0 < ε) :
    ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖sigKer (smatVar P) (Renorm.sig Sig) l W L z u v - sigKer (smatVar P) Sig l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0) := by
  intro σ hσ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set τ : ℝ := min 1 (c₁ * σ / 4) with hτdef
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτc : τ ≤ c₁ * σ / 4 := min_le_right _ _
  have hτc' : τ / c₁ ≤ σ / 4 := by rw [div_le_iff₀ hc₁]; linarith
  have hτσ : τ ≤ σ / 4 := by
    have : c₁ * σ / 4 ≤ σ / 4 := by
      have : c₁ ≤ 1 := by linarith
      nlinarith
    linarith
  obtain ⟨L₁, hL₁⟩ := hcl κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ0
  obtain ⟨L₂, hL₂⟩ := hbd κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ0
  obtain ⟨CS, hCS0, hCS⟩ := RenormDiff_S_bound P c₀ c₁ hc₀
  obtain ⟨W₃, hW₃⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  set Kc : ℝ := 1 + 2 * CS with hKc
  refine ⟨max (max (L₁ : ℝ) (L₂ : ℝ)) (max W₃ (max 1 (Kc ^ (2 / σ)))),
    fun W L _ hadm hW z hz u v => ?_⟩
  have hWa := (le_max_left _ _).trans hW
  have hWb := (le_max_right _ _).trans hW
  have hW1' : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWb)
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hWn hz
  obtain ⟨hWL, hLτ⟩ := RenormDiff_adm_LW hc₀ hc₁ hadm τ hτ0.le
  have hL1 : L₁ ≤ L := by
    have : (L₁ : ℝ) ≤ L := ((le_max_left _ _).trans hWa).trans hWL
    exact_mod_cast this
  have hL2 : L₂ ≤ L := by
    have : (L₂ : ℝ) ≤ L := ((le_max_right _ _).trans hWa).trans hWL
    exact_mod_cast this
  have hS : smatVar P W L = Smat P.ψ W L := hW₃ W L hadm ((le_max_left _ _).trans hWb)
  set η := z.im with hη
  set lam : ℝ := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hlam
  set R : Matrix (Zd d L) (Zd d L) ℂ :=
    sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l with hR
  set Sg : Matrix (Zd d L) (Zd d L) ℂ := sigMat Sig (smatVar P W L) z l with hSg
  obtain ⟨hT3, hT4⟩ := hL₁ W L hL1 hadm z hz
  have h127 := (hL₂ W L hL2 hadm z hz).2
  -- the value identity [I, (8.3)] and translation invariance
  have hid : sigKer (smatVar P) (Renorm.sig Sig) l W L z u v - sigKer (smatVar P) Sig l W L z u v =
      (R 0 (v - u) - Sg 0 (v - u)) - (∑ w, R 0 w) * (smatVar P W L u v : ℂ) := by
    change sigMat (Renorm.sig Sig) (smatVar P W L) z l u v - Sg u v = _
    rw [Renorm.sigMat_smatVar P Sig l W L z him u v]
    have h1 := (selfEnergySymm_smatVar d P (Function.update (Renorm.sig Sig) l (Sig l)) l W L z
      him u (v - u)).1
    have h2 := (selfEnergySymm_smatVar d P Sig l W L z him u (v - u)).1
    rw [add_sub_cancel] at h1 h2
    have h1' : R u v = R 0 (v - u) := h1
    have h2' : Sg u v = Sg 0 (v - u) := h2
    change R u v - (∑ w, R 0 w) * _ - Sg u v = _
    rw [h1', h2']
    ring
  -- the bounds
  have hbrk : brk d L W 0 (v - u) = brk d L W u v := by
    unfold brk; rw [zero_sub, neg_sub]
  have hb := RenormDiff_brk_pos (d := d) (L := L) hWn u v
  have hmain : (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
      brk d L W u v ^ (-(2 * (d : ℝ) - 6 - τ)) ≤
      lam * (W : ℝ) ^ τ * ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1))) := by
    have e1 : brk d L W u v ^ (-(2 * (d : ℝ) - 6 - τ)) =
        brk d L W u v ^ (-((d : ℝ) + 1)) * brk d L W u v ^ (-((d : ℝ) - 7 - τ)) := by
      rw [← Real.rpow_add hb]; ring_nf
    have e2 : brk d L W u v ^ (-((d : ℝ) - 7 - τ)) ≤ (W : ℝ) ^ (-((d : ℝ) - 7 - τ)) :=
      Real.rpow_le_rpow_of_nonpos hW0 (RenormDiff_le_brk u v) (by linarith)
    have e3 : (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
        (W : ℝ) ^ (-((d : ℝ) - 7 - τ)) = lam * (W : ℝ) ^ τ * (W : ℝ) := by
      have hr : lam * (W : ℝ) ^ τ * (W : ℝ) = (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2) + τ + 1) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
      rw [hr, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      congr 1; ring
    rw [e1]
    calc (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
          (brk d L W u v ^ (-((d : ℝ) + 1)) * brk d L W u v ^ (-((d : ℝ) - 7 - τ)))
        ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
          (brk d L W u v ^ (-((d : ℝ) + 1)) * (W : ℝ) ^ (-((d : ℝ) - 7 - τ))) := by gcongr
      _ = (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
          (W : ℝ) ^ (-((d : ℝ) - 7 - τ)) * brk d L W u v ^ (-((d : ℝ) + 1)) := by ring
      _ = _ := by rw [e3]; ring
  have hT3' := hT3 (v - u)
  rw [hbrk] at hT3'
  have hc : ‖∑ w, R 0 w‖ ≤ 2 * ((L : ℝ) ^ τ * η * lam) := by
    have : ∑ w, R 0 w = (∑ w, R 0 w - ∑ w, Sg 0 w) + ∑ w, Sg 0 w := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ w, R 0 w - ∑ w, Sg 0 w‖ ≤ (L : ℝ) ^ τ * η * lam := hT4
    have h2 : ‖∑ w, Sg 0 w‖ ≤ (L : ℝ) ^ τ * η * lam := h127
    linarith
  have hSb : ‖(smatVar P W L u v : ℂ)‖ ≤ CS * (W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, hS]
    exact hCS W L hadm hWn u v
  have hdiag : (if v - u = 0 then (L : ℝ) ^ τ * η * lam else 0) =
      (L : ℝ) ^ τ * η * lam * (if u = v then 1 else 0) := by
    by_cases h : u = v
    · simp [h]
    · have : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      simp [h, this]
  rw [hdiag] at hT3'
  -- the constants
  have hWσ4 : (W : ℝ) ^ τ ≤ (W : ℝ) ^ (σ / 4) := Real.rpow_le_rpow_of_exponent_le hW1' hτσ
  have hLσ4 : (L : ℝ) ^ τ ≤ (W : ℝ) ^ (σ / 4) :=
    hLτ.trans (Real.rpow_le_rpow_of_exponent_le hW1' hτc')
  have hKcW : Kc ≤ (W : ℝ) ^ (σ / 2) := by
    have hKc1 : 0 ≤ Kc := by rw [hKc]; positivity
    calc Kc = (Kc ^ (2 / σ)) ^ (σ / 2) := by
          rw [← Real.rpow_mul hKc1]; field_simp; simp
      _ ≤ (W : ℝ) ^ (σ / 2) := Real.rpow_le_rpow (by positivity)
          ((le_max_right _ _).trans ((le_max_right _ _).trans hWb)) (by positivity)
  have hW34 : (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 4) ≤ (W : ℝ) ^ σ := by
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
  have hσ4σ : (W : ℝ) ^ (σ / 4) ≤ (W : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
  have hX0 : 0 ≤ (W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) := by positivity
  have hlam0 : 0 ≤ lam := by positivity
  have hLτ0 : 0 ≤ (L : ℝ) ^ τ := by positivity
  have hδ0 : (0 : ℝ) ≤ if u = v then 1 else 0 := by split_ifs <;> norm_num
  rw [hid]
  calc ‖R 0 (v - u) - Sg 0 (v - u) - (∑ w, R 0 w) * (smatVar P W L u v : ℂ)‖
      ≤ ‖R 0 (v - u) - Sg 0 (v - u)‖ + ‖∑ w, R 0 w‖ * ‖(smatVar P W L u v : ℂ)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ (η * (lam * (W : ℝ) ^ τ * ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)))) +
          (L : ℝ) ^ τ * η * lam * (if u = v then 1 else 0)) +
        2 * ((L : ℝ) ^ τ * η * lam) * (CS * ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)))) := by
        refine add_le_add (hT3'.trans (add_le_add ?_ le_rfl)) ?_
        · calc η * (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
                brk d L W u v ^ (-(2 * (d : ℝ) - 6 - τ))
              = η * ((W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
                brk d L W u v ^ (-(2 * (d : ℝ) - 6 - τ))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hmain him.le
        · refine mul_le_mul hc (hSb.trans (le_of_eq (by ring))) (norm_nonneg _) (by positivity)
    _ = η * lam * (((W : ℝ) ^ τ + 2 * CS * (L : ℝ) ^ τ) *
          ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1))) +
          (L : ℝ) ^ τ * (if u = v then 1 else 0)) := by ring
    _ ≤ η * lam * ((W : ℝ) ^ σ * ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1))) +
          (W : ℝ) ^ σ * (if u = v then 1 else 0)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · refine mul_le_mul_of_nonneg_right ?_ hX0
          calc (W : ℝ) ^ τ + 2 * CS * (L : ℝ) ^ τ ≤ (W : ℝ) ^ (σ / 4) + 2 * CS * (W : ℝ) ^ (σ / 4) :=
                add_le_add hWσ4 (mul_le_mul_of_nonneg_left hLσ4 (by positivity))
            _ = Kc * (W : ℝ) ^ (σ / 4) := by rw [hKc]; ring
            _ ≤ (W : ℝ) ^ (σ / 2) * (W : ℝ) ^ (σ / 4) :=
                mul_le_mul_of_nonneg_right hKcW (by positivity)
            _ ≤ _ := hW34
        · exact mul_le_mul_of_nonneg_right (hLσ4.trans hσ4σ) hδ0
    _ = _ := by ring

end Delta

/-! ## The formal sum `Σ_n` -/

section Expansion

/-- The value of a graph of deterministic kinds with labels in `[4, N]` reads the self-energy
matrices of the record only at the orders `4 ≤ l ≤ N`. -/
private theorem RenormDiff_val_congr {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ}
    (Γ : Graph k n) (S : Matrix ι ι ℝ) (z : ℂ) (M M' : ℕ → Matrix ι ι ℂ) (N : ℕ)
    (hK : Γ.comps.all (Comp.isDetKind N) = true) (hM : ∀ l, 4 ≤ l → l ≤ N → M l = M' l)
    (e : Fin k → ι) : Γ.val (detData S z M) e = Γ.val (detData S z M') e := by
  unfold Graph.val Graph.term
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 2
  refine List.map_congr_left fun c hc => ?_
  have h := List.all_eq_true.1 hK c hc
  rcases c with ⟨κ, x, y, mi, lb⟩
  cases κ with
  | theta o =>
    simp only [Comp.isDetKind, labelOK, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at h
    change (o.foldl (fun A l => A * M l * cmat (Theta (msc z) S)) (cmat (Theta (msc z) S)))
        (Sum.elim e s x) (Sum.elim e s y) =
      (o.foldl (fun A l => A * M' l * cmat (Theta (msc z) S)) (cmat (Theta (msc z) S)))
        (Sum.elim e s x) (Sum.elim e s y)
    rw [List.foldl_ext _ _ _ fun a b hb => by rw [hM b (h.2 b hb).1.1 (h.2 b hb).1.2]]
  | waved w => cases w <;> rfl
  | _ => rfl

/-- The self-energy matrices below `N` depend only on the orders below `N` of the family. -/
private theorem RenormDiff_sigUpTo_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sig Sig' : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) :
    ∀ N : ℕ, (∀ k < N, Sig' k = Sig k) → sigUpTo Sig' S z N = sigUpTo Sig S z N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    have h1 : sigUpTo Sig' S z N = sigUpTo Sig S z N := ih fun k hk => h k (by omega)
    simp only [sigUpTo, h1, h N (by omega)]

/-- **The formal sum**: the bound of `RenormDiff_graphDiff` for every graph of a formal sum with
the shape of an `n`-th order self-energy, times the number of graphs. -/
private theorem RenormDiff_expDiff (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (KA KB : KerFamily d) (n : ℕ)
    (hA : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → KerSymm KA l ∧ KerBound KA l)
    (hB : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → KerSymm KB l ∧ KerBound KB l)
    (hΔ : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L],
      (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L, ∀ u v : Zd d L,
        ‖KA l W L z u v - KB l W L z u v‖ ≤
          z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
            ((W : ℝ) * brk d L W u v ^ (-((d : ℝ) + 1)) + if u = v then 1 else 0))
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ E : Expansion 2, SelfEnergyShape n E →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ x : Zd d L,
          ‖E.val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![0, x] -
              E.val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![0, x]‖ ≤
            E.length * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
              (if x = 0 then z.im * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2))
                else 0)) := by
  intro E
  induction E with
  | nil =>
    intro _
    exact ⟨0, fun W L _ _ _ z _ x => by simp [Expansion.val]⟩
  | cons g E ih =>
    intro hE
    obtain ⟨W₁, h₁⟩ := RenormDiff_graphDiff d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB n hA hB hΔ g
      (fun g' hg' => hE g' (by rw [List.mem_singleton] at hg'; rw [hg']; exact List.mem_cons_self))
      τ hτ
    obtain ⟨W₂, h₂⟩ := ih (fun g' hg' => hE g' (List.mem_cons_of_mem _ hg'))
    refine ⟨max W₁ W₂, fun W L _ hadm hW z hz x => ?_⟩
    have e : ∀ D : Data (Zd d L), Expansion.val (g :: E) D ![0, x] =
        g.2.val D ![0, x] + Expansion.val E D ![0, x] := fun D => by
      simp [Expansion.val]
    rw [e, e, add_sub_add_comm, List.length_cons]
    push_cast
    refine (norm_add_le _ _).trans ?_
    have h1 := h₁ W L hadm ((le_max_left _ _).trans hW) z hz x
    have h2 := h₂ W L hadm ((le_max_right _ _).trans hW) z hz x
    linarith

end Expansion

/-! ## [I, Lemma 8.3] -/

section Main

/-- For `L ≥ L₀` in `adm(c₀, c₁)`, `W ≥ W₀`. -/
private theorem RenormDiff_W_of_L {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) (W₀ : ℝ) :
    ∃ L₀ : ℕ, ∀ W L : ℕ, L₀ ≤ L → (W, L) ∈ adm c₀ c₁ → W₀ ≤ W := by
  refine ⟨⌈(max W₀ 0) ^ (1 / c₁)⌉₊, fun W L hL hadm => ?_⟩
  have h1 : (max W₀ 0) ^ (1 / c₁) ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have h2 : ((max W₀ 0) ^ (1 / c₁)) ^ c₁ ≤ (L : ℝ) ^ c₁ :=
    Real.rpow_le_rpow (by positivity) h1 hc₁.le
  rw [← Real.rpow_mul (le_max_right _ _), one_div_mul_cancel hc₁.ne', Real.rpow_one] at h2
  exact (le_max_left _ _).trans (h2.trans hadm.1)

/-- The value of `Σ_n` for a family `F` on the record with the matrices of orders `< n`: for
`4 ≤ l ≤ n - 1` they are the matrices `Σ_l` of a family `F'` agreeing with `F` below `n`. -/
private theorem RenormDiff_sigMat_rec {d : ℕ} (P : Profile d) (F F' : ℕ → Expansion 2) (n : ℕ)
    (hF : ∀ k < n, F k = F' k) (hK : ∀ g ∈ F n, g.2.comps.all (Comp.isDetKind (n - 1)) = true)
    (W L : ℕ) [NeZero L] (hS : smatVar P W L = Smat P.ψ W L) (z : ℂ) (x : Zd d L) :
    sigMat F (smatVar P W L) z n 0 x =
      (F n).val (detData (Smat P.ψ W L) z (fun l => sigKer (smatVar P) F' l W L z)) ![0, x] := by
  have h1 : sigMat F (smatVar P W L) z n 0 x =
      (F n).val (detData (smatVar P W L) z (sigUpTo F (smatVar P W L) z n)) ![0, x] := rfl
  have h2 : (F n).val (detData (smatVar P W L) z (sigUpTo F (smatVar P W L) z n)) ![0, x] =
      (F n).val (detData (smatVar P W L) z (fun l => sigKer (smatVar P) F' l W L z)) ![0, x] := by
    unfold Expansion.val
    refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
    refine RenormDiff_val_congr g.2 _ z _ _ (n - 1) (hK g hg) (fun l hl4 hln => ?_) _
    rw [sigUpTo_eq_sigMat _ F _ z l n (by omega)]
    change sigMat F (smatVar P W L) z l = sigMat F' (smatVar P W L) z l
    unfold sigMat
    rw [RenormDiff_sigUpTo_congr F' F _ z l fun k hk => hF k (by omega), hF l (by omega)]
  rw [h1, h2, hS]

/-- **[I, Lemma 8.3]** by induction on the order: (8.4) with the term at `x = 0` and (8.5) at
every order `n ≥ 4` whose lower orders are self-energies, `Σ_n` having the shape of an `n`-th
order self-energy. -/
private theorem RenormDiff_main (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) :
    ∀ n : ℕ, 4 ≤ n → SelfEnergiesUpTo d (smatVar P) Sig (n - 1) →
      SelfEnergyShape n (Sig n) → RenormDiff_claim d P Sig n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hSig hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set KA : KerFamily d := sigKer (smatVar P) (Renorm.sig Sig) with hKA
  set KB : KerFamily d := sigKer (smatVar P) Sig with hKB
  have hA : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → KerSymm KA l ∧ KerBound KA l :=
    fun l h4 hl he => Renorm.kerSymm_kerBound d hd P (n - 1) Sig hSig l h4 hl he
  have hB : ∀ l, 4 ≤ l → l ≤ n - 1 → Even l → KerSymm KB l ∧ KerBound KB l :=
    fun l h4 hl he => ⟨(hSig l h4 hl he).2.1, (hSig l h4 hl he).2.2⟩
  have hΔ := fun l (h4 : 4 ≤ l) (hl : l ≤ n - 1) (he : Even l) =>
    RenormDiff_delta d hd P Sig l (ih l (by omega) h4
      (fun k hk4 hkl hke => hSig k hk4 (by omega) hke) (hSig l h4 hl he).1)
      (hSig l h4 hl he).2.2 c₀ c₁ κ ε hc₀ hc₁ hc hκ hε
  set τ₁ : ℝ := min τ 1 / 4 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁τ : 4 * τ₁ ≤ τ := by rw [hτ₁]; linarith [min_le_left τ 1]
  have hτ₁1 : τ₁ ≤ 1 / 4 := by rw [hτ₁]; linarith [min_le_right τ 1]
  obtain ⟨W₁, h₁⟩ := RenormDiff_expDiff d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KA KB n hA hB hΔ τ₁ hτ₁0
    (Sig n) hsh
  obtain ⟨W₂, h₂⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₃, h₃⟩ := RenormDiff_two_le (c₁ := c₁) hc₀ (by linarith)
  obtain ⟨W₄, h₄⟩ := RenormDiff_logF_le (c₀ := c₀) hc₁ τ₁ hτ₁0
  set KE : ℝ := ((Sig n).length : ℝ) with hKE
  set Q : ℝ := (KE + 1) * (6 ^ d + 1) with hQ
  obtain ⟨L₀, hL₀⟩ := RenormDiff_W_of_L (c₀ := c₀) hc₁
    (max (max W₁ W₂) (max (max W₃ W₄) (max 1 (Q ^ (1 / τ₁)))))
  refine ⟨L₀, fun W L _ hL hadm z hz => ?_⟩
  have hW := hL₀ W L hL hadm
  have hWa := (le_max_left _ _).trans hW
  have hWb := (le_max_right _ _).trans hW
  have hW1' : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWb)
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hWn hz
  have hS := h₂ W L hadm ((le_max_right _ _).trans hWa)
  have hWL := h₃ W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hWb))
  have hlog := h₄ W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans hWb))
  have hlog0 := RenormDiff_logF_nonneg hWn hWL
  obtain ⟨hWLe, hLτ⟩ := RenormDiff_adm_LW hc₀ hc₁ hadm τ hτ.le
  have hQW : Q ≤ (W : ℝ) ^ τ₁ := by
    have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
    calc Q = (Q ^ (1 / τ₁)) ^ τ₁ := by
          rw [← Real.rpow_mul hQ0]; field_simp; simp
      _ ≤ (W : ℝ) ^ τ₁ := Real.rpow_le_rpow (by positivity)
          ((le_max_right _ _).trans ((le_max_right _ _).trans hWb)) hτ₁0.le
  have hKE0 : 0 ≤ KE := by rw [hKE]; positivity
  have hKEW : KE + 1 ≤ (W : ℝ) ^ τ₁ := by
    refine le_trans ?_ hQW
    rw [hQ]
    have : (1 : ℝ) ≤ 6 ^ d + 1 := by have : (0 : ℝ) ≤ 6 ^ d := by positivity
                                     linarith
    nlinarith
  have h6W : (6 : ℝ) ^ d + 1 ≤ (W : ℝ) ^ τ₁ := by
    refine le_trans ?_ hQW
    rw [hQ]
    have : (0 : ℝ) ≤ 6 ^ d + 1 := by positivity
    nlinarith
  have hWτ₁ : 1 ≤ (W : ℝ) ^ τ₁ := Real.one_le_rpow hW1' hτ₁0.le
  -- the values on the records of `KA`, `KB`
  have hK : ∀ g ∈ Sig n, g.2.comps.all (Comp.isDetKind (n - 1)) = true :=
    fun g hg => (hsh g hg).2.1
  have hRA : ∀ x, sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x =
      (Sig n).val (detData (Smat P.ψ W L) z (fun l => KA l W L z)) ![0, x] := by
    intro x
    have := RenormDiff_sigMat_rec P (Function.update (Renorm.sig Sig) n (Sig n)) (Renorm.sig Sig)
      n (fun k hk => Function.update_of_ne (by omega) _ _)
      (by rw [Function.update_self]; exact hK) W L hS z x
    rwa [Function.update_self] at this
  have hRB : ∀ x, sigMat Sig (smatVar P W L) z n 0 x =
      (Sig n).val (detData (Smat P.ψ W L) z (fun l => KB l W L z)) ![0, x] :=
    fun x => RenormDiff_sigMat_rec P Sig Sig n (fun k _ => rfl) hK W L hS z x
  have hpt : ∀ x : Zd d L,
      ‖sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x -
          sigMat Sig (smatVar P W L) z n 0 x‖ ≤
        KE * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ₁)) +
          (if x = 0 then z.im * (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0)) := by
    intro x
    rw [hRA, hRB]
    exact h₁ W L hadm ((le_max_left _ _).trans hWa) z hz x
  have hexp : (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) =
      (W : ℝ) ^ (-((n : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
  have hL1 : (1 : ℝ) ≤ L := hW1'.trans hWLe
  have hWLτ : (W : ℝ) ^ τ ≤ (L : ℝ) ^ τ := Real.rpow_le_rpow hW0.le hWLe hτ.le
  have hW2τ : (W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁ ≤ (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; exact Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
  have hW4τ : (W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁ * ((W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁) ≤ (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
  set lam2 : ℝ := (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) with hlam2
  have hlam20 : 0 ≤ lam2 := by positivity
  refine ⟨fun x => ?_, ?_⟩
  · -- (8.4) with the term at `x = 0`
    refine (hpt x).trans ?_
    have hb := RenormDiff_brk_pos (d := d) (L := L) hWn 0 x
    have hsplit : brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ₁)) =
        brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) * brk d L W 0 x ^ (-(τ - τ₁)) := by
      rw [← Real.rpow_add hb]; ring_nf
    have hKb : KE * brk d L W 0 x ^ (-(τ - τ₁)) ≤ 1 := by
      have h1 : brk d L W 0 x ^ (-(τ - τ₁)) ≤ (W : ℝ) ^ (-(τ - τ₁)) :=
        Real.rpow_le_rpow_of_nonpos hW0 (RenormDiff_le_brk 0 x) (by linarith)
      have h2 : (W : ℝ) ^ (-(τ - τ₁)) ≤ (W : ℝ) ^ (-τ₁) :=
        Real.rpow_le_rpow_of_exponent_le hW1' (by linarith)
      have h3 : (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-τ₁) = 1 := by rw [← Real.rpow_add hW0]; simp
      have h4 : 0 ≤ (W : ℝ) ^ (-τ₁) := by positivity
      calc KE * brk d L W 0 x ^ (-(τ - τ₁)) ≤ KE * (W : ℝ) ^ (-τ₁) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hKE0
        _ ≤ (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-τ₁) := mul_le_mul_of_nonneg_right (by linarith) h4
        _ = 1 := h3
    have hmain : KE * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ₁))) ≤
        z.im * (W : ℝ) ^ (-((n : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
          brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by
      rw [hsplit]
      have hX : 0 ≤ z.im * (W : ℝ) ^ (-((n : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
          brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by positivity
      calc KE * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            (brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) * brk d L W 0 x ^ (-(τ - τ₁))))
          = (z.im * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ)) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ))) *
            (KE * brk d L W 0 x ^ (-(τ - τ₁))) := by ring
        _ ≤ (z.im * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ)) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ))) * 1 := by
            refine mul_le_mul_of_nonneg_left hKb ?_
            rw [hexp]; linarith [hX, show z.im * ((W : ℝ) ^ (-((n : ℝ) * d / 2)) *
              (W : ℝ) ^ (2 * (d : ℝ) - 6)) * brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) =
              z.im * (W : ℝ) ^ (-((n : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 6) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) by ring]
        _ = _ := by rw [hexp]; ring
    have hdiag : KE * (if x = 0 then z.im * (W : ℝ) ^ τ₁ * lam2 else 0) ≤
        (if x = 0 then (L : ℝ) ^ τ * z.im * lam2 else 0) := by
      split_ifs
      · calc KE * (z.im * (W : ℝ) ^ τ₁ * lam2) = (KE * (W : ℝ) ^ τ₁) * (z.im * lam2) := by ring
          _ ≤ ((W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁) * (z.im * lam2) := by
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
          _ ≤ (L : ℝ) ^ τ * (z.im * lam2) :=
              mul_le_mul_of_nonneg_right (hW2τ.trans hWLτ) (by positivity)
          _ = _ := by ring
      · simp
    rw [mul_add]
    exact add_le_add hmain hdiag
  · -- (8.5): the sum over `x`
    rw [← Finset.sum_sub_distrib]
    have htail := RenormDiff_tail (d := d) (L := L) hWn hWL (2 * (d : ℝ) - 6 - τ₁) (by linarith) 0
    have hsum : ∑ x : Zd d L, (if x = 0 then z.im * (W : ℝ) ^ τ₁ * lam2 else 0) =
        z.im * (W : ℝ) ^ τ₁ * lam2 := by
      rw [Finset.sum_ite_eq']; simp
    have hpow : (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁)) = lam2 * (W : ℝ) ^ τ₁ := by
      rw [hlam2, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      congr 1; ring
    calc ‖∑ x, (sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x -
          sigMat Sig (smatVar P W L) z n 0 x)‖
        ≤ ∑ x : Zd d L, KE * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) *
            (W : ℝ) ^ (-6 : ℝ) * brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ₁)) +
          (if x = 0 then z.im * (W : ℝ) ^ τ₁ * lam2 else 0)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hpt x)
      _ = KE * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            ∑ x, brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ₁)) + z.im * (W : ℝ) ^ τ₁ * lam2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hsum, ← Finset.mul_sum]
      _ ≤ KE * (z.im * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            ((W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁)) * (6 ^ d * logF L W)) +
            z.im * (W : ℝ) ^ τ₁ * lam2) := by
          gcongr
      _ = KE * (z.im * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁))) * (6 ^ d * logF L W) +
            z.im * (W : ℝ) ^ τ₁ * lam2) := by ring
      _ = KE * (z.im * lam2 * (W : ℝ) ^ τ₁) * (6 ^ d * logF L W + 1) := by
          rw [hpow]; ring
      _ ≤ (W : ℝ) ^ τ₁ * (z.im * lam2 * (W : ℝ) ^ τ₁) *
            ((W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁) := by
          have h6 : 6 ^ d * logF L W + 1 ≤ (W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁ := by
            have : (6 : ℝ) ^ d * logF L W ≤ (6 ^ d) * (W : ℝ) ^ τ₁ :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
            nlinarith
          refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) h6
            (by positivity) (by positivity)
      _ = z.im * lam2 * ((W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁ * ((W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁)) := by ring
      _ ≤ z.im * lam2 * (L : ℝ) ^ τ :=
          mul_le_mul_of_nonneg_left (hW4τ.trans hWLτ) (by positivity)
      _ = _ := by ring

end Main

/-- **[I, Lemma 8.3], (8.5)**, with the quantifiers of the second conjunct of `SelfEnergyBound`,
under the hypotheses of (8.4):
`|Σ_x Σ^{(r)}_n(0, x) − Σ_x Σ_n(0, x)| ≤ L^τ η W^{-(n-2)d/2}`. -/
theorem RenormDiff.rowSum (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2)
    (hn : 4 ≤ n) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (n - 1))
    (hsh : SelfEnergyShape n (Sig n)) :
    ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L,
          ‖∑ x, sigMat (Function.update (Renorm.sig Sig) n (Sig n)) (smatVar P W L) z n 0 x -
              ∑ x, sigMat Sig (smatVar P W L) z n 0 x‖ ≤
            (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) := by
  intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  obtain ⟨L₀, h⟩ := RenormDiff_main d hd P Sig n hn hSig hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  exact ⟨L₀, fun W L _ hL hadm z hz => (h W L hL hadm z hz).2⟩


section Instances

section Instances

end Instances

end Instances

section Needed

end Needed

end RBM8D.Graphs
