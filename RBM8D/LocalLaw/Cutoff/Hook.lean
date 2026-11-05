import RBM8D.LocalLaw.Cutoff.Defs
import RBM8D.LocalLaw.QTerm
import Batteries.Tactic.OpenPrivate

/-!
# The hook graph sum

`hookGraphSum : hookGraphSumStmt`: for a graph with the hypotheses of the third row of
`graphSumStmt''` ([II, (8.23)–(8.24)]) and an internal atom `v`, the absolute-value graph with the
extra weight `B_{c σ(v)}^{1/2}` at `v` is at most `W^τ W^{−(n_𝔟−2)d/2} W^{−d/2} B_{𝔞𝔟}`, for every
centre `c`, under the entrywise bound `|G_{xy} − δ_{xy} m| ≤ W^{τ'} B_{xy}^{1/2}`.

The proof follows the third row of `graphSum''`. When `𝔟` lies in both spanning trees the weight
is bounded by `B_{cc}^{1/2} = W^{−d/2}`. Otherwise every blue edge is bounded entrywise by
`B^{1/2}`, and the sum over the internal labels is a deterministic sum over a black and a blue
spanning tree with the three marks `B_{𝔞 σ(x₀)}`, `B_{σ(u) 𝔟}` and `B^{1/2}_{c σ(v)}`. With
`V = W^{d/2} B^{1/2}` (so that `W^d B = V²`), the inequality `s² t ≤ s³ + t³` reduces the two trees
to one tree with the summable kernel `V³`, and the leaves are summed one at a time towards the
hook atom, using `Σ_y V_{xy}³ V_{yz}^k ≤ C W^d V_{xz}^k` (`k ≤ 3`) and
`Σ_t V_{at}² V_{tb}² V_{ct} ≤ C W^d V_{ab}²` (`d ≥ 8`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

open private Norm_tailSum Norm_brk_tri from RBM8D.Bound.Norm
open private prod_map_le_sub from RBM8D.Bound.AuxTree

/-! ## The kernel `V = W^{d/2} B^{1/2}` -/

section Kernel

variable {d L W : ℕ} [NeZero L]

/-- `V_{xy} = W^{d/2} B_{xy}^{1/2} = (⟨x − y⟩/W)^{−(d−2)/2}`. -/
private def hV (d L W : ℕ) [NeZero L] (x y : Zd d L) : ℝ :=
  (W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y)

private theorem hV_nonneg (x y : Zd d L) : 0 ≤ hV d L W x y := by
  unfold hV; positivity

private theorem hV_le_one (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) : hV d L W x y ≤ 1 :=
  rpow_mul_sqrt_bB_le hd hW x y

private theorem hV_comm (x y : Zd d L) : hV d L W x y = hV d L W y x := by
  unfold hV; rw [bB_comm']

private theorem hV_sq (hW : 1 ≤ W) (x y : Zd d L) :
    hV d L W x y ^ 2 = (W : ℝ) ^ (d : ℝ) * bB d L W x y := by
  rw [sq]; exact sq_half_eq hW x y

private theorem brk_comm' (x y : Zd d L) : brk d L W x y = brk d L W y x := by
  unfold brk; rw [← zdistInf_neg d L (x - y), neg_sub]

omit [NeZero L] in
private theorem brk_pos' (hW : 1 ≤ W) (x y : Zd d L) : 0 < brk d L W x y := by
  unfold brk
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  positivity

/-- `V_{xy} = W^p ⟨x − y⟩^{−p}` with `p = (d − 2)/2`. -/
private theorem hV_eq (hW : 1 ≤ W) (x y : Zd d L) :
    hV d L W x y = (W : ℝ) ^ (((d : ℝ) - 2) / 2) * brk d L W x y ^ (-(((d : ℝ) - 2) / 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hb := brk_pos' (d := d) (L := L) hW x y
  have hB : bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl
  unfold hV
  rw [hB, Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hW0.le,
    ← Real.rpow_mul hb.le, ← mul_assoc, ← Real.rpow_add hW0]
  congr 2 <;> ring

/-- One of `V_{xy}`, `V_{yz}` is at most `2^p V_{xz}`, `p = (d − 2)/2`. -/
private theorem hV_tri (hd : 2 ≤ d) (hW : 1 ≤ W) (x y z : Zd d L) :
    hV d L W x y ≤ (2 : ℝ) ^ (((d : ℝ) - 2) / 2) * hV d L W x z ∨
      hV d L W y z ≤ (2 : ℝ) ^ (((d : ℝ) - 2) / 2) * hV d L W x z := by
  set p : ℝ := ((d : ℝ) - 2) / 2 with hp
  have hp0 : 0 ≤ p := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hp]; linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hxz := brk_pos' (d := d) (L := L) hW x z
  have htri : brk d L W x z ≤ brk d L W x y + brk d L W y z := by
    have h := Norm_brk_tri d L W y x z
    rw [brk_comm' y x] at h
    have : (0 : ℝ) ≤ W := hW0.le
    linarith
  have key : ∀ r, 0 < r → brk d L W x z ≤ 2 * r →
      (W : ℝ) ^ p * r ^ (-p) ≤ (2 : ℝ) ^ p * ((W : ℝ) ^ p * brk d L W x z ^ (-p)) := by
    intro r hr h
    have h1 : r ^ (-p) ≤ (brk d L W x z / 2) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h2 : (brk d L W x z / 2) ^ (-p) = (2 : ℝ) ^ p * brk d L W x z ^ (-p) := by
      rw [Real.div_rpow hxz.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    calc (W : ℝ) ^ p * r ^ (-p) ≤ (W : ℝ) ^ p * ((2 : ℝ) ^ p * brk d L W x z ^ (-p)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  rw [hV_eq hW, hV_eq hW, hV_eq hW]
  rcases le_total (brk d L W y z) (brk d L W x y) with h | h
  · exact Or.inl (key _ (brk_pos' hW x y) (by linarith))
  · exact Or.inr (key _ (brk_pos' hW y z) (by linarith))

/-- `Σ_y V_{xy}³ ≤ C W^d` for `d ≥ 8`. -/
private theorem hV_tail (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ x : Zd d L,
      ∑ y, hV d L W x y ^ 3 ≤ C * (W : ℝ) ^ (d : ℝ) := by
  set p : ℝ := ((d : ℝ) - 2) / 2 with hp
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC0, hC⟩ := Norm_tailSum d (3 * p) (by rw [hp]; linarith)
  refine ⟨C, hC0, fun L W _ hW x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h := hC L W hW x (W : ℝ) (by linarith)
  have hfull : Finset.univ.filter (fun y : Zd d L => (W : ℝ) ≤ brk d L W y x) = Finset.univ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    unfold brk
    have : (0 : ℝ) ≤ (zdistInf d L (y - x) : ℝ) := Nat.cast_nonneg _
    linarith
  rw [hfull] at h
  have hpt : ∀ y, hV d L W x y ^ 3 = (W : ℝ) ^ (3 * p) * brk d L W y x ^ (-(3 * p)) := by
    intro y
    rw [hV_eq hW, brk_comm' x y, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hW0.le, ← Real.rpow_mul (brk_pos' hW y x).le]
    push_cast
    congr 1 <;> congr 1 <;> ring
  simp_rw [hpt]
  rw [← Finset.mul_sum]
  calc (W : ℝ) ^ (3 * p) * ∑ y, brk d L W y x ^ (-(3 * p))
      ≤ (W : ℝ) ^ (3 * p) * (C * (W : ℝ) ^ ((d : ℝ) - 3 * p)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * ((W : ℝ) ^ (3 * p) * (W : ℝ) ^ ((d : ℝ) - 3 * p)) := by ring
    _ = C * (W : ℝ) ^ (d : ℝ) := by rw [← Real.rpow_add hW0]; ring_nf

/-- `A³ B^k ≤ D^k (A³ + B³)` for `A, B, D ≥ 0`, `k ≤ 3` and `A ≤ D` or `B ≤ D`. -/
private theorem hV_pt (A B D : ℝ) (k : ℕ) (hk : k ≤ 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ≤ D ∨ B ≤ D) : A ^ 3 * B ^ k ≤ D ^ k * (A ^ 3 + B ^ 3) := by
  have hM : A ^ (3 - k) * B ^ k ≤ A ^ 3 + B ^ 3 := by
    rcases le_total A B with hAB | hAB
    · calc A ^ (3 - k) * B ^ k ≤ B ^ (3 - k) * B ^ k :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB _) (by positivity)
        _ = B ^ 3 := by rw [← pow_add]; congr 1; omega
        _ ≤ A ^ 3 + B ^ 3 := by have := pow_nonneg hA 3; linarith
    · calc A ^ (3 - k) * B ^ k ≤ A ^ (3 - k) * A ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hAB _) (by positivity)
        _ = A ^ 3 := by rw [← pow_add]; congr 1; omega
        _ ≤ A ^ 3 + B ^ 3 := by have := pow_nonneg hB 3; linarith
  rcases h with h | h
  · have hD : 0 ≤ D := hA.trans h
    calc A ^ 3 * B ^ k = A ^ k * (A ^ (3 - k) * B ^ k) := by
          rw [← mul_assoc, ← pow_add]; congr 2; omega
      _ ≤ D ^ k * (A ^ 3 + B ^ 3) :=
          mul_le_mul (pow_le_pow_left₀ hA h _) hM (by positivity) (by positivity)
  · have hD : 0 ≤ D := hB.trans h
    calc A ^ 3 * B ^ k ≤ A ^ 3 * D ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB h _) (by positivity)
      _ ≤ D ^ k * (A ^ 3 + B ^ 3) := by
          have := pow_nonneg hB 3
          have := pow_nonneg hD k
          nlinarith [mul_nonneg this (pow_nonneg hB 3)]

/-- `x² y ≤ x³ + y³` for `x, y ≥ 0`. -/
private theorem hV_amgm {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 * y ≤ x ^ 3 + y ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (x - y)) (add_nonneg hx hy), mul_nonneg hx (sq_nonneg y)]

/-- `Σ_y V_{xy}³ V_{yz}^k ≤ C W^d V_{xz}^k` for `k ≤ 3` and `d ≥ 8`. -/
private theorem hV_conv (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (k : ℕ), k ≤ 3 → ∀ x z : Zd d L,
      ∑ y, hV d L W x y ^ 3 * hV d L W y z ^ k ≤ C * (W : ℝ) ^ (d : ℝ) * hV d L W x z ^ k := by
  obtain ⟨C, hC0, hC⟩ := hV_tail d hd
  set p : ℝ := ((d : ℝ) - 2) / 2 with hp
  refine ⟨((2 : ℝ) ^ p + 1) ^ 3 * (2 * C), mul_nonneg (by positivity) (by linarith),
    fun L W _ hW k hk x z => ?_⟩
  set D := (2 : ℝ) ^ p * hV d L W x z with hD
  have hpt : ∀ y, hV d L W x y ^ 3 * hV d L W y z ^ k ≤
      D ^ k * (hV d L W x y ^ 3 + hV d L W z y ^ 3) := by
    intro y
    rw [hV_comm z y]
    exact hV_pt _ _ _ k hk (hV_nonneg _ _) (hV_nonneg _ _) (hV_tri (by omega) hW x y z)
  have hs := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hpt y
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have h1 := hC L W hW x
  have h2 := hC L W hW z
  have hWd : 0 ≤ (W : ℝ) ^ (d : ℝ) := by positivity
  have hDk : D ^ k ≤ ((2 : ℝ) ^ p + 1) ^ 3 * hV d L W x z ^ k := by
    rw [hD, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (hV_nonneg _ _) _)
    calc ((2 : ℝ) ^ p) ^ k ≤ ((2 : ℝ) ^ p + 1) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ ((2 : ℝ) ^ p + 1) ^ 3 :=
          pow_le_pow_right₀ (by have : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
                                linarith) hk
  calc _ ≤ D ^ k * (∑ y, hV d L W x y ^ 3 + ∑ y, hV d L W z y ^ 3) := hs
    _ ≤ (((2 : ℝ) ^ p + 1) ^ 3 * hV d L W x z ^ k) * (2 * C * (W : ℝ) ^ (d : ℝ)) := by
        refine mul_le_mul hDk (by linarith) (add_nonneg
          (Finset.sum_nonneg fun y _ => pow_nonneg (hV_nonneg _ _) _)
          (Finset.sum_nonneg fun y _ => pow_nonneg (hV_nonneg _ _) _))
          (mul_nonneg (by positivity) (pow_nonneg (hV_nonneg _ _) _))
    _ = _ := by ring

/-- `Σ_t V_{at}² V_{tb}² V_{ct} ≤ C W^d V_{ab}²` for `d ≥ 8`. -/
private theorem hV_three (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ a b c : Zd d L,
      ∑ t, hV d L W a t ^ 2 * hV d L W t b ^ 2 * hV d L W c t ≤
        C * (W : ℝ) ^ (d : ℝ) * hV d L W a b ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hV_tail d hd
  set p : ℝ := ((d : ℝ) - 2) / 2 with hp
  refine ⟨((2 : ℝ) ^ p) ^ 2 * (4 * C), mul_nonneg (by positivity) (by linarith),
    fun L W _ hW a b c => ?_⟩
  set D := (2 : ℝ) ^ p * hV d L W a b with hD
  have hpt : ∀ t, hV d L W a t ^ 2 * hV d L W t b ^ 2 * hV d L W c t ≤
      D ^ 2 * (hV d L W a t ^ 3 + hV d L W b t ^ 3 + 2 * hV d L W c t ^ 3) := by
    intro t
    have hA := hV_nonneg (W := W) a t
    have hB := hV_nonneg (W := W) t b
    have hE := hV_nonneg (W := W) c t
    have hBE := hV_amgm hB hE
    have hAE := hV_amgm hA hE
    rw [hV_comm b t]
    rcases hV_tri (by omega) hW a t b with h | h
    · have hD0 : 0 ≤ D := hA.trans h
      calc hV d L W a t ^ 2 * hV d L W t b ^ 2 * hV d L W c t
          ≤ D ^ 2 * (hV d L W t b ^ 2 * hV d L W c t) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA h 2) (by positivity)
        _ ≤ D ^ 2 * (hV d L W t b ^ 3 + hV d L W c t ^ 3) :=
            mul_le_mul_of_nonneg_left hBE (by positivity)
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [pow_nonneg hA 3, pow_nonneg hE 3]
    · have hD0 : 0 ≤ D := hB.trans h
      calc hV d L W a t ^ 2 * hV d L W t b ^ 2 * hV d L W c t
          ≤ D ^ 2 * (hV d L W a t ^ 2 * hV d L W c t) := by
            have : hV d L W t b ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hB h 2
            calc _ = hV d L W t b ^ 2 * (hV d L W a t ^ 2 * hV d L W c t) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ D ^ 2 * (hV d L W a t ^ 3 + hV d L W c t ^ 3) :=
            mul_le_mul_of_nonneg_left hAE (by positivity)
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [pow_nonneg hB 3, pow_nonneg hE 3]
  have hs := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hpt t
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have h1 : ∑ t, hV d L W a t ^ 3 ≤ C * (W : ℝ) ^ (d : ℝ) := hC L W hW a
  have h2 : ∑ t, hV d L W b t ^ 3 ≤ C * (W : ℝ) ^ (d : ℝ) := hC L W hW b
  have h3 : ∑ t, hV d L W c t ^ 3 ≤ C * (W : ℝ) ^ (d : ℝ) := hC L W hW c
  have hD2 : D ^ 2 = ((2 : ℝ) ^ p) ^ 2 * hV d L W a b ^ 2 := by rw [hD, mul_pow]
  calc _ ≤ D ^ 2 * (∑ t, hV d L W a t ^ 3 + ∑ t, hV d L W b t ^ 3 +
        2 * ∑ t, hV d L W c t ^ 3) := hs
    _ ≤ D ^ 2 * (4 * (C * (W : ℝ) ^ (d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity); linarith
    _ = _ := by rw [hD2]; ring

end Kernel

/-! ## Weights of the vertices: the marks `𝔞` and `𝔟` -/

section Marks

variable {d L W : ℕ} [NeZero L]

/-- The weight of a vertex carrying the marks `mA` (the factor `V_{𝔞 y}²`) and `mB` (the factor
`V_{y 𝔟}²`). -/
private def hF (d L W : ℕ) [NeZero L] (a b : Zd d L) (mA mB : Bool) (y : Zd d L) : ℝ :=
  (if mA then hV d L W a y ^ 2 else 1) * (if mB then hV d L W y b ^ 2 else 1)

/-- The class of weights with the marks `mA`, `mB`: `f + W^{−d} Σ_t V_{yt}³ f(t)`. -/
private def hPsi (d L W : ℕ) [NeZero L] (a b : Zd d L) (mA mB : Bool) (y : Zd d L) : ℝ :=
  hF d L W a b mA mB y + ((W : ℝ) ^ (d : ℝ))⁻¹ * ∑ t, hV d L W y t ^ 3 * hF d L W a b mA mB t

private theorem hF_nonneg (a b : Zd d L) (mA mB : Bool) (y : Zd d L) :
    0 ≤ hF d L W a b mA mB y := by
  unfold hF
  have := hV_nonneg (d := d) (L := L) (W := W)
  split_ifs <;> positivity

private theorem hconv_nonneg (a b : Zd d L) (mA mB : Bool) (y : Zd d L) :
    0 ≤ ((W : ℝ) ^ (d : ℝ))⁻¹ * ∑ t, hV d L W y t ^ 3 * hF d L W a b mA mB t :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
    mul_nonneg (pow_nonneg (hV_nonneg _ _) _) (hF_nonneg _ _ _ _ _))

private theorem hPsi_nonneg (a b : Zd d L) (mA mB : Bool) (y : Zd d L) :
    0 ≤ hPsi d L W a b mA mB y :=
  add_nonneg (hF_nonneg _ _ _ _ _) (hconv_nonneg _ _ _ _ _)

private theorem hF_le_hPsi (a b : Zd d L) (mA mB : Bool) (y : Zd d L) :
    hF d L W a b mA mB y ≤ hPsi d L W a b mA mB y :=
  le_add_of_nonneg_right (hconv_nonneg _ _ _ _ _)

/-- Disjoint marks multiply: `f_{m₁} f_{m₂} = f_{m₁ ∨ m₂}`. -/
private theorem hF_mul (a b : Zd d L) (mA₁ mB₁ mA₂ mB₂ : Bool) (hA : ¬ (mA₁ ∧ mA₂))
    (hB : ¬ (mB₁ ∧ mB₂)) (y : Zd d L) :
    hF d L W a b mA₁ mB₁ y * hF d L W a b mA₂ mB₂ y = hF d L W a b (mA₁ || mA₂) (mB₁ || mB₂) y := by
  unfold hF
  cases mA₁ <;> cases mA₂ <;> cases mB₁ <;> cases mB₂ <;> (simp_all; try ring)

/-- The classes are stable under `W^{−d} Σ_y V_{xy}³ (·)(y)`. -/
private theorem hPsi_conv (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b : Zd d L) (mA mB : Bool) (x : Zd d L),
      ((W : ℝ) ^ (d : ℝ))⁻¹ * ∑ y, hV d L W x y ^ 3 * hPsi d L W a b mA mB y ≤
        C * hPsi d L W a b mA mB x := by
  obtain ⟨C, hC0, hC⟩ := hV_conv d hd
  refine ⟨1 + C, by linarith, fun L W _ hW a b mA mB x => ?_⟩
  have hW0 : (0 : ℝ) < (W : ℝ) ^ (d : ℝ) := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  set Dd := (W : ℝ) ^ (d : ℝ) with hDd
  set f := hF d L W a b mA mB with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => hF_nonneg _ _ _ _ _
  have hswap : ∑ y, hV d L W x y ^ 3 * (Dd⁻¹ * ∑ t, hV d L W y t ^ 3 * f t) =
      Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W x y ^ 3 * hV d L W y t ^ 3 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun y _ => by ring
  have hinner : Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W x y ^ 3 * hV d L W y t ^ 3 ≤
      C * ∑ t, hV d L W x t ^ 3 * f t := by
    have : ∀ t, f t * ∑ y, hV d L W x y ^ 3 * hV d L W y t ^ 3 ≤
        f t * (C * Dd * hV d L W x t ^ 3) :=
      fun t => mul_le_mul_of_nonneg_left (hC L W hW 3 le_rfl x t) (hf0 t)
    calc Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W x y ^ 3 * hV d L W y t ^ 3
        ≤ Dd⁻¹ * ∑ t, f t * (C * Dd * hV d L W x t ^ 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => this t) (by positivity)
      _ = C * ∑ t, hV d L W x t ^ 3 * f t := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          field_simp
  have hS0 : 0 ≤ ∑ t, hV d L W x t ^ 3 * f t :=
    Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg (hV_nonneg _ _) _) (hf0 t)
  have e : ∑ y, hV d L W x y ^ 3 * hPsi d L W a b mA mB y =
      ∑ y, hV d L W x y ^ 3 * f y +
        ∑ y, hV d L W x y ^ 3 * (Dd⁻¹ * ∑ t, hV d L W y t ^ 3 * f t) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by unfold hPsi; rw [← hf, ← hDd]; ring
  have hP : hPsi d L W a b mA mB x = f x + Dd⁻¹ * ∑ t, hV d L W x t ^ 3 * f t := by
    unfold hPsi; rw [← hf, ← hDd]
  rw [e, hswap, hP]
  calc Dd⁻¹ * (∑ y, hV d L W x y ^ 3 * f y + Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W x y ^ 3 *
        hV d L W y t ^ 3)
      ≤ Dd⁻¹ * (∑ y, hV d L W x y ^ 3 * f y + C * ∑ t, hV d L W x t ^ 3 * f t) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (1 + C) * (Dd⁻¹ * ∑ t, hV d L W x t ^ 3 * f t) := by ring
    _ ≤ (1 + C) * (f x + Dd⁻¹ * ∑ t, hV d L W x t ^ 3 * f t) :=
        mul_le_mul_of_nonneg_left (by linarith [hf0 x]) (by linarith)

/-- A class with at most one mark is bounded by its weight: `Ψ_m ≤ C f_m`. -/
private theorem hPsi_le (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b : Zd d L) (mA mB : Bool), ¬ (mA ∧ mB) →
      ∀ x : Zd d L, hPsi d L W a b mA mB x ≤ C * hF d L W a b mA mB x := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hV_tail d hd
  obtain ⟨C, hC0, hC⟩ := hV_conv d hd
  refine ⟨1 + C₀ + C, by linarith, fun L W _ hW a b mA mB hm x => ?_⟩
  have hW0 : (0 : ℝ) < (W : ℝ) ^ (d : ℝ) := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  set Dd := (W : ℝ) ^ (d : ℝ) with hDd
  have key : Dd⁻¹ * ∑ t, hV d L W x t ^ 3 * hF d L W a b mA mB t ≤
      (C₀ + C) * hF d L W a b mA mB x := by
    have hle : ∑ t, hV d L W x t ^ 3 * hF d L W a b mA mB t ≤
        (C₀ + C) * Dd * hF d L W a b mA mB x := by
      cases mA <;> cases mB
      · simp only [hF, Bool.false_eq_true, ↓reduceIte, mul_one]
        have := hC₀ L W hW x
        nlinarith
      · simp only [hF, Bool.false_eq_true, ↓reduceIte, one_mul]
        have := hC L W hW 2 (by norm_num) x b
        have h1 : 0 ≤ C₀ * Dd * hV d L W x b ^ 2 := by
          have := hV_nonneg (d := d) (L := L) (W := W) x b; positivity
        nlinarith
      · simp only [hF, Bool.false_eq_true, ↓reduceIte, mul_one]
        simp_rw [hV_comm a]
        have := hC L W hW 2 (by norm_num) x a
        have h1 : 0 ≤ C₀ * Dd * hV d L W x a ^ 2 := by
          have := hV_nonneg (d := d) (L := L) (W := W) x a; positivity
        nlinarith
      · simp at hm
    calc Dd⁻¹ * ∑ t, hV d L W x t ^ 3 * hF d L W a b mA mB t
        ≤ Dd⁻¹ * ((C₀ + C) * Dd * hF d L W a b mA mB x) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (C₀ + C) * hF d L W a b mA mB x := by field_simp
  unfold hPsi
  linarith

/-- The step of the leaf summation: a vertex weight of class `m₁` times the leaf sum of a weight of
class `m₂` is of class `m₁ ∨ m₂`, for disjoint marks. -/
private theorem hPsi_step (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b : Zd d L) (mA₁ mB₁ mA₂ mB₂ : Bool),
      ¬ (mA₁ ∧ mA₂) → ¬ (mB₁ ∧ mB₂) → ∀ (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ →
      ∀ (φ₂ : Zd d L → ℝ), (∀ y, 0 ≤ φ₂ y) →
        (∀ y, φ₂ y ≤ K₂ * hPsi d L W a b mA₂ mB₂ y) → ∀ (x : Zd d L) (u : ℝ), 0 ≤ u →
        u ≤ K₁ * hPsi d L W a b mA₁ mB₁ x →
        u * (((W : ℝ) ^ (d : ℝ))⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y) ≤
          C * K₁ * K₂ * hPsi d L W a b (mA₁ || mA₂) (mB₁ || mB₂) x := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hPsi_conv d hd
  obtain ⟨C₂, hC₂1, hC₂⟩ := hPsi_le d hd
  refine ⟨(1 + C₁) * C₂ * C₂, by
    have h1 : 1 ≤ C₂ * C₂ := one_le_mul_of_one_le_of_one_le hC₂1 hC₂1
    nlinarith, fun L W _ hW a b mA₁ mB₁ mA₂ mB₂ hA hB K₁ K₂ hK₁ hK₂
    φ₂ hφ0 hφ x u hu0 hu => ?_⟩
  have hW0 : (0 : ℝ) < (W : ℝ) ^ (d : ℝ) := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  set Dd := (W : ℝ) ^ (d : ℝ) with hDd
  have hcv : Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y ≤ K₂ * (C₁ * hPsi d L W a b mA₂ mB₂ x) := by
    calc Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y
        ≤ Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * (K₂ * hPsi d L W a b mA₂ mB₂ y) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (hφ y) (pow_nonneg (hV_nonneg _ _) _)) (by positivity)
      _ = K₂ * (Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * hPsi d L W a b mA₂ mB₂ y) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ K₂ * (C₁ * hPsi d L W a b mA₂ mB₂ x) :=
          mul_le_mul_of_nonneg_left (hC₁ L W hW a b mA₂ mB₂ x) hK₂
  have hcv0 : 0 ≤ Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ =>
      mul_nonneg (pow_nonneg (hV_nonneg _ _) _) (hφ0 y))
  have hprod : u * (Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y) ≤
      K₁ * K₂ * C₁ * (hPsi d L W a b mA₁ mB₁ x * hPsi d L W a b mA₂ mB₂ x) := by
    calc u * (Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y)
        ≤ (K₁ * hPsi d L W a b mA₁ mB₁ x) * (K₂ * (C₁ * hPsi d L W a b mA₂ mB₂ x)) :=
          mul_le_mul hu hcv hcv0 (mul_nonneg hK₁ (hPsi_nonneg _ _ _ _ _))
      _ = _ := by ring
  have hPP : hPsi d L W a b mA₁ mB₁ x * hPsi d L W a b mA₂ mB₂ x ≤
      C₂ * C₂ * hPsi d L W a b (mA₁ || mA₂) (mB₁ || mB₂) x := by
    have hP1 := hPsi_nonneg (d := d) (L := L) (W := W) a b mA₁ mB₁ x
    have hP2 := hPsi_nonneg (d := d) (L := L) (W := W) a b mA₂ mB₂ x
    have h00 : hPsi d L W a b false false x ≤ C₂ := by
      have := hC₂ L W hW a b false false (by simp) x
      simpa [hF] using this
    by_cases h1 : mA₁ = false ∧ mB₁ = false
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [Bool.false_or]
      calc _ ≤ C₂ * hPsi d L W a b mA₂ mB₂ x := mul_le_mul_of_nonneg_right h00 hP2
        _ ≤ C₂ * C₂ * hPsi d L W a b mA₂ mB₂ x :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hC₂1) hP2
    by_cases h2 : mA₂ = false ∧ mB₂ = false
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Bool.or_false]
      calc _ ≤ hPsi d L W a b mA₁ mB₁ x * C₂ := mul_le_mul_of_nonneg_left h00 hP1
        _ = C₂ * hPsi d L W a b mA₁ mB₁ x := by ring
        _ ≤ C₂ * C₂ * hPsi d L W a b mA₁ mB₁ x :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hC₂1) hP1
    have hm1 : ¬ (mA₁ ∧ mB₁) := by
      revert hA hB h1 h2; cases mA₁ <;> cases mB₁ <;> cases mA₂ <;> cases mB₂ <;> decide
    have hm2 : ¬ (mA₂ ∧ mB₂) := by
      revert hA hB h1 h2; cases mA₁ <;> cases mB₁ <;> cases mA₂ <;> cases mB₂ <;> decide
    have e1 := hC₂ L W hW a b mA₁ mB₁ hm1 x
    have e2 := hC₂ L W hW a b mA₂ mB₂ hm2 x
    calc _ ≤ (C₂ * hF d L W a b mA₁ mB₁ x) * (C₂ * hF d L W a b mA₂ mB₂ x) :=
          mul_le_mul e1 e2 hP2 (mul_nonneg (by linarith) (hF_nonneg _ _ _ _ _))
      _ = C₂ * C₂ * (hF d L W a b mA₁ mB₁ x * hF d L W a b mA₂ mB₂ x) := by ring
      _ = C₂ * C₂ * hF d L W a b (mA₁ || mA₂) (mB₁ || mB₂) x := by
          rw [hF_mul a b mA₁ mB₁ mA₂ mB₂ hA hB]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hF_le_hPsi _ _ _ _ _) (by positivity)
  calc u * (Dd⁻¹ * ∑ y, hV d L W x y ^ 3 * φ₂ y)
      ≤ K₁ * K₂ * C₁ * (hPsi d L W a b mA₁ mB₁ x * hPsi d L W a b mA₂ mB₂ x) := hprod
    _ ≤ K₁ * K₂ * (1 + C₁) * (C₂ * C₂ * hPsi d L W a b (mA₁ || mA₂) (mB₁ || mB₂) x) := by
        have := mul_nonneg (hPsi_nonneg (d := d) (L := L) (W := W) a b mA₁ mB₁ x)
          (hPsi_nonneg (d := d) (L := L) (W := W) a b mA₂ mB₂ x)
        have hKK : 0 ≤ K₁ * K₂ := mul_nonneg hK₁ hK₂
        calc K₁ * K₂ * C₁ * (hPsi d L W a b mA₁ mB₁ x * hPsi d L W a b mA₂ mB₂ x)
            ≤ K₁ * K₂ * (1 + C₁) * (hPsi d L W a b mA₁ mB₁ x * hPsi d L W a b mA₂ mB₂ x) := by
              gcongr; linarith
          _ ≤ _ := by gcongr
    _ = _ := by ring

/-- The root sum: `Σ_y V_{cy} Ψ_{𝔞𝔟}(y) ≤ C W^d V_{𝔞𝔟}²`. -/
private theorem hPsi_root (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ a b c : Zd d L,
      ∑ y, hV d L W c y * hPsi d L W a b true true y ≤
        C * (W : ℝ) ^ (d : ℝ) * hV d L W a b ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hV_conv d hd
  obtain ⟨C₃, hC₃0, hC₃⟩ := hV_three d hd
  refine ⟨(1 + C₁) * C₃, by positivity, fun L W _ hW a b c => ?_⟩
  have hW0 : (0 : ℝ) < (W : ℝ) ^ (d : ℝ) := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW
    positivity
  set Dd := (W : ℝ) ^ (d : ℝ) with hDd
  set f := hF d L W a b true true with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => hF_nonneg _ _ _ _ _
  have hfe : ∀ t, f t = hV d L W a t ^ 2 * hV d L W t b ^ 2 := fun t => by simp [hf, hF]
  have hswap : ∑ y, hV d L W c y * (Dd⁻¹ * ∑ t, hV d L W y t ^ 3 * f t) =
      Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W t y ^ 3 * hV d L W y c ^ 1 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hV_comm y t, hV_comm c y]; ring
  have h2 : Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W t y ^ 3 * hV d L W y c ^ 1 ≤
      C₁ * ∑ t, f t * hV d L W c t := by
    calc Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W t y ^ 3 * hV d L W y c ^ 1
        ≤ Dd⁻¹ * ∑ t, f t * (C₁ * Dd * hV d L W t c ^ 1) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left (hC₁ L W hW 1 (by norm_num) t c) (hf0 t)) (by positivity)
      _ = C₁ * ∑ t, f t * hV d L W c t := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hV_comm t c, pow_one]
          field_simp
  have h3 : ∑ t, f t * hV d L W c t ≤ C₃ * Dd * hV d L W a b ^ 2 := by
    simp_rw [hfe]
    exact hC₃ L W hW a b c
  have hS0 : 0 ≤ ∑ t, f t * hV d L W c t :=
    Finset.sum_nonneg fun t _ => mul_nonneg (hf0 t) (hV_nonneg _ _)
  unfold hPsi
  rw [← hf]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hswap]
  have e1 : ∑ y, hV d L W c y * f y = ∑ t, f t * hV d L W c t :=
    Finset.sum_congr rfl fun t _ => by ring
  rw [e1]
  calc ∑ t, f t * hV d L W c t + Dd⁻¹ * ∑ t, f t * ∑ y, hV d L W t y ^ 3 * hV d L W y c ^ 1
      ≤ (1 + C₁) * ∑ t, f t * hV d L W c t := by linarith
    _ ≤ (1 + C₁) * (C₃ * Dd * hV d L W a b ^ 2) := mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = _ := by ring

end Marks

/-! ## The leaf summation on a rooted tree -/

section Tree

/-- The labellings of `V` as the value at `ℓ` and a labelling of the other vertices. -/
private theorem hook_split {V α : Type} [Fintype V] [DecidableEq V] [Fintype α]
    (ℓ : V) (F : (V → α) → ℝ) :
    ∑ σ : V → α, F σ = ∑ y : α, ∑ σ' : {w // w ≠ ℓ} → α,
      F (fun w => if h : w = ℓ then y else σ' ⟨w, h⟩) := by
  rw [← (Equiv.funSplitAt ℓ α).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun σ' _ => ?_
  congr 1
  funext w
  rw [Equiv.funSplitAt_symm_apply]

variable {d L W : ℕ} [NeZero L]

/-- The summand of the rooted tree sum: the hook factor `V_{c σ(X)}` at the root `X`, the vertex
weights, and the kernel `V³` on the edges `w — q(w)`. -/
private def hTerm (d L W : ℕ) [NeZero L] (c : Zd d L) {V : Type} [Fintype V] [DecidableEq V]
    (X : V) (q : V → V) (φ : V → Zd d L → ℝ) (σ : V → Zd d L) : ℝ :=
  hV d L W c (σ X) * ((∏ w, φ w (σ w)) *
    ∏ w, (if w = X then 1 else hV d L W (σ w) (σ (q w)) ^ 3))

/-- Removing a leaf `ℓ ≠ X` (no `w` with `q w = ℓ`): the sum over `σ(ℓ)` is the factor
`W^d · W^{−d} Σ_y V_{x y}³ φ_ℓ(y)` at `x = σ(q ℓ)`, multiplied into the weight of `q ℓ`. -/
private theorem hTerm_leaf (c : Zd d L) {V : Type} [Fintype V] [DecidableEq V] (X ℓ : V)
    (hXℓ : X ≠ ℓ) (q : V → V) (hnc : ∀ w, q w ≠ ℓ) (φ : V → Zd d L → ℝ) :
    ∑ σ : V → Zd d L, hTerm d L W c X q φ σ =
      ∑ σ' : {w // w ≠ ℓ} → Zd d L, hTerm d L W c (⟨X, hXℓ⟩ : {w // w ≠ ℓ})
        (fun w => ⟨q w.1, hnc w.1⟩)
        (fun w x => φ w.1 x * (if w.1 = q ℓ then ∑ y, hV d L W x y ^ 3 * φ ℓ y else 1)) σ' := by
  rw [hook_split ℓ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  have hprodq : ∀ x : {w // w ≠ ℓ} → ℝ, ∏ w : {w // w ≠ ℓ},
      (if w.1 = q ℓ then x w else 1) = x ⟨q ℓ, hnc ℓ⟩ := by
    intro x
    rw [Finset.prod_eq_single (⟨q ℓ, hnc ℓ⟩ : {w // w ≠ ℓ})]
    · simp
    · intro w _ hw
      rw [ite_eq_right]
      intro h; exact hw (Subtype.ext h)
    · simp
  set Pφ := ∏ w : {w // w ≠ ℓ}, φ w.1 (σ' w) with hPφ
  set PE := ∏ w : {w // w ≠ ℓ},
    (if w = ⟨X, hXℓ⟩ then 1 else hV d L W (σ' w) (σ' ⟨q w.1, hnc w.1⟩) ^ 3) with hPE
  have hL : ∀ y, hTerm d L W c X q φ (fun w => if h : w = ℓ then y else σ' ⟨w, h⟩) =
      hV d L W c (σ' ⟨X, hXℓ⟩) * (Pφ * PE) * (φ ℓ y * hV d L W (σ' ⟨q ℓ, hnc ℓ⟩) y ^ 3) := by
    intro y
    unfold hTerm
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ ℓ, Fintype.prod_eq_mul_prod_subtype_ne _ ℓ]
    have e1 : ∏ w : {w // w ≠ ℓ}, φ w.1 (if h : w.1 = ℓ then y else σ' ⟨w.1, h⟩) = Pφ :=
      Finset.prod_congr rfl fun w _ => by rw [dite_eq_right w.2]
    have e2 : ∏ w : {w // w ≠ ℓ}, (if w.1 = X then 1 else
        hV d L W (if h : w.1 = ℓ then y else σ' ⟨w.1, h⟩)
          (if h : q w.1 = ℓ then y else σ' ⟨q w.1, h⟩) ^ 3) = PE := by
      refine Finset.prod_congr rfl fun w _ => ?_
      have : (w.1 = X) ↔ (w = ⟨X, hXℓ⟩) := ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
      by_cases hw : w.1 = X
      · rw [ite_eq_left hw, ite_eq_left (this.1 hw)]
      · rw [ite_eq_right hw, ite_eq_right (fun h => hw (this.2 h)), dite_eq_right w.2,
          dite_eq_right (hnc w.1)]
    simp only [dite_true, dite_eq_right hXℓ, dite_eq_right (hnc ℓ),
      ite_eq_right (Ne.symm hXℓ)]
    rw [e1, e2, hV_comm y]
    ring
  simp_rw [hL]
  unfold hTerm
  rw [Finset.prod_mul_distrib, hprodq, ← hPφ, ← hPE, Finset.mul_sum, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- The leaf summation on a rooted tree with `n + 1` vertices (root `X`, parent map `q`, heights
`h`): with vertex weights of the classes `Ψ` of the marks of `x_A` and `x_B`,
`Σ_σ V_{c σ(X)} Π_w φ_w(σ w) Π_{w ≠ X} V³_{σ(w) σ(q w)} ≤ K W^{d(n+1)} V_{𝔞𝔟}²`. -/
private theorem hook_core (d : ℕ) (hd : 8 ≤ d) (n : ℕ) : ∀ K₀ : ℝ, 0 ≤ K₀ → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b c : Zd d L) (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n + 1 → ∀ (X xA xB : V) (q : V → V) (h : V → ℕ), q X = X →
      (∀ w, w ≠ X → h (q w) + 1 = h w) → ∀ φ : V → Zd d L → ℝ, (∀ w y, 0 ≤ φ w y) →
      (∀ w y, φ w y ≤ K₀ * hPsi d L W a b (decide (w = xA)) (decide (w = xB)) y) →
        ∑ σ : V → Zd d L, hTerm d L W c X q φ σ ≤
          K * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * hV d L W a b ^ 2 := by
  obtain ⟨Cr, hCr0, hCr⟩ := hPsi_root d hd
  obtain ⟨Cs, hCs1, hCs⟩ := hPsi_step d hd
  induction n with
  | zero =>
    intro K₀ hK₀
    refine ⟨K₀ * Cr, by positivity, fun L W _ hW a b c V _ _ hcV X xA xB q h hqX hh φ hφ0 hφ => ?_⟩
    have hall : ∀ w : V, w = X := fun w =>
      Fintype.card_le_one_iff.1 (by omega) w X
    have : IsEmpty {w // w ≠ X} := ⟨fun w => w.2 (hall w.1)⟩
    have huniv : (Finset.univ : Finset V) = {X} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun w _ => hall w⟩
    have hterm : ∀ σ : V → Zd d L, hTerm d L W c X q φ σ = hV d L W c (σ X) * φ X (σ X) := by
      intro σ
      unfold hTerm
      rw [huniv, Finset.prod_singleton, Finset.prod_singleton, ite_eq_left rfl, mul_one]
    simp_rw [hterm]
    have hsum : ∀ G : Zd d L → ℝ, ∑ σ : V → Zd d L, G (σ X) = ∑ y, G y := by
      intro G
      rw [hook_split X]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Fintype.sum_unique]
      change G (if h : X = X then y else _) = G y
      rw [dite_eq_left rfl]
    rw [hsum fun y => hV d L W c y * φ X y]
    have hA : xA = X := hall xA
    have hB : xB = X := hall xB
    have hle : ∀ y, hV d L W c y * φ X y ≤ hV d L W c y * (K₀ * hPsi d L W a b true true y) := by
      intro y
      have := hφ X y
      rw [hA, hB] at this
      simp only [decide_true] at this
      exact mul_le_mul_of_nonneg_left this (hV_nonneg _ _)
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    calc ∑ y, hV d L W c y * φ X y
        ≤ ∑ y, hV d L W c y * (K₀ * hPsi d L W a b true true y) :=
          Finset.sum_le_sum fun y _ => hle y
      _ = K₀ * ∑ y, hV d L W c y * hPsi d L W a b true true y := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ K₀ * (Cr * (W : ℝ) ^ (d : ℝ) * hV d L W a b ^ 2) :=
          mul_le_mul_of_nonneg_left (hCr L W hW a b c) hK₀
      _ = _ := by ring
  | succ n ih =>
    intro K₀ hK₀
    obtain ⟨K, hK0, hK⟩ := ih (Cs * K₀ * K₀ + K₀) (by positivity)
    refine ⟨K, hK0, fun L W _ hW a b c V _ _ hcV X xA xB q h hqX hh φ hφ0 hφ => ?_⟩
    have hW0 : (0 : ℝ) < (W : ℝ) ^ (d : ℝ) := by
      have : (1 : ℝ) ≤ W := by exact_mod_cast hW
      positivity
    set Dd := (W : ℝ) ^ (d : ℝ) with hDd
    -- a leaf: a vertex other than the root of greatest height
    have hne : (Finset.univ.filter fun w : V => w ≠ X).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hem
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.2 fun u v => by
        have hu := hem (Finset.mem_univ u); have hv := hem (Finset.mem_univ v)
        push Not at hu hv; rw [hu, hv]
      omega
    obtain ⟨ℓ, hℓS, hℓmax⟩ := Finset.exists_max_image _ h hne
    have hℓX : ℓ ≠ X := (Finset.mem_filter.1 hℓS).2
    have hnc : ∀ w, q w ≠ ℓ := by
      intro w hw
      by_cases hwX : w = X
      · rw [hwX, hqX] at hw; exact hℓX hw.symm
      · have h1 := hh w hwX
        have h2 := hℓmax w (Finset.mem_filter.2 ⟨Finset.mem_univ _, hwX⟩)
        rw [hw] at h1; omega
    rw [hTerm_leaf c X ℓ (Ne.symm hℓX) q hnc φ]
    set cv : Zd d L → ℝ := fun x => ∑ y, hV d L W x y ^ 3 * φ ℓ y with hcv
    -- the new marks
    set xA' : {w // w ≠ ℓ} := if hA : xA = ℓ then ⟨q ℓ, hnc ℓ⟩ else ⟨xA, hA⟩ with hxA'
    set xB' : {w // w ≠ ℓ} := if hB : xB = ℓ then ⟨q ℓ, hnc ℓ⟩ else ⟨xB, hB⟩ with hxB'
    set φ' : {w // w ≠ ℓ} → Zd d L → ℝ :=
      fun w x => φ w.1 x * (if w.1 = q ℓ then Dd⁻¹ * cv x else 1) with hφ'def
    have hcard : Fintype.card {w // w ≠ ℓ} = n + 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    have hcv0 : ∀ x, 0 ≤ cv x := fun x => Finset.sum_nonneg fun y _ =>
      mul_nonneg (pow_nonneg (hV_nonneg _ _) _) (hφ0 ℓ y)
    have hφ'0 : ∀ w y, 0 ≤ φ' w y := by
      intro w y
      simp only [hφ'def]
      split_ifs
      · exact mul_nonneg (hφ0 _ _) (mul_nonneg (by positivity) (hcv0 y))
      · rw [mul_one]; exact hφ0 _ _
    have hmA : ∀ w : {w // w ≠ ℓ}, decide (w = xA') =
        (decide (w.1 = xA) || (decide (w.1 = q ℓ) && decide (ℓ = xA))) := by
      intro w
      rw [show (decide (w.1 = xA) || (decide (w.1 = q ℓ) && decide (ℓ = xA))) =
        decide (w.1 = xA ∨ (w.1 = q ℓ ∧ ℓ = xA)) by simp only [Bool.decide_or, Bool.decide_and]]
      refine decide_eq_decide.2 ?_
      by_cases hA : xA = ℓ
      · have e : xA' = ⟨q ℓ, hnc ℓ⟩ := by rw [hxA', dite_eq_left hA]
        rw [e, Subtype.ext_iff]
        have hw : w.1 ≠ xA := by rw [hA]; exact w.2
        constructor
        · intro h'; exact Or.inr ⟨h', hA.symm⟩
        · rintro (h' | ⟨h', -⟩)
          · exact absurd h' hw
          · exact h'
      · have e : xA' = ⟨xA, hA⟩ := by rw [hxA', dite_eq_right hA]
        rw [e, Subtype.ext_iff]
        constructor
        · intro h'; exact Or.inl h'
        · rintro (h' | ⟨-, h'⟩)
          · exact h'
          · exact absurd h'.symm hA
    have hmB : ∀ w : {w // w ≠ ℓ}, decide (w = xB') =
        (decide (w.1 = xB) || (decide (w.1 = q ℓ) && decide (ℓ = xB))) := by
      intro w
      rw [show (decide (w.1 = xB) || (decide (w.1 = q ℓ) && decide (ℓ = xB))) =
        decide (w.1 = xB ∨ (w.1 = q ℓ ∧ ℓ = xB)) by simp only [Bool.decide_or, Bool.decide_and]]
      refine decide_eq_decide.2 ?_
      by_cases hB : xB = ℓ
      · have e : xB' = ⟨q ℓ, hnc ℓ⟩ := by rw [hxB', dite_eq_left hB]
        rw [e, Subtype.ext_iff]
        have hw : w.1 ≠ xB := by rw [hB]; exact w.2
        constructor
        · intro h'; exact Or.inr ⟨h', hB.symm⟩
        · rintro (h' | ⟨h', -⟩)
          · exact absurd h' hw
          · exact h'
      · have e : xB' = ⟨xB, hB⟩ := by rw [hxB', dite_eq_right hB]
        rw [e, Subtype.ext_iff]
        constructor
        · intro h'; exact Or.inl h'
        · rintro (h' | ⟨-, h'⟩)
          · exact h'
          · exact absurd h'.symm hB
    have hφ' : ∀ w y, φ' w y ≤ (Cs * K₀ * K₀ + K₀) *
        hPsi d L W a b (decide (w = xA')) (decide (w = xB')) y := by
      intro w y
      rw [hmA, hmB]
      simp only [hφ'def]
      by_cases hwq : w.1 = q ℓ
      · rw [ite_eq_left hwq]
        simp only [hwq, decide_true, Bool.true_and]
        have hqℓ : q ℓ ≠ ℓ := hnc ℓ
        have hst := hCs L W hW a b (decide (q ℓ = xA)) (decide (q ℓ = xB)) (decide (ℓ = xA))
          (decide (ℓ = xB)) (by
            intro ⟨h1, h2⟩; simp only [decide_eq_true_eq] at h1 h2; exact hqℓ (h1.trans h2.symm))
          (by
            intro ⟨h1, h2⟩; simp only [decide_eq_true_eq] at h1 h2; exact hqℓ (h1.trans h2.symm))
          K₀ K₀ hK₀ hK₀ (φ ℓ) (hφ0 ℓ) (hφ ℓ) y (φ (q ℓ) y) (hφ0 _ _) (hφ (q ℓ) y)
        have hP := hPsi_nonneg (d := d) (L := L) (W := W) a b
          (decide (q ℓ = xA) || decide (ℓ = xA)) (decide (q ℓ = xB) || decide (ℓ = xB)) y
        calc φ (q ℓ) y * (Dd⁻¹ * cv y)
            ≤ Cs * K₀ * K₀ * hPsi d L W a b (decide (q ℓ = xA) || decide (ℓ = xA))
              (decide (q ℓ = xB) || decide (ℓ = xB)) y := hst
          _ ≤ _ := by nlinarith
      · rw [ite_eq_right hwq, mul_one]
        have hwq' : decide (w.1 = q ℓ) = false := decide_eq_false hwq
        simp only [hwq', Bool.false_and, Bool.or_false]
        have hP := hPsi_nonneg (d := d) (L := L) (W := W) a b (decide (w.1 = xA))
          (decide (w.1 = xB)) y
        have := hφ w.1 y
        have hCK : 0 ≤ Cs * K₀ * K₀ := by positivity
        nlinarith
    have hqX' : (fun w : {w // w ≠ ℓ} => (⟨q w.1, hnc w.1⟩ : {w // w ≠ ℓ}))
        ⟨X, Ne.symm hℓX⟩ = ⟨X, Ne.symm hℓX⟩ := Subtype.ext hqX
    have hh' : ∀ w : {w // w ≠ ℓ}, w ≠ ⟨X, Ne.symm hℓX⟩ →
        h (⟨q w.1, hnc w.1⟩ : {w // w ≠ ℓ}).1 + 1 = h w.1 := by
      intro w hw
      exact hh w.1 fun h' => hw (Subtype.ext h')
    have hmain := hK L W hW a b c {w // w ≠ ℓ} hcard ⟨X, Ne.symm hℓX⟩ xA' xB'
      (fun w => ⟨q w.1, hnc w.1⟩) (fun w => h w.1) hqX' hh' φ' hφ'0 hφ'
    have heq : ∀ σ' : {w // w ≠ ℓ} → Zd d L,
        hTerm d L W c (⟨X, Ne.symm hℓX⟩ : {w // w ≠ ℓ}) (fun w => ⟨q w.1, hnc w.1⟩)
          (fun w x => φ w.1 x * (if w.1 = q ℓ then cv x else 1)) σ' =
        Dd * hTerm d L W c (⟨X, Ne.symm hℓX⟩ : {w // w ≠ ℓ}) (fun w => ⟨q w.1, hnc w.1⟩) φ' σ' := by
      intro σ'
      unfold hTerm
      simp only [hφ'def]
      have hprodq : ∀ x : {w // w ≠ ℓ} → ℝ, ∏ w : {w // w ≠ ℓ},
          (if w.1 = q ℓ then x w else 1) = x ⟨q ℓ, hnc ℓ⟩ := by
        intro x
        rw [Finset.prod_eq_single (⟨q ℓ, hnc ℓ⟩ : {w // w ≠ ℓ})]
        · simp
        · intro w _ hw
          rw [ite_eq_right]
          intro h'; exact hw (Subtype.ext h')
        · simp
      have e1 : ∏ w : {w // w ≠ ℓ}, φ w.1 (σ' w) * (if w.1 = q ℓ then cv (σ' w) else 1) =
          (∏ w : {w // w ≠ ℓ}, φ w.1 (σ' w)) * cv (σ' ⟨q ℓ, hnc ℓ⟩) := by
        rw [Finset.prod_mul_distrib, hprodq fun w => cv (σ' w)]
      have e2 : ∏ w : {w // w ≠ ℓ}, φ w.1 (σ' w) *
          (if w.1 = q ℓ then Dd⁻¹ * cv (σ' w) else 1) =
          (∏ w : {w // w ≠ ℓ}, φ w.1 (σ' w)) * (Dd⁻¹ * cv (σ' ⟨q ℓ, hnc ℓ⟩)) := by
        rw [Finset.prod_mul_distrib, hprodq fun w => Dd⁻¹ * cv (σ' w)]
      rw [e1, e2]
      field_simp
    refine (Finset.sum_congr rfl fun σ' _ => heq σ').trans_le ?_
    rw [← Finset.mul_sum]
    calc Dd * ∑ σ', hTerm d L W c (⟨X, Ne.symm hℓX⟩ : {w // w ≠ ℓ}) (fun w => ⟨q w.1, hnc w.1⟩)
          φ' σ'
        ≤ Dd * (K * Dd ^ (n + 1) * hV d L W a b ^ 2) := mul_le_mul_of_nonneg_left hmain hW0.le
      _ = K * Dd ^ (n + 1 + 1) * hV d L W a b ^ 2 := by ring

end Tree

/-! ## Spanning trees: the parent map and the marked tree sums -/

section Spanning

/-- A spanning tree, rooted at `X`: a parent map `q` with `q X = X`, heights `h` decreasing by one
towards the root, and for every `w ≠ X` an edge `ι w` of the list joining `w` and `q w`. -/
private theorem hook_parent {V : Type} [Fintype V] (E : List (V × V))
    (hE : TreeEdges E) (X : V) : ∃ (q : V → V) (h : V → ℕ) (ι : V → ℕ), q X = X ∧
      (∀ w, w ≠ X → h (q w) + 1 = h w) ∧
      (∀ w, w ≠ X → ∃ hi : ι w < E.length, E[ι w] = (w, q w) ∨ E[ι w] = (q w, w)) := by
  classical
  set G := SimpleGraph.fromRel fun u w => (u, w) ∈ E with hG
  have hP : ∀ v, ∃ n, ∃ p : G.Walk v X, p.length = n := fun v => by
    obtain ⟨p⟩ := hE.2 v X
    exact ⟨p.length, p, rfl⟩
  have hstep : ∀ v, v ≠ X → ∃ w, G.Adj v w ∧ Nat.find (hP w) + 1 = Nat.find (hP v) := by
    intro v hv
    obtain ⟨p, hp⟩ := Nat.find_spec (hP v)
    cases p with
    | nil => exact absurd rfl hv
    | @cons _ w _ hadj p' =>
      refine ⟨w, hadj, ?_⟩
      have h1 : Nat.find (hP w) ≤ p'.length := Nat.find_min' (hP w) ⟨p', rfl⟩
      have h2 : Nat.find (hP v) ≤ Nat.find (hP w) + 1 := by
        obtain ⟨p'', hp''⟩ := Nat.find_spec (hP w)
        exact Nat.find_min' (hP v) ⟨SimpleGraph.Walk.cons hadj p'', by simp [hp'']⟩
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega
  choose qf hqf using hstep
  set q : V → V := fun v => if hv : v = X then X else qf v hv with hq
  have hqe : ∀ v (hv : v ≠ X), q v = qf v hv := fun v hv => by simp [hq, hv]
  have hidx : ∀ v, v ≠ X → ∃ i, ∃ hi : i < E.length, E[i] = (v, q v) ∨ E[i] = (q v, v) := by
    intro v hv
    have hadj := (hqf v hv).1
    rw [← hqe v hv, hG, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hm | hm
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
      exact ⟨i, hi, Or.inl he⟩
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
      exact ⟨i, hi, Or.inr he⟩
  choose ιf hιf using hidx
  refine ⟨q, fun v => Nat.find (hP v), fun v => if hv : v = X then 0 else ιf v hv,
    by simp [hq], fun w hw => ?_, fun w hw => ?_⟩
  · rw [hqe w hw]; exact (hqf w hw).2
  · simp only [hw, dite_false]
    exact hιf w hw

/-- The product over the edges of a spanning tree of a symmetric weight in `[0, 1]` is at most the
product over the parent edges `w — q w`, `w ≠ X`. -/
private theorem hook_edges_le {V : Type} [Fintype V] [DecidableEq V] (E : List (V × V)) (X : V)
    (q : V → V) (h : V → ℕ) (ι : V → ℕ) (hh : ∀ w, w ≠ X → h (q w) + 1 = h w)
    (hι : ∀ w, w ≠ X → ∃ hi : ι w < E.length, E[ι w] = (w, q w) ∨ E[ι w] = (q w, w))
    (f : V → V → ℝ) (hf0 : ∀ x y, 0 ≤ f x y) (hf1 : ∀ x y, f x y ≤ 1)
    (hfs : ∀ x y, f x y = f y x) :
    (E.map fun e => f e.1 e.2).prod ≤ ∏ w, (if w = X then 1 else f w (q w)) := by
  classical
  set κ : {w // w ≠ X} → Fin E.length := fun w => ⟨ι w.1, (hι w.1 w.2).1⟩ with hκ
  have hinj : ∀ t ∈ (Finset.univ : Finset {w // w ≠ X}), ∀ t' ∈ (Finset.univ : Finset {w // w ≠ X}),
      κ t = κ t' → t = t' := by
    intro t _ t' _ htt
    have hi : ι t.1 = ι t'.1 := congrArg Fin.val htt
    obtain ⟨h1, e1⟩ := hι t.1 t.2
    obtain ⟨h2, e2⟩ := hι t'.1 t'.2
    have heq : E[ι t.1] = E[ι t'.1] := by simp only [hi]
    have hs1 := hh t.1 t.2
    have hs2 := hh t'.1 t'.2
    apply Subtype.ext
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rw [e1, e2] at heq <;>
      simp only [Prod.mk.injEq] at heq
    · exact heq.1
    · rw [heq.2] at hs1; rw [← heq.1] at hs2; omega
    · rw [heq.1] at hs1; rw [← heq.2] at hs2; omega
    · exact heq.2
  have hle := prod_map_le_sub E (fun e => f e.1 e.2) (fun e _ => hf0 _ _) (fun e _ => hf1 _ _)
    Finset.univ κ hinj
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ X, ite_eq_left rfl, one_mul]
  refine hle.trans (le_of_eq (Finset.prod_congr rfl fun t _ => ?_))
  rw [ite_eq_right t.2]
  obtain ⟨hi, e⟩ := hι t.1 t.2
  simp only [hκ, Fin.getElem_fin]
  rcases e with e | e <;> rw [e]
  exact hfs _ _

/-- `Π (g e)^k = (Π g e)^k` over a list. -/
private theorem hook_prod_pow {β : Type*} (l : List β) (g : β → ℝ) (k : ℕ) :
    (l.map fun e => g e ^ k).prod = (l.map g).prod ^ k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, mul_pow]

variable {d L W : ℕ} [NeZero L]

private theorem hook_prod_nonneg {V : Type} (E : List (V × V)) (σ : V → Zd d L) (k : ℕ) :
    0 ≤ (E.map fun e => hV d L W (σ e.1) (σ e.2) ^ k).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    exact pow_nonneg (hV_nonneg _ _) _

/-- The marked sum over one spanning tree with the kernel `V³`:
`Σ_σ V_{𝔞 σ(x₀)}² Π_E V³ V_{σ(u) 𝔟}² V_{c σ(v)} ≤ K W^{d(n+1)} V_{𝔞𝔟}²` on `n + 1` vertices. -/
private theorem hook_tree1 (d : ℕ) (hd : 8 ≤ d) (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b c : Zd d L) (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n + 1 → ∀ E : List (V × V), TreeEdges E → ∀ x₀ u v : V,
        ∑ σ : V → Zd d L, hV d L W a (σ x₀) ^ 2 *
          (E.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod * hV d L W (σ u) b ^ 2 *
            hV d L W c (σ v) ≤ K * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * hV d L W a b ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := hook_core d hd n 1 zero_le_one
  refine ⟨K, hK0, fun L W _ hW a b c V _ _ hcV E hE x₀ u v => ?_⟩
  obtain ⟨q, h, ι, hqX, hh, hι⟩ := hook_parent E hE v
  set φ : V → Zd d L → ℝ := fun w y => hF d L W a b (decide (w = x₀)) (decide (w = u)) y with hφ
  have hmain := hK L W hW a b c V hcV v x₀ u q h hqX hh φ (fun w y => hF_nonneg _ _ _ _ _)
    (fun w y => by rw [one_mul]; exact hF_le_hPsi _ _ _ _ _)
  refine le_trans (Finset.sum_le_sum fun σ _ => ?_) hmain
  unfold hTerm
  have hφprod : ∏ w, φ w (σ w) = hV d L W a (σ x₀) ^ 2 * hV d L W (σ u) b ^ 2 := by
    simp only [hφ, hF, decide_eq_true_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  rw [hφprod]
  have hE1 := hook_edges_le E v q h ι hh hι (fun x y => hV d L W (σ x) (σ y) ^ 3)
    (fun x y => pow_nonneg (hV_nonneg _ _) _)
    (fun x y => pow_le_one₀ (hV_nonneg _ _) (hV_le_one (by omega) hW _ _))
    (fun x y => by rw [hV_comm])
  have hA := hV_nonneg (d := d) (L := L) (W := W) a (σ x₀)
  have hB := hV_nonneg (d := d) (L := L) (W := W) (σ u) b
  have hC := hV_nonneg (d := d) (L := L) (W := W) c (σ v)
  calc hV d L W a (σ x₀) ^ 2 * (E.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod *
        hV d L W (σ u) b ^ 2 * hV d L W c (σ v)
      = hV d L W c (σ v) * (hV d L W a (σ x₀) ^ 2 * hV d L W (σ u) b ^ 2) *
        (E.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod := by ring
    _ ≤ hV d L W c (σ v) * (hV d L W a (σ x₀) ^ 2 * hV d L W (σ u) b ^ 2) *
        ∏ w, (if w = v then 1 else hV d L W (σ w) (σ (q w)) ^ 3) :=
        mul_le_mul_of_nonneg_left hE1 (by positivity)
    _ = _ := by ring

/-- The marked sum over a black tree (kernel `V²`) and a blue tree (kernel `V`), by
`s² t ≤ s³ + t³`: at most `K W^{d(n+1)} V_{𝔞𝔟}²` on `n + 1` vertices. -/
private theorem hook_tree2 (d : ℕ) (hd : 8 ≤ d) (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b c : Zd d L) (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n + 1 → ∀ Eb Eu : List (V × V), TreeEdges Eb → TreeEdges Eu →
      ∀ x₀ u v : V,
        ∑ σ : V → Zd d L, hV d L W a (σ x₀) ^ 2 *
          ((Eb.map fun e => hV d L W (σ e.1) (σ e.2) ^ 2).prod *
            (Eu.map fun e => hV d L W (σ e.1) (σ e.2)).prod) * hV d L W (σ u) b ^ 2 *
            hV d L W c (σ v) ≤ K * ((W : ℝ) ^ (d : ℝ)) ^ (n + 1) * hV d L W a b ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := hook_tree1 d hd n
  refine ⟨2 * K, by positivity, fun L W _ hW a b c V _ _ hcV Eb Eu hb hu x₀ u v => ?_⟩
  have h1 := hK L W hW a b c V hcV Eb hb x₀ u v
  have h2 := hK L W hW a b c V hcV Eu hu x₀ u v
  have hpt : ∀ σ : V → Zd d L, hV d L W a (σ x₀) ^ 2 *
      ((Eb.map fun e => hV d L W (σ e.1) (σ e.2) ^ 2).prod *
        (Eu.map fun e => hV d L W (σ e.1) (σ e.2)).prod) * hV d L W (σ u) b ^ 2 *
        hV d L W c (σ v) ≤
      hV d L W a (σ x₀) ^ 2 * (Eb.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod *
        hV d L W (σ u) b ^ 2 * hV d L W c (σ v) +
      hV d L W a (σ x₀) ^ 2 * (Eu.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod *
        hV d L W (σ u) b ^ 2 * hV d L W c (σ v) := by
    intro σ
    have hs := hook_prod_nonneg (W := W) Eb σ 1
    have ht := hook_prod_nonneg (W := W) Eu σ 1
    simp only [pow_one] at hs ht
    have hst := hV_amgm hs ht
    rw [← hook_prod_pow Eb, ← hook_prod_pow Eb, ← hook_prod_pow Eu] at hst
    have hA := hV_nonneg (d := d) (L := L) (W := W) a (σ x₀)
    have hB := hV_nonneg (d := d) (L := L) (W := W) (σ u) b
    have hC := hV_nonneg (d := d) (L := L) (W := W) c (σ v)
    have hX : 0 ≤ hV d L W a (σ x₀) ^ 2 * hV d L W (σ u) b ^ 2 * hV d L W c (σ v) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hst hX]
  calc _ ≤ ∑ σ : V → Zd d L, (hV d L W a (σ x₀) ^ 2 *
        (Eb.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod *
        hV d L W (σ u) b ^ 2 * hV d L W c (σ v) +
      hV d L W a (σ x₀) ^ 2 * (Eu.map fun e => hV d L W (σ e.1) (σ e.2) ^ 3).prod *
        hV d L W (σ u) b ^ 2 * hV d L W c (σ v)) := Finset.sum_le_sum fun σ _ => hpt σ
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

/-- The marked sum in terms of `B`: for a black and a blue spanning tree of `n + 1` vertices,
`Σ_σ B_{𝔞 σ(x₀)} Π_{black} B Π_{blue} B^{1/2} B_{σ(u) 𝔟} B^{1/2}_{c σ(v)}` is at most
`K W^{−(n+1)d/2} B_{𝔞𝔟}`. -/
private theorem hook_treeB (d : ℕ) (hd : 8 ≤ d) (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b c : Zd d L) (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = n + 1 → ∀ Eb Eu : List (V × V), TreeEdges Eb → TreeEdges Eu →
      ∀ x₀ u v : V,
        ∑ σ : V → Zd d L, bB d L W a (σ x₀) *
          (Eb.map fun e => bB d L W (σ e.1) (σ e.2)).prod *
          (Eu.map fun e => Real.sqrt (bB d L W (σ e.1) (σ e.2))).prod * bB d L W (σ u) b *
            Real.sqrt (bB d L W c (σ v)) ≤
          K * ((W : ℝ) ^ ((d : ℝ) / 2))⁻¹ ^ (n + 1) * bB d L W a b := by
  obtain ⟨K, hK0, hK⟩ := hook_tree2 d hd n
  refine ⟨K, hK0, fun L W _ hW a b c V _ _ hcV Eb Eu hb hu x₀ u v => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set S := (W : ℝ) ^ ((d : ℝ) / 2) with hS
  have hS0 : 0 < S := by positivity
  have hDd : (W : ℝ) ^ (d : ℝ) = S * S := by
    rw [hS, ← Real.rpow_add hW0]; ring_nf
  have hB : ∀ x y : Zd d L, bB d L W x y = (S * S)⁻¹ * hV d L W x y ^ 2 := by
    intro x y; rw [hV_sq hW, hDd]; field_simp
  have hsB : ∀ x y : Zd d L, Real.sqrt (bB d L W x y) = S⁻¹ * hV d L W x y := by
    intro x y; unfold hV; rw [← hS, ← mul_assoc, inv_mul_cancel₀ hS0.ne', one_mul]
  have hlb : Eb.length = n := by have := hb.1; omega
  have hlu : Eu.length = n := by have := hu.1; omega
  have hmain := hK L W hW a b c V hcV Eb Eu hb hu x₀ u v
  have hpt : ∀ σ : V → Zd d L, bB d L W a (σ x₀) *
      (Eb.map fun e => bB d L W (σ e.1) (σ e.2)).prod *
      (Eu.map fun e => Real.sqrt (bB d L W (σ e.1) (σ e.2))).prod * bB d L W (σ u) b *
        Real.sqrt (bB d L W c (σ v)) =
      ((S * S)⁻¹ ^ (n + 2) * S⁻¹ ^ (n + 1)) * (hV d L W a (σ x₀) ^ 2 *
        ((Eb.map fun e => hV d L W (σ e.1) (σ e.2) ^ 2).prod *
          (Eu.map fun e => hV d L W (σ e.1) (σ e.2)).prod) * hV d L W (σ u) b ^ 2 *
          hV d L W c (σ v)) := by
    intro σ
    simp_rw [hsB, hB]
    rw [list_prod_map_const_mul, list_prod_map_const_mul, hlb, hlu]
    ring
  simp_rw [hpt]
  rw [← Finset.mul_sum, hB a b]
  calc (S * S)⁻¹ ^ (n + 2) * S⁻¹ ^ (n + 1) * _
      ≤ (S * S)⁻¹ ^ (n + 2) * S⁻¹ ^ (n + 1) * (K * (S * S) ^ (n + 1) * hV d L W a b ^ 2) := by
        rw [hDd] at hmain; exact mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = K * S⁻¹ ^ (n + 1) * ((S * S)⁻¹ * hV d L W a b ^ 2) := by
        have hSS : S * S ≠ 0 := by positivity
        have e : (S * S)⁻¹ ^ (n + 2) * (S * S) ^ (n + 1) = (S * S)⁻¹ := by
          rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ, mul_right_comm, ← mul_pow,
            inv_mul_cancel₀ hSS, one_pow, one_mul]
        calc (S * S)⁻¹ ^ (n + 2) * S⁻¹ ^ (n + 1) * (K * (S * S) ^ (n + 1) * hV d L W a b ^ 2)
            = ((S * S)⁻¹ ^ (n + 2) * (S * S) ^ (n + 1)) * K * S⁻¹ ^ (n + 1) *
              hV d L W a b ^ 2 := by ring
          _ = _ := by rw [e]; ring
end Spanning

/-! ## The absolute-value graph with the hook weight -/

section Graphs

/-- The hook weight is bounded: `𝒢^{abs, w} ≤ K 𝒢^{abs}` for `w ≤ K`. -/
private theorem hook_le_absVal {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (D : Data ι) (e : Fin k → ι) (v : Fin n) (w : ι → ℝ) (K : ℝ) (hwK : ∀ y, w y ≤ K) :
    Γ.absValHook D e v w ≤ K * Γ.absVal D e := by
  unfold Graph.absValHook Graph.absVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hwK _) ?_
  refine mul_nonneg (norm_nonneg _) (List.prod_nonneg fun x hx => ?_)
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact norm_nonneg _

/-- `absVal_le` with the hook weight `w ≥ 0` at the internal atom `v`: the weight `w(s v)` is
carried into the sum over the internal labels. -/
private theorem hook_absVal_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W)
    (D : Data (Zd d L)) (N : ℕ) (E : Matrix (Zd d L) (Zd d L) ℝ) (K₁ C₀ Λ : ℝ) (hK₁ : 1 ≤ K₁)
    (hC₀ : 1 ≤ C₀) (hΛ : 1 ≤ Λ) (hm : ‖D.m‖ ≤ 1)
    (hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = E p q)
    (hE : ∀ p q, E p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ)
    (hΛW : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1)
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
      K₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    {k n : ℕ} (Γ : Graph k n)
    (hth : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (hT : Γ.TKinds N)
    (hxd : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)))
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup) (hbu' : bu.Nodup)
    (hbk : ∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w)
    (hbu : ∀ i ∈ bu, (∃ o, Γ.comps[i].kind = .theta o) ∨ (∃ ch, Γ.comps[i].kind = .G ch) ∨
      ∃ w, Γ.comps[i].kind = .waved w)
    (hboth : ∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w)
    (e : Fin k → Zd d L) (v : Fin n) (wt : Zd d L → ℝ) (hwt : ∀ y, 0 ≤ wt y) :
    Γ.absValHook D e v wt ≤ ‖Γ.coeff.eval D.m‖ *
      ((2 * C₀ * K₁) ^ Γ.comps.length * Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(ordE Γ.comps[i] : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length)) *
      ∑ s : Fin n → Zd d L, wt (s v) *
        (((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)).prod *
          (bu.map fun i => |blueMat d L W C₀ Λ E (blueIdx Γ.comps[i]) (Sum.elim e s Γ.comps[i].x)
            (Sum.elim e s Γ.comps[i].y)|).prod) * wDot Γ (Sum.elim e s)) := by
  unfold Graph.absValHook
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 := prod_le hd hW D N E K₁ C₀ Λ hK₁ hC₀ hΛ hm hEeq hE hΛW hwav Γ hth hT hxd bl bu
    hbk hbu hboth (Sum.elim e s)
  rw [prod_compBnd hW _ C₀ Λ E Γ bl bu hbl hbu' (Sum.elim e s)] at h1
  calc wt (s v) * (‖Γ.coeff.eval D.m‖ * (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod)
      ≤ wt (s v) * (‖Γ.coeff.eval D.m‖ * _) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (hwt _)
    _ = _ := by ring

/-- `dc_main` with the hook weight `w ≥ 0` at the internal atom `v`. -/
private theorem hook_dc (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) {k n : ℕ} (Γ : Graph k n) (hT : Γ.TKinds N)
    (hxd : ∀ c ∈ Γ.comps, c.kind.isSolid = true → ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)))
    (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup) (hbu' : bu.Nodup)
    (hbk : ∀ i ∈ bl, (∃ o, Γ.comps[i].kind = .theta o) ∨ ∃ w, Γ.comps[i].kind = .waved w)
    (hbu : ∀ i ∈ bu, (∃ o, Γ.comps[i].kind = .theta o) ∨ (∃ ch, Γ.comps[i].kind = .G ch) ∨
      ∃ w, Γ.comps[i].kind = .waved w)
    (hboth : ∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (τ₁ : ℝ) (hτ₁ : 0 < τ₁) :
    ∃ M W₀ : ℝ, 0 ≤ M ∧ 1 ≤ W₀ ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Λ : ℝ), 1 ≤ Λ →
        Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) →
        (∀ p q, errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ) → ∀ e : Fin k → Zd d L,
        ∀ (v : Fin n) (wt : Zd d L → ℝ), (∀ y, 0 ≤ wt y) →
          Γ.absValHook (gData (Smat P.ψ W L) z Sig G) e v wt ≤
            M * (W : ℝ) ^ (τ₁ * Γ.comps.length) *
              Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
              (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(ordE Γ.comps[i] : ℝ) * d / 2)) *
              (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length) *
              ∑ s : Fin n → Zd d L, wt (s v) *
                (((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x)
                    (Sum.elim e s Γ.comps[i].y)).prod *
                  (bu.map fun i => |blueMat d L W C₀ Λ (errAbs G z) (blueIdx Γ.comps[i])
                    (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)|).prod) *
                  wDot Γ (Sum.elim e s)) := by
  obtain ⟨K, W₀, hK, hW₀, hin⟩ := gData_inputs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig Γ hT
    τ₁ hτ₁
  obtain ⟨Cc, hCc0, hCc⟩ := coeff_bound κ hκ Γ.coeff
  refine ⟨Cc * (2 * C₀ * K) ^ Γ.comps.length, W₀, by positivity, hW₀,
    fun W L _ hadm hW z hz G Λ hΛ hΛW hE e v wt hwt => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := hW₀.trans hW
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have him := im_pos_of_specDom hW1n hz
  obtain ⟨hwav, hth⟩ := hin W L hadm hW z hz G
  set D := gData (Smat P.ψ W L) z Sig G with hD
  have hm : ‖D.m‖ ≤ 1 := (norm_msc_lt_one him).le
  have hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = errAbs G z p q :=
    fun p q => rfl
  have hΛW' : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1 := by
    calc (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ
        ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hΛW (by positivity)
      _ = 1 := by
          rw [← Real.rpow_add hW0, show -(1 : ℝ) * d / 2 + d / 2 = 0 by ring, Real.rpow_zero]
  have hK₁ : 1 ≤ K * (W : ℝ) ^ τ₁ := by
    have := Real.one_le_rpow hW1 hτ₁.le; nlinarith
  have h := hook_absVal_le (by omega) hW1n D N (errAbs G z) (K * (W : ℝ) ^ τ₁) C₀ Λ hK₁ hC₀ hΛ
    hm hEeq hE hΛW' hwav Γ hth hT hxd bl bu hbl hbu' hbk hbu hboth e v wt hwt
  have hcoeff : ‖Γ.coeff.eval D.m‖ ≤ Cc := hCc z him hz.1 hz.2.2
  have hS0 : (0 : ℝ) ≤ ∑ s : Fin n → Zd d L, wt (s v) *
      (((bl.map fun i => bB d L W (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)).prod *
        (bu.map fun i => |blueMat d L W C₀ Λ (errAbs G z) (blueIdx Γ.comps[i])
          (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y)|).prod) *
        wDot Γ (Sum.elim e s)) := by
    refine Finset.sum_nonneg fun s _ => mul_nonneg (hwt _) (mul_nonneg (mul_nonneg
      (List.prod_nonneg fun a ha => ?_) (List.prod_nonneg fun a ha => ?_))
      (Finset.prod_nonneg fun i _ => (dotInd_mem _ _).1))
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      unfold bB; positivity
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg _
  have hrest : 0 ≤ (2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length *
      Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
      (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(ordE Γ.comps[i] : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length) := by
    have : (0 : ℝ) ≤ Λ := by linarith
    have : (0 : ℝ) ≤ C₀ := by linarith
    have : (0 : ℝ) ≤ K := by linarith
    positivity
  have hpow : (2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length =
      (2 * C₀ * K) ^ Γ.comps.length * (W : ℝ) ^ (τ₁ * Γ.comps.length) := by
    rw [show 2 * C₀ * (K * (W : ℝ) ^ τ₁) = (2 * C₀ * K) * (W : ℝ) ^ τ₁ by ring, mul_pow,
      ← Real.rpow_natCast ((W : ℝ) ^ τ₁), ← Real.rpow_mul hW0.le]
  refine h.trans ?_
  calc ‖Γ.coeff.eval D.m‖ * ((2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length *
          Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(ordE Γ.comps[i] : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length)) * _
      ≤ Cc * ((2 * C₀ * (K * (W : ℝ) ^ τ₁)) ^ Γ.comps.length *
          Λ ^ (∑ i : Fin Γ.comps.length, lamW Γ.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-(ordE Γ.comps[i] : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ ((d : ℝ) / 2)) ^ bu.length)) * _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hrest) hS0
    _ = _ := by rw [hpow]; ring

/-- A product over a list of factors `0 ≤ f ≤ g` is at most the product of the `g`. -/
private theorem hook_list_le {β : Type*} (l : List β) (f g : β → ℝ)
    (h : ∀ i ∈ l, 0 ≤ f i ∧ f i ≤ g i) : (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha := h a List.mem_cons_self
    have ih' := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    have h0 : 0 ≤ (l.map f).prod := List.prod_nonneg fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact (h i (List.mem_cons_of_mem _ hi)).1
    exact mul_le_mul ha.2 ih' h0 (ha.1.trans ha.2)

set_option maxHeartbeats 4000000 in
-- the products over the edges of the trees take long to elaborate
/-- The hook graph sum of a graph whose internal atoms are joined to `⊗` by the `Θ` edge `⊗ – x₀`,
to `⊕` and `⊖` by the solid edges `e₁`, `e₂` at `u₁`, `u₂`, and to no external atom by a waved or
dotted edge, under `|G_{xy} − δ_{xy} m| ≤ W^{τ'} B_{xy}^{1/2}` with `W^{τ'} ≤ Λ`: every blue edge is
at most `B^{1/2}`, the two solid edges give `(W^{τ'}/Λ)² (B_{u₁𝔟} + B_{u₂𝔟})`, and the marked tree
sum gives `W^{−nd/2} B_{𝔞𝔟}`: `𝒢^{abs, hook} ≤ W^τ W^{2τ'} Λ^E W^{−Ed/2} W^{−d/2} B_{𝔞𝔟}`,
`E = Σ ordE − 2n − 2`. -/
private theorem hook_caseT (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) {n C : ℕ} (g : Graph 3 n) (hNo : g.Normal C)
    (hT : g.TKinds N) (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive) (hY : dotY g = ∅)
    (hmix : ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) → (c.x.isRight = true ↔ c.y.isRight = true))
    (x₀ : Fin n) (ia : Fin g.comps.length) (hiaD : g.comps[ia].kind.isDiffusive = true)
    (hia : (g.comps[ia].x = .inl 0 ∧ g.comps[ia].y = .inr x₀) ∨
      (g.comps[ia].x = .inr x₀ ∧ g.comps[ia].y = .inl 0))
    (e₁ e₂ : Fin g.comps.length) (h12 : e₁ ≠ e₂) (u₁ u₂ : Fin n)
    (he₁ : (∃ ch, g.comps[e₁].kind = .G ch) ∧ BAt g.comps[e₁] u₁)
    (he₂ : (∃ ch, g.comps[e₂].kind = .G ch) ∧ BAt g.comps[e₂] u₂) (v : Fin n) (τ : ℝ)
    (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Λ : ℝ), 1 ≤ Λ → Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) →
        (∀ p q, errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ) → ∀ τ' : ℝ, 0 ≤ τ' →
        (W : ℝ) ^ τ' ≤ Λ →
        (∀ x y, errAbs G z x y ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) → ∀ a b c : Zd d L,
          g.absValHook (gData (Smat P.ψ W L) z Sig G) ![a, b, b] v
              (fun y => Real.sqrt (bB d L W c y)) ≤
            (W : ℝ) ^ τ * (W : ℝ) ^ (2 * τ') *
              Λ ^ (∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) - 2 * (n : ℝ) - 2) *
              (W : ℝ) ^ (-((∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) - 2 * (n : ℝ) - 2) *
                d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b := by
  classical
  have hia' : g.comps[ia].x = .inl 0 ∨ g.comps[ia].y = .inl 0 := by
    rcases hia with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨lb, lu, hbl, hbu', hbk, hbu, hboth, hlbI, hluI, hlbT, hluT⟩ :=
    caseT_trees g hNo hT hDC hTD hY hmix x₀ ia hiaD hia' e₁ e₂ h12
      ⟨he₁.1, bInt_of_bAt _ _ he₁.2⟩ ⟨he₂.1, bInt_of_bAt _ _ he₂.2⟩
  have hxd := xdot_of_normal' g hNo
  set m := n - 1 with hm
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact x₀.elim0
  have hcardV : Fintype.card (Fin n) = m + 1 := by rw [Fintype.card_fin]; omega
  have hlb : lb.length = m := by
    have := hlbT.1; rw [List.length_map, hcardV] at this; omega
  have hlu : lu.length = m := by
    have := hluT.1; rw [List.length_map, hcardV] at this; omega
  set τ₁ : ℝ := τ / (4 * ((g.comps.length : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁ℓ : τ₁ * g.comps.length ≤ τ / 4 := by
    rw [hτ₁, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨M, W₁, hM, hW₁, hmain⟩ := hook_dc d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g hT
    hxd (ia :: lb) (lu ++ [e₁, e₂]) hbl hbu' hbk hbu hboth 1 le_rfl τ₁ hτ₁0
  obtain ⟨K, hK0, hK⟩ := hook_treeB d hd m
  obtain ⟨Wa, hWa⟩ := adm_eventually c₀ c₁ hc₀ hc₁ (M * (2 * K)) (by positivity) 0 (τ / 4)
    (by positivity)
  have hcount := count_le g hT (ia :: lb) hbl hbk
  rw [List.length_cons, hlb] at hcount
  refine ⟨max W₁ Wa, fun W L _ hadm hW z hz G Λ hΛ hΛW hE τ' hτ' hτΛ hEpt a b c => ?_⟩
  obtain ⟨hW1n, hWL, hlog⟩ := hWa W L hadm ((le_max_right _ _).trans hW)
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  rw [pow_zero, mul_one] at hlog
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨e3, he3⟩ : ∃ e3 : Fin 3 → Zd d L, e3 = ![a, b, b] := ⟨_, rfl⟩
  have he0 : e3 0 = a := by rw [he3]; rfl
  have he1 : e3 1 = b := by rw [he3]; rfl
  have he2 : e3 2 = b := by rw [he3]; rfl
  rw [← he3]
  have hmain' := hmain W L hadm ((le_max_left _ _).trans hW) z hz G Λ hΛ hΛW hE e3 v
    (fun y => Real.sqrt (bB d L W c y)) (fun y => Real.sqrt_nonneg _)
  set A := blueMat d L W 1 Λ (errAbs G z) with hAdef
  have hτΛ' : (W : ℝ) ^ τ' / Λ ≤ 1 := (div_le_one hΛ0).2 hτΛ
  have hA : ∀ j p q, |A j p q| ≤ Real.sqrt (bB d L W p q) := by
    intro j p q
    by_cases hj : j = 0
    · simp [hAdef, blueMat, hj, abs_of_nonneg (Real.sqrt_nonneg _)]
    · simp only [hAdef, blueMat, hj, ↓reduceIte]
      rw [abs_of_nonneg (div_nonneg (show (0 : ℝ) ≤ errAbs G z _ _ from norm_nonneg _) hΛ0.le)]
      calc errAbs G z p q / Λ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W p q) / Λ :=
            div_le_div_of_nonneg_right (hEpt p q) hΛ0.le
        _ = ((W : ℝ) ^ τ' / Λ) * Real.sqrt (bB d L W p q) := by ring
        _ ≤ 1 * Real.sqrt (bB d L W p q) :=
            mul_le_mul_of_nonneg_right hτΛ' (Real.sqrt_nonneg _)
        _ = _ := one_mul _
  -- the factor of a solid edge from `⊕` or `⊖` to `u`
  have hsolid : ∀ (e : Fin g.comps.length) (u : Fin n), (∃ ch, g.comps[e].kind = .G ch) →
      BAt g.comps[e] u → ∀ s : Fin n → Zd d L,
        |A (blueIdx g.comps[e]) (Sum.elim e3 s g.comps[e].x) (Sum.elim e3 s g.comps[e].y)| ≤
          (W : ℝ) ^ τ' / Λ * Real.sqrt (bB d L W (s u) b) := by
    intro e u ⟨ch, hch⟩ hB s
    have hs : g.comps[e].kind.isSolid = true := by rw [hch]; rfl
    have hidx : blueIdx g.comps[e] = 1 := by rw [blueIdx, ite_eq_left hs]
    rw [hidx]
    simp only [hAdef, blueMat, one_ne_zero, ↓reduceIte]
    rw [abs_of_nonneg (div_nonneg (show (0 : ℝ) ≤ errAbs G z _ _ from norm_nonneg _) hΛ0.le),
      div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hΛ0.le
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      have hx : Sum.elim e3 s g.comps[e].x = b := by
        rcases h1 with h | h <;> rw [h] <;> simp [he1, he2]
      rw [hx]
      refine (hEpt _ _).trans ?_
      rw [bB_comm']
      rfl
    · rw [h2]
      have hy : Sum.elim e3 s g.comps[e].y = b := by
        rcases h1 with h | h <;> rw [h] <;> simp [he1, he2]
      rw [hy]
      exact hEpt _ _
  set Pb : (Fin n → Zd d L) → ℝ := fun s =>
    ((lb.map (edgeT g x₀)).map fun p => bB d L W (s p.1) (s p.2)).prod with hPb
  set Pu : (Fin n → Zd d L) → ℝ := fun s =>
    ((lu.map (edgeT g x₀)).map fun p => Real.sqrt (bB d L W (s p.1) (s p.2))).prod with hPu
  have hPb0 : ∀ s, 0 ≤ Pb s := fun s => List.prod_nonneg fun x hx => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx; exact (bB_pos₁ hW1n _ _).le
  have hPu0 : ∀ s, 0 ≤ Pu s := fun s => List.prod_nonneg fun x hx => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx; exact Real.sqrt_nonneg _
  have hstep : ∀ s : Fin n → Zd d L, Real.sqrt (bB d L W c (s v)) *
      ((((ia :: lb).map fun i : Fin g.comps.length => bB d L W (Sum.elim e3 s g.comps[i].x)
          (Sum.elim e3 s g.comps[i].y)).prod *
        ((lu ++ [e₁, e₂]).map fun i : Fin g.comps.length =>
          |A (blueIdx g.comps[i]) (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)|).prod)
          * wDot g (Sum.elim e3 s)) ≤
      ((W : ℝ) ^ τ' / Λ) ^ 2 *
        (bB d L W a (s x₀) * Pb s * Pu s * bB d L W (s u₁) b * Real.sqrt (bB d L W c (s v)) +
          bB d L W a (s x₀) * Pb s * Pu s * bB d L W (s u₂) b *
            Real.sqrt (bB d L W c (s v))) := by
    intro s
    have hσ : ∀ i : Fin g.comps.length, IntInt g.comps[i] →
        Sum.elim e3 s g.comps[i].x = s (fT x₀ g.comps[i].x) ∧
          Sum.elim e3 s g.comps[i].y = s (fT x₀ g.comps[i].y) := by
      intro i ⟨h1, h2⟩
      constructor
      · rcases hcx : g.comps[i].x with j | j
        · rw [hcx] at h1; simp at h1
        · rfl
      · rcases hcy : g.comps[i].y with j | j
        · rw [hcy] at h2; simp at h2
        · rfl
    have h1 : bB d L W (Sum.elim e3 s g.comps[ia].x) (Sum.elim e3 s g.comps[ia].y) =
        bB d L W a (s x₀) := by
      rcases hia with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]; simp only [Sum.elim_inl, Sum.elim_inr, he0]
      · rw [hx, hy, bB_comm']; simp only [Sum.elim_inl, Sum.elim_inr, he0]
    have h2 : (lb.map fun i : Fin g.comps.length => bB d L W (Sum.elim e3 s g.comps[i].x)
        (Sum.elim e3 s g.comps[i].y)).prod = Pb s := by
      simp only [hPb]
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      obtain ⟨hx, hy⟩ := hσ i (hlbI i hi)
      simp only [Function.comp_apply, edgeT]
      rw [hx, hy]
    have h3 : (lu.map fun i : Fin g.comps.length =>
        |A (blueIdx g.comps[i]) (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)|).prod ≤
        Pu s := by
      refine (hook_list_le lu _ (fun i : Fin g.comps.length => Real.sqrt (bB d L W
        (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)))
        fun i _ => ⟨abs_nonneg _, hA _ _ _⟩).trans (le_of_eq ?_)
      simp only [hPu]
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      obtain ⟨hx, hy⟩ := hσ i (hluI i hi)
      simp only [Function.comp_apply, edgeT]
      rw [hx, hy]
    have hω₁ := hsolid e₁ u₁ he₁.1 he₁.2 s
    have hω₂ := hsolid e₂ u₂ he₂.1 he₂.2 s
    have hB1 := (bB_pos₁ (d := d) (L := L) hW1n (s u₁) b).le
    have hB2 := (bB_pos₁ (d := d) (L := L) hW1n (s u₂) b).le
    have hprod : |A (blueIdx g.comps[e₁]) (Sum.elim e3 s g.comps[e₁].x)
          (Sum.elim e3 s g.comps[e₁].y)| *
        |A (blueIdx g.comps[e₂]) (Sum.elim e3 s g.comps[e₂].x) (Sum.elim e3 s g.comps[e₂].y)| ≤
        ((W : ℝ) ^ τ' / Λ) ^ 2 * (bB d L W (s u₁) b + bB d L W (s u₂) b) := by
      have ham : Real.sqrt (bB d L W (s u₁) b) * Real.sqrt (bB d L W (s u₂) b) ≤
          bB d L W (s u₁) b + bB d L W (s u₂) b := by
        have := amgm (Real.sqrt (bB d L W (s u₁) b)) (Real.sqrt (bB d L W (s u₂) b)) 0
        rw [Real.sq_sqrt hB1, Real.sq_sqrt hB2] at this
        simpa using this
      calc _ ≤ ((W : ℝ) ^ τ' / Λ * Real.sqrt (bB d L W (s u₁) b)) *
            ((W : ℝ) ^ τ' / Λ * Real.sqrt (bB d L W (s u₂) b)) :=
            mul_le_mul hω₁ hω₂ (abs_nonneg _) (by positivity)
        _ = ((W : ℝ) ^ τ' / Λ) ^ 2 * (Real.sqrt (bB d L W (s u₁) b) *
            Real.sqrt (bB d L W (s u₂) b)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ham (by positivity)
    have hsplit : ((ia :: lb).map fun i : Fin g.comps.length => bB d L W
          (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)).prod *
        ((lu ++ [e₁, e₂]).map fun i : Fin g.comps.length =>
          |A (blueIdx g.comps[i]) (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)|).prod =
        bB d L W a (s x₀) * Pb s *
          (lu.map fun i : Fin g.comps.length =>
            |A (blueIdx g.comps[i]) (Sum.elim e3 s g.comps[i].x)
              (Sum.elim e3 s g.comps[i].y)|).prod *
          (|A (blueIdx g.comps[e₁]) (Sum.elim e3 s g.comps[e₁].x)
            (Sum.elim e3 s g.comps[e₁].y)| *
          |A (blueIdx g.comps[e₂]) (Sum.elim e3 s g.comps[e₂].x)
            (Sum.elim e3 s g.comps[e₂].y)|) := by
      rw [List.map_cons, List.prod_cons, List.map_append, List.prod_append, h1, h2]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
      ring
    obtain ⟨hw0, hw1⟩ := wDot_mem g (Sum.elim e3 s)
    rw [hsplit]
    have hLu0 : 0 ≤ (lu.map fun i : Fin g.comps.length =>
        |A (blueIdx g.comps[i]) (Sum.elim e3 s g.comps[i].x)
          (Sum.elim e3 s g.comps[i].y)|).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    have hBa := (bB_pos₁ (d := d) (L := L) hW1n a (s x₀)).le
    have hc0 := Real.sqrt_nonneg (bB d L W c (s v))
    have hP2 : 0 ≤ |A (blueIdx g.comps[e₁]) (Sum.elim e3 s g.comps[e₁].x)
          (Sum.elim e3 s g.comps[e₁].y)| *
        |A (blueIdx g.comps[e₂]) (Sum.elim e3 s g.comps[e₂].x)
          (Sum.elim e3 s g.comps[e₂].y)| := by positivity
    calc Real.sqrt (bB d L W c (s v)) * (bB d L W a (s x₀) * Pb s * _ * _ * wDot g (Sum.elim e3 s))
        ≤ Real.sqrt (bB d L W c (s v)) * (bB d L W a (s x₀) * Pb s * Pu s *
            (((W : ℝ) ^ τ' / Λ) ^ 2 * (bB d L W (s u₁) b + bB d L W (s u₂) b)) * 1) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ hw1 hw0 ?_) hc0
          · exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (mul_nonneg hBa (hPb0 s))) hprod hP2
              (mul_nonneg (mul_nonneg hBa (hPb0 s)) (hPu0 s))
          · have := hPb0 s; have := hPu0 s; positivity
      _ = _ := by ring
  set S1 := ∑ s : Fin n → Zd d L, bB d L W a (s x₀) * Pb s * Pu s * bB d L W (s u₁) b *
    Real.sqrt (bB d L W c (s v)) with hS1
  set S2 := ∑ s : Fin n → Zd d L, bB d L W a (s x₀) * Pb s * Pu s * bB d L W (s u₂) b *
    Real.sqrt (bB d L W c (s v)) with hS2
  have hT1 : S1 ≤ K * ((W : ℝ) ^ ((d : ℝ) / 2))⁻¹ ^ (m + 1) * bB d L W a b :=
    hK L W hW1n a b c (Fin n) hcardV _ _ hlbT hluT x₀ u₁ v
  have hT2 : S2 ≤ K * ((W : ℝ) ^ ((d : ℝ) / 2))⁻¹ ^ (m + 1) * bB d L W a b :=
    hK L W hW1n a b c (Fin n) hcardV _ _ hlbT hluT x₀ u₂ v
  have hSinv : ((W : ℝ) ^ ((d : ℝ) / 2))⁻¹ ^ (m + 1) = (W : ℝ) ^ (-(((m : ℝ) + 1) * d / 2)) := by
    rw [← Real.rpow_neg hW0.le, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
    congr 1; push_cast; ring
  have hS : ∑ s : Fin n → Zd d L, Real.sqrt (bB d L W c (s v)) *
      ((((ia :: lb).map fun i : Fin g.comps.length => bB d L W (Sum.elim e3 s g.comps[i].x)
          (Sum.elim e3 s g.comps[i].y)).prod *
        ((lu ++ [e₁, e₂]).map fun i : Fin g.comps.length =>
          |A (blueIdx g.comps[i]) (Sum.elim e3 s g.comps[i].x) (Sum.elim e3 s g.comps[i].y)|).prod)
          * wDot g (Sum.elim e3 s)) ≤
      ((W : ℝ) ^ τ' / Λ) ^ 2 * (2 * K * (W : ℝ) ^ (-(((m : ℝ) + 1) * d / 2)) * bB d L W a b) := by
    refine (Finset.sum_le_sum fun s _ => hstep s).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← hS1, ← hS2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hSinv]; linarith
  -- the powers
  set E : ℝ := ∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) - 2 * (n : ℝ) - 2 with hEdef
  have hmR : (m : ℝ) = (n : ℝ) - 1 := by rw [hm, Nat.cast_sub hn1]; simp
  have hqE : ((∑ i : Fin g.comps.length, lamW g.comps[i] : ℕ) : ℝ) - 2 ≤ E := by
    rw [hEdef]; push_cast at hcount ⊢; rw [hmR] at hcount; linarith
  have hΛq : Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) / Λ ^ 2 ≤ Λ ^ E := by
    rw [← Real.rpow_natCast, ← Real.rpow_two, ← Real.rpow_sub hΛ0]
    exact Real.rpow_le_rpow_of_exponent_le hΛ hqE
  have hexp : (W : ℝ) ^ (∑ i : Fin g.comps.length, (-(ordE g.comps[i] : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ (ia :: lb).length *
        ((W : ℝ) ^ ((d : ℝ) / 2)) ^ (lu ++ [e₁, e₂]).length) *
      (W : ℝ) ^ (-(((m : ℝ) + 1) * d / 2)) =
      (W : ℝ) ^ (-(E * d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2)) := by
    rw [sum_expo, List.length_cons, List.length_append, hlb, hlu]
    have := pow_combine (W : ℝ) hW0 (∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ)) (d : ℝ)
      ((m : ℝ) + 1) (m + 1) (m + [e₁, e₂].length)
    rw [this, ← Real.rpow_add hW0, hEdef]
    congr 1
    simp only [List.length_cons, List.length_nil]
    push_cast
    rw [hmR]
    ring
  have hWτ₁ : (W : ℝ) ^ (τ₁ * g.comps.length) ≤ (W : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hτ₁ℓ
  have hB0 := (bB_pos₁ (d := d) (L := L) hW1n a b).le
  have h3 : (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) ≤ (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hτ'2 : ((W : ℝ) ^ τ') ^ 2 = (W : ℝ) ^ (2 * τ') := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  calc g.absValHook (gData (Smat P.ψ W L) z Sig G) e3 v (fun y => Real.sqrt (bB d L W c y))
      ≤ _ := hmain'
    _ ≤ M * (W : ℝ) ^ (τ₁ * g.comps.length) * Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) *
          (W : ℝ) ^ (∑ i : Fin g.comps.length, (-(ordE g.comps[i] : ℝ) * d / 2)) *
          (((W : ℝ) ^ (d : ℝ)) ^ (ia :: lb).length *
            ((W : ℝ) ^ ((d : ℝ) / 2)) ^ (lu ++ [e₁, e₂]).length) *
          (((W : ℝ) ^ τ' / Λ) ^ 2 * (2 * K * (W : ℝ) ^ (-(((m : ℝ) + 1) * d / 2)) *
            bB d L W a b)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (M * (2 * K)) * (W : ℝ) ^ (τ₁ * g.comps.length) * ((W : ℝ) ^ τ') ^ 2 *
          (Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) / Λ ^ 2) *
          ((W : ℝ) ^ (∑ i : Fin g.comps.length, (-(ordE g.comps[i] : ℝ) * d / 2)) *
            (((W : ℝ) ^ (d : ℝ)) ^ (ia :: lb).length *
              ((W : ℝ) ^ ((d : ℝ) / 2)) ^ (lu ++ [e₁, e₂]).length) *
            (W : ℝ) ^ (-(((m : ℝ) + 1) * d / 2))) * bB d L W a b := by ring
    _ = (M * (2 * K)) * (W : ℝ) ^ (τ₁ * g.comps.length) * (W : ℝ) ^ (2 * τ') *
          (Λ ^ (∑ i : Fin g.comps.length, lamW g.comps[i]) / Λ ^ 2) *
          ((W : ℝ) ^ (-(E * d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2))) * bB d L W a b := by
        rw [hexp, hτ'2]
    _ ≤ (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (2 * τ') * Λ ^ E *
          ((W : ℝ) ^ (-(E * d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2))) * bB d L W a b := by
        gcongr
    _ ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (2 * τ') * Λ ^ E *
          ((W : ℝ) ^ (-(E * d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2))) * bB d L W a b := by
        gcongr
    _ = _ := by ring

/-- `B_{xy}^{1/2} ≤ W^{−d/2}`. -/
private theorem hook_sqrt_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    Real.sqrt (bB d L W x y) ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 := rpow_mul_sqrt_bB_le hd hW x y
  calc Real.sqrt (bB d L W x y)
      = (W : ℝ) ^ (-((d : ℝ) / 2)) * ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W x y)) := by
        rw [← mul_assoc, ← Real.rpow_add hW0, neg_add_cancel, Real.rpow_zero, one_mul]
    _ ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

/-- The inputs from the entrywise bound `|G_{xy} − δ_{xy} m| ≤ W^{τ'} B_{xy}^{1/2}` with
`W^{τ'} ≥ C₀`: `‖G − m‖_{w;(1,2)} ≤ W^{2τ'}` and `|G_{xy} − δ_{xy} m| ≤ W^{−d/2} W^{2τ'}`. -/
private theorem hook_inputs {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) (hW : 1 ≤ W) (C₀ : ℝ)
    (hC₀w : weakNorm d L W 1 2 (fun x y => Real.sqrt (bB d L W x y) / C₀) ≤ 1) (hC₀ : 1 ≤ C₀)
    (τ' : ℝ) (hC₀τ : C₀ ≤ (W : ℝ) ^ τ') (G : Matrix (Zd d L) (Zd d L) ℂ) (z : ℂ)
    (hG : ∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) :
    weakNorm d L W 1 2 (errAbs G z) ≤ (W : ℝ) ^ (2 * τ') ∧
      ∀ p q, errAbs G z p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ (2 * τ') := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hC0 : 0 < C₀ := by linarith
  have h2 : (W : ℝ) ^ (2 * τ') = (W : ℝ) ^ τ' * (W : ℝ) ^ τ' := by
    rw [← Real.rpow_add hW0]; ring_nf
  constructor
  · have h := weakNorm_le_mul (W := W) 1 2 ((W : ℝ) ^ τ' * C₀) (by positivity) (errAbs G z)
      (fun x y => Real.sqrt (bB d L W x y) / C₀) fun x y => by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ errAbs G z x y from norm_nonneg _),
          abs_of_nonneg (by positivity)]
        calc errAbs G z x y ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y) := hG x y
          _ = (W : ℝ) ^ τ' * C₀ * (Real.sqrt (bB d L W x y) / C₀) := by field_simp
    calc _ ≤ (W : ℝ) ^ τ' * C₀ * weakNorm d L W 1 2
          (fun x y => Real.sqrt (bB d L W x y) / C₀) := h
      _ ≤ (W : ℝ) ^ τ' * C₀ * 1 := mul_le_mul_of_nonneg_left hC₀w (by positivity)
      _ ≤ (W : ℝ) ^ τ' * (W : ℝ) ^ τ' := by rw [mul_one]; gcongr
      _ = _ := h2.symm
  · intro p q
    have hs : Real.sqrt (bB d L W p q) ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) := by
      rw [show (-(1 : ℝ) * d / 2) = -((d : ℝ) / 2) by ring]
      exact hook_sqrt_le hd hW p q
    have h1 : 1 ≤ (W : ℝ) ^ τ' := by linarith
    calc errAbs G z p q ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W p q) := hG p q
      _ ≤ (W : ℝ) ^ τ' * (W : ℝ) ^ (-(1 : ℝ) * d / 2) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (W : ℝ) ^ τ' * (W : ℝ) ^ τ' * (W : ℝ) ^ (-(1 : ℝ) * d / 2) := by
          have : 0 ≤ (W : ℝ) ^ τ' * (W : ℝ) ^ (-(1 : ℝ) * d / 2) := by positivity
          nlinarith
      _ = _ := by rw [h2]; ring

set_option maxHeartbeats 4000000 in
-- the case analysis on the edges at `⊕` and `⊖` takes long to elaborate
/-- The hook graph sum for a graph with an internal atom that is not a `⊕`-recollision graph at
`𝔟₁ = 𝔟₂` and is rooted at the external atoms, under
`|G_{xy} − δ_{xy} m| ≤ W^{τ'} B_{xy}^{1/2}`, for `2τ' ≤ d/2` and `(|n_𝔟 − 2| + 1) 2τ' ≤ τ/2`. -/
private theorem hook_row3 (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (Sig : ℕ → Expansion 2)
    (hSig : SelfEnergiesUpTo d (smatVar P) Sig N) {n C : ℕ} (g : Graph 3 n) (hNo : g.Normal C)
    (hT : g.TKinds N) (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive) (hDA : g.DotsAcyclic)
    (hR : ¬ g.DiagRecoll) (hRo : g.RootedAtExt) (v : Fin n) (τ' : ℝ) (hτ'0 : 0 < τ')
    (hτ'd : 2 * τ' ≤ (d : ℝ) / 2) (τ : ℝ) (hτ : 0 < τ)
    (hττ' : (|(g.diagOrd : ℝ) - 2| + 1) * (2 * τ') ≤ τ / 2) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
        ∀ a b c : Zd d L,
          g.absValHook (gData (Smat P.ψ W L) z Sig G) ![a, b, b] v
              (fun y => Real.sqrt (bB d L W c y)) ≤
            (W : ℝ) ^ τ * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
              (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b := by
  classical
  have hY := dotY_eq_empty g hR
  have hTi := tkind_at g hT
  obtain ⟨C₀, hC₀, hC₀n⟩ := sqrtB_norms d hd
  set Wc : ℝ := max 1 (C₀ ^ (1 / τ')) with hWc
  -- the thresholds common to both cases
  have hcommon : ∀ (W : ℕ), Wc ≤ W → 1 ≤ W ∧ C₀ ≤ (W : ℝ) ^ τ' := by
    intro W hW
    have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
    refine ⟨by exact_mod_cast hW1, ?_⟩
    calc C₀ = (C₀ ^ (1 / τ')) ^ τ' := by
          rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hτ'0.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ τ' :=
          Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hW) hτ'0.le
  have hΛ1 : ∀ (W : ℕ), 1 ≤ W → 1 ≤ (W : ℝ) ^ (2 * τ') := fun W hW =>
    Real.one_le_rpow (by exact_mod_cast hW) (by linarith)
  have hΛd : ∀ (W : ℕ), 1 ≤ W → (W : ℝ) ^ (2 * τ') ≤ (W : ℝ) ^ ((d : ℝ) / 2) := fun W hW =>
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hW) hτ'd
  have hsq : ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ c y : Zd d L,
      Real.sqrt (bB d L W c y) ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) := by
    intro L W _ hW c y
    exact hook_sqrt_le (by omega) hW c y
  -- the case where `𝔟` lies in both trees
  have hcaseB : ∀ c1 c2 : Option (Fin g.comps.length),
      (∀ i, c1 = some i → (∃ o, g.comps[i].kind = .theta o) ∧ BInt g.comps[i]) →
      (∀ i, c2 = some i →
        ((∃ o, g.comps[i].kind = .theta o) ∨ ∃ ch, g.comps[i].kind = .G ch) ∧ BInt g.comps[i]) →
      (∀ i j, c1 = some i → c2 = some j → i ≠ j) →
      ((dotY g).Nonempty ∨ (∃ i, c1 = some i) ∨
        ∃ i : Fin g.comps.length, (∃ w, g.comps[i].kind = .waved w) ∧ BInt g.comps[i]) →
      ((dotY g).Nonempty ∨ (∃ i, c2 = some i) ∨
        ∃ i : Fin g.comps.length, (∃ w, g.comps[i].kind = .waved w) ∧ BInt g.comps[i]) →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
          (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
          ∀ a b c : Zd d L,
            g.absValHook (gData (Smat P.ψ W L) z Sig G) ![a, b, b] v
                (fun y => Real.sqrt (bB d L W c y)) ≤
              (W : ℝ) ^ τ * (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
                (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b := by
    intro c1 c2 hc1 hc2 hc12 hnb hnu
    obtain ⟨W₀, h⟩ := caseB d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g hNo hT hDC hTD c1 c2
      hc1 hc2 hc12 hnb hnu (τ / 2) (by positivity)
    refine ⟨max W₀ Wc, fun W L _ hadm hW z hz G hG a b c => ?_⟩
    obtain ⟨hW1n, hC₀τ⟩ := hcommon W ((le_max_right _ _).trans hW)
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
    obtain ⟨hEw, -⟩ := hook_inputs (by omega) hW1n C₀ (hC₀n L W hW1n).1 hC₀ τ' hC₀τ G z hG
    have hb := h W L hadm ((le_max_left _ _).trans hW) z hz G _ (hΛ1 W hW1n) (hΛd W hW1n) hEw a b
    have hfp := final_pow (W : ℝ) (d : ℝ) 0 (2 * τ') _ (g.diagOrd : ℝ) hW1 (by linarith)
      (diagOrd_le g hNo hTD hDA) (by linarith)
    simp only [zero_add, add_zero] at hfp
    have hB0 : 0 ≤ bB d L W a b := (bB_pos₁ hW1n a b).le
    have hτ'h : |(g.diagOrd : ℝ) - 2| * (2 * τ') ≤ τ / 2 := by
      nlinarith [abs_nonneg ((g.diagOrd : ℝ) - 2)]
    have hle := hook_le_absVal g (gData (Smat P.ψ W L) z Sig G) ![a, b, b] v
      (fun y => Real.sqrt (bB d L W c y)) _ (hsq L W hW1n c)
    refine hle.trans ?_
    calc (W : ℝ) ^ (-((d : ℝ) / 2)) * g.absVal (gData (Smat P.ψ W L) z Sig G) ![a, b, b]
        ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) * ((W : ℝ) ^ (τ / 2) *
            (((W : ℝ) ^ (2 * τ')) ^ (∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) -
              2 * ((Fintype.card {i : Fin n // i ∉ dotY g} : ℝ) + 1)) *
            (W : ℝ) ^ (-((∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) -
              2 * ((Fintype.card {i : Fin n // i ∉ dotY g} : ℝ) + 1)) * d / 2))) *
            bB d L W a b) := by
          refine mul_le_mul_of_nonneg_left (hb.trans (le_of_eq ?_)) (by positivity)
          ring
      _ ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) * ((W : ℝ) ^ (τ / 2) *
            ((W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
              (W : ℝ) ^ (|(g.diagOrd : ℝ) - 2| * (2 * τ'))) * bB d L W a b) := by gcongr
      _ = ((W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (|(g.diagOrd : ℝ) - 2| * (2 * τ'))) *
            (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
            (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b := by ring
      _ ≤ _ := by gcongr; exact half_absorb _ _ _ hW1 hτ'h
  -- a waved edge from `⊕` or `⊖` to an internal atom
  by_cases hW : ∃ i : Fin g.comps.length, (∃ w, g.comps[i].kind = .waved w) ∧ BInt g.comps[i]
  · exact hcaseB none none (by simp) (by simp) (by simp) (Or.inr (Or.inr hW)) (Or.inr (Or.inr hW))
  -- a diffusive edge from `⊕` to an internal atom
  by_cases hD1 : ∃ i : Fin g.comps.length, g.comps[i].kind.isDiffusive = true ∧
      BInt g.comps[i] ∧ (g.comps[i].x = .inl 1 ∨ g.comps[i].y = .inl 1)
  · obtain ⟨i, hiD, hiB, hi1⟩ := hD1
    obtain ⟨j, hj, hjB, hj2⟩ : ∃ j : Fin g.comps.length,
        ((∃ o, g.comps[j].kind = .theta o) ∨ ∃ ch, g.comps[j].kind = .G ch) ∧ BInt g.comps[j] ∧
          (g.comps[j].x = .inl 2 ∨ g.comps[j].y = .inl 2) := by
      rcases hRo.2.2 with ⟨c, hc, hk, hcase⟩ | hdiff
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
        refine ⟨⟨j, hj⟩, Or.inr ⟨_, hk⟩, ?_, ?_⟩
        · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Or.inr h1, h2⟩
          · exact Or.inr ⟨Or.inr h1, h2⟩
        · rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact Or.inl h1
          · exact Or.inr h1
      · obtain ⟨j, hjD, hjB, hj2⟩ := bInt_of_hasDiff g hNo hTD hY 2 (Or.inr rfl) hdiff
        exact ⟨j, Or.inl (tkind_diff _ (hTi _) hjD), hjB, hj2⟩
    refine hcaseB (some i) (some j) ?_ ?_ ?_ (Or.inr (Or.inl ⟨i, rfl⟩))
      (Or.inr (Or.inl ⟨j, rfl⟩))
    · intro k hk
      cases hk
      exact ⟨tkind_diff _ (hTi _) hiD, hiB⟩
    · intro k hk
      cases hk
      exact ⟨hj, hjB⟩
    · intro k l hk hl hkl
      cases hk; cases hl
      subst hkl
      exact not_bInt_both _ hiB hi1 hj2
  -- a diffusive edge from `⊖` to an internal atom
  by_cases hD2 : ∃ i : Fin g.comps.length, g.comps[i].kind.isDiffusive = true ∧
      BInt g.comps[i] ∧ (g.comps[i].x = .inl 2 ∨ g.comps[i].y = .inl 2)
  · obtain ⟨i, hiD, hiB, hi2⟩ := hD2
    obtain ⟨j, hj, hjB, hj1⟩ : ∃ j : Fin g.comps.length,
        ((∃ o, g.comps[j].kind = .theta o) ∨ ∃ ch, g.comps[j].kind = .G ch) ∧ BInt g.comps[j] ∧
          (g.comps[j].x = .inl 1 ∨ g.comps[j].y = .inl 1) := by
      rcases hRo.2.1 with ⟨c, hc, hk, hcase⟩ | hdiff
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
        refine ⟨⟨j, hj⟩, Or.inr ⟨_, hk⟩, ?_, ?_⟩
        · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Or.inl h1, h2⟩
          · exact Or.inr ⟨Or.inl h1, h2⟩
        · rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact Or.inl h1
          · exact Or.inr h1
      · obtain ⟨j, hjD, hjB, hj1⟩ := bInt_of_hasDiff g hNo hTD hY 1 (Or.inl rfl) hdiff
        exact ⟨j, Or.inl (tkind_diff _ (hTi _) hjD), hjB, hj1⟩
    refine hcaseB (some i) (some j) ?_ ?_ ?_ (Or.inr (Or.inl ⟨i, rfl⟩))
      (Or.inr (Or.inl ⟨j, rfl⟩))
    · intro k hk
      cases hk
      exact ⟨tkind_diff _ (hTi _) hiD, hiB⟩
    · intro k hk
      cases hk
      exact ⟨hj, hjB⟩
    · intro k l hk hl hkl
      cases hk; cases hl
      subst hkl
      exact not_bInt_both _ hiB hj1 hi2
  -- the remaining case: two solid edges at `𝔟`
  obtain ⟨e₁, u₁, he₁⟩ : ∃ (e : Fin g.comps.length) (u : Fin n),
      (∃ ch, g.comps[e].kind = .G ch) ∧ BAt g.comps[e] u ∧
        (g.comps[e].x = .inl 1 ∨ g.comps[e].y = .inl 1) := by
    rcases hRo.2.1 with ⟨c, hc, hk, hcase⟩ | hdiff
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨u, hu⟩ : ∃ u, g.comps[j].y = .inr u := by
          rcases h : g.comps[j].y with k | k
          · rw [h] at h2; simp at h2
          · exact ⟨k, rfl⟩
        exact ⟨⟨j, hj⟩, u, ⟨_, hk⟩, Or.inl ⟨Or.inl h1, hu⟩, Or.inl h1⟩
      · obtain ⟨u, hu⟩ : ∃ u, g.comps[j].x = .inr u := by
          rcases h : g.comps[j].x with k | k
          · rw [h] at h2; simp at h2
          · exact ⟨k, rfl⟩
        exact ⟨⟨j, hj⟩, u, ⟨_, hk⟩, Or.inr ⟨Or.inl h1, hu⟩, Or.inr h1⟩
    · obtain ⟨j, hjD, hjB, hj1⟩ := bInt_of_hasDiff g hNo hTD hY 1 (Or.inl rfl) hdiff
      exact absurd ⟨j, hjD, hjB, hj1⟩ hD1
  obtain ⟨e₂, u₂, he₂⟩ : ∃ (e : Fin g.comps.length) (u : Fin n),
      (∃ ch, g.comps[e].kind = .G ch) ∧ BAt g.comps[e] u ∧
        (g.comps[e].x = .inl 2 ∨ g.comps[e].y = .inl 2) := by
    rcases hRo.2.2 with ⟨c, hc, hk, hcase⟩ | hdiff
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨u, hu⟩ : ∃ u, g.comps[j].y = .inr u := by
          rcases h : g.comps[j].y with k | k
          · rw [h] at h2; simp at h2
          · exact ⟨k, rfl⟩
        exact ⟨⟨j, hj⟩, u, ⟨_, hk⟩, Or.inl ⟨Or.inr h1, hu⟩, Or.inl h1⟩
      · obtain ⟨u, hu⟩ : ∃ u, g.comps[j].x = .inr u := by
          rcases h : g.comps[j].x with k | k
          · rw [h] at h2; simp at h2
          · exact ⟨k, rfl⟩
        exact ⟨⟨j, hj⟩, u, ⟨_, hk⟩, Or.inr ⟨Or.inr h1, hu⟩, Or.inr h1⟩
    · obtain ⟨j, hjD, hjB, hj2⟩ := bInt_of_hasDiff g hNo hTD hY 2 (Or.inr rfl) hdiff
      exact absurd ⟨j, hjD, hjB, hj2⟩ hD2
  have h12 : e₁ ≠ e₂ := by
    rintro rfl
    exact not_bInt_both _ (bInt_of_bAt _ _ he₁.2.1) he₁.2.2 he₂.2.2
  have hmix : ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) →
      (c.x.isRight = true ↔ c.y.isRight = true) := by
    intro c hc hw
    obtain ⟨hx0, hy0⟩ := waved_ne g hTD c hc hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    have hext : ∀ u : Atom 3 n, u ≠ .inl 0 → u.isRight = false → u = .inl 1 ∨ u = .inl 2 := by
      intro u hu hr
      rcases u with k | k
      · fin_cases k
        · exact absurd rfl hu
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp at hr
    by_contra hne
    apply hW
    refine ⟨⟨j, hj⟩, hw, ?_⟩
    by_cases hxr : g.comps[j].x.isRight = true
    · have hyr : g.comps[j].y.isRight = false := by
        by_contra h; exact hne ⟨fun _ => by simpa using h, fun _ => hxr⟩
      exact Or.inr ⟨hext _ hy0 hyr, hxr⟩
    · have hyr : g.comps[j].y.isRight = true := by
        by_contra h; exact hne ⟨fun h' => absurd h' hxr, fun h' => absurd h' h⟩
      exact Or.inl ⟨hext _ hx0 (by simpa using hxr), hyr⟩
  -- the edge at `⊗` ends at an internal atom
  obtain ⟨ia, xa, hxa0, hiaD, hia⟩ := exists_aEdge g hNo hTD
  obtain ⟨x₀, hia'⟩ : ∃ x₀ : Fin n, (g.comps[ia].x = .inl 0 ∧ g.comps[ia].y = .inr x₀) ∨
      (g.comps[ia].x = .inr x₀ ∧ g.comps[ia].y = .inl 0) := by
    have hdp := hRo.1.2 _ (List.getElem_mem _) hiaD
    rcases hia with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · obtain ⟨k, hk⟩ := right_of_not_unpinned g hNo hTD hY _ (hdp.1 hx)
      exact ⟨k, Or.inl ⟨hx, hk⟩⟩
    · obtain ⟨k, hk⟩ := right_of_not_unpinned g hNo hTD hY _ (hdp.2 hy)
      exact ⟨k, Or.inr ⟨hk, hy⟩⟩
  obtain ⟨W₀, h⟩ := hook_caseT d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g hNo hT hDC hTD hY
    hmix x₀ ia hiaD hia' e₁ e₂ h12 u₁ u₂ ⟨he₁.1, he₁.2.1⟩ ⟨he₂.1, he₂.2.1⟩ v (τ / 2)
    (by positivity)
  refine ⟨max W₀ Wc, fun W L _ hadm hW z hz G hG a b c => ?_⟩
  obtain ⟨hW1n, hC₀τ⟩ := hcommon W ((le_max_right _ _).trans hW)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨-, hEpt⟩ := hook_inputs (by omega) hW1n C₀ (hC₀n L W hW1n).1 hC₀ τ' hC₀τ G z hG
  have hτΛ : (W : ℝ) ^ τ' ≤ (W : ℝ) ^ (2 * τ') :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hb := h W L hadm ((le_max_left _ _).trans hW) z hz G _ (hΛ1 W hW1n) (hΛd W hW1n) hEpt
    τ' hτ'0.le hτΛ hG a b c
  have hfp := final_pow (W : ℝ) (d : ℝ) 0 (2 * τ') _ (g.diagOrd : ℝ) hW1 (by linarith)
    (diagOrd_le' g hNo hTD hDA hY) (by linarith)
  simp only [zero_add, add_zero] at hfp
  have hτ'h : 2 * τ' + |(g.diagOrd : ℝ) - 2| * (2 * τ') ≤ τ / 2 := by
    nlinarith [abs_nonneg ((g.diagOrd : ℝ) - 2)]
  refine hb.trans ?_
  have hB0 : 0 ≤ bB d L W a b := (bB_pos₁ hW1n a b).le
  calc _ = (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (2 * τ') *
        (((W : ℝ) ^ (2 * τ')) ^ (∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) -
          2 * (n : ℝ) - 2) *
        (W : ℝ) ^ (-((∑ i : Fin g.comps.length, (ordE g.comps[i] : ℝ) - 2 * (n : ℝ) - 2) *
          d / 2))) * ((W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b) := by ring
    _ ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (2 * τ') *
        ((W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
          (W : ℝ) ^ (|(g.diagOrd : ℝ) - 2| * (2 * τ'))) *
          ((W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b) := by gcongr
    _ = ((W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (2 * τ' + |(g.diagOrd : ℝ) - 2| * (2 * τ'))) *
        (W : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2))) *
          (W : ℝ) ^ (-((d : ℝ) / 2)) * bB d L W a b := by
        rw [Real.rpow_add hW0]; ring
    _ ≤ _ := by gcongr; exact half_absorb _ _ _ hW1 hτ'h

end Graphs

/-! ## The hook graph sum -/

/-- **The hook graph sum** `hookGraphSumStmt`, the bound [II, (8.23)–(8.24)] with the extra
weight `B^{1/2}_{c σ(v)}` at an internal atom, where `(L/W)²` becomes `W^{−d/2}`: for `d ≥ 8`,
self-energies `Sig` of orders `4, …, N`, a normal graph `g` with the kinds of [II, Def 3.2], only
diffusive components at `⊗`, doubly connected, with dotted edges forming a forest, not a
`⊕`-recollision graph at `𝔟₁ = 𝔟₂` and rooted at the external atoms, and an internal atom `v`:
for every `τ > 0` there are `τ' > 0` and `W₀` such that along `adm(c₀, c₁)`, for `W ≥ W₀`,
`z ∈ 𝐃(κ, ε)`, every matrix `G` with `|G_{xy} − δ_{xy} m| ≤ W^{τ'} B_{xy}^{1/2}` and all
`𝔞, 𝔟, c`, `Σ_σ K_g(𝔞, 𝔟, 𝔟; σ) B^{1/2}_{c σ(v)} ≤ W^τ W^{−(n_𝔟−2)d/2} W^{−d/2} B_{𝔞𝔟}`. -/
theorem hookGraphSum : hookGraphSumStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig nI C g hNo hT _ hDC hTD hDA hR hRo v τ hτ
  have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set nb : ℝ := (g.diagOrd : ℝ) with hnb
  set τ' : ℝ := min (τ / (4 * (|nb - 2| + 1))) ((d : ℝ) / 8) with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) (by positivity)
  have hτ'1 : τ' ≤ τ / (4 * (|nb - 2| + 1)) := min_le_left _ _
  have hτ'2 : τ' ≤ (d : ℝ) / 8 := min_le_right _ _
  have hτ'd : 2 * τ' ≤ (d : ℝ) / 2 := by linarith
  have hττ' : (|nb - 2| + 1) * (2 * τ') ≤ τ / 2 := by
    have hpos : 0 < |nb - 2| + 1 := by positivity
    calc (|nb - 2| + 1) * (2 * τ') = 2 * ((|nb - 2| + 1) * τ') := by ring
      _ ≤ 2 * ((|nb - 2| + 1) * (τ / (4 * (|nb - 2| + 1)))) := by gcongr
      _ = τ / 2 := by field_simp; ring
  exact ⟨τ', hτ'0, hook_row3 d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g hNo hT hDC hTD hDA
    hR hRo v τ' hτ'0 hτ'd τ hτ hττ'⟩

end RBM8D
