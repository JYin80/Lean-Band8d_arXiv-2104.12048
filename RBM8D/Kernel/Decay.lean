module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import RBM8D.Kernel.PropagatorSymbol
public import RBM8D.Kernel.Profile

@[expose] public section

/-!
# Decay of `S^±`

[I, Lemma 2.2] = [II, Lemma 2.1].
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

/-- The bound `W^{−d} 1(|x − y| ≤ W^{1+τ}) + ⟨x − y⟩^{−D}` of [I, (2.3)], with
`|x − y| = ‖x − y‖_L` and `⟨x − y⟩ = ‖x − y‖_L + W` ([I, (2.2)]). -/
def splusBound {d L : ℕ} (W : ℕ) (τ D : ℝ) (x y : Zd d L) : ℝ :=
  (if (zdistInf d L (x - y) : ℝ) ≤ (W : ℝ) ^ (1 + τ) then ((W : ℝ) ^ d)⁻¹ else 0) +
    ((zdistInf d L (x - y) : ℝ) + W) ^ (-D)

/-! ## Iterated forward differences -/

/-- The `n`-th forward difference with step `h`, `Δ_h^n f`. -/
private def fdiff {M G : Type*} [Add M] [Sub G] (h : M) : ℕ → (M → G) → M → G
  | 0, f => f
  | n + 1, f => fdiff h n (fun t => f (t + h) - f t)

private theorem fdiff_succ {M G : Type*} [Add M] [Sub G] (h : M) (n : ℕ) (f : M → G) :
    fdiff h (n + 1) f = fdiff h n (fun t => f (t + h) - f t) := rfl

/-- Two functions that agree along the stencils have the same `n`-th differences. -/
private theorem fdiff_congr {M M' G : Type*} [AddMonoid M] [AddMonoid M'] [AddCommGroup G]
    (h : M) (h' : M') : ∀ (n : ℕ) (f : M → G) (f' : M' → G) (x : M) (x' : M'),
    (∀ j ≤ n, f (x + j • h) = f' (x' + j • h')) → fdiff h n f x = fdiff h' n f' x'
  | 0, f, f', x, x', hf => by simpa [fdiff] using hf 0 le_rfl
  | n + 1, f, f', x, x', hf => by
    rw [fdiff_succ, fdiff_succ]
    refine fdiff_congr h h' n _ _ x x' fun j hj => ?_
    have h1 := hf j (by omega)
    have h2 := hf (j + 1) (by omega)
    simp only [succ_nsmul, ← add_assoc] at h2
    simp only [h1, h2]

/-- `|Δ_h^n f(x)| ≤ 2^n max_{j ≤ n} |f(x + j h)|`. -/
private theorem norm_fdiff_le {M : Type*} [AddMonoid M] (h : M) :
    ∀ (n : ℕ) (f : M → ℂ) (x : M) (B : ℝ), (∀ j ≤ n, ‖f (x + j • h)‖ ≤ B) →
      ‖fdiff h n f x‖ ≤ 2 ^ n * B
  | 0, f, x, B, hf => by simpa [fdiff] using hf 0 le_rfl
  | n + 1, f, x, B, hf => by
    rw [fdiff_succ]
    have := norm_fdiff_le h n (fun t => f (t + h) - f t) x (2 * B) fun j hj => by
      have h1 := hf j (by omega)
      have h2 := hf (j + 1) (by omega)
      simp only [succ_nsmul, ← add_assoc] at h2
      calc ‖f (x + j • h + h) - f (x + j • h)‖ ≤ ‖f (x + j • h + h)‖ + ‖f (x + j • h)‖ :=
            norm_sub_le _ _
        _ ≤ 2 * B := by linarith
    calc _ ≤ 2 ^ n * (2 * B) := this
      _ = 2 ^ (n + 1) * B := by ring

/-- The iterated mean value inequality: `|Δ_s^n φ(y)| ≤ s^n sup_{[y, y + ns]} |φ^{(n)}|`. -/
private theorem norm_fdiff_real_le (s : ℝ) (hs : 0 ≤ s) :
    ∀ (n : ℕ) (φ : ℝ → ℂ), (∀ m : ℕ, ContDiff ℝ m φ) → ∀ (y B : ℝ),
      (∀ u ∈ Set.Icc y (y + n * s), ‖iteratedDeriv n φ u‖ ≤ B) → ‖fdiff s n φ y‖ ≤ s ^ n * B
  | 0, φ, hφ, y, B, hB => by
    simpa [fdiff] using hB y ⟨le_rfl, by simp⟩
  | n + 1, φ, hφ, y, B, hB => by
    rw [fdiff_succ]
    have hφ' : ∀ m : ℕ, ContDiff ℝ m (fun t => φ (t + s) - φ t) := fun m =>
      ((hφ m).comp (contDiff_id.add contDiff_const)).sub (hφ m)
    have key : ∀ u ∈ Set.Icc y (y + n * s),
        ‖iteratedDeriv n (fun t => φ (t + s) - φ t) u‖ ≤ s * B := by
      intro u hu
      have e1 : iteratedDeriv n (fun t => φ (t + s) - φ t) u =
          iteratedDeriv n φ (u + s) - iteratedDeriv n φ u := by
        have := iteratedDeriv_sub (n := n) (x := u) (f := fun t => φ (t + s)) (g := φ)
          ((hφ n).comp (contDiff_id.add contDiff_const)).contDiffAt (hφ n).contDiffAt
        rw [show (fun t => φ (t + s) - φ t) = (fun t => φ (t + s)) - φ from rfl, this,
          iteratedDeriv_comp_add_const]
      rw [e1]
      have hdiff : Differentiable ℝ (iteratedDeriv n φ) :=
        (hφ (n + 1)).differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)
      have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := u + s)
        (f := iteratedDeriv n φ) (f' := iteratedDeriv (n + 1) φ) (C := B)
        (fun x _ => by
          rw [iteratedDeriv_succ]
          exact (hdiff x).hasDerivAt.hasDerivWithinAt)
        (fun x hx => hB x ⟨by linarith [hu.1, hx.1], by
          have := hx.2
          have := hu.2
          push_cast
          nlinarith⟩)
        (u + s) ⟨by linarith, le_rfl⟩
      calc _ ≤ B * (u + s - u) := hmv
        _ = s * B := by ring
    calc _ ≤ s ^ n * (s * B) := norm_fdiff_real_le s hs n _ hφ' y (s * B) key
      _ = s ^ (n + 1) * B := by ring

/-! ## Summation by parts on `Z_L^d` -/

section Lattice

variable {d L : ℕ}

/-- Summation by parts on `Z_L^d`:
`Σ_k (Δ_e^n f)(k) e^{i p_k·z} = (e^{−i p_e·z} − 1)^n Σ_k f(k) e^{i p_k·z}`. -/
private theorem sum_fdiff_zchar [NeZero L] (e z : Zd d L) :
    ∀ (n : ℕ) (f : Zd d L → ℂ),
      ∑ k, fdiff e n f k * zchar k z = (zchar (-e) z - 1) ^ n * ∑ k, f k * zchar k z
  | 0, f => by simp [fdiff]
  | n + 1, f => by
    rw [fdiff_succ, sum_fdiff_zchar e z n, pow_succ, mul_assoc]
    congr 1
    have hshift : ∑ k, f (k + e) * zchar k z = zchar (-e) z * ∑ k, f k * zchar k z := by
      have h1 : ∑ k, f (k + e) * zchar k z = ∑ k, f k * zchar (k + -e) z :=
        Fintype.sum_equiv (Equiv.addRight e) _ _ fun k => by simp
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [zchar_comm, zchar_add, zchar_comm z k, zchar_comm z (-e)]
      ring
    simp only [sub_mul, Finset.sum_sub_distrib, hshift]
    ring

/-- The character at `−e_i` is `e^{−2πi z_i/L}`. -/
private theorem zchar_neg_single [NeZero L] (i : Fin d) (z : Zd d L) :
    zchar (-(Pi.single i 1 : Zd d L)) z = ZMod.stdAddChar (-(z i)) := by
  rw [zchar, Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

/-- `|e^{−2πi z_i/L} − 1| ≥ 4 |[z_i]_L| / L` (Jordan's inequality). -/
private theorem norm_zchar_neg_single_sub_one [NeZero L] (i : Fin d) (z : Zd d L) :
    4 * |((z i).valMinAbs : ℝ)| / L ≤ ‖zchar (-(Pi.single i 1 : Zd d L)) z - 1‖ := by
  set v := (z i).valMinAbs with hv
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hvz : -(z i) = (((-v : ℤ)) : ZMod L) := by
    push_cast
    rw [hv, ZMod.coe_valMinAbs]
  have hmem := ZMod.valMinAbs_mem_Ioc (z i)
  have hv2 : |(v : ℝ)| * 2 ≤ L := by
    have h1 : -(L : ℤ) < v * 2 := hmem.1
    have h2 : v * 2 ≤ (L : ℤ) := hmem.2
    have : |v| * 2 ≤ (L : ℤ) := by
      rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
    exact_mod_cast this
  rw [zchar_neg_single, hvz, ZMod.stdAddChar_coe]
  have he : cexp (2 * ↑Real.pi * I * ↑(-v) / ↑L) =
      cexp (I * ↑(2 * Real.pi * ((-v : ℤ) : ℝ) / L)) := by
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have hx : 2 * Real.pi * ((-v : ℤ) : ℝ) / L / 2 = -(Real.pi * v / L) := by
    push_cast
    ring
  rw [hx, Real.sin_neg, abs_neg]
  have hpi := Real.pi_pos
  have hsin : 2 * |(v : ℝ)| / L ≤ |Real.sin (Real.pi * v / L)| := by
    have hx0 : 0 ≤ Real.pi * |(v : ℝ)| / L := by positivity
    have hx1 : Real.pi * |(v : ℝ)| / L ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have he2 : 2 / Real.pi * (Real.pi * |(v : ℝ)| / L) = 2 * |(v : ℝ)| / L := by
      field_simp
    rw [he2] at hj
    have habs : Real.sin (Real.pi * |(v : ℝ)| / L) ≤ |Real.sin (Real.pi * v / L)| := by
      rcases abs_cases (v : ℝ) with ⟨h, h0⟩ | ⟨h, h0⟩
      · rw [h]
        exact le_abs_self _
      · rw [h, show Real.pi * -(v : ℝ) / L = -(Real.pi * v / L) by ring, Real.sin_neg]
        exact neg_le_abs _
    linarith
  calc 4 * |(v : ℝ)| / L = 2 * (2 * |(v : ℝ)| / L) := by ring
    _ ≤ 2 * |Real.sin (Real.pi * v / L)| := by linarith

/-- Moving `u ∈ Z_L` up by `j` without passing `L/2` moves its centred representative by `j`. -/
private theorem valMinAbs_add_nat_of_le [NeZero L] (u : ZMod L) (j : ℕ)
    (h : (u.valMinAbs + j) * 2 ≤ L) : (u + j).valMinAbs = u.valMinAbs + j := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by push_cast; rfl, ?_, h⟩
  have := (ZMod.valMinAbs_mem_Ioc u).1
  omega

/-- Moving `u ∈ Z_L` up by `j ≤ L/4` past `L/2` moves its centred representative by `j − L`. -/
private theorem valMinAbs_add_nat_of_gt [NeZero L] (u : ZMod L) (j : ℕ)
    (h : (L : ℤ) < (u.valMinAbs + j) * 2) (hj : 4 * j ≤ L) :
    (u + j).valMinAbs = u.valMinAbs + j - L := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by push_cast; rw [ZMod.natCast_self, sub_zero], ?_, ?_⟩
  · omega
  · have := (ZMod.valMinAbs_mem_Ioc u).2
    omega

/-- If the stencil `u, u + 1, …, u + n` passes `L/2` and `4n ≤ L`, every point of it has centred
representative of modulus at least `L/4`. -/
private theorem le_four_mul_abs_valMinAbs [NeZero L] (u : ZMod L) (n j : ℕ) (hn : 4 * n ≤ L)
    (hj : j ≤ n) (hc : (L : ℤ) < (u.valMinAbs + n) * 2) :
    (L : ℤ) ≤ 4 * |(u + j).valMinAbs| := by
  have hu := ZMod.valMinAbs_mem_Ioc u
  have h1 := hu.1
  have h2 := hu.2
  by_cases hle : (u.valMinAbs + j) * 2 ≤ L
  · rw [valMinAbs_add_nat_of_le u j hle]
    have : (L : ℤ) ≤ 4 * (u.valMinAbs + j) := by omega
    exact this.trans (by have := le_abs_self (u.valMinAbs + (j : ℤ)); omega)
  · rw [valMinAbs_add_nat_of_gt u j (by omega) (by omega)]
    have : (L : ℤ) ≤ 4 * -(u.valMinAbs + j - L) := by omega
    exact this.trans (by have := neg_le_abs (u.valMinAbs + (j : ℤ) - L); omega)

/-- Shifting `k` by `j e_i` without passing `L/2` in the coordinate `i` shifts the frequency
`p_k` by `2πj/L` in the direction `e_i`. -/
private theorem zfreq_add_single [NeZero L] (k : Zd d L) (i : Fin d) (j : ℕ)
    (h : ((k i).valMinAbs + j) * 2 ≤ L) :
    zfreq (k + j • (Pi.single i 1 : Zd d L)) =
      zfreq k + (2 * Real.pi * j / L) • EuclideanSpace.single i (1 : ℝ) := by
  ext l
  by_cases hl : l = i
  · subst hl
    simp [zfreq, valMinAbs_add_nat_of_le _ j h]
    ring
  · simp [zfreq, hl]

/-! ## Lattice sums of `(1 + |W p|)^{−2d}` -/

private theorem sum_range_inv_sq_succ_le (β : ℝ) (hβ : 0 < β) :
    ∀ N : ℕ, ∑ j ∈ Finset.range N, ((1 + β * (j + 1)) ^ 2)⁻¹ ≤ 1 / β - 1 / (β * (1 + β * N))
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_range_inv_sq_succ_le β hβ N
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have key : ((1 + β * (N + 1)) ^ 2)⁻¹ ≤
        1 / (β * (1 + β * N)) - 1 / (β * (1 + β * ((N + 1 : ℕ) : ℝ))) := by
      push_cast
      have h1 : 0 < 1 + β * N := by positivity
      have h2 : 0 < 1 + β * (N + 1) := by positivity
      rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 * (β * (1 + β * (N + 1))) - β * (1 + β * N) * 1) * (1 + β * (N + 1)) ^ 2 -
          1 * (β * (1 + β * N) * (β * (1 + β * (N + 1)))) = β ^ 3 * (1 + β * (N + 1)) := by ring
      nlinarith [pow_pos hβ 3]
    linarith

/-- `Σ_{0 ≤ j < N} (1 + βj)^{−2} ≤ 1 + 1/β`. -/
private theorem sum_range_inv_sq_le (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    ∑ j ∈ Finset.range N, ((1 + β * j) ^ 2)⁻¹ ≤ 1 + 1 / β := by
  rcases N with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · rw [Finset.sum_range_succ']
    have h := sum_range_inv_sq_succ_le β hβ N
    have h2 : 0 ≤ 1 / (β * (1 + β * N)) := by positivity
    push_cast
    simp only [mul_zero, add_zero, one_pow, inv_one]
    linarith

/-- `Σ_{u ∈ Z_L} (1 + β|[u]_L|)^{−2} ≤ 2(1 + 1/β)`. -/
private theorem sum_zmod_inv_sq_le [NeZero L] (β : ℝ) (hβ : 0 < β) :
    ∑ u : ZMod L, ((1 + β * |((u.valMinAbs : ℤ) : ℝ)|) ^ 2)⁻¹ ≤ 2 * (1 + 1 / β) := by
  set g : ℕ → ℝ := fun j => ((1 + β * j) ^ 2)⁻¹ with hg
  have hrw : ∀ u : ZMod L, ((1 + β * |((u.valMinAbs : ℤ) : ℝ)|) ^ 2)⁻¹ = g u.valMinAbs.natAbs := by
    intro u
    simp only [hg, Nat.cast_natAbs, Int.cast_abs]
  simp only [hrw]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range L)
    (g := fun u : ZMod L => u.valMinAbs.natAbs) (fun u _ => by
      have := ZMod.natAbs_valMinAbs_le u
      have hL := Nat.pos_of_ne_zero (NeZero.ne L)
      simp only [Finset.mem_range]
      omega)]
  refine (Finset.sum_le_sum (g := fun j => 2 * g j) fun j _ => ?_).trans ?_
  · rw [Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.mp hu).2], Finset.sum_const,
      nsmul_eq_mul]
    have hg0 : 0 ≤ g j := by simp only [hg]; positivity
    refine mul_le_mul_of_nonneg_right ?_ hg0
    have key : ∀ T : Finset (ZMod L), (∀ u ∈ T, u.valMinAbs.natAbs = j) → (T.card : ℝ) ≤ 2 := by
      intro T hT
      have hcard := (Finset.card_le_card (s := T) (t := {(j : ZMod L), -(j : ZMod L)})
        fun u hu => by
          have h := hT u hu
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases Int.natAbs_eq_iff.mp h with h' | h'
          · left
            rw [← ZMod.coe_valMinAbs u, h']
            simp
          · right
            rw [← ZMod.coe_valMinAbs u, h']
            simp).trans Finset.card_le_two
      exact_mod_cast hcard
    exact key _ fun u hu => (Finset.mem_filter.mp hu).2
  · rw [← Finset.mul_sum]
    have := sum_range_inv_sq_le β hβ L
    simp only [hg] at *
    linarith

/-- `L^{−d} Σ_k (1 + |W p_k|)^{−2d} ≤ 3^d W^{−d}` for `1 ≤ W ≤ L`. -/
private theorem lattice_sum_le [NeZero L] (W : ℕ) (hW : 1 ≤ W) (hWL : W ≤ L) :
    ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ ≤
      3 ^ d * ((W : ℝ) ^ d)⁻¹ := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hWL' : (W : ℝ) ≤ L := by exact_mod_cast hWL
  set β : ℝ := 2 * Real.pi * W / L with hβ
  have hβpos : 0 < β := by positivity
  set f : ZMod L → ℝ := fun u => ((1 + β * |((u.valMinAbs : ℤ) : ℝ)|) ^ 2)⁻¹ with hf
  have hpt : ∀ k : Zd d L, ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ ≤ ∏ i, f (k i) := by
    intro k
    set q := (W : ℝ) • zfreq k
    have hqi : ∀ i, |q.ofLp i| = β * |((k i).valMinAbs : ℝ)| := by
      intro i
      simp only [q, zfreq, PiLp.smul_apply, smul_eq_mul, hβ]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_div, abs_mul, abs_of_nonneg hLpos.le,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      ring
    rw [hf]
    simp only
    rw [Finset.prod_inv_distrib]
    apply inv_anti₀ (by positivity)
    calc ∏ i, (1 + β * |(((k i).valMinAbs : ℤ) : ℝ)|) ^ 2 ≤ ∏ _i : Fin d, (1 + ‖q‖) ^ 2 := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          have h1 := PiLp.norm_apply_le q i
          rw [Real.norm_eq_abs, hqi] at h1
          have h0 : 0 ≤ β * |(((k i).valMinAbs : ℤ) : ℝ)| := by positivity
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = (1 + ‖q‖) ^ (2 * d) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← pow_mul, mul_comm]
  have hsum : ∑ k : Zd d L, ∏ i, f (k i) = (∑ u : ZMod L, f u) ^ d := by
    rw [← Fintype.prod_sum (fun (_ : Fin d) (u : ZMod L) => f u), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have h1 := sum_zmod_inv_sq_le (L := L) β hβpos
  have hS0 : 0 ≤ ∑ u : ZMod L, f u := Finset.sum_nonneg fun u _ => by simp only [hf]; positivity
  calc ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹
      ≤ ((L : ℝ) ^ d)⁻¹ * (∑ u : ZMod L, f u) ^ d := by
        rw [← hsum]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpt k) (by positivity)
    _ = ((∑ u : ZMod L, f u) / L) ^ d := by rw [div_pow, div_eq_inv_mul]
    _ ≤ (3 / W) ^ d := by
        refine pow_le_pow_left₀ (by positivity) ?_ d
        rw [div_le_div_iff₀ hLpos hWpos]
        have hpi : 2 ≤ Real.pi := Real.two_le_pi
        have h2 : 2 * (1 + 1 / β) * W ≤ 3 * L := by
          rw [hβ]
          field_simp
          nlinarith
        nlinarith
    _ = 3 ^ d * ((W : ℝ) ^ d)⁻¹ := by rw [div_pow, div_eq_mul_inv]

end Lattice

/-! ## The function `F(t) = wt/(1 − wt)` on the range of the symbol -/

section Resolvent

/-- The constant `c_F = min(1/2, δ/2, c′/2)`, a lower bound for `|1 − wt|` on
`t ∈ [−1 + c′/2, 1]` when `|w| ≤ 1` and `|1 − w| ≥ δ`. -/
private def cF (δ c' : ℝ) : ℝ := min (min (1 / 2) (δ / 2)) (c' / 2)

private theorem cF_pos {δ c' : ℝ} (hδ : 0 < δ) (hc' : 0 < c') : 0 < cF δ c' := by
  unfold cF
  positivity

private theorem cF_le_half (δ c' : ℝ) : cF δ c' ≤ 1 / 2 :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- `|1 − wt| ≥ c_F` for `t ∈ [−1 + c′/2, 1]`, `|w| ≤ 1`, `|1 − w| ≥ δ`. -/
private theorem cF_le_norm_one_sub {δ c' : ℝ} (hδ : 0 < δ) (hc' : 0 < c') {w : ℂ}
    (hw : ‖w‖ ≤ 1) (hδw : δ ≤ ‖1 - w‖) {t : ℝ} (ht0 : -1 + c' / 2 ≤ t) (ht1 : t ≤ 1) :
    cF δ c' ≤ ‖1 - w * t‖ := by
  have hc0 := cF_pos hδ hc'
  have hc1 : cF δ c' ≤ 1 / 2 := cF_le_half δ c'
  have hc2 : cF δ c' ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : cF δ c' ≤ c' / 2 := min_le_right _ _
  rcases le_or_gt 0 t with ht | ht
  · have hn : ‖1 - w * t‖ ^ 2 = (1 - w.re * t) ^ 2 + (w.im * t) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
      have h := Complex.sq_norm w
      rw [Complex.normSq_apply] at h
      nlinarith [norm_nonneg w]
    have hd2 : δ ^ 2 ≤ (1 - w.re) ^ 2 + w.im ^ 2 := by
      have h := Complex.sq_norm (1 - w)
      rw [Complex.normSq_apply] at h
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at h
      nlinarith [norm_nonneg (1 - w)]
    have hexp : (1 - w.re * t) ^ 2 + (w.im * t) ^ 2 - ((1 - t) ^ 2 + t * δ ^ 2) =
        t * (((1 - w.re) ^ 2 + w.im ^ 2 - δ ^ 2) + (1 - (w.re ^ 2 + w.im ^ 2)) * (1 - t)) := by
      ring
    have hge : (1 - t) ^ 2 + t * δ ^ 2 ≤ ‖1 - w * t‖ ^ 2 := by
      rw [hn]
      have : 0 ≤ t * (((1 - w.re) ^ 2 + w.im ^ 2 - δ ^ 2) +
          (1 - (w.re ^ 2 + w.im ^ 2)) * (1 - t)) :=
        mul_nonneg ht (add_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
      linarith
    have hsq : cF δ c' ^ 2 ≤ ‖1 - w * t‖ ^ 2 := by
      rcases le_or_gt t (1 / 2) with h | h
      · nlinarith
      · nlinarith
    exact (pow_le_pow_iff_left₀ hc0.le (norm_nonneg _) two_ne_zero).mp hsq
  · have h1 : ‖(w * t : ℂ)‖ ≤ -t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht]
      nlinarith [norm_nonneg w]
    have h2 := norm_sub_norm_le (1 : ℂ) (w * t)
    rw [norm_one] at h2
    linarith

/-- `F(t) = wt/(1 − wt)`, the symbol of `S^+` as a function of the symbol of `S`. -/
private def Fw (w t : ℂ) : ℂ := w * t / (1 - w * t)

/-- `g(t) = (1 − wt)⁻¹ = 1 + F(t)` on the real line. -/
private def gw (w : ℂ) (t : ℝ) : ℂ := (1 - w * t)⁻¹

private theorem Fw_eq_gw {w : ℂ} {t : ℝ} (h : (1 : ℂ) - w * t ≠ 0) : Fw w t = -1 + gw w t := by
  unfold Fw gw
  field_simp
  ring

private theorem norm_Fw_le {w t : ℂ} {c : ℝ} (hc : 0 < c) (hw : ‖w‖ ≤ 1) (h : c ≤ ‖1 - w * t‖) :
    ‖Fw w t‖ ≤ ‖t‖ / c := by
  unfold Fw
  rw [norm_div, norm_mul]
  have hpos : 0 < ‖1 - w * t‖ := lt_of_lt_of_le hc h
  calc ‖w‖ * ‖t‖ / ‖1 - w * t‖ ≤ ‖t‖ / ‖1 - w * t‖ := by
        gcongr
        nlinarith [norm_nonneg t]
    _ ≤ ‖t‖ / c := div_le_div_of_nonneg_left (norm_nonneg _) hc h

private theorem norm_Fw_sub_le {w a b : ℂ} {c : ℝ} (hc : 0 < c) (hw : ‖w‖ ≤ 1)
    (ha : c ≤ ‖1 - w * a‖) (hb : c ≤ ‖1 - w * b‖) : ‖Fw w a - Fw w b‖ ≤ ‖a - b‖ / c ^ 2 := by
  have ha0 : (1 : ℂ) - w * a ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hc ha)
  have hb0 : (1 : ℂ) - w * b ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hc hb)
  have he : Fw w a - Fw w b = w * (a - b) / ((1 - w * a) * (1 - w * b)) := by
    unfold Fw
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_mul]
  have hpa : 0 < ‖1 - w * a‖ := lt_of_lt_of_le hc ha
  have hpb : 0 < ‖1 - w * b‖ := lt_of_lt_of_le hc hb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ‖w‖ * ‖a - b‖ * c ^ 2 ≤ ‖a - b‖ * c ^ 2 := by
    calc ‖w‖ * ‖a - b‖ * c ^ 2 = ‖w‖ * (‖a - b‖ * c ^ 2) := by ring
      _ ≤ 1 * (‖a - b‖ * c ^ 2) := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = ‖a - b‖ * c ^ 2 := one_mul _
  have h2 : c ^ 2 ≤ ‖1 - w * a‖ * ‖1 - w * b‖ := by
    nlinarith
  nlinarith [norm_nonneg (a - b)]

/-- The open set `{t : |1 − wt| > c/2}` on which `g` is smooth. -/
private def goodSet (w : ℂ) (c : ℝ) : Set ℝ := {t | c / 2 < ‖1 - w * t‖}

private theorem isOpen_goodSet (w : ℂ) (c : ℝ) : IsOpen (goodSet w c) :=
  isOpen_lt continuous_const
    (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).norm

private theorem contDiffOn_gw (w : ℂ) (c : ℝ) (hc : 0 < c) (N : WithTop ℕ∞) :
    ContDiffOn ℝ N (gw w) (goodSet w c) := by
  have h : ContDiff ℝ N (fun t : ℝ => (1 : ℂ) - w * t) :=
    contDiff_const.sub (contDiff_const.mul Complex.ofRealCLM.contDiff)
  refine h.contDiffOn.inv fun t ht => ?_
  have : 0 < ‖(1 : ℂ) - w * t‖ := lt_trans (by positivity) ht
  exact norm_pos_iff.mp this

/-- `g^{(i)}(t) = i! wⁱ (1 − wt)^{−(i+1)}` on the good set. -/
private theorem iteratedDeriv_gw (w : ℂ) (c : ℝ) (hc : 0 < c) :
    ∀ (i : ℕ), ∀ t ∈ goodSet w c,
      iteratedDeriv i (gw w) t = (i.factorial : ℂ) * w ^ i * ((1 - w * t)⁻¹) ^ (i + 1)
  | 0, t, ht => by simp [gw]
  | i + 1, t, ht => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv i (gw w) =ᶠ[nhds t]
        fun s : ℝ => (i.factorial : ℂ) * w ^ i * ((1 - w * s)⁻¹) ^ (i + 1) :=
      Filter.eventually_of_mem ((isOpen_goodSet w c).mem_nhds ht) fun s hs =>
        iteratedDeriv_gw w c hc i s hs
    rw [hev.deriv_eq]
    have hne : (1 : ℂ) - w * t ≠ 0 := by
      have : 0 < ‖(1 : ℂ) - w * t‖ := lt_trans (by positivity) ht
      exact norm_pos_iff.mp this
    have h1 : HasDerivAt (fun s : ℝ => (1 : ℂ) - w * s) (-(w * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul w).const_sub 1
    have h2 := ((h1.inv hne).pow (i + 1)).const_mul ((i.factorial : ℂ) * w ^ i)
    have h3 := h2.deriv
    simp only [Pi.inv_apply, Pi.pow_apply] at h3
    rw [h3, Nat.add_sub_cancel]
    generalize (1 : ℂ) - w * t = u
    push_cast [Nat.factorial_succ]
    ring

/-- `|g^{(i)}(t)| ≤ n! (2/c)^{n+1}` on the good set, for `i ≤ n` and `|w| ≤ 1`. -/
private theorem norm_iteratedFDerivWithin_gw_le {w : ℂ} (hw : ‖w‖ ≤ 1) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 / 2) {n i : ℕ} (hi : i ≤ n) {t : ℝ} (ht : t ∈ goodSet w c) :
    ‖iteratedFDerivWithin ℝ i (gw w) (goodSet w c) t‖ ≤ n.factorial * (2 / c) ^ (n + 1) := by
  rw [iteratedFDerivWithin_of_isOpen i (isOpen_goodSet w c) ht,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gw w c hc i t ht]
  have hpos : 0 < ‖(1 : ℂ) - w * t‖ := lt_trans (by positivity) ht
  have hinv : ‖((1 : ℂ) - w * t)⁻¹‖ ≤ 2 / c := by
    rw [norm_inv]
    rw [inv_le_comm₀ hpos (by positivity)]
    have : c / 2 = (2 / c)⁻¹ := by field_simp
    rw [← this]
    exact (show c / 2 < ‖(1 : ℂ) - w * t‖ from ht).le
  have h2c : 1 ≤ 2 / c := by rw [le_div_iff₀ hc]; linarith
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  have hwi : ‖w‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
  calc (i.factorial : ℝ) * ‖w‖ ^ i * ‖((1 : ℂ) - w * t)⁻¹‖ ^ (i + 1)
      ≤ (i.factorial : ℝ) * 1 * (2 / c) ^ (i + 1) := by
        gcongr
    _ ≤ n.factorial * (2 / c) ^ (n + 1) := by
        rw [mul_one]
        exact mul_le_mul (by exact_mod_cast Nat.factorial_le hi)
          (pow_le_pow_right₀ h2c (by omega)) (by positivity) (by positivity)

/-- Schwartz decay `|ψ(q)| ≤ A (1 + |q|)^{−N}`. -/
private theorem schwartz_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : 𝓢(E, ℝ)) (N : ℕ) : ∃ A, 0 ≤ A ∧ ∀ q, ‖ψ q‖ ≤ A * ((1 + ‖q‖) ^ N)⁻¹ := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ,
    by positivity, fun q => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0)
    le_rfl le_rfl ψ q
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖q‖) ^ N := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- Decay of the `n`-th derivative of `g ∘ ψ` (Faà di Bruno), uniformly in `w`. -/
private theorem iteratedFDeriv_gw_comp_decay {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ψ : 𝓢(E, ℝ)) (n M : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1 / 2) :
    ∃ B, 0 ≤ B ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → (∀ q, c ≤ ‖1 - w * ψ q‖) → ∀ q,
      ‖iteratedFDeriv ℝ n (fun q => gw w (ψ q)) q‖ ≤ B * ((1 + ‖q‖) ^ M)⁻¹ := by
  set S := 2 ^ (M * n) * (Finset.Iic (M * n, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ
  set A := max 1 S
  set Cg : ℝ := n.factorial * (2 / c) ^ (n + 1)
  refine ⟨n.factorial * Cg * A ^ n, by positivity, fun w hw hgood q => ?_⟩
  set ρ : ℝ := (1 + ‖q‖)⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg q])
  have hA1 : 1 ≤ A := le_max_left _ _
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i ψ q‖ ≤ (A * ρ ^ M) ^ i := by
    intro i hi1 hin
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M * n, n)) (k := M * n)
      (n := i) le_rfl hin ψ q
    have hpos : 0 < (1 + ‖q‖) ^ (M * n) := by positivity
    have h1 : ‖iteratedFDeriv ℝ i ψ q‖ ≤ S * ρ ^ (M * n) := by
      rw [hρ, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      linarith
    calc ‖iteratedFDeriv ℝ i ψ q‖ ≤ S * ρ ^ (M * n) := h1
      _ ≤ A * ρ ^ (M * i) := mul_le_mul (le_max_right _ _)
          (pow_le_pow_of_le_one hρ0 hρ1 (Nat.mul_le_mul_left M hin)) (by positivity)
          (by positivity)
      _ ≤ A ^ i * ρ ^ (M * i) := by
          gcongr
          exact le_self_pow₀ hA1 (by omega)
      _ = (A * ρ ^ M) ^ i := by rw [mul_pow, ← pow_mul]
  have hrange : Set.range ψ ⊆ goodSet w c := by
    rintro _ ⟨q', rfl⟩
    change c / 2 < ‖1 - w * ψ q'‖
    linarith [hgood q']
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := gw w) (f := ψ) (n := n) (N := n)
    hrange (isOpen_goodSet w c).uniqueDiffOn (contDiffOn_gw w c hc n) (ψ.smooth n) le_rfl q
    (C := Cg) (D := A * ρ ^ M)
    (fun i hi => norm_iteratedFDerivWithin_gw_le hw hc hc1 hi (hrange ⟨q, rfl⟩)) hD
  calc ‖iteratedFDeriv ℝ n (fun q => gw w (ψ q)) q‖ ≤ n.factorial * Cg * (A * ρ ^ M) ^ n := hcomp
    _ = n.factorial * Cg * A ^ n * ρ ^ (M * n) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ n.factorial * Cg * A ^ n * ρ ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 (Nat.le_mul_of_pos_right M hn))
          (by positivity)
    _ = n.factorial * Cg * A ^ n * ((1 + ‖q‖) ^ M)⁻¹ := by rw [hρ, inv_pow]

/-- The `n`-th derivative of `t ↦ G(q + t e)` is bounded by `‖D^n G(q + t e)‖` for `|e| = 1`. -/
private theorem norm_iteratedDeriv_line_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → ℂ) (n : ℕ) (hG : ContDiff ℝ n G) (q e : E) (he : ‖e‖ = 1) (u : ℝ) :
    ‖iteratedDeriv n (fun t : ℝ => G (q + t • e)) u‖ ≤ ‖iteratedFDeriv ℝ n G (q + u • e)‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  set ℓ : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) e
  have hℓ : ∀ t, ℓ t = t • e := fun t => by simp [ℓ]
  have hfun : (fun t : ℝ => G (q + t • e)) = (fun z => G (q + z)) ∘ ℓ := by
    funext t
    simp [hℓ]
  have hG' : ContDiff ℝ n (fun z => G (q + z)) := hG.comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right ℓ hG' u le_rfl]
  have hℓn : ‖ℓ‖ ≤ 1 := by
    simp only [ℓ, ContinuousLinearMap.norm_smulRight_apply, he, mul_one]
    exact ContinuousLinearMap.norm_id_le
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [iteratedFDeriv_comp_add_left, hℓ]
  calc ‖iteratedFDeriv ℝ n G (q + u • e)‖ * ∏ _i : Fin n, ‖ℓ‖
      ≤ ‖iteratedFDeriv ℝ n G (q + u • e)‖ * 1 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hℓn) (norm_nonneg _)
    _ = _ := mul_one _

end Resolvent

/-! ## The main term `L^{−d} Σ_k F(ψ(W p_k)) e^{i p_k·z}` -/

section MainTerm

variable {d : ℕ}

/-- The main term `F(ψ(W p_k))` of the symbol of `S^+`. -/
private def Hmain (w : ℂ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℕ) {L : ℕ}
    (k : Zd d L) : ℂ :=
  Fw w (ψ ((W : ℝ) • zfreq k))

/-- Bulk bound: `|L^{−d} Σ_k F(ψ(W p_k)) e^{i p_k·z}| ≤ K₁ W^{−d}`. -/
private theorem main_bulk_le (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) {c : ℝ} (hc : 0 < c) :
    ∃ K₁, 0 ≤ K₁ ∧ ∀ (W L : ℕ) [NeZero L], 1 ≤ W → W ≤ L → ∀ w : ℂ, ‖w‖ ≤ 1 →
      (∀ q, c ≤ ‖1 - w * ψ q‖) → ∀ z : Zd d L,
        ‖((L : ℂ) ^ d)⁻¹ * ∑ k, Hmain w ψ W k * zchar k z‖ ≤ K₁ * ((W : ℝ) ^ d)⁻¹ := by
  obtain ⟨A, hA0, hA⟩ := schwartz_decay ψ (2 * d)
  refine ⟨A / c * 3 ^ d, by positivity, fun W L _ hW hWL w hw hgood z => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpt : ∀ k : Zd d L, ‖Hmain w ψ W k * zchar k z‖ ≤
      A / c * ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ := by
    intro k
    rw [norm_mul, norm_zchar, mul_one, Hmain]
    refine (norm_Fw_le hc hw (hgood _)).trans ?_
    rw [Complex.norm_real, div_le_iff₀ hc]
    have := hA ((W : ℝ) • zfreq k)
    calc ‖ψ ((W : ℝ) • zfreq k)‖ ≤ A * ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ := this
      _ = A / c * ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ * c := by field_simp
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((L : ℝ) ^ d)⁻¹ * ‖∑ k, Hmain w ψ W k * zchar k z‖
      ≤ ((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, A / c * ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hpt k))
          (by positivity)
    _ = A / c * (((L : ℝ) ^ d)⁻¹ * ∑ k : Zd d L, ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ A / c * (3 ^ d * ((W : ℝ) ^ d)⁻¹) :=
        mul_le_mul_of_nonneg_left (lattice_sum_le W hW hWL) (by positivity)
    _ = A / c * 3 ^ d * ((W : ℝ) ^ d)⁻¹ := by ring

/-- Tail bound by summation by parts:
`|L^{−d} Σ_k F(ψ(W p_k)) e^{i p_k·z}| |e^{−2πi z_i/L} − 1|^n ≤ (2πW/L)^n K₃ W^{−d} + K₄ W^{−N₂}`. -/
private theorem main_tail_le (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (n : ℕ) (hn : 1 ≤ n)
    (N₂ : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) :
    ∃ K₃ K₄, 0 ≤ K₃ ∧ 0 ≤ K₄ ∧ ∀ (W L : ℕ) [NeZero L], 1 ≤ W → W ≤ L → 4 * n ≤ L →
      ∀ w : ℂ, ‖w‖ ≤ 1 → (∀ q, c ≤ ‖1 - w * ψ q‖) → ∀ (z : Zd d L) (i : Fin d),
        ‖((L : ℂ) ^ d)⁻¹ * ∑ k, Hmain w ψ W k * zchar k z‖ *
            ‖zchar (-(Pi.single i 1 : Zd d L)) z - 1‖ ^ n ≤
          (2 * Real.pi * W / L) ^ n * K₃ * ((W : ℝ) ^ d)⁻¹ + K₄ * ((W : ℝ) ^ N₂)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := iteratedFDeriv_gw_comp_decay ψ n (2 * d) hn hc hc1
  obtain ⟨A₂, hA₂0, hA₂⟩ := schwartz_decay ψ N₂
  set B' := B * (1 + 2 * Real.pi * n) ^ (2 * d) with hB'
  have hB'0 : 0 ≤ B' := by positivity
  refine ⟨B' * 3 ^ d, 2 ^ n * (A₂ / c), by positivity, by positivity,
    fun W L _ hW hWL hnL w hw hgood z i => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hWL' : (W : ℝ) ≤ L := by exact_mod_cast hWL
  have hpi := Real.pi_pos
  set e : Zd d L := Pi.single i 1 with he
  set s : ℝ := 2 * Real.pi * W / L with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 2 * Real.pi := by
    rw [hs, div_le_iff₀ hLpos]
    nlinarith
  set e' : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1 with he'
  have he'n : ‖e'‖ = 1 := by simp [e']
  have hne : ∀ q, (1 : ℂ) - w * (ψ q : ℂ) ≠ 0 := fun q =>
    norm_pos_iff.mp (lt_of_lt_of_le hc (hgood q))
  have hG : ContDiff ℝ n (fun q => gw w (ψ q)) :=
    (contDiffOn_gw w c hc n).comp_contDiff (ψ.smooth n) fun q => by
      change c / 2 < ‖1 - w * ψ q‖
      linarith [hgood q]
  set T : ℝ := 2 ^ n * (A₂ / c) * ((W : ℝ) ^ N₂)⁻¹ with hT
  have hpt : ∀ k : Zd d L, ‖fdiff e n (Hmain w ψ W) k‖ ≤
      s ^ n * B' * ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ + T := by
    intro k
    set q := (W : ℝ) • zfreq k with hq
    have hT0 : 0 ≤ T := by positivity
    by_cases hcr : ((k i).valMinAbs + n) * 2 ≤ L
    · set φ : ℝ → ℂ := fun t => -1 + gw w (ψ (q + t • e')) with hφ
      have hcongr : fdiff e n (Hmain w ψ W) k = fdiff s n φ 0 := by
        apply fdiff_congr
        intro j hj
        have hj' : ((k i).valMinAbs + j) * 2 ≤ L := by
          have : (j : ℤ) ≤ n := by exact_mod_cast hj
          omega
        have hsc : (W : ℝ) * (2 * Real.pi * j / L) = j * s := by rw [hs]; ring
        simp only [Hmain, φ, zero_add]
        rw [zfreq_add_single k i j hj', smul_add, smul_smul, nsmul_eq_mul, hsc,
          ← Fw_eq_gw (hne _)]
      have hsmooth : ∀ m : ℕ, ContDiff ℝ m φ := fun m =>
        contDiff_const.add (((contDiffOn_gw w c hc m).comp_contDiff (ψ.smooth m) fun q => by
          change c / 2 < ‖1 - w * ψ q‖
          linarith [hgood q]).comp (contDiff_const.add (contDiff_id.smul contDiff_const)))
      have hbound : ∀ u ∈ Set.Icc (0 : ℝ) (0 + n * s),
          ‖iteratedDeriv n φ u‖ ≤ B' * ((1 + ‖q‖) ^ (2 * d))⁻¹ := by
        intro u hu
        have hu1 : u ≤ 2 * Real.pi * n := by
          have := hu.2
          rw [zero_add] at this
          nlinarith [hu.1]
        have h1 : iteratedDeriv n φ u = iteratedDeriv n (fun t => gw w (ψ (q + t • e'))) u :=
          iteratedDeriv_const_add (by omega) (-1 : ℂ)
        rw [h1]
        refine (norm_iteratedDeriv_line_le (fun q => gw w (ψ q)) n hG q e' he'n u).trans ?_
        refine (hB w hw hgood (q + u • e')).trans ?_
        rw [hB']
        have hX : 0 < (1 + ‖q + u • e'‖) ^ (2 * d) := by positivity
        have hY : 0 < (1 + ‖q‖) ^ (2 * d) := by positivity
        have hshift : 1 + ‖q‖ ≤ (1 + ‖q + u • e'‖) * (1 + 2 * Real.pi * n) := by
          have h2 : ‖q‖ ≤ ‖q + u • e'‖ + ‖u • e'‖ := by
            have := norm_sub_le (q + u • e') (u • e')
            rwa [add_sub_cancel_right] at this
          have hue : ‖u • e'‖ = u := by
            rw [norm_smul, he'n, mul_one, Real.norm_eq_abs, abs_of_nonneg hu.1]
          rw [hue] at h2
          nlinarith [mul_nonneg (norm_nonneg (q + u • e'))
            (by positivity : (0 : ℝ) ≤ 2 * Real.pi * n)]
        have hpow : (1 + ‖q‖) ^ (2 * d) ≤
            (1 + ‖q + u • e'‖) ^ (2 * d) * (1 + 2 * Real.pi * n) ^ (2 * d) := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hshift _
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hB0
        rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hX hY]
        linarith
      rw [hcongr]
      have := norm_fdiff_real_le s hs0 n φ hsmooth 0 _ hbound
      calc ‖fdiff s n φ 0‖ ≤ s ^ n * (B' * ((1 + ‖q‖) ^ (2 * d))⁻¹) := this
        _ ≤ s ^ n * B' * ((1 + ‖q‖) ^ (2 * d))⁻¹ + T := by rw [← mul_assoc]; linarith
    · push Not at hcr
      have hj : ∀ j ≤ n, ‖Hmain w ψ W (k + j • e)‖ ≤ A₂ / c * ((W : ℝ) ^ N₂)⁻¹ := by
        intro j hj
        set qj := (W : ℝ) • zfreq (k + j • e) with hqj
        have hv := le_four_mul_abs_valMinAbs (k i) n j hnL hj hcr
        have hki : (k + j • e) i = k i + j := by simp [e]
        have hqi : |qj.ofLp i| = 2 * Real.pi * W * |(((k i + j).valMinAbs : ℤ) : ℝ)| / L := by
          simp only [qj, zfreq, PiLp.smul_apply, smul_eq_mul, hki]
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_div, abs_mul,
            abs_of_nonneg hLpos.le, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
          ring
        have hv' : (L : ℝ) ≤ 4 * |(((k i + j).valMinAbs : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast hv
        have hWq : (W : ℝ) ≤ 1 + ‖qj‖ := by
          have h1 := PiLp.norm_apply_le qj i
          rw [Real.norm_eq_abs, hqi] at h1
          have h2 : (W : ℝ) ≤ 2 * Real.pi * W * |(((k i + j).valMinAbs : ℤ) : ℝ)| / L := by
            rw [le_div_iff₀ hLpos]
            have : (W : ℝ) * L ≤ W * (4 * |(((k i + j).valMinAbs : ℤ) : ℝ)|) :=
              mul_le_mul_of_nonneg_left hv' hWpos.le
            have h6 : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
            have h7 : (W : ℝ) * (4 * |(((k i + j).valMinAbs : ℤ) : ℝ)|) ≤
                2 * Real.pi * W * |(((k i + j).valMinAbs : ℤ) : ℝ)| := by
              nlinarith [mul_nonneg hWpos.le (abs_nonneg ((((k i + j).valMinAbs : ℤ) : ℝ)))]
            linarith
          linarith
        calc ‖Hmain w ψ W (k + j • e)‖ ≤ ‖((ψ qj : ℝ) : ℂ)‖ / c := norm_Fw_le hc hw (hgood _)
          _ ≤ A₂ * ((1 + ‖qj‖) ^ N₂)⁻¹ / c := by
              rw [Complex.norm_real]
              exact div_le_div_of_nonneg_right (hA₂ qj) hc.le
          _ ≤ A₂ * ((W : ℝ) ^ N₂)⁻¹ / c := by
              gcongr
          _ = A₂ / c * ((W : ℝ) ^ N₂)⁻¹ := by ring
      have := norm_fdiff_le e n (Hmain w ψ W) k _ hj
      have h0 : 0 ≤ s ^ n * B' * ((1 + ‖q‖) ^ (2 * d))⁻¹ := by positivity
      rw [hT]
      linarith
  have hsbp := sum_fdiff_zchar e z n (Hmain w ψ W)
  have hnorm : ‖((L : ℂ) ^ d)⁻¹ * ∑ k, Hmain w ψ W k * zchar k z‖ *
      ‖zchar (-e) z - 1‖ ^ n = ((L : ℝ) ^ d)⁻¹ * ‖∑ k, fdiff e n (Hmain w ψ W) k * zchar k z‖ := by
    rw [hsbp]
    simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    ring
  rw [hnorm]
  have hcard : ∑ _k : Zd d L, T = (L : ℝ) ^ d * T := by
    rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
    push_cast
    ring
  calc ((L : ℝ) ^ d)⁻¹ * ‖∑ k, fdiff e n (Hmain w ψ W) k * zchar k z‖
      ≤ ((L : ℝ) ^ d)⁻¹ *
          ∑ k : Zd d L, (s ^ n * B' * ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹ + T) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ => ?_)) (by positivity)
        rw [norm_mul, norm_zchar, mul_one]
        exact hpt k
    _ = s ^ n * B' * (((L : ℝ) ^ d)⁻¹ *
          ∑ k : Zd d L, ((1 + ‖(W : ℝ) • zfreq k‖) ^ (2 * d))⁻¹) + T := by
        rw [Finset.sum_add_distrib, hcard, ← Finset.mul_sum]
        field_simp
    _ ≤ s ^ n * B' * (3 ^ d * ((W : ℝ) ^ d)⁻¹) + T := by
        have := lattice_sum_le (d := d) W hW hWL
        have h0 : 0 ≤ s ^ n * B' := by positivity
        nlinarith
    _ = s ^ n * (B' * 3 ^ d) * ((W : ℝ) ^ d)⁻¹ + 2 ^ n * (A₂ / c) * ((W : ℝ) ^ N₂)⁻¹ := by
        rw [hT]
        ring

end MainTerm

/-! ## Exponent bookkeeping -/

/-- In the tail `|x − y| > W^{1+τ}`: `(W/|x − y|)^n ≤ 2^D ⟨x − y⟩^{−D}` once
`n ≥ D(1 + τ)/τ`. -/
private theorem exp_tail_le {W r τ D : ℝ} {n : ℕ} (hW : 1 ≤ W) (hτ : 0 < τ) (hD : 0 < D)
    (hr : W ^ (1 + τ) < r) (hn : D * (1 + τ) / τ ≤ n) :
    (W / r) ^ n ≤ 2 ^ D * ((r + W) ^ D)⁻¹ := by
  have hW0 : 0 < W := by linarith
  have h1W : W ≤ W ^ (1 + τ) := by
    have := Real.rpow_le_rpow_of_exponent_le hW (by linarith : (1 : ℝ) ≤ 1 + τ)
    rwa [Real.rpow_one] at this
  have hr1 : 1 < r := lt_of_le_of_lt (Real.one_le_rpow hW (by linarith)) hr
  have hr0 : 0 < r := by linarith
  have hWr : W ≤ r ^ (1 / (1 + τ)) := by
    have h := Real.rpow_le_rpow (by positivity) hr.le (by positivity : (0 : ℝ) ≤ 1 / (1 + τ))
    rwa [← Real.rpow_mul hW0.le, mul_one_div_cancel (by positivity), Real.rpow_one] at h
  have hWn : W ^ n ≤ r ^ ((n : ℝ) / (1 + τ)) := by
    calc W ^ n ≤ (r ^ (1 / (1 + τ))) ^ n := pow_le_pow_left₀ hW0.le hWr n
      _ = r ^ ((n : ℝ) / (1 + τ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
          congr 1
          ring
  have hexp : (n : ℝ) / (1 + τ) + D ≤ n := by
    rw [div_le_iff₀ hτ] at hn
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hrW : r + W ≤ 2 * r := by linarith
  have hpowD : (r + W) ^ D ≤ 2 ^ D * r ^ D := by
    rw [← Real.mul_rpow (by norm_num) hr0.le]
    exact Real.rpow_le_rpow (by positivity) hrW hD.le
  have hrn : r ^ ((n : ℝ) / (1 + τ)) * r ^ D ≤ r ^ n := by
    rw [← Real.rpow_add hr0, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hr1.le hexp
  have hpos : 0 < (r + W) ^ D := by positivity
  rw [le_mul_inv_iff₀ hpos, div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc W ^ n * (r + W) ^ D ≤ r ^ ((n : ℝ) / (1 + τ)) * (2 ^ D * r ^ D) :=
        mul_le_mul hWn hpowD (by positivity) (by positivity)
    _ = 2 ^ D * (r ^ ((n : ℝ) / (1 + τ)) * r ^ D) := by ring
    _ ≤ 2 ^ D * r ^ n := mul_le_mul_of_nonneg_left hrn (by positivity)

/-- In the window `L^{c₁} ≤ W`: `L^n W^{−N} ≤ 2^D ⟨x − y⟩^{−D}` once `n + D ≤ c₁N` and
`⟨x − y⟩ ≤ 2L`. -/
private theorem exp_window_le {W L r c₁ D : ℝ} {n N : ℕ} (hL : 1 ≤ L) (hc₁ : 0 < c₁)
    (hLW : L ^ c₁ ≤ W) (hD : 0 < D) (hN : n + D ≤ c₁ * N) (hrW : 0 < r + W)
    (hrL : r + W ≤ 2 * L) : L ^ n * (W ^ N)⁻¹ ≤ 2 ^ D * ((r + W) ^ D)⁻¹ := by
  have hL0 : 0 < L := by linarith
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hLW
  have hpowD : (r + W) ^ D ≤ 2 ^ D * L ^ D := by
    rw [← Real.mul_rpow (by norm_num) hL0.le]
    exact Real.rpow_le_rpow hrW.le hrL hD.le
  have hLN : L ^ n * L ^ D ≤ W ^ N := by
    rw [← Real.rpow_natCast L n, ← Real.rpow_add hL0]
    calc L ^ ((n : ℝ) + D) ≤ L ^ (c₁ * N) := Real.rpow_le_rpow_of_exponent_le hL hN
      _ = (L ^ c₁) ^ N := by rw [Real.rpow_mul hL0.le, Real.rpow_natCast]
      _ ≤ W ^ N := pow_le_pow_left₀ (by positivity) hLW N
  have hpos : 0 < (r + W) ^ D := Real.rpow_pos_of_pos hrW D
  rw [le_mul_inv_iff₀ hpos, mul_assoc, mul_comm _ ((r + W) ^ D), ← mul_assoc,
    mul_inv_le_iff₀ (by positivity)]
  calc L ^ n * (r + W) ^ D ≤ L ^ n * (2 ^ D * L ^ D) :=
        mul_le_mul_of_nonneg_left hpowD (by positivity)
    _ = 2 ^ D * (L ^ n * L ^ D) := by ring
    _ ≤ 2 ^ D * W ^ N := mul_le_mul_of_nonneg_left hLN (by positivity)

/-- Division by `|e^{−2πi z_i/L} − 1|^n ≥ (4|z_i|/L)^n` in the tail bound. -/
private theorem tail_main_le {M ω r L W K₃ K₄ Wd WN : ℝ} (n : ℕ) (hr : 1 ≤ r) (hL : 0 < L)
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hWd : 0 ≤ Wd) (hWN : 0 ≤ WN)
    (hω : 4 * r / L ≤ ω) (hMω : M * ω ^ n ≤ (2 * Real.pi * W / L) ^ n * K₃ * Wd + K₄ * WN) :
    M ≤ 2 ^ n * (W / r) ^ n * K₃ * Wd + L ^ n * K₄ * WN := by
  set a := 4 * r / L with ha
  have hr0 : 0 < r := by linarith
  have ha0 : 0 < a := by positivity
  have h1 : M * a ^ n ≤ M * ω ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0.le hω n) hM
  have hs : 2 * Real.pi * W / L = a * (Real.pi / 4 * (2 * (W / r))) := by
    rw [ha]
    field_simp
  have hpi : Real.pi / 4 * (2 * (W / r)) ≤ 2 * (W / r) := by
    have := Real.pi_le_four
    have h0 : 0 ≤ 2 * (W / r) := by positivity
    nlinarith
  have h2 : (2 * Real.pi * W / L) ^ n ≤ a ^ n * (2 ^ n * (W / r) ^ n) := by
    rw [hs, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (pow_le_pow_left₀ (by positivity) hpi n).trans_eq (mul_pow _ _ _)
  have h3 : 1 ≤ a ^ n * L ^ n := by
    rw [← mul_pow]
    refine one_le_pow₀ ?_
    rw [ha, div_mul_cancel₀ _ hL.ne']
    linarith
  have h4 : M * a ^ n ≤ (2 ^ n * (W / r) ^ n * K₃ * Wd + L ^ n * K₄ * WN) * a ^ n := by
    calc M * a ^ n ≤ (2 * Real.pi * W / L) ^ n * K₃ * Wd + K₄ * WN := h1.trans hMω
      _ ≤ a ^ n * (2 ^ n * (W / r) ^ n) * K₃ * Wd + (a ^ n * L ^ n) * (K₄ * WN) := by
          exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hK₃) hWd)
            (le_mul_of_one_le_left (by positivity) h3)
      _ = (2 ^ n * (W / r) ^ n * K₃ * Wd + L ^ n * K₄ * WN) * a ^ n := by ring
  exact le_of_mul_le_mul_right h4 (pow_pos ha0 n)

/-- Assembly of the bulk bound: `M + E ≤ (K₁ + P(K_t + K₂))(W^{−d} + X)`. -/
private theorem combine_bulk {M E K₁ K₂ Kt P Wd X : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hKt : 0 ≤ Kt) (hP : 0 ≤ P) (hWd : 0 ≤ Wd) (hX : 0 ≤ X) (hM : M ≤ K₁ * Wd)
    (hE : E ≤ K₂ * (P * X)) : M + E ≤ (K₁ + P * (Kt + K₂)) * (Wd + X) := by
  nlinarith [mul_nonneg hK₁ hX, mul_nonneg (mul_nonneg hP hKt) hWd,
    mul_nonneg (mul_nonneg hP hKt) hX, mul_nonneg (mul_nonneg hP hK₂) hWd]

/-- Assembly of the tail bound: `M + E ≤ (K₁ + P(K_t + K₂))(0 + X)`. -/
private theorem combine_tail {M E K₁ K₂ Kt P X : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hKt : 0 ≤ Kt) (hP : 0 ≤ P) (hX : 0 ≤ X) (hM : M ≤ Kt * (P * X))
    (hE : E ≤ K₂ * (P * X)) : M + E ≤ (K₁ + P * (Kt + K₂)) * (0 + X) := by
  nlinarith [mul_nonneg hK₁ hX]

/-! ## [I, Lemma 2.2] = [II, Lemma 2.1] -/

/-- [I, Lemma 2.2] = [II, Lemma 2.1] for `|m| ≤ 1`, `|1 − m²| ≥ δ` (this includes `m(E)` at
`η = 0`): under (H1)–(H3), `|S^±_{xy}| ≤ K (W^{−d} 1(|x − y| ≤ W^{1+τ}) + ⟨x − y⟩^{−D})` for
`W ≥ W₀`, with `K` and `W₀` depending only on `d, c₀, c₁, ψ, c′, C, δ, τ, D`. -/
theorem Splus_decay :
  ∀ (d : ℕ) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (δ τ D : ℝ) (hδ : 0 < δ) (hτ : 0 < τ)
    (hD : 0 < D),
    ∃ K W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ m : ℂ, ‖m‖ ≤ 1 → δ ≤ ‖1 - m ^ 2‖ → ∀ x y : Zd d L,
        ‖Splus m S x y‖ ≤ K * splusBound W τ D x y ∧ ‖Sminus m S x y‖ ≤ K * splusBound W τ D x y := by
  intro d c₀ c₁ hc₀ hc₁ ψ c' hψ C δ τ D hδ hτ hD
  have hc' := hψ.pos
  set c := cF δ c' with hcdef
  have hc : 0 < c := cF_pos hδ hc'
  have hc1 : c ≤ 1 / 2 := cF_le_half δ c'
  set n : ℕ := ⌈D * (1 + τ) / τ⌉₊ + 1 with hndef
  have hn1 : 1 ≤ n := Nat.le_add_left 1 _
  have hnD : D * (1 + τ) / τ ≤ n := by
    have := Nat.le_ceil (D * (1 + τ) / τ)
    rw [hndef]
    push_cast
    linarith
  set N₂ : ℕ := ⌈((n : ℝ) + D) / c₁⌉₊ with hN₂def
  have hN₂ : ((n : ℕ) : ℝ) + D ≤ c₁ * N₂ := by
    have := Nat.le_ceil (((n : ℝ) + D) / c₁)
    rw [div_le_iff₀ hc₁] at this
    linarith
  set D' : ℕ := ⌈D / c₁⌉₊ with hD'def
  have hD' : ((0 : ℕ) : ℝ) + D ≤ c₁ * D' := by
    have := Nat.le_ceil (D / c₁)
    rw [div_le_iff₀ hc₁] at this
    push_cast
    linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := main_bulk_le ψ hc
  obtain ⟨K₃, K₄, hK₃0, hK₄0, hK34⟩ := main_tail_le ψ n hn1 N₂ hc hc1
  set K₂ := |C D'| / c ^ 2 with hK₂def
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨K₁ + 2 ^ D * (2 ^ n * K₃ + K₄ + K₂), max (max 1 (2 * |C 1| / c')) (4 * n), ?_⟩
  intro W L _ hadm hW₀ S hS hSC m hm hδm x y
  -- the window
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW₀
  have hWnat : 1 ≤ W := by exact_mod_cast hW1
  have hLnat : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLnat
  have hLpos : (0 : ℝ) < L := by linarith
  have hWL : (W : ℝ) ≤ L := by
    refine hadm.2.trans ?_
    have := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : 1 - c₀ ≤ 1)
    rwa [Real.rpow_one] at this
  have hWLnat : W ≤ L := by exact_mod_cast hWL
  have hLW : (L : ℝ) ^ c₁ ≤ W := hadm.1
  have h4n : 4 * n ≤ L := by
    have h : (4 : ℝ) * n ≤ W := (le_max_right _ _).trans hW₀
    exact_mod_cast h.trans hWL
  have hC1 : |C 1| / W ≤ c' / 2 := by
    have h : 2 * |C 1| / c' ≤ W := ((le_max_right _ _).trans (le_max_left _ _)).trans hW₀
    rw [div_le_iff₀ hc'] at h
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the parameter `w = m²`
  set w := m ^ 2 with hwdef
  have hw : ‖w‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm
  have hgood : ∀ q, c ≤ ‖1 - w * ψ q‖ := fun q =>
    cF_le_norm_one_sub hδ hc' hw hδm (by linarith [(hψ.range q).1]) (hψ.range q).2
  -- the symbol of `S` is real, in `[−1 + c′/2, 1]`
  have hSre : ∀ k, symbol (cmat S) k = ((symbol (cmat S) k).re : ℂ) := fun k =>
    Complex.ext (by simp) (by simp [symbol_cmat_im S hS.symm hS.transInv k])
  have hSrange : ∀ k, -1 + c' / 2 ≤ (symbol (cmat S) k).re ∧ (symbol (cmat S) k).re ≤ 1 := by
    intro k
    refine ⟨?_, (Complex.re_le_norm _).trans (hS.norm_symbol_le k)⟩
    have h := hSC 1 k
    have h2 := Complex.abs_re_le_norm (symbol (cmat S) k - (ψ ((W : ℝ) • zfreq k) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    rw [pow_one] at h
    have h3 : C 1 / W ≤ |C 1| / W := div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
    have h4 := (hψ.range ((W : ℝ) • zfreq k)).1
    have h5 := neg_abs_le ((symbol (cmat S) k).re - ψ ((W : ℝ) • zfreq k))
    linarith
  have hgoodS : ∀ k, c ≤ ‖1 - w * symbol (cmat S) k‖ := by
    intro k
    rw [hSre k]
    exact cF_le_norm_one_sub hδ hc' hw hδm (hSrange k).1 (hSrange k).2
  have hne : ∀ k, m ^ 2 * symbol (cmat S) k ≠ 1 := fun k h => by
    have := hgoodS k
    rw [hwdef, h, sub_self, norm_zero] at this
    linarith
  -- the representation `S^+ = main + error`
  have hrep : Splus m S x y =
      ((L : ℂ) ^ d)⁻¹ * ∑ k, Hmain w ψ W k * zchar k (x - y) +
        ((L : ℂ) ^ d)⁻¹ *
          ∑ k, (Fw w (symbol (cmat S) k) - Hmain w ψ W k) * zchar k (x - y) := by
    rw [kernel_inversion _ (TransInv_propagators S hS.transInv m).1 x y, ← mul_add,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [symbol_Splus S hS.transInv m hne k, Fw, hwdef]
    ring
  -- the error term
  have herr : ‖((L : ℂ) ^ d)⁻¹ *
      ∑ k, (Fw w (symbol (cmat S) k) - Hmain w ψ W k) * zchar k (x - y)‖ ≤
        K₂ * ((W : ℝ) ^ D')⁻¹ := by
    have hpt : ∀ k : Zd d L, ‖(Fw w (symbol (cmat S) k) - Hmain w ψ W k) * zchar k (x - y)‖ ≤
        K₂ * ((W : ℝ) ^ D')⁻¹ := by
      intro k
      rw [norm_mul, norm_zchar, mul_one, Hmain]
      refine (norm_Fw_sub_le hc hw (hgoodS k) (hgood _)).trans ?_
      rw [hK₂def, div_le_iff₀ (by positivity)]
      have h := hSC D' k
      have h2 : C D' / (W : ℝ) ^ D' ≤ |C D'| / (W : ℝ) ^ D' :=
        div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      have h3 : |C D'| / c ^ 2 * ((W : ℝ) ^ D')⁻¹ * c ^ 2 = |C D'| / (W : ℝ) ^ D' := by
        field_simp
      linarith
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc ((L : ℝ) ^ d)⁻¹ * ‖∑ k, (Fw w (symbol (cmat S) k) - Hmain w ψ W k) * zchar k (x - y)‖
        ≤ ((L : ℝ) ^ d)⁻¹ * ∑ _k : Zd d L, K₂ * ((W : ℝ) ^ D')⁻¹ :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hpt k))
            (by positivity)
      _ = K₂ * ((W : ℝ) ^ D')⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          field_simp
  -- distances
  have hbound : splusBound W τ D x y =
      (if (zdistInf d L (x - y) : ℝ) ≤ (W : ℝ) ^ (1 + τ) then ((W : ℝ) ^ d)⁻¹ else 0) +
        (((zdistInf d L (x - y) : ℝ) + W) ^ D)⁻¹ := by
    rw [splusBound, Real.rpow_neg (by positivity)]
  have hrhalf := zdistInf_le_half d L (x - y)
  have hsup : zdistInf d L (x - y) = Finset.univ.sup fun i => zdist L ((x - y) i) := rfl
  generalize hrdef : zdistInf d L (x - y) = r at hbound hrhalf hsup
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hrL : (r : ℝ) + W ≤ 2 * L := by
    have : (r : ℝ) ≤ L := by exact_mod_cast hrhalf.trans (Nat.div_le_self L 2)
    linarith
  have hrW : (0 : ℝ) < r + W := by linarith
  set X : ℝ := (((r : ℝ) + W) ^ D)⁻¹ with hX
  have hX0 : 0 ≤ X := by positivity
  have herr' : K₂ * ((W : ℝ) ^ D')⁻¹ ≤ K₂ * (2 ^ D * X) := by
    refine mul_le_mul_of_nonneg_left ?_ hK₂0
    have := exp_window_le (n := 0) (N := D') hL1 hc₁ hLW hD hD' hrW hrL
    rwa [pow_zero, one_mul] at this
  have hmainS : ‖Splus m S x y‖ ≤ (K₁ + 2 ^ D * (2 ^ n * K₃ + K₄ + K₂)) *
      ((if (r : ℝ) ≤ (W : ℝ) ^ (1 + τ) then ((W : ℝ) ^ d)⁻¹ else 0) + X) := by
    rw [hrep]
    refine (norm_add_le _ _).trans ?_
    have h2D : (0 : ℝ) ≤ 2 ^ D := by positivity
    split_ifs with hbulk
    · exact combine_bulk hK₁0 hK₂0 (by positivity) h2D (by positivity) hX0
        (hK₁ W L hWnat hWLnat w hw hgood (x - y)) (herr.trans herr')
    · push Not at hbulk
      have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (Real.one_le_rpow hW1 (by linarith)) hbulk
      -- the coordinate realising `‖x − y‖_L`
      have hnemp : (Finset.univ : Finset (Fin d)).Nonempty := by
        rcases (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty with h | h
        · exfalso
          rw [h, Finset.sup_empty] at hsup
          have : r = 0 := hsup
          rw [this] at hr1
          norm_num at hr1
        · exact h
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hnemp
        (fun i => zdist L ((x - y) i))
      have hri : (r : ℝ) = |((((x - y) i).valMinAbs : ℤ) : ℝ)| := by
        have : r = zdist L ((x - y) i) := hsup.trans hi
        rw [this, zdist_eq_natAbs_valMinAbs, Nat.cast_natAbs, Int.cast_abs]
      have hω := norm_zchar_neg_single_sub_one i (x - y)
      rw [← hri] at hω
      have hM := tail_main_le n hr1.le hLpos (by positivity) (norm_nonneg _) hK₃0 hK₄0
        (by positivity) (by positivity) hω (hK34 W L hWnat hWLnat h4n w hw hgood (x - y) i)
      have hWd1 : ((W : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
      have ht1 : 2 ^ n * ((W : ℝ) / r) ^ n * K₃ * ((W : ℝ) ^ d)⁻¹ ≤ 2 ^ n * K₃ * (2 ^ D * X) := by
        have h2 := exp_tail_le (n := n) hW1 hτ hD hbulk hnD
        calc 2 ^ n * ((W : ℝ) / r) ^ n * K₃ * ((W : ℝ) ^ d)⁻¹
            ≤ 2 ^ n * ((W : ℝ) / r) ^ n * K₃ * 1 :=
              mul_le_mul_of_nonneg_left hWd1 (by positivity)
          _ = 2 ^ n * K₃ * ((W : ℝ) / r) ^ n := by ring
          _ ≤ 2 ^ n * K₃ * (2 ^ D * X) := mul_le_mul_of_nonneg_left h2 (by positivity)
      have ht2 : (L : ℝ) ^ n * K₄ * ((W : ℝ) ^ N₂)⁻¹ ≤ K₄ * (2 ^ D * X) := by
        have h2 := exp_window_le (n := n) (N := N₂) hL1 hc₁ hLW hD hN₂ hrW hrL
        calc (L : ℝ) ^ n * K₄ * ((W : ℝ) ^ N₂)⁻¹ = K₄ * ((L : ℝ) ^ n * ((W : ℝ) ^ N₂)⁻¹) := by
              ring
          _ ≤ K₄ * (2 ^ D * X) := mul_le_mul_of_nonneg_left h2 hK₄0
      refine combine_tail hK₁0 hK₂0 (by positivity) h2D hX0 ?_ (herr.trans herr')
      calc _ ≤ _ := hM
        _ ≤ 2 ^ n * K₃ * (2 ^ D * X) + K₄ * (2 ^ D * X) := add_le_add ht1 ht2
        _ = (2 ^ n * K₃ + K₄) * (2 ^ D * X) := by ring
  have hminus : ‖Sminus m S x y‖ = ‖Splus m S x y‖ := by
    simp [Sminus, Matrix.map_apply]
  rw [hbound]
  exact ⟨hmainS, hminus ▸ hmainS⟩

/-- [I, Lemma 2.2] at `m = m(z)`, for every `z = E + iη` with `|E| < 2 − κ` and `η > 0`. -/
theorem Splus_decay_msc :
  ∀ (d : ℕ) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (κ τ D : ℝ) (hκ : 0 < κ) (hτ : 0 < τ)
    (hD : 0 < D),
    ∃ K W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ S : Matrix (Zd d L) (Zd d L) ℝ, IsSymKernel S → SymbolClose ψ C W S →
      ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → ∀ x y : Zd d L,
        ‖Splus (msc z) S x y‖ ≤ K * splusBound W τ D x y ∧
          ‖Sminus (msc z) S x y‖ ≤ K * splusBound W τ D x y := by
  intro d c₀ c₁ hc₀ hc₁ ψ c' hψ C κ τ D hκ hτ hD
  obtain ⟨K, W₀, h⟩ := Splus_decay d c₀ c₁ hc₀ hc₁ ψ c' hψ C (Real.sqrt (2 * κ) / 5) τ D
    (by positivity) hτ hD
  refine ⟨K, W₀, fun W L _ hadm hW S hS hSC z hz hE x y => ?_⟩
  obtain ⟨h1, h2⟩ := msc_bulk κ hκ z hz hE.le
  exact h W L hadm hW S hS hSC (msc z) h1 h2 x y


section Witness

end Witness

end RBM8D
