module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import RBM8D.Kernel.InfSymbol
public import RBM8D.Kernel.Circulant

@[expose] public section

/-!
# Shell kernels and decay on `ℤ^d`

Bounds of the shell and core kernels, the decay of `Θ_{ℤ^d}(a)`, `Θ_∞` ([I, (7.7)]) and `S^±_∞` ([I, (7.6)]).
-/

noncomputable section

set_option linter.unusedVariables false

open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace RBM8D

variable {d : ℕ}

/-- The kernel of the shell `j`: symbol `χ_j(p) F(ŝ(p))`. -/
def shellKernel (F : ℂ → ℂ) (s : (Fin d → ℤ) → ℝ) (W j : ℕ) (x : Fin d → ℤ) : ℂ :=
  latticeFourier (fun p => (shellCut W j p : ℂ) * F (zdSymbol s p)) x

open scoped ContDiff

/-! ## Elementary bounds -/

section Elementary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sqNorm_nonneg' (p : Fin d → ℝ) : 0 ≤ sqNorm p :=
  Finset.sum_nonneg fun i _ => sq_nonneg (p i)

/-- The sup norm is at most the Euclidean norm: `‖p‖² ≤ |p|²`. -/
private theorem norm_sq_le_sqNorm (p : Fin d → ℝ) : ‖p‖ ^ 2 ≤ sqNorm p := by
  have h : ‖p‖ ≤ Real.sqrt (sqNorm p) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => p i ^ 2)
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))
  calc ‖p‖ ^ 2 ≤ Real.sqrt (sqNorm p) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sqNorm p := Real.sq_sqrt (sqNorm_nonneg' p)

/-- `W ‖p‖ ≤ 2 / 2^j` when `W² |p|² ≤ 4 / 4^j`. -/
private theorem norm_le_of_sqNorm_le {W : ℝ} (hW : 0 < W) (j : ℕ) {p : Fin d → ℝ}
    (hp : W ^ 2 * sqNorm p ≤ 4 / 4 ^ j) : ‖p‖ ≤ 2 / (2 ^ j * W) := by
  have h1 : (W * ‖p‖) ^ 2 ≤ (2 / 2 ^ j) ^ 2 := by
    calc (W * ‖p‖) ^ 2 = W ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ W ^ 2 * sqNorm p := mul_le_mul_of_nonneg_left (norm_sq_le_sqNorm p) (by positivity)
      _ ≤ 4 / 4 ^ j := hp
      _ = (2 / 2 ^ j) ^ 2 := by
          rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have h2 : W * ‖p‖ ≤ 2 / 2 ^ j :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  rw [le_div_iff₀ (by positivity)]
  calc ‖p‖ * (2 ^ j * W) = 2 ^ j * (W * ‖p‖) := by ring
    _ ≤ 2 ^ j * (2 / 2 ^ j) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 := by field_simp

/-- A point with `W² |p|² ≤ 4` and `W ≥ 1` lies in the cube. -/
private theorem mem_cubePi_of_sqNorm_le {W : ℝ} (hW : 1 ≤ W) {p : Fin d → ℝ}
    (hp : W ^ 2 * sqNorm p ≤ 4) : p ∈ cubePi d := by
  intro i _
  have h1 : p i ^ 2 ≤ sqNorm p :=
    Finset.single_le_sum (f := fun i => p i ^ 2) (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have hW2 : 1 ≤ W ^ 2 := one_le_pow₀ hW
  have h2 : sqNorm p ≤ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hW2 (sqNorm_nonneg' p)]
  have h3 : |p i| ≤ 2 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt (p i ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  constructor <;> linarith [abs_le.1 h3]

/-- Points of the cube have sup norm at most `π`. -/
private theorem norm_le_pi_of_mem_cubePi {p : Fin d → ℝ} (hp : p ∈ cubePi d) : ‖p‖ ≤ Real.pi :=
  (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun i => by
    rw [Real.norm_eq_abs, abs_le]; exact hp i (Set.mem_univ i)

/-- `(1 + y/L)^N ≤ 2^N (1 + (y/L)^N)` turns the two integrations by parts (`N = 0` and `N`) into
a weighted bound. -/
private theorem mul_one_add_pow_le {K y L A₀ A₁ : ℝ} (N : ℕ) (hL : 0 < L) (hK : 0 ≤ K)
    (hy : 0 ≤ y) (h0 : K ≤ A₀) (h1 : K * y ^ N ≤ A₁ * L ^ N) :
    K * (1 + y / L) ^ N ≤ 2 ^ N * (A₀ + A₁) := by
  set t := y / L with ht
  have ht0 : 0 ≤ t := div_nonneg hy hL.le
  have hpow : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
    rcases le_total t 1 with h | h
    · calc (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
        _ ≤ 2 ^ N * (1 + t ^ N) := by
            have : 0 ≤ t ^ N := pow_nonneg ht0 N
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]
    · calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
        _ = 2 ^ N * t ^ N := mul_pow 2 t N
        _ ≤ 2 ^ N * (1 + t ^ N) := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]
  have hKt : K * t ^ N ≤ A₁ := by
    rw [ht, div_pow, mul_div_assoc', div_le_iff₀ (pow_pos hL N)]
    exact h1
  calc K * (1 + t) ^ N ≤ K * (2 ^ N * (1 + t ^ N)) := mul_le_mul_of_nonneg_left hpow hK
    _ = 2 ^ N * (K + K * t ^ N) := by ring
    _ ≤ 2 ^ N * (A₀ + A₁) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-- The iterated derivatives of a function vanishing near `x` vanish at `x`. -/
private theorem iteratedFDeriv_eq_zero_of_eventuallyEq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {x : E} (h : f =ᶠ[nhds x] 0) (n : ℕ) :
    iteratedFDeriv ℝ n f x = 0 := by
  have := (h.iteratedFDeriv ℝ n).eq_of_nhds
  rw [this]
  have : (0 : E → F) = fun _ => (0 : F) := rfl
  rw [this]
  cases n with
  | zero => ext; simp
  | succ n => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]; rfl

/-- Casting a real function to `ℂ` preserves the norms of its iterated derivatives. -/
private theorem norm_iteratedFDeriv_ofReal {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => (f y : ℂ)) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  have h := LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (x := x) (i := n)
    Complex.ofRealLI hf.contDiffAt (by exact_mod_cast le_top)
  exact h

/-- Leibniz bound: if `‖D^i f‖ ≤ A L^i` and `‖D^i g‖ ≤ B L^i` at `x` for `i ≤ n`, then
`‖D^n (f g)(x)‖ ≤ 2^n A B L^n`. -/
private theorem norm_iteratedFDeriv_mul_le_of {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : E) (n : ℕ) {A B L : ℝ} (hL : 0 ≤ L)
    (hA : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A * L ^ i)
    (hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B * L ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2 ^ n * A * B * L ^ n := by
  refine (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
      ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ (n.choose i : ℝ) * (A * B * L ^ n) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hA i hi'
    have h2 := hB (n - i) (Nat.sub_le n i)
    have h1' : 0 ≤ A * L ^ i := (norm_nonneg _).trans h1
    have hLn : L ^ i * L ^ (n - i) = L ^ n := by rw [← pow_add, Nat.add_sub_cancel' hi']
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
        ≤ (n.choose i : ℝ) * (A * L ^ i) * (B * L ^ (n - i)) := by
          gcongr
      _ = (n.choose i : ℝ) * (A * B * (L ^ i * L ^ (n - i))) := by ring
      _ = (n.choose i : ℝ) * (A * B * L ^ n) := by rw [hLn]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [this]; ring

/-- Leibniz bound for `f^l Ψ`: if `‖D^i f‖, ‖D^i Ψ‖ ≤ K L^i` at `x` for `i ≤ m`, then for `k ≤ m`,
`‖D^k (f^l Ψ)(x)‖ ≤ Q_l L^k`, with the extra factor `‖f(x)‖` when `k < l`. -/
private theorem norm_iteratedFDeriv_pow_mul_le {f Ψ : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hΨ : ContDiff ℝ ∞ Ψ) (x : E) (m : ℕ) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hfx : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ K * L ^ i)
    (hΨx : ∀ i ≤ m, ‖iteratedFDeriv ℝ i Ψ x‖ ≤ K * L ^ i) (l : ℕ) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y => f y ^ l * Ψ y) x‖ ≤
      (2 ^ m * (max 1 K) ^ 2) ^ l * K * L ^ k * (if k < l then ‖f x‖ else 1) := by
  have hK1 : K ≤ max 1 K := le_max_right _ _
  have h1K : (1 : ℝ) ≤ max 1 K := le_max_left _ _
  have hfx0 : ‖f x‖ ≤ K := by simpa using hfx 0 (Nat.zero_le _)
  have hfac : ∀ k' l' : ℕ, (if k' < l' then ‖f x‖ else (1 : ℝ)) ≤ max 1 K := by
    intro k' l'
    split_ifs
    · exact hfx0.trans hK1
    · exact h1K
  have hfac0 : ∀ k' l' : ℕ, 0 ≤ (if k' < l' then ‖f x‖ else (1 : ℝ)) := by
    intro k' l'; split_ifs <;> positivity
  induction l with
  | zero =>
    intro k hk
    simp only [pow_zero, one_mul, Nat.not_lt_zero, ↓reduceIte, mul_one]
    exact hΨx k hk
  | succ l ih =>
    intro k hk
    set Q := (2 ^ m * (max 1 K) ^ 2) ^ l * K with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have hcont : ContDiff ℝ ∞ (fun y => f y ^ l * Ψ y) := (hf.pow l).mul hΨ
    have heq : (fun y => f y ^ (l + 1) * Ψ y) = fun y => f y * (f y ^ l * Ψ y) := by
      funext y; ring
    rw [heq]
    refine (norm_iteratedFDeriv_mul_le hf hcont x (by exact_mod_cast le_top)).trans ?_
    set fac : ℝ := (if k < l + 1 then ‖f x‖ else 1) with hfacdef
    have hfac0' : 0 ≤ fac := hfac0 k (l + 1)
    have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun y => f y ^ l * Ψ y) x‖ ≤
        (k.choose i : ℝ) * ((max 1 K) ^ 2 * Q * L ^ k * fac) := by
      intro i hi
      have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hb := ih (k - i) (by omega)
      have hLk : L ^ i * L ^ (k - i) = L ^ k := by rw [← pow_add, Nat.add_sub_cancel' hi']
      have hc0 : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
      have hfi := hfx i (hi'.trans hk)
      have hM2 : max 1 K ≤ (max 1 K) ^ 2 := by nlinarith
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hc0
      by_cases hkl : k < l + 1
      · have hfe : fac = ‖f x‖ := by simp only [hfacdef, hkl, ↓reduceIte]
        rw [hfe]
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [norm_iteratedFDeriv_zero, Nat.sub_zero]
          have hb' := ih k (by omega)
          have := hfac k l
          calc ‖f x‖ * ‖iteratedFDeriv ℝ k (fun y => f y ^ l * Ψ y) x‖
              ≤ ‖f x‖ * (Q * L ^ k * max 1 K) := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                refine hb'.trans ?_
                exact mul_le_mul_of_nonneg_left this (by positivity)
            _ ≤ ‖f x‖ * (Q * L ^ k * (max 1 K) ^ 2) := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hM2 (by positivity)
            _ = (max 1 K) ^ 2 * Q * L ^ k * ‖f x‖ := by ring
        · have hlt : k - i < l := by omega
          simp only [hlt, ↓reduceIte] at hb
          calc ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) (fun y => f y ^ l * Ψ y) x‖
              ≤ (K * L ^ i) * (Q * L ^ (k - i) * ‖f x‖) :=
                mul_le_mul hfi hb (norm_nonneg _) (by positivity)
            _ = K * Q * (L ^ i * L ^ (k - i)) * ‖f x‖ := by ring
            _ ≤ (max 1 K) ^ 2 * Q * (L ^ i * L ^ (k - i)) * ‖f x‖ := by
                gcongr
                exact hK1.trans hM2
            _ = (max 1 K) ^ 2 * Q * L ^ k * ‖f x‖ := by rw [hLk]
      · have hfe : fac = 1 := by simp only [hfacdef, hkl, ↓reduceIte]
        rw [hfe]
        have := hfac (k - i) l
        calc ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) (fun y => f y ^ l * Ψ y) x‖
            ≤ (K * L ^ i) * (Q * L ^ (k - i) * max 1 K) := by
              refine mul_le_mul hfi (hb.trans ?_) (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left this (by positivity)
          _ = K * max 1 K * Q * (L ^ i * L ^ (k - i)) := by ring
          _ ≤ max 1 K * max 1 K * Q * (L ^ i * L ^ (k - i)) := by gcongr
          _ = (max 1 K) ^ 2 * Q * L ^ k * 1 := by rw [hLk]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hs : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    rw [hs]
    have h2 : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk
    calc (2 : ℝ) ^ k * ((max 1 K) ^ 2 * Q * L ^ k * fac)
        ≤ 2 ^ m * ((max 1 K) ^ 2 * Q * L ^ k * fac) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2 ^ m * (max 1 K) ^ 2) ^ (l + 1) * K * L ^ k * fac := by
          rw [hQ, pow_succ]; ring

end Elementary

/-! ## A smooth inverse -/

section CutInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `u ↦ 1/u` on `[b, ∞)`, cut off smoothly to `0` on `(-∞, b/2]`. -/
private def cinv (b u : ℝ) : ℝ := Real.smoothTransition ((u - b / 2) / (b / 2)) * u⁻¹

private theorem cinv_eq {b u : ℝ} (hb : 0 < b) (hu : b ≤ u) : cinv b u = u⁻¹ := by
  unfold cinv
  rw [Real.smoothTransition.one_of_one_le, one_mul]
  rw [le_div_iff₀ (by positivity)]; linarith

private theorem cinv_eq_zero {b u : ℝ} (hb : 0 < b) (hu : u ≤ b / 2) : cinv b u = 0 := by
  unfold cinv
  rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

private theorem contDiff_cinv {b : ℝ} (hb : 0 < b) : ContDiff ℝ ∞ (cinv b) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge 0 u with hu | hu
  · have h1 : ContDiff ℝ ∞ fun u : ℝ => Real.smoothTransition ((u - b / 2) / (b / 2)) :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact h1.contDiffAt.mul (contDiffAt_inv ℝ hu.ne')
  · have : cinv b =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show u < b / 2 by linarith)] with v hv
      exact cinv_eq_zero hb hv.le
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- The iterated derivatives of `cinv b` are bounded on `ℝ`. -/
private theorem cinv_deriv_bound {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ u, ‖iteratedFDeriv ℝ n (cinv b) u‖ ≤ C := by
  have hc : Continuous fun u => iteratedFDeriv ℝ n (cinv b) u :=
    (contDiff_cinv hb).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := b / 2) (b := b)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max (max C₁ 0) (n.factorial / b ^ (n + 1)), le_max_of_le_left (le_max_right _ _),
    fun u => ?_⟩
  rcases lt_or_ge u (b / 2) with h | h
  · have hz : cinv b =ᶠ[nhds u] 0 := by
      filter_upwards [Iio_mem_nhds h] with v hv
      exact cinv_eq_zero hb hv.le
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq hz, norm_zero]
    exact le_max_of_le_left (le_max_right _ _)
  · rcases le_or_gt u b with h' | h'
    · exact (hC₁ u ⟨h, h'⟩).trans (le_max_of_le_left (le_max_left _ _))
    · have he : cinv b =ᶠ[nhds u] Inv.inv := by
        filter_upwards [Ioi_mem_nhds h'] with v hv
        exact cinv_eq hb (le_of_lt hv)
      rw [(he.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedDeriv_eq_iterate, iter_deriv_inv]
      have hu0 : 0 < u := by linarith
      have hz : u ^ (-1 - (n : ℤ)) = (u ^ (n + 1))⁻¹ := by
        rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg,
          zpow_natCast]
      rw [hz, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_inv, abs_of_pos (pow_pos hu0 _), abs_of_nonneg (Nat.cast_nonneg _)]
      refine le_max_of_le_right ?_
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hb _)
        (pow_le_pow_left₀ hb.le h'.le _)

/-- Faà di Bruno for `cinv b ∘ h`: if `‖D^i h(x)‖ ≤ Λ^i` for `1 ≤ i ≤ n`, then
`‖D^i (cinv b ∘ h)(x)‖ ≤ C Λ^i` for `i ≤ n`. -/
private theorem norm_iteratedFDeriv_cinv_comp_le {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (h : E → ℝ), ContDiff ℝ ∞ h → ∀ (x : E) (Λ : ℝ), 0 ≤ Λ →
      (∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i h x‖ ≤ Λ ^ i) →
      ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun y => cinv b (h y)) x‖ ≤ C * Λ ^ i := by
  choose Cι hCι0 hCι using cinv_deriv_bound hb
  set S := ∑ k ∈ Finset.range (n + 1), Cι k with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => hCι0 k
  refine ⟨n.factorial * S, by positivity, fun h hh x Λ hΛ hD i hi => ?_⟩
  have hC : ∀ k, k ≤ i → ‖iteratedFDeriv ℝ k (cinv b) (h x)‖ ≤ S := fun k hk =>
    (hCι k (h x)).trans (Finset.single_le_sum (f := Cι) (fun k _ => hCι0 k)
      (Finset.mem_range.2 (by omega)))
  have hD' : ∀ k, 1 ≤ k → k ≤ i → ‖iteratedFDeriv ℝ k h x‖ ≤ Λ ^ k := fun k hk1 hk =>
    hD k hk1 (hk.trans hi)
  have := norm_iteratedFDeriv_comp_le (contDiff_cinv hb) hh (by exact_mod_cast le_top) x hC hD'
  refine this.trans ?_
  have hfac : (i.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hi
  have : 0 ≤ S * Λ ^ i := by positivity
  calc (i.factorial : ℝ) * S * Λ ^ i = i.factorial * (S * Λ ^ i) := by ring
    _ ≤ n.factorial * (S * Λ ^ i) := mul_le_mul_of_nonneg_right hfac this
    _ = n.factorial * S * Λ ^ i := by ring

end CutInverse

/-! ## The symbol of an `InfKernel` -/

section Symbol

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ} {W : ℕ} {s : (Fin d → ℤ) → ℝ}

private theorem two_lt_pi : 2 < Real.pi := by
  refine lt_of_le_of_ne Real.two_le_pi fun h => ?_
  have := Real.sin_pos_of_pos_of_le_two (x := 2) two_pos le_rfl
  rw [h, Real.sin_pi] at this
  exact lt_irrefl _ this

private theorem InfKernel.summable_s (hs : InfKernel ψ C W s) : Summable s := by
  by_contra h
  have := hs.sum_one
  rw [tsum_eq_zero_of_not_summable h] at this
  exact zero_ne_one this

private theorem InfKernel.summable_abs (hs : InfKernel ψ C W s) : Summable fun x => |s x| :=
  summable_abs_iff.2 hs.summable_s

private theorem InfKernel.im_eq (hs : InfKernel ψ C W s) (p : Fin d → ℝ) :
    (zdSymbol s p).im = 0 :=
  zdSymbol_im s hs.symm hs.summable_s p

private theorem zexp_neg_left (p : Fin d → ℝ) (x : Fin d → ℤ) : zexp (-p) x = conj (zexp p x) := by
  unfold zexp
  rw [← Complex.exp_conj]
  congr 1
  simp [Finset.sum_neg_distrib]

private theorem InfKernel.zdSymbol_neg (hs : InfKernel ψ C W s) (p : Fin d → ℝ) :
    zdSymbol s (-p) = zdSymbol s p := by
  have h1 : zdSymbol s (-p) = conj (zdSymbol s p) := by
    unfold zdSymbol zdSeries
    rw [Complex.conj_tsum]
    refine tsum_congr fun x => ?_
    rw [map_mul, Complex.conj_ofReal, zexp_neg_left]
  rw [h1, Complex.conj_eq_iff_im.2 (hs.im_eq p)]

/-- The symbol is even, so its derivative vanishes at `0`. -/
private theorem InfKernel.fderiv_zero (hs : InfKernel ψ C W s)
    (hd : DifferentiableAt ℝ (zdSymbol s) 0) : fderiv ℝ (zdSymbol s) 0 = 0 := by
  set f := zdSymbol s with hf
  have h0 : HasFDerivAt f (fderiv ℝ f 0) (-(0 : Fin d → ℝ)) := by
    rw [neg_zero]; exact hd.hasFDerivAt
  have h1 : HasFDerivAt (fun p => f (-p))
      ((fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ (Fin d → ℝ))) 0 :=
    h0.comp 0 (hasFDerivAt_id (0 : Fin d → ℝ)).neg
  have h2 : (fun p => f (-p)) = f := funext fun p => hs.zdSymbol_neg p
  rw [h2] at h1
  have h3 := h1.fderiv
  have h4 : (fderiv ℝ f 0).comp (-ContinuousLinearMap.id ℝ (Fin d → ℝ)) = -fderiv ℝ f 0 := by
    ext v; simp
  rw [h4] at h3
  ext v
  have hv := congrArg (fun T : (Fin d → ℝ) →L[ℝ] ℂ => T v) h3
  simp only [_root_.neg_apply] at hv
  simp only [_root_.zero_apply]
  linear_combination hv / 2

/-- Mean value bound for the derivative: `‖Df(p)‖ ≤ K ‖p‖` when `Df(0) = 0` and `‖D²f‖ ≤ K`. -/
private theorem norm_fderiv_le_of_zero {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (h0 : fderiv ℝ f 0 = 0) {K : ℝ} (h2 : ∀ q, ‖iteratedFDeriv ℝ 2 f q‖ ≤ K) (p : E) :
    ‖fderiv ℝ f p‖ ≤ K * ‖p‖ := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ f) (s := Set.univ)
    (x := 0) (y := p) (fun x _ => hd x) (fun q _ => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact h2 q)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  rwa [h0, sub_zero, sub_zero] at this

/-- Taking real parts does not increase the norms of iterated derivatives. -/
private theorem norm_iteratedFDeriv_re_le {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => (f y).re) x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  have hre : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
      simpa using Complex.abs_re_le_norm z
  have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (x := x) (n := n)
    Complex.reCLM hf.contDiffAt (by exact_mod_cast le_top)
  refine this.trans ?_
  calc ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ n f x‖
      ≤ 1 * ‖iteratedFDeriv ℝ n f x‖ := mul_le_mul_of_nonneg_right hre (norm_nonneg _)
    _ = _ := one_mul _

end Symbol

/-! ## Periodisation of a function supported near `0` -/

section Periodize

/-- The lattice translation `2π k`. -/
private def tr (k : Fin d → ℤ) : Fin d → ℝ := fun i => 2 * Real.pi * (k i : ℝ)

private theorem norm_tr_apply (k : Fin d → ℤ) (i : Fin d) :
    ‖tr k i‖ = 2 * Real.pi * |(k i : ℝ)| := by
  simp [tr, abs_of_pos Real.pi_pos]

private theorem two_pi_le_norm_tr {k : Fin d → ℤ} (hk : k ≠ 0) : 2 * Real.pi ≤ ‖tr k‖ := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
  calc 2 * Real.pi ≤ 2 * Real.pi * |(k i : ℝ)| := le_mul_of_one_le_right (by positivity) h1
    _ = ‖tr k i‖ := (norm_tr_apply k i).symm
    _ ≤ ‖tr k‖ := norm_le_pi_norm _ i

/-- The periodisation `Σ_k H(p - 2πk)`. -/
private def perz (H : (Fin d → ℝ) → ℂ) (p : Fin d → ℝ) : ℂ := ∑' k : Fin d → ℤ, H (p - tr k)

variable {H : (Fin d → ℝ) → ℂ}

private theorem perz_eq_sum (hH : ∀ p, 2 ≤ ‖p‖ → H p = 0) (p₀ : Fin d → ℝ) :
    ∃ R : ℕ, ∀ q, ‖q - p₀‖ < 1 → perz H q = ∑ k ∈ boxZ d R, H (q - tr k) := by
  refine ⟨⌈(‖p₀‖ + 3) / (2 * Real.pi)⌉₊, fun q hq => ?_⟩
  unfold perz
  apply tsum_eq_sum
  intro k hk
  apply hH
  by_contra hlt
  push Not at hlt
  apply hk
  simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : ‖tr k‖ < ‖p₀‖ + 3 := by
    have hq' : ‖q‖ ≤ ‖p₀‖ + ‖q - p₀‖ := by
      calc ‖q‖ = ‖p₀ + (q - p₀)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    calc ‖tr k‖ = ‖q - (q - tr k)‖ := by congr 1; abel
      _ ≤ ‖q‖ + ‖q - tr k‖ := norm_sub_le _ _
      _ < (‖p₀‖ + 1) + 2 := by linarith
      _ = ‖p₀‖ + 3 := by ring
  have h2 : 2 * Real.pi * |(k i : ℝ)| < ‖p₀‖ + 3 := by
    calc 2 * Real.pi * |(k i : ℝ)| = ‖tr k i‖ := (norm_tr_apply k i).symm
      _ ≤ ‖tr k‖ := norm_le_pi_norm _ i
      _ < _ := h1
  have h3 : |(k i : ℝ)| ≤ ⌈(‖p₀‖ + 3) / (2 * Real.pi)⌉₊ := by
    have : |(k i : ℝ)| < (‖p₀‖ + 3) / (2 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    exact this.le.trans (Nat.le_ceil _)
  have h4 : |k i| ≤ (⌈(‖p₀‖ + 3) / (2 * Real.pi)⌉₊ : ℤ) := by
    have : ((|k i| : ℤ) : ℝ) ≤ ((⌈(‖p₀‖ + 3) / (2 * Real.pi)⌉₊ : ℕ) : ℝ) := by
      rw [Int.cast_abs]; exact h3
    exact_mod_cast this
  exact abs_le.1 h4

private theorem contDiff_perz {n : ℕ} (hc : ContDiff ℝ n H) (hH : ∀ p, 2 ≤ ‖p‖ → H p = 0) :
    ContDiff ℝ n (perz H) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  obtain ⟨R, hR⟩ := perz_eq_sum hH p₀
  have hfin : ContDiff ℝ n (fun q => ∑ k ∈ boxZ d R, H (q - tr k)) :=
    ContDiff.sum fun k _ => hc.comp (contDiff_id.sub contDiff_const)
  refine hfin.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds p₀ one_pos] with q hq
  exact hR q (by rwa [Metric.mem_ball, dist_eq_norm] at hq)

private theorem perz_add_single (i : Fin d) (p : Fin d → ℝ) :
    perz H (p + Pi.single i (2 * Real.pi)) = perz H p := by
  unfold perz
  conv_lhs => rw [← (Equiv.addRight (Pi.single i (1 : ℤ))).tsum_eq]
  refine tsum_congr fun k => ?_
  congr 1
  funext l
  simp only [Pi.add_apply, Pi.sub_apply, Equiv.coe_addRight, tr, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

private theorem perz_eq_self (hH : ∀ p, 2 ≤ ‖p‖ → H p = 0) {p : Fin d → ℝ}
    (hp : ‖p‖ < 2 * Real.pi - 2) : perz H p = H p := by
  unfold perz
  rw [tsum_eq_single 0]
  · have : tr (0 : Fin d → ℤ) = 0 := by funext i; simp [tr]
    rw [this, sub_zero]
  · intro k hk
    apply hH
    have h1 := two_pi_le_norm_tr hk
    have h2 := norm_sub_norm_le (tr k) p
    rw [norm_sub_rev] at h2
    linarith

/-- Integration by parts for a `C^N` function vanishing for `‖p‖ ≥ 2` (supported inside the
open cube), through its periodisation. -/
private theorem norm_latticeFourier_mul_pow_le_of_support (N : ℕ) (hc : ContDiff ℝ N H)
    (hH : ∀ p, 2 ≤ ‖p‖ → H p = 0) (x : Fin d → ℤ) :
    ‖latticeFourier H x‖ * (zdInf x : ℝ) ^ N ≤
      ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖iteratedFDeriv ℝ N H p‖ := by
  have hpi := two_lt_pi
  have hU : ∀ p ∈ cubePi d, ‖p‖ < 2 * Real.pi - 2 := fun p hp => by
    have := norm_le_pi_of_mem_cubePi hp; linarith
  have hev : ∀ p ∈ cubePi d, perz H =ᶠ[nhds p] H := fun p hp => by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds (hU p hp)] with q hq
    exact perz_eq_self hH hq
  have hmeas : MeasurableSet (cubePi d) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have h1 : latticeFourier (perz H) x = latticeFourier H x := by
    unfold latticeFourier
    congr 1
    refine setIntegral_congr_fun hmeas fun p hp => ?_
    simp only [(hev p hp).eq_of_nhds]
  have h2 : ∫ p in cubePi d, ‖iteratedFDeriv ℝ N (perz H) p‖ =
      ∫ p in cubePi d, ‖iteratedFDeriv ℝ N H p‖ :=
    setIntegral_congr_fun hmeas fun p hp => by
      simp only [((hev p hp).iteratedFDeriv ℝ N).eq_of_nhds]
  have := norm_latticeFourier_mul_pow_le N (perz H) (contDiff_perz hc hH)
    (fun i p => perz_add_single i p) x
  rwa [h1, h2] at this

end Periodize

/-! ## Weighted bounds for Fourier coefficients -/

section Weighted

private theorem measurableSet_cubePi' : MeasurableSet (cubePi d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

private theorem isCompact_cubePi'' : IsCompact (cubePi d) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- `∫_{[-π,π]^d} f ≤ A (2r)^d` for continuous `0 ≤ f ≤ A` vanishing outside the closed ball of
radius `r`. -/
private theorem setIntegral_cubePi_le_of_support {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hf0 : ∀ p, 0 ≤ f p) {A r : ℝ} (hr : 0 ≤ r) (hA : ∀ p, f p ≤ A)
    (hsupp : ∀ p, r < ‖p‖ → f p = 0) : ∫ p in cubePi d, f p ≤ A * (2 * r) ^ d := by
  set g : (Fin d → ℝ) → ℝ := (Metric.closedBall (0 : Fin d → ℝ) r).indicator fun _ => A
  have hfg : ∀ p, f p ≤ g p := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : Fin d → ℝ) r
    · simp only [g, Set.indicator_of_mem hp]; exact hA p
    · simp only [g, Set.indicator_of_notMem hp]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hp
      rw [hsupp p hp]
  have hgi : Integrable g := by
    refine (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 ?_
    exact integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne
  have hg0 : ∀ p, 0 ≤ g p := fun p => (hf0 p).trans (hfg p)
  calc ∫ p in cubePi d, f p ≤ ∫ p in cubePi d, g p :=
        setIntegral_mono_on (hf.continuousOn.integrableOn_compact isCompact_cubePi'')
          hgi.integrableOn measurableSet_cubePi' fun p _ => hfg p
    _ ≤ ∫ p, g p := setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)
    _ = A * (2 * r) ^ d := by
        rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, Measure.real,
          Real.volume_pi_closedBall _ hr, ENNReal.toReal_ofReal (by positivity),
          Fintype.card_fin, smul_eq_mul, mul_comm]

/-- Weighted bound for a smooth function supported in the ball of radius `r ≤ 2`:
`|K(x)| (1 + |x|/L)^M ≤ 2^M (2π)^{-d} (2r)^d (A₀ + A₁)` if `|H| ≤ A₀` and `‖D^M H‖ ≤ A₁ L^M`. -/
private theorem kernel_bound_of_support (M : ℕ) {H : (Fin d → ℝ) → ℂ} (hc : ContDiff ℝ ∞ H)
    {r L A₀ A₁ : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2) (hL : 0 < L) (hH : ∀ p, r ≤ ‖p‖ → H p = 0)
    (h0 : ∀ p, ‖H p‖ ≤ A₀) (h1 : ∀ p, ‖iteratedFDeriv ℝ M H p‖ ≤ A₁ * L ^ M)
    (x : Fin d → ℤ) :
    ‖latticeFourier H x‖ * (1 + (zdInf x : ℝ) / L) ^ M ≤
      2 ^ M * (((2 * Real.pi) ^ d)⁻¹ * (2 * r) ^ d * (A₀ + A₁)) := by
  have hH2 : ∀ p, 2 ≤ ‖p‖ → H p = 0 := fun p hp => hH p (hr.trans hp)
  have hc' : ∀ N : ℕ, ContDiff ℝ N H := fun N => hc.of_le (by exact_mod_cast le_top)
  have hcpi : (0 : ℝ) ≤ ((2 * Real.pi) ^ d)⁻¹ := by positivity
  have hzero : ∀ p, r < ‖p‖ → iteratedFDeriv ℝ M H p = 0 := by
    intro p hp
    apply iteratedFDeriv_eq_zero_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hp] with q hq
    exact hH q hq.le
  have hI0 : ∫ p in cubePi d, ‖iteratedFDeriv ℝ 0 H p‖ ≤ A₀ * (2 * r) ^ d := by
    simp only [norm_iteratedFDeriv_zero]
    exact setIntegral_cubePi_le_of_support hc.continuous.norm (fun p => norm_nonneg _) hr0 h0
      fun p hp => by rw [hH p hp.le, norm_zero]
  have hI1 : ∫ p in cubePi d, ‖iteratedFDeriv ℝ M H p‖ ≤ A₁ * L ^ M * (2 * r) ^ d :=
    setIntegral_cubePi_le_of_support
      ((hc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm)
      (fun p => norm_nonneg _) hr0 h1 fun p hp => by rw [hzero p hp, norm_zero]
  have k0 := norm_latticeFourier_mul_pow_le_of_support 0 (hc' 0) hH2 x
  have k1 := norm_latticeFourier_mul_pow_le_of_support M (hc' M) hH2 x
  rw [pow_zero, mul_one] at k0
  refine (mul_one_add_pow_le (A₀ := ((2 * Real.pi) ^ d)⁻¹ * (A₀ * (2 * r) ^ d))
    (A₁ := ((2 * Real.pi) ^ d)⁻¹ * A₁ * (2 * r) ^ d) M hL (norm_nonneg _) (Nat.cast_nonneg _)
    ?_ ?_).trans (le_of_eq ?_)
  · exact k0.trans (mul_le_mul_of_nonneg_left hI0 hcpi)
  · refine k1.trans ?_
    calc ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖iteratedFDeriv ℝ M H p‖
        ≤ ((2 * Real.pi) ^ d)⁻¹ * (A₁ * L ^ M * (2 * r) ^ d) :=
          mul_le_mul_of_nonneg_left hI1 hcpi
      _ = ((2 * Real.pi) ^ d)⁻¹ * A₁ * (2 * r) ^ d * L ^ M := by ring
  · ring

/-- Weighted bound for a smooth `2π`-periodic function from two integrations by parts. -/
private theorem kernel_bound_of_periodic (M : ℕ) {G : (Fin d → ℝ) → ℂ} (hc : ContDiff ℝ ∞ G)
    (hper : ∀ (i : Fin d) (p : Fin d → ℝ), G (p + Pi.single i (2 * Real.pi)) = G p)
    {L A₀ A₁ : ℝ} (hL : 0 < L)
    (h0 : ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖G p‖ ≤ A₀)
    (h1 : ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖iteratedFDeriv ℝ M G p‖ ≤ A₁ * L ^ M)
    (x : Fin d → ℤ) :
    ‖latticeFourier G x‖ * (1 + (zdInf x : ℝ) / L) ^ M ≤ 2 ^ M * (A₀ + A₁) := by
  have hc' : ∀ N : ℕ, ContDiff ℝ N G := fun N => hc.of_le (by exact_mod_cast le_top)
  have k0 := norm_latticeFourier_mul_pow_le 0 G (hc' 0) hper x
  have k1 := norm_latticeFourier_mul_pow_le M G (hc' M) hper x
  rw [pow_zero, mul_one] at k0
  simp only [norm_iteratedFDeriv_zero] at k0
  exact mul_one_add_pow_le M hL (norm_nonneg _) (Nat.cast_nonneg _) (k0.trans h0) (k1.trans h1)

end Weighted

/-! ## Shell and core pieces -/

section Pieces

/-- Derivatives of an affine image `c₀ + c₁ f`. -/
private theorem norm_iteratedFDeriv_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (c₀ c₁ : ℝ) {k : ℕ} (hk : k ≠ 0) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => c₀ + c₁ * f y) x‖ = |c₁| * ‖iteratedFDeriv ℝ k f x‖ := by
  have he : (fun y => c₀ + c₁ * f y) = (fun _ => c₀) + c₁ • f := by
    funext y; simp [smul_eq_mul]
  have h2 : ContDiffAt ℝ k (c₁ • f) x :=
    (show ContDiff ℝ ∞ (c₁ • f) from hf.const_smul c₁).contDiffAt.of_le
      (by exact_mod_cast le_top)
  rw [he, iteratedFDeriv_add_apply (f := fun _ => c₀) (g := c₁ • f) contDiffAt_const h2,
    iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_add,
    iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
    Real.norm_eq_abs]

/-- The smooth symbol of a shell or core piece at scale `j`:
`χ(p) (4^j cinv_b(4^j (1 - a Re ŝ(p))) - 1)`, equal to `χ(p) a ŝ/(1 - a ŝ)` where
`4^j (1 - a ŝ) ≥ b`. -/
private def pieceSym (χ : (Fin d → ℝ) → ℝ) (b a : ℝ) (j : ℕ) (s : (Fin d → ℤ) → ℝ)
    (p : Fin d → ℝ) : ℂ :=
  (χ p : ℂ) * (((4 : ℝ) ^ j * cinv b ((4 : ℝ) ^ j * (1 - a * (zdSymbol s p).re)) - 1 : ℝ) : ℂ)

private theorem contDiff_pieceSym {χ : (Fin d → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ) {b : ℝ}
    (hb : 0 < b) (a : ℝ) (j : ℕ) {s : (Fin d → ℤ) → ℝ} (hs : ContDiff ℝ ∞ (zdSymbol s)) :
    ContDiff ℝ ∞ (pieceSym χ b a j s) := by
  unfold pieceSym
  have hσ : ContDiff ℝ ∞ fun p => (zdSymbol s p).re := Complex.reCLM.contDiff.comp hs
  have hG : ContDiff ℝ ∞ fun p =>
      ((4 : ℝ) ^ j * cinv b ((4 : ℝ) ^ j * (1 - a * (zdSymbol s p).re)) - 1) :=
    (contDiff_const.mul ((contDiff_cinv hb).comp
      (contDiff_const.mul (contDiff_const.sub (contDiff_const.mul hσ))))).sub contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp hχ).mul (Complex.ofRealCLM.contDiff.comp hG)

/-- Scale-uniform derivative bounds of a piece: `‖D^n pieceSym(p)‖ ≤ B 4^j (2^j W)^n`, given
`‖D^i ŝ‖ ≤ K_i W^i`, `‖Dŝ(p)‖ ≤ K_2 W² ‖p‖`, `‖D^i χ‖ ≤ C_i (2^j W)^i`, and on the region `R`
outside of which `χ` vanishes, `W²|p|² ≤ 4/4^j` and `4^j (1 - a Re ŝ) ≥ b`. -/
private theorem pieceSym_deriv_le (K Cχ : ℕ → ℝ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ (W : ℝ) (j : ℕ) (a : ℝ) (s : (Fin d → ℤ) → ℝ) (χ : (Fin d → ℝ) → ℝ)
      (R : Set (Fin d → ℝ)), 1 ≤ W → 0 ≤ a → a ≤ 1 → ContDiff ℝ ∞ (zdSymbol s) →
      (∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * W ^ i) →
      (∀ p, ‖fderiv ℝ (zdSymbol s) p‖ ≤ K 2 * W ^ 2 * ‖p‖) →
      ContDiff ℝ ∞ χ → (∀ i p, ‖iteratedFDeriv ℝ i χ p‖ ≤ Cχ i * (2 ^ j * W) ^ i) →
      (∀ p ∉ R, χ =ᶠ[nhds p] 0) →
      (∀ p ∈ R, W ^ 2 * sqNorm p ≤ 4 / 4 ^ j ∧ b ≤ 4 ^ j * (1 - a * (zdSymbol s p).re)) →
      ∀ p, ‖iteratedFDeriv ℝ n (pieceSym χ b a j s) p‖ ≤ B * 4 ^ j * (2 ^ j * W) ^ n := by
  set Λ : ℝ := 1 + 2 * |K 2| + ∑ i ∈ Finset.range (n + 1), |K i| with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ ∑ i ∈ Finset.range (n + 1), |K i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have : 0 ≤ 2 * |K 2| := by positivity
    linarith
  obtain ⟨Cf, hCf0, hCf⟩ := norm_iteratedFDeriv_cinv_comp_le (E := Fin d → ℝ) hb n
  obtain ⟨Cι, hCι0, hCι⟩ := cinv_deriv_bound hb 0
  set Cχs : ℝ := ∑ i ∈ Finset.range (n + 1), |Cχ i| with hCχs
  have hCχs0 : 0 ≤ Cχs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set B' : ℝ := Cι + 1 + Cf * Λ ^ n with hB'
  have hB'0 : 0 ≤ B' := by positivity
  refine ⟨2 ^ n * Cχs * B', by positivity, ?_⟩
  intro W j a s χ R hW ha0 ha1 hs hK hK2 hχ hCχ hRχ hR p
  have hW0 : 0 < W := by linarith
  set L : ℝ := 2 ^ j * W with hL
  have hL0 : 0 ≤ L := by positivity
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  by_cases hp : p ∉ R
  · have hz : pieceSym χ b a j s =ᶠ[nhds p] 0 := by
      filter_upwards [hRχ p hp] with q hq
      simp only [pieceSym, Pi.zero_apply] at hq ⊢
      rw [hq]; simp
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq hz, norm_zero]
    positivity
  push Not at hp
  obtain ⟨hpR1, hpR2⟩ := hR p hp
  set σ : (Fin d → ℝ) → ℝ := fun q => (zdSymbol s q).re with hσdef
  have hσ : ContDiff ℝ ∞ σ := Complex.reCLM.contDiff.comp hs
  have hσK : ∀ i, ‖iteratedFDeriv ℝ i σ p‖ ≤ ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ :=
    fun i => norm_iteratedFDeriv_re_le hs i p
  set h : (Fin d → ℝ) → ℝ := fun q => (4 : ℝ) ^ j + (-((4 : ℝ) ^ j * a)) * σ q with hhdef
  have hh : ContDiff ℝ ∞ h := contDiff_const.add (contDiff_const.mul hσ)
  have hpn : ‖p‖ ≤ 2 / (2 ^ j * W) := norm_le_of_sqNorm_le hW0 j hpR1
  have hD : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k h p‖ ≤ (Λ * L) ^ k := by
    intro k hk1 hkn
    rw [hhdef, norm_iteratedFDeriv_affine hσ _ _ (by omega)]
    have habs : |(-((4 : ℝ) ^ j * a))| ≤ 4 ^ j := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      calc (4 : ℝ) ^ j * a ≤ 4 ^ j * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
        _ = 4 ^ j := mul_one _
    have hKk : |K k| ≤ Λ := by
      have : |K k| ≤ ∑ i ∈ Finset.range (n + 1), |K i| :=
        Finset.single_le_sum (f := fun i => |K i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
      have : 0 ≤ 2 * |K 2| := by positivity
      linarith
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk : k = 1 := by omega
      subst hk
      rw [norm_iteratedFDeriv_one] at *
      have h1 : ‖iteratedFDeriv ℝ 1 σ p‖ ≤ ‖fderiv ℝ (zdSymbol s) p‖ := by
        rw [← norm_iteratedFDeriv_one]; exact hσK 1
      rw [norm_iteratedFDeriv_one] at h1
      have h2 : ‖fderiv ℝ (zdSymbol s) p‖ ≤ |K 2| * W ^ 2 * (2 / (2 ^ j * W)) := by
        refine (hK2 p).trans ?_
        have : K 2 ≤ |K 2| := le_abs_self _
        gcongr
      have h3 : (4 : ℝ) ^ j * (|K 2| * W ^ 2 * (2 / (2 ^ j * W))) = 2 * |K 2| * L := by
        rw [hL, show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
        field_simp
      calc |(-((4 : ℝ) ^ j * a))| * ‖fderiv ℝ σ p‖
          ≤ 4 ^ j * ‖fderiv ℝ (zdSymbol s) p‖ :=
            mul_le_mul habs h1 (norm_nonneg _) (by positivity)
        _ ≤ 4 ^ j * (|K 2| * W ^ 2 * (2 / (2 ^ j * W))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * |K 2| * L := h3
        _ ≤ Λ * L := by
            apply mul_le_mul_of_nonneg_right _ hL0
            have : 0 ≤ ∑ i ∈ Finset.range (n + 1), |K i| :=
              Finset.sum_nonneg fun i _ => abs_nonneg _
            linarith
        _ = (Λ * L) ^ 1 := (pow_one _).symm
    · have h1 : ‖iteratedFDeriv ℝ k σ p‖ ≤ |K k| * W ^ k :=
        (hσK k).trans ((hK k p).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
      have h44 : (4 : ℝ) ^ j ≤ (2 ^ j) ^ k := by
        calc (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ (2 ^ j) ^ k := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hk2
      have hΛk : Λ ≤ Λ ^ k := by
        calc Λ = Λ ^ 1 := (pow_one _).symm
          _ ≤ Λ ^ k := pow_le_pow_right₀ hΛ1 (by omega)
      calc |(-((4 : ℝ) ^ j * a))| * ‖iteratedFDeriv ℝ k σ p‖
          ≤ 4 ^ j * (|K k| * W ^ k) := mul_le_mul habs h1 (norm_nonneg _) (by positivity)
        _ ≤ (2 ^ j) ^ k * (Λ ^ k * W ^ k) := by
            apply mul_le_mul h44 _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right (hKk.trans hΛk) (by positivity)
        _ = (Λ * L) ^ k := by rw [hL, mul_pow, mul_pow]; ring
  set φ : (Fin d → ℝ) → ℝ := fun q => cinv b (h q) with hφdef
  have hφ : ContDiff ℝ ∞ φ := (contDiff_cinv hb).comp hh
  set G : (Fin d → ℝ) → ℝ := fun q => (-1) + (4 : ℝ) ^ j * φ q with hGdef
  have hG : ContDiff ℝ ∞ G := contDiff_const.add (contDiff_const.mul hφ)
  have hpe : pieceSym χ b a j s = fun q => (χ q : ℂ) * (G q : ℂ) := by
    funext q
    simp only [pieceSym, hGdef, hφdef, hhdef, hσdef]
    congr 2
    ring_nf
  rw [hpe]
  have hA : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun q => (χ q : ℂ)) p‖ ≤ Cχs * L ^ i := by
    intro i hi
    rw [norm_iteratedFDeriv_ofReal hχ]
    refine (hCχ i p).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cχ i|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
  have hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun q => (G q : ℂ)) p‖ ≤ (4 ^ j * B') * L ^ i := by
    intro i hi
    rw [norm_iteratedFDeriv_ofReal hG]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
      have hc := hCι (h p)
      rw [norm_iteratedFDeriv_zero] at hc
      simp only [hGdef, hφdef]
      calc ‖(-1 : ℝ) + 4 ^ j * cinv b (h p)‖ ≤ 1 + 4 ^ j * Cι := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_neg, norm_one, norm_mul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 4 ^ j)]
            gcongr
        _ ≤ 4 ^ j * B' := by
            rw [hB']
            have : 0 ≤ Cf * Λ ^ n := by positivity
            nlinarith
    · rw [hGdef, norm_iteratedFDeriv_affine hφ _ _ (by omega),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ j)]
      have hc : ‖iteratedFDeriv ℝ i φ p‖ ≤ Cf * (Λ * L) ^ i :=
        hCf h hh p (Λ * L) (by positivity) hD i hi
      have hΛi : Λ ^ i ≤ Λ ^ n := pow_le_pow_right₀ hΛ1 hi
      calc (4 : ℝ) ^ j * ‖iteratedFDeriv ℝ i φ p‖ ≤ 4 ^ j * (Cf * (Λ * L) ^ i) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 4 ^ j * (Cf * Λ ^ i) * L ^ i := by rw [mul_pow]; ring
        _ ≤ 4 ^ j * B' * L ^ i := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hB']
            have : Cf * Λ ^ i ≤ Cf * Λ ^ n := mul_le_mul_of_nonneg_left hΛi hCf0
            linarith
  have := norm_iteratedFDeriv_mul_le_of (Complex.ofRealCLM.contDiff.comp hχ)
    (Complex.ofRealCLM.contDiff.comp hG) p n hL0 hA hB
  refine this.trans (le_of_eq ?_)
  ring

/-- `W ‖p‖ < 2 / 2^j` when `W² |p|² < 4 / 4^j`. -/
private theorem norm_lt_of_sqNorm_lt {W : ℝ} (hW : 0 < W) (j : ℕ) {p : Fin d → ℝ}
    (hp : W ^ 2 * sqNorm p < 4 / 4 ^ j) : ‖p‖ < 2 / (2 ^ j * W) := by
  have h1 : (W * ‖p‖) ^ 2 < (2 / 2 ^ j) ^ 2 := by
    calc (W * ‖p‖) ^ 2 = W ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ W ^ 2 * sqNorm p := mul_le_mul_of_nonneg_left (norm_sq_le_sqNorm p) (by positivity)
      _ < 4 / 4 ^ j := hp
      _ = (2 / 2 ^ j) ^ 2 := by
          rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
  have h2 : W * ‖p‖ < 2 / 2 ^ j :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  rw [lt_div_iff₀ (by positivity)]
  calc ‖p‖ * (2 ^ j * W) = 2 ^ j * (W * ‖p‖) := by ring
    _ < 2 ^ j * (2 / 2 ^ j) := mul_lt_mul_of_pos_left h2 (by positivity)
    _ = 2 := by field_simp

/-- The weighted kernel bound of a piece, uniformly in `a ∈ [0, 1]`:
`|K(x)| (1 + |x|/(2^j W))^M ≤ C₀ 4^j (2^j W)^{-d}` for the kernel with symbol
`χ(p) a ŝ(p)/(1 - a ŝ(p))`, where `χ` is a smooth real cutoff vanishing outside
`W²|p|² < 4/4^j`, with `‖D^i χ‖ ≤ Cχ_i (2^j W)^i`, and `4^j (1 - a Re ŝ) ≥ b` on the region
`R` outside of which `χ` vanishes; the symbol satisfies `‖D^i ŝ‖ ≤ K_i W^i` and
`‖Dŝ(p)‖ ≤ K_2 W² ‖p‖`. This is the dyadic piece estimate of the proofs of [I, (1.17)] and
[I, Lemma 7.3]. -/
theorem shellKernel_piece_kernel_bound (K Cχ : ℕ → ℝ) {b : ℝ} (hb : 0 < b) (M : ℕ) :
    ∃ C₀, 0 ≤ C₀ ∧ ∀ (W : ℝ) (j : ℕ) (a : ℝ) (s : (Fin d → ℤ) → ℝ) (χ : (Fin d → ℝ) → ℝ)
      (R : Set (Fin d → ℝ)), 1 ≤ W → 0 ≤ a → a ≤ 1 → ContDiff ℝ ∞ (zdSymbol s) →
      (∀ p, (zdSymbol s p).im = 0) →
      (∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * W ^ i) →
      (∀ p, ‖fderiv ℝ (zdSymbol s) p‖ ≤ K 2 * W ^ 2 * ‖p‖) →
      ContDiff ℝ ∞ χ → (∀ i p, ‖iteratedFDeriv ℝ i χ p‖ ≤ Cχ i * (2 ^ j * W) ^ i) →
      (∀ p ∉ R, χ =ᶠ[nhds p] 0) →
      (∀ p ∈ R, W ^ 2 * sqNorm p ≤ 4 / 4 ^ j ∧ b ≤ 4 ^ j * (1 - a * (zdSymbol s p).re)) →
      (∀ p, χ p ≠ 0 → W ^ 2 * sqNorm p < 4 / 4 ^ j) →
      ∀ x : Fin d → ℤ,
        ‖latticeFourier (fun p => (χ p : ℂ) *
            ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))) x‖ *
          (1 + (zdInf x : ℝ) / (2 ^ j * W)) ^ M ≤ C₀ * 4 ^ j / (2 ^ j * W) ^ d := by
  obtain ⟨B0, hB00, hB0⟩ := pieceSym_deriv_le (d := d) K Cχ hb 0
  obtain ⟨BM, hBM0, hBM⟩ := pieceSym_deriv_le (d := d) K Cχ hb M
  refine ⟨2 ^ M * (((2 * Real.pi) ^ d)⁻¹ * 4 ^ d * (B0 + BM)), by positivity, ?_⟩
  intro W j a s χ R hW ha0 ha1 hs him hK hK2 hχ hCχ hRχ hR hsupp x
  have hW0 : 0 < W := by linarith
  set L : ℝ := 2 ^ j * W with hL
  have hL0 : 0 < L := by positivity
  have hL1 : 1 ≤ L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hW
  set H := pieceSym χ b a j s with hHdef
  have hHc : ContDiff ℝ ∞ H := contDiff_pieceSym hχ hb a j hs
  have hmem : ∀ p, χ p ≠ 0 → p ∈ R := fun p hp => by
    by_contra hpR
    exact hp ((hRχ p hpR).eq_of_nhds)
  have heq : ∀ p, (χ p : ℂ) * ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p)) = H p := by
    intro p
    by_cases hχp : χ p = 0
    · simp [hHdef, pieceSym, hχp]
    obtain ⟨-, hbp⟩ := hR p (hmem p hχp)
    have hpos : 0 < 1 - a * (zdSymbol s p).re := by
      have : 0 < (4 : ℝ) ^ j * (1 - a * (zdSymbol s p).re) := lt_of_lt_of_le hb hbp
      exact pos_of_mul_pos_right this (by positivity)
    have hse : zdSymbol s p = ((zdSymbol s p).re : ℂ) :=
      Complex.ext (by simp) (by simp [him p])
    simp only [hHdef, pieceSym]
    rw [cinv_eq hb hbp, hse, Complex.ofReal_re]
    set t := (zdSymbol s p).re
    have hne : (1 : ℂ) - (a : ℂ) * (t : ℂ) ≠ 0 := by
      have : ((1 - a * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      simpa using this
    have h4 : (4 : ℝ) ^ j ≠ 0 := by positivity
    congr 1
    push_cast
    field_simp
    ring
  have hlf : latticeFourier (fun p => (χ p : ℂ) *
      ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))) x = latticeFourier H x := by
    unfold latticeFourier
    congr 1
    refine setIntegral_congr_fun measurableSet_cubePi' fun p _ => ?_
    simp only [heq p]
  rw [hlf]
  have hsuppH : ∀ p, 2 / L ≤ ‖p‖ → H p = 0 := by
    intro p hp
    by_contra hne
    have hχp : χ p ≠ 0 := by
      intro h0; apply hne; simp [hHdef, pieceSym, h0]
    have := norm_lt_of_sqNorm_lt hW0 j (hsupp p hχp)
    rw [← hL] at this
    linarith
  have h0 : ∀ p, ‖H p‖ ≤ B0 * 4 ^ j := by
    intro p
    have := hB0 W j a s χ R hW ha0 ha1 hs hK hK2 hχ hCχ hRχ hR p
    rwa [norm_iteratedFDeriv_zero, pow_zero, mul_one] at this
  have h1 : ∀ p, ‖iteratedFDeriv ℝ M H p‖ ≤ BM * 4 ^ j * L ^ M :=
    fun p => hBM W j a s χ R hW ha0 ha1 hs hK hK2 hχ hCχ hRχ hR p
  have hr2 : 2 / L ≤ 2 := by rw [div_le_iff₀ hL0]; nlinarith
  have := kernel_bound_of_support M hHc (by positivity) hr2 hL0 hsuppH h0 h1 x
  refine this.trans (le_of_eq ?_)
  rw [show 2 * (2 / L) = 4 / L by ring, div_pow]
  field_simp

end Pieces

/-! ## Cutoffs -/

section Cutoffs

private theorem contDiff_lowPass' : ContDiff ℝ ∞ lowPass :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)

private theorem contDiff_sqNorm' : ContDiff ℝ ∞ (sqNorm : (Fin d → ℝ) → ℝ) :=
  ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2

private theorem continuous_sqNorm' : Continuous (sqNorm : (Fin d → ℝ) → ℝ) :=
  contDiff_sqNorm'.continuous

private theorem contDiff_coreCut (W J : ℕ) : ContDiff ℝ ∞ (coreCut (d := d) W J) :=
  contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm')

private theorem contDiff_shellCut (W j : ℕ) : ContDiff ℝ ∞ (shellCut (d := d) W j) :=
  (contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm')).sub
    (contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm'))

private theorem contDiff_highCut (W : ℕ) : ContDiff ℝ ∞ (highCut (d := d) W) :=
  contDiff_const.sub (contDiff_lowPass'.comp (contDiff_const.mul contDiff_sqNorm'))

private theorem lowPass_eq_zero' {t : ℝ} (h : 4 ≤ t) : lowPass t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem lowPass_eq_one' {t : ℝ} (h : t ≤ 1) : lowPass t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private theorem lowPass_mem_Icc (t : ℝ) : 0 ≤ lowPass t ∧ lowPass t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The core at scale `J` vanishes where `W²|p|² > 4/4^J`. -/
private theorem coreCut_eq_zero {W J : ℕ} {p : Fin d → ℝ}
    (hp : 4 / 4 ^ J < (W : ℝ) ^ 2 * sqNorm p) : coreCut W J p = 0 := by
  unfold coreCut
  apply lowPass_eq_zero'
  rw [div_lt_iff₀ (by positivity)] at hp
  nlinarith

private theorem shellCut_eventually_zero {W j : ℕ} {p : Fin d → ℝ}
    (hp : ¬ (((4 : ℝ) ^ (j + 1))⁻¹ ≤ (W : ℝ) ^ 2 * sqNorm p ∧
      (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ j)) : shellCut (d := d) W j =ᶠ[nhds p] 0 := by
  have hcont : Continuous fun q : Fin d → ℝ => (W : ℝ) ^ 2 * sqNorm q :=
    continuous_const.mul continuous_sqNorm'
  have hopen : IsOpen {q : Fin d → ℝ | (W : ℝ) ^ 2 * sqNorm q < ((4 : ℝ) ^ (j + 1))⁻¹ ∨
      4 / 4 ^ j < (W : ℝ) ^ 2 * sqNorm q} :=
    (isOpen_lt hcont continuous_const).union (isOpen_lt continuous_const hcont)
  have hmem : p ∈ {q : Fin d → ℝ | (W : ℝ) ^ 2 * sqNorm q < ((4 : ℝ) ^ (j + 1))⁻¹ ∨
      4 / 4 ^ j < (W : ℝ) ^ 2 * sqNorm q} := by
    simp only [Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    exact hp h
  filter_upwards [hopen.mem_nhds hmem] with q hq
  by_contra hne
  have := shellCut_support W j q hne
  rcases hq with hq | hq <;> linarith [this.1, this.2]

private theorem coreCut_eventually_zero {W J : ℕ} {p : Fin d → ℝ}
    (hp : ¬ (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J) : coreCut (d := d) W J =ᶠ[nhds p] 0 := by
  have hcont : Continuous fun q : Fin d → ℝ => (W : ℝ) ^ 2 * sqNorm q :=
    continuous_const.mul continuous_sqNorm'
  push Not at hp
  filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hp] with q hq
  exact coreCut_eq_zero hq

end Cutoffs

/-! ## The shell estimate -/

section ShellEstimate

/-- On `[-π, π]^d`, `1 - a Re ŝ ≥ min(c, 1) min(W²|p|², 1)` for `a ∈ [0, 1]`, from
`1 - Re ŝ ≥ c min(W²|p|², 1)`. -/
private theorem one_sub_mul_ge {c a σ X : ℝ} (hc : 0 < c) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hX : 0 ≤ X) (h : c * min X 1 ≤ 1 - σ) : min c 1 * min X 1 ≤ 1 - a * σ := by
  have hm1 : min X 1 ≤ 1 := min_le_right _ _
  have hm0 : 0 ≤ min X 1 := le_min hX zero_le_one
  have hc1 : min c 1 ≤ c := min_le_left _ _
  have hc1' : min c 1 ≤ 1 := min_le_right _ _
  rcases le_or_gt σ 0 with hσ | hσ
  · have : a * σ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hσ
    nlinarith
  · have : a * σ ≤ σ := by nlinarith
    nlinarith

/-- The derivative of the symbol of an `InfKernel` at `p` is at most `K_2 W² ‖p‖`. -/
private theorem InfKernel.norm_fderiv_le {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) (hcd : ContDiff ℝ ∞ (zdSymbol s))
    {K₂ : ℝ} (h2 : ∀ p, ‖iteratedFDeriv ℝ 2 (zdSymbol s) p‖ ≤ K₂ * (W : ℝ) ^ 2)
    (p : Fin d → ℝ) : ‖fderiv ℝ (zdSymbol s) p‖ ≤ K₂ * (W : ℝ) ^ 2 * ‖p‖ :=
  norm_fderiv_le_of_zero hcd (hs.fderiv_zero (hcd.differentiable (by simp) 0)) h2 p

/-- One dyadic shell `j` of `Θ_{ℤ^d}(a)`, uniformly in `a ∈ [0, 1]`:
`|K_j(x)| (1 + |x|/(2^j W))^M ≤ C₀ 4^j (2^j W)^{-d}`, where `K_j` has symbol
`χ_j(p) a ŝ(p)/(1 - a ŝ(p))`. This is the dyadic shell estimate of the proof of [I, (1.17)]
given here; it does not use the local central limit theorem [I, Lemma B.1]. -/
theorem shellKernel_bound :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ)
    (C : ℕ → ℝ) (M : ℕ), ∃ C₀ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → ∀ (j : ℕ) (x : Fin d → ℤ),
        ‖shellKernel (fun t => (a : ℂ) * t / (1 - (a : ℂ) * t)) s W j x‖ *
            (1 + (zdInf x : ℝ) / (2 ^ j * W)) ^ M ≤ C₀ * 4 ^ j / (2 ^ j * (W : ℝ)) ^ d := by
  intro d ψ cψ hψ C M
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  choose Cc hCc using norm_iteratedFDeriv_cut_le d
  obtain ⟨c, W₁, hc, hW₁⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  have hc1 : 0 < min c 1 := lt_min hc one_pos
  obtain ⟨C₀, -, hC₀⟩ := shellKernel_piece_kernel_bound (d := d) K Cc (b := min c 1 / 4) (by positivity) M
  refine ⟨C₀, max 1 W₁, ?_⟩
  intro W hW s hs a ha0 ha1 j x
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hcd := (hK 0 W hWn s hs).1
  have hKall : ∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * (W : ℝ) ^ i :=
    fun i p => (hK i W hWn s hs).2.2 p
  have hK2 := hs.norm_fderiv_le hcd (fun q => hKall 2 q)
  set R : Set (Fin d → ℝ) := {p | ((4 : ℝ) ^ (j + 1))⁻¹ ≤ (W : ℝ) ^ 2 * sqNorm p ∧
      (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ j} with hRdef
  have hR : ∀ p ∈ R, (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ j ∧
      min c 1 / 4 ≤ 4 ^ j * (1 - a * (zdSymbol s p).re) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨hp2, ?_⟩
    have h4 : (4 : ℝ) / 4 ^ j ≤ 4 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have hcube := mem_cubePi_of_sqNorm_le hW1 (hp2.trans h4)
    obtain ⟨-, hge⟩ := hW₁ W (le_trans (le_max_right _ _) hW) s hs p hcube
    have hX : 0 ≤ (W : ℝ) ^ 2 * sqNorm p := mul_nonneg (by positivity) (sqNorm_nonneg' p)
    have h1 := one_sub_mul_ge hc ha0 ha1 hX hge
    have hmin : ((4 : ℝ) ^ (j + 1))⁻¹ ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
      le_min hp1 (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
    have h2 : min c 1 * ((4 : ℝ) ^ (j + 1))⁻¹ ≤ 1 - a * (zdSymbol s p).re :=
      (mul_le_mul_of_nonneg_left hmin hc1.le).trans h1
    calc min c 1 / 4 = 4 ^ j * (min c 1 * ((4 : ℝ) ^ (j + 1))⁻¹) := by
          rw [pow_succ]; field_simp
      _ ≤ 4 ^ j * (1 - a * (zdSymbol s p).re) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hRχ : ∀ p ∉ R, shellCut (d := d) W j =ᶠ[nhds p] 0 := fun p hp =>
    shellCut_eventually_zero hp
  have hsupp : ∀ p, shellCut (d := d) W j p ≠ 0 → (W : ℝ) ^ 2 * sqNorm p < 4 / 4 ^ j :=
    fun p hp => (shellCut_support W j p hp).2
  exact hC₀ W j a s (shellCut W j) R hW1 ha0 ha1 hcd hs.im_eq hKall hK2 (contDiff_shellCut W j)
    (fun i p => (hCc i W j p).1) hRχ hR hsupp x

end ShellEstimate

/-! ## Linearity of the Fourier coefficients -/

section Linear

private theorem continuous_zexp' (y : Fin d → ℤ) : Continuous fun p : Fin d → ℝ => zexp p y := by
  unfold zexp; fun_prop

private theorem integrableOn_mul_zexp {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (x : Fin d → ℤ) : IntegrableOn (fun p => F p * zexp p (-x)) (cubePi d) :=
  hF.mul_continuousOn (continuous_zexp' _).continuousOn isCompact_cubePi''

private theorem latticeFourier_add {F G : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (hG : IntegrableOn G (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => F p + G p) x = latticeFourier F x + latticeFourier G x := by
  unfold latticeFourier
  rw [← mul_add, ← integral_add (integrableOn_mul_zexp hF x) (integrableOn_mul_zexp hG x)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

private theorem latticeFourier_sub {F G : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (hG : IntegrableOn G (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => F p - G p) x = latticeFourier F x - latticeFourier G x := by
  unfold latticeFourier
  rw [← mul_sub, ← integral_sub (integrableOn_mul_zexp hF x) (integrableOn_mul_zexp hG x)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

private theorem latticeFourier_const_mul (c : ℂ) (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    latticeFourier (fun p => c * F p) x = c * latticeFourier F x := by
  unfold latticeFourier
  simp_rw [mul_assoc c]
  rw [integral_const_mul]; ring

private theorem latticeFourier_finset_sum {ι : Type*} (S : Finset ι)
    {F : ι → (Fin d → ℝ) → ℂ} (hF : ∀ n ∈ S, IntegrableOn (F n) (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => ∑ n ∈ S, F n p) x = ∑ n ∈ S, latticeFourier (F n) x := by
  unfold latticeFourier
  rw [← Finset.mul_sum, ← integral_finsetSum S fun n hn => integrableOn_mul_zexp (hF n hn) x]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Finset.sum_mul]

private theorem latticeFourier_congr {F G : (Fin d → ℝ) → ℂ}
    (h : ∀ p ∈ cubePi d, F p = G p) (x : Fin d → ℤ) : latticeFourier F x = latticeFourier G x := by
  unfold latticeFourier
  congr 1
  exact setIntegral_congr_fun measurableSet_cubePi' fun p hp => by simp only [h p hp]

end Linear

/-! ## Convolution with `s` and powers of the symbol -/

section Convolution

variable {ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)} {C : ℕ → ℝ} {W : ℕ} {s : (Fin d → ℤ) → ℝ}

private theorem natAbs_le_zdInf' (x : Fin d → ℤ) (j : Fin d) :
    |((x j : ℤ) : ℝ)| ≤ (zdInf x : ℝ) := by
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ j)

private theorem sum_range_le' (W : ℝ) (hW : 1 ≤ W) (M : ℕ) :
    ∑ n ∈ Finset.range M, ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ ≤ W - W ^ 2 / (W + M) := by
  induction M with
  | zero =>
    have : W ^ 2 / (W + ((0 : ℕ) : ℝ)) = W := by
      rw [Nat.cast_zero, add_zero, sq, mul_div_assoc, div_self (by linarith), mul_one]
    simp only [Finset.range_zero, Finset.sum_empty, this, sub_self, le_refl]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) ≤ M := M.cast_nonneg
    have key : ((1 + ((M : ℝ) + 1) / W) ^ 2)⁻¹ ≤
        W ^ 2 / (W + M) - W ^ 2 / (W + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      have h1 : 0 < W + M := by linarith
      have h2 : 0 < W + (M + 1) := by linarith
      have e : ((1 + ((M : ℝ) + 1) / W) ^ 2)⁻¹ = W ^ 2 / (W + (M + 1)) ^ 2 := by
        field_simp
      rw [e, div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg W, mul_pos h1 h2]
    linarith

/-- The one-dimensional weight `(1 + |m|/W)^{-2}`. -/
private def wt' (W : ℝ) (m : ℤ) : ℝ := ((1 + |(m : ℝ)| / W) ^ 2)⁻¹

private theorem wt_nonneg' (W : ℝ) (hW : 1 ≤ W) (m : ℤ) : 0 ≤ wt' W m := by
  unfold wt'; have : 0 ≤ |(m : ℝ)| / W := by positivity
  positivity

private theorem summable_wt' (W : ℝ) (hW : 1 ≤ W) :
    Summable (wt' W) ∧ ∑' m, wt' W m ≤ 1 + 2 * W := by
  have hpos : ∀ n : ℕ, 0 ≤ ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := fun n => by
    have : 0 ≤ ((n : ℝ) + 1) / W := by positivity
    positivity
  have hsr : ∀ n, ∑ i ∈ Finset.range n, ((1 + ((i : ℝ) + 1) / W) ^ 2)⁻¹ ≤ W := fun n => by
    have := sum_range_le' W hW n
    have : 0 ≤ W ^ 2 / (W + n) := by positivity
    linarith
  have hA := summable_of_sum_range_le hpos hsr
  have e1 : (fun n : ℕ => wt' W ((n + 1 : ℕ) : ℤ)) =
      fun n : ℕ => ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := by
    funext n; unfold wt'; push_cast
    rw [abs_of_nonneg (by positivity)]
  have e2 : (fun n : ℕ => wt' W (-((n : ℤ) + 1))) =
      fun n : ℕ => ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := by
    funext n; unfold wt'; push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hnat : Summable fun n : ℕ => wt' W n := by
    rw [← summable_nat_add_iff 1]
    exact_mod_cast (e1 ▸ hA : Summable fun n : ℕ => wt' W ((n + 1 : ℕ) : ℤ))
  have hneg : Summable fun n : ℕ => wt' W (-((n : ℤ) + 1)) := by rw [e2]; exact hA
  refine ⟨hnat.of_nat_of_neg_add_one hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add, e2]
  have e0 : wt' W ((0 : ℕ) : ℤ) = 1 := by simp [wt']
  have e1' : (∑' n : ℕ, wt' W ((n + 1 : ℕ) : ℤ)) = ∑' n : ℕ, ((1 + ((n : ℝ) + 1) / W) ^ 2)⁻¹ := by
    rw [e1]
  rw [e0, e1']
  have := Real.tsum_le_of_sum_range_le hpos hsr
  linarith

private theorem summable_of_le_prod' (f : (Fin d → ℤ) → ℝ) (g : ℤ → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ m, 0 ≤ g m) (hg : Summable g) (hgB : ∑' m, g m ≤ B)
    (hfg : ∀ x, f x ≤ A * ∏ j, g (x j)) : Summable f ∧ ∑' x, f x ≤ A * B ^ d := by
  classical
  have hu : ∀ u : Finset (Fin d → ℤ), ∑ x ∈ u, f x ≤ A * B ^ d := by
    intro u
    set T : Fin d → Finset ℤ := fun j => u.image fun x => x j
    have hsub : u ⊆ Fintype.piFinset T := fun x hx =>
      Fintype.mem_piFinset.2 fun j => Finset.mem_image_of_mem _ hx
    have hT : ∀ j, ∑ m ∈ T j, g m ≤ B := fun j =>
      (hg.sum_le_tsum _ fun m _ => hg0 m).trans hgB
    have hT0 : ∀ j, 0 ≤ ∑ m ∈ T j, g m := fun j => Finset.sum_nonneg fun m _ => hg0 m
    calc ∑ x ∈ u, f x ≤ ∑ x ∈ Fintype.piFinset T, f x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hf0 x
      _ ≤ ∑ x ∈ Fintype.piFinset T, A * ∏ j, g (x j) := Finset.sum_le_sum fun x _ => hfg x
      _ = A * ∏ j, ∑ m ∈ T j, g m := by
          rw [← Finset.mul_sum, Finset.prod_univ_sum]
      _ ≤ A * ∏ _j : Fin d, B := by
          exact mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ => hT0 j) fun j _ => hT j) hA
      _ = A * B ^ d := by simp
  exact ⟨summable_of_sum_le (fun x => hf0 x) hu, Real.tsum_le_of_sum_le (fun x => hf0 x) hu⟩

private theorem InfKernel.C_nonneg' (hW : 1 ≤ W) (hs : InfKernel ψ C W s) (k : ℕ) :
    0 ≤ C k := by
  have h := hs.decay k 0
  have hW' : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have : 0 ≤ |s 0| * (1 + (zdInf (0 : Fin d → ℤ) : ℝ) / W) ^ k := by
    have : 0 ≤ (zdInf (0 : Fin d → ℤ) : ℝ) / W := by positivity
    positivity
  have := this.trans h
  rwa [le_div_iff₀ hW', zero_mul] at this

/-- The weighted mass `Σ_y |s(y)| (1 + |y|/W)^N ≤ 3^d C_{N+2d}` of an `InfKernel`. -/
private theorem InfKernel.weighted_sum (hW : 1 ≤ W) (hs : InfKernel ψ C W s) (N : ℕ) :
    Summable (fun y => |s y| * (1 + (zdInf y : ℝ) / W) ^ N) ∧
      ∑' y, |s y| * (1 + (zdInf y : ℝ) / W) ^ N ≤ 3 ^ d * C (N + 2 * d) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hC := hs.C_nonneg' hW (N + 2 * d)
  obtain ⟨hg, hgB⟩ := summable_wt' (W : ℝ) hW1
  have hA : 0 ≤ C (N + 2 * d) / (W : ℝ) ^ d := by positivity
  have hpt : ∀ y : Fin d → ℤ, |s y| * (1 + (zdInf y : ℝ) / W) ^ N ≤
      C (N + 2 * d) / (W : ℝ) ^ d * ∏ j, wt' W (y j) := by
    intro y
    set t : ℝ := 1 + (zdInf y : ℝ) / W
    have ht : 1 ≤ t := by have : 0 ≤ (zdInf y : ℝ) / W := by positivity
                          linarith
    have ht0 : 0 < t := by linarith
    have hdec := hs.decay (N + 2 * d) y
    have hprod : (t ^ (2 * d))⁻¹ ≤ ∏ j, wt' W (y j) := by
      have : ∀ j, (t ^ 2)⁻¹ ≤ wt' W (y j) := by
        intro j
        unfold wt'
        have h1 : 0 ≤ |((y j : ℤ) : ℝ)| / W := by positivity
        have h2 : 1 + |((y j : ℤ) : ℝ)| / W ≤ t := by
          simp only [t]; gcongr; exact natAbs_le_zdInf' y j
        gcongr
      calc (t ^ (2 * d))⁻¹ = ∏ _j : Fin d, (t ^ 2)⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow, pow_mul, inv_pow]
        _ ≤ ∏ j, wt' W (y j) := Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => this j
    calc |s y| * t ^ N = (|s y| * t ^ (N + 2 * d)) * (t ^ (2 * d))⁻¹ := by
          rw [pow_add]; field_simp
      _ ≤ (C (N + 2 * d) / (W : ℝ) ^ d) * ∏ j, wt' W (y j) := by
          gcongr
  have := summable_of_le_prod' (fun y => |s y| * (1 + (zdInf y : ℝ) / W) ^ N) (wt' W) _
    (1 + 2 * W) hA (fun y => by positivity) (wt_nonneg' W hW1) hg hgB hpt
  refine ⟨this.1, this.2.trans ?_⟩
  calc C (N + 2 * d) / (W : ℝ) ^ d * (1 + 2 * W) ^ d
      ≤ C (N + 2 * d) / (W : ℝ) ^ d * (3 * W) ^ d := by
        gcongr; linarith
    _ = 3 ^ d * C (N + 2 * d) := by
        rw [mul_pow]; field_simp

/-- Multiplying the symbol by `ŝ` convolves the kernel with `s`:
`(2π)^{-d} ∫ ŝ Φ e^{-ip·x} = Σ_y s(y) (2π)^{-d} ∫ Φ e^{-ip·(x-y)}`. -/
private theorem latticeFourier_zdSymbol_mul (hsum : Summable fun y => |s y|)
    {Φ : (Fin d → ℝ) → ℂ} (hΦ : IntegrableOn Φ (cubePi d)) (x : Fin d → ℤ) :
    latticeFourier (fun p => zdSymbol s p * Φ p) x =
      ∑' y, (s y : ℂ) * latticeFourier Φ (x - y) := by
  unfold latticeFourier
  set F : (Fin d → ℤ) → (Fin d → ℝ) → ℂ := fun y p => (s y : ℂ) * (Φ p * zexp p (-(x - y)))
  have hF : ∀ y, Integrable (F y) (volume.restrict (cubePi d)) := fun y =>
    (integrableOn_mul_zexp hΦ (x - y)).const_mul _
  have hnorm : ∀ y, ∫ p in cubePi d, ‖F y p‖ = |s y| * ∫ p in cubePi d, ‖Φ p‖ := by
    intro y
    simp only [F, norm_mul, norm_zexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [integral_const_mul]
  have hsumm : Summable fun y => ∫ p in cubePi d, ‖F y p‖ := by
    simp_rw [hnorm]; exact hsum.mul_right _
  have h := integral_tsum_of_summable_integral_norm hF hsumm
  have hpt : ∀ p, zdSymbol s p * Φ p * zexp p (-x) = ∑' y, F y p := by
    intro p
    unfold zdSymbol zdSeries
    rw [mul_assoc, ← tsum_mul_right]
    refine tsum_congr fun y => ?_
    simp only [F]
    have : zexp p (-(x - y)) = zexp p y * zexp p (-x) := by
      rw [← zexp_add]; congr 1; abel
    rw [this]; ring
  simp_rw [hpt]
  rw [← h, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  simp only [F]
  rw [integral_const_mul]; ring

/-- Convolution with `s` maps the class `|k(x)| (1 + |x|/W)^N ≤ B` into itself with the factor
`Λ ≥ Σ_y |s(y)| (1 + |y|/W)^N`. -/
private theorem conv_weight_le {W : ℝ} (hW : 0 < W) (N : ℕ) {Λ : ℝ}
    (hsumw : Summable fun y => |s y| * (1 + (zdInf y : ℝ) / W) ^ N)
    (hΛ : ∑' y, |s y| * (1 + (zdInf y : ℝ) / W) ^ N ≤ Λ) {k : (Fin d → ℤ) → ℂ} {B : ℝ}
    (hk : ∀ x, ‖k x‖ * (1 + (zdInf x : ℝ) / W) ^ N ≤ B) (x : Fin d → ℤ) :
    ‖∑' y, (s y : ℂ) * k (x - y)‖ * (1 + (zdInf x : ℝ) / W) ^ N ≤ Λ * B := by
  set w : (Fin d → ℤ) → ℝ := fun z => (1 + (zdInf z : ℝ) / W) ^ N with hw
  have hw1 : ∀ z, 1 ≤ w z := fun z => one_le_pow₀ (by
    have : 0 ≤ (zdInf z : ℝ) / W := by positivity
    linarith)
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by linarith [hw1 0])).trans (hk 0)
  have hwmul : ∀ y, w x ≤ w y * w (x - y) := by
    intro y
    simp only [hw]
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have h1 : (zdInf x : ℝ) ≤ zdInf y + zdInf (x - y) := by
      have := zdInf_add_le y (x - y)
      rw [add_sub_cancel] at this
      exact_mod_cast this
    have h2 : 0 ≤ (zdInf y : ℝ) / W * ((zdInf (x - y) : ℝ) / W) := by positivity
    have h3 : (zdInf x : ℝ) / W ≤ (zdInf y : ℝ) / W + (zdInf (x - y) : ℝ) / W := by
      rw [← add_div]; exact div_le_div_of_nonneg_right h1 hW.le
    nlinarith
  have hterm : ∀ y, ‖(s y : ℂ) * k (x - y)‖ * w x ≤ |s y| * w y * B := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |s y| * ‖k (x - y)‖ * w x ≤ |s y| * ‖k (x - y)‖ * (w y * w (x - y)) :=
          mul_le_mul_of_nonneg_left (hwmul y) (by positivity)
      _ = |s y| * w y * (‖k (x - y)‖ * w (x - y)) := by ring
      _ ≤ |s y| * w y * B := mul_le_mul_of_nonneg_left (hk _) (by positivity)
  have hsn : Summable fun y => ‖(s y : ℂ) * k (x - y)‖ := by
    refine Summable.of_nonneg_of_le (fun y => norm_nonneg _) (fun y => ?_) (hsumw.mul_right B)
    calc ‖(s y : ℂ) * k (x - y)‖ ≤ ‖(s y : ℂ) * k (x - y)‖ * w x :=
          le_mul_of_one_le_right (norm_nonneg _) (hw1 x)
      _ ≤ |s y| * w y * B := hterm y
  calc ‖∑' y, (s y : ℂ) * k (x - y)‖ * w x ≤ (∑' y, ‖(s y : ℂ) * k (x - y)‖) * w x :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsn) (by linarith [hw1 x])
    _ = ∑' y, ‖(s y : ℂ) * k (x - y)‖ * w x := by rw [tsum_mul_right]
    _ ≤ ∑' y, |s y| * w y * B :=
        Summable.tsum_le_tsum hterm (hsn.mul_right _) (hsumw.mul_right B)
    _ = (∑' y, |s y| * w y) * B := by rw [tsum_mul_right]
    _ ≤ Λ * B := mul_le_mul_of_nonneg_right hΛ hB

/-- The kernel of `ŝ^n`, `n ≥ 1`, is the `n`-fold convolution of `s`:
`|K(x)| (1 + |x|/W)^N ≤ (3^d C_{N+2d})^{n-1} C_N W^{-d}`. -/
private theorem pow_kernel_bound (hW : 1 ≤ W) (hs : InfKernel ψ C W s)
    (hcd : Continuous (zdSymbol s)) (N : ℕ) (n : ℕ) (hn : 1 ≤ n) (x : Fin d → ℤ) :
    ‖latticeFourier (fun p => zdSymbol s p ^ n) x‖ * (1 + (zdInf x : ℝ) / W) ^ N ≤
      (3 ^ d * C (N + 2 * d)) ^ (n - 1) * (C N / (W : ℝ) ^ d) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hsumw, hΛ⟩ := hs.weighted_sum hW N
  induction n, hn using Nat.le_induction generalizing x with
  | base =>
    simp only [pow_one, Nat.sub_self, pow_zero, one_mul]
    have hsum : Summable fun y => ‖((s y : ℝ) : ℂ)‖ := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hs.summable_abs
    have : latticeFourier (zdSymbol s) x = (s x : ℂ) := latticeFourier_zdSeries _ hsum x
    simp only [this, Complex.norm_real, Real.norm_eq_abs]
    exact hs.decay N x
  | succ n hn ih =>
    have hΦ : IntegrableOn (fun p => zdSymbol s p ^ n) (cubePi d) :=
      (hcd.pow n).continuousOn.integrableOn_compact isCompact_cubePi''
    have he : (fun p => zdSymbol s p ^ (n + 1)) = fun p => zdSymbol s p * zdSymbol s p ^ n := by
      funext p; ring
    rw [he, latticeFourier_zdSymbol_mul hs.summable_abs hΦ x]
    have := conv_weight_le (s := s) hW0 N hsumw hΛ (k := latticeFourier fun p => zdSymbol s p ^ n)
      ih x
    refine this.trans (le_of_eq ?_)
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]; ring

end Convolution

/-! ## Remainders with a factor `ŝ` -/

section Remainder

private theorem volume_real_cubePi : (volume (cubePi d)).toReal = (2 * Real.pi) ^ d := by
  have : cubePi d = Set.Icc (fun _ : Fin d => -Real.pi) (fun _ => Real.pi) := by
    unfold cubePi
    rw [← Set.pi_univ_Icc]
  rw [this, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity), ENNReal.toReal_ofReal (by positivity)]

private theorem norm_smul_le_norm_toLp (W : ℝ) (p : Fin d → ℝ) :
    ‖W • p‖ ≤ ‖W • WithLp.toLp 2 p‖ := by
  have h1 : ‖W • WithLp.toLp 2 p‖ ^ 2 = W ^ 2 * sqNorm p := by
    rw [norm_smul, mul_pow, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rfl
  have h2 : ‖W • p‖ ^ 2 ≤ W ^ 2 * sqNorm p := by
    refine (norm_sq_le_sqNorm (W • p)).trans (le_of_eq ?_)
    simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [← h1] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- `∫_{[-π,π]^d} |ŝ| ≤ B W^{-d}`: by closeness to the Schwartz profile `ψ(W·)` with
`D′ = d + 1`, the symbol is small away from `|p| ≲ 1/W`. -/
private theorem integral_norm_zdSymbol_le (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (C : ℕ → ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ (W : ℕ), 1 ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      Continuous (zdSymbol s) → ∫ p in cubePi d, ‖zdSymbol s p‖ ≤ B / (W : ℝ) ^ d := by
  set A : ℝ := 2 ^ (d + 1) *
    ((Finset.Iic (d + 1, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hAdef
  have hA : ∀ q, (1 + ‖q‖) ^ (d + 1) * |ψ q| ≤ A := fun q => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 1, 0)) (k := d + 1)
      (n := 0) le_rfl le_rfl ψ q
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hA0 : 0 ≤ A := (mul_nonneg (by positivity) (abs_nonneg _)).trans (hA 0)
  set f : (Fin d → ℝ) → ℝ := fun q => ((1 + ‖q‖) ^ (d + 1))⁻¹ with hfdef
  have hfc : Continuous f := by
    simp only [hfdef]
    have h1 : Continuous fun q : Fin d → ℝ => (1 + ‖q‖) ^ (d + 1) := by fun_prop
    exact h1.inv₀ fun q => (pow_pos (by positivity : (0 : ℝ) < 1 + ‖q‖) _).ne'
  have hf0 : ∀ q, 0 ≤ f q := fun q => by simp only [hfdef]; positivity
  have hfi : Integrable f := by
    have := integrable_one_add_norm (E := Fin d → ℝ) (μ := volume) (r := ((d + 1 : ℕ) : ℝ))
      (by rw [Module.finrank_fin_fun]; push_cast; linarith)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hfdef]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  set I := ∫ q, f q with hI
  have hI0 : 0 ≤ I := integral_nonneg hf0
  refine ⟨A * I + |C (d + 1)| * (2 * Real.pi) ^ d, by positivity, ?_⟩
  intro W hW s hs hc
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set c' : ℝ := C (d + 1) / (W : ℝ) ^ (d + 1) with hc'
  have hpt : ∀ p ∈ cubePi d, ‖zdSymbol s p‖ ≤ A * f ((W : ℝ) • p) + c' := by
    intro p hp
    have hcl := hs.close (d + 1) p hp
    have hψ : |ψ ((W : ℝ) • WithLp.toLp 2 p)| ≤ A * f ((W : ℝ) • p) := by
      have h1 := hA ((W : ℝ) • WithLp.toLp 2 p)
      have h2 := norm_smul_le_norm_toLp (W : ℝ) p
      have h3 : (1 + ‖(W : ℝ) • p‖) ^ (d + 1) ≤ (1 + ‖(W : ℝ) • WithLp.toLp 2 p‖) ^ (d + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      simp only [hfdef]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc |ψ ((W : ℝ) • WithLp.toLp 2 p)| * (1 + ‖(W : ℝ) • p‖) ^ (d + 1)
          ≤ |ψ ((W : ℝ) • WithLp.toLp 2 p)| * (1 + ‖(W : ℝ) • WithLp.toLp 2 p‖) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ ≤ A := by rw [mul_comm]; exact h1
    calc ‖zdSymbol s p‖ ≤ ‖zdSymbol s p - (ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)‖ +
          ‖(ψ ((W : ℝ) • WithLp.toLp 2 p) : ℂ)‖ := norm_le_norm_sub_add _ _
      _ ≤ c' + A * f ((W : ℝ) • p) := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add hcl hψ
      _ = A * f ((W : ℝ) • p) + c' := by ring
  have hfWc : Continuous fun p : Fin d → ℝ => f ((W : ℝ) • p) := hfc.comp (continuous_const_smul _)
  have hfWi : Integrable fun p : Fin d → ℝ => f ((W : ℝ) • p) := hfi.comp_smul hW0.ne'
  have hint1 : IntegrableOn (fun p => ‖zdSymbol s p‖) (cubePi d) :=
    hc.norm.continuousOn.integrableOn_compact isCompact_cubePi''
  have hint2 : IntegrableOn (fun p : Fin d → ℝ => A * f ((W : ℝ) • p) + c') (cubePi d) :=
    ((continuous_const.mul hfWc).add continuous_const).continuousOn.integrableOn_compact
      isCompact_cubePi''
  have hsc : ∫ p, f ((W : ℝ) • p) = I / (W : ℝ) ^ d := by
    rw [Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul,
      abs_of_pos (by positivity), inv_mul_eq_div]
  calc ∫ p in cubePi d, ‖zdSymbol s p‖ ≤ ∫ p in cubePi d, (A * f ((W : ℝ) • p) + c') :=
        setIntegral_mono_on hint1 hint2 measurableSet_cubePi' hpt
    _ = A * (∫ p in cubePi d, f ((W : ℝ) • p)) + c' * (2 * Real.pi) ^ d := by
        rw [integral_add (hfWi.integrableOn.const_mul A) (integrableOn_const
            isCompact_cubePi''.measure_lt_top.ne), integral_const_mul, setIntegral_const,
          Measure.real, volume_real_cubePi, smul_eq_mul]
        ring
    _ ≤ A * (I / (W : ℝ) ^ d) + |C (d + 1)| / (W : ℝ) ^ d * (2 * Real.pi) ^ d := by
        gcongr
        · rw [← hsc]
          exact setIntegral_le_integral hfWi (Filter.Eventually.of_forall fun p => hf0 _)
        · rw [hc', pow_succ]
          calc C (d + 1) / ((W : ℝ) ^ d * W) ≤ |C (d + 1)| / ((W : ℝ) ^ d * W) :=
                div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |C (d + 1)| / ((W : ℝ) ^ d) :=
                div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
                  (le_mul_of_one_le_right (by positivity) hW1)
    _ = (A * I + |C (d + 1)| * (2 * Real.pi) ^ d) / (W : ℝ) ^ d := by ring

/-- The kernel of `ŝ^{N+1} Ψ` for smooth periodic `Ψ` with `‖D^i Ψ‖ ≤ K′ W^i` (`i ≤ N`):
`|K(x)| (1 + |x|/W)^N ≤ B W^{-d}`. Each derivative of order `≤ N` keeps a factor `ŝ`, whose
integral over the cube is `O(W^{-d})`. -/
private theorem remainder_kernel_bound (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (C : ℕ → ℝ)
    (N : ℕ) (K' : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ (W : ℕ) (s : (Fin d → ℤ) → ℝ) (Ψ : (Fin d → ℝ) → ℂ), 1 ≤ W →
      InfKernel ψ C W s → ContDiff ℝ ∞ Ψ →
      (∀ (i : Fin d) (p : Fin d → ℝ), Ψ (p + Pi.single i (2 * Real.pi)) = Ψ p) →
      (∀ i ≤ N, ∀ p, ‖iteratedFDeriv ℝ i Ψ p‖ ≤ K' * (W : ℝ) ^ i) →
      ∀ x : Fin d → ℤ, ‖latticeFourier (fun p => zdSymbol s p ^ (N + 1) * Ψ p) x‖ *
        (1 + (zdInf x : ℝ) / W) ^ N ≤ B / (W : ℝ) ^ d := by
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  obtain ⟨Bσ, hBσ0, hBσ⟩ := integral_norm_zdSymbol_le ψ C
  set Km : ℝ := |K'| + ∑ i ∈ Finset.range (N + 1), |K i| with hKm
  have hKm0 : 0 ≤ Km := by positivity
  set Q : ℝ := (2 ^ N * (max 1 Km) ^ 2) ^ (N + 1) * Km with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set c : ℝ := ((2 * Real.pi) ^ d)⁻¹ with hcdef
  have hc0 : 0 ≤ c := by positivity
  refine ⟨2 ^ N * (c * Q * Bσ + c * Q * Bσ), by positivity, ?_⟩
  intro W s Ψ hW hs hΨ hper hΨb x
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hcd, hsper, -⟩ := hK 0 W hW s hs
  set X : (Fin d → ℝ) → ℂ := fun p => zdSymbol s p ^ (N + 1) * Ψ p with hXdef
  have hXc : ContDiff ℝ ∞ X := (hcd.pow _).mul hΨ
  have hXper : ∀ (i : Fin d) (p : Fin d → ℝ), X (p + Pi.single i (2 * Real.pi)) = X p := by
    intro i p; simp only [hXdef, hsper i p, hper i p]
  have hpm : ∀ p, ∀ k ≤ N, ‖iteratedFDeriv ℝ k X p‖ ≤ Q * (W : ℝ) ^ k * ‖zdSymbol s p‖ := by
    intro p k hk
    have hfx : ∀ i ≤ N, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ Km * (W : ℝ) ^ i := by
      intro i hi
      refine ((hK i W hW s hs).2.2 p).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have : |K i| ≤ ∑ i ∈ Finset.range (N + 1), |K i| :=
        Finset.single_le_sum (f := fun i => |K i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
      have := le_abs_self (K i)
      have := abs_nonneg K'
      linarith
    have hΨx : ∀ i ≤ N, ‖iteratedFDeriv ℝ i Ψ p‖ ≤ Km * (W : ℝ) ^ i := by
      intro i hi
      refine (hΨb i hi p).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have : 0 ≤ ∑ i ∈ Finset.range (N + 1), |K i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      have := le_abs_self K'
      linarith
    have := norm_iteratedFDeriv_pow_mul_le hcd hΨ p N hKm0 hW0.le hfx hΨx (N + 1) k hk
    simp only [show k < N + 1 by omega, ↓reduceIte] at this
    exact this
  have hint : ∀ k ≤ N, c * ∫ p in cubePi d, ‖iteratedFDeriv ℝ k X p‖ ≤
      c * Q * Bσ / (W : ℝ) ^ d * (W : ℝ) ^ k := by
    intro k hk
    have hcont : Continuous fun p => ‖iteratedFDeriv ℝ k X p‖ :=
      (hXc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have h1 : ∫ p in cubePi d, ‖iteratedFDeriv ℝ k X p‖ ≤
        ∫ p in cubePi d, Q * (W : ℝ) ^ k * ‖zdSymbol s p‖ :=
      setIntegral_mono_on (hcont.continuousOn.integrableOn_compact isCompact_cubePi'')
        ((continuous_const.mul hcd.continuous.norm).continuousOn.integrableOn_compact
          isCompact_cubePi'') measurableSet_cubePi' fun p _ => hpm p k hk
    rw [integral_const_mul] at h1
    have h2 := hBσ W hW s hs hcd.continuous
    calc c * ∫ p in cubePi d, ‖iteratedFDeriv ℝ k X p‖
        ≤ c * (Q * (W : ℝ) ^ k * (Bσ / (W : ℝ) ^ d)) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = c * Q * Bσ / (W : ℝ) ^ d * (W : ℝ) ^ k := by ring
  have h0 : c * ∫ p in cubePi d, ‖X p‖ ≤ c * Q * Bσ / (W : ℝ) ^ d := by
    have := hint 0 (Nat.zero_le _)
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using this
  have := kernel_bound_of_periodic N hXc hXper hW0 h0 (hint N le_rfl) x
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Polynomial part plus remainder: the kernel of `Σ_{n=1}^{N} w^n ŝ^n + ŝ^{N+1} Ψ`, `|w| ≤ 1`,
satisfies `|K(x)| (1 + |x|/W)^N ≤ B W^{-d}`. -/
private theorem polyRem_kernel_bound (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (C : ℕ → ℝ)
    (N : ℕ) (K' : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ (W : ℕ) (s : (Fin d → ℤ) → ℝ) (Ψ : (Fin d → ℝ) → ℂ) (w : ℂ), 1 ≤ W →
      InfKernel ψ C W s → ‖w‖ ≤ 1 → ContDiff ℝ ∞ Ψ →
      (∀ (i : Fin d) (p : Fin d → ℝ), Ψ (p + Pi.single i (2 * Real.pi)) = Ψ p) →
      (∀ i ≤ N, ∀ p, ‖iteratedFDeriv ℝ i Ψ p‖ ≤ K' * (W : ℝ) ^ i) →
      ∀ x : Fin d → ℤ, ‖latticeFourier (fun p => (∑ n ∈ Finset.Ico 1 (N + 1),
          w ^ n * zdSymbol s p ^ n) + zdSymbol s p ^ (N + 1) * Ψ p) x‖ *
        (1 + (zdInf x : ℝ) / W) ^ N ≤ B / (W : ℝ) ^ d := by
  obtain ⟨BR, hBR0, hBR⟩ := remainder_kernel_bound ψ C N K'
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  set Λ : ℝ := |3 ^ d * C (N + 2 * d)| with hΛ
  set S : ℝ := ∑ n ∈ Finset.Ico 1 (N + 1), Λ ^ (n - 1) * |C N| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => by positivity
  refine ⟨S + BR, by positivity, ?_⟩
  intro W s Ψ w hW hs hw hΨ hper hΨb x
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hcd, hsper, -⟩ := hK 0 W hW s hs
  have hcont : Continuous (zdSymbol s) := hcd.continuous
  have hi1 : IntegrableOn (fun p => ∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * zdSymbol s p ^ n)
      (cubePi d) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul (hcont.pow n)).continuousOn
      |>.integrableOn_compact isCompact_cubePi''
  have hi2 : IntegrableOn (fun p => zdSymbol s p ^ (N + 1) * Ψ p) (cubePi d) :=
    ((hcont.pow _).mul hΨ.continuous).continuousOn.integrableOn_compact isCompact_cubePi''
  rw [latticeFourier_add hi1 hi2,
    latticeFourier_finset_sum (F := fun n p => w ^ n * zdSymbol s p ^ n) _
      (fun n _ => (continuous_const.mul (hcont.pow n)).continuousOn
        |>.integrableOn_compact isCompact_cubePi'')]
  simp_rw [latticeFourier_const_mul]
  set wt := (1 + (zdInf x : ℝ) / W) ^ N with hwt
  have hwt0 : 0 ≤ wt := by positivity
  have hpoly : ‖∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * latticeFourier (fun p => zdSymbol s p ^ n) x‖ *
      wt ≤ S / (W : ℝ) ^ d := by
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) hwt0).trans ?_
    rw [Finset.sum_mul, hS, Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Ico.1 hn).1
    have hb := pow_kernel_bound hW hs hcont N n hn1 x
    rw [norm_mul, norm_pow]
    have hwn : ‖w‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
    calc ‖w‖ ^ n * ‖latticeFourier (fun p => zdSymbol s p ^ n) x‖ * wt
        ≤ 1 * (‖latticeFourier (fun p => zdSymbol s p ^ n) x‖ * wt) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hwn (by positivity)
      _ ≤ (3 ^ d * C (N + 2 * d)) ^ (n - 1) * (C N / (W : ℝ) ^ d) := by rw [one_mul]; exact hb
      _ = Λ ^ (n - 1) * (|C N| / (W : ℝ) ^ d) := by
          rw [hΛ, abs_of_nonneg (mul_nonneg (by positivity) (hs.C_nonneg' hW (N + 2 * d))),
            abs_of_nonneg (hs.C_nonneg' hW N)]
      _ = Λ ^ (n - 1) * |C N| / (W : ℝ) ^ d := by ring
  have hrem := hBR W s Ψ hW hs hΨ hper hΨb x
  calc ‖∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * latticeFourier (fun p => zdSymbol s p ^ n) x +
        latticeFourier (fun p => zdSymbol s p ^ (N + 1) * Ψ p) x‖ * wt
      ≤ (‖∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * latticeFourier (fun p => zdSymbol s p ^ n) x‖ +
        ‖latticeFourier (fun p => zdSymbol s p ^ (N + 1) * Ψ p) x‖) * wt :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hwt0
    _ ≤ S / (W : ℝ) ^ d + BR / (W : ℝ) ^ d := by rw [add_mul]; exact add_le_add hpoly hrem
    _ = (S + BR) / (W : ℝ) ^ d := by ring

/-- `z/(1 - z) = Σ_{n=1}^{N} z^n + z^{N+1}/(1 - z)`. -/
private theorem geom_identity (z : ℂ) (hz : z ≠ 1) (N : ℕ) :
    z / (1 - z) = ∑ n ∈ Finset.Ico 1 (N + 1), z ^ n + z ^ (N + 1) / (1 - z) := by
  have h1 : (∑ n ∈ Finset.range (N + 1), z ^ n) * (1 - z) = 1 - z ^ (N + 1) :=
    geom_sum_mul_neg z (N + 1)
  have h2 : ∑ n ∈ Finset.range (N + 1), z ^ n = 1 + ∑ n ∈ Finset.Ico 1 (N + 1), z ^ n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero]
  have hne : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [h2] at h1
  field_simp
  linear_combination -h1

/-- Derivative bounds for `Σ_{n=1}^{N} w^n f^n + f^{N+1} Ψ`. -/
private theorem polyRem_deriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ)
    {Km : ℝ} (hKm : 1 ≤ Km) {W : ℝ} (hW : 0 ≤ W) {f Ψ : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hΨ : ContDiff ℝ ∞ Ψ) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hfb : ∀ i ≤ N, ∀ p, ‖iteratedFDeriv ℝ i f p‖ ≤ Km * W ^ i)
    (hΨb : ∀ i ≤ N, ∀ p, ‖iteratedFDeriv ℝ i Ψ p‖ ≤ Km * W ^ i) :
    ∀ k ≤ N, ∀ p, ‖iteratedFDeriv ℝ k
      (fun p => (∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * f p ^ n) + f p ^ (N + 1) * Ψ p) p‖ ≤
        ((N : ℝ) + 1) * ((2 ^ N * Km ^ 2) ^ (N + 1) * Km * Km) * W ^ k := by
  intro k hk p
  have hmax : max 1 Km = Km := max_eq_right hKm
  set Q : ℝ := (2 ^ N * Km ^ 2) ^ (N + 1) * Km * Km with hQ
  have hbase : 1 ≤ 2 ^ N * Km ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hKm)
  have hterm : ∀ (n : ℕ) (Φ : E → ℂ), n ≤ N + 1 → ContDiff ℝ ∞ Φ →
      (∀ i ≤ N, ‖iteratedFDeriv ℝ i Φ p‖ ≤ Km * W ^ i) →
      ‖iteratedFDeriv ℝ k (fun y => f y ^ n * Φ y) p‖ ≤ Q * W ^ k := by
    intro n Φ hn hΦ hΦb
    have := norm_iteratedFDeriv_pow_mul_le hf hΦ p N (by linarith) hW (fun i hi => hfb i hi p)
      hΦb n k hk
    refine this.trans ?_
    rw [hmax]
    have hfac : (if k < n then ‖f p‖ else (1 : ℝ)) ≤ Km := by
      split_ifs
      · have := hfb 0 (Nat.zero_le _) p
        simpa using this
      · exact hKm
    have hpow : (2 ^ N * Km ^ 2) ^ n ≤ (2 ^ N * Km ^ 2) ^ (N + 1) := pow_le_pow_right₀ hbase hn
    calc (2 ^ N * Km ^ 2) ^ n * Km * W ^ k * (if k < n then ‖f p‖ else 1)
        ≤ (2 ^ N * Km ^ 2) ^ (N + 1) * Km * W ^ k * Km := by
          have h0 : 0 ≤ (if k < n then ‖f p‖ else (1 : ℝ)) := by split_ifs <;> positivity
          gcongr
      _ = Q * W ^ k := by rw [hQ]; ring
  have hconst : ∀ n ≤ N + 1, ∀ i ≤ N,
      ‖iteratedFDeriv ℝ i (fun _ : E => w ^ n) p‖ ≤ Km * W ^ i := by
    intro n hn i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDeriv_zero, norm_pow, pow_zero, mul_one]
      exact (pow_le_one₀ (norm_nonneg _) hw).trans hKm
    · rw [iteratedFDeriv_const_of_ne hi0.ne', Pi.zero_apply, norm_zero]; positivity
  have hcd : ∀ n, ContDiff ℝ ∞ (fun y => w ^ n * f y ^ n) := fun n =>
    contDiff_const.mul (hf.pow n)
  have hsplit : (fun p => (∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * f p ^ n) + f p ^ (N + 1) * Ψ p) =
      (fun p => ∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * f p ^ n) +
        (fun p => f p ^ (N + 1) * Ψ p) := rfl
  rw [hsplit, iteratedFDeriv_add_apply
      ((ContDiff.sum fun n _ => hcd n).contDiffAt.of_le (by exact_mod_cast le_top))
      (((hf.pow _).mul hΨ).contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_fun_sum_apply fun n _ => (hcd n).contDiffAt.of_le (by exact_mod_cast le_top)]
  have hs : ‖∑ n ∈ Finset.Ico 1 (N + 1), iteratedFDeriv ℝ k (fun y => w ^ n * f y ^ n) p‖ ≤
      N * (Q * W ^ k) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Finset.Ico 1 (N + 1),
        ‖iteratedFDeriv ℝ k (fun y => w ^ n * f y ^ n) p‖ ≤ Q * W ^ k := by
      intro n hn
      have hn' : n ≤ N + 1 := (Finset.mem_Ico.1 hn).2.le
      have he : (fun y => w ^ n * f y ^ n) = fun y => f y ^ n * (fun _ : E => w ^ n) y := by
        funext y; ring
      rw [he]
      exact hterm n _ hn' contDiff_const (hconst n hn')
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  have hr := hterm (N + 1) Ψ le_rfl hΨ (fun i hi => hΨb i hi p)
  calc ‖∑ n ∈ Finset.Ico 1 (N + 1), iteratedFDeriv ℝ k (fun y => w ^ n * f y ^ n) p +
        iteratedFDeriv ℝ k (fun y => f y ^ (N + 1) * Ψ y) p‖
      ≤ N * (Q * W ^ k) + Q * W ^ k := (norm_add_le _ _).trans (add_le_add hs hr)
    _ = ((N : ℝ) + 1) * Q * W ^ k := by ring

end Remainder

/-! ## The core and the high part -/

section CoreHigh

/-- The high part `|Wp| ≳ 1` of `Θ_{ℤ^d}(a)`, uniformly in `a ∈ [0, 1]`:
`|K_high(x)| (1 + |x|/W)^M ≤ C₀ W^{-d}`. -/
private theorem high_kernel_bound (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (M : ℕ) :
    ∃ C₀ W₀ : ℝ, 0 ≤ C₀ ∧ 1 ≤ W₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → ∀ x : Fin d → ℤ,
        ‖latticeFourier (fun p => (highCut W p : ℂ) *
              ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))) x‖ *
            (1 + (zdInf x : ℝ) / W) ^ M ≤ C₀ / (W : ℝ) ^ d := by
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  choose Cc hCc using norm_iteratedFDeriv_cut_le d
  obtain ⟨c, W₁, hc, hW₁⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  have hc1 : 0 < min c 1 := lt_min hc one_pos
  set bι : ℝ := min c 1 / 2 with hbι
  have hbι0 : 0 < bι := by positivity
  obtain ⟨Cf, hCf0, hCf⟩ := norm_iteratedFDeriv_cinv_comp_le (E := Fin d → ℝ) hbι0 M
  set Λ : ℝ := 1 + ∑ i ∈ Finset.range (M + 1), |K i| with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ ∑ i ∈ Finset.range (M + 1), |K i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set K' : ℝ := Cf * Λ ^ M with hK'
  have hK'0 : 0 ≤ K' := by positivity
  obtain ⟨B₁, hB₁0, hB₁⟩ := polyRem_kernel_bound ψ C M K'
  set Km : ℝ := Λ + K' with hKm
  have hKm1 : 1 ≤ Km := by linarith
  set BF : ℕ → ℝ := fun k => ((M : ℝ) + 1) * ((2 ^ M * Km ^ 2) ^ (M + 1) * Km * Km) with hBF
  set Cs : ℝ := ∑ i ∈ Finset.range (M + 1), |Cc i| with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set BL : ℝ := 2 ^ M * Cs * BF 0 with hBL
  have hBL0 : 0 ≤ BL := by simp only [hBL, hBF]; positivity
  refine ⟨B₁ + 2 ^ M * (((2 * Real.pi) ^ d)⁻¹ * 4 ^ d * (BL + BL)), max 1 W₁, by positivity,
    le_max_left _ _, ?_⟩
  intro W hW s hs a ha0 ha1 x
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hcd, hsper, -⟩ := hK 0 W hWn s hs
  have hKb : ∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * (W : ℝ) ^ i :=
    fun i p => (hK i W hWn s hs).2.2 p
  set σ : (Fin d → ℝ) → ℝ := fun p => (zdSymbol s p).re with hσdef
  have hσ : ContDiff ℝ ∞ σ := Complex.reCLM.contDiff.comp hcd
  set h : (Fin d → ℝ) → ℝ := fun p => 1 + (-a) * σ p with hhdef
  have hh : ContDiff ℝ ∞ h := contDiff_const.add (contDiff_const.mul hσ)
  set Ψ : (Fin d → ℝ) → ℂ := fun p => ((a ^ (M + 1) * cinv bι (h p) : ℝ) : ℂ) with hΨdef
  have hΨr : ContDiff ℝ ∞ (fun p => a ^ (M + 1) * cinv bι (h p)) :=
    contDiff_const.mul ((contDiff_cinv hbι0).comp hh)
  have hΨ : ContDiff ℝ ∞ Ψ := Complex.ofRealCLM.contDiff.comp hΨr
  have hΨper : ∀ (i : Fin d) (p : Fin d → ℝ), Ψ (p + Pi.single i (2 * Real.pi)) = Ψ p := by
    intro i p; simp only [hΨdef, hhdef, hσdef, hsper i p]
  have hΛk : ∀ k, 1 ≤ k → k ≤ M → |K k| ≤ Λ ^ k := by
    intro k hk1 hkM
    have : |K k| ≤ ∑ i ∈ Finset.range (M + 1), |K i| :=
      Finset.single_le_sum (f := fun i => |K i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    calc |K k| ≤ Λ := by linarith
      _ = Λ ^ 1 := (pow_one _).symm
      _ ≤ Λ ^ k := pow_le_pow_right₀ hΛ1 hk1
  have hΨb : ∀ i ≤ M, ∀ p, ‖iteratedFDeriv ℝ i Ψ p‖ ≤ K' * (W : ℝ) ^ i := by
    intro i hi p
    rw [hΨdef, norm_iteratedFDeriv_ofReal hΨr]
    have hD : ∀ k, 1 ≤ k → k ≤ M → ‖iteratedFDeriv ℝ k h p‖ ≤ (Λ * W) ^ k := by
      intro k hk1 hkM
      rw [hhdef, norm_iteratedFDeriv_affine hσ _ _ (by omega)]
      have h1 : |(-a)| ≤ 1 := by rw [abs_neg, abs_of_nonneg ha0]; exact ha1
      calc |(-a)| * ‖iteratedFDeriv ℝ k σ p‖ ≤ 1 * (|K k| * (W : ℝ) ^ k) := by
            apply mul_le_mul h1 _ (norm_nonneg _) zero_le_one
            exact (norm_iteratedFDeriv_re_le hcd k p).trans ((hKb k p).trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
        _ ≤ Λ ^ k * (W : ℝ) ^ k := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (hΛk k hk1 hkM) (by positivity)
        _ = (Λ * W) ^ k := (mul_pow _ _ _).symm
    have hcf := hCf h hh p (Λ * W) (by positivity) hD i hi
    have hpe : (fun p => a ^ (M + 1) * cinv bι (h p)) =
        fun p => 0 + a ^ (M + 1) * cinv bι (h p) := by funext p; ring
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [norm_iteratedFDeriv_zero] at hcf ⊢
      simp only [pow_zero, mul_one] at hcf ⊢
      rw [norm_mul, norm_pow, Real.norm_of_nonneg ha0]
      calc a ^ (M + 1) * ‖cinv bι (h p)‖ ≤ 1 * Cf := by
            apply mul_le_mul (pow_le_one₀ ha0 ha1) hcf (norm_nonneg _) zero_le_one
        _ ≤ K' := by rw [one_mul, hK']; exact le_mul_of_one_le_right hCf0 (one_le_pow₀ hΛ1)
    · rw [hpe, norm_iteratedFDeriv_affine (f := fun q => cinv bι (h q))
        ((contDiff_cinv hbι0).comp hh) _ _ hi0.ne',
        abs_of_nonneg (by positivity)]
      calc a ^ (M + 1) * ‖iteratedFDeriv ℝ i (fun q => cinv bι (h q)) p‖
          ≤ 1 * (Cf * (Λ * W) ^ i) :=
            mul_le_mul (pow_le_one₀ ha0 ha1) hcf (norm_nonneg _) zero_le_one
        _ = Cf * Λ ^ i * (W : ℝ) ^ i := by rw [mul_pow]; ring
        _ ≤ K' * (W : ℝ) ^ i := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ1 hi) hCf0
  set Ft : (Fin d → ℝ) → ℂ := fun p => (∑ n ∈ Finset.Ico 1 (M + 1),
      (a : ℂ) ^ n * zdSymbol s p ^ n) + zdSymbol s p ^ (M + 1) * Ψ p with hFt
  have hFtc : ContDiff ℝ ∞ Ft :=
    (ContDiff.sum fun n _ => contDiff_const.mul (hcd.pow n)).add ((hcd.pow _).mul hΨ)
  have hwa : ‖(a : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg ha0]; exact ha1
  -- the symbol on the cube
  have hsym : ∀ p ∈ cubePi d, (highCut W p : ℂ) *
      ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p)) =
        Ft p - (coreCut W 0 p : ℂ) * Ft p := by
    intro p hp
    have hhc : highCut (d := d) W p = 1 - coreCut W 0 p := by
      simp [highCut, coreCut]
    rw [hhc]
    push_cast
    rw [← one_sub_mul]
    by_cases h0 : (1 : ℂ) - (coreCut W 0 p : ℂ) = 0
    · rw [h0, zero_mul, zero_mul]
    congr 1
    have hlow : 1 < (W : ℝ) ^ 2 * sqNorm p := by
      by_contra hle
      push Not at hle
      apply h0
      have : coreCut (d := d) W 0 p = 1 := by
        simp only [coreCut, pow_zero, one_mul]; exact lowPass_eq_one' hle
      rw [this]; simp
    obtain ⟨him, hge⟩ := hW₁ W (le_trans (le_max_right _ _) hW) s hs p hp
    have hX : 0 ≤ (W : ℝ) ^ 2 * sqNorm p := by linarith
    have h1 := one_sub_mul_ge hc ha0 ha1 hX hge
    rw [min_eq_right hlow.le, mul_one] at h1
    have hhp : bι ≤ h p := by
      simp only [hhdef, hσdef, hbι]; linarith
    have hse : zdSymbol s p = ((zdSymbol s p).re : ℂ) := Complex.ext (by simp) (by simp [him])
    simp only [hFt, hΨdef, cinv_eq hbι0 hhp]
    set t := (zdSymbol s p).re with ht
    have hhp' : h p = 1 - a * t := by simp only [hhdef, hσdef, ht]; ring
    rw [hhp']
    have hpos : 0 < 1 - a * t := by linarith
    have hz : (a : ℂ) * zdSymbol s p ≠ 1 := by
      rw [hse]
      intro heq
      have : ((a * t : ℝ) : ℂ) = 1 := by push_cast; exact heq
      have : a * t = 1 := by exact_mod_cast this
      linarith
    rw [geom_identity _ hz M]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow]
    · rw [hse, mul_pow]
      push_cast
      field_simp
  have hlf : latticeFourier (fun p => (highCut W p : ℂ) *
      ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))) x =
      latticeFourier Ft x - latticeFourier (fun p => (coreCut W 0 p : ℂ) * Ft p) x := by
    rw [latticeFourier_congr hsym x]
    exact latticeFourier_sub (hFtc.continuous.continuousOn.integrableOn_compact isCompact_cubePi'')
      (((Complex.ofRealCLM.contDiff.comp (contDiff_coreCut W 0)).mul hFtc).continuous.continuousOn
        |>.integrableOn_compact isCompact_cubePi'') x
  rw [hlf]
  -- the low-pass part
  set HL : (Fin d → ℝ) → ℂ := fun p => (coreCut W 0 p : ℂ) * Ft p with hHL
  have hHLc : ContDiff ℝ ∞ HL := (Complex.ofRealCLM.contDiff.comp (contDiff_coreCut W 0)).mul hFtc
  have hFtb : ∀ k ≤ M, ∀ p, ‖iteratedFDeriv ℝ k Ft p‖ ≤ BF 0 * (W : ℝ) ^ k := by
    intro k hk p
    have hfb : ∀ i ≤ M, ∀ p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ Km * (W : ℝ) ^ i := by
      intro i hi p
      refine (hKb i p).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have : |K i| ≤ ∑ i ∈ Finset.range (M + 1), |K i| :=
        Finset.single_le_sum (f := fun i => |K i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
      linarith [le_abs_self (K i)]
    have hΨb' : ∀ i ≤ M, ∀ p, ‖iteratedFDeriv ℝ i Ψ p‖ ≤ Km * (W : ℝ) ^ i := fun i hi p =>
      (hΨb i hi p).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    exact polyRem_deriv_le M hKm1 hW0.le hcd hΨ hwa hfb hΨb' k hk p
  have hLb : ∀ n ≤ M, ∀ p, ‖iteratedFDeriv ℝ n HL p‖ ≤ BL * (W : ℝ) ^ n := by
    intro n hn p
    have hA : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun q => (coreCut W 0 q : ℂ)) p‖ ≤
        Cs * (W : ℝ) ^ i := by
      intro i hi
      rw [norm_iteratedFDeriv_ofReal (contDiff_coreCut W 0)]
      have := (hCc i W 0 p).2.1
      rw [pow_zero, one_mul] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cc i|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
    have := norm_iteratedFDeriv_mul_le_of (Complex.ofRealCLM.contDiff.comp (contDiff_coreCut W 0))
      hFtc p n hW0.le hA (fun i hi => hFtb i (hi.trans hn) p)
    refine this.trans ?_
    rw [hBL]
    have : (2 : ℝ) ^ n ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hn
    have hBF0 : 0 ≤ BF 0 := by simp only [hBF]; positivity
    calc 2 ^ n * Cs * BF 0 * (W : ℝ) ^ n ≤ 2 ^ M * Cs * BF 0 * (W : ℝ) ^ n := by gcongr
      _ = _ := rfl
  have hLsupp : ∀ p, 2 / (W : ℝ) ≤ ‖p‖ → HL p = 0 := by
    intro p hp
    have h4 : 4 ≤ (W : ℝ) ^ 2 * sqNorm p := by
      have h1 : ‖p‖ ^ 2 ≤ sqNorm p := norm_sq_le_sqNorm p
      have h2 : 2 ≤ (W : ℝ) * ‖p‖ := by rwa [div_le_iff₀ hW0, mul_comm] at hp
      calc (4 : ℝ) ≤ ((W : ℝ) * ‖p‖) ^ 2 := by nlinarith
        _ = (W : ℝ) ^ 2 * ‖p‖ ^ 2 := by ring
        _ ≤ (W : ℝ) ^ 2 * sqNorm p := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hz : coreCut (d := d) W 0 p = 0 := by
      simp only [coreCut, pow_zero, one_mul]; exact lowPass_eq_zero' h4
    simp only [hHL, hz, Complex.ofReal_zero, zero_mul]
  have hr2 : 2 / (W : ℝ) ≤ 2 := by rw [div_le_iff₀ hW0]; nlinarith
  have hL0 : ∀ p, ‖HL p‖ ≤ BL := fun p => by
    have := hLb 0 (Nat.zero_le _) p
    rwa [norm_iteratedFDeriv_zero, pow_zero, mul_one] at this
  have hlow := kernel_bound_of_support M hHLc (by positivity) hr2 hW0 hLsupp hL0
    (hLb M le_rfl) x
  have hpr := hB₁ W s Ψ (a : ℂ) hWn hs hwa hΨ hΨper hΨb x
  set wt := (1 + (zdInf x : ℝ) / W) ^ M with hwt
  have hwt0 : 0 ≤ wt := by positivity
  calc ‖latticeFourier Ft x - latticeFourier HL x‖ * wt
      ≤ (‖latticeFourier Ft x‖ + ‖latticeFourier HL x‖) * wt :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) hwt0
    _ = ‖latticeFourier Ft x‖ * wt + ‖latticeFourier HL x‖ * wt := by ring
    _ ≤ B₁ / (W : ℝ) ^ d + 2 ^ M * (((2 * Real.pi) ^ d)⁻¹ * (2 * (2 / (W : ℝ))) ^ d * (BL + BL)) :=
        add_le_add hpr hlow
    _ = (B₁ + 2 ^ M * (((2 * Real.pi) ^ d)⁻¹ * 4 ^ d * (BL + BL))) / (W : ℝ) ^ d := by
        rw [show 2 * (2 / (W : ℝ)) = 4 / W by ring, div_pow]
        field_simp

/-- `1 - a σ ≥ (1 - a)/2` for `σ ≤ 1` and `0 ≤ a ≤ 1`. -/
private theorem one_sub_mul_ge_half {a σ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hσ : σ ≤ 1) :
    (1 - a) / 2 ≤ 1 - a * σ := by
  rcases le_or_gt (1 / 2) σ with h | h
  · nlinarith
  · rcases le_or_gt 0 σ with h' | h'
    · nlinarith
    · nlinarith

/-- The core and the high part of `Θ_{ℤ^d}(a)`: for `a < 1` and `J = shellCount a`,
`|K_core(x)| (1 + |x|/(2^J W))^M ≤ C₀ 4^J (2^J W)^{-d}`; for `a ∈ [0, 1]`,
`|K_high(x)| (1 + |x|/W)^M ≤ C₀ W^{-d}`. With `shellKernel_bound` and `shellCut_partition`,
these give the decay of `Θ_{ℤ^d}` that enters [I, (1.17)]. -/
theorem coreKernel_bound :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ)
    (C : ℕ → ℝ) (M : ℕ), ∃ C₀ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → ∀ x : Fin d → ℤ,
        (a < 1 →
          ‖latticeFourier (fun p => (coreCut W (shellCount a) p : ℂ) *
              ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))) x‖ *
            (1 + (zdInf x : ℝ) / (2 ^ shellCount a * W)) ^ M ≤
          C₀ * 4 ^ shellCount a / (2 ^ shellCount a * (W : ℝ)) ^ d) ∧
        ‖latticeFourier (fun p => (highCut W p : ℂ) *
              ((a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))) x‖ *
            (1 + (zdInf x : ℝ) / W) ^ M ≤ C₀ / (W : ℝ) ^ d := by
  intro d ψ cψ hψ C M
  obtain ⟨Ch, Wh, hCh0, hWh1, hhigh⟩ := high_kernel_bound d ψ cψ hψ C M
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  choose Cc hCc using norm_iteratedFDeriv_cut_le d
  obtain ⟨c, W₁, hc, hW₁⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  obtain ⟨Cc0, hCc00, hcore⟩ := shellKernel_piece_kernel_bound (d := d) K Cc (b := 1 / 2) (by norm_num) M
  refine ⟨max Cc0 Ch, max (max 1 W₁) Wh, ?_⟩
  intro W hW s hs a ha0 ha1 x
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  refine ⟨fun ha => ?_, ?_⟩
  · set J := shellCount a with hJ
    obtain ⟨hJ1, -⟩ := shellCount_spec a ha0 ha
    have hcd := (hK 0 W hWn s hs).1
    have hKall : ∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * (W : ℝ) ^ i :=
      fun i p => (hK i W hWn s hs).2.2 p
    have hK2 := hs.norm_fderiv_le hcd (fun q => hKall 2 q)
    set R : Set (Fin d → ℝ) := {p | (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J} with hRdef
    have hR : ∀ p ∈ R, (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J ∧
        1 / 2 ≤ 4 ^ J * (1 - a * (zdSymbol s p).re) := by
      intro p hp
      refine ⟨hp, ?_⟩
      have h4 : (4 : ℝ) / 4 ^ J ≤ 4 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
      have hcube := mem_cubePi_of_sqNorm_le hW1 ((show (W : ℝ) ^ 2 * sqNorm p ≤ 4 / 4 ^ J
        from hp).trans h4)
      obtain ⟨-, hge⟩ := hW₁ W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW) s
        hs p hcube
      have hX : 0 ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
        le_min (mul_nonneg (by positivity) (sqNorm_nonneg' p)) zero_le_one
      have hσ1 : (zdSymbol s p).re ≤ 1 := by nlinarith
      have h1 := one_sub_mul_ge_half ha0 ha1 hσ1
      have hpos : 0 < 1 - a := by linarith
      have h2 : 1 ≤ (4 : ℝ) ^ J * (1 - a) := by
        rw [inv_le_iff_one_le_mul₀ hpos] at hJ1; linarith
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) J]
    have hRχ : ∀ p ∉ R, coreCut (d := d) W J =ᶠ[nhds p] 0 := fun p hp =>
      coreCut_eventually_zero hp
    have hsupp : ∀ p, coreCut (d := d) W J p ≠ 0 → (W : ℝ) ^ 2 * sqNorm p < 4 / 4 ^ J := by
      intro p hp
      by_contra hle
      push Not at hle
      apply hp
      unfold coreCut
      apply lowPass_eq_zero'
      rw [div_le_iff₀ (by positivity)] at hle
      nlinarith
    have := hcore W J a s (coreCut W J) R hW1 ha0 ha.le hcd hs.im_eq hKall hK2
      (contDiff_coreCut W J) (fun i p => (hCc i W J p).2.1) hRχ hR hsupp x
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hhigh W (le_trans (le_max_right _ _) hW) s hs a ha0 ha1 x).trans ?_
    gcongr
    exact le_max_right _ _

end CoreHigh

/-! ## Integrability of the symbol of `Θ_{ℤ^d}` for `d ≥ 3` -/

section Integrability

private theorem integrableOn_abs_rpow {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun t : ℝ => |t| ^ r) (Set.Icc (-Real.pi) Real.pi) := by
  have h0 : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 Real.pi :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have h1 : IntervalIntegrable (fun t : ℝ => |t| ^ r) volume 0 Real.pi := by
    refine IntervalIntegrable.congr (fun t ht => ?_) h0
    rw [Set.uIoc_of_le Real.pi_pos.le] at ht
    simp only [abs_of_pos ht.1]
  have h2 : IntervalIntegrable (fun t : ℝ => |t| ^ r) volume (-Real.pi) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun t : ℝ => |t| ^ r)).1 h1
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).1 (h2.trans h1)

private theorem prod_abs_rpow (r : ℝ) (p : Fin d → ℝ) (S : Finset (Fin d)) :
    ∏ i ∈ S, |p i| ^ r = (∏ i ∈ S, |p i|) ^ r := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Real.mul_rpow (abs_nonneg _) (Finset.prod_nonneg fun i _ => abs_nonneg _)]

/-- `p ↦ Π_i |p_i|^{-2/d}` is integrable on `[-π, π]^d` for `d ≥ 3`. -/
private theorem integrableOn_prod_rpow (hd : 3 ≤ d) :
    IntegrableOn (fun p : Fin d → ℝ => ∏ i, |p i| ^ (-(2 : ℝ) / d)) (cubePi d) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : -1 < -(2 : ℝ) / d := by
    rw [neg_div, neg_lt_neg_iff, div_lt_one (by linarith)]; linarith
  have h1 := integrableOn_abs_rpow hr
  have hmeas : volume.restrict (cubePi d) =
      Measure.pi fun _ : Fin d => volume.restrict (Set.Icc (-Real.pi) Real.pi) := by
    unfold cubePi
    rw [volume_pi, Measure.restrict_pi_pi]
  unfold IntegrableOn
  rw [hmeas]
  exact Integrable.fintype_prod (f := fun _ t => |t| ^ (-(2 : ℝ) / d)) fun _ => h1

private theorem ae_coord_ne_zero :
    ∀ᵐ p ∂(volume : Measure (Fin d → ℝ)), ∀ i, p i ≠ 0 := by
  rw [ae_iff]
  have : {p : Fin d → ℝ | ¬ ∀ i, p i ≠ 0} = ⋃ i, {p | p i = 0} := by
    ext p; simp
  rw [this, measure_iUnion_null_iff]
  intro i
  rw [volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i 0

/-- `‖p‖^{-2} ≤ Π_i |p_i|^{-2/d}` when all coordinates are nonzero. -/
private theorem inv_norm_sq_le_prod (hd : 1 ≤ d) {p : Fin d → ℝ} (hp : ∀ i, p i ≠ 0) :
    (‖p‖ ^ 2)⁻¹ ≤ ∏ i, |p i| ^ (-(2 : ℝ) / d) := by
  have hpos : 0 < ∏ i, |p i| := Finset.prod_pos fun i _ => abs_pos.2 (hp i)
  have hle : ∏ i, |p i| ≤ ‖p‖ ^ d := by
    calc ∏ i, |p i| ≤ ∏ _i : Fin d, ‖p‖ :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p i
      _ = ‖p‖ ^ d := by simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : 0 < ‖p‖ := by
    obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact lt_of_lt_of_le (abs_pos.2 (hp i)) (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p i)
  rw [prod_abs_rpow]
  calc (‖p‖ ^ 2)⁻¹ = (‖p‖ ^ d) ^ (-(2 : ℝ) / d) := by
        rw [← Real.rpow_natCast ‖p‖ d, ← Real.rpow_mul hn.le]
        have : (d : ℝ) * (-(2 : ℝ) / d) = -2 := by field_simp
        rw [this, Real.rpow_neg hn.le, Real.rpow_two]
    _ ≤ (∏ i, |p i|) ^ (-(2 : ℝ) / d) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by
          have : (0 : ℝ) ≤ 2 / d := by positivity
          rw [neg_div]; linarith)

/-- For `d ≥ 3` the symbol `a ŝ/(1 - a ŝ)` of `Θ_{ℤ^d}(a)` is integrable on `[-π, π]^d`,
uniformly in `a ∈ [0, 1]`: `|a ŝ/(1 - a ŝ)| ≲ 1 + (W|p|)^{-2}`. -/
private theorem integrableOn_theta_symbol (d : ℕ) (hd : 3 ≤ d)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ) (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (a : ℝ), 0 ≤ a → a ≤ 1 →
        IntegrableOn (fun p => (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))
          (cubePi d) := by
  obtain ⟨K₀, hK₀⟩ := zdSymbol_smooth d ψ C 0
  obtain ⟨c, W₁, hc, hW₁⟩ := one_sub_zdSymbol_ge d ψ cψ hψ C
  have hc1 : 0 < min c 1 := lt_min hc one_pos
  refine ⟨max 1 W₁, le_max_left _ _, ?_⟩
  intro W hW s hs a ha0 ha1
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hcd, -, hb0⟩ := hK₀ W hWn s hs
  set B : ℝ := |K₀| / min c 1 with hB
  set G : (Fin d → ℝ) → ℝ := fun p => ∏ i, |p i| ^ (-(2 : ℝ) / d) with hG
  have hGi := integrableOn_prod_rpow hd
  have hbound : IntegrableOn (fun p => B * (1 + ((W : ℝ) ^ 2)⁻¹ * G p)) (cubePi d) :=
    ((integrableOn_const isCompact_cubePi''.measure_lt_top.ne).add
      (hGi.const_mul _)).const_mul B
  refine Integrable.mono' hbound ?_ ?_
  · have : Measurable fun p => (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p) := by
      have hm := hcd.continuous.measurable
      fun_prop
    exact this.aestronglyMeasurable
  · have hae := ae_restrict_of_ae (s := cubePi d) (ae_coord_ne_zero (d := d))
    filter_upwards [hae, ae_restrict_mem measurableSet_cubePi'] with p hp hpc
    obtain ⟨him, hge⟩ := hW₁ W (le_trans (le_max_right _ _) hW) s hs p hpc
    set σ := (zdSymbol s p).re with hσ
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσ]) (by simp [him])
    have hσb : |σ| ≤ |K₀| := by
      have := hb0 p
      rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, hse, Complex.norm_real,
        Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have hd1 : 1 ≤ d := by omega
    have hn : 0 < ‖p‖ := by
      obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
      exact lt_of_lt_of_le (abs_pos.2 (hp i))
        (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p i)
    set u := (W : ℝ) ^ 2 * ‖p‖ ^ 2 with hu
    have hu0 : 0 < u := by positivity
    have hmin : min u 1 ≤ min ((W : ℝ) ^ 2 * sqNorm p) 1 :=
      min_le_min_right _ (mul_le_mul_of_nonneg_left (norm_sq_le_sqNorm p) (by positivity))
    have h1 := one_sub_mul_ge hc ha0 ha1 (mul_nonneg (by positivity) (sqNorm_nonneg' p)) hge
    have hden : min c 1 * min u 1 ≤ 1 - a * σ :=
      (mul_le_mul_of_nonneg_left hmin hc1.le).trans h1
    have hmu : 0 < min u 1 := lt_min hu0 one_pos
    have hden0 : 0 < 1 - a * σ := lt_of_lt_of_le (by positivity) hden
    have hinv : (min u 1)⁻¹ ≤ 1 + ((W : ℝ) ^ 2)⁻¹ * G p := by
      have h2 : (min u 1)⁻¹ ≤ 1 + u⁻¹ := by
        rcases le_total u 1 with h | h
        · rw [min_eq_left h]; linarith [inv_nonneg.2 (zero_le_one : (0 : ℝ) ≤ 1)]
        · rw [min_eq_right h, inv_one]; linarith [inv_nonneg.2 hu0.le]
      have h3 : u⁻¹ ≤ ((W : ℝ) ^ 2)⁻¹ * G p := by
        rw [hu, mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_norm_sq_le_prod hd1 hp) (by positivity)
      linarith
    rw [hse]
    have hcast : (a : ℂ) * (σ : ℂ) / (1 - (a : ℂ) * (σ : ℂ)) = ((a * σ / (1 - a * σ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hden0]
    have hnum : |a * σ| ≤ |K₀| := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc a * |σ| ≤ 1 * |K₀| := mul_le_mul ha1 hσb (abs_nonneg _) zero_le_one
        _ = |K₀| := one_mul _
    rw [div_le_iff₀ hden0]
    calc |a * σ| ≤ |K₀| := hnum
      _ = B * (min c 1 * min u 1) * (min u 1)⁻¹ := by
          rw [hB]; field_simp
      _ ≤ B * (1 - a * σ) * (1 + ((W : ℝ) ^ 2)⁻¹ * G p) := by
          have hB0 : 0 ≤ B := by positivity
          apply mul_le_mul (mul_le_mul_of_nonneg_left hden hB0) hinv (by positivity)
            (by positivity)
      _ = B * (1 + ((W : ℝ) ^ 2)⁻¹ * G p) * (1 - a * σ) := by ring

end Integrability

/-! ## Assembly: the decay of `Θ_{ℤ^d}` -/

section Assembly

private theorem norm_latticeFourier_le (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    ‖latticeFourier F x‖ ≤ ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖F p‖ := by
  unfold latticeFourier
  rw [norm_mul]
  have hc : ‖((2 * Real.pi : ℂ) ^ d)⁻¹‖ = ((2 * Real.pi) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hc]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext p
  rw [norm_mul, norm_zexp, mul_one]

private theorem abs_cut_le_one {W j J : ℕ} (p : Fin d → ℝ) :
    |highCut W p| ≤ 1 ∧ |shellCut W j p| ≤ 1 ∧ |coreCut W J p| ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have := lowPass_mem_Icc ((W : ℝ) ^ 2 * sqNorm p)
    unfold highCut; rw [abs_le]; constructor <;> linarith
  · have h1 := lowPass_mem_Icc (4 ^ j * (W : ℝ) ^ 2 * sqNorm p)
    have h2 := lowPass_mem_Icc (4 ^ (j + 1) * (W : ℝ) ^ 2 * sqNorm p)
    unfold shellCut; rw [abs_le]; constructor <;> linarith
  · have := lowPass_mem_Icc (4 ^ J * (W : ℝ) ^ 2 * sqNorm p)
    unfold coreCut; rw [abs_le]; constructor <;> linarith

private theorem integrableOn_cut_mul {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    {χ : (Fin d → ℝ) → ℝ} (hχ : Continuous χ) (hb : ∀ p, |χ p| ≤ 1) :
    IntegrableOn (fun p => (χ p : ℂ) * F p) (cubePi d) := by
  refine Integrable.bdd_mul (c := 1) hF
    (Complex.continuous_ofReal.comp hχ).aestronglyMeasurable (Filter.Eventually.of_forall
      fun p => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact hb p

/-- The dyadic decomposition of a kernel: high part, shells `j < J`, core at scale `J`. -/
private theorem latticeFourier_decomp {F : (Fin d → ℝ) → ℂ} (hF : IntegrableOn F (cubePi d))
    (W J : ℕ) (x : Fin d → ℤ) :
    latticeFourier F x = latticeFourier (fun p => (highCut W p : ℂ) * F p) x +
      ∑ j ∈ Finset.range J, latticeFourier (fun p => (shellCut W j p : ℂ) * F p) x +
      latticeFourier (fun p => (coreCut W J p : ℂ) * F p) x := by
  have hh := integrableOn_cut_mul hF (contDiff_highCut (d := d) W).continuous
    fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).1
  have hs : ∀ j ∈ Finset.range J, IntegrableOn (fun p => (shellCut W j p : ℂ) * F p) (cubePi d) :=
    fun j _ => integrableOn_cut_mul hF (contDiff_shellCut (d := d) W j).continuous
      fun p => (abs_cut_le_one (W := W) (j := j) (J := J) p).2.1
  have hc := integrableOn_cut_mul hF (contDiff_coreCut (d := d) W J).continuous
    fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2
  have hsum : IntegrableOn (fun p => ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p)
      (cubePi d) := by
    exact integrable_finsetSum (Finset.range J) hs
  have hpt : ∀ p ∈ cubePi d, F p = ((highCut W p : ℂ) * F p +
      ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p) + (coreCut W J p : ℂ) * F p := by
    intro p _
    have h := shellCut_partition (d := d) W J p
    have hc' : ((highCut W p + ∑ j ∈ Finset.range J, shellCut W j p + coreCut W J p : ℝ) : ℂ) =
        1 := by
      rw [h]; simp
    push_cast at hc'
    rw [← Finset.sum_mul, ← add_mul, ← add_mul, hc', one_mul]
  rw [latticeFourier_congr hpt x,
    latticeFourier_add (F := fun p => (highCut W p : ℂ) * F p +
      ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p)
      (G := fun p => (coreCut W J p : ℂ) * F p) (hh.add hsum) hc,
    latticeFourier_add (F := fun p => (highCut W p : ℂ) * F p)
      (G := fun p => ∑ j ∈ Finset.range J, (shellCut W j p : ℂ) * F p) hh hsum,
    latticeFourier_finset_sum (F := fun j p => (shellCut W j p : ℂ) * F p) _ hs]

/-- Absorbing a weight: from `X (1 + u)^{M+e} ≤ B` and `w ≤ κ (1 + u)^M`,
`X w ≤ κ B (1 + u)^{-e}`. -/
private theorem absorb_weight {X u w B κ : ℝ} {M e : ℕ} (hX : 0 ≤ X) (hu : 0 ≤ u) (hκ : 0 ≤ κ)
    (h : X * (1 + u) ^ (M + e) ≤ B) (hw : w ≤ κ * (1 + u) ^ M) :
    X * w ≤ κ * B * ((1 + u) ^ e)⁻¹ := by
  have hpos : 0 < (1 + u) ^ e := pow_pos (by linarith) e
  calc X * w ≤ X * (κ * (1 + u) ^ M) := mul_le_mul_of_nonneg_left hw hX
    _ = κ * (X * (1 + u) ^ (M + e)) * ((1 + u) ^ e)⁻¹ := by
        rw [pow_add]; field_simp
    _ ≤ κ * B * ((1 + u) ^ e)⁻¹ := by gcongr

/-- `4^j (2^j W)^{-d} = (2^j)^{-(d-2)} W^{-d}` for `d ≥ 2`. -/
private theorem four_pow_div (hd : 2 ≤ d) (j : ℕ) (W : ℝ) (hW : 0 < W) :
    (4 : ℝ) ^ j / (2 ^ j * W) ^ d = (((2 : ℝ) ^ j) ^ (d - 2))⁻¹ / W ^ d := by
  have h4 : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e : ((2 : ℝ) ^ j) ^ d = ((2 : ℝ) ^ j) ^ (d - 2) * ((2 : ℝ) ^ j) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [h4, mul_pow, e]
  have : (0 : ℝ) < 2 ^ j := by positivity
  field_simp

/-- The core at scale `J` tends to `0` pointwise away from `0`. -/
private theorem tendsto_coreCut {W : ℕ} (hW : 1 ≤ W) {p : Fin d → ℝ} (hp : p ≠ 0) :
    Filter.Tendsto (fun J => coreCut W J p) Filter.atTop (nhds 0) := by
  have hsq : 0 < sqNorm p := by
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h; push Not at h; exact hp (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => p i ^ 2)
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hX : 0 < (W : ℝ) ^ 2 * sqNorm p := by positivity
  have hev : ∀ᶠ J in Filter.atTop, 4 / ((W : ℝ) ^ 2 * sqNorm p) ≤ (4 : ℝ) ^ J :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).eventually_ge_atTop _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with J hJ
  symm
  unfold coreCut
  apply lowPass_eq_zero'
  rw [div_le_iff₀ hX] at hJ
  linarith

/-- `(1 + |x| (1 - a)^{1/2}/W)^M ≤ 3^M (1 + |x|/(2^j W))^M` for `j ≤ shellCount a`, `a < 1`. -/
private theorem weight_le_shell {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {j : ℕ}
    (hj : j ≤ shellCount a) (X W : ℝ) (hX : 0 ≤ X) (hW : 0 < W) (M : ℕ) :
    (1 + X * Real.sqrt (1 - a) / W) ^ M ≤ 3 ^ M * (1 + X / (2 ^ j * W)) ^ M := by
  obtain ⟨-, hJ2⟩ := shellCount_spec a ha0 ha1
  have hpos : 0 < 1 - a := by linarith
  have h4j : (4 : ℝ) ^ j ≤ 4 ^ shellCount a := pow_le_pow_right₀ (by norm_num) hj
  have h1 : (1 - a) * 4 ^ shellCount a ≤ 8 := by
    have := mul_lt_mul_of_pos_left hJ2 hpos
    have e : (1 - a) * (4 * ((1 - a)⁻¹ + 1)) = 4 + 4 * (1 - a) := by field_simp
    rw [e] at this; linarith
  have h2 : 1 - a ≤ (3 / 2 ^ j) ^ 2 := by
    have e2 : (3 / (2 : ℝ) ^ j) ^ 2 = 9 / 4 ^ j := by
      rw [div_pow, ← pow_mul, mul_comm j 2, pow_mul]; norm_num
    rw [e2, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h4j hpos.le]
  have hsq : Real.sqrt (1 - a) ≤ 3 / 2 ^ j :=
    Real.sqrt_le_iff.2 ⟨by positivity, h2⟩
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have : X * Real.sqrt (1 - a) / W ≤ 3 * (X / (2 ^ j * W)) := by
    calc X * Real.sqrt (1 - a) / W ≤ X * (3 / 2 ^ j) / W := by gcongr
      _ = 3 * (X / (2 ^ j * W)) := by field_simp
  have : 0 ≤ X / (2 ^ j * W) := by positivity
  linarith

/-- The decay of `Θ_{ℤ^d}(a)` for `d ≥ 3`, uniformly in `a ∈ [0, 1]`: the symbol
`a ŝ/(1 - a ŝ)` is integrable on `[-π, π]^d` and
`|Θ_{ℤ^d}(a)(x)| (1 + |x| (1 - a)^{1/2}/W)^M ≤ C₀ W^{-2} (|x| + W)^{-(d-2)}`, i.e. the bound
`W^{-2} ⟨x⟩^{-(d-2)} (1 + |x|/R_a)^{-M}` with `R_a = W (1 - a)^{-1/2}` that enters [I, (1.17)].
The proof does not use [I, Lemma B.1] or [I, (B.3), (B.7)–(B.11)]. -/
theorem ThetaZd_decay :
  ∀ (d : ℕ) (hd : 3 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (M : ℕ), ∃ C₀ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s → ∀ (a : ℝ), 0 ≤ a → a ≤ 1 →
        IntegrableOn (fun p => (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p))
          (cubePi d) ∧
        ∀ x : Fin d → ℤ,
          ‖ThetaZd a s x‖ * (1 + (zdInf x : ℝ) * Real.sqrt (1 - a) / W) ^ M ≤
            C₀ / ((W : ℝ) ^ 2 * ((zdInf x : ℝ) + W) ^ (d - 2)) := by
  intro d hd ψ cψ hψ C M
  set M' := M + (d - 1) with hM'
  obtain ⟨C₁, W₁, hsh⟩ := shellKernel_bound d ψ cψ hψ C M'
  obtain ⟨C₂, W₂, hch⟩ := coreKernel_bound d ψ cψ hψ C M'
  obtain ⟨CS, hCS⟩ := sum_shell_le d (d - 1) hd (by omega)
  obtain ⟨Wi, hWi1, hint⟩ := integrableOn_theta_symbol d hd ψ cψ hψ C
  set A : ℝ := |C₁| + |C₂| with hA
  refine ⟨3 ^ M * A * (|CS| + 2), max (max W₁ W₂) Wi, ?_⟩
  intro W hW s hs a ha0 ha1
  have hWi : Wi ≤ (W : ℝ) := le_trans (le_max_right _ _) hW
  have hW1' : W₁ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2' : W₂ ≤ (W : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := hWi1.trans hWi
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set Fs : (Fin d → ℝ) → ℂ := fun p => (a : ℂ) * zdSymbol s p / (1 - (a : ℂ) * zdSymbol s p)
    with hFs
  have hFi : IntegrableOn Fs (cubePi d) := hint W hWi s hs a ha0 ha1
  refine ⟨hFi, fun x => ?_⟩
  set t : ℝ := (zdInf x : ℝ) / W with ht
  have ht0 : 0 ≤ t := by positivity
  set T : ℝ := ((1 + t) ^ (d - 2))⁻¹ with hT
  have hT0 : 0 ≤ T := by positivity
  have hd2 : 2 ≤ d := by omega
  have hRHS : 3 ^ M * A * (|CS| + 2) / ((W : ℝ) ^ 2 * ((zdInf x : ℝ) + W) ^ (d - 2)) =
      3 ^ M * A * (|CS| + 2) * T / (W : ℝ) ^ d := by
    have e1 : (zdInf x : ℝ) + W = W * (1 + t) := by rw [ht]; field_simp; ring
    have e2 : (W : ℝ) ^ d = W ^ 2 * W ^ (d - 2) := by rw [← pow_add]; congr 1; omega
    rw [e1, mul_pow, hT, e2]
    field_simp
  rw [hRHS]
  have hTheta : ThetaZd a s x = latticeFourier Fs x := rfl
  rw [hTheta]
  have hA0 : 0 ≤ A := by positivity
  have h3M : (1 : ℝ) ≤ 3 ^ M := one_le_pow₀ (by norm_num)
  have hu : ∀ j : ℕ, (zdInf x : ℝ) / (2 ^ j * W) = t / 2 ^ j := fun j => by
    rw [ht]; field_simp
  have hshell : ∀ j, ‖latticeFourier (fun p => (shellCut W j p : ℂ) * Fs p) x‖ *
      (1 + t / 2 ^ j) ^ (M + (d - 1)) ≤ C₁ * ((((2 : ℝ) ^ j) ^ (d - 2))⁻¹ / (W : ℝ) ^ d) := by
    intro j
    have := hsh W hW1' s hs a ha0 ha1 j x
    rw [hu j, mul_div_assoc, four_pow_div hd2 j W hW0] at this
    exact this
  have hTle : ∀ e, d - 2 ≤ e → ((1 + t) ^ e)⁻¹ ≤ T := fun e he =>
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) he)
  -- the high part, for any weight `≤ (1 + t)^M`
  have hhigh : ∀ w, w ≤ 1 * (1 + t) ^ M →
      ‖latticeFourier (fun p => (highCut W p : ℂ) * Fs p) x‖ * w ≤ |C₂| / (W : ℝ) ^ d * T := by
    intro w hw
    have h := (hch W hW2' s hs a ha0 ha1 x).2
    rw [← ht] at h
    have := absorb_weight (norm_nonneg _) ht0 zero_le_one h hw
    refine this.trans ?_
    rw [one_mul]
    apply mul_le_mul _ (hTle (d - 1) (by omega)) (by positivity) (by positivity)
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  -- the shells, for any weight `≤ 3^M (1 + t/2^j)^M`
  have hshells : ∀ (J : ℕ) (w : ℝ), (∀ j < J, w ≤ 3 ^ M * (1 + t / 2 ^ j) ^ M) →
      ∑ j ∈ Finset.range J, ‖latticeFourier (fun p => (shellCut W j p : ℂ) * Fs p) x‖ * w ≤
        3 ^ M * |C₁| / (W : ℝ) ^ d * (|CS| * T) := by
    intro J w hw
    have hterm : ∀ j ∈ Finset.range J,
        ‖latticeFourier (fun p => (shellCut W j p : ℂ) * Fs p) x‖ * w ≤
          3 ^ M * |C₁| / (W : ℝ) ^ d *
            ((((2 : ℝ) ^ j) ^ (d - 2))⁻¹ * ((1 + t / 2 ^ j) ^ (d - 1))⁻¹) := by
      intro j hj
      have := absorb_weight (norm_nonneg _) (by positivity) (by positivity) (hshell j)
        (hw j (Finset.mem_range.1 hj))
      refine this.trans (le_of_eq_of_le rfl ?_)
      have hC1 : C₁ ≤ |C₁| := le_abs_self _
      calc 3 ^ M * (C₁ * ((((2 : ℝ) ^ j) ^ (d - 2))⁻¹ / (W : ℝ) ^ d)) *
            ((1 + t / 2 ^ j) ^ (d - 1))⁻¹
          ≤ 3 ^ M * (|C₁| * ((((2 : ℝ) ^ j) ^ (d - 2))⁻¹ / (W : ℝ) ^ d)) *
            ((1 + t / 2 ^ j) ^ (d - 1))⁻¹ := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (hCS J t ht0).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hT0
  have hnorm3 : ∀ (J : ℕ) (w : ℝ), 0 ≤ w →
      ‖latticeFourier Fs x‖ * w ≤
        ‖latticeFourier (fun p => (highCut W p : ℂ) * Fs p) x‖ * w +
        ∑ j ∈ Finset.range J, ‖latticeFourier (fun p => (shellCut W j p : ℂ) * Fs p) x‖ * w +
        ‖latticeFourier (fun p => (coreCut W J p : ℂ) * Fs p) x‖ * w := by
    intro J w hw
    rw [latticeFourier_decomp hFi W J x, ← Finset.sum_mul, ← add_mul, ← add_mul]
    apply mul_le_mul_of_nonneg_right _ hw
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add le_rfl (norm_sum_le _ _))) le_rfl)
  rcases lt_or_eq_of_le ha1 with ha | ha
  · -- `a < 1`: shells `j < J` and the core at `J = shellCount a`
    set J := shellCount a with hJ
    set w := (1 + (zdInf x : ℝ) * Real.sqrt (1 - a) / W) ^ M with hw
    have hw0 : 0 ≤ w := by positivity
    have hwj : ∀ j ≤ J, w ≤ 3 ^ M * (1 + t / 2 ^ j) ^ M := fun j hj => by
      have := weight_le_shell ha0 ha hj (zdInf x : ℝ) W (by positivity) hW0 M
      rwa [hu j] at this
    have hwh : w ≤ 1 * (1 + t) ^ M := by
      rw [one_mul]
      apply pow_le_pow_left₀ (by positivity)
      have : Real.sqrt (1 - a) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
      have : (zdInf x : ℝ) * Real.sqrt (1 - a) / W ≤ t := by
        rw [ht]
        exact div_le_div_of_nonneg_right
          (mul_le_of_le_one_right (by positivity) this) hW0.le
      linarith
    have hcore : ‖latticeFourier (fun p => (coreCut W J p : ℂ) * Fs p) x‖ * w ≤
        3 ^ M * |C₂| / (W : ℝ) ^ d * T := by
      have h := (hch W hW2' s hs a ha0 ha1 x).1 ha
      rw [← hJ, hu J, mul_div_assoc, four_pow_div hd2 J W hW0] at h
      have := absorb_weight (norm_nonneg _) (by positivity) (by positivity) h (hwj J le_rfl)
      refine this.trans ?_
      have hkey : (((2 : ℝ) ^ J) ^ (d - 2))⁻¹ * ((1 + t / 2 ^ J) ^ (d - 1))⁻¹ ≤ T := by
        rw [← mul_inv, hT]
        apply inv_anti₀ (by positivity)
        have h2J : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
        have hb : 1 ≤ 1 + t / 2 ^ J := le_add_of_nonneg_right (by positivity)
        calc (1 + t) ^ (d - 2) ≤ ((2 : ℝ) ^ J * (1 + t / 2 ^ J)) ^ (d - 2) := by
              apply pow_le_pow_left₀ (by positivity)
              rw [mul_add, mul_one, mul_div_cancel₀ _ (by positivity)]; linarith
          _ = ((2 : ℝ) ^ J) ^ (d - 2) * (1 + t / 2 ^ J) ^ (d - 2) := mul_pow _ _ _
          _ ≤ ((2 : ℝ) ^ J) ^ (d - 2) * (1 + t / 2 ^ J) ^ (d - 1) := by
              gcongr
              omega
      have hC2 : C₂ ≤ |C₂| := le_abs_self _
      calc 3 ^ M * (C₂ * ((((2 : ℝ) ^ J) ^ (d - 2))⁻¹ / (W : ℝ) ^ d)) *
            ((1 + t / 2 ^ J) ^ (d - 1))⁻¹
          = 3 ^ M * C₂ / (W : ℝ) ^ d *
            ((((2 : ℝ) ^ J) ^ (d - 2))⁻¹ * ((1 + t / 2 ^ J) ^ (d - 1))⁻¹) := by ring
        _ ≤ 3 ^ M * |C₂| / (W : ℝ) ^ d * T := by
            apply mul_le_mul _ hkey (by positivity) (by positivity)
            gcongr
    have hsum := hshells J w fun j hj => hwj j hj.le
    have hhi := hhigh w hwh
    refine (hnorm3 J w hw0).trans ?_
    have hfin : |C₂| / (W : ℝ) ^ d * T + 3 ^ M * |C₁| / (W : ℝ) ^ d * (|CS| * T) +
        3 ^ M * |C₂| / (W : ℝ) ^ d * T ≤ 3 ^ M * A * (|CS| + 2) * T / (W : ℝ) ^ d := by
      have hW' : (0 : ℝ) < (W : ℝ) ^ d := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hW'.le
      have h1 : |C₂| * T ≤ 3 ^ M * |C₂| * T := by
        have := mul_le_mul_of_nonneg_right h3M (mul_nonneg (abs_nonneg C₂) hT0)
        nlinarith
      have hCS0 : 0 ≤ |CS| := abs_nonneg _
      have h2 : |C₁| ≤ A := by rw [hA]; linarith [abs_nonneg C₂]
      have h3 : |C₂| ≤ A := by rw [hA]; linarith [abs_nonneg C₁]
      have h3M0 : (0 : ℝ) ≤ 3 ^ M := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg h3M0 (mul_nonneg hCS0 hT0)),
        mul_le_mul_of_nonneg_left h3 (mul_nonneg h3M0 hT0)]
    linarith
  · -- `a = 1`: all shells, the core tends to `0`
    subst ha
    have hw1 : (1 + (zdInf x : ℝ) * Real.sqrt (1 - 1) / W) ^ M = 1 := by simp
    rw [hw1, mul_one]
    set Bnd : ℝ := |C₂| / (W : ℝ) ^ d * T + 3 ^ M * |C₁| / (W : ℝ) ^ d * (|CS| * T) with hBnd
    have hstep : ∀ J : ℕ, ‖latticeFourier Fs x‖ ≤
        Bnd + ‖latticeFourier (fun p => (coreCut W J p : ℂ) * Fs p) x‖ := by
      intro J
      have h := hnorm3 J 1 zero_le_one
      simp only [mul_one] at h
      have hhi := hhigh 1 (by rw [one_mul]; exact one_le_pow₀ (by linarith))
      have hsum := hshells J 1 fun j _ => by
        have : (1 : ℝ) ≤ (1 + t / 2 ^ j) ^ M := one_le_pow₀ (by
          have : 0 ≤ t / 2 ^ j := by positivity
          linarith)
        nlinarith
      simp only [mul_one] at hhi hsum
      linarith
    have hd1 : 1 ≤ d := by omega
    have hDC : Filter.Tendsto (fun J : ℕ => ∫ p in cubePi d, ‖(coreCut W J p : ℂ) * Fs p‖)
        Filter.atTop (nhds 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (cubePi d))
        (F := fun (J : ℕ) p => ‖(coreCut W J p : ℂ) * Fs p‖) (f := fun _ => (0 : ℝ))
        (fun p => ‖Fs p‖)
        (fun J => (integrableOn_cut_mul hFi (contDiff_coreCut (d := d) W J).continuous
          fun p => (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2).norm.aestronglyMeasurable)
        hFi.norm
        (fun J => Filter.Eventually.of_forall fun p => by
          rw [norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (abs_cut_le_one (W := W) (j := 0) (J := J) p).2.2)
        (by
          filter_upwards [ae_restrict_of_ae (s := cubePi d) (ae_coord_ne_zero (d := d))]
            with p hp
          have hp0 : p ≠ 0 := by
            intro h0
            exact hp ⟨0, by omega⟩ (by rw [h0]; rfl)
          have h1 := tendsto_coreCut hWn hp0
          have h2 : Filter.Tendsto (fun J => ‖((coreCut W J p : ℝ) : ℂ) * Fs p‖) Filter.atTop
              (nhds ‖((0 : ℝ) : ℂ) * Fs p‖) :=
            ((Complex.continuous_ofReal.tendsto 0).comp h1 |>.mul_const _).norm
          simpa using h2)
      simpa using this
    have hcore0 : Filter.Tendsto
        (fun J : ℕ => ‖latticeFourier (fun p => (coreCut W J p : ℂ) * Fs p) x‖)
        Filter.atTop (nhds 0) := by
      have h2 := hDC.const_mul ((2 * Real.pi) ^ d)⁻¹
      rw [mul_zero] at h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
        (fun J => norm_nonneg _) (fun J => norm_latticeFourier_le _ x)
    have hlim : Filter.Tendsto
        (fun J : ℕ => Bnd + ‖latticeFourier (fun p => (coreCut W J p : ℂ) * Fs p) x‖)
        Filter.atTop (nhds (Bnd + 0)) := tendsto_const_nhds.add hcore0
    rw [add_zero] at hlim
    have hle : ‖latticeFourier Fs x‖ ≤ Bnd := ge_of_tendsto' hlim hstep
    refine hle.trans ?_
    have hW' : (0 : ℝ) < (W : ℝ) ^ d := by positivity
    rw [hBnd, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hW'.le
    have hCS0 : 0 ≤ |CS| := abs_nonneg _
    have h2 : |C₁| ≤ A := by rw [hA]; linarith [abs_nonneg C₂]
    have h3 : |C₂| ≤ A := by rw [hA]; linarith [abs_nonneg C₁]
    have h3M0 : (0 : ℝ) ≤ 3 ^ M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg h3M0 (mul_nonneg hCS0 hT0)),
      mul_le_mul_of_nonneg_left h3 (mul_nonneg h3M0 hT0),
      mul_le_mul_of_nonneg_right h3M (mul_nonneg (abs_nonneg C₂) hT0)]

/-- [I, Lemma 7.2], existence of `Θ_∞` and (7.7), for `d ≥ 3`: the symbol `ŝ/(1 - ŝ)` is
integrable on `[-π, π]^d` and `|(Θ_∞)_{0x}| ≤ W^{-2} (|x| + W)^{-(d-2-τ)}` for `W ≥ W₀`. -/
theorem ThetaInf_decay :
  ∀ (d : ℕ) (hd : 3 ≤ d) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (cψ : ℝ)
    (hψ : ProfileShape ψ cψ) (C : ℕ → ℝ) (τ : ℝ) (hτ : 0 < τ), ∃ W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
        IntegrableOn (fun p => zdSymbol s p / (1 - zdSymbol s p)) (cubePi d) ∧
        ∀ x : Fin d → ℤ,
          ‖ThetaInf s x‖ ≤ 1 / ((W : ℝ) ^ 2 * ((zdInf x : ℝ) + W) ^ ((d : ℝ) - 2 - τ)) := by
  intro d hd ψ cψ hψ C τ hτ
  obtain ⟨C₀, W₀, h⟩ := ThetaZd_decay d hd ψ cψ hψ C 0
  refine ⟨max (max W₀ 1) (|C₀| ^ (1 / τ)), ?_⟩
  intro W hW s hs
  have hW₀ : W₀ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWC : |C₀| ^ (1 / τ) ≤ (W : ℝ) := le_trans (le_max_right _ _) hW
  obtain ⟨hI, hb⟩ := h W hW₀ s hs 1 zero_le_one le_rfl
  refine ⟨?_, fun x => ?_⟩
  · simpa using hI
  · have hx := hb x
    rw [pow_zero, mul_one] at hx
    have hT : ThetaInf s x = ThetaZd 1 s x := rfl
    rw [hT]
    refine hx.trans ?_
    set y : ℝ := (zdInf x : ℝ) + W with hy
    have hy0 : 0 < y := by positivity
    have hWy : (W : ℝ) ≤ y := by rw [hy]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf x)]
    have hC : C₀ ≤ y ^ τ := by
      calc C₀ ≤ |C₀| := le_abs_self _
        _ = (|C₀| ^ (1 / τ)) ^ τ := by
            rw [← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
        _ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow (by positivity) hWC hτ.le
        _ ≤ y ^ τ := Real.rpow_le_rpow (by positivity) hWy hτ.le
    have hexp : y ^ ((d : ℝ) - 2 - τ) = y ^ (d - 2) / y ^ τ := by
      rw [Real.rpow_sub hy0, ← Real.rpow_natCast, Nat.cast_sub (by omega)]
      norm_num
    rw [hexp]
    have hyd : 0 < y ^ (d - 2) := by positivity
    have hyt : 0 < y ^ τ := Real.rpow_pos_of_pos hy0 τ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc C₀ * ((W : ℝ) ^ 2 * (y ^ (d - 2) / y ^ τ)) = C₀ * ((W : ℝ) ^ 2 * y ^ (d - 2)) / y ^ τ := by
          ring
      _ ≤ y ^ τ * ((W : ℝ) ^ 2 * y ^ (d - 2)) / y ^ τ := by gcongr
      _ = 1 * ((W : ℝ) ^ 2 * y ^ (d - 2)) := by field_simp

end Assembly

/-! ## `S^±_∞` -/

section Splus

/-- Derivatives of a complex affine image `c₀ + c₁ f`. -/
private theorem norm_iteratedFDeriv_affineC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (c₀ c₁ : ℂ) {k : ℕ} (hk : k ≠ 0) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => c₀ + c₁ * f y) x‖ = ‖c₁‖ * ‖iteratedFDeriv ℝ k f x‖ := by
  have he : (fun y => c₀ + c₁ * f y) = (fun _ => c₀) + c₁ • f := by
    funext y; simp [smul_eq_mul]
  have h2 : ContDiffAt ℝ k (c₁ • f) x :=
    (show ContDiff ℝ ∞ (c₁ • f) from hf.const_smul c₁).contDiffAt.of_le
      (by exact_mod_cast le_top)
  rw [he, iteratedFDeriv_add_apply (f := fun _ => c₀) (g := c₁ • f) contDiffAt_const h2,
    iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_add,
    iteratedFDeriv_const_smul_apply (hf.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul]

/-- `q(t) = 1 - 2 Re(w) t + t² = |1 - w t|²` is bounded below for `t ≥ -1 + c′/2`, when `|w| = 1`
and `|1 - w| ≥ δ ≥ 0`. -/
private theorem q_lower {w : ℂ} (hw : ‖w‖ = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ ‖1 - w‖)
    {c' t : ℝ} (hc' : 0 < c') (ht : -1 + c' / 2 ≤ t) :
    min (min 1 (δ ^ 2 / 2)) ((c' / 2) ^ 2) ≤ 1 - 2 * w.re * t + t ^ 2 := by
  have hn : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  have h1w : ‖1 - w‖ ^ 2 = 2 - 2 * w.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith
  have hδ2 : δ ^ 2 ≤ 2 - 2 * w.re := by
    rw [← h1w]; exact pow_le_pow_left₀ hδ0 hδ 2
  have hre1 : w.re ≤ 1 := by nlinarith [sq_nonneg w.im]
  have hre1' : -1 ≤ w.re := by nlinarith [sq_nonneg w.im]
  rcases le_or_gt 0 t with h0 | h0
  · rcases le_or_gt w.re 0 with hr | hr
    · have : 1 ≤ 1 - 2 * w.re * t + t ^ 2 := by nlinarith
      exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) this)
    · have : δ ^ 2 / 2 ≤ 1 - 2 * w.re * t + t ^ 2 := by nlinarith [sq_nonneg (t - w.re)]
      exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) this)
  · have h1t : c' / 2 ≤ 1 + t := by linarith
    have : (c' / 2) ^ 2 ≤ 1 - 2 * w.re * t + t ^ 2 := by
      have h2 : (c' / 2) ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ (by positivity) h1t 2
      nlinarith
    exact le_trans (min_le_right _ _) this

/-- `(1 - w t)(1 - w̄ t) = 1 - 2 Re(w) t + t²` for `|w| = 1` and real `t`. -/
private theorem one_sub_mul_conj {w : ℂ} (hw : ‖w‖ = 1) (t : ℝ) :
    (1 - w * t) * (1 - conj w * t) = ((1 - 2 * w.re * t + t ^ 2 : ℝ) : ℂ) := by
  have hn : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq w
    rw [hw, Complex.normSq_apply] at this
    nlinarith
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    nlinarith
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring

/-- Derivative bounds, uniform in `|w| = 1`, for
`Ψ_w = w^{N+1} (1 - w̄ f) cinv_b(1 - 2 Re(w) Re f + (Re f)²)` when `‖D^i f‖ ≤ K_i W^i`. -/
private theorem splusPsi_deriv_le (K : ℕ → ℝ) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ∃ K', 0 ≤ K' ∧ ∀ (W : ℝ) (w : ℂ) (f : (Fin d → ℝ) → ℂ), 1 ≤ W → ‖w‖ = 1 →
      ContDiff ℝ ∞ f → (∀ i p, ‖iteratedFDeriv ℝ i f p‖ ≤ K i * W ^ i) →
      ∀ i ≤ N, ∀ p, ‖iteratedFDeriv ℝ i (fun p => w ^ (N + 1) * ((1 - conj w * f p) *
        ((cinv b (1 + (-2 * w.re) * (f p).re + (f p).re ^ 2) : ℝ) : ℂ))) p‖ ≤ K' * W ^ i := by
  set Kσ : ℝ := 1 + ∑ i ∈ Finset.range (N + 1), |K i| with hKσ
  have hKσ1 : 1 ≤ Kσ := by
    have : 0 ≤ ∑ i ∈ Finset.range (N + 1), |K i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set Λ : ℝ := 2 * Kσ + 2 ^ N * Kσ ^ 2 with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ 2 ^ N * Kσ ^ 2 := by positivity
    linarith
  obtain ⟨Cf, hCf0, hCf⟩ := norm_iteratedFDeriv_cinv_comp_le (E := Fin d → ℝ) hb N
  refine ⟨2 ^ N * (1 + Kσ) * (Cf * Λ ^ N), by positivity, ?_⟩
  intro W w f hW hw hf hfK i hi p
  have hW0 : 0 ≤ W := by linarith
  have hKle : ∀ k ≤ N, K k ≤ Kσ := by
    intro k hk
    have : |K k| ≤ ∑ i ∈ Finset.range (N + 1), |K i| :=
      Finset.single_le_sum (f := fun i => |K i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    linarith [le_abs_self (K k)]
  have hfb : ∀ k ≤ N, ‖iteratedFDeriv ℝ k f p‖ ≤ Kσ * W ^ k := fun k hk =>
    (hfK k p).trans (mul_le_mul_of_nonneg_right (hKle k hk) (by positivity))
  set σ : (Fin d → ℝ) → ℝ := fun p => (f p).re with hσdef
  have hσ : ContDiff ℝ ∞ σ := Complex.reCLM.contDiff.comp hf
  have hσb : ∀ k ≤ N, ‖iteratedFDeriv ℝ k σ p‖ ≤ Kσ * W ^ k := fun k hk =>
    (norm_iteratedFDeriv_re_le hf k p).trans (hfb k hk)
  set h : (Fin d → ℝ) → ℝ := fun p => 1 + (-2 * w.re) * σ p + σ p ^ 2 with hhdef
  have hh : ContDiff ℝ ∞ h := (contDiff_const.add (contDiff_const.mul hσ)).add (hσ.pow 2)
  have hre : |(-2 * w.re)| ≤ 2 := by
    rw [abs_mul, abs_neg, abs_two]
    have := Complex.abs_re_le_norm w
    rw [hw] at this; linarith
  have hD : ∀ k, 1 ≤ k → k ≤ N → ‖iteratedFDeriv ℝ k h p‖ ≤ (Λ * W) ^ k := by
    intro k hk1 hkN
    have hsplit : h = (fun p => 1 + (-2 * w.re) * σ p) + (fun p => σ p * σ p) := by
      funext q; simp only [hhdef, Pi.add_apply]; ring
    rw [hsplit, iteratedFDeriv_add_apply
      ((contDiff_const.add (contDiff_const.mul hσ)).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hσ.mul hσ).contDiffAt.of_le (by exact_mod_cast le_top))]
    have h1 := norm_iteratedFDeriv_affine hσ 1 (-2 * w.re) (by omega : k ≠ 0) p
    have h2 := norm_iteratedFDeriv_mul_le_of (A := ℝ) hσ hσ p k hW0
      (fun i hi => hσb i (hi.trans hkN)) (fun i hi => hσb i (hi.trans hkN))
    have h2' : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hkN
    calc ‖iteratedFDeriv ℝ k (fun p => 1 + (-2 * w.re) * σ p) p +
          iteratedFDeriv ℝ k (fun p => σ p * σ p) p‖
        ≤ ‖iteratedFDeriv ℝ k (fun p => 1 + (-2 * w.re) * σ p) p‖ +
          ‖iteratedFDeriv ℝ k (fun p => σ p * σ p) p‖ := norm_add_le _ _
      _ ≤ 2 * (Kσ * W ^ k) + 2 ^ N * Kσ * Kσ * W ^ k := by
          rw [h1]
          apply add_le_add
          · exact mul_le_mul hre (hσb k hkN) (norm_nonneg _) zero_le_two
          · refine h2.trans ?_
            gcongr
      _ = Λ * W ^ k := by rw [hΛ]; ring
      _ ≤ Λ ^ k * W ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc Λ = Λ ^ 1 := (pow_one _).symm
            _ ≤ Λ ^ k := pow_le_pow_right₀ hΛ1 hk1
      _ = (Λ * W) ^ k := (mul_pow _ _ _).symm
  set g1 : (Fin d → ℝ) → ℂ := fun p => 1 + (-conj w) * f p with hg1
  have hg1c : ContDiff ℝ ∞ g1 := contDiff_const.add (contDiff_const.mul hf)
  set g2r : (Fin d → ℝ) → ℝ := fun p => cinv b (h p) with hg2r
  have hg2rc : ContDiff ℝ ∞ g2r := (contDiff_cinv hb).comp hh
  set g2 : (Fin d → ℝ) → ℂ := fun p => (g2r p : ℂ) with hg2
  have hg2c : ContDiff ℝ ∞ g2 := Complex.ofRealCLM.contDiff.comp hg2rc
  have hg1b : ∀ k ≤ i, ‖iteratedFDeriv ℝ k g1 p‖ ≤ (1 + Kσ) * W ^ k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
      have hf0 := hfb 0 (Nat.zero_le _)
      rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at hf0
      calc ‖1 + (-conj w) * f p‖ ≤ ‖(1 : ℂ)‖ + ‖-conj w‖ * ‖f p‖ :=
            (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ 1 + 1 * Kσ := by
            rw [norm_one, norm_neg, Complex.norm_conj, hw]; linarith
        _ = 1 + Kσ := by ring
    · rw [hg1, norm_iteratedFDeriv_affineC hf _ _ hk0.ne', norm_neg, Complex.norm_conj, hw,
        one_mul]
      refine (hfb k (hk.trans hi)).trans ?_
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hg2b : ∀ k ≤ i, ‖iteratedFDeriv ℝ k g2 p‖ ≤ (Cf * Λ ^ N) * W ^ k := by
    intro k hk
    rw [hg2, norm_iteratedFDeriv_ofReal hg2rc]
    have := hCf h hh p (Λ * W) (by positivity) hD k (hk.trans hi)
    refine this.trans ?_
    rw [mul_pow, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ1 (hk.trans hi)) hCf0
  have hprod := norm_iteratedFDeriv_mul_le_of hg1c hg2c p i hW0 hg1b hg2b
  have hfun : (fun p => w ^ (N + 1) * ((1 - conj w * f p) *
      ((cinv b (1 + (-2 * w.re) * (f p).re + (f p).re ^ 2) : ℝ) : ℂ))) =
      fun p => 0 + w ^ (N + 1) * (g1 p * g2 p) := by
    funext q; simp only [hg1, hg2, hg2r, hhdef, hσdef]; ring
  rw [hfun]
  have hwN : ‖w ^ (N + 1)‖ = 1 := by rw [norm_pow, hw, one_pow]
  have hcore : ‖iteratedFDeriv ℝ i (fun p => 0 + w ^ (N + 1) * (g1 p * g2 p)) p‖ =
      ‖iteratedFDeriv ℝ i (fun p => g1 p * g2 p) p‖ := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [norm_iteratedFDeriv_zero, zero_add, norm_mul, hwN, one_mul]
    · rw [norm_iteratedFDeriv_affineC (hg1c.mul hg2c) _ _ hi0.ne', hwN, one_mul]
  rw [hcore]
  refine hprod.trans ?_
  have : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hi
  calc 2 ^ i * (1 + Kσ) * (Cf * Λ ^ N) * W ^ i ≤ 2 ^ N * (1 + Kσ) * (Cf * Λ ^ N) * W ^ i := by
        gcongr
    _ = _ := rfl

/-- From `X (1 + y/W)^N ≤ B W^{-d}` with `τ N ≥ (1 + τ) D`: `X ≤ (2^D B + B) (W^{-d} 1(y ≤ W^{1+τ})
+ (y + W)^{-D})`. -/
private theorem split_bound {B W y τ D X : ℝ} {N d : ℕ} (hW : 1 ≤ W) (hy : 0 ≤ y) (hτ : 0 < τ)
    (hD : 0 < D) (hN : (1 + τ) * D ≤ τ * N) (hB : 0 ≤ B) (hX0 : 0 ≤ X)
    (hX : X * (1 + y / W) ^ N ≤ B / W ^ d) :
    X ≤ (2 ^ D * B + B) * ((if y ≤ W ^ (1 + τ) then (W ^ d)⁻¹ else 0) + (y + W) ^ (-D)) := by
  have hW0 : 0 < W := by linarith
  have hyW0 : 0 ≤ y / W := by positivity
  have hwt : 1 ≤ (1 + y / W) ^ N := one_le_pow₀ (by linarith)
  have hXB : X ≤ B / W ^ d := le_trans (le_mul_of_one_le_right hX0 hwt) hX
  have hrp : 0 ≤ (y + W) ^ (-D) := Real.rpow_nonneg (by positivity) _
  have h2D : 0 ≤ (2 : ℝ) ^ D := Real.rpow_nonneg (by norm_num) _
  split_ifs with h
  · have hWd : 0 ≤ (W ^ d)⁻¹ := by positivity
    calc X ≤ B / W ^ d := hXB
      _ = B * (W ^ d)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (2 ^ D * B + B) * ((W ^ d)⁻¹ + (y + W) ^ (-D)) := by
          nlinarith [mul_nonneg h2D hB, mul_nonneg (mul_nonneg h2D hB) hWd,
            mul_nonneg hB hrp, mul_nonneg (mul_nonneg h2D hB) hrp]
  · push Not at h
    have hWτ : W ≤ W ^ (1 + τ) := by
      calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
        _ ≤ W ^ (1 + τ) := Real.rpow_le_rpow_of_exponent_le hW (by linarith)
    have hyW : W < y := lt_of_le_of_lt hWτ h
    have hy0 : 0 < y := by linarith
    have hND : D ≤ N := by nlinarith
    -- the exponent comparison `W^{N-d} ≤ y^{N-D}`
    have key : W ^ ((N : ℝ) - d) ≤ y ^ ((N : ℝ) - D) := by
      calc W ^ ((N : ℝ) - d) ≤ W ^ ((1 + τ) * ((N : ℝ) - D)) := by
            apply Real.rpow_le_rpow_of_exponent_le hW
            have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
            nlinarith
        _ = (W ^ (1 + τ)) ^ ((N : ℝ) - D) := Real.rpow_mul hW0.le _ _
        _ ≤ y ^ ((N : ℝ) - D) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hW0.le _) h.le (by linarith)
    have key2 : W ^ (N : ℝ) * y ^ D ≤ W ^ (d : ℝ) * y ^ (N : ℝ) := by
      have e1 : W ^ (N : ℝ) = W ^ ((N : ℝ) - d) * W ^ (d : ℝ) := by
        rw [← Real.rpow_add hW0]; congr 1; ring
      have e2 : y ^ (N : ℝ) = y ^ ((N : ℝ) - D) * y ^ D := by
        rw [← Real.rpow_add hy0]; congr 1; ring
      rw [e1, e2]
      have : 0 ≤ W ^ (d : ℝ) * y ^ D := by positivity
      nlinarith [mul_le_mul_of_nonneg_right key this]
    have hX2 : X * (y / W) ^ N ≤ B / W ^ d :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hyW0 (by linarith) N) hX0) hX
    rw [Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast] at key2
    have hyD : 0 < y ^ D := Real.rpow_pos_of_pos hy0 D
    -- `X ≤ B y^{-D}`
    have hX3 : X ≤ B * (y ^ D)⁻¹ := by
      rw [div_pow] at hX2
      have hyN : 0 < y ^ N := by positivity
      have hWN : 0 < W ^ N := by positivity
      have hWd : 0 < W ^ d := by positivity
      have h1 : X * y ^ N * W ^ d ≤ B * W ^ N := by
        have := mul_le_mul_of_nonneg_right hX2 (mul_nonneg hWN.le hWd.le)
        field_simp at this
        linarith
      rw [le_mul_inv_iff₀ hyD]
      have h2 : X * y ^ D * W ^ d * y ^ N ≤ B * W ^ d * y ^ N := by
        calc X * y ^ D * W ^ d * y ^ N = (X * y ^ N * W ^ d) * y ^ D := by ring
          _ ≤ (B * W ^ N) * y ^ D := mul_le_mul_of_nonneg_right h1 hyD.le
          _ = B * (W ^ N * y ^ D) := by ring
          _ ≤ B * (W ^ d * y ^ N) := mul_le_mul_of_nonneg_left key2 hB
          _ = B * W ^ d * y ^ N := by ring
      have : 0 < W ^ d * y ^ N := by positivity
      nlinarith
    have hyWD : (y ^ D)⁻¹ ≤ 2 ^ D * (y + W) ^ (-D) := by
      have h1 : (y + W) ^ D ≤ (2 * y) ^ D := Real.rpow_le_rpow (by positivity) (by linarith) hD.le
      rw [Real.mul_rpow (by norm_num) hy0.le] at h1
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos
        (by positivity) D)]
      calc (y ^ D)⁻¹ * (y + W) ^ D ≤ (y ^ D)⁻¹ * (2 ^ D * y ^ D) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 ^ D := by field_simp
    calc X ≤ B * (y ^ D)⁻¹ := hX3
      _ ≤ B * (2 ^ D * (y + W) ^ (-D)) := mul_le_mul_of_nonneg_left hyWD hB
      _ ≤ (2 ^ D * B + B) * (0 + (y + W) ^ (-D)) := by
          rw [zero_add]; nlinarith [mul_nonneg hB hrp]

/-- The weighted bound for `S^+_∞`: `|S^+_∞(x)| (1 + |x|/W)^N ≤ B W^{-d}` for `|E| ≤ 2 - κ`. -/
private theorem splus_weighted (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (c' : ℝ)
    (hψ : SymbolBound ψ c') (C : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ) (N : ℕ) :
    ∃ B W₀ : ℝ, 0 ≤ B ∧ 1 ≤ W₀ ∧ ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ (E : ℝ), |E| ≤ 2 - κ → ∀ x : Fin d → ℤ,
        ‖SplusInf (mE E) s x‖ * (1 + (zdInf x : ℝ) / W) ^ N ≤ B / (W : ℝ) ^ d := by
  set δ : ℝ := Real.sqrt (2 * κ) / 5 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hc' := hψ.pos
  set b : ℝ := min (min 1 (δ ^ 2 / 2)) ((c' / 2) ^ 2) with hb
  have hb0 : 0 < b := lt_min (lt_min one_pos (by positivity)) (by positivity)
  choose K hK using fun i => zdSymbol_smooth d ψ C i
  obtain ⟨K', hK'0, hΨb⟩ := splusPsi_deriv_le (d := d) K hb0 N
  obtain ⟨B, hB0, hBb⟩ := polyRem_kernel_bound ψ C N K'
  obtain ⟨Wg, hWg⟩ := zdSymbol_ge d ψ c' hψ C
  refine ⟨B, max 1 Wg, hB0, le_max_left _ _, ?_⟩
  intro W hW s hs E hE x
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  obtain ⟨hm1, hmδ⟩ := mE_bulk κ hκ E hE
  set w : ℂ := mE E ^ 2 with hwdef
  have hw1 : ‖w‖ = 1 := by rw [hwdef, norm_pow, hm1, one_pow]
  obtain ⟨hcd, hsper, -⟩ := hK 0 W hWn s hs
  have hKb : ∀ i p, ‖iteratedFDeriv ℝ i (zdSymbol s) p‖ ≤ K i * (W : ℝ) ^ i :=
    fun i p => (hK i W hWn s hs).2.2 p
  set Ψ : (Fin d → ℝ) → ℂ := fun p => w ^ (N + 1) * ((1 - conj w * zdSymbol s p) *
    ((cinv b (1 + (-2 * w.re) * (zdSymbol s p).re + (zdSymbol s p).re ^ 2) : ℝ) : ℂ)) with hΨdef
  have hσ : ContDiff ℝ ∞ fun p => (zdSymbol s p).re := Complex.reCLM.contDiff.comp hcd
  have hΨc : ContDiff ℝ ∞ Ψ := contDiff_const.mul ((contDiff_const.sub (contDiff_const.mul hcd)).mul
    (Complex.ofRealCLM.contDiff.comp ((contDiff_cinv hb0).comp
      ((contDiff_const.add (contDiff_const.mul hσ)).add (hσ.pow 2)))))
  have hΨper : ∀ (i : Fin d) (p : Fin d → ℝ), Ψ (p + Pi.single i (2 * Real.pi)) = Ψ p := by
    intro i p; simp only [hΨdef, hsper i p]
  have hΨd := hΨb W w (zdSymbol s) hW1 hw1 hcd hKb
  have hsym : ∀ p ∈ cubePi d, mE E ^ 2 * zdSymbol s p / (1 - mE E ^ 2 * zdSymbol s p) =
      (∑ n ∈ Finset.Ico 1 (N + 1), w ^ n * zdSymbol s p ^ n) + zdSymbol s p ^ (N + 1) * Ψ p := by
    intro p hp
    rw [← hwdef]
    have hge := hWg W (le_trans (le_max_right _ _) hW) s hs p hp
    set σ := (zdSymbol s p).re with hσdef
    have hse : zdSymbol s p = (σ : ℂ) := Complex.ext (by simp [hσdef]) (by simp [hs.im_eq p])
    have hq := q_lower hw1 (by positivity) hmδ hc' hge
    rw [← hb] at hq
    have hq0 : 0 < 1 - 2 * w.re * σ + σ ^ 2 := lt_of_lt_of_le hb0 hq
    have hqq : 1 + (-2 * w.re) * σ + σ ^ 2 = 1 - 2 * w.re * σ + σ ^ 2 := by ring
    simp only [hΨdef]
    rw [← hσdef, hqq, cinv_eq hb0 hq, hse]
    have hprod := one_sub_mul_conj hw1 σ
    have hne : ((1 - 2 * w.re * σ + σ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    have h1 : (1 : ℂ) - w * σ ≠ 0 := fun h0 => hne (by rw [← hprod, h0, zero_mul])
    have h2 : (1 : ℂ) - conj w * σ ≠ 0 := fun h0 => hne (by rw [← hprod, h0, mul_zero])
    have hz : w * (σ : ℂ) ≠ 1 := fun h0 => h1 (by rw [h0, sub_self])
    rw [geom_identity _ hz N]
    congr 1
    · exact Finset.sum_congr rfl fun n _ => mul_pow _ _ _
    · have h2' : (1 : ℂ) - (σ : ℂ) * conj w ≠ 0 := by rw [mul_comm]; exact h2
      rw [Complex.ofReal_inv, ← hprod, mul_pow]
      field_simp
  have hS : SplusInf (mE E) s x = latticeFourier (fun p => mE E ^ 2 * zdSymbol s p /
      (1 - mE E ^ 2 * zdSymbol s p)) x := rfl
  rw [hS, latticeFourier_congr hsym x]
  exact hBb W s Ψ w hWn hs hw1.le hΨc hΨper hΨd x

/-- [I, Lemma 7.2], existence of `S^±_∞` and (7.6): for `|E| ≤ 2 - κ` and `W ≥ W₀`,
`|(S^±_∞)_{0x}(E)| ≤ K (W^{-d} 1(|x| ≤ W^{1+τ}) + (|x| + W)^{-D})`. -/
theorem SplusInf_decay :
  ∀ (d : ℕ) (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (c' : ℝ) (hψ : SymbolBound ψ c')
    (C : ℕ → ℝ) (κ τ D : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) (hD : 0 < D),
    ∃ K W₀ : ℝ, ∀ (W : ℕ), W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ (E : ℝ), |E| ≤ 2 - κ → ∀ x : Fin d → ℤ,
        ‖SplusInf (mE E) s x‖ ≤
            K * ((if (zdInf x : ℝ) ≤ (W : ℝ) ^ (1 + τ) then ((W : ℝ) ^ d)⁻¹ else 0) +
              ((zdInf x : ℝ) + W) ^ (-D)) ∧
          ‖SminusInf (mE E) s x‖ ≤
            K * ((if (zdInf x : ℝ) ≤ (W : ℝ) ^ (1 + τ) then ((W : ℝ) ^ d)⁻¹ else 0) +
              ((zdInf x : ℝ) + W) ^ (-D)) := by
  intro d ψ c' hψ C κ τ D hκ hτ hD
  set N : ℕ := ⌈(1 + τ) * D / τ⌉₊ with hNdef
  have hN : (1 + τ) * D ≤ τ * N := by
    have := Nat.le_ceil ((1 + τ) * D / τ)
    rw [← hNdef, div_le_iff₀ hτ] at this
    linarith
  obtain ⟨B, W₀, hB0, hW₀1, hB⟩ := splus_weighted d ψ c' hψ C κ hκ N
  refine ⟨2 ^ D * B + B, W₀, ?_⟩
  intro W hW s hs E hE x
  have hW1 : (1 : ℝ) ≤ W := hW₀1.trans hW
  have h := split_bound hW1 (Nat.cast_nonneg _) hτ hD hN hB0 (norm_nonneg _)
    (hB W hW s hs E hE x)
  refine ⟨h, ?_⟩
  have hc : ‖SminusInf (mE E) s x‖ = ‖SplusInf (mE E) s x‖ := Complex.norm_conj _
  rw [hc]
  exact h

end Splus

section Witness

end Witness

end RBM8D
