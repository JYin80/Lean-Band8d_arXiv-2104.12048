module

public import RBM8D.TExp.Defs
public import RBM8D.Kernel.ThetaDecay
public import RBM8D.Kernel.ZdCancel
public import RBM8D.Profile.Symbol
public import RBM8D.Input.Entry
public import RBM8D.Input.Sizes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# The weak and strong norms and the bound `B`

The weak and strong `(a, b)` norms of [I, Def 6.8] = [II, Def 8.2], their elementary properties
[I, (6.11)–(6.13)] = [II, (8.6)–(8.8)], the comparison of the two norms, and the sums of `B` used in
[II, (8.33)].
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

section Norms

variable (d L W : ℕ) [NeZero L]

/-- `⟨x - y⟩ = ‖x - y‖_L + W`, with the periodic `ℓ^∞` distance. -/
def brk (x y : Zd d L) : ℝ := (zdistInf d L (x - y) : ℝ) + W

/-- The weak-`(a, b)` norm of [I, Def 6.8] = [II, Def 8.2]:
`W^{ad/2} max |A_{xy}| + sup_{K ∈ [W, L/2]} (W/K)^b K^{ad/2} max_{x, x₀} K^{-d}
Σ_{|y - x₀| ≤ K} (|A_{xy}| + |A_{yx}|)`, the supremum over integers `K`. -/
def weakNorm (a b : ℝ) (A : Matrix (Zd d L) (Zd d L) ℝ) : ℝ :=
  (W : ℝ) ^ (a * d / 2) * (⨆ x, ⨆ y, |A x y|) +
    ⨆ K : {K : ℕ // W ≤ K ∧ 2 * K ≤ L}, ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) *
      ⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d

/-- The strong-`(a, b)` norm of [I, Def 6.8] = [II, Def 8.2]:
`max_{x, y} (W/⟨x - y⟩)^b ⟨x - y⟩^{ad/2} |A_{xy}|`. -/
def strongNorm (a b : ℝ) (A : Matrix (Zd d L) (Zd d L) ℝ) : ℝ :=
  ⨆ x, ⨆ y, ((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) * |A x y|

/-- `Γ(y₁, …, y_k) = Σ_i Π_{j ≠ i} B_{y_i y_j}` of [I, (6.34)] = [II, (8.13)]. -/
def gammaB {k : ℕ} (y : Fin k → Zd d L) : ℝ :=
  ∑ i, ∏ j ∈ Finset.univ.erase i, bB d L W (y i) (y j)

/-- The dyadic factor `log₂(L/W) + 2`. -/
def logF : ℝ := Real.logb 2 ((L : ℝ) / W) + 2

end Norms

/-- The ball `{y : ‖y - x₀‖_L ≤ ρ}` of `Z_L^d` has at most `(2ρ + 1)^d` points. -/
private theorem Norm_card_ball (d L : ℕ) [NeZero L] (x₀ : Zd d L) (ρ : ℕ) :
    (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ ρ)).card ≤ (2 * ρ + 1) ^ d := by
  have h : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(ρ : ℤ)) ρ).card = (2 * ρ + 1) ^ d := by
    rw [Fintype.card_piFinset]
    simp [Int.card_Icc]
    congr 1; omega
  rw [← h]
  refine Finset.card_le_card_of_injOn (fun y i => (y - x₀) i |>.valMinAbs) ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := zdist_le_zdistInf d L (y - x₀) i
    rw [zdist_eq_natAbs_valMinAbs] at h1
    omega
  · intro y _ z _ hyz
    have : y - x₀ = z - x₀ := funext fun i => ZMod.valMinAbs_inj.1 (congrFun hyz i)
    exact sub_left_injective this


/-- `⟨x - y⟩ = ⟨y - x⟩`. -/
private theorem Norm_brk_comm (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    brk d L W x y = brk d L W y x := by
  unfold brk
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- Dyadic decomposition: if `f` is nonnegative and nonincreasing on `[M, ∞)`, `M ≥ 1/2`, then `Σ
f(⟨y - x⟩)` over the points with `M ≤ ⟨y - x⟩ < 2^N M` is at most `Σ_{j < N} (3 · 2^{j+1} M)^d
f(2^j M)`. -/
private theorem Norm_levels (d L W : ℕ) [NeZero L] (x : Zd d L) (M : ℝ)
    (hM : 1 ≤ 2 * M) (f : ℝ → ℝ) (hf0 : ∀ t, M ≤ t → 0 ≤ f t)
    (hf : ∀ s t, M ≤ s → s ≤ t → f t ≤ f s) (N : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧ brk d L W y x < 2 ^ N * M),
        f (brk d L W y x) ≤
      ∑ j ∈ Finset.range N, (3 * 2 ^ (j + 1) * M) ^ d * f (2 ^ j * M) := by
  have hM0 : 0 < M := by linarith
  induction N with
  | zero =>
    have : Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧ brk d L W y x < 2 ^ 0 * M)
        = ∅ := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, pow_zero, one_mul]; intro h; linarith [h.1, h.2]
    rw [this]; simp
  | succ N ih =>
    have hpos : (0 : ℝ) < 2 ^ N * M := by positivity
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun y : Zd d L => brk d L W y x < 2 ^ N * M),
      Finset.sum_range_succ]
    have h1 : (Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧
        brk d L W y x < 2 ^ (N + 1) * M)).filter (fun y => brk d L W y x < 2 ^ N * M) =
        Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧ brk d L W y x < 2 ^ N * M) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        rw [pow_succ]; nlinarith
    rw [h1]
    refine add_le_add ih ?_
    set S := (Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧
        brk d L W y x < 2 ^ (N + 1) * M)).filter (fun y => ¬ brk d L W y x < 2 ^ N * M) with hS
    have hbound : ∀ y ∈ S, f (brk d L W y x) ≤ f (2 ^ N * M) := by
      intro y hy
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hy
      have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      exact hf _ _ (by nlinarith) hy.2
    have hcard : (S.card : ℝ) ≤ (3 * 2 ^ (N + 1) * M) ^ d := by
      set ρ := ⌊(2 : ℝ) ^ (N + 1) * M⌋₊ with hρ
      have hsub : S ⊆ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x) ≤ ρ) := by
        intro y hy
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        apply Nat.le_floor
        have := hy.1.2
        unfold brk at this
        have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
        linarith
      have h2 := (Finset.card_le_card hsub).trans (Norm_card_ball d L x ρ)
      have h3 : ((2 * ρ + 1 : ℕ) : ℝ) ≤ 3 * 2 ^ (N + 1) * M := by
        have h4 : (ρ : ℝ) ≤ 2 ^ (N + 1) * M := Nat.floor_le (by positivity)
        have h5 : (1 : ℝ) ≤ 2 ^ (N + 1) * M := by
          have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
          rw [pow_succ]; nlinarith
        push_cast; linarith
      calc (S.card : ℝ) ≤ ((2 * ρ + 1 : ℕ) ^ d : ℕ) := by exact_mod_cast h2
        _ = ((2 * ρ + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) h3 d
    calc ∑ y ∈ S, f (brk d L W y x) ≤ S.card • f (2 ^ N * M) :=
          Finset.sum_le_card_nsmul _ _ _ hbound
      _ = (S.card : ℝ) * f (2 ^ N * M) := by rw [nsmul_eq_mul]
      _ ≤ (3 * 2 ^ (N + 1) * M) ^ d * f (2 ^ N * M) :=
          mul_le_mul_of_nonneg_right hcard (hf0 _ (by
            have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
            nlinarith))


/-- The dyadic sum of `⟨y - x⟩^{-p}`, `p ≥ 0`, over `M ≤ ⟨y - x⟩ < 2^N M` is at most `6^d M^{d-p}
Σ_{j < N} (2^{d-p})^j`. -/
private theorem Norm_powLevels (d L W : ℕ) [NeZero L] (x : Zd d L) (M p : ℝ) (hM : 1 ≤ 2 * M)
    (hp : 0 ≤ p) (N : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧ brk d L W y x < 2 ^ N * M),
        brk d L W y x ^ (-p) ≤
      6 ^ d * M ^ ((d : ℝ) - p) * ∑ j ∈ Finset.range N, ((2 : ℝ) ^ ((d : ℝ) - p)) ^ j := by
  have hM0 : 0 < M := by linarith
  refine (Norm_levels d L W x M hM (fun t => t ^ (-p)) (fun t ht => ?_) (fun s t hs hst => ?_) N).trans
    (le_of_eq ?_)
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.rpow_le_rpow_of_nonpos (by linarith) hst (by linarith)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (3 * 2 ^ (j + 1) * M : ℝ) = (6 * M) * 2 ^ j := by ring
    have h2 : ((2 : ℝ) ^ j * M) ^ (-p) = ((2 : ℝ) ^ (-p)) ^ j * M ^ (-p) := by
      rw [Real.mul_rpow (by positivity) hM0.le, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm, mul_comm (j : ℝ)]
      ring
    have h3 : ((2 : ℝ) ^ ((d : ℝ) - p)) = (2 : ℝ) ^ d * (2 : ℝ) ^ (-p) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_natCast]
    have h4 : M ^ ((d : ℝ) - p) = M ^ d * M ^ (-p) := by
      rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_natCast]
    have h5 : ((2 : ℝ) ^ j) ^ d = ((2 : ℝ) ^ d) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h1, h2, h3, h4]
    simp only [mul_pow]
    rw [h5]
    ring


/-- For `0 ≤ s < d`, `Σ_{‖y - x‖_L ≤ K} ⟨y - x⟩^{-s} ≤ C (K + W)^{d - s}` with `C` depending on
`d, s` only, for `W ≥ 1`. -/
private theorem Norm_ballSum (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (x : Zd d L) (K : ℕ),
      ∑ y ∈ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x) ≤ K),
          brk d L W y x ^ (-s) ≤ C * ((K : ℝ) + W) ^ ((d : ℝ) - s) := by
  set σ : ℝ := (d : ℝ) - s with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  set ρ : ℝ := (2 : ℝ) ^ σ with hρ
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by norm_num) hσ0
  refine ⟨6 ^ d * 2 ^ σ / (ρ - 1), by have : 0 < ρ - 1 := by linarith
                                      positivity, fun L W _ hW x K => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hex : ∃ N : ℕ, K + W < 2 ^ N * W := ⟨K + W, by
    have := Nat.lt_two_pow_self (n := K + W)
    nlinarith⟩
  classical
  set N := Nat.find hex with hN
  have hspec : K + W < 2 ^ N * W := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h; rw [h] at hspec; omega
  obtain ⟨N', hN'⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hmin : ¬ K + W < 2 ^ N' * W := Nat.find_min hex (by omega)
  have hle : (2 : ℝ) ^ N * W ≤ 2 * ((K : ℝ) + W) := by
    have : 2 ^ N' * W ≤ K + W := by omega
    have h2 : ((2 ^ N' * W : ℕ) : ℝ) ≤ ((K + W : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    rw [hN', pow_succ]; nlinarith
  have hspecR : (K : ℝ) + W < 2 ^ N * W := by exact_mod_cast hspec
  have hsub : Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x) ≤ K) ⊆
      Finset.univ.filter (fun y : Zd d L => (W : ℝ) ≤ brk d L W y x ∧
        brk d L W y x < 2 ^ N * W) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have h1 : (zdistInf d L (y - x) : ℝ) ≤ K := by exact_mod_cast hy
    have h0 : (0 : ℝ) ≤ zdistInf d L (y - x) := Nat.cast_nonneg _
    unfold brk
    constructor <;> linarith
  have h1 := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ =>
    Real.rpow_nonneg (by unfold brk; positivity) _)).trans
    (Norm_powLevels d L W x W s (by linarith) hs0 N)
  have hgeom : ∑ j ∈ Finset.range N, ((2 : ℝ) ^ ((d : ℝ) - s)) ^ j ≤ ρ ^ N / (ρ - 1) := by
    rw [← hσ, ← hρ, geom_sum_eq hρ1.ne']
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hρN : ρ ^ N = ((2 : ℝ) ^ N) ^ σ := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hWσ : (W : ℝ) ^ σ * ((2 : ℝ) ^ N) ^ σ ≤ 2 ^ σ * ((K : ℝ) + W) ^ σ := by
    rw [← Real.mul_rpow hW0.le (by positivity), ← Real.mul_rpow (by norm_num) (by positivity),
      mul_comm (W : ℝ)]
    exact Real.rpow_le_rpow (by positivity) hle hσ0.le
  calc _ ≤ 6 ^ d * (W : ℝ) ^ σ * ∑ j ∈ Finset.range N, ρ ^ j := h1
    _ ≤ 6 ^ d * (W : ℝ) ^ σ * (ρ ^ N / (ρ - 1)) := by
        gcongr
    _ = 6 ^ d * ((W : ℝ) ^ σ * ((2 : ℝ) ^ N) ^ σ) / (ρ - 1) := by
        rw [hρN]; ring
    _ ≤ 6 ^ d * (2 ^ σ * ((K : ℝ) + W) ^ σ) / (ρ - 1) := by
        gcongr
    _ = _ := by ring


/-- For `q > d`, `Σ_{⟨y - x⟩ ≥ M} ⟨y - x⟩^{-q} ≤ C M^{d - q}` with `C` depending on `d, q` only,
for `W ≥ 1` and `M ≥ 1/2`. -/
private theorem Norm_tailSum (d : ℕ) (q : ℝ) (hq : (d : ℝ) < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (x : Zd d L) (M : ℝ), 1 ≤ 2 * M →
      ∑ y ∈ Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x), brk d L W y x ^ (-q) ≤
        C * M ^ ((d : ℝ) - q) := by
  set ρ : ℝ := (2 : ℝ) ^ ((d : ℝ) - q) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨6 ^ d / (1 - ρ), by have : 0 < 1 - ρ := by linarith
                              positivity, fun L W _ hW x M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (((L : ℝ) + W) / M) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hM0] at hN
  have hsub : Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x) ⊆
      Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧ brk d L W y x < 2 ^ N * M) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨hy, lt_of_le_of_lt ?_ hN⟩
    unfold brk
    have h1 : zdistInf d L (y - x) ≤ L / 2 := zdistInf_le_half d L _
    have h2 : (zdistInf d L (y - x) : ℝ) ≤ L := by
      exact_mod_cast h1.trans (Nat.div_le_self _ _)
    linarith
  have h1 := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ =>
    Real.rpow_nonneg (by unfold brk; positivity) _)).trans
    (Norm_powLevels d L W x M q hM (by linarith) N)
  have hgeom : ∑ j ∈ Finset.range N, ρ ^ j ≤ 1 / (1 - ρ) := by
    rw [geom_sum_eq hρ1.ne]
    have : 0 ≤ ρ ^ N := by positivity
    have e : (ρ ^ N - 1) / (ρ - 1) = (1 - ρ ^ N) / (1 - ρ) := by
      have h1 : 1 - ρ ≠ 0 := by linarith
      have h2 : ρ - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc _ ≤ 6 ^ d * M ^ ((d : ℝ) - q) * ∑ j ∈ Finset.range N, ρ ^ j := h1
    _ ≤ 6 ^ d * M ^ ((d : ℝ) - q) * (1 / (1 - ρ)) := by gcongr
    _ = _ := by ring

/-- A term of a double supremum over finite index types is at most the supremum. -/
private theorem Norm_le_iSup₂ {ι κ : Type*} [Finite ι] [Finite κ] (f : ι → κ → ℝ) (i : ι) (j : κ) :
    f i j ≤ ⨆ i, ⨆ j, f i j :=
  (le_ciSup (Set.finite_range (f i)).bddAbove j).trans
    (le_ciSup (Set.finite_range fun i => ⨆ j, f i j).bddAbove i)

/-- `(W/t)^b t^c = W^b t^{c-b}` for `W, t > 0`. -/
private theorem Norm_coef_eq {W t : ℝ} (hW : 0 < W) (ht : 0 < t) (b c : ℝ) :
    (W / t) ^ b * t ^ c = W ^ b * t ^ (c - b) := by
  rw [Real.div_rpow hW.le ht.le, Real.rpow_sub ht, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The coefficient `(W/t)^b t^c` is positive, with inverse `W^{-b} t^{-(c-b)}`. -/
private theorem Norm_coef {W t : ℝ} (hW : 0 < W) (ht : 0 < t) (b c : ℝ) :
    0 < (W / t) ^ b * t ^ c ∧
      ((W / t) ^ b * t ^ c)⁻¹ = W ^ (-b) * t ^ (-(c - b)) := by
  have h1 := Norm_coef_eq hW ht b c
  refine ⟨by positivity, ?_⟩
  rw [h1, mul_inv, ← Real.rpow_neg hW.le, ← Real.rpow_neg ht.le]

/-- The first term of `weakNorm` is at most `weakNorm`. -/
private theorem Norm_weak_first_le (d L W : ℕ) [NeZero L] (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ) :
    (W : ℝ) ^ (a * d / 2) * (⨆ x, ⨆ y, |A x y|) ≤ weakNorm d L W a b A := by
  unfold weakNorm
  refine le_add_of_nonneg_right (Real.iSup_nonneg fun K => mul_nonneg (by positivity)
    (Real.iSup_nonneg fun x => Real.iSup_nonneg fun x₀ => by positivity))

/-- The term of `weakNorm` at an integer `K ∈ [W, L/2]` is at most `weakNorm`. -/
private theorem Norm_weak_K_le (d L W : ℕ) [NeZero L] (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ) (K : ℕ) (hK1 : W ≤ K) (hK2 : 2 * K ≤ L) :
    ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) *
      (⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d) ≤ weakNorm d L W a b A := by
  unfold weakNorm
  have hfin : Finite {K : ℕ // W ≤ K ∧ 2 * K ≤ L} :=
    Finite.of_injective (fun K => (⟨K.1, by have := K.2.2; omega⟩ : Fin (L + 1)))
      (fun p q h => Subtype.ext (by simpa using h))
  have hnn : 0 ≤ (W : ℝ) ^ (a * d / 2) * (⨆ x, ⨆ y, |A x y|) :=
    mul_nonneg (by positivity) (Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => abs_nonneg _)
  refine le_add_of_nonneg_of_le hnn ?_
  exact le_ciSup (f := fun K : {K : ℕ // W ≤ K ∧ 2 * K ≤ L} => ((W : ℝ) / K) ^ b *
    (K : ℝ) ^ (a * d / 2) * ⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d) (Set.finite_range _).bddAbove ⟨K, hK1, hK2⟩

/-- Each term of `strongNorm` is at most `strongNorm`. -/
private theorem Norm_strong_le (d L W : ℕ) [NeZero L] (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) :
    ((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) * |A x y| ≤
      strongNorm d L W a b A :=
  Norm_le_iSup₂ (fun x y => ((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) *
    |A x y|) x y

/-- `strongNorm` is nonnegative. -/
private theorem Norm_strong_nonneg (d L W : ℕ) [NeZero L] (a b : ℝ)
    (A : Matrix (Zd d L) (Zd d L) ℝ) : 0 ≤ strongNorm d L W a b A :=
  Real.iSup_nonneg fun x => Real.iSup_nonneg fun y => by unfold brk; positivity

/-- For `0 ≤ s < d` and integers `K ≥ W ≥ 1`, `Σ_{‖y - x₀‖_L ≤ K} ⟨y - x⟩^{-s} ≤ C K^{d - s}` with
`C` depending on `d, s` only. -/
private theorem Norm_ballSum2 (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (x x₀ : Zd d L) (K : ℕ), W ≤ K →
      ∑ y ∈ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K),
          brk d L W y x ^ (-s) ≤ C * (K : ℝ) ^ ((d : ℝ) - s) := by
  obtain ⟨C₀, hC₀, hb⟩ := Norm_ballSum d s hs0 hsd
  refine ⟨C₀ * 2 ^ ((d : ℝ) - s) + 3 ^ d, by positivity, fun L W _ hW x x₀ K hK => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hW.trans hK
  have hKW : (W : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hσ : 0 ≤ (d : ℝ) - s := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K))
    (fun y : Zd d L => zdistInf d L (y - x) ≤ K)]
  have hnn : ∀ y : Zd d L, 0 ≤ brk d L W y x ^ (-s) := fun y =>
    Real.rpow_nonneg (by unfold brk; positivity) _
  have p1 : ∑ y ∈ (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K)).filter
      (fun y => zdistInf d L (y - x) ≤ K), brk d L W y x ^ (-s) ≤
      C₀ * 2 ^ ((d : ℝ) - s) * (K : ℝ) ^ ((d : ℝ) - s) := by
    have hsub : (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K)).filter
        (fun y => zdistInf d L (y - x) ≤ K) ⊆
        Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x) ≤ K) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy.2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hnn y)).trans
      ((hb L W hW x K).trans ?_)
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hK0.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hσ) hC₀
    linarith
  have p2 : ∑ y ∈ (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K)).filter
      (fun y => ¬ zdistInf d L (y - x) ≤ K), brk d L W y x ^ (-s) ≤
      3 ^ d * (K : ℝ) ^ ((d : ℝ) - s) := by
    set T := (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K)).filter
      (fun y => ¬ zdistInf d L (y - x) ≤ K) with hT
    have hterm : ∀ y ∈ T, brk d L W y x ^ (-s) ≤ (K : ℝ) ^ (-s) := by
      intro y hy
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy
      have h1 : (K : ℝ) + 1 ≤ zdistInf d L (y - x) := by exact_mod_cast hy.2
      refine Real.rpow_le_rpow_of_nonpos hK0 ?_ (by linarith)
      unfold brk
      linarith
    have hcard : (T.card : ℝ) ≤ (3 * K) ^ d := by
      have hsubT : T ⊆ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ K) :=
        Finset.filter_subset _ _
      have h2 := (Finset.card_le_card hsubT).trans (Norm_card_ball d L x₀ K)
      calc (T.card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast h2
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by push_cast; linarith) d
    calc ∑ y ∈ T, brk d L W y x ^ (-s) ≤ T.card • (K : ℝ) ^ (-s) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (T.card : ℝ) * (K : ℝ) ^ (-s) := by rw [nsmul_eq_mul]
      _ ≤ (3 * K) ^ d * (K : ℝ) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hK0.le _)
      _ = _ := by
          rw [mul_pow, mul_assoc, sub_eq_add_neg, Real.rpow_add hK0, Real.rpow_natCast]
  linarith

/-- `‖x - y‖_L = ‖y - x‖_L`. -/
private theorem Norm_zdistInf_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- `B_{xy} = W^{-2} ⟨x - y⟩^{-(d-2)}`. -/
private theorem Norm_bB_eq (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl

/-- `B_{xy} = B_{yx}`. -/
private theorem Norm_bB_comm (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    bB d L W x y = bB d L W y x := by
  rw [Norm_bB_eq, Norm_bB_eq, Norm_brk_comm]

/-- `B_{xy} ≥ 0`. -/
private theorem Norm_bB_nonneg (d L W : ℕ) [NeZero L] (x y : Zd d L) : 0 ≤ bB d L W x y := by
  rw [Norm_bB_eq]; unfold brk; positivity

/-- `⟨x - y⟩ > 0` for `W ≥ 1`. -/
private theorem Norm_brk_pos (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    0 < brk d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold brk; positivity

/-- `W ≤ ⟨x - y⟩`. -/
private theorem Norm_le_brk (d L W : ℕ) [NeZero L] (x y : Zd d L) : (W : ℝ) ≤ brk d L W x y := by
  unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]

/-- `⟨p - q⟩ + W ≤ ⟨y - p⟩ + ⟨y - q⟩`. -/
private theorem Norm_brk_tri (d L W : ℕ) [NeZero L] (y p q : Zd d L) :
    brk d L W p q + W ≤ brk d L W y p + brk d L W y q := by
  have h1 : zdistInf d L (p - q) ≤ zdistInf d L (p - y) + zdistInf d L (y - q) := by
    have := zdistInf_add_le d L (p - y) (y - q)
    rwa [sub_add_sub_cancel] at this
  rw [Norm_zdistInf_comm d L p y] at h1
  have h2 : (zdistInf d L (p - q) : ℝ) ≤ zdistInf d L (y - p) + zdistInf d L (y - q) := by
    exact_mod_cast h1
  unfold brk
  rw [Norm_zdistInf_comm d L p q] at h2 ⊢
  linarith [h2]

/-- `B_{xy}² = W^{-4} ⟨x - y⟩^{-(2d-4)}`. -/
private theorem Norm_bB_sq (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ^ 2 = (W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-(2 * (d : ℝ) - 4)) := by
  have hW0 : (0 : ℝ) < W := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW
                               linarith
  have ht := Norm_brk_pos d L W hW x y
  rw [Norm_bB_eq, mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-2 : ℝ)),
    ← Real.rpow_natCast (brk d L W x y ^ (2 - (d : ℝ))), ← Real.rpow_mul hW0.le,
    ← Real.rpow_mul ht.le]
  congr 2 <;> push_cast <;> ring

/-- For `d ≥ 2`, `Σ B_{yp} B_{yq} ≤ C W^{-4} ⟨p - q⟩^{-(d-4)}`, summed over the points `y` with
`⟨y - p⟩ < ⟨p - q⟩ / 2`. -/
private theorem Norm_region1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ p q : Zd d L,
      ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y p < brk d L W p q / 2),
          bB d L W y p * bB d L W y q ≤
        C * (W : ℝ) ^ (-4 : ℝ) * brk d L W p q ^ (-((d : ℝ) - 4)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₀, hC₀, hb⟩ := Norm_ballSum d ((d : ℝ) - 2) (by linarith) (by linarith)
  refine ⟨C₀ * ((2 : ℝ)⁻¹) ^ (2 - (d : ℝ)), by positivity, fun L W _ hW p q => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set K := zdistInf d L (p - q) with hK
  set D := brk d L W p q with hD
  have hDK : D = (K : ℝ) + W := rfl
  have hD0 : 0 < D := Norm_brk_pos d L W hW p q
  set F := Finset.univ.filter (fun y : Zd d L => brk d L W y p < D / 2) with hF
  have hv : ∀ y ∈ F, bB d L W y q ≤ (W : ℝ) ^ (-2 : ℝ) * (D / 2) ^ (2 - (d : ℝ)) := by
    intro y hy
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have h1 := Norm_brk_tri d L W y p q
    rw [Norm_bB_eq]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
      (by positivity)
    linarith
  have hsubF : F ⊆ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - p) ≤ K) := by
    intro y hy
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have h1 : (zdistInf d L (y - p) : ℝ) < K := by
      unfold brk at hy
      rw [hDK] at hy
      have : (0 : ℝ) ≤ zdistInf d L (y - p) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith
    exact_mod_cast h1.le
  have hsumB : ∑ y ∈ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - p) ≤ K),
      bB d L W y p ≤ (W : ℝ) ^ (-2 : ℝ) * (C₀ * D ^ (2 : ℝ)) := by
    have e : ∑ y ∈ Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - p) ≤ K),
        bB d L W y p = (W : ℝ) ^ (-2 : ℝ) * ∑ y ∈ Finset.univ.filter
          (fun y : Zd d L => zdistInf d L (y - p) ≤ K), brk d L W y p ^ (-((d : ℝ) - 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Norm_bB_eq]; congr 2; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ((hb L W hW p K).trans ?_) (by positivity)
    rw [show (d : ℝ) - ((d : ℝ) - 2) = 2 by ring, hDK]
  calc ∑ y ∈ F, bB d L W y p * bB d L W y q
      ≤ ∑ y ∈ F, bB d L W y p * ((W : ℝ) ^ (-2 : ℝ) * (D / 2) ^ (2 - (d : ℝ))) :=
        Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hv y hy) (Norm_bB_nonneg _ _ _ _ _)
    _ = (∑ y ∈ F, bB d L W y p) * ((W : ℝ) ^ (-2 : ℝ) * (D / 2) ^ (2 - (d : ℝ))) := by
        rw [Finset.sum_mul]
    _ ≤ ((W : ℝ) ^ (-2 : ℝ) * (C₀ * D ^ (2 : ℝ))) *
          ((W : ℝ) ^ (-2 : ℝ) * (D / 2) ^ (2 - (d : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ((Finset.sum_le_sum_of_subset_of_nonneg hsubF
          (fun y _ _ => Norm_bB_nonneg _ _ _ _ _)).trans hsumB) (by positivity)
    _ = _ := by
        have e1 : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ) = (W : ℝ) ^ (-4 : ℝ) := by
          rw [← Real.rpow_add hW0]; norm_num
        have e2 : D ^ (2 : ℝ) * (D ^ (2 - (d : ℝ))) = D ^ (-((d : ℝ) - 4)) := by
          rw [← Real.rpow_add hD0]; congr 1; ring
        have e3 : (D / 2) ^ (2 - (d : ℝ)) = D ^ (2 - (d : ℝ)) * ((2 : ℝ)⁻¹) ^ (2 - (d : ℝ)) := by
          rw [div_eq_mul_inv, Real.mul_rpow hD0.le (by norm_num)]
        rw [e3]
        calc _ = ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ)) * (D ^ (2 : ℝ) * (D ^ (2 - (d : ℝ)))) *
              (C₀ * ((2 : ℝ)⁻¹) ^ (2 - (d : ℝ))) := by ring
          _ = _ := by rw [e1, e2]; ring


/-- [I, (6.11)–(6.13)] = [II, (8.6)–(8.8)]: for `W ≥ 1`, `|A_{xy}| ≤ W^{-ad/2} ‖A‖_{w;(a,b)}`;
the ball averages `K^{-d} Σ_{|y - x₀| ≤ K} (|A_{xy}| + |A_{yx}|) ≤ W^{-b} K^{-(ad/2 - b)}
‖A‖_{w;(a,b)}` for integers `K ∈ [W, L/2]`; `|A_{xy}| ≤ W^{-b} ⟨x - y⟩^{-(ad/2 - b)}
‖A‖_{s;(a,b)}`. -/
theorem normBasic :
  ∀ (d L W : ℕ) [NeZero L], 1 ≤ W → ∀ (a b : ℝ) (A : Matrix (Zd d L) (Zd d L) ℝ),
    (∀ x y, |A x y| ≤ (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b A) ∧
    (∀ K : ℕ, W ≤ K → 2 * K ≤ L → ∀ x x₀ : Zd d L,
      (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d ≤
        (W : ℝ) ^ (-b) * (K : ℝ) ^ (-(a * d / 2 - b)) * weakNorm d L W a b A) ∧
    (∀ x y, |A x y| ≤
      (W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b)) * strongNorm d L W a b A) := by
  intro d L W _ hW a b A
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  refine ⟨fun x y => ?_, fun K hK1 hK2 x x₀ => ?_, fun x y => ?_⟩
  · have h1 := Norm_weak_first_le d L W a b A
    have h2 : |A x y| ≤ ⨆ x, ⨆ y, |A x y| := Norm_le_iSup₂ (fun x y => |A x y|) x y
    have h3 : (W : ℝ) ^ (a * d / 2) * |A x y| ≤ weakNorm d L W a b A :=
      (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h1
    rw [Real.rpow_neg hW0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  · have hK0 : (0 : ℝ) < K := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hW.trans hK1
      linarith
    obtain ⟨hc, hci⟩ := Norm_coef hW0 hK0 b (a * d / 2)
    have h1 := Norm_weak_K_le d L W a b A K hK1 hK2
    have h2 : (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K),
          (|A x y| + |A y x|)) / (K : ℝ) ^ d ≤
        ⨆ x, ⨆ x₀ : Zd d L, (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K),
          (|A x y| + |A y x|)) / (K : ℝ) ^ d :=
      Norm_le_iSup₂ (fun x x₀ : Zd d L => (∑ y ∈ Finset.univ.filter
        (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) / (K : ℝ) ^ d) x x₀
    have h4 := (le_inv_mul_iff₀ hc).2 h1
    rw [hci] at h4
    exact h2.trans h4
  · have ht : 0 < brk d L W x y := by unfold brk; positivity
    obtain ⟨hc, hci⟩ := Norm_coef hW0 ht b (a * d / 2)
    have h1 := Norm_strong_le d L W a b A x y
    have h3 := (le_inv_mul_iff₀ hc).2 h1
    rw [hci] at h3
    exact h3

/-- `‖B‖_{s;(2,2)} = 1` and `‖B^{1/2}‖_{s;(1,1)} = 1` ([I, §6.4], [II, §8.1]), for `W ≥ 1`. -/
theorem bB_strongNorm :
  ∀ (d L W : ℕ) [NeZero L], 1 ≤ W →
    strongNorm d L W 2 2 (fun x y => bB d L W x y) = 1 ∧
      strongNorm d L W 1 1 (fun x y => Real.sqrt (bB d L W x y)) = 1 := by
  intro d L W _ hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have ht : ∀ x y : Zd d L, 0 < brk d L W x y := fun x y => by unfold brk; positivity
  have hB : ∀ x y : Zd d L, bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) :=
    fun x y => rfl
  constructor
  · have key : ∀ x y : Zd d L, ((W : ℝ) / brk d L W x y) ^ (2 : ℝ) *
        brk d L W x y ^ ((2 : ℝ) * d / 2) * |bB d L W x y| = 1 := by
      intro x y
      have htx := ht x y
      have h0 : 0 ≤ bB d L W x y := by rw [hB]; positivity
      have e : (W : ℝ) ^ (2 : ℝ) * (W : ℝ) ^ (-2 : ℝ) = 1 := by
        rw [← Real.rpow_add hW0]; norm_num
      rw [abs_of_nonneg h0, hB, Real.div_rpow hW0.le htx.le]
      calc (W : ℝ) ^ (2 : ℝ) / brk d L W x y ^ (2 : ℝ) * brk d L W x y ^ ((2 : ℝ) * d / 2) *
            ((W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)))
          = ((W : ℝ) ^ (2 : ℝ) * (W : ℝ) ^ (-2 : ℝ)) *
            ((brk d L W x y ^ ((2 : ℝ) * d / 2) * brk d L W x y ^ (2 - (d : ℝ))) /
              brk d L W x y ^ (2 : ℝ)) := by ring
        _ = 1 := by
          rw [e, ← Real.rpow_add htx, show (2 : ℝ) * d / 2 + (2 - d) = 2 by ring,
            div_self (by positivity), one_mul]
    unfold strongNorm
    simp only [key]
    simp
  · have key : ∀ x y : Zd d L, ((W : ℝ) / brk d L W x y) ^ (1 : ℝ) *
        brk d L W x y ^ ((1 : ℝ) * d / 2) * |Real.sqrt (bB d L W x y)| = 1 := by
      intro x y
      have htx := ht x y
      have hsq : bB d L W x y =
          ((W : ℝ) ^ (-1 : ℝ) * brk d L W x y ^ (1 - (d : ℝ) / 2)) ^ 2 := by
        rw [hB, mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-1 : ℝ)),
          ← Real.rpow_natCast (brk d L W x y ^ (1 - (d : ℝ) / 2)), ← Real.rpow_mul hW0.le,
          ← Real.rpow_mul htx.le]
        congr 2 <;> push_cast <;> ring
      have h0 : 0 ≤ (W : ℝ) ^ (-1 : ℝ) * brk d L W x y ^ (1 - (d : ℝ) / 2) := by positivity
      rw [hsq, Real.sqrt_sq h0, abs_of_nonneg h0, Real.div_rpow hW0.le htx.le]
      have e : (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (-1 : ℝ) = 1 := by
        rw [← Real.rpow_add hW0]; norm_num
      calc (W : ℝ) ^ (1 : ℝ) / brk d L W x y ^ (1 : ℝ) * brk d L W x y ^ ((1 : ℝ) * d / 2) *
            ((W : ℝ) ^ (-1 : ℝ) * brk d L W x y ^ (1 - (d : ℝ) / 2))
          = ((W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (-1 : ℝ)) *
            ((brk d L W x y ^ ((1 : ℝ) * d / 2) * brk d L W x y ^ (1 - (d : ℝ) / 2)) /
              brk d L W x y ^ (1 : ℝ)) := by ring
        _ = 1 := by
          rw [e, ← Real.rpow_add htx, show (1 : ℝ) * d / 2 + (1 - (d : ℝ) / 2) = 1 by ring,
            div_self (by positivity), one_mul]
    unfold strongNorm
    simp only [key]
    simp

/-- The strong-`(a, b)` norm controls the weak one ([II, §8.1]) when `0 ≤ ad/2 - b < d`:
`‖A‖_{w;(a,b)} ≤ C ‖A‖_{s;(a,b)}`, with `C` depending on `d, a, b`. -/
theorem weak_le_strong :
  ∀ (d : ℕ) (a b : ℝ), 0 ≤ a * d / 2 - b → a * d / 2 - b < d → ∃ C : ℝ,
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ A : Matrix (Zd d L) (Zd d L) ℝ,
      weakNorm d L W a b A ≤ C * strongNorm d L W a b A := by
  intro d a b hs0 hsd
  obtain ⟨C₁, hC₁, hball⟩ := Norm_ballSum2 d (a * d / 2 - b) hs0 hsd
  refine ⟨1 + 2 * C₁, fun L W _ hW A => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hS0 := Norm_strong_nonneg d L W a b A
  have hA := (normBasic d L W hW a b A).2.2
  set S := strongNorm d L W a b A with hS
  -- first term
  have h1 : ∀ x y, |A x y| ≤ (W : ℝ) ^ (-(a * d / 2)) * S := by
    intro x y
    have ht : (W : ℝ) ≤ brk d L W x y := by unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]
    calc |A x y| ≤ (W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b)) * S := hA x y
      _ ≤ (W : ℝ) ^ (-b) * (W : ℝ) ^ (-(a * d / 2 - b)) * S := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hW0 ht (by linarith)) (by positivity)) hS0
      _ = _ := by rw [← Real.rpow_add hW0]; congr 2; ring
  have hnn : 0 ≤ (W : ℝ) ^ (-(a * d / 2)) * S := by positivity
  have hfirst : (W : ℝ) ^ (a * d / 2) * (⨆ x, ⨆ y, |A x y|) ≤ S := by
    calc _ ≤ (W : ℝ) ^ (a * d / 2) * ((W : ℝ) ^ (-(a * d / 2)) * S) :=
          mul_le_mul_of_nonneg_left (Real.iSup_le (fun x => Real.iSup_le (fun y => h1 x y) hnn)
            hnn) (by positivity)
      _ = S := by rw [← mul_assoc, ← Real.rpow_add hW0, add_neg_cancel, Real.rpow_zero, one_mul]
  -- the `K`-terms
  have hK : ∀ K : {K : ℕ // W ≤ K ∧ 2 * K ≤ L}, ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) *
      (⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d) ≤ 2 * C₁ * S := by
    rintro ⟨K, hK1, hK2⟩
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hW.trans hK1
    have hK0 : (0 : ℝ) < K := by linarith
    have hrhs : 0 ≤ 2 * (W : ℝ) ^ (-b) * S * (C₁ * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) /
        (K : ℝ) ^ d := by positivity
    have hpt : ∀ x x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d ≤ 2 * (W : ℝ) ^ (-b) * S *
            (C₁ * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) / (K : ℝ) ^ d := by
      intro x x₀
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc _ ≤ ∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K),
            2 * ((W : ℝ) ^ (-b) * S) * brk d L W y x ^ (-(a * d / 2 - b)) := by
            refine Finset.sum_le_sum fun y _ => ?_
            have e1 := hA x y
            have e2 := hA y x
            rw [Norm_brk_comm d L W x y] at e1
            linarith
        _ = 2 * ((W : ℝ) ^ (-b) * S) * ∑ y ∈ Finset.univ.filter
              (fun y => zdistInf d L (y - x₀) ≤ K), brk d L W y x ^ (-(a * d / 2 - b)) := by
            rw [← Finset.mul_sum]
        _ ≤ 2 * ((W : ℝ) ^ (-b) * S) * (C₁ * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) :=
            mul_le_mul_of_nonneg_left (hball L W hW x x₀ K hK1) (by positivity)
        _ = _ := by ring
    have hsup : (⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K), (|A x y| + |A y x|)) /
          (K : ℝ) ^ d) ≤ 2 * (W : ℝ) ^ (-b) * S *
            (C₁ * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) / (K : ℝ) ^ d :=
      Real.iSup_le (fun x => Real.iSup_le (fun x₀ => hpt x x₀) hrhs) hrhs
    have hcoef := Norm_coef_eq hW0 hK0 b (a * d / 2)
    calc _ ≤ ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) * (2 * (W : ℝ) ^ (-b) * S *
            (C₁ * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) / (K : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = 2 * C₁ * S := by
          rw [hcoef]
          have e1 : (W : ℝ) ^ b * (W : ℝ) ^ (-b) = 1 := by
            rw [← Real.rpow_add hW0]; simp
          have e2 : (K : ℝ) ^ (a * d / 2 - b) * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b)) =
              (K : ℝ) ^ d := by
            rw [← Real.rpow_add hK0, ← Real.rpow_natCast]; congr 1; ring
          have e3 : (0 : ℝ) < (K : ℝ) ^ d := by positivity
          calc (W : ℝ) ^ b * (K : ℝ) ^ (a * d / 2 - b) *
                (2 * (W : ℝ) ^ (-b) * S * (C₁ * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) /
                  (K : ℝ) ^ d)
              = (((W : ℝ) ^ b * (W : ℝ) ^ (-b)) * ((K : ℝ) ^ (a * d / 2 - b) *
                  (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b)))) / (K : ℝ) ^ d *
                (2 * C₁ * S) := by ring
            _ = _ := by rw [e1, e2, one_mul, div_self e3.ne', one_mul]
  unfold weakNorm
  calc _ ≤ S + 2 * C₁ * S := add_le_add hfirst (Real.iSup_le hK (by positivity))
    _ = _ := by ring

/-- The sums of `B` used in [II, (8.33)]: `Σ_y B_{ay} ≤ C L²/W²` for `d ≥ 3`, and
`Σ_y B_{ay} B_{yb} ≤ C W^{-4} ⟨a - b⟩^{-(d-4)}` for `d ≥ 5`, for `W ≥ 1`. -/
theorem bSum :
  (∀ d : ℕ, 3 ≤ d → ∃ C : ℝ, ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ a : Zd d L,
    ∑ y, bB d L W a y ≤ C * (L : ℝ) ^ 2 / (W : ℝ) ^ 2) ∧
  (∀ d : ℕ, 5 ≤ d → ∃ C : ℝ, ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ a b : Zd d L,
    ∑ y, bB d L W a y * bB d L W y b ≤
      C * (W : ℝ) ^ (-4 : ℝ) * brk d L W a b ^ (-((d : ℝ) - 4))) := by
  constructor
  · intro d hd
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    obtain ⟨C₀, hC₀, hb⟩ := Norm_ballSum d ((d : ℝ) - 2) (by linarith) (by linarith)
    refine ⟨4 * C₀ + 1, fun L W _ hW a => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have hW0 : (0 : ℝ) < W := by linarith
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hLW : 0 ≤ (L : ℝ) ^ 2 / (W : ℝ) ^ 2 := by positivity
    rcases le_or_gt W L with hWL | hWL
    · have hbB : ∀ y, bB d L W a y = (W : ℝ) ^ (-2 : ℝ) * brk d L W y a ^ (-((d : ℝ) - 2)) := by
        intro y
        rw [Norm_bB_eq, Norm_brk_comm]
        congr 2; ring
      have hsum : ∑ y, bB d L W a y = (W : ℝ) ^ (-2 : ℝ) * ∑ y ∈ Finset.univ.filter
          (fun y : Zd d L => zdistInf d L (y - a) ≤ L / 2), brk d L W y a ^ (-((d : ℝ) - 2)) := by
        rw [Finset.filter_true_of_mem (fun y _ => zdistInf_le_half d L (y - a)), Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => hbB y
      have h1 := hb L W hW a (L / 2)
      have h2 : (((L / 2 : ℕ) : ℝ) + W) ^ ((d : ℝ) - ((d : ℝ) - 2)) ≤ 4 * (L : ℝ) ^ 2 := by
        have : (L / 2 : ℕ) ≤ L := Nat.div_le_self _ _
        have h3 : ((L / 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast this
        have h4 : (d : ℝ) - ((d : ℝ) - 2) = ((2 : ℕ) : ℝ) := by push_cast; ring
        rw [h4, Real.rpow_natCast]
        have : ((L / 2 : ℕ) : ℝ) + W ≤ 2 * L := by
          have : (W : ℝ) ≤ L := by exact_mod_cast hWL
          linarith
        nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((L / 2 : ℕ) : ℝ)), hW0]
      rw [hsum]
      calc _ ≤ (W : ℝ) ^ (-2 : ℝ) * (C₀ * (4 * (L : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hC₀)) (by positivity)
        _ = 4 * C₀ * ((L : ℝ) ^ 2 / (W : ℝ) ^ 2) := by
            rw [Real.rpow_neg hW0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
        _ ≤ _ := by rw [mul_div_assoc]; nlinarith
    · have hpt : ∀ y, bB d L W a y ≤ ((W : ℝ) ^ d)⁻¹ := by
        intro y
        rw [Norm_bB_eq]
        calc (W : ℝ) ^ (-2 : ℝ) * brk d L W a y ^ (2 - (d : ℝ))
            ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hW0 (Norm_le_brk d L W a y)
                (by linarith)) (by positivity)
          _ = ((W : ℝ) ^ d)⁻¹ := by
              rw [← Real.rpow_add hW0, show (-2 : ℝ) + (2 - (d : ℝ)) = -(d : ℝ) by ring,
                Real.rpow_neg hW0.le, Real.rpow_natCast]
      have hs : ∑ y, bB d L W a y ≤ (L : ℝ) ^ d * ((W : ℝ) ^ d)⁻¹ := by
        calc _ ≤ ∑ y : Zd d L, ((W : ℝ) ^ d)⁻¹ := Finset.sum_le_sum fun y _ => hpt y
          _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]; push_cast; ring
      have hr0 : 0 ≤ (L : ℝ) / W := by positivity
      have hr1 : (L : ℝ) / W ≤ 1 := by rw [div_le_one hW0]; exact_mod_cast hWL.le
      have h5 : ((L : ℝ) / W) ^ d ≤ ((L : ℝ) / W) ^ 2 :=
        pow_le_pow_of_le_one hr0 hr1 (by exact_mod_cast (by linarith : (2 : ℝ) ≤ d))
      rw [div_pow, div_pow] at h5
      calc _ ≤ (L : ℝ) ^ d * ((W : ℝ) ^ d)⁻¹ := hs
        _ = (L : ℝ) ^ d / (W : ℝ) ^ d := by rw [div_eq_mul_inv]
        _ ≤ (L : ℝ) ^ 2 / (W : ℝ) ^ 2 := h5
        _ ≤ _ := by rw [mul_div_assoc]; nlinarith
  · intro d hd
    have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
    obtain ⟨C₁, hC₁, hR⟩ := Norm_region1 d (by omega)
    obtain ⟨C₂, hC₂, hT⟩ := Norm_tailSum d (2 * (d : ℝ) - 4) (by linarith)
    refine ⟨2 * C₁ + C₂ * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4)), fun L W _ hW a b => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have hW0 : (0 : ℝ) < W := by linarith
    set D := brk d L W a b with hD
    have hD1 : (W : ℝ) ≤ D := Norm_le_brk d L W a b
    have hD0 : 0 < D := by linarith
    set X : ℝ := (W : ℝ) ^ (-4 : ℝ) * D ^ (-((d : ℝ) - 4)) with hX
    have hX0 : 0 ≤ X := by positivity
    have hg : ∀ y, bB d L W a y * bB d L W y b = bB d L W y a * bB d L W y b := by
      intro y; rw [Norm_bB_comm d L W a y]
    rw [Finset.sum_congr rfl (fun y _ => hg y)]
    have hh0 : ∀ y, 0 ≤ bB d L W y a * bB d L W y b := fun y =>
      mul_nonneg (Norm_bB_nonneg _ _ _ _ _) (Norm_bB_nonneg _ _ _ _ _)
    have hsplit : ∑ y, bB d L W y a * bB d L W y b ≤
        ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y a < D / 2),
          bB d L W y a * bB d L W y b +
        ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y b < D / 2),
          bB d L W y a * bB d L W y b +
        ∑ y ∈ Finset.univ.filter (fun y : Zd d L => D / 2 ≤ brk d L W y a ∧
          D / 2 ≤ brk d L W y b), bB d L W y a * bB d L W y b := by
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases h1 : brk d L W y a < D / 2
      · simp only [h1, ite_true]
        have := hh0 y
        split_ifs <;> linarith
      · by_cases h2 : brk d L W y b < D / 2
        · simp only [h1, h2, ite_true, ite_false]
          have := hh0 y
          split_ifs <;> linarith
        · have h3 : D / 2 ≤ brk d L W y a ∧ D / 2 ≤ brk d L W y b := ⟨not_lt.1 h1, not_lt.1 h2⟩
          simp only [h1, h2, h3, ite_true, ite_false, and_self]
          linarith
    have s1 := hR L W hW a b
    have s2 : ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y b < D / 2),
        bB d L W y a * bB d L W y b ≤ C₁ * X := by
      have := hR L W hW b a
      rw [Norm_brk_comm d L W b a] at this
      calc _ = ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y b < D / 2),
            bB d L W y b * bB d L W y a := Finset.sum_congr rfl fun y _ => mul_comm _ _
        _ ≤ _ := by rw [hX, ← mul_assoc]; exact this
    have s3 : ∑ y ∈ Finset.univ.filter (fun y : Zd d L => D / 2 ≤ brk d L W y a ∧
          D / 2 ≤ brk d L W y b), bB d L W y a * bB d L W y b ≤
        C₂ * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4)) * X := by
      have hM : 1 ≤ 2 * (D / 2) := by linarith
      have ta := hT L W hW a (D / 2) hM
      have tb := hT L W hW b (D / 2) hM
      have hc : (D / 2) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)) =
          D ^ (-((d : ℝ) - 4)) * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4)) := by
        rw [div_eq_mul_inv, Real.mul_rpow hD0.le (by norm_num)]
        congr 2 <;> ring
      rw [hc] at ta tb
      have hpt : ∀ y : Zd d L, bB d L W y a * bB d L W y b ≤
          (W : ℝ) ^ (-4 : ℝ) / 2 * (brk d L W y a ^ (-(2 * (d : ℝ) - 4)) +
            brk d L W y b ^ (-(2 * (d : ℝ) - 4))) := by
        intro y
        have h1 := Norm_bB_sq d L W hW y a
        have h2 := Norm_bB_sq d L W hW y b
        nlinarith [sq_nonneg (bB d L W y a - bB d L W y b)]
      have hnn : ∀ z y : Zd d L, 0 ≤ brk d L W y z ^ (-(2 * (d : ℝ) - 4)) :=
        fun z y => Real.rpow_nonneg (Norm_brk_pos d L W hW y z).le _
      set S3 := Finset.univ.filter (fun y : Zd d L => D / 2 ≤ brk d L W y a ∧
          D / 2 ≤ brk d L W y b) with hS3
      have u1 : ∑ y ∈ S3, brk d L W y a ^ (-(2 * (d : ℝ) - 4)) ≤
          C₂ * (D ^ (-((d : ℝ) - 4)) * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4))) := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_)
          (fun y _ _ => hnn a y)).trans ta
        simp only [hS3, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hy.1
      have u2 : ∑ y ∈ S3, brk d L W y b ^ (-(2 * (d : ℝ) - 4)) ≤
          C₂ * (D ^ (-((d : ℝ) - 4)) * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4))) := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_)
          (fun y _ _ => hnn b y)).trans tb
        simp only [hS3, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hy.2
      calc ∑ y ∈ S3, bB d L W y a * bB d L W y b
          ≤ ∑ y ∈ S3, (W : ℝ) ^ (-4 : ℝ) / 2 * (brk d L W y a ^ (-(2 * (d : ℝ) - 4)) +
            brk d L W y b ^ (-(2 * (d : ℝ) - 4))) := Finset.sum_le_sum fun y _ => hpt y
        _ = (W : ℝ) ^ (-4 : ℝ) / 2 * (∑ y ∈ S3, brk d L W y a ^ (-(2 * (d : ℝ) - 4)) +
            ∑ y ∈ S3, brk d L W y b ^ (-(2 * (d : ℝ) - 4))) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ (W : ℝ) ^ (-4 : ℝ) / 2 * (C₂ * (D ^ (-((d : ℝ) - 4)) * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4))) +
            C₂ * (D ^ (-((d : ℝ) - 4)) * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4)))) :=
            mul_le_mul_of_nonneg_left (add_le_add u1 u2) (by positivity)
        _ = _ := by rw [hX]; ring
    calc _ ≤ _ := hsplit
      _ ≤ C₁ * X + C₁ * X + C₂ * ((2 : ℝ)⁻¹) ^ (-((d : ℝ) - 4)) * X := by
          refine add_le_add (add_le_add ?_ s2) s3
          rw [hX, ← mul_assoc]; exact s1
      _ = _ := by rw [hX]; ring



end RBM8D
