module

public import RBM8D.TExp.Defs
public import RBM8D.Kernel.ThetaDecay
public import RBM8D.Kernel.ZdCancel
public import RBM8D.Profile.Symbol
public import RBM8D.Input.Entry
public import RBM8D.Input.Sizes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import RBM8D.Bound.Norm

@[expose] public section

/-!
# Labelled `Θ` edges on the torus ([I, Lemma 6.2] = [II, Lemma 2.8])

For an abstract family of kernels with the properties [I, (1.25)–(1.27)].
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

/-- A family of kernels `K l W L z` on `Z_L^d`, indexed by the order `l`, the band width `W`,
the side length `L` and the spectral parameter `z`. -/
abbrev KerFamily (d : ℕ) : Type :=
  ℕ → ℕ → ∀ (L : ℕ) [NeZero L], ℂ → Matrix (Zd d L) (Zd d L) ℂ

/-- [I, (1.25)] for the order `l` of a kernel family: translation invariance and symmetry, for
every `(W, L)` and every `z` with `Im z > 0`. -/
def KerSymm {d : ℕ} (K : KerFamily d) (l : ℕ) : Prop :=
  ∀ (W L : ℕ) [NeZero L] (z : ℂ), 0 < z.im → ∀ x a : Zd d L,
    K l W L z x (x + a) = K l W L z 0 a ∧ K l W L z 0 a = K l W L z 0 (-a)

/-- [I, (1.26)–(1.27)] for the order `l` of a kernel family, with the quantifiers of
`SelfEnergyBound`: `|K(0, x)| ≤ L^τ W^{-(l-4)d/2} B_{0x}² + L^τ W^{-(l-2)d/2} 1_{x=0}` and
`|Σ_x K(0, x)| ≤ L^τ η W^{-(l-2)d/2}`. The diagonal term `L^τ W^{-(l-2)d/2} 1_{x=0}` is added to
[I, (1.26)], as in `SelfEnergyBound`; it is `W^{-d}` times the coefficient of `B_{0x}²`, and it is
absorbed after one product with `Θ` (`thetaSigma`). -/
def KerBound {d : ℕ} (K : KerFamily d) (l : ℕ) : Prop :=
  ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L,
        (∀ x : Zd d L, ‖K l W L z 0 x‖ ≤
          (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
            (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) ∧
        ‖∑ x : Zd d L, K l W L z 0 x‖ ≤
          (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))

/-- The kernel family of the self-energies `Sig` for the variance family `Svar`. -/
def sigKer {d : ℕ} (Svar : VarFamily d) (Sig : ℕ → Expansion 2) : KerFamily d :=
  fun l W L _ z => sigMat Sig (Svar W L) z l

/-! ## Summation toolbox -/

/-- The ball `{y : ‖y - x₀‖_L ≤ ρ}` of `Z_L^d` has at most `(2ρ + 1)^d` points. -/
private theorem Chain_card_ball (d L : ℕ) [NeZero L] (x₀ : Zd d L) (ρ : ℕ) :
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
private theorem Chain_brk_comm (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    brk d L W x y = brk d L W y x := by
  unfold brk
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- Dyadic decomposition: if `f` is nonnegative and nonincreasing on `[M, ∞)`, `M ≥ 1/2`, then `Σ
f(⟨y - x⟩)` over the points with `M ≤ ⟨y - x⟩ < 2^N M` is at most `Σ_{j < N} (3 · 2^{j+1} M)^d
f(2^j M)`. -/
private theorem Chain_levels (d L W : ℕ) [NeZero L] (x : Zd d L) (M : ℝ)
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
      have h2 := (Finset.card_le_card hsub).trans (Chain_card_ball d L x ρ)
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
private theorem Chain_powLevels (d L W : ℕ) [NeZero L] (x : Zd d L) (M p : ℝ) (hM : 1 ≤ 2 * M)
    (hp : 0 ≤ p) (N : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : Zd d L => M ≤ brk d L W y x ∧ brk d L W y x < 2 ^ N * M),
        brk d L W y x ^ (-p) ≤
      6 ^ d * M ^ ((d : ℝ) - p) * ∑ j ∈ Finset.range N, ((2 : ℝ) ^ ((d : ℝ) - p)) ^ j := by
  have hM0 : 0 < M := by linarith
  refine (Chain_levels d L W x M hM (fun t => t ^ (-p)) (fun t ht => ?_) (fun s t hs hst => ?_) N).trans
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
private theorem Chain_ballSum (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
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
    (Chain_powLevels d L W x W s (by linarith) hs0 N)
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
private theorem Chain_tailSum (d : ℕ) (q : ℝ) (hq : (d : ℝ) < q) :
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
    (Chain_powLevels d L W x M q hM (by linarith) N)
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

/-- `‖x - y‖_L = ‖y - x‖_L`. -/
private theorem Chain_zdistInf_comm (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- `B_{xy} = W^{-2} ⟨x - y⟩^{-(d-2)}`. -/
private theorem Chain_bB_eq (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl

/-- `B_{xy} ≥ 0`. -/
private theorem Chain_bB_nonneg (d L W : ℕ) [NeZero L] (x y : Zd d L) : 0 ≤ bB d L W x y := by
  rw [Chain_bB_eq]; unfold brk; positivity

/-- `⟨x - y⟩ > 0` for `W ≥ 1`. -/
private theorem Chain_brk_pos (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    0 < brk d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold brk; positivity

/-- `W ≤ ⟨x - y⟩`. -/
private theorem Chain_le_brk (d L W : ℕ) [NeZero L] (x y : Zd d L) : (W : ℝ) ≤ brk d L W x y := by
  unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]

/-- `⟨p - q⟩ + W ≤ ⟨y - p⟩ + ⟨y - q⟩`. -/
private theorem Chain_brk_tri (d L W : ℕ) [NeZero L] (y p q : Zd d L) :
    brk d L W p q + W ≤ brk d L W y p + brk d L W y q := by
  have h1 : zdistInf d L (p - q) ≤ zdistInf d L (p - y) + zdistInf d L (y - q) := by
    have := zdistInf_add_le d L (p - y) (y - q)
    rwa [sub_add_sub_cancel] at this
  rw [Chain_zdistInf_comm d L p y] at h1
  have h2 : (zdistInf d L (p - q) : ℝ) ≤ zdistInf d L (y - p) + zdistInf d L (y - q) := by
    exact_mod_cast h1
  unfold brk
  rw [Chain_zdistInf_comm d L p q] at h2 ⊢
  linarith [h2]

/-- `B_{xy}² = W^{-4} ⟨x - y⟩^{-(2d-4)}`. -/
private theorem Chain_bB_sq (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ^ 2 = (W : ℝ) ^ (-4 : ℝ) * brk d L W x y ^ (-(2 * (d : ℝ) - 4)) := by
  have hW0 : (0 : ℝ) < W := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW
                               linarith
  have ht := Chain_brk_pos d L W hW x y
  rw [Chain_bB_eq, mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ (-2 : ℝ)),
    ← Real.rpow_natCast (brk d L W x y ^ (2 - (d : ℝ))), ← Real.rpow_mul hW0.le,
    ← Real.rpow_mul ht.le]
  congr 2 <;> push_cast <;> ring


/-- `⟨y - x⟩ ≤ L + W`. -/
private theorem Chain_brk_le (d L W : ℕ) [NeZero L] (y x : Zd d L) :
    brk d L W y x ≤ (L : ℝ) + W := by
  unfold brk
  have h1 : zdistInf d L (y - x) ≤ L / 2 := zdistInf_le_half d L _
  have h2 : (zdistInf d L (y - x) : ℝ) ≤ L := by exact_mod_cast h1.trans (Nat.div_le_self _ _)
  linarith

/-- For `q + δ > d` and `δ > 0`: `Σ_{⟨y - x⟩ ≤ M} ⟨y - x⟩^{-q} ≤ C M^δ W^{d - q - δ}`, with `C`
depending on `d, q, δ` only, for `W ≥ 1` and `M > 0`. -/
private theorem Chain_sumLe (d : ℕ) (q δ : ℝ) (hδ : 0 < δ) (hq : (d : ℝ) < q + δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (x : Zd d L) (M : ℝ), 0 < M →
      ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M), brk d L W y x ^ (-q) ≤
        C * M ^ δ * (W : ℝ) ^ ((d : ℝ) - q - δ) := by
  obtain ⟨C, hC, h⟩ := Chain_tailSum d (q + δ) hq
  refine ⟨C, hC, fun L W _ hW x M hM => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hall : ∑ y : Zd d L, brk d L W y x ^ (-(q + δ)) ≤ C * (W : ℝ) ^ ((d : ℝ) - (q + δ)) := by
    have := h L W hW x W (by linarith)
    have e : Finset.univ.filter (fun y : Zd d L => (W : ℝ) ≤ brk d L W y x) = Finset.univ := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [Chain_brk_comm]; exact Chain_le_brk d L W x y
    rwa [e] at this
  calc ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M), brk d L W y x ^ (-q)
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M),
          M ^ δ * brk d L W y x ^ (-(q + δ)) := by
        refine Finset.sum_le_sum fun y hy => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have ht : 0 < brk d L W y x := by rw [Chain_brk_comm]; exact Chain_brk_pos d L W hW x y
        have e : brk d L W y x ^ (-q) = brk d L W y x ^ δ * brk d L W y x ^ (-(q + δ)) := by
          rw [← Real.rpow_add ht]; congr 1; ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le hy hδ.le)
          (Real.rpow_nonneg ht.le _)
    _ = M ^ δ * ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M),
          brk d L W y x ^ (-(q + δ)) := by rw [Finset.mul_sum]
    _ ≤ M ^ δ * ∑ y : Zd d L, brk d L W y x ^ (-(q + δ)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun y _ _ => ?_)) (by positivity)
        refine Real.rpow_nonneg ?_ _
        rw [Chain_brk_comm]; exact (Chain_brk_pos d L W hW x y).le
    _ ≤ M ^ δ * (C * (W : ℝ) ^ ((d : ℝ) - (q + δ))) := mul_le_mul_of_nonneg_left hall (by positivity)
    _ = C * M ^ δ * (W : ℝ) ^ ((d : ℝ) - q - δ) := by
        rw [show (d : ℝ) - q - δ = (d : ℝ) - (q + δ) by ring]; ring

/-- For `0 ≤ s < d` and `M > 0`: `Σ_{⟨y - x⟩ ≤ M} ⟨y - x⟩^{-s} ≤ C M^{d - s}`, with `C`
depending on `d, s` only, for `W ≥ 1`. -/
private theorem Chain_ballLe (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (x : Zd d L) (M : ℝ), 0 < M →
      ∑ y ∈ Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M), brk d L W y x ^ (-s) ≤
        C * M ^ ((d : ℝ) - s) := by
  obtain ⟨C₀, hC₀, hb⟩ := Chain_ballSum d s hs0 hsd
  refine ⟨C₀ * 2 ^ ((d : ℝ) - s), by positivity, fun L W _ hW x M hM => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hσ : 0 < (d : ℝ) - s := by linarith
  by_cases hMW : (W : ℝ) ≤ M
  · set K := ⌊M⌋₊ with hK
    have hsub : Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M) ⊆
        Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x) ≤ K) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      apply Nat.le_floor
      unfold brk at hy
      linarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ =>
      Real.rpow_nonneg (by unfold brk; positivity) _)).trans ((hb L W hW x K).trans ?_)
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) hM.le]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hσ.le) hC₀
    have : (K : ℝ) ≤ M := Nat.floor_le hM.le
    linarith
  · rw [not_le] at hMW
    have : Finset.univ.filter (fun y : Zd d L => brk d L W y x ≤ M) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_le]
      rw [Chain_brk_comm]; exact lt_of_lt_of_le hMW (Chain_le_brk d L W x y)
    rw [this, Finset.sum_empty]
    positivity


/-- `⟨x - α⟩ ≤ ⟨x - y⟩ + ⟨α - y⟩`. -/
private theorem Chain_brk_tri2 (d L W : ℕ) [NeZero L] (x y α : Zd d L) :
    brk d L W x α ≤ brk d L W x y + brk d L W α y := by
  have h := Chain_brk_tri d L W y x α
  rw [Chain_brk_comm d L W y x, Chain_brk_comm d L W y α] at h
  have : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  linarith

/-- `⟨x - y⟩ + W ≤ ⟨x - α⟩ + ⟨α - y⟩`. -/
private theorem Chain_brk_tri3 (d L W : ℕ) [NeZero L] (x y α : Zd d L) :
    brk d L W x y + W ≤ brk d L W x α + brk d L W α y := by
  have h := Chain_brk_tri d L W α x y
  rw [Chain_brk_comm d L W α x] at h
  exact h

/-- The convolution of `⟨·⟩^{-d}` with `⟨·⟩^{-(d-2)}`:
`Σ_α ⟨x - α⟩^{-d} ⟨α - y⟩^{-(d-2)} ≤ C (⟨x - y⟩/W)^δ ⟨x - y⟩^{-(d-2)}`, for `d ≥ 3`, `δ > 0`. -/
private theorem Chain_conv (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ x y : Zd d L,
      ∑ α, brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
        C * (brk d L W x y / W) ^ δ * brk d L W x y ^ (-((d : ℝ) - 2)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, hC₁, h1⟩ := Chain_ballLe d ((d : ℝ) - 2) (by linarith) (by linarith)
  obtain ⟨C₂, hC₂, h2⟩ := Chain_sumLe d (d : ℝ) δ hδ (by linarith)
  obtain ⟨C₃, hC₃, h3⟩ := Chain_tailSum d (2 * (d : ℝ) - 2) (by linarith)
  refine ⟨2 ^ ((d : ℝ) - 2) * (C₁ + C₂ + 3 ^ ((d : ℝ) - 2) * C₃), by positivity,
    fun L W _ hW x y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set r := brk d L W x y with hr
  have hrW : (W : ℝ) ≤ r := Chain_le_brk d L W x y
  have hr0 : 0 < r := by linarith
  set u := r / 2 with hu
  have hu0 : 0 < u := by positivity
  have hpos : ∀ a b : Zd d L, 0 < brk d L W a b := fun a b => Chain_brk_pos d L W hW a b
  have hcomm : ∀ α : Zd d L, brk d L W x α = brk d L W α x := fun α => Chain_brk_comm d L W x α
  -- the pointwise bound
  have hpt : ∀ α : Zd d L, brk d L W α x ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
      (if brk d L W α y ≤ u then u ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) else 0) +
      (if brk d L W α x ≤ u then u ^ (-((d : ℝ) - 2)) * brk d L W α x ^ (-(d : ℝ)) else 0) +
      (if u ≤ brk d L W α x then 3 ^ ((d : ℝ) - 2) * brk d L W α x ^ (-(2 * (d : ℝ) - 2))
        else 0) := by
    intro α
    have hxα := hpos α x
    have hαy := hpos α y
    have t3 := Chain_brk_tri3 d L W x y α
    have t2 := Chain_brk_tri2 d L W x y α
    rw [hcomm α] at t2 t3
    have h4 : 0 ≤ (if brk d L W α y ≤ u then u ^ (-(d : ℝ)) *
        brk d L W α y ^ (-((d : ℝ) - 2)) else 0) := by split_ifs <;> positivity
    have h4' : 0 ≤ (if brk d L W α x ≤ u then u ^ (-((d : ℝ) - 2)) *
        brk d L W α x ^ (-(d : ℝ)) else 0) := by split_ifs <;> positivity
    have h5 : 0 ≤ (if u ≤ brk d L W α x then 3 ^ ((d : ℝ) - 2) *
        brk d L W α x ^ (-(2 * (d : ℝ) - 2)) else 0) := by split_ifs <;> positivity
    by_cases hA : brk d L W α y ≤ u
    · -- near `y`
      have hxu : u ≤ brk d L W α x := by linarith
      rw [if_pos hA]
      have h6 : brk d L W α x ^ (-(d : ℝ)) ≤ u ^ (-(d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hu0 hxu (by linarith)
      have h7 : brk d L W α x ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
          u ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hαy.le _)
      linarith
    · rw [not_le] at hA
      by_cases hB : brk d L W α x ≤ u
      · have h8 : brk d L W α y ^ (-((d : ℝ) - 2)) ≤ u ^ (-((d : ℝ) - 2)) :=
          Real.rpow_le_rpow_of_nonpos hu0 hA.le (by linarith)
        rw [if_pos hB]
        have h7 : brk d L W α x ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
            brk d L W α x ^ (-(d : ℝ)) * u ^ (-((d : ℝ) - 2)) :=
          mul_le_mul_of_nonneg_left h8 (Real.rpow_nonneg hxα.le _)
        linarith
      · rw [not_le] at hB
        rw [if_pos hB.le]
        -- both far: `⟨α - y⟩ ≥ ⟨α - x⟩ / 3`
        have h9 : brk d L W α x / 3 ≤ brk d L W α y := by linarith
        have h10 : brk d L W α y ^ (-((d : ℝ) - 2)) ≤ (brk d L W α x / 3) ^ (-((d : ℝ) - 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h9 (by linarith)
        have h11 : (brk d L W α x / 3) ^ (-((d : ℝ) - 2)) =
            3 ^ ((d : ℝ) - 2) * brk d L W α x ^ (-((d : ℝ) - 2)) := by
          rw [div_eq_mul_inv, Real.mul_rpow hxα.le (by norm_num), Real.inv_rpow (by norm_num),
            ← Real.rpow_neg (by norm_num), neg_neg]
          ring
        have h12 : brk d L W α x ^ (-(d : ℝ)) * brk d L W α x ^ (-((d : ℝ) - 2)) =
            brk d L W α x ^ (-(2 * (d : ℝ) - 2)) := by
          rw [← Real.rpow_add hxα]; congr 1; ring
        have h13 : brk d L W α x ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
            brk d L W α x ^ (-(d : ℝ)) * (3 ^ ((d : ℝ) - 2) *
              brk d L W α x ^ (-((d : ℝ) - 2))) := by
          rw [← h11]
          exact mul_le_mul_of_nonneg_left h10 (Real.rpow_nonneg hxα.le _)
        have h14 : brk d L W α x ^ (-(d : ℝ)) * (3 ^ ((d : ℝ) - 2) *
              brk d L W α x ^ (-((d : ℝ) - 2))) =
            3 ^ ((d : ℝ) - 2) * brk d L W α x ^ (-(2 * (d : ℝ) - 2)) := by
          rw [← h12]; ring
        linarith
  have e1 : ∑ α, brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) =
      ∑ α, brk d L W α x ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) :=
    Finset.sum_congr rfl fun α _ => by rw [hcomm α]
  rw [e1]
  have hS1 : ∑ α ∈ Finset.univ.filter (fun α : Zd d L => brk d L W α y ≤ u),
      u ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤ C₁ * u ^ (-((d : ℝ) - 2)) := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (h1 L W hW y u hu0) (Real.rpow_nonneg hu0.le (-(d : ℝ)))
    refine this.trans (le_of_eq ?_)
    rw [show (d : ℝ) - ((d : ℝ) - 2) = 2 by ring, mul_left_comm, ← Real.rpow_add hu0]
    congr 2; ring
  have hS2 : ∑ α ∈ Finset.univ.filter (fun α : Zd d L => brk d L W α x ≤ u),
      u ^ (-((d : ℝ) - 2)) * brk d L W α x ^ (-(d : ℝ)) ≤
      C₂ * u ^ (-((d : ℝ) - 2)) * (u / W) ^ δ := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (h2 L W hW x u hu0) (Real.rpow_nonneg hu0.le (-((d : ℝ) - 2)))
    refine this.trans (le_of_eq ?_)
    rw [Real.div_rpow hu0.le hW0.le, show (d : ℝ) - d - δ = -δ by ring, Real.rpow_neg hW0.le]
    ring
  have hS3 : ∑ α ∈ Finset.univ.filter (fun α : Zd d L => u ≤ brk d L W α x),
      3 ^ ((d : ℝ) - 2) * brk d L W α x ^ (-(2 * (d : ℝ) - 2)) ≤
      3 ^ ((d : ℝ) - 2) * C₃ * u ^ (-((d : ℝ) - 2)) := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (h3 L W hW x u (by linarith))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((d : ℝ) - 2))
    refine this.trans (le_of_eq ?_)
    rw [show (d : ℝ) - (2 * d - 2) = -((d : ℝ) - 2) by ring]
    ring
  calc ∑ α, brk d L W α x ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2))
      ≤ ∑ α, ((if brk d L W α y ≤ u then u ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2))
          else 0) +
        (if brk d L W α x ≤ u then u ^ (-((d : ℝ) - 2)) * brk d L W α x ^ (-(d : ℝ)) else 0) +
        (if u ≤ brk d L W α x then 3 ^ ((d : ℝ) - 2) * brk d L W α x ^ (-(2 * (d : ℝ) - 2))
          else 0)) := Finset.sum_le_sum fun α _ => hpt α
    _ = (∑ α ∈ Finset.univ.filter (fun α : Zd d L => brk d L W α y ≤ u),
          u ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2))) +
        (∑ α ∈ Finset.univ.filter (fun α : Zd d L => brk d L W α x ≤ u),
          u ^ (-((d : ℝ) - 2)) * brk d L W α x ^ (-(d : ℝ))) +
        ∑ α ∈ Finset.univ.filter (fun α : Zd d L => u ≤ brk d L W α x),
          3 ^ ((d : ℝ) - 2) * brk d L W α x ^ (-(2 * (d : ℝ) - 2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
          Finset.sum_filter]
    _ ≤ C₁ * u ^ (-((d : ℝ) - 2)) + C₂ * u ^ (-((d : ℝ) - 2)) * (u / W) ^ δ +
          3 ^ ((d : ℝ) - 2) * C₃ * u ^ (-((d : ℝ) - 2)) := by linarith
    _ ≤ _ := by
        have hu1 : 1 ≤ (r / W) ^ δ := Real.one_le_rpow (by rw [le_div_iff₀ hW0]; linarith) hδ.le
        have huW : (u / W) ^ δ ≤ (r / W) ^ δ := by
          refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
          rw [hu]; gcongr; linarith
        have hup : 0 ≤ u ^ (-((d : ℝ) - 2)) := Real.rpow_nonneg hu0.le _
        have e2 : u ^ (-((d : ℝ) - 2)) = 2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2)) := by
          rw [hu, div_eq_mul_inv, Real.mul_rpow hr0.le (by norm_num), Real.inv_rpow (by norm_num),
            ← Real.rpow_neg (by norm_num), neg_neg]
          ring
        rw [e2]
        have hr2 : 0 ≤ r ^ (-((d : ℝ) - 2)) := Real.rpow_nonneg hr0.le _
        have h2d : 0 ≤ (2 : ℝ) ^ ((d : ℝ) - 2) := by positivity
        calc C₁ * (2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2))) +
              C₂ * (2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2))) * (u / W) ^ δ +
              3 ^ ((d : ℝ) - 2) * C₃ * (2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2)))
            ≤ C₁ * (2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2))) * (r / W) ^ δ +
              C₂ * (2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2))) * (r / W) ^ δ +
              3 ^ ((d : ℝ) - 2) * C₃ * (2 ^ ((d : ℝ) - 2) * r ^ (-((d : ℝ) - 2))) * (r / W) ^ δ := by
              have hA := mul_nonneg hC₁ (mul_nonneg h2d hr2)
              have hB := mul_nonneg hC₂ (mul_nonneg h2d hr2)
              have hC := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ ((d : ℝ) - 2)) hC₃)
                (mul_nonneg h2d hr2)
              nlinarith [mul_le_mul_of_nonneg_left huW hB]
          _ = _ := by ring


/-- `Σ_y ⟨y - x⟩^{-q} ≤ C W^{d - q}` for `q > d`, with `C` depending on `d, q` only, for `W ≥ 1`. -/
private theorem Chain_sumAll (d : ℕ) (q : ℝ) (hq : (d : ℝ) < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ x : Zd d L,
      ∑ y : Zd d L, brk d L W y x ^ (-q) ≤ C * (W : ℝ) ^ ((d : ℝ) - q) := by
  obtain ⟨C, hC, h⟩ := Chain_tailSum d q hq
  refine ⟨C, hC, fun L W _ hW x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have := h L W hW x W (by linarith)
  have e : Finset.univ.filter (fun y : Zd d L => (W : ℝ) ≤ brk d L W y x) = Finset.univ := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [Chain_brk_comm]; exact Chain_le_brk d L W x y
  rwa [e] at this

/-- `B_{xy} = W^{-2} ⟨x - y⟩^{-(d-2)}`. -/
private theorem Chain_bB_eq' (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 2)) := by
  rw [Chain_bB_eq]; congr 2; ring

/-- `L^t ≤ W^{t/c₁}` for `t ≥ 0` when `L^{c₁} ≤ W`. -/
private theorem Chain_Lpow {L W : ℕ} {c₁ : ℝ} (hc₁ : 0 < c₁) (hL : 1 ≤ L)
    (hLW : (L : ℝ) ^ c₁ ≤ W) {t : ℝ} (ht : 0 ≤ t) : (L : ℝ) ^ t ≤ (W : ℝ) ^ (t / c₁) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  calc (L : ℝ) ^ t = ((L : ℝ) ^ c₁) ^ (t / c₁) := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
    _ ≤ (W : ℝ) ^ (t / c₁) := Real.rpow_le_rpow (by positivity) hLW (by positivity)

/-- Reindexing of a sum over `Z_L^d` by a translation. -/
private theorem Chain_sum_sub {d L : ℕ} [NeZero L] {M : Type*} [AddCommMonoid M]
    (F : Zd d L → M) (x₀ : Zd d L) : ∑ u, F (u - x₀) = ∑ v, F v :=
  Fintype.sum_equiv (Equiv.subRight x₀) _ _ (fun _ => rfl)

/-- `‖v‖_L ≤ ⟨v⟩`. -/
private theorem Chain_zd_le_brk (d L W : ℕ) [NeZero L] (v : Zd d L) :
    (zdistInf d L v : ℝ) ≤ brk d L W v 0 := by
  unfold brk; rw [sub_zero]; linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]

/-- `⟨v⟩ = ‖v‖_L + W`. -/
private theorem Chain_brk_zero (d L W : ℕ) [NeZero L] (v : Zd d L) :
    brk d L W v 0 = (zdistInf d L v : ℝ) + W := by
  unfold brk; rw [sub_zero]

/-- The pointwise bound for `Θ`: from the decay `thetaBound` with `D = d`, `|Θ_{0u}| ≤ 2 W^σ
B_{0u}` for `W ≥ 1`. -/
private theorem Chain_theta_pt {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) {σ η : ℝ} (hσ : 0 ≤ σ)
    {Θ₀ : Zd d L → ℝ} (hdec : ∀ u, |Θ₀ u| ≤ thetaBound W η σ (d : ℝ) 0 u) (u : Zd d L) :
    |Θ₀ u| ≤ 2 * (W : ℝ) ^ σ * bB d L W 0 u := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h1 := hdec u
  unfold thetaBound at h1
  have hs : zdistInf d L (0 - u) = zdistInf d L u := by rw [zero_sub, zdistInf_neg]
  rw [hs] at h1
  have hb : bB d L W 0 u = (W : ℝ) ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2)) := by
    rw [Chain_bB_eq', Chain_brk_comm]
  have ht : 0 < brk d L W u 0 := Chain_brk_pos d L W hW u 0
  have hWb : (W : ℝ) ≤ brk d L W u 0 := by rw [Chain_brk_comm]; exact Chain_le_brk d L W 0 u
  have h2 : ((zdistInf d L u : ℝ) + W) ^ (-(d : ℝ)) ≤ bB d L W 0 u := by
    rw [hb, ← Chain_brk_zero]
    have e : brk d L W u 0 ^ (-(d : ℝ)) = brk d L W u 0 ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2)) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht.le _)
    exact Real.rpow_le_rpow_of_nonpos hW0 hWb (by norm_num)
  have hσ1 : (1 : ℝ) ≤ (W : ℝ) ^ σ := Real.one_le_rpow hW1 hσ
  have hB0 : 0 ≤ bB d L W 0 u := by rw [hb]; positivity
  have h3 : (if (zdistInf d L u : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
      (W : ℝ) ^ σ * bB d L W 0 u else 0) ≤ (W : ℝ) ^ σ * bB d L W 0 u := by
    split_ifs
    · exact le_rfl
    · positivity
  nlinarith

/-- `B_{0u} ≤ W^{-d}`. -/
private theorem Chain_bB_le {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (u : Zd d L) (hd : 2 ≤ d) :
    bB d L W 0 u ≤ (W : ℝ) ^ (-(d : ℝ)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hb : bB d L W 0 u = (W : ℝ) ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2)) := by
    rw [Chain_bB_eq', Chain_brk_comm]
  have hWb : (W : ℝ) ≤ brk d L W u 0 := by rw [Chain_brk_comm]; exact Chain_le_brk d L W 0 u
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [hb]
  calc (W : ℝ) ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2))
      ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hW0 hWb (by linarith)) (by positivity)
    _ = (W : ℝ) ^ (-(d : ℝ)) := by rw [← Real.rpow_add hW0]; congr 1; ring


/-- The cancellation property of `Θ_{0·}` of [I, Lemma 6.1], for `K ≥ W`, `g` symmetric,
supported on `‖x‖_L ≤ K` with `Σ_x g(x) = 0`, and `‖x₀‖_L ≥ K^{1+c}`. -/
private def Chain_ThetaCan (d L W : ℕ) [NeZero L] (η σ c D : ℝ) (Θ₀ : Zd d L → ℝ) : Prop :=
  ∀ (K : ℕ), W ≤ K → ∀ g : Zd d L → ℝ, (∀ x, g (-x) = g x) →
    (∀ x, K < zdistInf d L x → g x = 0) → ∑ x, g x = 0 →
      ∀ x₀ : Zd d L, (K : ℝ) ^ (1 + c) ≤ zdistInf d L x₀ →
        |∑ x, Θ₀ x * g (x - x₀)| ≤
          (∑ x, ((zdistInf d L x : ℝ) / zdistInf d L x₀) ^ 2 * |g x|) *
            ((if (zdistInf d L x₀ : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
                (zdistInf d L x₀ : ℝ) ^ σ * bB d L W 0 x₀ else 0) +
              (zdistInf d L x₀ : ℝ) ^ (-D))

/-- The part of `g` supported on `‖v‖_L ≤ R`, with its mean moved to the origin: symmetric,
supported on `‖v‖_L ≤ R` and of sum zero. -/
private def Chain_gt {d L : ℕ} [NeZero L] (R : ℕ) (g : Zd d L → ℂ) : Zd d L → ℂ :=
  fun v => (if zdistInf d L v ≤ R then g v else 0) -
    (if v = 0 then ∑ w, (if zdistInf d L w ≤ R then g w else 0) else 0)

/-- `g = g̃ + (Σ_{‖v‖ ≤ R} g) δ₀ + g 1_{‖v‖ > R}`. -/
private theorem Chain_gt_decomp {d L : ℕ} [NeZero L] (R : ℕ) (g : Zd d L → ℂ) (v : Zd d L) :
    g v = Chain_gt R g v + (if v = 0 then ∑ w, (if zdistInf d L w ≤ R then g w else 0) else 0) +
      (if R < zdistInf d L v then g v else 0) := by
  unfold Chain_gt
  by_cases h : zdistInf d L v ≤ R
  · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
  · rw [if_neg h, if_pos (not_le.mp h)]; ring

private theorem Chain_gt_symm {d L : ℕ} [NeZero L] (R : ℕ) (g : Zd d L → ℂ)
    (hg : ∀ v, g (-v) = g v) (v : Zd d L) : Chain_gt R g (-v) = Chain_gt R g v := by
  unfold Chain_gt
  simp only [zdistInf_neg, hg, neg_eq_zero]

private theorem Chain_gt_supp {d L : ℕ} [NeZero L] (R : ℕ) (g : Zd d L → ℂ) (v : Zd d L)
    (hv : R < zdistInf d L v) : Chain_gt R g v = 0 := by
  unfold Chain_gt
  have hv0 : v ≠ 0 := fun h => by
    rw [h, (zdistInf_eq_zero_iff d L).2 rfl] at hv; omega
  rw [if_neg (not_le.mpr hv), if_neg hv0]; ring

private theorem Chain_gt_sum {d L : ℕ} [NeZero L] (R : ℕ) (g : Zd d L → ℂ) :
    ∑ v, Chain_gt R g v = 0 := by
  unfold Chain_gt
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (0 : Zd d L)]
  simp

private theorem Chain_gt_norm {d L : ℕ} [NeZero L] (R : ℕ) (g : Zd d L → ℂ) (v : Zd d L)
    (hv : v ≠ 0) : ‖Chain_gt R g v‖ ≤ ‖g v‖ := by
  unfold Chain_gt
  rw [if_neg hv, sub_zero]
  split_ifs
  · exact le_rfl
  · simp

/-- One real linear part of the cancellation term. -/
private theorem Chain_T1_part {d L W : ℕ} [NeZero L] {σ c η D : ℝ} {Θ₀ : Zd d L → ℝ}
    (hcan : Chain_ThetaCan d L W η σ c D Θ₀) (R : ℕ) (hR : W ≤ R)
    (g : Zd d L → ℂ) (hg2 : ∀ v, g (-v) = g v) (x₀ : Zd d L)
    (hx₀ : (R : ℝ) ^ (1 + c) ≤ zdistInf d L x₀) (f : ℂ →ₗ[ℝ] ℝ) (hf : ∀ z, |f z| ≤ ‖z‖)
    (hΨ : 0 ≤ (if (zdistInf d L x₀ : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
                (zdistInf d L x₀ : ℝ) ^ σ * bB d L W 0 x₀ else 0) +
              (zdistInf d L x₀ : ℝ) ^ (-D)) :
    |∑ u, Θ₀ u * f (Chain_gt R g (u - x₀))| ≤
      (∑ x, ((zdistInf d L x : ℝ) / zdistInf d L x₀) ^ 2 * ‖g x‖) *
        ((if (zdistInf d L x₀ : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
            (zdistInf d L x₀ : ℝ) ^ σ * bB d L W 0 x₀ else 0) + (zdistInf d L x₀ : ℝ) ^ (-D)) := by
  have h := hcan R hR (fun v => f (Chain_gt R g v))
    (fun x => by simp only [Chain_gt_symm R g hg2 x])
    (fun x hx => by simp only [Chain_gt_supp R g x hx, map_zero])
    (by rw [← map_sum, Chain_gt_sum, map_zero]) x₀ hx₀
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hΨ)
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : x = 0
  · rw [hx, (zdistInf_eq_zero_iff d L).2 rfl]
    simp
  · refine mul_le_mul_of_nonneg_left ((hf _).trans (Chain_gt_norm R g x hx)) (by positivity)

/-- The cancellation term: `‖Σ_u Θ_{0u} g̃(u - x₀)‖ ≤ 2 (Σ_x (‖x‖/‖x₀‖)² ‖g(x)‖) Ψ`, where `Ψ`
is the right side factor of the cancellation property. -/
private theorem Chain_T1 {d L W : ℕ} [NeZero L] {σ c η D : ℝ} {Θ₀ : Zd d L → ℝ}
    (hcan : Chain_ThetaCan d L W η σ c D Θ₀) (R : ℕ) (hR : W ≤ R)
    (g : Zd d L → ℂ) (hg2 : ∀ v, g (-v) = g v) (x₀ : Zd d L)
    (hx₀ : (R : ℝ) ^ (1 + c) ≤ zdistInf d L x₀)
    (hΨ : 0 ≤ (if (zdistInf d L x₀ : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
                (zdistInf d L x₀ : ℝ) ^ σ * bB d L W 0 x₀ else 0) +
              (zdistInf d L x₀ : ℝ) ^ (-D)) :
    ‖∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀)‖ ≤
      2 * (∑ x, ((zdistInf d L x : ℝ) / zdistInf d L x₀) ^ 2 * ‖g x‖) *
        ((if (zdistInf d L x₀ : ℝ) ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
            (zdistInf d L x₀ : ℝ) ^ σ * bB d L W 0 x₀ else 0) + (zdistInf d L x₀ : ℝ) ^ (-D)) := by
  have h1 := Chain_T1_part hcan R hR g hg2 x₀ hx₀ Complex.reLm Complex.abs_re_le_norm hΨ
  have h2 := Chain_T1_part hcan R hR g hg2 x₀ hx₀ Complex.imLm Complex.abs_im_le_norm hΨ
  have hre : (∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀)).re =
      ∑ u, Θ₀ u * Complex.reLm (Chain_gt R g (u - x₀)) := by
    rw [Complex.re_sum]; simp
  have him : (∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀)).im =
      ∑ u, Θ₀ u * Complex.imLm (Chain_gt R g (u - x₀)) := by
    rw [Complex.im_sum]; simp
  have := Complex.norm_le_abs_re_add_abs_im (∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀))
  rw [hre, him] at this
  linarith

/-- `(r/2)^{-p} = 2^p r^{-p}` for `r > 0`. -/
private theorem Chain_half_rpow {r : ℝ} (hr : 0 < r) (p : ℝ) :
    (r / 2) ^ (-p) = 2 ^ p * r ^ (-p) := by
  rw [div_eq_mul_inv, Real.mul_rpow hr.le (by norm_num), Real.inv_rpow (by norm_num),
    ← Real.rpow_neg (by norm_num), neg_neg]
  ring

/-- The convolution of `⟨·⟩^{-(d-2)}` with `⟨· - x₀⟩^{-(2d-4)}` outside the ball of radius `R`
about `x₀`: at most `C (⟨x₀⟩^{-(d-2)} R^{-(d-4)} + ⟨x₀⟩^{-(2d-6)})`. -/
private theorem Chain_conv2 (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (R : ℕ), 1 ≤ R → ∀ x₀ : Zd d L,
      ∑ u ∈ Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)),
        brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) ≤
      C * (brk d L W x₀ 0 ^ (-((d : ℝ) - 2)) * (R : ℝ) ^ (-((d : ℝ) - 4)) +
        brk d L W x₀ 0 ^ (-(2 * (d : ℝ) - 6))) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, hC₁, h1⟩ := Chain_ballLe d ((d : ℝ) - 2) (by linarith) (by linarith)
  obtain ⟨C₀, hC₀, h0⟩ := Chain_tailSum d (2 * (d : ℝ) - 4) (by linarith)
  refine ⟨2 ^ ((d : ℝ) - 2) * C₀ + 2 ^ (2 * (d : ℝ) - 6) * C₁, by positivity,
    fun L W _ hW R hR x₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set r := brk d L W x₀ 0 with hr
  have hr0 : 0 < r := Chain_brk_pos d L W hW x₀ 0
  set u₀ := r / 2 with hu₀
  have hu0 : 0 < u₀ := by positivity
  have hpt : ∀ u : Zd d L, (if R < zdistInf d L (u - x₀) then
      brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) else 0) ≤
      (if R < zdistInf d L (u - x₀) then u₀ ^ (-((d : ℝ) - 2)) *
        brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) else 0) +
      (if brk d L W u 0 ≤ u₀ then brk d L W u 0 ^ (-((d : ℝ) - 2)) * u₀ ^ (-(2 * (d : ℝ) - 4))
        else 0) := by
    intro u
    have hA := Chain_brk_pos d L W hW u 0
    have hG := Chain_brk_pos d L W hW u x₀
    have t := Chain_brk_tri d L W u x₀ 0
    have h2 : 0 ≤ (if brk d L W u 0 ≤ u₀ then brk d L W u 0 ^ (-((d : ℝ) - 2)) *
        u₀ ^ (-(2 * (d : ℝ) - 4)) else 0) := by split_ifs <;> positivity
    have h1' : 0 ≤ (if R < zdistInf d L (u - x₀) then u₀ ^ (-((d : ℝ) - 2)) *
        brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) else 0) := by split_ifs <;> positivity
    by_cases hS : R < zdistInf d L (u - x₀)
    · rw [if_pos hS, if_pos hS]
      by_cases hu : u₀ ≤ brk d L W u 0
      · have : brk d L W u 0 ^ (-((d : ℝ) - 2)) ≤ u₀ ^ (-((d : ℝ) - 2)) :=
          Real.rpow_le_rpow_of_nonpos hu0 hu (by linarith)
        have := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hG.le (-(2 * (d : ℝ) - 4)))
        linarith
      · rw [not_le] at hu
        rw [if_pos hu.le]
        have hxu : u₀ ≤ brk d L W u x₀ := by linarith
        have : brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) ≤ u₀ ^ (-(2 * (d : ℝ) - 4)) :=
          Real.rpow_le_rpow_of_nonpos hu0 hxu (by linarith)
        have := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hA.le (-((d : ℝ) - 2)))
        have h1'' : 0 ≤ u₀ ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) := by positivity
        linarith
    · rw [if_neg hS]; linarith
  have hS1 : ∑ u ∈ Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)),
      u₀ ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) ≤
      u₀ ^ (-((d : ℝ) - 2)) * (C₀ * (R : ℝ) ^ (-((d : ℝ) - 4))) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hu0.le _)
    have hsub : Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)) ⊆
        Finset.univ.filter (fun u : Zd d L => (R : ℝ) ≤ brk d L W u x₀) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      unfold brk
      have : (R : ℝ) < zdistInf d L (u - x₀) := by exact_mod_cast hu
      linarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ =>
      Real.rpow_nonneg (Chain_brk_pos d L W hW u x₀).le _)).trans ?_
    refine (h0 L W hW x₀ R (by linarith)).trans (le_of_eq ?_)
    rw [show (d : ℝ) - (2 * d - 4) = -((d : ℝ) - 4) by ring]
  have hS2 : ∑ u ∈ Finset.univ.filter (fun u : Zd d L => brk d L W u 0 ≤ u₀),
      brk d L W u 0 ^ (-((d : ℝ) - 2)) * u₀ ^ (-(2 * (d : ℝ) - 4)) ≤
      C₁ * u₀ ^ (-(2 * (d : ℝ) - 6)) := by
    rw [← Finset.sum_mul]
    have := mul_le_mul_of_nonneg_right (h1 L W hW 0 u₀ hu0)
      (Real.rpow_nonneg hu0.le (-(2 * (d : ℝ) - 4)))
    refine this.trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.rpow_add hu0, show (d : ℝ) - ((d : ℝ) - 2) + -(2 * d - 4) =
      -(2 * (d : ℝ) - 6) by ring]
  calc ∑ u ∈ Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)),
        brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4))
      = ∑ u, (if R < zdistInf d L (u - x₀) then
        brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) else 0) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ u, ((if R < zdistInf d L (u - x₀) then u₀ ^ (-((d : ℝ) - 2)) *
          brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) else 0) +
        (if brk d L W u 0 ≤ u₀ then brk d L W u 0 ^ (-((d : ℝ) - 2)) *
          u₀ ^ (-(2 * (d : ℝ) - 4)) else 0)) := Finset.sum_le_sum fun u _ => hpt u
    _ = (∑ u ∈ Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)),
          u₀ ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4))) +
        ∑ u ∈ Finset.univ.filter (fun u : Zd d L => brk d L W u 0 ≤ u₀),
          brk d L W u 0 ^ (-((d : ℝ) - 2)) * u₀ ^ (-(2 * (d : ℝ) - 4)) := by
        rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ ≤ u₀ ^ (-((d : ℝ) - 2)) * (C₀ * (R : ℝ) ^ (-((d : ℝ) - 4))) +
        C₁ * u₀ ^ (-(2 * (d : ℝ) - 6)) := by linarith
    _ ≤ _ := by
        rw [hu₀, Chain_half_rpow hr0, Chain_half_rpow hr0]
        have e1 : 0 ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * C₀ * r ^ (-(2 * (d : ℝ) - 6)) := by positivity
        have e2 : 0 ≤ (2 : ℝ) ^ (2 * (d : ℝ) - 6) * C₁ *
            (r ^ (-((d : ℝ) - 2)) * (R : ℝ) ^ (-((d : ℝ) - 4))) := by positivity
        nlinarith [e1, e2]


/-- The near case: without cancellation, `|Σ_u Θ_{0u} g(u - x₀)| ≤ C W^σ (Λ W^{-d}) W^{-d}`, for
`|g(v)| ≤ Λ W^{-4} ⟨v⟩^{-(2d-4)} + Λ W^{-d} 1_{v=0}`. -/
private theorem Chain_near (d : ℕ) (hd : 6 ≤ d) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (Θ₀ : Zd d L → ℝ) (η : ℝ),
      (∀ u, |Θ₀ u| ≤ thetaBound W η σ (d : ℝ) 0 u) → ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4)) +
        (if v = 0 then Λ * (W : ℝ) ^ (-(d : ℝ)) else 0)) →
      ∀ x₀ : Zd d L, ‖∑ u, (Θ₀ u : ℂ) * g (u - x₀)‖ ≤
        C * (W : ℝ) ^ σ * (Λ * (W : ℝ) ^ (-(d : ℝ))) * (W : ℝ) ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₀, hC₀, h0⟩ := Chain_sumAll d (2 * (d : ℝ) - 4) (by linarith)
  refine ⟨2 * (C₀ + 1), by positivity, fun L W _ hW Θ₀ η hdec g Λ hΛ hg x₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hpt : ∀ u, |Θ₀ u| ≤ 2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-(d : ℝ)) := fun u =>
    (Chain_theta_pt hW hσ.le hdec u).trans
      (mul_le_mul_of_nonneg_left (Chain_bB_le hW u (by omega)) (by positivity))
  have hsum : ∑ v, ‖g v‖ ≤
      Λ * (W : ℝ) ^ (-4 : ℝ) * ∑ v, brk d L W v 0 ^ (-(2 * (d : ℝ) - 4)) +
        Λ * (W : ℝ) ^ (-(d : ℝ)) := by
    refine (Finset.sum_le_sum fun v _ => hg v).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Zd d L), Finset.mul_sum]
    simp
  calc ‖∑ u, (Θ₀ u : ℂ) * g (u - x₀)‖ ≤ ∑ u, ‖(Θ₀ u : ℂ) * g (u - x₀)‖ := norm_sum_le _ _
    _ ≤ ∑ u, 2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-(d : ℝ)) * ‖g (u - x₀)‖ := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hpt u) (norm_nonneg _)
    _ = 2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-(d : ℝ)) * ∑ v, ‖g v‖ := by
        rw [← Finset.mul_sum, Chain_sum_sub (fun v => ‖g v‖) x₀]
    _ ≤ 2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-(d : ℝ)) *
          (Λ * (W : ℝ) ^ (-4 : ℝ) * ∑ v, brk d L W v 0 ^ (-(2 * (d : ℝ) - 4)) +
            Λ * (W : ℝ) ^ (-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-(d : ℝ)) *
          (Λ * (W : ℝ) ^ (-4 : ℝ) * (C₀ * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4))) +
            Λ * (W : ℝ) ^ (-(d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left
          (h0 L W hW 0) (by positivity)) _) (by positivity)
    _ = _ := by
        have : (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)) = (W : ℝ) ^ (-(d : ℝ)) := by
          rw [← Real.rpow_add hW0]; congr 1; ring
        calc 2 * (W : ℝ) ^ σ * (W : ℝ) ^ (-(d : ℝ)) *
            (Λ * (W : ℝ) ^ (-4 : ℝ) * (C₀ * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4))) +
              Λ * (W : ℝ) ^ (-(d : ℝ)))
            = 2 * (W : ℝ) ^ σ * (Λ * (C₀ * ((W : ℝ) ^ (-4 : ℝ) *
                (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4)))) + Λ * (W : ℝ) ^ (-(d : ℝ))) *
              (W : ℝ) ^ (-(d : ℝ)) := by ring
          _ = _ := by rw [this]; ring


/-- `R^{-p} ≤ (4ω)^p r^{-p}` when `r ≤ 4 ω R`, for `p ≥ 0`. -/
private theorem Chain_R_pow {r R ω : ℝ} (hr : 0 < r) (hω : 0 < ω) (hR : r ≤ 4 * ω * R) {p : ℝ}
    (hp : 0 ≤ p) : R ^ (-p) ≤ (4 * ω) ^ p * r ^ (-p) := by
  have h4 : 0 < 4 * ω := by positivity
  have hq : r / (4 * ω) ≤ R := by rw [div_le_iff₀ h4]; linarith
  calc R ^ (-p) ≤ (r / (4 * ω)) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hq (by linarith)
    _ = (4 * ω) ^ p * r ^ (-p) := by
        rw [div_eq_mul_inv, Real.mul_rpow hr.le (by positivity), Real.inv_rpow h4.le,
          ← Real.rpow_neg h4.le, neg_neg]
        ring

/-- `(4 W^σ)^p = 4^p W^{σ p}`. -/
private theorem Chain_four_pow {W σ : ℝ} (hW : 0 < W) (p : ℝ) :
    (4 * W ^ σ) ^ p = 4 ^ p * W ^ (σ * p) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW.le]

/-- A point with `‖v‖_L > R` is not the origin. -/
private theorem Chain_ne_zero_of_lt {d L : ℕ} [NeZero L] {R : ℕ} {v : Zd d L}
    (h : R < zdistInf d L v) : v ≠ 0 := fun hv => by
  rw [hv, (zdistInf_eq_zero_iff d L).2 rfl] at h; omega

/-- The mean `s = Σ_{‖w‖ ≤ R} g(w)` of the truncation: `|s| ≤ Λ W^{-d} η + Λ W^{-4} C R^{-(d-4)}`. -/
private theorem Chain_s_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (R : ℕ), 1 ≤ R →
      ∀ (g : Zd d L → ℂ) (Λ η : ℝ), 0 ≤ Λ →
      (∀ v, v ≠ 0 → ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4))) →
      ‖∑ v, g v‖ ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * η →
      ‖∑ w, (if zdistInf d L w ≤ R then g w else 0)‖ ≤
        Λ * (W : ℝ) ^ (-(d : ℝ)) * η + Λ * (W : ℝ) ^ (-4 : ℝ) * (C * (R : ℝ) ^ (-((d : ℝ) - 4))) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₀, hC₀, h0⟩ := Chain_tailSum d (2 * (d : ℝ) - 4) (by linarith)
  refine ⟨C₀, hC₀, fun L W _ hW R hR g Λ η hΛ hg hs => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hdec : ∑ w, (if zdistInf d L w ≤ R then g w else 0) =
      ∑ v, g v - ∑ w, (if R < zdistInf d L w then g w else 0) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : zdistInf d L w ≤ R
    · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_pos (not_le.mp h)]; ring
  have htail : ‖∑ w, (if R < zdistInf d L w then g w else 0)‖ ≤
      Λ * (W : ℝ) ^ (-4 : ℝ) * (C₀ * (R : ℝ) ^ (-((d : ℝ) - 4))) := by
    calc ‖∑ w, (if R < zdistInf d L w then g w else 0)‖
        ≤ ∑ w, ‖(if R < zdistInf d L w then g w else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ w, (if R < zdistInf d L w then
            Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W w 0 ^ (-(2 * (d : ℝ) - 4)) else 0) := by
          refine Finset.sum_le_sum fun w _ => ?_
          split_ifs with hw
          · exact hg w (Chain_ne_zero_of_lt hw)
          · simp
      _ = ∑ w ∈ Finset.univ.filter (fun w : Zd d L => R < zdistInf d L w),
            Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W w 0 ^ (-(2 * (d : ℝ) - 4)) := by
          rw [Finset.sum_filter]
      _ = Λ * (W : ℝ) ^ (-4 : ℝ) * ∑ w ∈ Finset.univ.filter (fun w : Zd d L => R < zdistInf d L w),
            brk d L W w 0 ^ (-(2 * (d : ℝ) - 4)) := by rw [Finset.mul_sum]
      _ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * (C₀ * (R : ℝ) ^ (-((d : ℝ) - 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsub : Finset.univ.filter (fun w : Zd d L => R < zdistInf d L w) ⊆
              Finset.univ.filter (fun w : Zd d L => (R : ℝ) ≤ brk d L W w 0) := by
            intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
            rw [Chain_brk_zero]
            have : (R : ℝ) < zdistInf d L w := by exact_mod_cast hw
            linarith
          refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ =>
            Real.rpow_nonneg (Chain_brk_pos d L W hW w 0).le _)).trans ?_
          refine (h0 L W hW 0 R (by linarith)).trans (le_of_eq ?_)
          rw [show (d : ℝ) - (2 * d - 4) = -((d : ℝ) - 4) by ring]
  rw [hdec]
  calc ‖∑ v, g v - ∑ w, (if R < zdistInf d L w then g w else 0)‖
      ≤ ‖∑ v, g v‖ + ‖∑ w, (if R < zdistInf d L w then g w else 0)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hs htail


/-- `⟨(u - x₀) - 0⟩ = ⟨u - x₀⟩`. -/
private theorem Chain_brk_sub (d L W : ℕ) [NeZero L] (u x₀ : Zd d L) :
    brk d L W (u - x₀) 0 = brk d L W u x₀ := by
  unfold brk; rw [sub_zero]

/-- `B_{0u} = W^{-2} ⟨u⟩^{-(d-2)}`. -/
private theorem Chain_bB0 (d L W : ℕ) [NeZero L] (u : Zd d L) :
    bB d L W 0 u = (W : ℝ) ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2)) := by
  rw [Chain_bB_eq', Chain_brk_comm]

/-- The outer part of the sum: `|Σ_u Θ_{0u} g(u - x₀) 1(‖u - x₀‖ > R)|` is at most
`C W^{σ(d-3)} (Λ W^{-d}) ⟨x₀⟩^{-d}` when `⟨x₀⟩ ≤ 4 W^σ R`. -/
private theorem Chain_T3 (d : ℕ) (hd : 6 ≤ d) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (Θ₀ : Zd d L → ℝ) (η : ℝ),
      (∀ u, |Θ₀ u| ≤ thetaBound W η σ (d : ℝ) 0 u) → ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, v ≠ 0 → ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4))) →
      ∀ (R : ℕ), 1 ≤ R → ∀ x₀ : Zd d L, brk d L W x₀ 0 ≤ 4 * (W : ℝ) ^ σ * R →
      ‖∑ u, (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0)‖ ≤
        C * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          brk d L W x₀ 0 ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₃, hC₃, h3⟩ := Chain_conv2 d (by omega)
  refine ⟨2 * C₃ * (4 ^ ((d : ℝ) - 4) + 1), by positivity,
    fun L W _ hW Θ₀ η hdec g Λ hΛ hg R hR x₀ hx₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set r := brk d L W x₀ 0 with hr
  have hr0 : 0 < r := Chain_brk_pos d L W hW x₀ 0
  have hrW : (W : ℝ) ≤ r := by rw [hr, Chain_brk_comm]; exact Chain_le_brk d L W 0 x₀
  set ω : ℝ := (W : ℝ) ^ σ with hω
  have hω1 : 1 ≤ ω := Real.one_le_rpow hW1 hσ.le
  have hω0 : 0 < ω := by linarith
  have hterm : ∀ u : Zd d L, ‖(Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0)‖ ≤
      if R < zdistInf d L (u - x₀) then
        (2 * ω * (W : ℝ) ^ (-2 : ℝ)) * (Λ * (W : ℝ) ^ (-4 : ℝ)) *
          (brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4))) else 0 := by
    intro u
    split_ifs with h
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |Θ₀ u| ≤ 2 * ω * ((W : ℝ) ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2))) := by
        rw [← Chain_bB0]; exact Chain_theta_pt hW hσ.le hdec u
      have h2 : ‖g (u - x₀)‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4)) := by
        have := hg (u - x₀) (Chain_ne_zero_of_lt h); rwa [Chain_brk_sub] at this
      calc |Θ₀ u| * ‖g (u - x₀)‖
          ≤ (2 * ω * ((W : ℝ) ^ (-2 : ℝ) * brk d L W u 0 ^ (-((d : ℝ) - 2)))) *
            (Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4))) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hω0.le)
              (mul_nonneg (by positivity) (Real.rpow_nonneg (Chain_brk_pos d L W hW u 0).le _)))
        _ = _ := by ring
    · simp
  have hsum : ‖∑ u, (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0)‖ ≤
      (2 * ω * (W : ℝ) ^ (-2 : ℝ)) * (Λ * (W : ℝ) ^ (-4 : ℝ)) *
        ∑ u ∈ Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)),
          (brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4))) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun u _ => hterm u).trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
  have hconv := h3 L W hW R hR x₀
  have hRp := Chain_R_pow hr0 hω0 hx₀ (p := (d : ℝ) - 4) (by linarith)
  have e1 : r ^ (-((d : ℝ) - 2)) * (R : ℝ) ^ (-((d : ℝ) - 4)) ≤
      (4 * ω) ^ ((d : ℝ) - 4) * r ^ (-(2 * (d : ℝ) - 6)) := by
    calc r ^ (-((d : ℝ) - 2)) * (R : ℝ) ^ (-((d : ℝ) - 4))
        ≤ r ^ (-((d : ℝ) - 2)) * ((4 * ω) ^ ((d : ℝ) - 4) * r ^ (-((d : ℝ) - 4))) :=
          mul_le_mul_of_nonneg_left hRp (Real.rpow_nonneg hr0.le _)
      _ = (4 * ω) ^ ((d : ℝ) - 4) * r ^ (-(2 * (d : ℝ) - 6)) := by
          rw [mul_left_comm, ← Real.rpow_add hr0]; congr 2; ring
  have hr6 : (W : ℝ) ^ (-6 : ℝ) * r ^ (-(2 * (d : ℝ) - 6)) ≤ (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by
    have : r ^ (-(2 * (d : ℝ) - 6)) = r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 6)) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    rw [this]
    have h2 : r ^ (-((d : ℝ) - 6)) ≤ (W : ℝ) ^ (-((d : ℝ) - 6)) :=
      Real.rpow_le_rpow_of_nonpos hW0 hrW (by linarith)
    have h3 : (W : ℝ) ^ (-6 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 6)) = (W : ℝ) ^ (-(d : ℝ)) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    calc (W : ℝ) ^ (-6 : ℝ) * (r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 6)))
        = r ^ (-(d : ℝ)) * ((W : ℝ) ^ (-6 : ℝ) * r ^ (-((d : ℝ) - 6))) := by ring
      _ ≤ r ^ (-(d : ℝ)) * ((W : ℝ) ^ (-6 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 6))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
      _ = (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by rw [h3]; ring
  have hω4 : (4 * ω) ^ ((d : ℝ) - 4) = 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 4)) :=
    Chain_four_pow hW0 _
  have hωe : ω * (W : ℝ) ^ (σ * ((d : ℝ) - 4)) = (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := by
    rw [hω, ← Real.rpow_add hW0]; congr 1; ring
  have hωle : ω ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := by
    rw [hω]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
  have hWe : 1 ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 4)) := Real.one_le_rpow hW1 (by nlinarith)
  -- assemble
  have hbr : 0 ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
  have hb2 : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-4 : ℝ) = (W : ℝ) ^ (-6 : ℝ) := by
    rw [← Real.rpow_add hW0]; norm_num
  have hbracket : ∑ u ∈ Finset.univ.filter (fun u : Zd d L => R < zdistInf d L (u - x₀)),
      (brk d L W u 0 ^ (-((d : ℝ) - 2)) * brk d L W u x₀ ^ (-(2 * (d : ℝ) - 4))) ≤
      C₃ * (((4 * ω) ^ ((d : ℝ) - 4) + 1) * r ^ (-(2 * (d : ℝ) - 6))) := by
    refine hconv.trans (mul_le_mul_of_nonneg_left ?_ hC₃)
    have : r ^ (-(2 * (d : ℝ) - 6)) ≥ 0 := Real.rpow_nonneg hr0.le _
    nlinarith
  calc ‖∑ u, (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0)‖
      ≤ (2 * ω * (W : ℝ) ^ (-2 : ℝ)) * (Λ * (W : ℝ) ^ (-4 : ℝ)) *
        (C₃ * (((4 * ω) ^ ((d : ℝ) - 4) + 1) * r ^ (-(2 * (d : ℝ) - 6)))) :=
        hsum.trans (mul_le_mul_of_nonneg_left hbracket (by positivity))
    _ = 2 * C₃ * ω * ((4 * ω) ^ ((d : ℝ) - 4) + 1) * Λ *
          ((W : ℝ) ^ (-6 : ℝ) * r ^ (-(2 * (d : ℝ) - 6))) := by
        rw [← hb2]; ring
    _ ≤ 2 * C₃ * ω * ((4 * ω) ^ ((d : ℝ) - 4) + 1) * Λ *
          ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left hr6 (by positivity)
    _ ≤ 2 * C₃ * (4 ^ ((d : ℝ) - 4) + 1) * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) *
          (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) := by
        have key : ω * ((4 * ω) ^ ((d : ℝ) - 4) + 1) ≤
            (4 ^ ((d : ℝ) - 4) + 1) * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := by
          rw [hω4]
          have h4 : (0 : ℝ) ≤ 4 ^ ((d : ℝ) - 4) := by positivity
          calc ω * (4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 4)) + 1)
              = 4 ^ ((d : ℝ) - 4) * (ω * (W : ℝ) ^ (σ * ((d : ℝ) - 4))) + ω := by ring
            _ ≤ 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) +
                (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := by rw [hωe]; linarith
            _ = _ := by ring
        have hnn : 0 ≤ 2 * C₃ * Λ * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) := by positivity
        calc 2 * C₃ * ω * ((4 * ω) ^ ((d : ℝ) - 4) + 1) * Λ * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)))
            = (2 * C₃ * Λ * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)))) *
                (ω * ((4 * ω) ^ ((d : ℝ) - 4) + 1)) := by ring
          _ ≤ (2 * C₃ * Λ * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)))) *
                ((4 ^ ((d : ℝ) - 4) + 1) * (W : ℝ) ^ (σ * ((d : ℝ) - 3))) :=
              mul_le_mul_of_nonneg_left key hnn
          _ = _ := by ring


/-- `W^{-6} r^{-(2d-6)} ≤ W^{-d} r^{-d}` for `r ≥ W` and `d ≥ 6`. -/
private theorem Chain_w6 {W r : ℝ} (hW : 0 < W) (hrW : W ≤ r) {d : ℕ} (hd : 6 ≤ d) :
    W ^ (-6 : ℝ) * r ^ (-(2 * (d : ℝ) - 6)) ≤ W ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : 0 < r := lt_of_lt_of_le hW hrW
  have : r ^ (-(2 * (d : ℝ) - 6)) = r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 6)) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  rw [this]
  have h2 : r ^ (-((d : ℝ) - 6)) ≤ W ^ (-((d : ℝ) - 6)) :=
    Real.rpow_le_rpow_of_nonpos hW hrW (by linarith)
  have h3 : W ^ (-6 : ℝ) * W ^ (-((d : ℝ) - 6)) = W ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  calc W ^ (-6 : ℝ) * (r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 6)))
      = r ^ (-(d : ℝ)) * (W ^ (-6 : ℝ) * r ^ (-((d : ℝ) - 6))) := by ring
    _ ≤ r ^ (-(d : ℝ)) * (W ^ (-6 : ℝ) * W ^ (-((d : ℝ) - 6))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
          (by positivity)
    _ = W ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by rw [h3]; ring

/-- `W^{-4} r^{-(2d-4)} ≤ W^{-d} r^{-d}` for `r ≥ W` and `d ≥ 4`. -/
private theorem Chain_w4 {W r : ℝ} (hW : 0 < W) (hrW : W ≤ r) {d : ℕ} (hd : 4 ≤ d) :
    W ^ (-4 : ℝ) * r ^ (-(2 * (d : ℝ) - 4)) ≤ W ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : 0 < r := lt_of_lt_of_le hW hrW
  have : r ^ (-(2 * (d : ℝ) - 4)) = r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 4)) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  rw [this]
  have h2 : r ^ (-((d : ℝ) - 4)) ≤ W ^ (-((d : ℝ) - 4)) :=
    Real.rpow_le_rpow_of_nonpos hW hrW (by linarith)
  have h3 : W ^ (-4 : ℝ) * W ^ (-((d : ℝ) - 4)) = W ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  calc W ^ (-4 : ℝ) * (r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 4)))
      = r ^ (-(d : ℝ)) * (W ^ (-4 : ℝ) * r ^ (-((d : ℝ) - 4))) := by ring
    _ ≤ r ^ (-(d : ℝ)) * (W ^ (-4 : ℝ) * W ^ (-((d : ℝ) - 4))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
          (by positivity)
    _ = W ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by rw [h3]; ring

/-- If `ρ ≤ η^{-1/2} W^{1+σ}` then `ρ² η ≤ W^{2+2σ}`. -/
private theorem Chain_eta_le {ρ η W σ : ℝ} (hρ : 0 ≤ ρ) (hη : 0 < η) (hW : 0 < W)
    (h : ρ ≤ η ^ (-(1 / 2 : ℝ)) * W ^ (1 + σ)) : ρ ^ 2 * η ≤ W ^ (2 + 2 * σ) := by
  have hs : 0 < η ^ (1 / 2 : ℝ) := by positivity
  have hss : (η ^ (1 / 2 : ℝ)) ^ 2 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]; norm_num
  rw [Real.rpow_neg hη.le] at h
  have h2 : ρ * η ^ (1 / 2 : ℝ) ≤ W ^ (1 + σ) := by
    have := mul_le_mul_of_nonneg_right h hs.le
    calc ρ * η ^ (1 / 2 : ℝ) ≤ (η ^ (1 / 2 : ℝ))⁻¹ * W ^ (1 + σ) * η ^ (1 / 2 : ℝ) := this
      _ = W ^ (1 + σ) := by field_simp
  have h3 : (ρ * η ^ (1 / 2 : ℝ)) ^ 2 ≤ (W ^ (1 + σ)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  calc ρ ^ 2 * η = (ρ * η ^ (1 / 2 : ℝ)) ^ 2 := by rw [mul_pow, hss]
    _ ≤ (W ^ (1 + σ)) ^ 2 := h3
    _ = W ^ (2 + 2 * σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; congr 1; push_cast; ring

/-- The point mass term: `|Θ_{0 x₀} s| ≤ C W^{σ(d-3)} (Λ W^{-d}) ⟨x₀⟩^{-d}` for the mean `s` of
the truncation. -/
private theorem Chain_T2 (d : ℕ) (hd : 6 ≤ d) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (Θ₀ : Zd d L → ℝ) (η : ℝ), 0 < η → η ≤ 1 →
      (∀ u, |Θ₀ u| ≤ thetaBound W η σ (d : ℝ) 0 u) → ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, v ≠ 0 → ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4))) →
      ‖∑ v, g v‖ ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * η →
      ∀ (R : ℕ), 1 ≤ R → ∀ x₀ : Zd d L, (W : ℝ) ≤ zdistInf d L x₀ →
        brk d L W x₀ 0 ≤ 4 * (W : ℝ) ^ σ * R →
      ‖(Θ₀ x₀ : ℂ) * ∑ w, (if zdistInf d L w ≤ R then g w else 0)‖ ≤
        C * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          brk d L W x₀ 0 ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₀, hC₀, hs⟩ := Chain_s_bound d (by omega)
  refine ⟨5 + 2 * 4 ^ ((d : ℝ) - 4) * C₀, by positivity,
    fun L W _ hW Θ₀ η hη0 hη1 hdec g Λ hΛ hg hg3 R hR x₀ hρ hx₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set r := brk d L W x₀ 0 with hr
  have hr0 : 0 < r := Chain_brk_pos d L W hW x₀ 0
  have hrW : (W : ℝ) ≤ r := by rw [hr, Chain_brk_comm]; exact Chain_le_brk d L W 0 x₀
  set ρ : ℝ := (zdistInf d L x₀ : ℝ) with hρdef
  have hrρ : r = ρ + W := by rw [hr, Chain_brk_zero]
  have hρ2 : r ≤ 2 * ρ := by linarith
  set ω : ℝ := (W : ℝ) ^ σ with hω
  have hω1 : 1 ≤ ω := Real.one_le_rpow hW1 hσ.le
  have hω0 : 0 < ω := by linarith
  have hρ0 : 0 ≤ ρ := Nat.cast_nonneg _
  have hσ4 : 0 ≤ σ * ((d : ℝ) - 4) := mul_nonneg hσ.le (by linarith)
  have hσ6 : 0 ≤ σ * ((d : ℝ) - 6) := mul_nonneg hσ.le (by linarith)
  -- the pointwise bound for `Θ₀ x₀`
  have hb : bB d L W 0 x₀ = (W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2)) := Chain_bB0 d L W x₀
  have hΘ : |Θ₀ x₀| ≤ (if ρ ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then
      ω * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) else 0) + r ^ (-(d : ℝ)) := by
    have h1 := hdec x₀
    unfold thetaBound at h1
    have hs0 : zdistInf d L (0 - x₀) = zdistInf d L x₀ := by rw [zero_sub, zdistInf_neg]
    rw [hs0, ← hρdef, hb, ← hrρ] at h1
    exact h1
  have hrd : r ^ (-((d : ℝ) - 2)) = r ^ (-(d : ℝ)) * r ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hr0]; congr 1; ring
  have e2 : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 + 2 * σ) = (W : ℝ) ^ (2 * σ) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have e3 : ω * (W : ℝ) ^ (2 * σ) = (W : ℝ) ^ (3 * σ) := by
    rw [hω, ← Real.rpow_add hW0]; congr 1; ring
  have hrd0 : 0 ≤ r ^ (-(d : ℝ)) := Real.rpow_nonneg hr0.le _
  have hΘη : |Θ₀ x₀| * η ≤ (1 + 4 * (W : ℝ) ^ (3 * σ)) * r ^ (-(d : ℝ)) := by
    by_cases hY : ρ ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ)
    · rw [if_pos hY] at hΘ
      have hηρ := Chain_eta_le hρ0 hη0 hW0 hY
      have hr2 : r ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
      have hηr : r ^ 2 * η ≤ 4 * (W : ℝ) ^ (2 + 2 * σ) := by
        calc r ^ 2 * η ≤ (4 * ρ ^ 2) * η := mul_le_mul_of_nonneg_right hr2 hη0.le
          _ = 4 * (ρ ^ 2 * η) := by ring
          _ ≤ 4 * (W : ℝ) ^ (2 + 2 * σ) := by linarith
      have h4 : ω * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) * η ≤
          4 * (W : ℝ) ^ (3 * σ) * r ^ (-(d : ℝ)) := by
        rw [hrd]
        calc ω * ((W : ℝ) ^ (-2 : ℝ) * (r ^ (-(d : ℝ)) * r ^ 2)) * η
            = ω * (W : ℝ) ^ (-2 : ℝ) * r ^ (-(d : ℝ)) * (r ^ 2 * η) := by ring
          _ ≤ ω * (W : ℝ) ^ (-2 : ℝ) * r ^ (-(d : ℝ)) * (4 * (W : ℝ) ^ (2 + 2 * σ)) :=
              mul_le_mul_of_nonneg_left hηr (by positivity)
          _ = 4 * (ω * ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 + 2 * σ))) * r ^ (-(d : ℝ)) := by ring
          _ = 4 * (W : ℝ) ^ (3 * σ) * r ^ (-(d : ℝ)) := by rw [e2, e3]
      calc |Θ₀ x₀| * η ≤ (ω * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) + r ^ (-(d : ℝ))) * η :=
            mul_le_mul_of_nonneg_right hΘ hη0.le
        _ = ω * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) * η + r ^ (-(d : ℝ)) * η := by ring
        _ ≤ 4 * (W : ℝ) ^ (3 * σ) * r ^ (-(d : ℝ)) + r ^ (-(d : ℝ)) * 1 := by
            refine add_le_add h4 (mul_le_mul_of_nonneg_left hη1 hrd0)
        _ = _ := by ring
    · rw [if_neg hY, zero_add] at hΘ
      calc |Θ₀ x₀| * η ≤ r ^ (-(d : ℝ)) * 1 :=
            mul_le_mul hΘ hη1 hη0.le hrd0
        _ ≤ (1 + 4 * (W : ℝ) ^ (3 * σ)) * r ^ (-(d : ℝ)) := by
            have : 0 ≤ 4 * (W : ℝ) ^ (3 * σ) * r ^ (-(d : ℝ)) := by positivity
            nlinarith
  -- the bound for `Θ₀ x₀ · R^{-(d-4)}`
  have hΘ0 : |Θ₀ x₀| ≤ ω * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) + r ^ (-(d : ℝ)) := by
    refine hΘ.trans (add_le_add ?_ le_rfl)
    split_ifs
    · exact le_rfl
    · positivity
  have hRp := Chain_R_pow hr0 hω0 hx₀ (p := (d : ℝ) - 4) (by linarith)
  have hω4 : (4 * ω) ^ ((d : ℝ) - 4) = 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 4)) :=
    Chain_four_pow hW0 _
  have hωe : ω * (W : ℝ) ^ (σ * ((d : ℝ) - 4)) = (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := by
    rw [hω, ← Real.rpow_add hW0]; congr 1; ring
  have hWe : 1 ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 4)) := Real.one_le_rpow hW1 (by linarith)
  have hΘR : |Θ₀ x₀| * (W : ℝ) ^ (-4 : ℝ) * (R : ℝ) ^ (-((d : ℝ) - 4)) ≤
      (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) * (2 * 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 3))) := by
    have hw6 := Chain_w6 hW0 hrW hd
    have hw4 := Chain_w4 hW0 hrW (by omega : 4 ≤ d)
    have hR' : (R : ℝ) ^ (-((d : ℝ) - 4)) ≤ (4 * ω) ^ ((d : ℝ) - 4) * r ^ (-((d : ℝ) - 4)) := hRp
    have hrr : r ^ (-((d : ℝ) - 2)) * r ^ (-((d : ℝ) - 4)) = r ^ (-(2 * (d : ℝ) - 6)) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have hrr2 : r ^ (-(d : ℝ)) * r ^ (-((d : ℝ) - 4)) = r ^ (-(2 * (d : ℝ) - 4)) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have hA : 0 ≤ (W : ℝ) ^ (-4 : ℝ) := by positivity
    have hω4' : 0 ≤ (4 * ω) ^ ((d : ℝ) - 4) := by positivity
    have hWW : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-4 : ℝ) = (W : ℝ) ^ (-6 : ℝ) := by
      rw [← Real.rpow_add hW0]; norm_num
    calc |Θ₀ x₀| * (W : ℝ) ^ (-4 : ℝ) * (R : ℝ) ^ (-((d : ℝ) - 4))
        ≤ (ω * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) + r ^ (-(d : ℝ))) * (W : ℝ) ^ (-4 : ℝ) *
          ((4 * ω) ^ ((d : ℝ) - 4) * r ^ (-((d : ℝ) - 4))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hΘ0 hA) hR'
            (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = (4 * ω) ^ ((d : ℝ) - 4) * (ω * ((W : ℝ) ^ (-6 : ℝ) * r ^ (-(2 * (d : ℝ) - 6))) +
            (W : ℝ) ^ (-4 : ℝ) * r ^ (-(2 * (d : ℝ) - 4))) := by
          rw [← hrr, ← hrr2, ← hWW]; ring
      _ ≤ (4 * ω) ^ ((d : ℝ) - 4) * (ω * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) +
            (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ hw4) hω4'
          exact mul_le_mul_of_nonneg_left hw6 hω0.le
      _ = (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) * ((4 * ω) ^ ((d : ℝ) - 4) * (ω + 1)) := by ring
      _ ≤ (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) *
            (2 * 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 3))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hω4]
          have h4 : (0 : ℝ) ≤ 4 ^ ((d : ℝ) - 4) := by positivity
          have hωle : ω ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := by
            rw [hω]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
          calc 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 4)) * (ω + 1)
              = 4 ^ ((d : ℝ) - 4) * ((W : ℝ) ^ (σ * ((d : ℝ) - 4)) * ω +
                  (W : ℝ) ^ (σ * ((d : ℝ) - 4))) := by ring
            _ ≤ 4 ^ ((d : ℝ) - 4) * ((W : ℝ) ^ (σ * ((d : ℝ) - 3)) +
                  (W : ℝ) ^ (σ * ((d : ℝ) - 3))) := by
                refine mul_le_mul_of_nonneg_left ?_ h4
                have h5 : (W : ℝ) ^ (σ * ((d : ℝ) - 4)) ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3)) :=
                  Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
                rw [mul_comm, hωe]; linarith
            _ = _ := by ring
  -- assemble
  have hsb := hs L W hW R hR g Λ η hΛ hg hg3
  have hη2 : 1 ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3)) := Real.one_le_rpow hW1 (by linarith)
  have h3σ : (W : ℝ) ^ (3 * σ) ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3)) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  calc ‖(Θ₀ x₀ : ℂ) * ∑ w, (if zdistInf d L w ≤ R then g w else 0)‖
      = |Θ₀ x₀| * ‖∑ w, (if zdistInf d L w ≤ R then g w else 0)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |Θ₀ x₀| * (Λ * (W : ℝ) ^ (-(d : ℝ)) * η +
          Λ * (W : ℝ) ^ (-4 : ℝ) * (C₀ * (R : ℝ) ^ (-((d : ℝ) - 4)))) :=
        mul_le_mul_of_nonneg_left hsb (abs_nonneg _)
    _ = Λ * (W : ℝ) ^ (-(d : ℝ)) * (|Θ₀ x₀| * η) +
          Λ * C₀ * (|Θ₀ x₀| * (W : ℝ) ^ (-4 : ℝ) * (R : ℝ) ^ (-((d : ℝ) - 4))) := by ring
    _ ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * ((1 + 4 * (W : ℝ) ^ (3 * σ)) * r ^ (-(d : ℝ))) +
          Λ * C₀ * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) *
            (2 * 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 3)))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hΘη (by positivity))
          (mul_le_mul_of_nonneg_left hΘR (by positivity))
    _ ≤ _ := by
        have hnn : 0 ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) := by positivity
        have e : Λ * (W : ℝ) ^ (-(d : ℝ)) * ((1 + 4 * (W : ℝ) ^ (3 * σ)) * r ^ (-(d : ℝ))) +
            Λ * C₀ * ((W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ)) *
              (2 * 4 ^ ((d : ℝ) - 4) * (W : ℝ) ^ (σ * ((d : ℝ) - 3)))) =
            (Λ * (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) *
              ((1 + 4 * (W : ℝ) ^ (3 * σ)) + 2 * 4 ^ ((d : ℝ) - 4) * C₀ *
                (W : ℝ) ^ (σ * ((d : ℝ) - 3))) := by ring
        rw [e]
        have e' : (5 + 2 * 4 ^ ((d : ℝ) - 4) * C₀) * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) *
            (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) =
            (Λ * (W : ℝ) ^ (-(d : ℝ)) * r ^ (-(d : ℝ))) *
              ((5 + 2 * 4 ^ ((d : ℝ) - 4) * C₀) * (W : ℝ) ^ (σ * ((d : ℝ) - 3))) := by ring
        rw [e']
        refine mul_le_mul_of_nonneg_left ?_ hnn
        have h4C : 0 ≤ 2 * 4 ^ ((d : ℝ) - 4) * C₀ := by positivity
        nlinarith

/-- The second moment of `g`: `Σ_x (‖x‖/ρ)² ‖g(x)‖ ≤ ρ^{-2} Λ W^{-4} C (L + W)^σ
W^{d - (2d-6) - σ}`. -/
private theorem Chain_S_bound (d : ℕ) (hd : 6 ≤ d) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, v ≠ 0 → ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4))) →
      ∀ ρ : ℝ, 0 < ρ →
      ∑ x, ((zdistInf d L x : ℝ) / ρ) ^ 2 * ‖g x‖ ≤
        ρ ^ (-2 : ℝ) * (Λ * (W : ℝ) ^ (-4 : ℝ)) *
          (C * ((L : ℝ) + W) ^ σ * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6) - σ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC, h⟩ := Chain_sumLe d (2 * (d : ℝ) - 6) σ hσ (by linarith)
  refine ⟨C, hC, fun L W _ hW g Λ hΛ hg ρ hρ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < (L : ℝ) + W := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    linarith
  have hpt : ∀ x : Zd d L, ((zdistInf d L x : ℝ) / ρ) ^ 2 * ‖g x‖ ≤
      ρ ^ (-2 : ℝ) * (Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W x 0 ^ (-(2 * (d : ℝ) - 6))) := by
    intro x
    have ht := Chain_brk_pos d L W hW x 0
    by_cases hx0 : x = 0
    · rw [hx0, (zdistInf_eq_zero_iff d L).2 rfl]
      have : 0 ≤ brk d L W 0 0 ^ (-(2 * (d : ℝ) - 6)) := Real.rpow_nonneg (hx0 ▸ ht).le _
      simp only [Nat.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul]
      positivity
    have h1 : ((zdistInf d L x : ℝ) / ρ) ^ 2 = ρ ^ (-2 : ℝ) * (zdistInf d L x : ℝ) ^ 2 := by
      rw [div_pow, Real.rpow_neg hρ.le, ← Real.rpow_natCast ρ 2]; push_cast; ring
    have h2 : (zdistInf d L x : ℝ) ^ 2 ≤ brk d L W x 0 ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Chain_zd_le_brk d L W x) 2
    have h3 : brk d L W x 0 ^ 2 * brk d L W x 0 ^ (-(2 * (d : ℝ) - 4)) =
        brk d L W x 0 ^ (-(2 * (d : ℝ) - 6)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht]; congr 1; push_cast; ring
    rw [h1]
    calc ρ ^ (-2 : ℝ) * (zdistInf d L x : ℝ) ^ 2 * ‖g x‖
        ≤ ρ ^ (-2 : ℝ) * (zdistInf d L x : ℝ) ^ 2 *
          (Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W x 0 ^ (-(2 * (d : ℝ) - 4))) :=
          mul_le_mul_of_nonneg_left (hg x hx0) (by positivity)
      _ ≤ ρ ^ (-2 : ℝ) * brk d L W x 0 ^ 2 *
          (Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W x 0 ^ (-(2 * (d : ℝ) - 4))) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hρ.le _)) (by positivity)
      _ = ρ ^ (-2 : ℝ) * (Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W x 0 ^ (-(2 * (d : ℝ) - 6))) := by
          rw [← h3]; ring
  have hsum : ∑ x : Zd d L, brk d L W x 0 ^ (-(2 * (d : ℝ) - 6)) ≤
      C * ((L : ℝ) + W) ^ σ * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6) - σ) := by
    have := h L W hW 0 ((L : ℝ) + W) hL0
    have e : Finset.univ.filter (fun y : Zd d L => brk d L W y 0 ≤ (L : ℝ) + W) = Finset.univ := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Chain_brk_le d L W y 0
    rwa [e] at this
  calc ∑ x, ((zdistInf d L x : ℝ) / ρ) ^ 2 * ‖g x‖
      ≤ ∑ x : Zd d L, ρ ^ (-2 : ℝ) * (Λ * (W : ℝ) ^ (-4 : ℝ) *
          brk d L W x 0 ^ (-(2 * (d : ℝ) - 6))) := Finset.sum_le_sum fun x _ => hpt x
    _ = ρ ^ (-2 : ℝ) * (Λ * (W : ℝ) ^ (-4 : ℝ)) *
          ∑ x : Zd d L, brk d L W x 0 ^ (-(2 * (d : ℝ) - 6)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)


/-- `ρ^{-p} ≤ 2^p r^{-p}` when `r ≤ 2ρ`, for `p ≥ 0`. -/
private theorem Chain_rho_pow {r ρ : ℝ} (hr : 0 < r) (h : r ≤ 2 * ρ) {p : ℝ} (hp : 0 ≤ p) :
    ρ ^ (-p) ≤ 2 ^ p * r ^ (-p) := by
  have hρ : 0 < ρ := by linarith
  calc ρ ^ (-p) ≤ (r / 2) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    _ = 2 ^ p * r ^ (-p) := Chain_half_rpow hr p

/-- The cancellation term: for `x₀` with `‖x₀‖_L ≥ W`, and the truncation radius `R ≥ W` with
`R^{1+σc₁} ≤ ‖x₀‖_L`, `|Σ_u Θ_{0u} g̃(u - x₀)| ≤ C W^{2σ/c₁} (Λ W^{-d}) ⟨x₀⟩^{-d}`. -/
private theorem Chain_T1b (d : ℕ) (hd : 6 ≤ d) (σ c₁ : ℝ) (hσ : 0 < σ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → (L : ℝ) ^ c₁ ≤ W → (W : ℝ) ≤ L →
      ∀ (η : ℝ) (Θ₀ : Zd d L → ℝ), Chain_ThetaCan d L W η σ (σ * c₁) (d : ℝ) Θ₀ →
      ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, v ≠ 0 → ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4))) →
      (∀ v, g (-v) = g v) → ∀ (R : ℕ), W ≤ R → ∀ x₀ : Zd d L, (W : ℝ) ≤ zdistInf d L x₀ →
        (R : ℝ) ^ (1 + σ * c₁) ≤ zdistInf d L x₀ →
      ‖∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀)‖ ≤
        C * (W : ℝ) ^ (2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) * brk d L W x₀ 0 ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₄, hC₄, hS⟩ := Chain_S_bound d hd σ hσ
  refine ⟨2 * C₄ * 2 ^ σ * (4 + 2 ^ (d : ℝ)), by positivity,
    fun L W _ hW hLW hWL η Θ₀ hcan g Λ hΛ hg hg2 R hR x₀ hρW hx₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set r := brk d L W x₀ 0 with hr
  have hr0 : 0 < r := Chain_brk_pos d L W hW x₀ 0
  have hrW : (W : ℝ) ≤ r := by rw [hr, Chain_brk_comm]; exact Chain_le_brk d L W 0 x₀
  set ρ : ℝ := (zdistInf d L x₀ : ℝ) with hρdef
  have hrρ : r = ρ + W := by rw [hr, Chain_brk_zero]
  have hρ2 : r ≤ 2 * ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hbB : 0 ≤ bB d L W 0 x₀ := by rw [Chain_bB0]; exact mul_nonneg (by positivity) (Real.rpow_nonneg hr0.le _)
  have hΨ0 : 0 ≤ (if ρ ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then ρ ^ σ * bB d L W 0 x₀ else 0) +
      ρ ^ (-(d : ℝ)) := by
    refine add_nonneg ?_ (Real.rpow_nonneg hρ0.le _)
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg hρ0.le _) hbB
    · exact le_rfl
  have h1 := Chain_T1 hcan R hR g hg2 x₀ hx₀ hΨ0
  have hSb := hS L W hW g Λ hΛ hg ρ hρ0
  have hexp : (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6) - σ) =
      (W : ℝ) ^ (-(d : ℝ)) * (W : ℝ) ^ 2 * (W : ℝ) ^ (-σ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    congr 1; ring
  -- `L + W ≤ 2 L`, `M^σ ≤ 2^σ W^{σ/c₁}`, `ρ^σ ≤ W^{σ/c₁}`
  have hM : ((L : ℝ) + W) ^ σ ≤ 2 ^ σ * (W : ℝ) ^ (σ / c₁) := by
    calc ((L : ℝ) + W) ^ σ ≤ (2 * (L : ℝ)) ^ σ :=
          Real.rpow_le_rpow (by positivity) (by linarith) hσ.le
      _ = 2 ^ σ * (L : ℝ) ^ σ := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 ^ σ * (W : ℝ) ^ (σ / c₁) :=
          mul_le_mul_of_nonneg_left (Chain_Lpow hc₁ hL1 hLW hσ.le) (by positivity)
  have hρL : ρ ^ σ ≤ (W : ℝ) ^ (σ / c₁) := by
    have : ρ ≤ L := by
      have h1 : zdistInf d L x₀ ≤ L / 2 := zdistInf_le_half d L x₀
      have h2 : (zdistInf d L x₀ : ℝ) ≤ L := by exact_mod_cast h1.trans (Nat.div_le_self _ _)
      exact h2
    exact (Real.rpow_le_rpow hρ0.le this hσ.le).trans (Chain_Lpow hc₁ hL1 hLW hσ.le)
  have hWc : 1 ≤ (W : ℝ) ^ (σ / c₁) := Real.one_le_rpow hW1 (by positivity)
  have hWσ : (W : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hWρ : (W : ℝ) ^ 2 * ρ ^ (-2 : ℝ) ≤ 1 := by
    have : ρ ^ (-2 : ℝ) = (ρ ^ 2)⁻¹ := by rw [Real.rpow_neg hρ0.le, Real.rpow_two]
    rw [this, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hW0.le hρW 2
  set M : ℝ := ((L : ℝ) + W) ^ σ with hMdef
  have hM0 : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  set Q : ℝ := Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄ * M * (W : ℝ) ^ (-σ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hSQ : ∑ x, ((zdistInf d L x : ℝ) / ρ) ^ 2 * ‖g x‖ ≤ Q * ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ)) := by
    refine hSb.trans (le_of_eq ?_)
    have : ρ ^ (-2 : ℝ) * (Λ * (W : ℝ) ^ (-4 : ℝ)) * (C₄ * M * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6) - σ))
        = Λ * C₄ * M * ρ ^ (-2 : ℝ) * ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6) - σ)) := by
      ring
    rw [this, hexp, hQ]; ring
  have hΨle : (if ρ ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then ρ ^ σ * bB d L W 0 x₀ else 0) +
      ρ ^ (-(d : ℝ)) ≤ ρ ^ σ * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) + ρ ^ (-(d : ℝ)) := by
    refine add_le_add ?_ le_rfl
    rw [← Chain_bB0]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.rpow_nonneg hρ0.le _) hbB
  have hρ2' : ρ ^ (-2 : ℝ) ≤ 2 ^ (2 : ℝ) * r ^ (-2 : ℝ) := Chain_rho_pow hr0 hρ2 (by norm_num)
  have hρd : ρ ^ (-(d : ℝ)) ≤ 2 ^ (d : ℝ) * r ^ (-(d : ℝ)) := Chain_rho_pow hr0 hρ2 (by linarith)
  have hrr : r ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2)) = r ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hWW : (W : ℝ) ^ 2 * (W : ℝ) ^ (-2 : ℝ) = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hW0]; norm_num
  have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [Real.rpow_two]; norm_num
  have hrd0 : 0 ≤ r ^ (-(d : ℝ)) := Real.rpow_nonneg hr0.le _
  have hWρ0 : 0 ≤ (W : ℝ) ^ 2 * ρ ^ (-2 : ℝ) := by positivity
  calc ‖∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀)‖
      ≤ 2 * (∑ x, ((zdistInf d L x : ℝ) / ρ) ^ 2 * ‖g x‖) *
        ((if ρ ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then ρ ^ σ * bB d L W 0 x₀ else 0) +
          ρ ^ (-(d : ℝ))) := h1
    _ ≤ 2 * (Q * ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ))) *
        ((if ρ ≤ η ^ (-(1 / 2 : ℝ)) * (W : ℝ) ^ (1 + σ) then ρ ^ σ * bB d L W 0 x₀ else 0) +
          ρ ^ (-(d : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSQ (by norm_num)) hΨ0
    _ ≤ 2 * (Q * ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ))) *
        (ρ ^ σ * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) + ρ ^ (-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left hΨle (by positivity)
    _ = 2 * Q * (ρ ^ σ * (ρ ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) +
          ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ)) * ρ ^ (-(d : ℝ))) := by
        have : (W : ℝ) ^ 2 * ρ ^ (-2 : ℝ) * (ρ ^ σ * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2)))) =
            ρ ^ σ * (ρ ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) * ((W : ℝ) ^ 2 * (W : ℝ) ^ (-2 : ℝ)) := by ring
        calc 2 * (Q * ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ))) *
            (ρ ^ σ * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2))) + ρ ^ (-(d : ℝ)))
            = 2 * Q * ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ) *
                (ρ ^ σ * ((W : ℝ) ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2)))) +
              ((W : ℝ) ^ 2 * ρ ^ (-2 : ℝ)) * ρ ^ (-(d : ℝ))) := by ring
          _ = _ := by rw [this, hWW]; ring
    _ ≤ 2 * Q * (ρ ^ σ * (4 * r ^ (-(d : ℝ))) + 1 * (2 ^ (d : ℝ) * r ^ (-(d : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hρ0.le _)
          calc ρ ^ (-2 : ℝ) * r ^ (-((d : ℝ) - 2)) ≤ (2 ^ (2 : ℝ) * r ^ (-2 : ℝ)) * r ^ (-((d : ℝ) - 2)) :=
                mul_le_mul_of_nonneg_right hρ2' (Real.rpow_nonneg hr0.le _)
            _ = 4 * r ^ (-(d : ℝ)) := by rw [h22, mul_assoc, hrr]
        · exact mul_le_mul hWρ hρd (Real.rpow_nonneg hρ0.le _) zero_le_one
    _ = 2 * Q * ((4 * ρ ^ σ + 2 ^ (d : ℝ)) * r ^ (-(d : ℝ))) := by ring
    _ ≤ 2 * (Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄ * (2 ^ σ * (W : ℝ) ^ (σ / c₁)) * 1) *
          (((4 + 2 ^ (d : ℝ)) * (W : ℝ) ^ (σ / c₁)) * r ^ (-(d : ℝ))) := by
        have hQle : Q ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄ * (2 ^ σ * (W : ℝ) ^ (σ / c₁)) * 1 := by
          rw [hQ]
          have hA : 0 ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄ := by positivity
          calc Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄ * M * (W : ℝ) ^ (-σ)
              = (Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄) * (M * (W : ℝ) ^ (-σ)) := by ring
            _ ≤ (Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄) * ((2 ^ σ * (W : ℝ) ^ (σ / c₁)) * 1) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul hM hWσ (Real.rpow_nonneg hW0.le _)
                  (by positivity)) hA
            _ = _ := by ring
        have h4ρ : 4 * ρ ^ σ + 2 ^ (d : ℝ) ≤ (4 + 2 ^ (d : ℝ)) * (W : ℝ) ^ (σ / c₁) := by
          have h2d : (0 : ℝ) ≤ 2 ^ (d : ℝ) := by positivity
          nlinarith
        refine mul_le_mul (mul_le_mul_of_nonneg_left hQle (by norm_num))
          (mul_le_mul_of_nonneg_right h4ρ hrd0) (by positivity) (by positivity)
    _ = _ := by
        have e : (W : ℝ) ^ (σ / c₁) * (W : ℝ) ^ (σ / c₁) = (W : ℝ) ^ (2 * σ / c₁) := by
          rw [← Real.rpow_add hW0]; congr 1; ring
        calc 2 * (Λ * (W : ℝ) ^ (-(d : ℝ)) * C₄ * (2 ^ σ * (W : ℝ) ^ (σ / c₁)) * 1) *
            (((4 + 2 ^ (d : ℝ)) * (W : ℝ) ^ (σ / c₁)) * r ^ (-(d : ℝ)))
            = 2 * C₄ * 2 ^ σ * (4 + 2 ^ (d : ℝ)) *
              ((W : ℝ) ^ (σ / c₁) * (W : ℝ) ^ (σ / c₁)) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
                r ^ (-(d : ℝ)) := by ring
          _ = _ := by rw [e]

/-- The far case: for `‖x₀‖_L ≥ 2 W^{1+σ}`, with the cancellation property of `Θ_{0·}` and the
properties of `g`, `|Σ_u Θ_{0u} g(u - x₀)| ≤ C W^{σ(d-3) + 2σ/c₁} (Λ W^{-d}) ⟨x₀⟩^{-d}`. -/
private theorem Chain_far (d : ℕ) (hd : 6 ≤ d) (σ c₁ : ℝ) (hσ : 0 < σ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → (L : ℝ) ^ c₁ ≤ W → (W : ℝ) ≤ L →
      ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ (Θ₀ : Zd d L → ℝ),
      (∀ u, |Θ₀ u| ≤ thetaBound W η σ (d : ℝ) 0 u) →
      Chain_ThetaCan d L W η σ (σ * c₁) (d : ℝ) Θ₀ →
      ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, v ≠ 0 → ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4))) →
      (∀ v, g (-v) = g v) → ‖∑ v, g v‖ ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * η →
      ∀ x₀ : Zd d L, 2 * (W : ℝ) ^ (1 + σ) ≤ zdistInf d L x₀ →
      ‖∑ u, (Θ₀ u : ℂ) * g (u - x₀)‖ ≤
        C * (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          brk d L W x₀ 0 ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₁, hC₁, h1⟩ := Chain_T1b d hd σ c₁ hσ hc₁
  obtain ⟨C₂, hC₂, h2⟩ := Chain_T2 d hd σ hσ
  obtain ⟨C₃, hC₃, h3⟩ := Chain_T3 d hd σ hσ
  refine ⟨C₁ + C₂ + C₃, by positivity,
    fun L W _ hW hLW hWL η hη0 hη1 Θ₀ hdec hcan g Λ hΛ hg hg2 hg3 x₀ hx₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set r := brk d L W x₀ 0 with hr
  have hr0 : 0 < r := Chain_brk_pos d L W hW x₀ 0
  set ρ : ℝ := (zdistInf d L x₀ : ℝ) with hρdef
  have hrρ : r = ρ + W := by rw [hr, Chain_brk_zero]
  set ω : ℝ := (W : ℝ) ^ σ with hω
  have hω1 : 1 ≤ ω := Real.one_le_rpow hW1 hσ.le
  have hω0 : 0 < ω := by linarith
  have hWσ : (W : ℝ) ^ (1 + σ) = W * ω := by
    rw [hω, Real.rpow_add hW0, Real.rpow_one]
  have hρ2W : 2 * (W * ω) ≤ ρ := by rw [← hWσ]; exact hx₀
  have hρW : (W : ℝ) ≤ ρ := by nlinarith
  have hρ0 : 0 < ρ := by linarith
  have hρ2 : r ≤ 2 * ρ := by linarith
  -- the truncation radius
  set y : ℝ := ρ / ω with hy
  have hy0 : 0 < y := by positivity
  have hyω : ρ = ω * y := by rw [hy]; field_simp
  have hy2 : 2 * W ≤ y := by
    rw [hy, le_div_iff₀ hω0]; linarith
  set R : ℕ := ⌊y⌋₊ with hRdef
  have hRy : (R : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyR : y < R + 1 := Nat.lt_floor_add_one y
  have hRW : W ≤ R := by
    have : (W : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hR1 : 1 ≤ R := le_trans hW hRW
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hR3 : r ≤ 4 * ω * R := by
    have : y ≤ 2 * R := by linarith
    nlinarith
  have hR2 : (R : ℝ) ^ (1 + σ * c₁) ≤ ρ := by
    have hyρ : y ≤ ρ := by rw [hy, div_le_iff₀ hω0]; nlinarith
    have hρL : ρ ≤ L := by
      have h1 : zdistInf d L x₀ ≤ L / 2 := zdistInf_le_half d L x₀
      have h2 : (zdistInf d L x₀ : ℝ) ≤ L := by exact_mod_cast h1.trans (Nat.div_le_self _ _)
      exact h2
    have hRc : (R : ℝ) ^ (σ * c₁) ≤ ω := by
      calc (R : ℝ) ^ (σ * c₁) ≤ ρ ^ (σ * c₁) :=
            Real.rpow_le_rpow (by positivity) (hRy.trans hyρ) (by positivity)
        _ ≤ (L : ℝ) ^ (σ * c₁) := Real.rpow_le_rpow hρ0.le hρL (by positivity)
        _ = ((L : ℝ) ^ c₁) ^ σ := by
            rw [mul_comm, Real.rpow_mul (by positivity)]
        _ ≤ ω := Real.rpow_le_rpow (by positivity) hLW hσ.le
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    calc (R : ℝ) * (R : ℝ) ^ (σ * c₁) ≤ y * ω :=
          mul_le_mul hRy hRc (Real.rpow_nonneg (by positivity) _) hy0.le
      _ = ρ := by rw [hyω]; ring
  -- the decomposition
  set s : ℂ := ∑ w, (if zdistInf d L w ≤ R then g w else 0) with hs
  have hdecomp : ∑ u, (Θ₀ u : ℂ) * g (u - x₀) = ∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀) +
      (Θ₀ x₀ : ℂ) * s + ∑ u, (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0) := by
    have hpt : ∀ u : Zd d L, (Θ₀ u : ℂ) * g (u - x₀) = (Θ₀ u : ℂ) * Chain_gt R g (u - x₀) +
        (if u = x₀ then (Θ₀ x₀ : ℂ) * s else 0) +
        (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0) := by
      intro u
      have := Chain_gt_decomp R g (u - x₀)
      by_cases hu : u = x₀
      · subst hu
        rw [if_pos rfl]
        simp only [sub_self, if_true] at this ⊢
        rw [← hs] at this
        calc (Θ₀ u : ℂ) * g 0 = (Θ₀ u : ℂ) * (Chain_gt R g 0 + s +
            if R < zdistInf d L 0 then g 0 else 0) := by rw [← this]
          _ = _ := by ring
      · have hne : u - x₀ ≠ 0 := sub_ne_zero.mpr hu
        rw [if_neg hu]
        rw [if_neg hne] at this
        calc (Θ₀ u : ℂ) * g (u - x₀) = (Θ₀ u : ℂ) * (Chain_gt R g (u - x₀) + 0 +
            if R < zdistInf d L (u - x₀) then g (u - x₀) else 0) := by rw [← this]
          _ = _ := by ring
    rw [Finset.sum_congr rfl fun u _ => hpt u, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ x₀]
    simp
  have hT1 := h1 L W hW hLW hWL η Θ₀ hcan g Λ hΛ hg hg2 R hRW x₀ hρW hR2
  have hT2 := h2 L W hW Θ₀ η hη0 hη1 hdec g Λ hΛ hg hg3 R hR1 x₀ hρW hR3
  have hT3 := h3 L W hW Θ₀ η hdec g Λ hΛ hg R hR1 x₀ hR3
  have hσ4 : 0 ≤ σ * ((d : ℝ) - 3) := mul_nonneg hσ.le (by linarith)
  have hσc : 0 ≤ 2 * σ / c₁ := by positivity
  have hm1 : (W : ℝ) ^ (2 * σ / c₁) ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hm2 : (W : ℝ) ^ (σ * ((d : ℝ) - 3)) ≤ (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hnn : 0 ≤ (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) := by positivity
  rw [hdecomp]
  calc ‖∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀) + (Θ₀ x₀ : ℂ) * s +
        ∑ u, (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0)‖
      ≤ ‖∑ u, (Θ₀ u : ℂ) * Chain_gt R g (u - x₀)‖ + ‖(Θ₀ x₀ : ℂ) * s‖ +
        ‖∑ u, (Θ₀ u : ℂ) * (if R < zdistInf d L (u - x₀) then g (u - x₀) else 0)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C₁ * (W : ℝ) ^ (2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) +
        C₂ * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) * (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) +
        C₃ * (W : ℝ) ^ (σ * ((d : ℝ) - 3)) * (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ ≤ C₁ * (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          r ^ (-(d : ℝ)) +
        C₂ * (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          r ^ (-(d : ℝ)) +
        C₃ * (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          r ^ (-(d : ℝ)) := by
        have e1 : ∀ (C : ℝ) (a b : ℝ), 0 ≤ C → a ≤ b →
            C * a * (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) ≤
              C * b * (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) := by
          intro C a b hC hab
          have := mul_le_mul_of_nonneg_left hab hC
          have := mul_le_mul_of_nonneg_right this hnn
          linarith
        exact add_le_add (add_le_add (e1 _ _ _ hC₁ hm1) (e1 _ _ _ hC₂ hm2)) (e1 _ _ _ hC₃ hm2)
    _ = _ := by ring


/-- The core bound: for `|g(v)| ≤ Λ W^{-4} ⟨v⟩^{-(2d-4)} + Λ W^{-d} 1_{v=0}`, symmetric `g` with
`|Σ_v g(v)| ≤ Λ W^{-d} η`, and all `x₀`,
`|Σ_u Θ_{0u} g(u - x₀)| ≤ C W^{σ(d+1) + 2σ/c₁} (Λ W^{-d}) ⟨x₀⟩^{-d}`. The term at `v = 0` enters
only the near case, through `Σ_v |g(v)|`; the far case reads `g` at `v ≠ 0` and through
`Σ_v g(v)`. -/
private theorem Chain_core (d : ℕ) (hd : 6 ≤ d) (σ c₁ : ℝ) (hσ : 0 < σ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → (L : ℝ) ^ c₁ ≤ W → (W : ℝ) ≤ L →
      ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ (Θ₀ : Zd d L → ℝ),
      (∀ u, |Θ₀ u| ≤ thetaBound W η σ (d : ℝ) 0 u) →
      Chain_ThetaCan d L W η σ (σ * c₁) (d : ℝ) Θ₀ →
      ∀ (g : Zd d L → ℂ) (Λ : ℝ), 0 ≤ Λ →
      (∀ v, ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4)) +
        (if v = 0 then Λ * (W : ℝ) ^ (-(d : ℝ)) else 0)) →
      (∀ v, g (-v) = g v) → ‖∑ v, g v‖ ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * η →
      ∀ x₀ : Zd d L,
      ‖∑ u, (Θ₀ u : ℂ) * g (u - x₀)‖ ≤
        C * (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          brk d L W x₀ 0 ^ (-(d : ℝ)) := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cn, hCn, hn⟩ := Chain_near d hd σ hσ
  obtain ⟨Cf, hCf, hf⟩ := Chain_far d hd σ c₁ hσ hc₁
  refine ⟨Cf + Cn * 3 ^ (d : ℝ), by positivity,
    fun L W _ hW hLW hWL η hη0 hη1 Θ₀ hdec hcan g Λ hΛ hg hg2 hg3 x₀ => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set r := brk d L W x₀ 0 with hr
  have hr0 : 0 < r := Chain_brk_pos d L W hW x₀ 0
  have hrd0 : 0 ≤ r ^ (-(d : ℝ)) := Real.rpow_nonneg hr0.le _
  have hnn : 0 ≤ (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) := by positivity
  have hσc : 0 ≤ 2 * σ / c₁ := by positivity
  by_cases hfar : 2 * (W : ℝ) ^ (1 + σ) ≤ zdistInf d L x₀
  · have hg' : ∀ v, v ≠ 0 →
        ‖g v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4)) := fun v hv => by
      simpa only [if_neg hv, add_zero] using hg v
    have h := hf L W hW hLW hWL η hη0 hη1 Θ₀ hdec hcan g Λ hΛ hg' hg2 hg3 x₀ hfar
    refine h.trans ?_
    have hm : (W : ℝ) ^ (σ * ((d : ℝ) - 3) + 2 * σ / c₁) ≤
        (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
    have := mul_le_mul_of_nonneg_left hm hCf
    have h2 := mul_le_mul_of_nonneg_right this hnn
    have h3 : 0 ≤ Cn * 3 ^ (d : ℝ) * (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) *
        ((Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ))) := by positivity
    nlinarith
  · rw [not_le] at hfar
    have hn' := hn L W hW Θ₀ η hdec g Λ hΛ hg x₀
    refine hn'.trans ?_
    -- `r < 3 W^{1+σ}`
    have hrρ : r = (zdistInf d L x₀ : ℝ) + W := by rw [hr, Chain_brk_zero]
    have hW1σ : (W : ℝ) ≤ (W : ℝ) ^ (1 + σ) := by
      calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (W : ℝ) ^ (1 + σ) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hr3 : r ≤ 3 * (W : ℝ) ^ (1 + σ) := by linarith
    have hWd : (W : ℝ) ^ (-(d : ℝ)) ≤ 3 ^ (d : ℝ) * (W : ℝ) ^ (σ * d) * r ^ (-(d : ℝ)) := by
      have h1 : (3 * (W : ℝ) ^ (1 + σ)) ^ (-(d : ℝ)) ≤ r ^ (-(d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 hr3 (by linarith)
      have h2 : (3 * (W : ℝ) ^ (1 + σ)) ^ (-(d : ℝ)) =
          3 ^ (-(d : ℝ)) * (W : ℝ) ^ ((1 + σ) * (-(d : ℝ))) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le]
      have h3 : (3 : ℝ) ^ (d : ℝ) * (3 : ℝ) ^ (-(d : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have h4 : (W : ℝ) ^ (σ * d) * (W : ℝ) ^ ((1 + σ) * (-(d : ℝ))) = (W : ℝ) ^ (-(d : ℝ)) := by
        rw [← Real.rpow_add hW0]; congr 1; ring
      calc (W : ℝ) ^ (-(d : ℝ)) = (3 : ℝ) ^ (d : ℝ) * (3 : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) ^ (σ * d) *
            (W : ℝ) ^ ((1 + σ) * (-(d : ℝ)))) := by rw [h3, h4, one_mul]
        _ = 3 ^ (d : ℝ) * (W : ℝ) ^ (σ * d) * (3 ^ (-(d : ℝ)) * (W : ℝ) ^ ((1 + σ) * (-(d : ℝ)))) := by
            ring
        _ ≤ 3 ^ (d : ℝ) * (W : ℝ) ^ (σ * d) * r ^ (-(d : ℝ)) := by
            rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hm : (W : ℝ) ^ σ * (W : ℝ) ^ (σ * d) ≤
        (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) := by
      rw [← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
    have hΛW : 0 ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) := by positivity
    calc Cn * (W : ℝ) ^ σ * (Λ * (W : ℝ) ^ (-(d : ℝ))) * (W : ℝ) ^ (-(d : ℝ))
        ≤ Cn * (W : ℝ) ^ σ * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          (3 ^ (d : ℝ) * (W : ℝ) ^ (σ * d) * r ^ (-(d : ℝ))) :=
          mul_le_mul_of_nonneg_left hWd (by positivity)
      _ = (Cn * 3 ^ (d : ℝ)) * ((W : ℝ) ^ σ * (W : ℝ) ^ (σ * d)) * (Λ * (W : ℝ) ^ (-(d : ℝ))) *
          r ^ (-(d : ℝ)) := by ring
      _ ≤ (Cn * 3 ^ (d : ℝ)) * (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) *
          (Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ)) := by
          have h0 : 0 ≤ Cn * 3 ^ (d : ℝ) := by positivity
          have := mul_le_mul_of_nonneg_left hm h0
          have h2 := mul_le_mul_of_nonneg_right this hnn
          nlinarith
      _ ≤ _ := by
          have h3 : 0 ≤ Cf * (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) *
              ((Λ * (W : ℝ) ^ (-(d : ℝ))) * r ^ (-(d : ℝ))) := by positivity
          nlinarith


/-! ## The kernel `Θ` and the product `Θ K` -/

/-- `Θ_{xy} = Θ_{0, y - x}` for a translation invariant `S`. -/
private theorem Chain_Theta_translate {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : TransInv S) (m : ℂ) (x y : Zd d L) : Theta m S x y = Theta m S 0 (y - x) := by
  have hT := (TransInv_propagators S hS m).2.2
  have := hT x y (-x)
  rw [← this]
  congr 1 <;> abel

/-- `(Θ K)_{xy} = Σ_u Θ_{0u} K(0, u - (y - x))` for a translation invariant symmetric `K`. -/
private theorem Chain_prod_eq {d L : ℕ} [NeZero L] (Θ : Matrix (Zd d L) (Zd d L) ℝ)
    (hΘ : ∀ x y, Θ x y = Θ 0 (y - x)) (Km : Matrix (Zd d L) (Zd d L) ℂ)
    (hK1 : ∀ x a, Km x (x + a) = Km 0 a) (hK2 : ∀ a, Km 0 a = Km 0 (-a)) (x y : Zd d L) :
    (cmat Θ * Km) x y = ∑ u, (Θ 0 u : ℂ) * Km 0 (u - (y - x)) := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ (fun α => ?_)
  simp only [cmat, Matrix.map_apply, Equiv.subRight_apply]
  have h1 : Km α y = Km 0 (α - y) := by
    have := hK1 α (y - α)
    rw [add_sub_cancel] at this
    rw [this, hK2 (y - α), neg_sub]
  rw [h1, hΘ x α, show α - x - (y - x) = α - y by abel]

/-- The package of the decay and the cancellation property of `Θ` for the variance matrices of a
profile: for `W ≥ W₀` along `adm(c₀, c₁)` and `z ∈ 𝐃(κ, ε)`, with `D = d`. -/
private theorem Chain_Theta_pkg (d : ℕ) (hd : 3 ≤ d) (P : Profile d) (c₀ c₁ κ ε σ : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L,
        (∀ u, |Theta (msc z) (Smat P.ψ W L) 0 u| ≤ thetaBound W z.im σ (d : ℝ) 0 u) ∧
        Chain_ThetaCan d L W z.im σ (σ * c₁) (d : ℝ) (fun x => Theta (msc z) (Smat P.ψ W L) 0 x) ∧
        TransInv (Smat P.ψ W L) := by
  obtain ⟨C, hC⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨W₁, h1⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨W₂, h2⟩ := Theta_decay d hd c₀ c₁ hc₀ hc₁ P.ψ P.cψ (profileShape_of_profile d P) C κ ε σ
    (d : ℝ) hκ hε hσ hd0
  obtain ⟨W₃, h3⟩ := Theta_cancel d hd c₀ c₁ hc₀ hc₁ P.ψ P.cψ (profileShape_of_profile d P) C κ ε
    (σ * c₁) σ (d : ℝ) hκ hε (mul_pos hσ hc₁) hσ hd0
  refine ⟨max (max W₁ W₂) W₃, fun W L _ hadm hW z hz => ?_⟩
  have hW1 : W₁ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ (W : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3 : W₃ ≤ (W : ℝ) := le_trans (le_max_right _ _) hW
  have hS := h1 W L hadm hW1
  refine ⟨fun u => h2 W L hadm hW2 _ hS (hC W L hadm) z hz 0 u, ?_, hS.transInv⟩
  intro K hK g hg1 hg2 hg3 x₀ hx₀
  exact h3 W L hadm hW3 _ hS (hC W L hadm) z hz K hK g hg1 hg2 hg3 x₀ hx₀


/-- `W^{σ(d+1) + 2σ/c₁} W^σ = W^{τ/2}` for `σ = τ / (2 (d + 2 + 2/c₁))`. -/
private theorem Chain_exp_eq {d c₁ τ : ℝ} (hc₁ : 0 < c₁) (hd : 0 ≤ d) (hτ : 0 < τ) :
    τ / (2 * (d + 2 + 2 / c₁)) * (d + 1) + 2 * (τ / (2 * (d + 2 + 2 / c₁))) / c₁ +
      τ / (2 * (d + 2 + 2 / c₁)) = τ / 2 := by
  have h : 0 < d + 2 + 2 / c₁ := by positivity
  field_simp
  ring

/-- [I, Lemma 6.2, (6.1)] = [II, Lemma 2.8, (2.7)] for a kernel of order `l` with the properties
[I, (1.25)–(1.27)]: for `d ≥ 6` and every `τ > 0` there is `W₀` with
`|(Θ K_l)_{xy}| ≤ W^τ W^{-(l-2)d/2} ⟨x - y⟩^{-d}` for `W ≥ W₀` along `adm(c₀, c₁)` and
`z ∈ 𝐃(κ, ε)`. -/
theorem thetaSigma :
  ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (K : KerFamily d) (l : ℕ), KerSymm K l → KerBound K l →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
          ‖(cmat (Theta (msc z) (Smat P.ψ W L)) * K l W L z) x y‖ ≤
            (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * brk d L W x y ^ (-(d : ℝ)) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K l hsym hbd τ hτ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  set σ : ℝ := τ / (2 * ((d : ℝ) + 2 + 2 / c₁)) with hσ
  have hσ0 : 0 < σ := by positivity
  obtain ⟨C, hC, hcore⟩ := Chain_core d hd σ c₁ hσ0 hc₁
  obtain ⟨L₀, hL₀⟩ := hbd κ ε c₀ c₁ hκ hε hc₀ hc₁ hc (c₁ * σ) (mul_pos hc₁ hσ0)
  obtain ⟨W₁, hpkg⟩ := Chain_Theta_pkg d (by omega) P c₀ c₁ κ ε σ hc₀ hc₁ hκ hε hσ0
  refine ⟨max (max W₁ (L₀ : ℝ)) (max 1 (C ^ (2 / τ))), fun W L _ hadm hW z hz x y => ?_⟩
  have hWa : W₁ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWb : (L₀ : ℝ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWC : C ^ (2 / τ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLW : (L : ℝ) ^ c₁ ≤ W := hadm.1
  have hWL : (W : ℝ) ≤ L := by
    calc (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := hadm.2
      _ ≤ (L : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1' (by linarith)
      _ = L := Real.rpow_one _
  have hLL₀ : L₀ ≤ L := by
    have : (L₀ : ℝ) ≤ L := hWb.trans hWL
    exact_mod_cast this
  have him : 0 < z.im := by
    have := hz.2.1
    have h2 : 0 < (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by positivity
    linarith
  have him1 : z.im ≤ 1 := hz.2.2
  obtain ⟨hdec, hcan, htr⟩ := hpkg W L hadm hWa z hz
  obtain ⟨hK1, hK2⟩ := hL₀ W L hLL₀ hadm z hz
  have hs := hsym W L z him
  set Λ : ℝ := (L : ℝ) ^ (c₁ * σ) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hprod := Chain_prod_eq (Theta (msc z) (Smat P.ψ W L))
    (Chain_Theta_translate (Smat P.ψ W L) htr (msc z)) (K l W L z)
    (fun x a => (hs x a).1) (fun a => (hs 0 a).2) x y
  have hexp : Λ * (W : ℝ) ^ (-(d : ℝ)) = (L : ℝ) ^ (c₁ * σ) * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
    rw [hΛ, mul_assoc, ← Real.rpow_add hW0]; congr 2; ring
  have hg1 : ∀ v, ‖K l W L z 0 v‖ ≤ Λ * (W : ℝ) ^ (-4 : ℝ) * brk d L W v 0 ^ (-(2 * (d : ℝ) - 4)) +
      (if v = 0 then Λ * (W : ℝ) ^ (-(d : ℝ)) else 0) := by
    intro v
    refine (hK1 v).trans (le_of_eq ?_)
    rw [Chain_bB_sq d L W hWn, Chain_brk_comm d L W 0 v, hexp, hΛ]
    ring
  have hg2 : ∀ v, K l W L z 0 (-v) = K l W L z 0 v := fun v => ((hs 0 v).2).symm
  have hg3 : ‖∑ v, K l W L z 0 v‖ ≤ Λ * (W : ℝ) ^ (-(d : ℝ)) * z.im := by
    refine hK2.trans (le_of_eq ?_)
    rw [hexp]; ring
  rw [hprod]
  have hc1 := hcore L W hWn hLW hWL z.im him him1
    (fun u => Theta (msc z) (Smat P.ψ W L) 0 u) hdec hcan (fun v => K l W L z 0 v) Λ hΛ0 hg1 hg2 hg3
    (y - x)
  refine hc1.trans ?_
  rw [Chain_brk_sub d L W y x, Chain_brk_comm d L W y x, hexp]
  set A : ℝ := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg hW0.le _
  have hb0 : 0 ≤ brk d L W x y ^ (-(d : ℝ)) :=
    Real.rpow_nonneg (Chain_brk_pos d L W hWn x y).le _
  have hLσ : (L : ℝ) ^ (c₁ * σ) ≤ (W : ℝ) ^ σ := by
    have := Chain_Lpow hc₁ hL1 hLW (t := c₁ * σ) (by positivity)
    rwa [mul_div_cancel_left₀ _ hc₁.ne'] at this
  have hCW : C ≤ (W : ℝ) ^ (τ / 2) := by
    calc C = (C ^ (2 / τ)) ^ (τ / 2) := by
          rw [← Real.rpow_mul hC]; field_simp; simp
      _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow (by positivity) hWC (by positivity)
  have hE : (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) * (W : ℝ) ^ σ = (W : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hW0]
    congr 1
    exact Chain_exp_eq hc₁ hd0 hτ
  have hττ : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  have hE0 : 0 ≤ (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) := Real.rpow_nonneg hW0.le _
  calc C * (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) * ((L : ℝ) ^ (c₁ * σ) * A) *
        brk d L W x y ^ (-(d : ℝ))
      ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) * ((W : ℝ) ^ σ * A) *
        brk d L W x y ^ (-(d : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hb0
        refine mul_le_mul (mul_le_mul_of_nonneg_right hCW hE0) (mul_le_mul_of_nonneg_right hLσ hA0)
          (by positivity) (by positivity)
    _ = (W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (σ * ((d : ℝ) + 1) + 2 * σ / c₁) * (W : ℝ) ^ σ) * A *
        brk d L W x y ^ (-(d : ℝ)) := by ring
    _ = (W : ℝ) ^ τ * A * brk d L W x y ^ (-(d : ℝ)) := by rw [hE, ← hττ]

/-! ## The labelled chain -/

/-- `Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ = Θ (Σ_{o₁} Θ) ⋯ (Σ_{o_l} Θ)` as a fold. -/
private theorem Chain_foldl {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ)
    (Ks : ℕ → Matrix ι ι ℂ) (o : List ℕ) (M : Matrix ι ι ℂ) :
    o.foldl (fun M l => M * Ks l * B) M = M * (o.map fun l => Ks l * B).prod := by
  induction o generalizing M with
  | nil => simp
  | cons l o ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons]
    simp only [Matrix.mul_assoc]

/-- `chain (l :: o) = (Θ Σ_l) chain o`. -/
private theorem Chain_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (l : ℕ)
    (o : List ℕ) : D.chain (l :: o) = (D.Theta * D.Sig l) * D.chain o := by
  unfold Data.chain
  rw [Chain_foldl D.Theta D.Sig (l :: o), Chain_foldl D.Theta D.Sig o, List.map_cons,
    List.prod_cons]
  simp only [Matrix.mul_assoc]

/-- `chain [] = Θ`. -/
private theorem Chain_nil {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) :
    D.chain [] = D.Theta := rfl

/-- The exponent of the labelled `Θ` edge: `ord - 2 = Σ (oᵢ - 2)`. -/
private theorem Chain_ord_sub (o : List ℕ) :
    (((Kind.theta o).ord : ℤ) : ℝ) - 2 = (o.map fun l : ℕ => (l : ℝ) - 2).sum := by
  induction o with
  | nil => simp [Kind.ord]
  | cons l o ih =>
    simp only [Kind.ord] at ih ⊢
    simp only [List.sum_cons, List.length_cons, List.map_cons] at ih ⊢
    push_cast at ih ⊢
    linarith

/-- The induction on the length of the label: if `Θ Σ_l` (`l` in the label) and `Θ` have the
bounds `a W^{-(l-2)d/2} ⟨x - y⟩^{-d}` and `c B`, and the convolution of `⟨·⟩^{-d}` with
`⟨·⟩^{-(d-2)}` is at most `Q ⟨x - y⟩^{-(d-2)}`, then
`|chain_o(x, y)| ≤ c (Q a)^{len o} W^{-(Σ (oᵢ - 2)) d/2} B_{xy}`. -/
private theorem Chain_induct {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (D : Data (Zd d L))
    (S : Finset ℕ) (a Q c : ℝ) (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hc : 0 ≤ c)
    (h1 : ∀ l ∈ S, ∀ x y, ‖(D.Theta * D.Sig l) x y‖ ≤
      a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * brk d L W x y ^ (-(d : ℝ)))
    (h2 : ∀ x y, ‖D.Theta x y‖ ≤ c * bB d L W x y)
    (h3 : ∀ x y, ∑ α, brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
      Q * brk d L W x y ^ (-((d : ℝ) - 2))) :
    ∀ o : List ℕ, (∀ l ∈ o, l ∈ S) → ∀ x y, ‖D.chain o x y‖ ≤
      c * (Q * a) ^ o.length * (W : ℝ) ^ (-((o.map fun l : ℕ => (l : ℝ) - 2).sum * d / 2)) *
        bB d L W x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  intro o
  induction o with
  | nil =>
    intro _ x y
    simpa [Chain_nil] using h2 x y
  | cons l o ih =>
    intro ho x y
    have hl : l ∈ S := ho l List.mem_cons_self
    have ho' : ∀ l' ∈ o, l' ∈ S := fun l' hl' => ho l' (List.mem_cons_of_mem _ hl')
    rw [Chain_cons, Matrix.mul_apply]
    set m := o.length with hm
    set s : ℝ := (o.map fun l : ℕ => (l : ℝ) - 2).sum with hs
    set c' : ℝ := c * (Q * a) ^ m * (W : ℝ) ^ (-(s * d / 2)) with hc'
    have hc'0 : 0 ≤ c' := mul_nonneg (mul_nonneg hc (pow_nonneg (mul_nonneg hQ ha) _))
      (Real.rpow_nonneg hW0.le _)
    have hKW : 0 ≤ a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) :=
      mul_nonneg ha (Real.rpow_nonneg hW0.le _)
    have hterm : ∀ α : Zd d L, ‖(D.Theta * D.Sig l) x α * D.chain o α y‖ ≤
        a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * c' * (W : ℝ) ^ (-2 : ℝ) *
          (brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2))) := by
      intro α
      rw [norm_mul]
      have e1 := h1 l hl x α
      have e2 := ih ho' α y
      rw [Chain_bB_eq'] at e2
      calc ‖(D.Theta * D.Sig l) x α‖ * ‖D.chain o α y‖
          ≤ (a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * brk d L W x α ^ (-(d : ℝ))) *
            (c' * ((W : ℝ) ^ (-2 : ℝ) * brk d L W α y ^ (-((d : ℝ) - 2)))) :=
            mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hKW
              (Real.rpow_nonneg (Chain_brk_pos d L W hW x α).le _))
        _ = _ := by ring
    calc ‖∑ α, (D.Theta * D.Sig l) x α * D.chain o α y‖
        ≤ ∑ α, ‖(D.Theta * D.Sig l) x α * D.chain o α y‖ := norm_sum_le _ _
      _ ≤ ∑ α, a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * c' * (W : ℝ) ^ (-2 : ℝ) *
          (brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2))) :=
          Finset.sum_le_sum fun α _ => hterm α
      _ = a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * c' * (W : ℝ) ^ (-2 : ℝ) *
          ∑ α, (brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2))) := by
          rw [← Finset.mul_sum]
      _ ≤ a * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * c' * (W : ℝ) ^ (-2 : ℝ) *
          (Q * brk d L W x y ^ (-((d : ℝ) - 2))) :=
          mul_le_mul_of_nonneg_left (h3 x y)
            (mul_nonneg (mul_nonneg hKW hc'0) (Real.rpow_nonneg hW0.le _))
      _ = c * (Q * a) ^ (l :: o).length *
          (W : ℝ) ^ (-(((l :: o).map fun l : ℕ => (l : ℝ) - 2).sum * d / 2)) * bB d L W x y := by
          have e : (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ (-(s * d / 2)) =
              (W : ℝ) ^ (-(((l :: o).map fun l : ℕ => (l : ℝ) - 2).sum * d / 2)) := by
            rw [← Real.rpow_add hW0]; congr 1
            simp only [List.map_cons, List.sum_cons, ← hs]; ring
          rw [Chain_bB_eq', List.length_cons, ← e, hc', ← hm]
          ring

/-- The labelled chain for the labels with entries in a finite set `S` of orders, uniformly in
the label: `|chain_o(x, y)| ≤ W^{(len o + 1) τ} W^{-(k-2)d/2} B_{xy}`, with `W₀` depending on `S`
and `τ` only. -/
private theorem Chain_main (d : ℕ) (hd : 6 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (K : KerFamily d)
    (S : Finset ℕ) (hS : ∀ l ∈ S, KerSymm K l ∧ KerBound K l) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ o : List ℕ, (∀ l ∈ o, l ∈ S) → ∀ x y : Zd d L,
        ‖(detData (Smat P.ψ W L) z (fun l => K l W L z)).chain o x y‖ ≤
          (W : ℝ) ^ (((o.length : ℝ) + 1) * τ) *
            (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) * bB d L W x y := by
  set τ₁ : ℝ := τ / 3 with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hts : ∀ l : ℕ, ∃ W₀ : ℝ, l ∈ S → ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
        ‖(cmat (Theta (msc z) (Smat P.ψ W L)) * K l W L z) x y‖ ≤
          (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * brk d L W x y ^ (-(d : ℝ)) := by
    intro l
    by_cases hl : l ∈ S
    · obtain ⟨W₀, h⟩ := thetaSigma d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K l (hS l hl).1 (hS l hl).2
        τ₁ hτ₁0
      exact ⟨W₀, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose f hf using hts
  obtain ⟨W₁, hpkg⟩ := Chain_Theta_pkg d (by omega) P c₀ c₁ κ ε τ₁ hc₀ hc₁ hκ hε hτ₁0
  obtain ⟨C, hC0, hconv⟩ := Chain_conv d (by omega) (c₁ * τ₁) (mul_pos hc₁ hτ₁0)
  set C₃ : ℝ := max 2 (C * 2 ^ (c₁ * τ₁)) with hC₃
  have hC₃2 : 2 ≤ C₃ := le_max_left _ _
  have hC₃C : C * 2 ^ (c₁ * τ₁) ≤ C₃ := le_max_right _ _
  have hC₃0 : 0 ≤ C₃ := by linarith
  refine ⟨max (max W₁ (∑ l ∈ S, |f l|)) (max 1 (C₃ ^ (1 / τ₁))),
    fun W L _ hadm hW z hz o ho x y => ?_⟩
  have hWa : W₁ ≤ (W : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWb : ∀ l ∈ S, f l ≤ (W : ℝ) := fun l hl =>
    le_trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun l => |f l|)
      (fun l _ => abs_nonneg _) hl)) (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW)
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWC : C₃ ^ (1 / τ₁) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLW : (L : ℝ) ^ c₁ ≤ W := hadm.1
  have hWL : (W : ℝ) ≤ L := by
    calc (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := hadm.2
      _ ≤ (L : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1' (by linarith)
      _ = L := Real.rpow_one _
  obtain ⟨hdec, _, htr⟩ := hpkg W L hadm hWa z hz
  have h2 : ∀ x y : Zd d L, ‖(detData (Smat P.ψ W L) z (fun l => K l W L z)).Theta x y‖ ≤
      (2 * (W : ℝ) ^ τ₁) * bB d L W x y := by
    intro x y
    have e : (detData (Smat P.ψ W L) z (fun l => K l W L z)).Theta x y =
        ((Theta (msc z) (Smat P.ψ W L) 0 (y - x) : ℝ) : ℂ) := by
      show ((Theta (msc z) (Smat P.ψ W L) x y : ℝ) : ℂ) = _
      rw [Chain_Theta_translate (Smat P.ψ W L) htr (msc z) x y]
    have hbB : bB d L W 0 (y - x) = bB d L W x y := by
      rw [Chain_bB_eq', Chain_bB_eq']
      have : brk d L W 0 (y - x) = brk d L W x y := by
        unfold brk; rw [zero_sub, neg_sub]
      rw [this]
    rw [e, Complex.norm_real, Real.norm_eq_abs, ← hbB]
    exact Chain_theta_pt hWn hτ₁0.le hdec (y - x)
  have hQ : ∀ x y : Zd d L,
      ∑ α, brk d L W x α ^ (-(d : ℝ)) * brk d L W α y ^ (-((d : ℝ) - 2)) ≤
        (C * 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁) * brk d L W x y ^ (-((d : ℝ) - 2)) := by
    intro x y
    refine (hconv L W hWn x y).trans ?_
    have hb : brk d L W x y / W ≤ 2 * L := by
      rw [div_le_iff₀ hW0]
      have h1 := Chain_brk_le d L W x y
      nlinarith
    have hq : (brk d L W x y / W) ^ (c₁ * τ₁) ≤ 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁ := by
      have hbpos := Chain_brk_pos d L W hWn x y
      calc (brk d L W x y / W) ^ (c₁ * τ₁) ≤ (2 * L) ^ (c₁ * τ₁) :=
            Real.rpow_le_rpow (by positivity) hb (by positivity)
        _ = 2 ^ (c₁ * τ₁) * (L : ℝ) ^ (c₁ * τ₁) := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁ := by
          gcongr
          have := Chain_Lpow hc₁ hL1 hLW (t := c₁ * τ₁) (by positivity)
          rwa [mul_div_cancel_left₀ _ hc₁.ne'] at this
    have hbp : 0 ≤ brk d L W x y ^ (-((d : ℝ) - 2)) :=
      Real.rpow_nonneg (Chain_brk_pos d L W hWn x y).le _
    calc C * (brk d L W x y / W) ^ (c₁ * τ₁) * brk d L W x y ^ (-((d : ℝ) - 2))
        ≤ C * (2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁) * brk d L W x y ^ (-((d : ℝ) - 2)) := by
          gcongr
      _ = _ := by ring
  have hbound := Chain_induct (D := detData (Smat P.ψ W L) z (fun l => K l W L z)) hWn S
    ((W : ℝ) ^ τ₁) (C * 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁) (2 * (W : ℝ) ^ τ₁) (by positivity)
    (by positivity) (by positivity)
    (fun l hl x y => hf l hl W L hadm (hWb l hl) z hz x y) h2 hQ o ho x y
  set m := o.length with hm
  set s : ℝ := (o.map fun l : ℕ => (l : ℝ) - 2).sum with hs
  have hexp : -s * d / 2 = -(s * d / 2) := by ring
  rw [Chain_ord_sub o, ← hs, hexp]
  have hτ3 : τ₁ + τ₁ + τ₁ = τ := by rw [hτ₁]; ring
  have hCW : C₃ ≤ (W : ℝ) ^ τ₁ := by
    calc C₃ = (C₃ ^ (1 / τ₁)) ^ τ₁ := by
          rw [← Real.rpow_mul hC₃0]; field_simp; simp
      _ ≤ (W : ℝ) ^ τ₁ := Real.rpow_le_rpow (by positivity) hWC hτ₁0.le
  have hWτ : (0 : ℝ) ≤ (W : ℝ) ^ τ₁ := by positivity
  have hc1 : 2 * (W : ℝ) ^ τ₁ ≤ (W : ℝ) ^ (τ₁ + τ₁) := by
    rw [Real.rpow_add hW0]
    exact mul_le_mul_of_nonneg_right (hC₃2.trans hCW) hWτ |>.trans_eq' (by ring) |>.trans_eq
      (by ring)
  have hc2 : C * 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁ ≤ (W : ℝ) ^ τ := by
    rw [← hτ3, Real.rpow_add hW0, Real.rpow_add hW0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC₃C.trans hCW) hWτ) hWτ
  have hc3 : (C * 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁) ^ m ≤ (W : ℝ) ^ (τ * m) := by
    calc _ ≤ ((W : ℝ) ^ τ) ^ m := pow_le_pow_left₀ (by positivity) hc2 m
      _ = (W : ℝ) ^ (τ * m) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hc4 : 2 * (W : ℝ) ^ τ₁ * (C * 2 ^ (c₁ * τ₁) * (W : ℝ) ^ τ₁ * (W : ℝ) ^ τ₁) ^ m ≤
      (W : ℝ) ^ (((m : ℝ) + 1) * τ) := by
    calc _ ≤ (W : ℝ) ^ (τ₁ + τ₁) * (W : ℝ) ^ (τ * m) :=
          mul_le_mul hc1 hc3 (by positivity) (by positivity)
      _ = (W : ℝ) ^ (τ₁ + τ₁ + τ * m) := (Real.rpow_add hW0 _ _).symm
      _ ≤ (W : ℝ) ^ (((m : ℝ) + 1) * τ) := by
        refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
        have : (0 : ℝ) ≤ τ₁ := hτ₁0.le
        nlinarith
  have hA0 : 0 ≤ (W : ℝ) ^ (-(s * d / 2)) := Real.rpow_nonneg hW0.le _
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc4 hA0)
    (Chain_bB_nonneg d L W x y)

/-- [I, Lemma 6.2, (6.2)] = [II, Lemma 2.8, (2.8)]: for a label `o` whose entries have the
properties [I, (1.25)–(1.27)], `|(Θ K_{o₁} Θ ⋯ K_{o_l} Θ)_{xy}| ≤ W^τ W^{-(k-2)d/2} B_{xy}` with
`k = Σ oᵢ + 2 - 2l` the scaling order of the labelled `Θ` edge. -/
theorem chain :
  ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (K : KerFamily d) (o : List ℕ), (∀ l ∈ o, KerSymm K l ∧ KerBound K l) →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
          ‖(detData (Smat P.ψ W L) z (fun l => K l W L z)).chain o x y‖ ≤
            (W : ℝ) ^ τ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              bB d L W x y := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K o ho τ hτ
  have hm : (0 : ℝ) < (o.length : ℝ) + 1 := by positivity
  obtain ⟨W₀, h⟩ := Chain_main d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε K o.toFinset
    (fun l hl => ho l (List.mem_toFinset.1 hl)) (τ / ((o.length : ℝ) + 1)) (by positivity)
  refine ⟨W₀, fun W L _ hadm hW z hz x y => ?_⟩
  have e : ((o.length : ℝ) + 1) * (τ / ((o.length : ℝ) + 1)) = τ := by field_simp
  have := h W L hadm hW z hz o (fun l hl => List.mem_toFinset.2 hl) x y
  rwa [e] at this

section Instances

section Witness
open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end Instances

end RBM8D
