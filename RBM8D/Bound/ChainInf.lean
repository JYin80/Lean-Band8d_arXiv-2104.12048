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
# Labelled `Θ` edges on `ℤ^d` ([I, Lemma 7.4])
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

/-- A family of kernels `k l W` on `ℤ^d`, functions of the offset: `Σ^∞_l(x, y) = k l W (y - x)`. -/
abbrev KerInf (d : ℕ) : Type := ℕ → ℕ → (Fin d → ℤ) → ℂ

/-- [I, (2.13), (2.14), (2.16)] for the order `l`: `k(-a) = k(a)`; for every `τ > 0` and
`W ≥ W₀(τ)`, `|k(x)| ≤ W^{-ld/2} W^{2d-4} (|x| + W)^{-(2d-4-τ)} + W^{-(l-2)d/2} W^τ 1_{x=0}`; and
`Σ_{x ∈ ℤ^d} k(x) = 0`. The diagonal term `W^{-(l-2)d/2} W^τ 1_{x=0}` is added to [I, (2.14)],
with the loss `W^τ` of that line at `x = 0`; it is the analogue on `ℤ^d` of the diagonal term of
[I, (1.26)] in `SelfEnergyBound`. -/
def KerInfHyp {d : ℕ} (k : KerInf d) (l : ℕ) : Prop :=
  (∀ (W : ℕ) (a : Fin d → ℤ), k l W (-a) = k l W a) ∧
  (∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ x : Fin d → ℤ,
    ‖k l W x‖ ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) +
      (if x = 0 then (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ else 0)) ∧
  (∀ W : ℕ, ∑' x, k l W x = 0)

/-- The convolution `(f ∗ g)(x) = Σ_{α ∈ ℤ^d} f(α) g(x - α)`. -/
def convZ {d : ℕ} (f g : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ) : ℂ := ∑' α, f α * g (x - α)

/-- The chain `Θ_∞ Σ^∞_{o₁} Θ_∞ ⋯ Σ^∞_{o_l} Θ_∞` on `ℤ^d`, as a function of the offset. -/
def chainZ {d : ℕ} (s : (Fin d → ℤ) → ℝ) (k : KerInf d) (W : ℕ) (o : List ℕ) :
    (Fin d → ℤ) → ℂ :=
  o.foldl (fun F l => convZ (convZ F (k l W)) (ThetaInf s)) (ThetaInf s)

/-! ## Lattice sums -/

section Sums

variable {d : ℕ}

private theorem mem_boxZ_iff {K : ℕ} {y : Fin d → ℤ} : y ∈ boxZ d K ↔ zdInf y ≤ K := by
  constructor
  · intro hy
    refine Finset.sup_le fun i _ => ?_
    have h := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hy i)
    omega
  · intro hy
    refine Fintype.mem_piFinset.2 fun i => ?_
    have h : (y i).natAbs ≤ zdInf y :=
      Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i)
    rw [Finset.mem_Icc]
    omega

/-- The `ℓ^∞` sphere of radius `n` in `ℤ^d` has at most `2d (2n + 1)^{d-1}` points. -/
private theorem card_sphere_le (hd : 1 ≤ d) (R n : ℕ) :
    ((((boxZ d R).filter fun z => zdInf z = n).card : ℕ) : ℝ) ≤
      2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by
  classical
  set T : Fin d → Fin d → Finset ℤ := fun i j =>
    if j = i then ({(n : ℤ), -(n : ℤ)} : Finset ℤ) else Finset.Icc (-(n : ℤ)) n with hT
  have hsub : ((boxZ d R).filter fun z => zdInf z = n) ⊆
      Finset.univ.biUnion fun i => Fintype.piFinset (T i) := by
    intro z hz
    have hzn := (Finset.mem_filter.1 hz).2
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
      Finset.univ_nonempty fun i => (z i).natAbs
    have hle : ∀ j, (z j).natAbs ≤ n := fun j => by
      rw [← hzn]; exact Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ j)
    have hin : (z i).natAbs = n := by rw [← hzn]; exact hi.symm
    refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.2 fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp only [hT, ite_true, Finset.mem_insert, Finset.mem_singleton]
      omega
    · simp only [hT, hj, ite_false, Finset.mem_Icc]
      have := hle j
      omega
  have hcard : ∀ i, ((Fintype.piFinset (T i)).card : ℝ) ≤ 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by
    intro i
    rw [Fintype.card_piFinset, Nat.cast_prod]
    have hfac : ∀ j, (((T i j).card : ℕ) : ℝ) ≤ if j = i then 2 else 2 * (n : ℝ) + 1 := by
      intro j
      by_cases hj : j = i
      · simp only [hT, hj, ite_true]
        exact_mod_cast Finset.card_le_two
      · simp only [hT, hj, ite_false, Int.card_Icc]
        have : (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, Int.toNat_natCast]
        push_cast; rfl
    calc ∏ j, (((T i j).card : ℕ) : ℝ) ≤ ∏ j, (if j = i then (2 : ℝ) else 2 * (n : ℝ) + 1) :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) fun j _ => hfac j
      _ = 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := by
          rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
          have h1 : ∀ j ∈ Finset.univ \ {i},
              (if j = i then (2 : ℝ) else 2 * (n : ℝ) + 1) = 2 * (n : ℝ) + 1 := by
            intro j hj
            have : j ≠ i := by simpa using (Finset.mem_sdiff.1 hj).2
            simp [this]
          rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_univ_sdiff,
            Fintype.card_fin, Finset.card_singleton]
          simp
  calc ((((boxZ d R).filter fun z => zdInf z = n).card : ℕ) : ℝ)
      ≤ ((Finset.univ.biUnion fun i => Fintype.piFinset (T i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i, ((Fintype.piFinset (T i)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 2 * (2 * (n : ℝ) + 1) ^ (d - 1) := Finset.sum_le_sum fun i _ => hcard i
    _ = 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) := by simp; ring

/-- Sums over `ℤ^d` of functions of the `ℓ^∞` norm, by spheres. -/
private theorem summable_zdInf (hd : 1 ≤ d) {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {B : ℝ}
    (hB : ∀ R : ℕ, ∑ n ∈ Finset.range (R + 1), 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n ≤ B) :
    Summable (fun z : Fin d → ℤ => f (zdInf z)) ∧ ∑' z : Fin d → ℤ, f (zdInf z) ≤ B := by
  classical
  have hu : ∀ u : Finset (Fin d → ℤ), ∑ z ∈ u, f (zdInf z) ≤ B := by
    intro u
    set R : ℕ := u.sup zdInf with hR
    have hsub : u ⊆ boxZ d R := fun z hz =>
      mem_boxZ_iff.2 (Finset.le_sup (f := zdInf) hz)
    have hmaps : ∀ z ∈ boxZ d R, zdInf z ∈ Finset.range (R + 1) := fun z hz =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (mem_boxZ_iff.1 hz))
    calc ∑ z ∈ u, f (zdInf z) ≤ ∑ z ∈ boxZ d R, f (zdInf z) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hf _
      _ = ∑ n ∈ Finset.range (R + 1), ∑ z ∈ (boxZ d R).filter fun z => zdInf z = n,
            f (zdInf z) := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ n ∈ Finset.range (R + 1),
            (((boxZ d R).filter fun z => zdInf z = n).card : ℝ) * f n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.1 hz).2],
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.range (R + 1), 2 * d * (2 * (n : ℝ) + 1) ^ (d - 1) * f n :=
          Finset.sum_le_sum fun n _ =>
            mul_le_mul_of_nonneg_right (card_sphere_le hd R n) (hf n)
      _ ≤ B := hB R
  exact ⟨summable_of_sum_le (fun z => hf _) hu, Real.tsum_le_of_sum_le (fun z => hf _) hu⟩

/-- `(t + 1)^{-s} ≤ (t^{1-s} - (t + 1)^{1-s}) / (s - 1)` for `t > 0`, `s > 1`. -/
private theorem rpow_succ_le_sub {t s : ℝ} (ht : 0 < t) (hs : 1 < s) :
    (t + 1) ^ (-s) ≤ (t ^ (1 - s) - (t + 1) ^ (1 - s)) / (s - 1) := by
  have hnot : (0 : ℝ) ∉ Set.uIcc t (t + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hI : ∫ x in t..t + 1, x ^ (-s) = ((t + 1) ^ (-s + 1) - t ^ (-s + 1)) / (-s + 1) :=
    integral_rpow (Or.inr ⟨by linarith, hnot⟩)
  have hmono : ∫ _x in t..t + 1, (t + 1) ^ (-s) ≤ ∫ x in t..t + 1, x ^ (-s) :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_rpow (Or.inr hnot))
      (fun x hx => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2 (by linarith))
  rw [intervalIntegral.integral_const, hI, smul_eq_mul, show t + 1 - t = 1 by ring, one_mul]
    at hmono
  refine hmono.trans (le_of_eq ?_)
  rw [show -s + 1 = -(s - 1) by ring, show (1 : ℝ) - s = -(s - 1) by ring, div_neg, ← neg_div,
    neg_sub]

/-- `Σ_{j=0}^{R} (j + W)^{-s} ≤ (1 + 1/(s-1)) W^{1-s}` for `W ≥ 1`, `s > 1`. -/
private theorem sum_range_rpow_le {W s : ℝ} (hW : 1 ≤ W) (hs : 1 < s) (R : ℕ) :
    ∑ j ∈ Finset.range (R + 1), ((j : ℝ) + W) ^ (-s) ≤ (1 + 1 / (s - 1)) * W ^ (1 - s) := by
  have hW0 : 0 < W := by linarith
  rw [Finset.sum_range_succ']
  set g : ℕ → ℝ := fun i => ((i : ℝ) + W) ^ (1 - s) / (s - 1) with hg
  have h1 : ∑ i ∈ Finset.range R, (((i + 1 : ℕ) : ℝ) + W) ^ (-s) ≤ W ^ (1 - s) / (s - 1) := by
    calc ∑ i ∈ Finset.range R, (((i + 1 : ℕ) : ℝ) + W) ^ (-s)
        ≤ ∑ i ∈ Finset.range R, (g i - g (i + 1)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := rpow_succ_le_sub (t := (i : ℝ) + W) (by positivity) hs
          simp only [hg]
          push_cast
          rw [show (i : ℝ) + 1 + W = (i : ℝ) + W + 1 by ring, ← sub_div]
          exact h
      _ = g 0 - g R := Finset.sum_range_sub' g R
      _ ≤ W ^ (1 - s) / (s - 1) := by
          have hs1 : 0 < s - 1 := by linarith
          have : 0 ≤ g R := by simp only [hg]; positivity
          have h0 : g 0 = W ^ (1 - s) / (s - 1) := by simp only [hg, Nat.cast_zero, zero_add]
          linarith
  have h0 : (((0 : ℕ) : ℝ) + W) ^ (-s) ≤ W ^ (1 - s) := by
    rw [Nat.cast_zero, zero_add]
    exact Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  calc ∑ i ∈ Finset.range R, (((i + 1 : ℕ) : ℝ) + W) ^ (-s) + (((0 : ℕ) : ℝ) + W) ^ (-s)
      ≤ W ^ (1 - s) / (s - 1) + W ^ (1 - s) := add_le_add h1 h0
    _ = (1 + 1 / (s - 1)) * W ^ (1 - s) := by ring

/-- The constant `2d · 2^{d-1} (1 + 1/(n - d))` of the lattice sum `Σ_z (|z| + W)^{-n}`. -/
private def sumC (d : ℕ) (n : ℝ) : ℝ := 2 * d * 2 ^ (d - 1) * (1 + 1 / (n - d))

private theorem sumC_nonneg (d : ℕ) {n : ℝ} (hn : (d : ℝ) < n) : 0 ≤ sumC d n := by
  unfold sumC
  have : 0 < n - d := by linarith
  positivity

/-- `Σ_{z ∈ ℤ^d} (|z| + W)^{-n} ≤ sumC d n · W^{d-n}` for `n > d`, `W ≥ 1`. -/
private theorem sum_wt_le (hd : 1 ≤ d) {n W : ℝ} (hn : (d : ℝ) < n) (hW : 1 ≤ W) :
    Summable (fun z : Fin d → ℤ => ((zdInf z : ℝ) + W) ^ (-n)) ∧
      ∑' z : Fin d → ℤ, ((zdInf z : ℝ) + W) ^ (-n) ≤ sumC d n * W ^ ((d : ℝ) - n) := by
  have hW0 : 0 < W := by linarith
  have hs : 1 < n - d + 1 := by linarith
  have hterm : ∀ j : ℕ, 2 * d * (2 * (j : ℝ) + 1) ^ (d - 1) * ((j : ℝ) + W) ^ (-n) ≤
      2 * d * 2 ^ (d - 1) * ((j : ℝ) + W) ^ (-(n - d + 1)) := by
    intro j
    have hjW : 0 < (j : ℝ) + W := by positivity
    have h1 : (2 * (j : ℝ) + 1) ^ (d - 1) ≤ (2 * ((j : ℝ) + W)) ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : ((j : ℝ) + W) ^ (d - 1) * ((j : ℝ) + W) ^ (-n) =
        ((j : ℝ) + W) ^ (-(n - d + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hjW, Nat.cast_sub hd]
      congr 1
      push_cast
      ring
    calc 2 * d * (2 * (j : ℝ) + 1) ^ (d - 1) * ((j : ℝ) + W) ^ (-n)
        ≤ 2 * d * (2 * ((j : ℝ) + W)) ^ (d - 1) * ((j : ℝ) + W) ^ (-n) := by gcongr
      _ = 2 * d * 2 ^ (d - 1) * (((j : ℝ) + W) ^ (d - 1) * ((j : ℝ) + W) ^ (-n)) := by
          rw [mul_pow]; ring
      _ = _ := by rw [h2]
  refine summable_zdInf hd (f := fun j : ℕ => ((j : ℝ) + W) ^ (-n)) (fun j => by positivity) ?_
  intro R
  calc ∑ j ∈ Finset.range (R + 1), 2 * d * (2 * (j : ℝ) + 1) ^ (d - 1) * ((j : ℝ) + W) ^ (-n)
      ≤ ∑ j ∈ Finset.range (R + 1), 2 * d * 2 ^ (d - 1) * ((j : ℝ) + W) ^ (-(n - d + 1)) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * d * 2 ^ (d - 1) * ∑ j ∈ Finset.range (R + 1), ((j : ℝ) + W) ^ (-(n - d + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * d * 2 ^ (d - 1) * ((1 + 1 / (n - d + 1 - 1)) * W ^ (1 - (n - d + 1))) := by
        gcongr
        exact sum_range_rpow_le hW hs R
    _ = sumC d n * W ^ ((d : ℝ) - n) := by
        rw [show n - d + 1 - 1 = n - d by ring, show 1 - (n - d + 1) = (d : ℝ) - n by ring]
        unfold sumC
        ring

/-- The lattice sum of `(|x + y| + W)^{-n}` over `y`. -/
private theorem sum_wt_add_le (hd : 1 ≤ d) {n W : ℝ} (hn : (d : ℝ) < n) (hW : 1 ≤ W)
    (x : Fin d → ℤ) :
    Summable (fun y : Fin d → ℤ => ((zdInf (x + y) : ℝ) + W) ^ (-n)) ∧
      ∑' y : Fin d → ℤ, ((zdInf (x + y) : ℝ) + W) ^ (-n) ≤ sumC d n * W ^ ((d : ℝ) - n) := by
  obtain ⟨h1, h2⟩ := sum_wt_le hd hn hW
  refine ⟨(Equiv.addLeft x).summable_iff.2 h1, ?_⟩
  exact ((Equiv.addLeft x).tsum_eq (fun z => ((zdInf z : ℝ) + W) ^ (-n))).trans_le h2

/-- The lattice sum of `(|x - y| + W)^{-n}` over `y`. -/
private theorem sum_wt_sub_le (hd : 1 ≤ d) {n W : ℝ} (hn : (d : ℝ) < n) (hW : 1 ≤ W)
    (x : Fin d → ℤ) :
    Summable (fun y : Fin d → ℤ => ((zdInf (x - y) : ℝ) + W) ^ (-n)) ∧
      ∑' y : Fin d → ℤ, ((zdInf (x - y) : ℝ) + W) ^ (-n) ≤ sumC d n * W ^ ((d : ℝ) - n) := by
  obtain ⟨h1, h2⟩ := sum_wt_le hd hn hW
  refine ⟨(Equiv.subLeft x).summable_iff.2 h1, ?_⟩
  exact ((Equiv.subLeft x).tsum_eq (fun z => ((zdInf z : ℝ) + W) ^ (-n))).trans_le h2

/-- `a^{-u} b^{-v} ≤ 2^m R^{-m} b^{-(u+v-m)}` for `b ≤ a`, `R ≤ a + b`, `0 ≤ m ≤ u`. -/
private theorem rpow_mul_rpow_le_aux {a b R u v m : ℝ} (hb : 0 < b) (hR : 0 < R)
    (hba : b ≤ a) (hab : R ≤ a + b) (hm : 0 ≤ m) (hmu : m ≤ u) :
    a ^ (-u) * b ^ (-v) ≤ 2 ^ m * R ^ (-m) * b ^ (-(u + v - m)) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have h1 : a ^ (-(u - m)) ≤ b ^ (-(u - m)) := Real.rpow_le_rpow_of_nonpos hb hba (by linarith)
  have h2 : a ^ (-m) ≤ (R / 2) ^ (-m) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h3 : (R / 2) ^ (-m) = 2 ^ m * R ^ (-m) := by
    rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  calc a ^ (-u) * b ^ (-v) = a ^ (-m) * (a ^ (-(u - m)) * b ^ (-v)) := by
        rw [← mul_assoc, ← Real.rpow_add ha]; congr 2; ring
    _ ≤ (R / 2) ^ (-m) * (b ^ (-(u - m)) * b ^ (-v)) := by gcongr
    _ = 2 ^ m * R ^ (-m) * b ^ (-(u + v - m)) := by
        rw [h3, ← Real.rpow_add hb]; congr 2; ring

/-- `a^{-u} b^{-v} ≤ 2^m R^{-m} (a^{-(u+v-m)} + b^{-(u+v-m)})` for `R ≤ a + b` and
`0 ≤ m ≤ min(u, v)`. -/
private theorem rpow_mul_rpow_le {a b R u v m : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 < R)
    (hab : R ≤ a + b) (hm : 0 ≤ m) (hmu : m ≤ u) (hmv : m ≤ v) :
    a ^ (-u) * b ^ (-v) ≤ 2 ^ m * R ^ (-m) * (a ^ (-(u + v - m)) + b ^ (-(u + v - m))) := by
  have hC : 0 ≤ 2 ^ m * R ^ (-m) := by positivity
  have hA : 0 ≤ a ^ (-(u + v - m)) := by positivity
  have hB : 0 ≤ b ^ (-(u + v - m)) := by positivity
  rcases le_total b a with h | h
  · have := rpow_mul_rpow_le_aux (v := v) hb hR h hab hm hmu
    nlinarith
  · have := rpow_mul_rpow_le_aux (v := u) ha hR h (by linarith) hm hmv
    rw [show v + u - m = u + v - m by ring] at this
    nlinarith

/-- `C ≤ W^e` once `W ≥ |C|^{1/e}`. -/
private theorem le_rpow_of_le {C e W : ℝ} (he : 0 < e) (hWC : |C| ^ (1 / e) ≤ W) :
    C ≤ W ^ e :=
  calc C ≤ |C| := le_abs_self _
    _ = (|C| ^ (1 / e)) ^ e := by
        rw [← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
    _ ≤ W ^ e := Real.rpow_le_rpow (by positivity) hWC he.le

/-- `zdInf x ≤ zdInf (x + y) + zdInf y`. -/
private theorem zdInf_le_add (x y : Fin d → ℤ) : zdInf x ≤ zdInf (x + y) + zdInf y := by
  have h := zdInf_add_le (x + y) (-y)
  rwa [add_neg_cancel_right, zdInf_neg] at h

/-- `zdInf x ≤ zdInf α + zdInf (x - α)`. -/
private theorem zdInf_le_sub (x α : Fin d → ℤ) : zdInf x ≤ zdInf α + zdInf (x - α) := by
  have h := zdInf_add_le α (x - α)
  rwa [add_sub_cancel] at h

/-- Splitting a sum over `ℤ^d` along a finite set. -/
private theorem tsum_split {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (S : Finset (Fin d → ℤ))
    (f : (Fin d → ℤ) → E) (hf : Summable f) :
    ∑' y, f y = ∑ y ∈ S, f y + ∑' y, (if y ∈ S then 0 else f y) := by
  have h1 : HasSum (fun y => if y ∈ S then f y else 0) (∑ y ∈ S, f y) := by
    have h : HasSum (fun y => if y ∈ S then f y else 0) (∑ y ∈ S, if y ∈ S then f y else 0) :=
      hasSum_sum_of_ne_finset_zero (fun y hy => by simp [hy])
    rwa [show (∑ y ∈ S, if y ∈ S then f y else 0) = ∑ y ∈ S, f y from
      Finset.sum_congr rfl fun y hy => by simp [hy]] at h
  have h2 : Summable fun y => if y ∈ S then 0 else f y := by
    have := hf.sub h1.summable
    refine this.congr fun y => ?_
    by_cases hy : y ∈ S <;> simp [hy]
  have h3 := h1.add h2.hasSum
  have he : (fun y => (if y ∈ S then f y else 0) + (if y ∈ S then 0 else f y)) = f := by
    funext y; by_cases hy : y ∈ S <;> simp [hy]
  rw [he] at h3
  exact h3.tsum_eq

end Sums

/-! ## The cancellation estimate for `Θ_∞ ∗ k` -/

section Cancel

variable {d : ℕ}

/-- The cancellation bound of [I, Lemma 7.3] for real symmetric box-mean-zero `g`, extended to
complex `g` through its real and imaginary parts. -/
private theorem cancel_complex {Θ : (Fin d → ℤ) → ℂ} {W K : ℕ} {c δ : ℝ}
    (hcan : ∀ K : ℕ, W ≤ K → ∀ g : (Fin d → ℤ) → ℝ, (∀ y, g (-y) = g y) →
      ∑ y ∈ boxZ d K, g y = 0 → ∀ x₀ : Fin d → ℤ, (K : ℝ) ^ (1 + c) ≤ zdInf x₀ →
        ‖∑ y ∈ boxZ d K, Θ (x₀ + y) * g y‖ ≤
          (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x₀) ^ 2 * |g y|) *
            (1 / ((W : ℝ) ^ 2 * (zdInf x₀ : ℝ) ^ ((d : ℝ) - 2 - δ))))
    (hK : W ≤ K) (g : (Fin d → ℤ) → ℂ) (hg : ∀ y, g (-y) = g y)
    (hg0 : ∑ y ∈ boxZ d K, g y = 0) (x : Fin d → ℤ) (hx : (K : ℝ) ^ (1 + c) ≤ zdInf x) :
    ‖∑ y ∈ boxZ d K, Θ (x + y) * g y‖ ≤
      2 * (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * ‖g y‖) *
        (1 / ((W : ℝ) ^ 2 * (zdInf x : ℝ) ^ ((d : ℝ) - 2 - δ))) := by
  have hre := hcan K hK (fun y => (g y).re) (fun y => by simp only [hg])
    (by rw [← Complex.re_sum, hg0, Complex.zero_re]) x hx
  have him := hcan K hK (fun y => (g y).im) (fun y => by simp only [hg])
    (by rw [← Complex.im_sum, hg0, Complex.zero_im]) x hx
  have hsplit : ∑ y ∈ boxZ d K, Θ (x + y) * g y =
      ∑ y ∈ boxZ d K, Θ (x + y) * ((g y).re : ℂ) +
        Complex.I * ∑ y ∈ boxZ d K, Θ (x + y) * ((g y).im : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    conv_lhs => rw [← Complex.re_add_im (g y)]
    ring
  set B : ℝ := 1 / ((W : ℝ) ^ 2 * (zdInf x : ℝ) ^ ((d : ℝ) - 2 - δ)) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have h1 : ∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * |(g y).re| ≤
      ∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * ‖g y‖ :=
    Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (sq_nonneg _)
  have h2 : ∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * |(g y).im| ≤
      ∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * ‖g y‖ :=
    Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (sq_nonneg _)
  rw [hsplit]
  calc _ ≤ ‖∑ y ∈ boxZ d K, Θ (x + y) * ((g y).re : ℂ)‖ +
        ‖Complex.I * ∑ y ∈ boxZ d K, Θ (x + y) * ((g y).im : ℂ)‖ := norm_add_le _ _
    _ = ‖∑ y ∈ boxZ d K, Θ (x + y) * ((g y).re : ℂ)‖ +
        ‖∑ y ∈ boxZ d K, Θ (x + y) * ((g y).im : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * |(g y).re|) * B +
        (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x) ^ 2 * |(g y).im|) * B := add_le_add hre him
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h1 hB0, mul_le_mul_of_nonneg_right h2 hB0]

/-- The weighted box sum of the near piece:
`Σ_{|y| ≤ K} (|y|/X)² |g(y)| ≤ X^{-(2-2δ)} a W^{2d-4} Σ_y (|y| + W)^{-(2d-6+δ)}`, when `g = k` off
the origin, `K ≤ X` and `|k(y)| ≤ a W^{2d-4} (|y| + W)^{-(2d-4-δ)}`. -/
private theorem near_sum_le (hd : 6 ≤ d) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 16) {w X : ℝ}
    (hw : 1 ≤ w) (hX1 : 1 ≤ X) {K : ℕ} (hKX : (K : ℝ) ≤ X) (k g : (Fin d → ℤ) → ℂ) {a : ℝ}
    (ha : 0 ≤ a)
    (hk : ∀ y, y ≠ 0 →
      ‖k y‖ ≤ a * w ^ (2 * (d : ℝ) - 4) * ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)))
    (hg : ∀ y, y ≠ 0 → g y = k y) :
    ∑ y ∈ boxZ d K, ((zdInf y : ℝ) / X) ^ 2 * ‖g y‖ ≤
      X ^ (-(2 - 2 * δ)) * (a * w ^ (2 * (d : ℝ) - 4) *
        (sumC d (2 * d - 6 + δ) * w ^ ((d : ℝ) - (2 * d - 6 + δ)))) := by
  have hX0 : 0 < X := by linarith
  have hw0 : 0 < w := by linarith
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : (d : ℝ) < 2 * d - 6 + δ := by linarith
  obtain ⟨hsum, htsum⟩ := sum_wt_le (d := d) (by omega) hb hw
  set A : ℝ := a * w ^ (2 * (d : ℝ) - 4) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hterm : ∀ y ∈ boxZ d K, ((zdInf y : ℝ) / X) ^ 2 * ‖g y‖ ≤
      X ^ (-(2 - 2 * δ)) * (A * ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 6 + δ))) := by
    intro y hy
    have hyK : (zdInf y : ℝ) ≤ K := by exact_mod_cast mem_boxZ_iff.1 hy
    have hy0 : (0 : ℝ) ≤ zdInf y := Nat.cast_nonneg _
    have hyw : 0 < (zdInf y : ℝ) + w := by positivity
    by_cases h0 : y = 0
    · subst h0
      have : zdInf (0 : Fin d → ℤ) = 0 := by simp [zdInf]
      simp only [this, Nat.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_mul]
      positivity
    have hgk : ((zdInf y : ℝ) / X) ^ 2 * ‖g y‖ = ((zdInf y : ℝ) / X) ^ 2 * ‖k y‖ := by
      rw [hg y h0]
    rw [hgk]
    have hq0 : 0 ≤ (zdInf y : ℝ) / X := by positivity
    have hq1 : (zdInf y : ℝ) / X ≤ 1 := by rw [div_le_one hX0]; linarith
    have h1 : ((zdInf y : ℝ) / X) ^ 2 ≤ ((zdInf y : ℝ) / X) ^ (2 - 2 * δ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hq0 hq1 (by linarith) (by push_cast; linarith)
    have h2 : ((zdInf y : ℝ) / X) ^ (2 - 2 * δ) ≤
        ((zdInf y : ℝ) + w) ^ (2 - 2 * δ) * X ^ (-(2 - 2 * δ)) := by
      rw [Real.div_rpow hy0 hX0.le, div_eq_mul_inv, ← Real.rpow_neg hX0.le]
      gcongr <;> linarith
    have h3 : ((zdInf y : ℝ) + w) ^ (2 - 2 * δ) * ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)) =
        ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 6 + δ)) := by
      rw [← Real.rpow_add hyw]; congr 1; ring
    calc ((zdInf y : ℝ) / X) ^ 2 * ‖k y‖
        ≤ (((zdInf y : ℝ) + w) ^ (2 - 2 * δ) * X ^ (-(2 - 2 * δ))) *
            (A * ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ))) := by
          gcongr
          · exact h1.trans h2
          · exact hk y h0
      _ = X ^ (-(2 - 2 * δ)) * (A * (((zdInf y : ℝ) + w) ^ (2 - 2 * δ) *
            ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)))) := by ring
      _ = _ := by rw [h3]
  have hXp : 0 ≤ X ^ (-(2 - 2 * δ)) := by positivity
  calc ∑ y ∈ boxZ d K, ((zdInf y : ℝ) / X) ^ 2 * ‖g y‖
      ≤ ∑ y ∈ boxZ d K, X ^ (-(2 - 2 * δ)) * (A * ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 6 + δ))) :=
        Finset.sum_le_sum hterm
    _ = X ^ (-(2 - 2 * δ)) *
          (A * ∑ y ∈ boxZ d K, ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 6 + δ))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ X ^ (-(2 - 2 * δ)) * (A * ∑' y, ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 6 + δ))) := by
        gcongr
        exact hsum.sum_le_tsum _ fun y _ => by positivity
    _ ≤ _ := by
        gcongr

/-- `(2^d)^{-1} Y^{-(d-8δ)} ≤ (X + w)^{-(d-8δ)}` when `X + w ≤ 2Y`. -/
private theorem target_lower {δ X w Y : ℝ} (hd8 : 8 * δ ≤ d) (hXw : 0 < X + w) (hY : 0 < Y)
    (h : X + w ≤ 2 * Y) (hδ : 0 ≤ δ) :
    ((2 : ℝ) ^ d)⁻¹ * Y ^ (-((d : ℝ) - 8 * δ)) ≤ (X + w) ^ (-((d : ℝ) - 8 * δ)) := by
  have h1 : (2 * Y) ^ (-((d : ℝ) - 8 * δ)) ≤ (X + w) ^ (-((d : ℝ) - 8 * δ)) :=
    Real.rpow_le_rpow_of_nonpos hXw h (by linarith)
  rw [Real.mul_rpow (by norm_num) hY.le] at h1
  have h2 : ((2 : ℝ) ^ d)⁻¹ ≤ (2 : ℝ) ^ (-((d : ℝ) - 8 * δ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc ((2 : ℝ) ^ d)⁻¹ * Y ^ (-((d : ℝ) - 8 * δ))
      ≤ (2 : ℝ) ^ (-((d : ℝ) - 8 * δ)) * Y ^ (-((d : ℝ) - 8 * δ)) := by gcongr
    _ ≤ _ := h1

/-- The near piece is at most half of `a W^d (2^d)^{-1} X^{-(d-8δ)}` once
`2^{d+2} sumC ≤ W^δ`. -/
private theorem near_final (hd : 6 ≤ d) {δ w X a : ℝ} (hδ : 0 < δ) (hw : 1 ≤ w) (hX1 : 1 ≤ X)
    (ha : 0 ≤ a) (hM : 2 ^ (d + 2) * sumC d (2 * d - 6 + δ) ≤ w ^ δ) :
    2 * (X ^ (-(2 - 2 * δ)) * (a * w ^ (2 * (d : ℝ) - 4) *
        (sumC d (2 * d - 6 + δ) * w ^ ((d : ℝ) - (2 * d - 6 + δ))))) *
      (1 / (w ^ 2 * X ^ ((d : ℝ) - 2 - δ))) ≤
    1 / 2 * (a * w ^ (d : ℝ) * (((2 : ℝ) ^ d)⁻¹ * X ^ (-((d : ℝ) - 8 * δ)))) := by
  have hw0 : 0 < w := by linarith
  have hX0 : 0 < X := by linarith
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  set sb := sumC d (2 * d - 6 + δ) with hsb
  have hsb0 : 0 ≤ sb := sumC_nonneg d (by linarith)
  have e1 : 1 / (w ^ 2 * X ^ ((d : ℝ) - 2 - δ)) = w ^ (-(2 : ℝ)) * X ^ (-((d : ℝ) - 2 - δ)) := by
    rw [Real.rpow_neg hw0.le, Real.rpow_neg hX0.le, Real.rpow_two, one_div, mul_inv]
  have ew : w ^ (2 * (d : ℝ) - 4) * w ^ ((d : ℝ) - (2 * d - 6 + δ)) * w ^ (-(2 : ℝ)) =
      w ^ (d : ℝ) * w ^ (-δ) := by
    rw [← Real.rpow_add hw0, ← Real.rpow_add hw0, ← Real.rpow_add hw0]; congr 1; ring
  have eX : X ^ (-(2 - 2 * δ)) * X ^ (-((d : ℝ) - 2 - δ)) =
      X ^ (-((d : ℝ) - 8 * δ)) * X ^ (-(5 * δ)) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; ring
  have hX5 : X ^ (-(5 * δ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  have hwδ : 0 < w ^ δ := Real.rpow_pos_of_pos hw0 δ
  have hc : 2 * sb * w ^ (-δ) ≤ 1 / 2 * ((2 : ℝ) ^ d)⁻¹ := by
    rw [Real.rpow_neg hw0.le, pow_add] at *
    rw [show 2 * sb * (w ^ δ)⁻¹ = 2 * sb / w ^ δ by ring, div_le_iff₀ hwδ]
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    field_simp
    nlinarith
  have hP : 0 ≤ a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ)) := by positivity
  calc 2 * (X ^ (-(2 - 2 * δ)) * (a * w ^ (2 * (d : ℝ) - 4) *
        (sb * w ^ ((d : ℝ) - (2 * d - 6 + δ))))) * (1 / (w ^ 2 * X ^ ((d : ℝ) - 2 - δ)))
      = 2 * sb * a * (w ^ (2 * (d : ℝ) - 4) * w ^ ((d : ℝ) - (2 * d - 6 + δ)) * w ^ (-(2 : ℝ))) *
          (X ^ (-(2 - 2 * δ)) * X ^ (-((d : ℝ) - 2 - δ))) := by rw [e1]; ring
    _ = (2 * sb * w ^ (-δ)) * (a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ))) * X ^ (-(5 * δ)) := by
        rw [ew, eX]; ring
    _ ≤ (2 * sb * w ^ (-δ)) * (a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ))) * 1 := by
        gcongr
    _ ≤ (1 / 2 * ((2 : ℝ) ^ d)⁻¹) * (a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ))) := by
        rw [mul_one]; gcongr
    _ = _ := by ring

/-- The correction and outer pieces together are at most half of
`a W^d (2^d)^{-1} X^{-(d-8δ)}` once `2^{d+1} (1 + 2^d) sumC ≤ W^δ`. -/
private theorem far_final (hd : 6 ≤ d) {δ w X a β c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 16)
    (hw : 1 ≤ w) (hwX : w ≤ X) (ha : 0 ≤ a) (hc0 : 0 < c) (hcd : c * d = δ) (hβ0 : 0 < β)
    (hβc : β * (1 + c) = 1) (hM : 2 ^ (d + 1) * ((1 + 2 ^ d) * sumC d (d + δ)) ≤ w ^ δ) :
    w ^ (-(2 : ℝ)) * (X + w) ^ (-((d : ℝ) - 2 - δ)) *
        (a * w ^ (2 * (d : ℝ) - 4) * (X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ)) * sumC d (d + δ)) +
      w ^ (-(2 : ℝ)) * (a * w ^ (2 * (d : ℝ) - 4) * (X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ))) *
        (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) * (2 * sumC d (d + δ)) ≤
    1 / 2 * (a * w ^ (d : ℝ) * (((2 : ℝ) ^ d)⁻¹ * X ^ (-((d : ℝ) - 8 * δ)))) := by
  have hw0 : 0 < w := by linarith
  have hX1 : 1 ≤ X := hw.trans hwX
  have hX0 : 0 < X := by linarith
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  set sn := sumC d (d + δ) with hsn
  have hsn0 : 0 ≤ sn := sumC_nonneg d (by linarith)
  set p : ℝ := (d : ℝ) - 2 - δ with hp
  have h2p : 2 * (2 : ℝ) ^ p ≤ 2 ^ d := by
    have : 2 * (2 : ℝ) ^ p = (2 : ℝ) ^ (p + 1) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
    rw [this, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hp]; linarith)
  have hexp : ((d : ℝ) - 6) + (-p) + β * (-((d : ℝ) - 4 - 2 * δ)) ≤
      -((d : ℝ) - 8 * δ) + (-δ) := by
    have h1 : ((d : ℝ) - 4 - 6 * δ) * (1 + c) ≤ (d : ℝ) - 4 - 2 * δ := by
      nlinarith [mul_pos hc0 hδ]
    have key : (d : ℝ) - 4 - 6 * δ ≤ β * ((d : ℝ) - 4 - 2 * δ) := by
      calc (d : ℝ) - 4 - 6 * δ = ((d : ℝ) - 4 - 6 * δ) * (β * (1 + c)) := by rw [hβc, mul_one]
        _ = β * (((d : ℝ) - 4 - 6 * δ) * (1 + c)) := by ring
        _ ≤ β * ((d : ℝ) - 4 - 2 * δ) := mul_le_mul_of_nonneg_left h1 hβ0.le
    rw [hp]
    linarith
  have hXp : (X + w) ^ (-p) ≤ X ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hX0 (by linarith) (by rw [hp]; linarith)
  have hww : w ^ (-(2 : ℝ)) * w ^ (2 * (d : ℝ) - 4) ≤ w ^ (d : ℝ) * X ^ ((d : ℝ) - 6) := by
    have : w ^ (-(2 : ℝ)) * w ^ (2 * (d : ℝ) - 4) = w ^ (d : ℝ) * w ^ ((d : ℝ) - 6) := by
      rw [← Real.rpow_add hw0, ← Real.rpow_add hw0]; congr 1; ring
    rw [this]
    gcongr
  have hXX : X ^ ((d : ℝ) - 6) * (X ^ (-p) * (X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ))) ≤
      X ^ (-((d : ℝ) - 8 * δ)) * X ^ (-δ) := by
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0,
      ← add_assoc]
    exact Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hXw : X ^ (-δ) ≤ w ^ (-δ) := Real.rpow_le_rpow_of_nonpos hw0 hwX (by linarith)
  have hwδ : 0 < w ^ δ := Real.rpow_pos_of_pos hw0 δ
  have hc : (1 + 2 ^ d) * sn * w ^ (-δ) ≤ 1 / 2 * ((2 : ℝ) ^ d)⁻¹ := by
    rw [Real.rpow_neg hw0.le, pow_succ] at *
    rw [show (1 + 2 ^ d) * sn * (w ^ δ)⁻¹ = (1 + 2 ^ d) * sn / w ^ δ by ring,
      div_le_iff₀ hwδ]
    have h2d : (0 : ℝ) < 2 ^ d := by positivity
    field_simp
    nlinarith
  set T₀ : ℝ := (X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ)) with hT₀
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hP : 0 ≤ a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ)) := by positivity
  calc w ^ (-(2 : ℝ)) * (X + w) ^ (-p) * (a * w ^ (2 * (d : ℝ) - 4) * T₀ * sn) +
        w ^ (-(2 : ℝ)) * (a * w ^ (2 * (d : ℝ) - 4) * T₀) * (2 ^ p * (X + w) ^ (-p)) * (2 * sn)
      = a * (w ^ (-(2 : ℝ)) * w ^ (2 * (d : ℝ) - 4)) * ((X + w) ^ (-p) * T₀) *
          (sn * (1 + 2 * 2 ^ p)) := by ring
    _ ≤ a * (w ^ (d : ℝ) * X ^ ((d : ℝ) - 6)) * (X ^ (-p) * T₀) * (sn * (1 + 2 ^ d)) := by
        gcongr
    _ = a * w ^ (d : ℝ) * (X ^ ((d : ℝ) - 6) * (X ^ (-p) * T₀)) * (sn * (1 + 2 ^ d)) := by ring
    _ ≤ a * w ^ (d : ℝ) * (X ^ (-((d : ℝ) - 8 * δ)) * X ^ (-δ)) * (sn * (1 + 2 ^ d)) := by
        gcongr
    _ ≤ a * w ^ (d : ℝ) * (X ^ (-((d : ℝ) - 8 * δ)) * w ^ (-δ)) * (sn * (1 + 2 ^ d)) := by
        gcongr
    _ = ((1 + 2 ^ d) * sn * w ^ (-δ)) * (a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ))) := by ring
    _ ≤ (1 / 2 * ((2 : ℝ) ^ d)⁻¹) * (a * w ^ (d : ℝ) * X ^ (-((d : ℝ) - 8 * δ))) := by gcongr
    _ = _ := by ring

/-- The crude bound in the regime `|x| < W^{1+c}`: `sup |Θ| · Σ |k|`, with `Σ |k|` at most
`a W^{2d-4} sQ W^{d-(2d-4-δ)}`, is at most `a W^d (|x| + W)^{-(d-8δ)}` once `2^d sQ ≤ W^δ`. -/
private theorem small_final (hd : 6 ≤ d) {δ w X a c sQ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 16)
    (hw : 1 ≤ w) (hX0 : 0 ≤ X) (ha : 0 ≤ a) (hc0 : 0 < c) (hcd : c * d = δ)
    (hXlt : X < w ^ (1 + c)) (hsQ0 : 0 ≤ sQ) (hM : 2 ^ d * sQ ≤ w ^ δ) :
    w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) * (a * w ^ (2 * (d : ℝ) - 4) *
        (sQ * w ^ ((d : ℝ) - (2 * d - 4 - δ)))) ≤
      a * w ^ (d : ℝ) * (X + w) ^ (-((d : ℝ) - 8 * δ)) := by
  have hw0 : 0 < w := by linarith
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hwc : w ≤ w ^ (1 + c) := by
    calc w = w ^ (1 : ℝ) := (Real.rpow_one w).symm
      _ ≤ w ^ (1 + c) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  have hY : 0 < w ^ (1 + c) := Real.rpow_pos_of_pos hw0 _
  have hlow := target_lower (d := d) (δ := δ) (X := X) (w := w) (Y := w ^ (1 + c))
    (by linarith) (by linarith) hY (by linarith) hδ.le
  have he : w ^ (7 * δ) ≤ w ^ (d : ℝ) * (w ^ (1 + c)) ^ (-((d : ℝ) - 8 * δ)) := by
    rw [← Real.rpow_mul hw0.le, ← Real.rpow_add hw0]
    apply Real.rpow_le_rpow_of_exponent_le hw
    have : (d : ℝ) + (1 + c) * (-((d : ℝ) - 8 * δ)) = 7 * δ + 8 * (c * δ) := by
      linear_combination (-1 : ℝ) * hcd
    rw [this]
    nlinarith [mul_pos hc0 hδ]
  have ew : w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) * w ^ (2 * (d : ℝ) - 4) *
      w ^ ((d : ℝ) - (2 * d - 4 - δ)) = w ^ (2 * δ) := by
    rw [← Real.rpow_add hw0, ← Real.rpow_add hw0, ← Real.rpow_add hw0]; congr 1; ring
  have h5 : w ^ δ ≤ w ^ (5 * δ) := Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  have e7 : w ^ (7 * δ) = w ^ (2 * δ) * w ^ (5 * δ) := by
    rw [← Real.rpow_add hw0]; ring_nf
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hw2 : 0 < w ^ (2 * δ) := Real.rpow_pos_of_pos hw0 _
  have hab : sQ * w ^ (2 * δ) ≤ ((2 : ℝ) ^ d)⁻¹ * w ^ (7 * δ) := by
    rw [e7]
    have : (2 : ℝ) ^ d * sQ ≤ w ^ (5 * δ) := hM.trans h5
    rw [inv_mul_eq_div, le_div_iff₀ h2d]
    nlinarith
  calc w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) * (a * w ^ (2 * (d : ℝ) - 4) *
        (sQ * w ^ ((d : ℝ) - (2 * d - 4 - δ))))
      = a * (sQ * (w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) * w ^ (2 * (d : ℝ) - 4) *
          w ^ ((d : ℝ) - (2 * d - 4 - δ)))) := by ring
    _ = a * (sQ * w ^ (2 * δ)) := by rw [ew]
    _ ≤ a * (((2 : ℝ) ^ d)⁻¹ * w ^ (7 * δ)) := by gcongr
    _ ≤ a * (((2 : ℝ) ^ d)⁻¹ * (w ^ (d : ℝ) * (w ^ (1 + c)) ^ (-((d : ℝ) - 8 * δ)))) := by
        gcongr
    _ = a * w ^ (d : ℝ) * (((2 : ℝ) ^ d)⁻¹ * (w ^ (1 + c)) ^ (-((d : ℝ) - 8 * δ))) := by ring
    _ ≤ _ := by gcongr

/-- The constant of the absorption condition `coreM d δ ≤ W^δ`. -/
private def coreM (d : ℕ) (δ : ℝ) : ℝ :=
  2 ^ (d + 2) *
    (sumC d (2 * d - 6 + δ) + (1 + 2 ^ d) * sumC d (d + δ) + sumC d (2 * d - 4 - δ) + 1)

/-- The estimate behind [I, (7.10)]: for `Θ` with the decay of [I, (7.7)] and the cancellation of
[I, Lemma 7.3] (exponent `δ`, `c = δ/d`), and `k` symmetric with total sum zero and
`|k(y)| ≤ a W^{2d-4} (|y| + W)^{-(2d-4-δ)} + a W^d W^δ 1_{y=0}`:
`|Σ_y Θ(x + y) k(y)| ≤ a W^d (|x| + W)^{-(d-8δ)}`, once `coreM d δ ≤ W^δ`. The term at `y = 0`
enters only the regime `|x| < W^{1+c}`, through `Σ_y |k(y)|`; in the regime `|x| ≥ W^{1+c}` the
bound reads `k` at `y ≠ 0` and through the total sum. -/
private theorem core (hd : 6 ≤ d) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 16) {W : ℕ} (hW1 : 1 ≤ W)
    (hM : coreM d δ ≤ (W : ℝ) ^ δ) (Θ : (Fin d → ℤ) → ℂ)
    (hΘ : ∀ z, ‖Θ z‖ ≤ 1 / ((W : ℝ) ^ 2 * ((zdInf z : ℝ) + W) ^ ((d : ℝ) - 2 - δ)))
    (hcan : ∀ K : ℕ, W ≤ K → ∀ g : (Fin d → ℤ) → ℝ, (∀ y, g (-y) = g y) →
      ∑ y ∈ boxZ d K, g y = 0 → ∀ x₀ : Fin d → ℤ, (K : ℝ) ^ (1 + δ / d) ≤ zdInf x₀ →
        ‖∑ y ∈ boxZ d K, Θ (x₀ + y) * g y‖ ≤
          (∑ y ∈ boxZ d K, ((zdInf y : ℝ) / zdInf x₀) ^ 2 * |g y|) *
            (1 / ((W : ℝ) ^ 2 * (zdInf x₀ : ℝ) ^ ((d : ℝ) - 2 - δ))))
    (k : (Fin d → ℤ) → ℂ) (hks : ∀ y, k (-y) = k y) (hk0 : ∑' y, k y = 0) {a : ℝ} (ha : 0 ≤ a)
    (hk : ∀ y, ‖k y‖ ≤ a * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      ((zdInf y : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - δ)) +
      (if y = 0 then a * (W : ℝ) ^ (d : ℝ) * (W : ℝ) ^ δ else 0))
    (x : Fin d → ℤ) :
    ‖∑' y, Θ (x + y) * k y‖ ≤
      a * (W : ℝ) ^ (d : ℝ) * ((zdInf x : ℝ) + W) ^ (-((d : ℝ) - 8 * δ)) := by
  set w : ℝ := (W : ℝ) with hwdef
  have hw : 1 ≤ w := by rw [hwdef]; exact_mod_cast hW1
  have hw0 : 0 < w := by linarith
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  set X : ℝ := (zdInf x : ℝ) with hXdef
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  set c : ℝ := δ / d with hc
  have hc0 : 0 < c := by positivity
  have hcd : c * d = δ := by rw [hc]; field_simp
  set β : ℝ := 1 / (1 + c) with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one (by linarith)]; linarith
  have hβc : β * (1 + c) = 1 := by rw [hβ]; field_simp
  have hM0 : 0 ≤ sumC d (2 * d - 6 + δ) := sumC_nonneg d (by linarith)
  have hM1 : 0 ≤ sumC d (d + δ) := sumC_nonneg d (by linarith)
  have hM2 : 0 ≤ sumC d (2 * d - 4 - δ) := sumC_nonneg d (by linarith)
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hMb : 2 ^ (d + 2) * sumC d (2 * d - 6 + δ) ≤ w ^ δ := by
    refine le_trans ?_ hM; unfold coreM
    have : 0 ≤ (1 + 2 ^ d) * sumC d (d + δ) := by positivity
    gcongr; linarith
  have hMn : 2 ^ (d + 1) * ((1 + 2 ^ d) * sumC d (d + δ)) ≤ w ^ δ := by
    refine le_trans ?_ hM; unfold coreM
    have h0 : 0 ≤ (1 + 2 ^ d) * sumC d (d + δ) := by positivity
    have h1 : (2 : ℝ) ^ (d + 1) ≤ 2 ^ (d + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc 2 ^ (d + 1) * ((1 + 2 ^ d) * sumC d (d + δ))
        ≤ 2 ^ (d + 2) * ((1 + 2 ^ d) * sumC d (d + δ)) := by gcongr
      _ ≤ _ := by gcongr; linarith
  have hMQ : 2 ^ d * (sumC d (2 * d - 4 - δ) + 1) ≤ w ^ δ := by
    refine le_trans ?_ hM; unfold coreM
    have h0 : 0 ≤ (1 + 2 ^ d) * sumC d (d + δ) := by positivity
    have h1 : (2 : ℝ) ^ d ≤ 2 ^ (d + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc 2 ^ d * (sumC d (2 * d - 4 - δ) + 1) ≤ 2 ^ (d + 2) * (sumC d (2 * d - 4 - δ) + 1) := by
          gcongr
      _ ≤ _ := by gcongr; linarith
  -- the bounds on `Θ`
  have hΘ' : ∀ z, ‖Θ z‖ ≤ w ^ (-(2 : ℝ)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - δ)) := by
    intro z
    have hz : 0 < (zdInf z : ℝ) + w := by positivity
    refine (hΘ z).trans (le_of_eq ?_)
    rw [Real.rpow_neg hw0.le, Real.rpow_neg hz.le, Real.rpow_two, one_div, mul_inv]
  have hΘb : ∀ z, ‖Θ z‖ ≤ w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) := by
    intro z
    refine (hΘ' z).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_nonpos hw0
      (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf z)]) (by linarith)
  -- summability
  have hQd : (d : ℝ) < 2 * d - 4 - δ := by linarith
  obtain ⟨hsQ, htQ⟩ := sum_wt_le (d := d) (by omega) hQd hw
  have hk' : ∀ y, y ≠ 0 → ‖k y‖ ≤ a * w ^ (2 * (d : ℝ) - 4) *
      ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)) := fun y hy => by
    simpa only [if_neg hy, add_zero] using hk y
  have hdiag := hasSum_ite_eq (0 : Fin d → ℤ) (a * w ^ (d : ℝ) * w ^ δ)
  have hkn : Summable fun y => ‖k y‖ :=
    Summable.of_nonneg_of_le (fun y => norm_nonneg _) hk ((hsQ.mul_left _).add hdiag.summable)
  have hF : Summable fun y => Θ (x + y) * k y := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun y => norm_nonneg _) (fun y => ?_)
      (hkn.mul_left (w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)))))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hΘb _) (norm_nonneg _)
  by_cases hreg : w ≤ X ^ β
  swap
  · -- the regime `|x| < W^{1+c}`
    push Not at hreg
    have hXlt : X < w ^ (1 + c) := by
      have h := Real.rpow_lt_rpow (by positivity) hreg (by linarith : (0 : ℝ) < 1 + c)
      rwa [← Real.rpow_mul hX0, hβc, Real.rpow_one] at h
    refine le_trans ?_ (small_final hd hδ hδ1 hw hX0 ha hc0 hcd hXlt (by linarith) hMQ)
    have ediag : a * w ^ (d : ℝ) * w ^ δ =
        a * w ^ (2 * (d : ℝ) - 4) * w ^ ((d : ℝ) - (2 * d - 4 - δ)) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hw0, ← Real.rpow_add hw0]; congr 2; ring
    have hsum2 := (hsQ.mul_left (a * w ^ (2 * (d : ℝ) - 4))).add hdiag.summable
    calc ‖∑' y, Θ (x + y) * k y‖ ≤ ∑' y, ‖Θ (x + y) * k y‖ := norm_tsum_le_tsum_norm hF.norm
      _ ≤ ∑' y, w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) *
            (a * w ^ (2 * (d : ℝ) - 4) * ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)) +
              (if y = 0 then a * w ^ (d : ℝ) * w ^ δ else 0)) := by
          refine hF.norm.tsum_le_tsum (fun y => ?_) (hsum2.mul_left _)
          rw [norm_mul]
          exact mul_le_mul (hΘb _) (hk y) (norm_nonneg _) (by positivity)
      _ = w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) *
            (a * w ^ (2 * (d : ℝ) - 4) * ∑' y, ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)) +
              a * w ^ (d : ℝ) * w ^ δ) := by
          rw [tsum_mul_left, (hsQ.mul_left _).tsum_add hdiag.summable, tsum_mul_left,
            hdiag.tsum_eq]
      _ ≤ w ^ (-(2 : ℝ)) * w ^ (-((d : ℝ) - 2 - δ)) *
            (a * w ^ (2 * (d : ℝ) - 4) * (sumC d (2 * d - 4 - δ) * w ^ ((d : ℝ) - (2 * d - 4 - δ))) +
              a * w ^ (d : ℝ) * w ^ δ) := by gcongr
      _ = _ := by rw [ediag]; ring
  -- the regime `|x| ≥ W^{1+c}`, with the box of radius `K = ⌊|x|^{1/(1+c)}⌋`
  have hX1 : 1 ≤ X := by
    by_contra h
    push Not at h
    have : X ^ β < 1 := Real.rpow_lt_one hX0 h hβ0
    linarith
  have hXβX : X ^ β ≤ X := by
    calc X ^ β ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hβ1
      _ = X := Real.rpow_one X
  have hwX : w ≤ X := hreg.trans hXβX
  set K : ℕ := ⌊X ^ β⌋₊ with hK
  have hWK : W ≤ K := Nat.le_floor hreg
  have hKXβ : (K : ℝ) ≤ X ^ β := Nat.floor_le (by positivity)
  have hKX : (K : ℝ) ≤ X := hKXβ.trans hXβX
  have hKc : (K : ℝ) ^ (1 + c) ≤ X := by
    calc (K : ℝ) ^ (1 + c) ≤ (X ^ β) ^ (1 + c) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hKXβ (by linarith)
      _ = X := by rw [← Real.rpow_mul hX0, hβc, Real.rpow_one]
  have hout : ∀ y, y ∉ boxZ d K → X ^ β ≤ (zdInf y : ℝ) + w := by
    intro y hy
    have h1 : K < zdInf y := by rw [mem_boxZ_iff] at hy; omega
    have h2 : X ^ β < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (K : ℝ) + 1 ≤ zdInf y := by exact_mod_cast h1
    linarith
  set S := boxZ d K with hS
  have hsplitF := tsum_split S (fun y => Θ (x + y) * k y) hF
  have hsplitk := tsum_split S k hkn.of_norm
  rw [hk0] at hsplitk
  set SK := ∑ y ∈ S, k y with hSK
  set g : (Fin d → ℤ) → ℂ := fun y => k y - if y = 0 then SK else 0 with hg
  have h0S : (0 : Fin d → ℤ) ∈ S := mem_boxZ_iff.2 (by simp [zdInf])
  have hgs : ∀ y, g (-y) = g y := by intro y; simp only [hg, hks, neg_eq_zero]
  have hg0 : ∑ y ∈ S, g y = 0 := by
    simp only [hg, Finset.sum_sub_distrib, Finset.sum_ite_eq', h0S, ite_true]
    exact sub_self _
  have hgk : ∀ y, y ≠ 0 → g y = k y := by intro y hy; simp [hg, hy]
  have hnear_eq : ∑ y ∈ S, Θ (x + y) * k y = ∑ y ∈ S, Θ (x + y) * g y + Θ x * SK := by
    simp only [hg, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', h0S,
      ite_true, add_zero]
    ring
  set kout : (Fin d → ℤ) → ℂ := fun y => if y ∈ S then 0 else k y with hkout_def
  set out : (Fin d → ℤ) → ℂ := fun y => if y ∈ S then 0 else Θ (x + y) * k y with hout_def
  have hSKeq : SK = -∑' y, kout y := eq_neg_of_add_eq_zero_left hsplitk.symm
  have hFeq : ∑' y, Θ (x + y) * k y = ∑ y ∈ S, Θ (x + y) * g y + Θ x * SK + ∑' y, out y := by
    rw [hsplitF, hnear_eq]
  -- the near piece
  have hnear : ‖∑ y ∈ S, Θ (x + y) * g y‖ ≤
      2 * (X ^ (-(2 - 2 * δ)) * (a * w ^ (2 * (d : ℝ) - 4) *
        (sumC d (2 * d - 6 + δ) * w ^ ((d : ℝ) - (2 * d - 6 + δ))))) *
      (1 / (w ^ 2 * X ^ ((d : ℝ) - 2 - δ))) := by
    refine (cancel_complex hcan hWK g hgs hg0 x hKc).trans ?_
    gcongr
    exact near_sum_le hd hδ hδ1 hw hX1 hKX k g ha hk' hgk
  -- the tail of `k` past the box
  set Tl : ℝ := a * w ^ (2 * (d : ℝ) - 4) * (X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ)) with hTl
  have hTl0 : 0 ≤ Tl := by positivity
  have hn : (d : ℝ) < d + δ := by linarith
  obtain ⟨hsn, htn⟩ := sum_wt_le (d := d) (by omega) hn hw
  have hwn : w ^ ((d : ℝ) - (d + δ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw (by linarith)
  have hkout : ∀ y, ‖kout y‖ ≤ Tl * ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ)) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [hkout_def, hy, ite_true, norm_zero]; positivity
    · simp only [hkout_def, hy, ite_false]
      have hyw : 0 < (zdInf y : ℝ) + w := by positivity
      have hy0 : y ≠ 0 := by rintro rfl; exact hy h0S
      refine (hk' y hy0).trans ?_
      have e : ((zdInf y : ℝ) + w) ^ (-(2 * (d : ℝ) - 4 - δ)) =
          ((zdInf y : ℝ) + w) ^ (-((d : ℝ) - 4 - 2 * δ)) *
            ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ)) := by
        rw [← Real.rpow_add hyw]; congr 1; ring
      have h2 : ((zdInf y : ℝ) + w) ^ (-((d : ℝ) - 4 - 2 * δ)) ≤
          (X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (hout y hy) (by linarith)
      rw [e, hTl]
      calc a * w ^ (2 * (d : ℝ) - 4) * (((zdInf y : ℝ) + w) ^ (-((d : ℝ) - 4 - 2 * δ)) *
            ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ)))
          ≤ a * w ^ (2 * (d : ℝ) - 4) * ((X ^ β) ^ (-((d : ℝ) - 4 - 2 * δ)) *
            ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ))) := by gcongr
        _ = _ := by ring
  have hkoutS : Summable fun y => ‖kout y‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hkout (hsn.mul_left Tl)
  have hkoutT : ∑' y, ‖kout y‖ ≤ Tl * sumC d (d + δ) := by
    calc ∑' y, ‖kout y‖ ≤ ∑' y, Tl * ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ)) :=
          hkoutS.tsum_le_tsum hkout (hsn.mul_left Tl)
      _ = Tl * ∑' y, ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ)) := tsum_mul_left
      _ ≤ Tl * (sumC d (d + δ) * w ^ ((d : ℝ) - (d + δ))) := by gcongr
      _ ≤ Tl * sumC d (d + δ) := by
          gcongr
          calc sumC d (d + δ) * w ^ ((d : ℝ) - (d + δ)) ≤ sumC d (d + δ) * 1 := by gcongr
            _ = _ := mul_one _
  -- the outer piece
  have hp0 : 0 ≤ (d : ℝ) - 2 - δ := by linarith
  have hpn : (d : ℝ) - 2 - δ ≤ (d : ℝ) + δ := by linarith
  have hout_pt : ∀ y, ‖out y‖ ≤ w ^ (-(2 : ℝ)) * Tl *
      (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) *
      (((zdInf (x + y) : ℝ) + w) ^ (-((d : ℝ) + δ)) + ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ))) := by
    intro y
    have hout_eq : ‖out y‖ = ‖Θ (x + y)‖ * ‖kout y‖ := by
      by_cases hy : y ∈ S
      · simp [hout_def, hkout_def, hy]
      · simp [hout_def, hkout_def, hy]
    rw [hout_eq]
    have hR : X + w ≤ ((zdInf (x + y) : ℝ) + w) + ((zdInf y : ℝ) + w) := by
      have h := zdInf_le_add x y
      have : (zdInf x : ℝ) ≤ zdInf (x + y) + zdInf y := by exact_mod_cast h
      linarith
    have hpt := rpow_mul_rpow_le (u := (d : ℝ) - 2 - δ) (v := (d : ℝ) + δ)
      (m := (d : ℝ) - 2 - δ) (by positivity : (0 : ℝ) < (zdInf (x + y) : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf y : ℝ) + w) (by positivity : (0 : ℝ) < X + w) hR hp0
      le_rfl hpn
    rw [show (d : ℝ) - 2 - δ + ((d : ℝ) + δ) - ((d : ℝ) - 2 - δ) = (d : ℝ) + δ by ring] at hpt
    calc ‖Θ (x + y)‖ * ‖kout y‖
        ≤ (w ^ (-(2 : ℝ)) * ((zdInf (x + y) : ℝ) + w) ^ (-((d : ℝ) - 2 - δ))) *
            (Tl * ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ))) :=
          mul_le_mul (hΘ' _) (hkout y) (norm_nonneg _) (by positivity)
      _ = w ^ (-(2 : ℝ)) * Tl * (((zdInf (x + y) : ℝ) + w) ^ (-((d : ℝ) - 2 - δ)) *
            ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ))) := by ring
      _ ≤ w ^ (-(2 : ℝ)) * Tl * (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ)) *
            (((zdInf (x + y) : ℝ) + w) ^ (-((d : ℝ) + δ)) +
              ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ)))) :=
          mul_le_mul_of_nonneg_left hpt (by positivity)
      _ = _ := by ring
  obtain ⟨hsn', htn'⟩ := sum_wt_add_le (d := d) (by omega) hn hw x
  have hbS := hsn'.add hsn
  have houtS : Summable fun y => ‖out y‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hout_pt (hbS.mul_left _)
  have houtT : ∑' y, ‖out y‖ ≤ w ^ (-(2 : ℝ)) * Tl *
      (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) * (2 * sumC d (d + δ)) := by
    have hC : 0 ≤ w ^ (-(2 : ℝ)) * Tl *
        (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) := by
      positivity
    calc ∑' y, ‖out y‖ ≤ ∑' y, w ^ (-(2 : ℝ)) * Tl *
          (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) *
          (((zdInf (x + y) : ℝ) + w) ^ (-((d : ℝ) + δ)) + ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ))) :=
          houtS.tsum_le_tsum hout_pt (hbS.mul_left _)
      _ = w ^ (-(2 : ℝ)) * Tl * (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) *
          (∑' y, ((zdInf (x + y) : ℝ) + w) ^ (-((d : ℝ) + δ)) +
            ∑' y, ((zdInf y : ℝ) + w) ^ (-((d : ℝ) + δ))) := by
          rw [tsum_mul_left, hsn'.tsum_add hsn]
      _ ≤ w ^ (-(2 : ℝ)) * Tl * (2 ^ ((d : ℝ) - 2 - δ) * (X + w) ^ (-((d : ℝ) - 2 - δ))) *
          (sumC d (d + δ) * w ^ ((d : ℝ) - (d + δ)) +
            sumC d (d + δ) * w ^ ((d : ℝ) - (d + δ))) := by
          gcongr
      _ ≤ _ := by
          gcongr
          calc sumC d (d + δ) * w ^ ((d : ℝ) - (d + δ)) + sumC d (d + δ) * w ^ ((d : ℝ) - (d + δ))
              ≤ sumC d (d + δ) * 1 + sumC d (d + δ) * 1 := by gcongr
            _ = _ := by ring
  have hΘx : ‖Θ x‖ ≤ w ^ (-(2 : ℝ)) * (X + w) ^ (-((d : ℝ) - 2 - δ)) := hΘ' x
  -- assembly
  have hmain : ‖∑' y, Θ (x + y) * k y‖ ≤ ‖∑ y ∈ S, Θ (x + y) * g y‖ +
      ‖Θ x‖ * ∑' y, ‖kout y‖ + ∑' y, ‖out y‖ := by
    rw [hFeq, hSKeq]
    calc _ ≤ ‖∑ y ∈ S, Θ (x + y) * g y + Θ x * -∑' y, kout y‖ + ‖∑' y, out y‖ :=
          norm_add_le _ _
      _ ≤ ‖∑ y ∈ S, Θ (x + y) * g y‖ + ‖Θ x * -∑' y, kout y‖ + ‖∑' y, out y‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by
          gcongr
          · rw [norm_mul, norm_neg]
            gcongr
            exact norm_tsum_le_tsum_norm hkoutS
          · exact norm_tsum_le_tsum_norm houtS
  have hfar := far_final hd hδ hδ1 hw hwX ha hc0 hcd hβ0 hβc hMn
  have hnf := near_final hd hδ hw hX1 ha hMb
  have hlow := target_lower (d := d) (δ := δ) (X := X) (w := w) (Y := X)
    (by linarith) (by linarith) (by linarith) (by linarith) hδ.le
  have hsum2 : ‖Θ x‖ * ∑' y, ‖kout y‖ ≤
      w ^ (-(2 : ℝ)) * (X + w) ^ (-((d : ℝ) - 2 - δ)) * (Tl * sumC d (d + δ)) :=
    mul_le_mul hΘx hkoutT (by positivity) (by positivity)
  calc ‖∑' y, Θ (x + y) * k y‖
      ≤ ‖∑ y ∈ S, Θ (x + y) * g y‖ + ‖Θ x‖ * ∑' y, ‖kout y‖ + ∑' y, ‖out y‖ := hmain
    _ ≤ 1 / 2 * (a * w ^ (d : ℝ) * (((2 : ℝ) ^ d)⁻¹ * X ^ (-((d : ℝ) - 8 * δ)))) +
        1 / 2 * (a * w ^ (d : ℝ) * (((2 : ℝ) ^ d)⁻¹ * X ^ (-((d : ℝ) - 8 * δ)))) := by
        rw [hTl] at hsum2 houtT
        linarith
    _ = a * w ^ (d : ℝ) * (((2 : ℝ) ^ d)⁻¹ * X ^ (-((d : ℝ) - 8 * δ))) := by ring
    _ ≤ _ := by gcongr

end Cancel

/-! ## [I, Lemma 7.4, (7.10)] -/

/-- [I, Lemma 7.4, (7.10)] (with `Θ_∞` in its proof): for `d ≥ 6`, a profile shape `ψ`, the
constants `C`, and a kernel of order `l` with `KerInfHyp`: for every `τ > 0` there is `W₀` with
`|(Θ_∞ ∗ k_l)(x)| ≤ W^{-(l-2)d/2} (|x| + W)^{-(d-τ)}` for `W ≥ W₀` and every kernel `s` of
`InfKernel ψ C W`. -/
theorem thetaSigmaInf :
  ∀ (d : ℕ), 6 ≤ d → ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (cψ : ℝ),
    ProfileShape ψ cψ → ∀ (C : ℕ → ℝ) (k : KerInf d) (l : ℕ), KerInfHyp k l →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
        ∀ x : Fin d → ℤ, ‖convZ (ThetaInf s) (k l W) x‖ ≤
          (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((zdInf x : ℝ) + W) ^ (-((d : ℝ) - τ)) := by
  intro d hd ψ cψ hψ C k l hk τ hτ
  set τ' : ℝ := min τ (1 / 2) with hτ'
  have hτ'0 : 0 < τ' := lt_min hτ (by norm_num)
  have hτ'τ : τ' ≤ τ := min_le_left _ _
  have hτ'1 : τ' ≤ 1 / 2 := min_le_right _ _
  set δ : ℝ := τ' / 8 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 16 := by rw [hδdef]; linarith
  have hd3 : 3 ≤ d := by omega
  have hd6 : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨W₁, h₁⟩ := ThetaInf_decay d hd3 ψ cψ hψ C δ hδ
  obtain ⟨W₂, h₂⟩ := ThetaInf_cancel d hd3 ψ cψ hψ C (δ / d) δ (by positivity) hδ
  obtain ⟨W₃, h₃⟩ := hk.2.1 δ hδ
  refine ⟨max (max W₁ W₂) (max W₃ (max 1 (|coreM d δ| ^ (1 / δ)))), ?_⟩
  intro W hW s hs x
  have hW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW₂ : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW₃ : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW1r : (1 : ℝ) ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hWM : |coreM d δ| ^ (1 / δ) ≤ (W : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hW
  have hW1 : 1 ≤ W := by exact_mod_cast hW1r
  have hM : coreM d δ ≤ (W : ℝ) ^ δ := le_rpow_of_le hδ hWM
  have hconv : convZ (ThetaInf s) (k l W) x = ∑' y, ThetaInf s (x + y) * k l W y := by
    unfold convZ
    rw [← (Equiv.addLeft x).tsum_eq (fun α => ThetaInf s α * k l W (x - α))]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addLeft]
    rw [show x - (x + y) = -y by abel, hk.1 W y]
  rw [hconv]
  have hWpos : (0 : ℝ) < W := by linarith
  have e1 : (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (d : ℝ) =
      (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  have hk₃ : ∀ y, ‖k l W y‖ ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      ((zdInf y : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - δ)) +
      (if y = 0 then (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (d : ℝ) * (W : ℝ) ^ δ else 0) := by
    intro y; rw [e1]; exact h₃ W hW₃ y
  refine (core hd hδ hδ1 hW1 hM (ThetaInf s) ((h₁ W hW₁ s hs).2) (h₂ W hW₂ s hs) (k l W)
    (hk.1 W) (hk.2.2 W) (a := (W : ℝ) ^ (-((l : ℝ) * d / 2))) (by positivity) hk₃ x).trans ?_
  rw [e1, show 8 * δ = τ' by rw [hδdef]; ring]
  have hx1 : (1 : ℝ) ≤ (zdInf x : ℝ) + W := by
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf x)]
  gcongr

/-! ## Convolutions on `ℤ^d` -/

section Conv

variable {d : ℕ}

/-- The lattice sum of `(|y - α| + W)^{-n}` over `y`. -/
private theorem sum_wt_subR_le (hd : 1 ≤ d) {n W : ℝ} (hn : (d : ℝ) < n) (hW : 1 ≤ W)
    (α : Fin d → ℤ) :
    Summable (fun y : Fin d → ℤ => ((zdInf (y - α) : ℝ) + W) ^ (-n)) ∧
      ∑' y : Fin d → ℤ, ((zdInf (y - α) : ℝ) + W) ^ (-n) ≤ sumC d n * W ^ ((d : ℝ) - n) := by
  obtain ⟨h1, h2⟩ := sum_wt_le hd hn hW
  refine ⟨(Equiv.subRight α).summable_iff.2 h1, ?_⟩
  exact ((Equiv.subRight α).tsum_eq (fun z => ((zdInf z : ℝ) + W) ^ (-n))).trans_le h2

/-- `convZ` is commutative. -/
private theorem convZ_comm (f g : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ) :
    convZ f g x = convZ g f x := by
  unfold convZ
  rw [← (Equiv.subLeft x).tsum_eq (fun α => g α * f (x - α))]
  refine tsum_congr fun α => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

/-- `convZ` is associative under absolute summability of the double sum. -/
private theorem convZ_assoc (F k Θ : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ)
    (h : Summable (Function.uncurry fun (α β : Fin d → ℤ) => F α * k (β - α) * Θ (x - β))) :
    convZ (convZ F k) Θ x = convZ F (convZ k Θ) x := by
  unfold convZ
  have lhs : ∑' β, (∑' α, F α * k (β - α)) * Θ (x - β) =
      ∑' β, ∑' α, F α * k (β - α) * Θ (x - β) :=
    tsum_congr fun β => by rw [tsum_mul_right]
  have rhs : ∑' α, F α * ∑' γ, k γ * Θ (x - α - γ) =
      ∑' α, ∑' β, F α * k (β - α) * Θ (x - β) := by
    refine tsum_congr fun α => ?_
    rw [← tsum_mul_left, ← (Equiv.subRight α).tsum_eq (fun γ => F α * (k γ * Θ (x - α - γ)))]
    refine tsum_congr fun β => ?_
    simp only [Equiv.subRight_apply]
    rw [sub_sub_sub_cancel_right]
    ring
  rw [lhs, rhs]
  exact h.tsum_comm

/-- Absolute summability of `F(α) k(β - α) Θ(x - β)` over `(α, β)` for power-law bounds with
`p ≤ Q`, `Q > d` and `u + p > d`. -/
private theorem summable_triple (hd : 1 ≤ d) {w u p Q cF ck cΘ : ℝ} (hw : 1 ≤ w)
    (F k Θ : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ) (hcF : 0 ≤ cF) (hck : 0 ≤ ck) (hcΘ : 0 ≤ cΘ)
    (hF : ∀ z, ‖F z‖ ≤ cF * ((zdInf z : ℝ) + w) ^ (-u))
    (hk : ∀ z, ‖k z‖ ≤ ck * ((zdInf z : ℝ) + w) ^ (-Q))
    (hΘ : ∀ z, ‖Θ z‖ ≤ cΘ * ((zdInf z : ℝ) + w) ^ (-p))
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hpQ : p ≤ Q) (hQ : (d : ℝ) < Q) (hup : (d : ℝ) < u + p) :
    Summable (Function.uncurry fun (α β : Fin d → ℤ) => F α * k (β - α) * Θ (x - β)) := by
  have hw0 : 0 < w := by linarith
  set G : (Fin d → ℤ) × (Fin d → ℤ) → ℝ := fun q =>
    cF * ((zdInf q.1 : ℝ) + w) ^ (-u) * (ck * ((zdInf (q.2 - q.1) : ℝ) + w) ^ (-Q)) *
      (cΘ * ((zdInf (x - q.2) : ℝ) + w) ^ (-p)) with hG
  have hG0 : 0 ≤ G := fun q => by simp only [hG]; positivity
  have hle : ∀ q, ‖Function.uncurry (fun (α β : Fin d → ℤ) => F α * k (β - α) * Θ (x - β)) q‖ ≤
      G q := by
    intro q
    simp only [Function.uncurry, hG, norm_mul]
    exact mul_le_mul (mul_le_mul (hF _) (hk _) (norm_nonneg _) (by positivity)) (hΘ _)
      (norm_nonneg _) (by positivity)
  -- the inner sums
  set D : (Fin d → ℤ) → ℝ := fun α => cF * ck * cΘ * (2 ^ p *
    (((zdInf (x - α) : ℝ) + w) ^ (-p))) * ((zdInf α : ℝ) + w) ^ (-u) with hD
  have hinner : ∀ α, ∀ β, G (α, β) ≤ D α * (((zdInf (β - α) : ℝ) + w) ^ (-Q) +
      ((zdInf (x - β) : ℝ) + w) ^ (-Q)) := by
    intro α β
    have hR : (zdInf (x - α) : ℝ) + w ≤
        ((zdInf (β - α) : ℝ) + w) + ((zdInf (x - β) : ℝ) + w) := by
      have h := zdInf_add_le (β - α) (x - β)
      rw [show β - α + (x - β) = x - α by abel] at h
      have : (zdInf (x - α) : ℝ) ≤ zdInf (β - α) + zdInf (x - β) := by exact_mod_cast h
      linarith
    have hpt := rpow_mul_rpow_le (u := Q) (v := p) (m := p)
      (by positivity : (0 : ℝ) < (zdInf (β - α) : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf (x - β) : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf (x - α) : ℝ) + w) hR hp hpQ le_rfl
    rw [show Q + p - p = Q by ring] at hpt
    simp only [hG, hD]
    calc cF * ((zdInf α : ℝ) + w) ^ (-u) * (ck * ((zdInf (β - α) : ℝ) + w) ^ (-Q)) *
          (cΘ * ((zdInf (x - β) : ℝ) + w) ^ (-p))
        = cF * ck * cΘ * ((zdInf α : ℝ) + w) ^ (-u) *
          (((zdInf (β - α) : ℝ) + w) ^ (-Q) * ((zdInf (x - β) : ℝ) + w) ^ (-p)) := by ring
      _ ≤ cF * ck * cΘ * ((zdInf α : ℝ) + w) ^ (-u) *
          (2 ^ p * ((zdInf (x - α) : ℝ) + w) ^ (-p) *
            (((zdInf (β - α) : ℝ) + w) ^ (-Q) + ((zdInf (x - β) : ℝ) + w) ^ (-Q))) := by
          gcongr
      _ = _ := by ring
  have hs1 := fun α => (sum_wt_subR_le (d := d) hd hQ hw α).1
  have ht1 := fun α => (sum_wt_subR_le (d := d) hd hQ hw α).2
  obtain ⟨hs2, ht2⟩ := sum_wt_sub_le (d := d) hd hQ hw x
  have hsumβ : ∀ α, Summable fun β => ((zdInf (β - α) : ℝ) + w) ^ (-Q) +
      ((zdInf (x - β) : ℝ) + w) ^ (-Q) := fun α => (hs1 α).add hs2
  have hsG : ∀ α, Summable fun β => G (α, β) := fun α =>
    Summable.of_nonneg_of_le (fun β => hG0 _) (hinner α) ((hsumβ α).mul_left _)
  have htG : ∀ α, ∑' β, G (α, β) ≤ D α * (2 * (sumC d Q * w ^ ((d : ℝ) - Q))) := by
    intro α
    calc ∑' β, G (α, β) ≤ ∑' β, D α * (((zdInf (β - α) : ℝ) + w) ^ (-Q) +
          ((zdInf (x - β) : ℝ) + w) ^ (-Q)) :=
          (hsG α).tsum_le_tsum (hinner α) ((hsumβ α).mul_left _)
      _ = D α * (∑' β, ((zdInf (β - α) : ℝ) + w) ^ (-Q) +
          ∑' β, ((zdInf (x - β) : ℝ) + w) ^ (-Q)) := by
          rw [tsum_mul_left, (hs1 α).tsum_add hs2]
      _ ≤ D α * (sumC d Q * w ^ ((d : ℝ) - Q) + sumC d Q * w ^ ((d : ℝ) - Q)) := by
          have : 0 ≤ D α := by simp only [hD]; positivity
          gcongr
          exact ht1 α
      _ = _ := by ring
  -- the outer sum
  obtain ⟨hs3, -⟩ := sum_wt_le (d := d) hd hup hw
  obtain ⟨hs4, -⟩ := sum_wt_sub_le (d := d) hd hup hw x
  have hDsum : Summable D := by
    refine Summable.of_nonneg_of_le (fun α => by simp only [hD]; positivity) (fun α => ?_)
      ((hs3.add hs4).mul_left (cF * ck * cΘ * 2 ^ p))
    have hR : (1 : ℝ) ≤ ((zdInf α : ℝ) + w) + ((zdInf (x - α) : ℝ) + w) := by
      linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf α),
        (Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf (x - α))]
    have hpt := rpow_mul_rpow_le (u := u) (v := p) (m := 0)
      (by positivity : (0 : ℝ) < (zdInf α : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf (x - α) : ℝ) + w) one_pos hR le_rfl hu hp
    rw [Real.rpow_zero, Real.one_rpow, one_mul, one_mul, sub_zero] at hpt
    simp only [hD]
    calc cF * ck * cΘ * (2 ^ p * ((zdInf (x - α) : ℝ) + w) ^ (-p)) * ((zdInf α : ℝ) + w) ^ (-u)
        = cF * ck * cΘ * 2 ^ p * (((zdInf α : ℝ) + w) ^ (-u) *
            ((zdInf (x - α) : ℝ) + w) ^ (-p)) := by ring
      _ ≤ cF * ck * cΘ * 2 ^ p * (((zdInf α : ℝ) + w) ^ (-(u + p)) +
            ((zdInf (x - α) : ℝ) + w) ^ (-(u + p))) := by gcongr
  have hGsum : Summable G := by
    refine (summable_prod_of_nonneg hG0).2 ⟨hsG, ?_⟩
    exact Summable.of_nonneg_of_le (fun α => tsum_nonneg fun β => hG0 _) htG
      (hDsum.mul_right _)
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _) hle hGsum)

/-- One step of the chain: for power-law bounds on `F`, `k`, `Θ` and `Θ ∗ k`,
`|((F ∗ k) ∗ Θ)(x)| ≤ cF cH (|x| + W)^{-m}`, once
`2^{d+1} sumC d n ≤ W^{n-d}` with `n = u + v - m > d`. -/
private theorem chain_step (hd : 1 ≤ d) {w u v p Q m cF ck cΘ cH : ℝ} (hw : 1 ≤ w)
    (F k Θ : (Fin d → ℤ) → ℂ) (hcF : 0 ≤ cF) (hck : 0 ≤ ck) (hcΘ : 0 ≤ cΘ) (hcH : 0 ≤ cH)
    (hF : ∀ z, ‖F z‖ ≤ cF * ((zdInf z : ℝ) + w) ^ (-u))
    (hk : ∀ z, ‖k z‖ ≤ ck * ((zdInf z : ℝ) + w) ^ (-Q))
    (hΘ : ∀ z, ‖Θ z‖ ≤ cΘ * ((zdInf z : ℝ) + w) ^ (-p))
    (hH : ∀ z, ‖convZ Θ k z‖ ≤ cH * ((zdInf z : ℝ) + w) ^ (-v))
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hpQ : p ≤ Q) (hQ : (d : ℝ) < Q) (hup : (d : ℝ) < u + p)
    (hm : 0 ≤ m) (hmu : m ≤ u) (hmv : m ≤ v) (hmd : m ≤ d) (hn : (d : ℝ) < u + v - m)
    (habs : 2 ^ (d + 1) * sumC d (u + v - m) ≤ w ^ (u + v - m - d)) (x : Fin d → ℤ) :
    ‖convZ (convZ F k) Θ x‖ ≤ cF * cH * ((zdInf x : ℝ) + w) ^ (-m) := by
  have hw0 : 0 < w := by linarith
  rw [convZ_assoc F k Θ x (summable_triple hd hw F k Θ x hcF hck hcΘ hF hk hΘ hu hp hpQ hQ hup)]
  have hcomm : convZ k Θ = convZ Θ k := funext (convZ_comm k Θ)
  rw [hcomm]
  set H := convZ Θ k with hHdef
  set n := u + v - m with hndef
  change ‖∑' α, F α * H (x - α)‖ ≤ _
  set C₀ : ℝ := cF * cH * (2 ^ m * ((zdInf x : ℝ) + w) ^ (-m)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hpt : ∀ α, ‖F α * H (x - α)‖ ≤
      C₀ * (((zdInf α : ℝ) + w) ^ (-n) + ((zdInf (x - α) : ℝ) + w) ^ (-n)) := by
    intro α
    have hR : (zdInf x : ℝ) + w ≤ ((zdInf α : ℝ) + w) + ((zdInf (x - α) : ℝ) + w) := by
      have h := zdInf_le_sub x α
      have : (zdInf x : ℝ) ≤ zdInf α + zdInf (x - α) := by exact_mod_cast h
      linarith
    have h := rpow_mul_rpow_le (u := u) (v := v) (m := m)
      (by positivity : (0 : ℝ) < (zdInf α : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf (x - α) : ℝ) + w)
      (by positivity : (0 : ℝ) < (zdInf x : ℝ) + w) hR hm hmu hmv
    rw [norm_mul]
    calc ‖F α‖ * ‖H (x - α)‖
        ≤ (cF * ((zdInf α : ℝ) + w) ^ (-u)) * (cH * ((zdInf (x - α) : ℝ) + w) ^ (-v)) :=
          mul_le_mul (hF α) (hH _) (norm_nonneg _) (by positivity)
      _ = cF * cH * (((zdInf α : ℝ) + w) ^ (-u) * ((zdInf (x - α) : ℝ) + w) ^ (-v)) := by ring
      _ ≤ cF * cH * (2 ^ m * ((zdInf x : ℝ) + w) ^ (-m) *
            (((zdInf α : ℝ) + w) ^ (-n) + ((zdInf (x - α) : ℝ) + w) ^ (-n))) := by gcongr
      _ = _ := by rw [hC₀]; ring
  obtain ⟨hs1, ht1⟩ := sum_wt_le hd hn hw
  obtain ⟨hs2, ht2⟩ := sum_wt_sub_le hd hn hw x
  have hS := (hs1.add hs2).mul_left C₀
  have hnS : Summable fun α => ‖F α * H (x - α)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hS
  have hsn0 : 0 ≤ sumC d n := sumC_nonneg d hn
  have hwn : w ^ ((d : ℝ) - n) * w ^ (n - d) = 1 := by
    rw [← Real.rpow_add hw0]; simp
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ d := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hmd
  have hC : 2 ^ m * (2 * (sumC d n * w ^ ((d : ℝ) - n))) ≤ 1 := by
    have hwd : 0 ≤ w ^ ((d : ℝ) - n) := by positivity
    calc 2 ^ m * (2 * (sumC d n * w ^ ((d : ℝ) - n)))
        ≤ 2 ^ d * (2 * (sumC d n * w ^ ((d : ℝ) - n))) := by gcongr
      _ = (2 ^ (d + 1) * sumC d n) * w ^ ((d : ℝ) - n) := by rw [pow_succ]; ring
      _ ≤ w ^ (n - d) * w ^ ((d : ℝ) - n) := by gcongr
      _ = 1 := by rw [mul_comm, hwn]
  calc ‖∑' α, F α * H (x - α)‖ ≤ ∑' α, ‖F α * H (x - α)‖ := norm_tsum_le_tsum_norm hnS
    _ ≤ ∑' α, C₀ * (((zdInf α : ℝ) + w) ^ (-n) + ((zdInf (x - α) : ℝ) + w) ^ (-n)) :=
        hnS.tsum_le_tsum hpt hS
    _ = C₀ * (∑' α, ((zdInf α : ℝ) + w) ^ (-n) + ∑' α, ((zdInf (x - α) : ℝ) + w) ^ (-n)) := by
        rw [tsum_mul_left, hs1.tsum_add hs2]
    _ ≤ C₀ * (sumC d n * w ^ ((d : ℝ) - n) + sumC d n * w ^ ((d : ℝ) - n)) := by gcongr
    _ = cF * cH * ((zdInf x : ℝ) + w) ^ (-m) * (2 ^ m * (2 * (sumC d n * w ^ ((d : ℝ) - n)))) := by
        rw [hC₀]; ring
    _ ≤ cF * cH * ((zdInf x : ℝ) + w) ^ (-m) * 1 := by gcongr
    _ = _ := mul_one _

/-- A threshold `W₀` that works for every entry of a list. -/
private theorem exists_W0_list {P : ℕ → ℕ → Prop} (o : List ℕ)
    (h : ∀ l ∈ o, ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → P l W) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ l ∈ o, P l W := by
  induction o with
  | nil => exact ⟨0, fun W _ l hl => absurd hl List.not_mem_nil⟩
  | cons a o ih =>
    obtain ⟨Wa, ha⟩ := h a List.mem_cons_self
    obtain ⟨Wo, hoo⟩ := ih fun l hl => h l (List.mem_cons_of_mem a hl)
    refine ⟨max Wa Wo, fun W hW l hl => ?_⟩
    rcases List.mem_cons.1 hl with rfl | hl'
    · exact ha W (le_trans (le_max_left _ _) hW)
    · exact hoo W (le_trans (le_max_right _ _) hW) l hl'

end Conv

/-- `Σᵢ -(oᵢ - 2) d/2 = -(ord(Θ_o) - 2) d/2` for the order `Σ oᵢ + 2 - 2l` of a labelled `Θ`
edge. -/
private theorem sum_map_ord (d : ℕ) (o : List ℕ) :
    (o.map fun l : ℕ => -(((l : ℝ) - 2) * d / 2)).sum =
      -((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2 := by
  have h : ∀ o : List ℕ, (o.map fun l : ℕ => -(((l : ℝ) - 2) * d / 2)).sum =
      -((((o.sum : ℕ) : ℝ) - 2 * (o.length : ℝ)) * d / 2) := by
    intro o
    induction o with
    | nil => simp
    | cons a o ih =>
      rw [List.map_cons, List.sum_cons, ih, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_add, Nat.cast_one]
      ring
  rw [h]
  simp only [Kind.ord, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

/-! ## [I, Lemma 7.4, (7.11)] -/

/-- [I, Lemma 7.4, (7.11)]: for a label `o` whose entries satisfy `KerInfHyp`,
`|(Θ_∞ Σ^∞_{o₁} Θ_∞ ⋯ Σ^∞_{o_l} Θ_∞)(x)| ≤ W^{-(k-2)d/2} W^{-2} (|x| + W)^{-(d-2-τ)}`. -/
theorem chainInf :
  ∀ (d : ℕ), 6 ≤ d → ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (cψ : ℝ),
    ProfileShape ψ cψ → ∀ (C : ℕ → ℝ) (k : KerInf d) (o : List ℕ), (∀ l ∈ o, KerInfHyp k l) →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
        ∀ x : Fin d → ℤ, ‖chainZ s k W o x‖ ≤
          (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-2 : ℝ) * ((zdInf x : ℝ) + W) ^ (-((d : ℝ) - 2 - τ))) := by
  intro d hd ψ cψ hψ C k o ho τ hτ
  have hd6 : (6 : ℝ) ≤ d := by exact_mod_cast hd
  set N : ℕ := o.length with hN
  set τ' : ℝ := min τ (1 / 4) with hτ'
  have hτ'0 : 0 < τ' := lt_min hτ (by norm_num)
  have hτ'τ : τ' ≤ τ := min_le_left _ _
  have hτ'1 : τ' ≤ 1 / 4 := min_le_right _ _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set ε : ℝ := τ' / (2 * ((N : ℝ) + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεN : 2 * ε * ((N : ℝ) + 1) = τ' := by rw [hεdef]; field_simp
  have hε1 : 2 * ε ≤ τ' := by nlinarith
  obtain ⟨W₁, h₁⟩ := ThetaInf_decay d (by omega) ψ cψ hψ C (2 * ε) (by positivity)
  set P : ℕ → ℕ → Prop := fun l W =>
    (∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s → ∀ z : Fin d → ℤ,
      ‖convZ (ThetaInf s) (k l W) z‖ ≤
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - ε))) ∧
    (∀ z : Fin d → ℤ, ‖k l W z‖ ≤ ((W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) +
      (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (2 * (d : ℝ) - 4 - 1)) *
      ((zdInf z : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - 1))) with hP
  have hl : ∀ l ∈ o, ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → P l W := by
    intro l hlo
    obtain ⟨Wa, ha⟩ := thetaSigmaInf d hd ψ cψ hψ C k l (ho l hlo) ε hε
    obtain ⟨Wb, hb⟩ := (ho l hlo).2.1 1 one_pos
    refine ⟨max (max Wa Wb) 1, fun W hW =>
      ⟨ha W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW), fun z => ?_⟩⟩
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hW)
    have hz0 : 0 < (zdInf z : ℝ) + W := by positivity
    refine (hb W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW) z).trans ?_
    rw [add_mul]
    refine add_le_add le_rfl ?_
    split_ifs with hz
    · subst hz
      have h0 : zdInf (0 : Fin d → ℤ) = 0 := by simp [zdInf]
      have e : (W : ℝ) ^ (2 * (d : ℝ) - 4 - 1) * (W : ℝ) ^ (-(2 * (d : ℝ) - 4 - 1)) = 1 := by
        rw [← Real.rpow_add hW0]; simp
      rw [h0, Nat.cast_zero, zero_add]
      refine le_of_eq ?_
      calc (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ (1 : ℝ)
          = (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ (1 : ℝ) *
            ((W : ℝ) ^ (2 * (d : ℝ) - 4 - 1) * (W : ℝ) ^ (-(2 * (d : ℝ) - 4 - 1))) := by
            rw [e, mul_one]
        _ = _ := by ring
    · positivity
  obtain ⟨W₂, h₂⟩ := exists_W0_list o hl
  set B : ℝ := 2 ^ (d + 1) * sumC d (d + ε) with hB
  refine ⟨max (max W₁ W₂) (max 1 (|B| ^ (1 / ε))), ?_⟩
  intro W hW s hs x
  have hW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW₂ : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWB : |B| ^ (1 / ε) ≤ (W : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have habs : B ≤ (W : ℝ) ^ ε := le_rpow_of_le hε hWB
  have hPo := h₂ W hW₂
  set w : ℝ := (W : ℝ) with hwdef
  have hw0 : 0 < w := by linarith
  have hΘ : ∀ z, ‖ThetaInf s z‖ ≤
      w ^ (-(2 : ℝ)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - 2 * ε)) := by
    intro z
    have hz : 0 < (zdInf z : ℝ) + w := by positivity
    refine ((h₁ W hW₁ s hs).2 z).trans (le_of_eq ?_)
    rw [Real.rpow_neg hw0.le, Real.rpow_neg hz.le, Real.rpow_two, one_div, mul_inv]
  have key : ∀ (o' : List ℕ), (∀ l ∈ o', P l W) → ∀ (F : (Fin d → ℤ) → ℂ) (e σ : ℝ), 0 ≤ σ →
      σ + 2 * ε * o'.length ≤ τ' →
      (∀ z, ‖F z‖ ≤ w ^ e * (w ^ (-(2 : ℝ)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - σ)))) →
      ∀ z, ‖o'.foldl (fun F l => convZ (convZ F (k l W)) (ThetaInf s)) F z‖ ≤
        w ^ (e + (o'.map fun l : ℕ => -(((l : ℝ) - 2) * d / 2)).sum) *
          (w ^ (-(2 : ℝ)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - (σ + 2 * ε * o'.length)))) := by
    intro o'
    induction o' with
    | nil =>
      intro _ F e σ _ _ hF z
      simpa using hF z
    | cons l o'' ih =>
      intro hPl' F e σ hσ hστ hF z
      rw [List.foldl_cons]
      have hPl := hPl' l List.mem_cons_self
      have hlen : ((l :: o'').length : ℝ) = (o''.length : ℝ) + 1 := by
        rw [List.length_cons]; push_cast; ring
      rw [hlen] at hστ
      have hl0 : (0 : ℝ) ≤ o''.length := Nat.cast_nonneg _
      have hσ1 : σ + 2 * ε ≤ τ' := by nlinarith
      have hstep : ∀ z, ‖convZ (convZ F (k l W)) (ThetaInf s) z‖ ≤
          w ^ (e + -(((l : ℝ) - 2) * d / 2)) *
            (w ^ (-(2 : ℝ)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - (σ + 2 * ε)))) := by
        intro z
        have hn : (d : ℝ) - 2 - σ + ((d : ℝ) - ε) - ((d : ℝ) - 2 - (σ + 2 * ε)) = d + ε := by ring
        have h := chain_step (d := d) (by omega) hW1 F (k l W) (ThetaInf s)
          (cF := w ^ e * w ^ (-(2 : ℝ)))
          (ck := w ^ (-((l : ℝ) * d / 2)) * w ^ (2 * (d : ℝ) - 4) +
            w ^ (-(((l : ℝ) - 2) * d / 2)) * w ^ (1 : ℝ) * w ^ (2 * (d : ℝ) - 4 - 1))
          (cΘ := w ^ (-(2 : ℝ))) (cH := w ^ (-(((l : ℝ) - 2) * d / 2)))
          (u := (d : ℝ) - 2 - σ) (Q := 2 * (d : ℝ) - 4 - 1) (p := (d : ℝ) - 2 - 2 * ε)
          (v := (d : ℝ) - ε) (m := (d : ℝ) - 2 - (σ + 2 * ε))
          (by positivity) (by positivity) (by positivity) (by positivity)
          (fun z => by rw [mul_assoc]; exact hF z) hPl.2 hΘ (hPl.1 s hs)
          (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith) (by rw [hn]; linarith)
          (by rw [hn, show (d : ℝ) + ε - d = ε by ring]; exact habs) z
        refine h.trans (le_of_eq ?_)
        rw [Real.rpow_add hw0]
        ring
      refine (ih (fun l' hl' => hPl' l' (List.mem_cons_of_mem l hl')) _
        (e + -(((l : ℝ) - 2) * d / 2)) (σ + 2 * ε) (by linarith) (by linarith) hstep z).trans
        (le_of_eq ?_)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      ring_nf
  have hbase : ∀ z, ‖ThetaInf s z‖ ≤ w ^ (0 : ℝ) *
      (w ^ (-(2 : ℝ)) * ((zdInf z : ℝ) + w) ^ (-((d : ℝ) - 2 - 2 * ε))) := by
    intro z; rw [Real.rpow_zero, one_mul]; exact hΘ z
  have h := key o hPo (ThetaInf s) 0 (2 * ε) (by positivity) (by rw [← hN]; linarith) hbase x
  rw [zero_add, sum_map_ord, show 2 * ε + 2 * ε * (o.length : ℝ) = τ' by rw [← hN]; linarith] at h
  unfold chainZ
  refine h.trans ?_
  have hx1 : (1 : ℝ) ≤ (zdInf x : ℝ) + w := by
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf x)]
  gcongr

section Witness

namespace G9

end G9

end Witness

end RBM8D
