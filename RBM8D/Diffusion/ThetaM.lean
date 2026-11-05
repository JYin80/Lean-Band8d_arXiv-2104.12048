import RBM8D.Diffusion.Defs
import RBM8D.SelfEnergy.Step
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The renormalized diffusive matrix `Θ^{(M)}`

[I, Theorem 1.5]: for the self-energies `Σ_l` of `SigmaOf`, the matrix
`1 − |m|² S (1 + Σ̃^{(M)})` is invertible, `Θ^{(M)}` of [I, (1.23)] satisfies
`|Θ^{(M)}_{xy}| ≤ L^τ B_{xy}` ([I, (1.24)]), the bounds [I, (1.26)–(1.27)] hold for `4 ≤ l ≤ M`,
and the change of order `M ≤ N` costs `L^τ W^{−(M+1)d/2}` entrywise for `Θ^{(·)}` and for
`(1 − X |m|² S)⁻¹` ([I, (1.29)]); this is `thetaMStmt`.

The proof follows [I, §8], (8.18)–(8.19), with maximal row sums and maximal entries only:
* `1 − |m|² S X = (1 − |m|² S)(1 − Θ Σ̃^{(M)})`, and the row sums of `Θ Σ_l` are small by
  [I, Lemma 6.2, (6.1)] (`thetaSigma`) and `Σ_y ⟨x − y⟩^{−d} ≤ (2 + 2 log L)^d`;
* `Θ^{(M)} = Θ + Θ Σ̃^{(M)} Θ^{(M)} = Θ + Θ^{(M)} Σ̃^{(M)} Θ`, so that `Θ^{(M)}` is the sum of the
  labelled `Θ` edges `Θ Σ_{o₁} Θ ⋯ Σ_{o_k} Θ` of length `k < K`, bounded by [I, Lemma 6.2, (6.2)]
  (`chain`), and a remainder of size `‖Θ Σ̃^{(M)}‖^K`;
* [I, (1.26)–(1.27)] are the bounds of the self-energies;
* `(1 − X |m|² S)⁻¹ = 1 + X Θ^{(M)}`, and the differences of order are fixed points of
  `V ↦ U + Θ Σ̃ V` or `V ↦ U + V Σ̃ Θ`.
-/

noncomputable section

open scoped BigOperators
open Matrix

set_option linter.unusedSectionVars false

namespace RBM8D

open Graphs

namespace ThetaM

/-! ## Row sums, maximal entries and fixed points -/

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If every row of `Y` has absolute sum at most `ρ < 1`, then `1 − Y` is invertible. -/
private theorem isUnit_one_sub {𝕜 : Type*} [NormedField 𝕜] (Y : Matrix ι ι 𝕜) (ρ : ℝ)
    (hY : ∀ x, ∑ y, ‖Y x y‖ ≤ ρ) (hρ : ρ < 1) : IsUnit (1 - Y) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have h0 : (1 - Y) *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  set w := u - v with hw
  have hfix : ∀ x, w x = ∑ y, Y x y * w y := by
    intro x
    have h1 := congrFun h0 x
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply,
      sub_eq_zero] at h1
    simpa [Matrix.mulVec, dotProduct] using h1
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact funext fun x => (IsEmpty.false x).elim
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max fun x => ‖w x‖
  have hle : ‖w x₀‖ ≤ ρ * ‖w x₀‖ := by
    calc ‖w x₀‖ = ‖∑ y, Y x₀ y * w y‖ := by rw [← hfix]
      _ ≤ ∑ y, ‖Y x₀ y‖ * ‖w x₀‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hx₀ y) (norm_nonneg _)
      _ = (∑ y, ‖Y x₀ y‖) * ‖w x₀‖ := by rw [Finset.sum_mul]
      _ ≤ ρ * ‖w x₀‖ := mul_le_mul_of_nonneg_right (hY x₀) (norm_nonneg _)
  have hz : ‖w x₀‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (w x₀)]) (norm_nonneg _)
  have hw0 : w = 0 := funext fun x => norm_le_zero_iff.1 ((hx₀ x).trans hz.le)
  exact sub_eq_zero.1 hw0

/-- `|(P Q)_{xy}| ≤ p q` when the rows of `P` have absolute sums at most `p` and the entries of
`Q` are at most `q`. -/
private theorem mul_le_row (P Q : Matrix ι ι ℂ) (p q : ℝ) (hP : ∀ x, ∑ w, ‖P x w‖ ≤ p)
    (hQ : ∀ w y, ‖Q w y‖ ≤ q) (x y : ι) : ‖(P * Q) x y‖ ≤ p * q := by
  have hq : 0 ≤ q := (norm_nonneg _).trans (hQ x y)
  rw [Matrix.mul_apply]
  calc ‖∑ w, P x w * Q w y‖ ≤ ∑ w, ‖P x w‖ * q := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hQ w y) (norm_nonneg _)
    _ = (∑ w, ‖P x w‖) * q := by rw [Finset.sum_mul]
    _ ≤ p * q := mul_le_mul_of_nonneg_right (hP x) hq

/-- `|(P Q)_{xy}| ≤ p q` when the entries of `P` are at most `p` and the columns of `Q` have
absolute sums at most `q`. -/
private theorem mul_le_col (P Q : Matrix ι ι ℂ) (p q : ℝ) (hP : ∀ x w, ‖P x w‖ ≤ p)
    (hQ : ∀ y, ∑ w, ‖Q w y‖ ≤ q) (x y : ι) : ‖(P * Q) x y‖ ≤ p * q := by
  have hp : 0 ≤ p := (norm_nonneg _).trans (hP x x)
  rw [Matrix.mul_apply]
  calc ‖∑ w, P x w * Q w y‖ ≤ ∑ w, p * ‖Q w y‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hP x w) (norm_nonneg _)
    _ = p * ∑ w, ‖Q w y‖ := by rw [Finset.mul_sum]
    _ ≤ p * q := mul_le_mul_of_nonneg_left (hQ y) hp

/-- A solution of `V = U + Y V` with row sums of `Y` at most `ρ ≤ 1/2` has entries at most twice
those of `U`. -/
private theorem fix_left (V U Y : Matrix ι ι ℂ) (ρ u : ℝ) (hV : V = U + Y * V)
    (hY : ∀ x, ∑ w, ‖Y x w‖ ≤ ρ) (hρ : ρ ≤ 1 / 2) (hU : ∀ x y, ‖U x y‖ ≤ u) :
    ∀ x y, ‖V x y‖ ≤ 2 * u := by
  intro x y
  have : Nonempty (ι × ι) := ⟨(x, y)⟩
  obtain ⟨p, hp⟩ := Finite.exists_max fun p : ι × ι => ‖V p.1 p.2‖
  have hρ0 : 0 ≤ ρ := (Finset.sum_nonneg fun w _ => norm_nonneg (Y x w)).trans (hY x)
  have h1 : ‖V p.1 p.2‖ ≤ u + ρ * ‖V p.1 p.2‖ := by
    have e : V p.1 p.2 = U p.1 p.2 + (Y * V) p.1 p.2 := by
      conv_lhs => rw [hV]
      rfl
    refine (congrArg norm e).le.trans ((norm_add_le _ _).trans (add_le_add (hU _ _) ?_))
    exact mul_le_row Y V ρ ‖V p.1 p.2‖ hY (fun w y => hp (w, y)) p.1 p.2
  have h2 : ‖V p.1 p.2‖ ≤ 2 * u := by nlinarith [norm_nonneg (V p.1 p.2)]
  exact (hp (x, y)).trans h2

/-- A solution of `V = U + V Z` with column sums of `Z` at most `ρ ≤ 1/2` has entries at most
twice those of `U`. -/
private theorem fix_right (V U Z : Matrix ι ι ℂ) (ρ u : ℝ) (hV : V = U + V * Z)
    (hZ : ∀ y, ∑ w, ‖Z w y‖ ≤ ρ) (hρ : ρ ≤ 1 / 2) (hU : ∀ x y, ‖U x y‖ ≤ u) :
    ∀ x y, ‖V x y‖ ≤ 2 * u := by
  have hT : Vᵀ = Uᵀ + Zᵀ * Vᵀ := by
    conv_lhs => rw [hV]
    rw [Matrix.transpose_add, Matrix.transpose_mul]
  intro x y
  exact fix_left Vᵀ Uᵀ Zᵀ ρ u hT (fun x => hZ x) hρ (fun x y => hU y x) y x

/-- The remainder of the Neumann expansion: if `V = T + Y V`, then
`V − Σ_{j<k} Y^j T = Y^k V` has entries at most `ρ^k μ`. -/
private theorem rem (V T Y : Matrix ι ι ℂ) (ρ μ : ℝ) (hV : V = T + Y * V)
    (hY : ∀ x, ∑ w, ‖Y x w‖ ≤ ρ) (hμ : ∀ x y, ‖V x y‖ ≤ μ) (k : ℕ) :
    ∀ x y, ‖(V - ∑ j ∈ Finset.range k, Y ^ j * T) x y‖ ≤ ρ ^ k * μ := by
  induction k with
  | zero => simpa using hμ
  | succ k ih =>
    have e : V - ∑ j ∈ Finset.range (k + 1), Y ^ j * T =
        Y * (V - ∑ j ∈ Finset.range k, Y ^ j * T) := by
      rw [Finset.sum_range_succ', pow_zero, one_mul, mul_sub, Finset.mul_sum]
      have : ∀ j ∈ Finset.range k, Y ^ (j + 1) * T = Y * (Y ^ j * T) := fun j _ => by
        rw [pow_succ', mul_assoc]
      rw [Finset.sum_congr rfl this]
      conv_lhs => rw [hV]
      abel
    intro x y
    rw [e, pow_succ', mul_assoc]
    exact mul_le_row Y _ ρ (ρ ^ k * μ) hY ih x y

/-- An entrywise bound for a finite sum `Σ_{l ∈ s} P_l` from bounds `e w_l g_{xy}` with
`w_l ≤ c`. -/
private theorem sum_le (P : ℕ → Matrix ι ι ℂ) (g : ι → ι → ℝ) (e c : ℝ) (wt : ℕ → ℝ)
    (s : Finset ℕ) (hP : ∀ l ∈ s, ∀ x y, ‖P l x y‖ ≤ e * wt l * g x y)
    (hw : ∀ l ∈ s, wt l ≤ c) (he : 0 ≤ e) (hg : ∀ x y, 0 ≤ g x y) :
    ∀ x y, ‖(∑ l ∈ s, P l) x y‖ ≤ s.card * (e * c) * g x y := by
  intro x y
  rw [Matrix.sum_apply]
  calc ‖∑ l ∈ s, P l x y‖ ≤ ∑ l ∈ s, e * c * g x y := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        refine (hP l hl x y).trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw l hl) he) (hg x y)
    _ = s.card * (e * c) * g x y := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The words of length `k` with letters in `[4, M]`. -/
private def words (M : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (words M k).flatMap fun o => (Finset.Icc 4 M).toList.map fun l => o ++ [l]

/-- The chain `Θ K_{o₁} Θ ⋯ K_{o_k} Θ`. -/
private def chainM (T : Matrix ι ι ℂ) (K : ℕ → Matrix ι ι ℂ) (o : List ℕ) : Matrix ι ι ℂ :=
  o.foldl (fun P l => P * K l * T) T

/-- A word of `words M k` has length `k` and letters in `[4, M]`. -/
private theorem words_mem {M k : ℕ} {o : List ℕ} (h : o ∈ words M k) :
    o.length = k ∧ ∀ l ∈ o, 4 ≤ l ∧ l ≤ M := by
  induction k generalizing o with
  | zero =>
    simp only [words, List.mem_singleton] at h
    subst h
    simp
  | succ k ih =>
    simp only [words, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_Icc] at h
    obtain ⟨o', ho', l, hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ho'
    refine ⟨by simp [h1], fun l' hl' => ?_⟩
    rcases List.mem_append.1 hl' with h | h
    · exact h2 l' h
    · rw [List.mem_singleton] at h
      subst h
      exact hl

/-- There are at most `(M + 1)^k` words of length `k`. -/
private theorem words_length (M k : ℕ) : (words M k).length ≤ (M + 1) ^ k := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    simp only [words, List.length_flatMap, List.length_map, Finset.length_toList, Nat.card_Icc,
      List.map_const', List.sum_replicate, smul_eq_mul]
    calc (words M k).length * (M + 1 - 4) ≤ (M + 1) ^ k * (M + 1) :=
          Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = (M + 1) ^ (k + 1) := (pow_succ _ _).symm

/-- The entries of a sum of matrices over a list are at most the sums of the entries. -/
private theorem norm_list_sum_le {α : Type*} (L : List α) (f : α → Matrix ι ι ℂ) (x y : ι) :
    ‖(L.map f).sum x y‖ ≤ (L.map fun a => ‖f a x y‖).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Appending a letter `l` multiplies the chain by `K_l Θ` on the right. -/
private theorem chain_snoc (T : Matrix ι ι ℂ) (K : ℕ → Matrix ι ι ℂ) (o : List ℕ) (l : ℕ) :
    chainM T K (o ++ [l]) = chainM T K o * K l * T := by
  simp [chainM, List.foldl_append]

/-- `(Θ Σ̃)^k Θ` is the sum of the chains over the words of length `k`. -/
private theorem pow_mul_eq (T : Matrix ι ι ℂ) (K : ℕ → Matrix ι ι ℂ) (M k : ℕ) :
    (T * ∑ l ∈ Finset.Icc 4 M, K l) ^ k * T = ((words M k).map (chainM T K)).sum := by
  set S := ∑ l ∈ Finset.Icc 4 M, K l
  have hstep : ∀ L : List (List ℕ),
      ((L.flatMap fun o => (Finset.Icc 4 M).toList.map fun l => o ++ [l]).map
        (chainM T K)).sum = (L.map (chainM T K)).sum * S * T := by
    intro L
    induction L with
    | nil => simp
    | cons o L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
        add_mul, add_mul]
      congr 1
      rw [List.map_map]
      have : ((Finset.Icc 4 M).toList.map (chainM T K ∘ fun l => o ++ [l])).sum =
          ∑ l ∈ Finset.Icc 4 M, chainM T K o * K l * T := by
        rw [← Finset.sum_map_toList]
        congr 1
        exact List.map_congr_left fun l _ => chain_snoc T K o l
      rw [this, ← Finset.sum_mul, ← Finset.mul_sum]
  induction k with
  | zero => simp [words, chainM]
  | succ k ih =>
    have e : (T * S) ^ (k + 1) * T = ((T * S) ^ k * T) * S * T := by
      rw [pow_succ]; simp only [mul_assoc]
    rw [e, ih]
    simp only [words]
    rw [hstep]

/-- The deterministic core of [I, (8.18)–(8.19)] for abstract matrices: `A = |m|² S` with row sums
`< 1`, `Θ` with `(1 − A)Θ = Θ(1 − A) = A`, kernels `K_l` whose products `Θ K_l` and `K_l Θ` are
bounded by `e w_l b`, chains bounded by `e ω^k B`, and the scalar conditions of the exponent
table. -/
private theorem core (A T : Matrix ι ι ℂ) (K : ℕ → Matrix ι ι ℂ) (M N Kw : ℕ) (hMN : M ≤ N)
    (hKw : 0 < Kw) (b B : ι → ι → ℝ) (wt : ℕ → ℝ) (a e R ω ω' Lτ : ℝ)
    (hA : ∀ x, ∑ y, ‖A x y‖ ≤ a) (ha : a < 1)
    (hAT : (1 - A) * T = A) (hTA : T * (1 - A) = A)
    (hTK : ∀ l, 4 ≤ l → l ≤ N → ∀ x y, ‖(T * K l) x y‖ ≤ e * wt l * b x y)
    (hKT : ∀ l, 4 ≤ l → l ≤ N → ∀ x y, ‖(K l * T) x y‖ ≤ e * wt l * b y x)
    (hwt : ∀ l, 4 ≤ l → wt l ≤ ω) (hwt' : ∀ l, M + 1 ≤ l → wt l ≤ ω')
    (hb0 : ∀ x y, 0 ≤ b x y) (hbω : ∀ x y, b x y ≤ ω)
    (hbr : ∀ x, ∑ y, b x y ≤ R) (hbc : ∀ y, ∑ x, b x y ≤ R)
    (hB0 : ∀ x y, 0 ≤ B x y) (hBω : ∀ x y, B x y ≤ ω)
    (hch : ∀ k < Kw, ∀ o ∈ words M k, ∀ x y, ‖chainM T K o x y‖ ≤ e * ω ^ k * B x y)
    (he : 1 ≤ e) (hR : 1 ≤ R) (hω0 : 0 ≤ ω) (hω'0 : 0 ≤ ω')
    (h1 : ((N : ℝ) + 1) * e * ω * R ≤ 1 / 2) (h2 : ((N : ℝ) + 1) * ω ≤ 1 / 2)
    (h3 : ∀ x y, (((N : ℝ) + 1) * e * ω * R) ^ Kw * (2 * (e * ω)) ≤ Lτ / 2 * B x y)
    (h4 : 4 * e ≤ Lτ) (h5 : 10 * ((N : ℝ) + 1) ^ 2 * e ^ 2 * R ≤ Lτ) :
    IsUnit (1 - A * (1 + ∑ l ∈ Finset.Icc 4 M, K l)) ∧
    (∀ x y, ‖(Ring.inverse (1 - A * (1 + ∑ l ∈ Finset.Icc 4 M, K l)) * A) x y‖ ≤ Lτ * B x y) ∧
    (∀ x y, ‖(Ring.inverse (1 - A * (1 + ∑ l ∈ Finset.Icc 4 N, K l)) * A -
        Ring.inverse (1 - A * (1 + ∑ l ∈ Finset.Icc 4 M, K l)) * A) x y‖ ≤ Lτ * (ω' * ω)) ∧
    (∀ x y, ‖(Ring.inverse (1 - (1 + ∑ l ∈ Finset.Icc 4 N, K l) * A) -
        Ring.inverse (1 - (1 + ∑ l ∈ Finset.Icc 4 M, K l) * A)) x y‖ ≤ Lτ * (ω' * ω)) := by
  set n : ℝ := (N : ℝ) + 1 with hn
  have hn1 : 1 ≤ n := by rw [hn]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have he0 : 0 ≤ e := by linarith
  set ρ : ℝ := n * e * ω * R with hρ
  set SM := ∑ l ∈ Finset.Icc 4 M, K l with hSM
  set SN := ∑ l ∈ Finset.Icc 4 N, K l with hSN
  set Δ := ∑ l ∈ Finset.Icc 4 N \ Finset.Icc 4 M, K l with hΔ
  have hsub : Finset.Icc 4 M ⊆ Finset.Icc 4 N := Finset.Icc_subset_Icc_right hMN
  have hSND : SN = Δ + SM := (Finset.sum_sdiff hsub).symm
  have hcardM : ((Finset.Icc 4 M).card : ℝ) ≤ n := by
    rw [hn, Nat.card_Icc]; exact_mod_cast (show M + 1 - 4 ≤ N + 1 by omega)
  have hcardN : ((Finset.Icc 4 N).card : ℝ) ≤ n := by
    rw [hn, Nat.card_Icc]; exact_mod_cast (show N + 1 - 4 ≤ N + 1 by omega)
  have hcardD : ((Finset.Icc 4 N \ Finset.Icc 4 M).card : ℝ) ≤ n :=
    (Nat.cast_le.2 (Finset.card_le_card Finset.sdiff_subset)).trans hcardN
  have memM : ∀ l ∈ Finset.Icc 4 M, 4 ≤ l ∧ l ≤ N := fun l hl => by
    rw [Finset.mem_Icc] at hl; omega
  have memN : ∀ l ∈ Finset.Icc 4 N, 4 ≤ l ∧ l ≤ N := fun l hl => by
    rw [Finset.mem_Icc] at hl; omega
  have memD : ∀ l ∈ Finset.Icc 4 N \ Finset.Icc 4 M, 4 ≤ l ∧ l ≤ N ∧ M + 1 ≤ l := fun l hl => by
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hl; omega
  -- entry bounds of `Θ Σ`, `Σ Θ` over a set of letters
  have bTK : ∀ (s : Finset ℕ) (c : ℝ), 0 ≤ c → (s.card : ℝ) ≤ n → (∀ l ∈ s, 4 ≤ l ∧ l ≤ N) →
      (∀ l ∈ s, wt l ≤ c) → ∀ x y, ‖(T * ∑ l ∈ s, K l) x y‖ ≤ n * e * c * b x y := by
    intro s c hc hs hmem hw x y
    rw [Finset.mul_sum]
    refine (sum_le (fun l => T * K l) b e c wt s (fun l hl => hTK l (hmem l hl).1 (hmem l hl).2)
      hw he0 hb0 x y).trans ?_
    have := mul_le_mul_of_nonneg_right hs (mul_nonneg (mul_nonneg he0 hc) (hb0 x y))
    linarith
  have bKT : ∀ (s : Finset ℕ) (c : ℝ), 0 ≤ c → (s.card : ℝ) ≤ n → (∀ l ∈ s, 4 ≤ l ∧ l ≤ N) →
      (∀ l ∈ s, wt l ≤ c) → ∀ x y, ‖((∑ l ∈ s, K l) * T) x y‖ ≤ n * e * c * b y x := by
    intro s c hc hs hmem hw x y
    rw [Finset.sum_mul]
    refine (sum_le (fun l => K l * T) (fun x y => b y x) e c wt s
      (fun l hl => hKT l (hmem l hl).1 (hmem l hl).2) hw he0 (fun x y => hb0 y x) x y).trans ?_
    have := mul_le_mul_of_nonneg_right hs (mul_nonneg (mul_nonneg he0 hc) (hb0 y x))
    linarith
  have rowsum : ∀ (P : Matrix ι ι ℂ) (c : ℝ), 0 ≤ c → (∀ x y, ‖P x y‖ ≤ c * b x y) →
      ∀ x, ∑ y, ‖P x y‖ ≤ c * R := by
    intro P c hc hP x
    calc ∑ y, ‖P x y‖ ≤ ∑ y, c * b x y := Finset.sum_le_sum fun y _ => hP x y
      _ = c * ∑ y, b x y := by rw [Finset.mul_sum]
      _ ≤ c * R := mul_le_mul_of_nonneg_left (hbr x) hc
  have rowsumT : ∀ (P : Matrix ι ι ℂ) (c : ℝ), 0 ≤ c → (∀ x y, ‖P x y‖ ≤ c * b y x) →
      ∀ x, ∑ y, ‖P x y‖ ≤ c * R := by
    intro P c hc hP x
    calc ∑ y, ‖P x y‖ ≤ ∑ y, c * b y x := Finset.sum_le_sum fun y _ => hP x y
      _ = c * ∑ y, b y x := by rw [Finset.mul_sum]
      _ ≤ c * R := mul_le_mul_of_nonneg_left (hbc x) hc
  have colsumT : ∀ (P : Matrix ι ι ℂ) (c : ℝ), 0 ≤ c → (∀ x y, ‖P x y‖ ≤ c * b y x) →
      ∀ y, ∑ x, ‖P x y‖ ≤ c * R := by
    intro P c hc hP y
    calc ∑ x, ‖P x y‖ ≤ ∑ x, c * b y x := Finset.sum_le_sum fun x _ => hP x y
      _ = c * ∑ x, b y x := by rw [Finset.mul_sum]
      _ ≤ c * R := mul_le_mul_of_nonneg_left (hbr y) hc
  have hneω : 0 ≤ n * e * ω := by positivity
  have hneω' : 0 ≤ n * e * ω' := by positivity
  -- `Θ Σ̃^{(M)}`, `Θ Σ̃^{(N)}`, `Σ̃^{(M)} Θ`, `Σ̃^{(N)} Θ`, `Θ Δ`, `Δ Θ`
  have eYM : ∀ x y, ‖(T * SM) x y‖ ≤ n * e * ω * b x y :=
    bTK _ ω hω0 hcardM memM fun l hl => hwt l (memM l hl).1
  have eYN : ∀ x y, ‖(T * SN) x y‖ ≤ n * e * ω * b x y :=
    bTK _ ω hω0 hcardN memN fun l hl => hwt l (memN l hl).1
  have eZM : ∀ x y, ‖(SM * T) x y‖ ≤ n * e * ω * b y x :=
    bKT _ ω hω0 hcardM memM fun l hl => hwt l (memM l hl).1
  have eZN : ∀ x y, ‖(SN * T) x y‖ ≤ n * e * ω * b y x :=
    bKT _ ω hω0 hcardN memN fun l hl => hwt l (memN l hl).1
  have eTD : ∀ x y, ‖(T * Δ) x y‖ ≤ n * e * ω' * b x y :=
    bTK _ ω' hω'0 hcardD (fun l hl => ⟨(memD l hl).1, (memD l hl).2.1⟩)
      fun l hl => hwt' l (memD l hl).2.2
  have eDT : ∀ x y, ‖(Δ * T) x y‖ ≤ n * e * ω' * b y x :=
    bKT _ ω' hω'0 hcardD (fun l hl => ⟨(memD l hl).1, (memD l hl).2.1⟩)
      fun l hl => hwt' l (memD l hl).2.2
  have rYM : ∀ x, ∑ y, ‖(T * SM) x y‖ ≤ ρ := rowsum _ _ hneω eYM
  have rYN : ∀ x, ∑ y, ‖(T * SN) x y‖ ≤ ρ := rowsum _ _ hneω eYN
  have rZM : ∀ x, ∑ y, ‖(SM * T) x y‖ ≤ ρ := rowsumT _ _ hneω eZM
  have cZN : ∀ y, ∑ x, ‖(SN * T) x y‖ ≤ ρ := colsumT _ _ hneω eZN
  have rTD : ∀ x, ∑ y, ‖(T * Δ) x y‖ ≤ n * e * ω' * R := rowsum _ _ hneω' eTD
  have cDT : ∀ y, ∑ x, ‖(Δ * T) x y‖ ≤ n * e * ω' * R := colsumT _ _ hneω' eDT
  have entry : ∀ (P : Matrix ι ι ℂ) (c : ℝ), 0 ≤ c → (∀ x y, ‖P x y‖ ≤ c * b x y) →
      ∀ x y, ‖P x y‖ ≤ c * ω := fun P c hc hP x y =>
    (hP x y).trans (mul_le_mul_of_nonneg_left (hbω x y) hc)
  have entryT : ∀ (P : Matrix ι ι ℂ) (c : ℝ), 0 ≤ c → (∀ x y, ‖P x y‖ ≤ c * b y x) →
      ∀ x y, ‖P x y‖ ≤ c * ω := fun P c hc hP x y =>
    (hP x y).trans (mul_le_mul_of_nonneg_left (hbω y x) hc)
  -- invertibility
  have hUA : IsUnit (1 - A) := isUnit_one_sub A a hA ha
  have hfac : ∀ S : Matrix ι ι ℂ, 1 - A * (1 + S) = (1 - A) * (1 - T * S) := by
    intro S
    rw [mul_sub, mul_one, ← mul_assoc, hAT]
    noncomm_ring
  have hρ1 : ρ < 1 := by linarith
  have hUM : IsUnit (1 - A * (1 + SM)) := by
    rw [hfac]; exact hUA.mul (isUnit_one_sub _ ρ rYM hρ1)
  have hUN : IsUnit (1 - A * (1 + SN)) := by
    rw [hfac]; exact hUA.mul (isUnit_one_sub _ ρ rYN hρ1)
  -- the two fixed-point equations
  have fpL : ∀ S : Matrix ι ι ℂ, IsUnit (1 - A * (1 + S)) →
      Ring.inverse (1 - A * (1 + S)) * A = T + T * S * (Ring.inverse (1 - A * (1 + S)) * A) := by
    intro S hU
    have e1 : (1 - A * (1 + S)) * (Ring.inverse (1 - A * (1 + S)) * A) = A := by
      rw [← mul_assoc, Ring.mul_inverse_cancel _ hU, one_mul]
    generalize Ring.inverse (1 - A * (1 + S)) * A = V at e1 ⊢
    refine hUA.mul_left_cancel ?_
    have e2 : (1 - A) * (T + T * S * V) = A + A * S * V := by
      calc (1 - A) * (T + T * S * V) = (1 - A) * T + ((1 - A) * T) * S * V := by noncomm_ring
        _ = A + A * S * V := by rw [hAT]
    rw [e2]
    have e3 : (1 - A) * V = (1 - A * (1 + S)) * V + A * S * V := by noncomm_ring
    rw [e3, e1]
  have fpR : ∀ S : Matrix ι ι ℂ, IsUnit (1 - A * (1 + S)) →
      Ring.inverse (1 - A * (1 + S)) * A = T + Ring.inverse (1 - A * (1 + S)) * A * (S * T) := by
    intro S hU
    have e1 : Ring.inverse (1 - A * (1 + S)) * A * (1 - (1 + S) * A) = A := by
      have : A * (1 - (1 + S) * A) = (1 - A * (1 + S)) * A := by noncomm_ring
      rw [mul_assoc, this, ← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]
    generalize Ring.inverse (1 - A * (1 + S)) * A = V at e1 ⊢
    refine hUA.mul_right_cancel ?_
    have e2 : (T + V * (S * T)) * (1 - A) = A + V * S * A := by
      calc (T + V * (S * T)) * (1 - A) = T * (1 - A) + V * S * (T * (1 - A)) := by noncomm_ring
        _ = A + V * S * A := by rw [hTA]
    rw [e2]
    have e3 : V * (1 - A) = V * (1 - (1 + S) * A) + V * S * A := by noncomm_ring
    rw [e3, e1]
  have hRes : ∀ S : Matrix ι ι ℂ, IsUnit (1 - A * (1 + S)) →
      Ring.inverse (1 - (1 + S) * A) = 1 + (1 + S) * (Ring.inverse (1 - A * (1 + S)) * A) := by
    intro S hU
    rw [G16.inverse_one_sub_mul A (1 + S) hU, mul_assoc]
  have lM := fpL SM hUM
  have lN := fpL SN hUN
  have rM := fpR SM hUM
  have rN := fpR SN hUN
  rw [hRes SN hUN, hRes SM hUM]
  generalize Ring.inverse (1 - A * (1 + SM)) * A = VM at lM rM ⊢
  generalize Ring.inverse (1 - A * (1 + SN)) * A = VN at lN rN ⊢
  clear_value SM SN Δ
  -- maximal entries of `Θ` and `Θ^{(M)}`
  have hT : ∀ x y, ‖T x y‖ ≤ e * ω := by
    intro x y
    have := hch 0 hKw [] (by simp [words]) x y
    simp only [chainM, List.foldl_nil, pow_zero, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hBω x y) he0)
  have hρh : ρ ≤ 1 / 2 := h1
  have μM : ∀ x y, ‖VM x y‖ ≤ 2 * (e * ω) := fix_left VM T (T * SM) ρ (e * ω) lM rYM hρh hT
  have μN : ∀ x y, ‖VN x y‖ ≤ 2 * (e * ω) := fix_left VN T (T * SN) ρ (e * ω) lN rYN hρh hT
  -- `Θ^{(N)} − Θ^{(M)}`
  have hD : VN - VM = T * Δ * VM + T * SN * (VN - VM) := by
    calc VN - VM = (T + T * SN * VN) - (T + T * SM * VM) := by rw [← lN, ← lM]
      _ = _ := by rw [hSND]; noncomm_ring
  have hDb := fix_left (VN - VM) (T * Δ * VM) (T * SN) ρ _ hD rYN hρh (mul_le_row _ _ _ _ rTD μM)
  have hne1 : 1 ≤ n * e := one_le_mul_of_one_le_of_one_le hn1 he
  have hQ : n * e ≤ n ^ 2 * e ^ 2 * R := by
    have h1' : n * e ≤ (n * e) ^ 2 := by nlinarith
    have h2' : (n * e) ^ 2 ≤ (n * e) ^ 2 * R := le_mul_of_one_le_right (sq_nonneg _) hR
    have h3' : (n * e) ^ 2 * R = n ^ 2 * e ^ 2 * R := by ring
    linarith
  have hQ' : n * e ^ 2 * R ≤ n ^ 2 * e ^ 2 * R := by
    have hnn : n ≤ n ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hnn (show 0 ≤ e ^ 2 * R by positivity)
    linarith
  have hQ0 : 0 ≤ n ^ 2 * e ^ 2 * R := by positivity
  have hωω : 0 ≤ ω' * ω := mul_nonneg hω'0 hω0
  refine ⟨hUM, ?_, ?_, ?_⟩
  · -- (1.24)
    intro x y
    have hrem := rem VM T (T * SM) ρ (2 * (e * ω)) lM rYM μM Kw x y
    have hmain : ‖(∑ j ∈ Finset.range Kw, (T * SM) ^ j * T) x y‖ ≤ 2 * e * B x y := by
      rw [Matrix.sum_apply]
      have hnω : ((M : ℝ) + 1) * ω ≤ 1 / 2 := by
        have : (M : ℝ) + 1 ≤ n := by rw [hn]; exact_mod_cast Nat.succ_le_succ hMN
        nlinarith
      calc ‖∑ j ∈ Finset.range Kw, ((T * SM) ^ j * T) x y‖
          ≤ ∑ j ∈ Finset.range Kw, e * B x y * (1 / 2) ^ j := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
            have hj' := Finset.mem_range.1 hj
            rw [hSM, pow_mul_eq]
            refine (norm_list_sum_le _ _ x y).trans ?_
            refine (List.sum_le_length_nsmul _ (e * ω ^ j * B x y) fun r hr => ?_).trans ?_
            · simp only [List.mem_map] at hr
              obtain ⟨o, ho, rfl⟩ := hr
              exact hch j hj' o ho x y
            · rw [List.length_map, nsmul_eq_mul]
              have hl := words_length M j
              have hl' : ((words M j).length : ℝ) ≤ ((M : ℝ) + 1) ^ j := by exact_mod_cast hl
              have hpow : ((M : ℝ) + 1) ^ j * ω ^ j ≤ (1 / 2) ^ j := by
                rw [← mul_pow]
                exact pow_le_pow_left₀ (by positivity) hnω j
              calc ((words M j).length : ℝ) * (e * ω ^ j * B x y)
                  ≤ ((M : ℝ) + 1) ^ j * (e * ω ^ j * B x y) :=
                    mul_le_mul_of_nonneg_right hl' (by have := hB0 x y; positivity)
                _ = e * B x y * (((M : ℝ) + 1) ^ j * ω ^ j) := by ring
                _ ≤ e * B x y * (1 / 2) ^ j :=
                    mul_le_mul_of_nonneg_left hpow (mul_nonneg he0 (hB0 x y))
        _ = e * B x y * ∑ j ∈ Finset.range Kw, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
        _ ≤ e * B x y * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le Kw) (mul_nonneg he0 (hB0 x y))
        _ = 2 * e * B x y := by ring
    have hsplit : VM x y = (∑ j ∈ Finset.range Kw, (T * SM) ^ j * T) x y +
        (VM - ∑ j ∈ Finset.range Kw, (T * SM) ^ j * T) x y := by
      rw [Matrix.sub_apply]; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h3' := h3 x y
    have h4' : 2 * e * B x y ≤ Lτ / 2 * B x y := by
      have := mul_le_mul_of_nonneg_right h4 (hB0 x y)
      linarith
    linarith
  · -- the change of order of `Θ^{(·)}`
    intro x y
    refine (hDb x y).trans ?_
    have hk : 4 * (n * e ^ 2 * R) ≤ Lτ := by linarith
    have c1 : 2 * (n * e * ω' * R * (2 * (e * ω))) = 4 * (n * e ^ 2 * R) * (ω' * ω) := by ring
    rw [c1]
    exact mul_le_mul_of_nonneg_right hk hωω
  · -- the change of order of `(1 − X |m|² S)⁻¹`
    have hdec : (1 + (1 + SN) * VN) - (1 + (1 + SM) * VM) =
        (VN - VM) + Δ * VN + SM * (VN - VM) := by
      rw [hSND]; noncomm_ring
    rw [hdec]
    -- `Δ Θ^{(N)}`
    have hE : Δ * VN = Δ * T + Δ * VN * (SN * T) := by
      conv_lhs => rw [rN]
      noncomm_ring
    have hEb := fix_right (Δ * VN) (Δ * T) (SN * T) ρ _ hE cZN hρh (entryT _ _ hneω' eDT)
    -- `Σ̃^{(M)} Θ^{(M)}`
    have hG : SM * VM = SM * T + SM * T * (SM * VM) := by
      conv_lhs => rw [lM]
      noncomm_ring
    have hGb := fix_left (SM * VM) (SM * T) (SM * T) ρ _ hG rZM hρh (entryT _ _ hneω eZM)
    -- `Σ̃^{(M)} (Θ^{(N)} − Θ^{(M)})`
    have hF : SM * (VN - VM) = SM * VM * (Δ * T) + SM * (VN - VM) * (SN * T) := by
      have : VN - VM = VM * (Δ * T) + (VN - VM) * (SN * T) := by
        calc VN - VM = (T + VN * (SN * T)) - (T + VM * (SM * T)) := by rw [← rN, ← rM]
          _ = _ := by rw [hSND]; noncomm_ring
      conv_lhs => rw [this]
      noncomm_ring
    have hFb := fix_right (SM * (VN - VM)) (SM * VM * (Δ * T)) (SN * T) ρ _ hF cZN hρh
      (mul_le_col _ _ _ _ hGb cDT)
    intro x y
    rw [Matrix.add_apply, Matrix.add_apply]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    have b1 := hDb x y
    have b2 := hEb x y
    have b3 := hFb x y
    have hω1 : ω ≤ 1 := by
      have := le_mul_of_one_le_left hω0 hn1
      linarith
    have c1 : 2 * (n * e * ω' * R * (2 * (e * ω))) = 4 * (n * e ^ 2 * R) * (ω' * ω) := by ring
    have c2 : 2 * (n * e * ω' * ω) = 2 * (n * e) * (ω' * ω) := by ring
    have c3 : 2 * (2 * (n * e * ω * ω) * (n * e * ω' * R)) =
        4 * (n ^ 2 * e ^ 2 * R) * (ω' * ω) * ω := by ring
    rw [c1] at b1
    rw [c2] at b2
    rw [c3] at b3
    have b3' : 4 * (n ^ 2 * e ^ 2 * R) * (ω' * ω) * ω ≤ 4 * (n ^ 2 * e ^ 2 * R) * (ω' * ω) :=
      mul_le_of_le_one_right (by positivity) hω1
    have key : 4 * (n * e ^ 2 * R) + 2 * (n * e) + 4 * (n ^ 2 * e ^ 2 * R) ≤ Lτ := by linarith
    have key' := mul_le_mul_of_nonneg_right key hωω
    linarith

end Core

/-! ## The propagator `Θ`, the bracket `⟨x − y⟩` and the bound `B` -/

section Model

/-- The complexification is multiplicative. -/
private theorem cmat_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℝ) :
    cmat (P * Q) = cmat P * cmat Q := by
  ext i j
  simp [cmat, Matrix.mul_apply]

/-- The complexification is additive. -/
private theorem cmat_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℝ) :
    cmat (P - Q) = cmat P - cmat Q := by
  ext i j
  simp [cmat]

/-- The complexification of `1` is `1`. -/
private theorem cmat_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    cmat (1 : Matrix ι ι ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [cmat, Matrix.one_apply, h]

/-- For `S ≥ 0` with row sums `1` and `Im z > 0`: the rows of `A = |m|² S` have absolute sums
`|m|² < 1`, and `(1 − A)Θ = Θ(1 − A) = A` for `Θ = |m|² S (1 − |m|² S)⁻¹` ([I, (1.16)]). -/
private theorem theta_rel {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) :
    (∀ x, ∑ y, ‖amat S z x y‖ ≤ ‖msc z‖ ^ 2) ∧ ‖msc z‖ ^ 2 < 1 ∧
    (1 - amat S z) * cmat (Theta (msc z) S) = amat S z ∧
    cmat (Theta (msc z) S) * (1 - amat S z) = amat S z := by
  have hm : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hm2 : ‖msc z‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hm two_ne_zero
  set Ar : Matrix ι ι ℝ := ‖msc z‖ ^ 2 • S with hAr
  have hrow : ∀ x, ∑ y, ‖Ar x y‖ = ‖msc z‖ ^ 2 := by
    intro x
    simp only [hAr, Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      abs_pow, abs_norm]
    rw [← Finset.mul_sum]
    simp [abs_of_nonneg (hS0 x _), hS1 x]
  have hA : amat S z = cmat Ar := by
    ext i j
    simp [amat, mAbs2, cmat, hAr]
  have hU : IsUnit (1 - Ar) := isUnit_one_sub Ar _ (fun x => (hrow x).le) hm2
  have hTh : Theta (msc z) S = Ar * Ring.inverse (1 - Ar) := rfl
  have r1 : (1 - Ar) * (Ar * Ring.inverse (1 - Ar)) = Ar := by
    have : (1 - Ar) * Ar = Ar * (1 - Ar) := by noncomm_ring
    rw [← mul_assoc, this, mul_assoc, Ring.mul_inverse_cancel _ hU, mul_one]
  have r2 : Ar * Ring.inverse (1 - Ar) * (1 - Ar) = Ar := by
    rw [mul_assoc, Ring.inverse_mul_cancel _ hU, mul_one]
  refine ⟨fun x => ?_, hm2, ?_, ?_⟩
  · rw [hA]
    simp only [cmat, Matrix.map_apply, Complex.norm_real]
    exact (hrow x).le
  · rw [hA, hTh, ← cmat_one, ← cmat_sub, ← cmat_mul, r1]
  · rw [hA, hTh, ← cmat_one, ← cmat_sub, ← cmat_mul, r2]

/-- `Σ_t f(t) ≤ Σ_{k < L} f(k)` over `t ∈ ℤ/Lℤ` read through its representative, for `f ≥ 0`. -/
private theorem sum_val_le (L : ℕ) [NeZero L] (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ t : ZMod L, f t.val ≤ ∑ k ∈ Finset.range L, f k := by
  rw [← Finset.sum_image (f := f) (g := ZMod.val) fun a _ b _ h => ZMod.val_injective L h]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hf k
  intro k hk
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hk
  exact Finset.mem_range.2 (ZMod.val_lt t)

/-- `Σ_{t ∈ ℤ/Lℤ} (‖t‖_L + W)^{−1} ≤ 2 + 2 log L` for `W ≥ 1`. -/
private theorem sum_zdist_inv (L W : ℕ) [NeZero L] (hW : 1 ≤ W) :
    ∑ t : ZMod L, ((zdist L t : ℝ) + W)⁻¹ ≤ 2 + 2 * Real.log L := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hpt : ∀ t : ZMod L, ((zdist L t : ℝ) + W)⁻¹ ≤
      ((t.val : ℝ) + 1)⁻¹ + (((L - t.val : ℕ) : ℝ))⁻¹ := by
    intro t
    have hlt := ZMod.val_lt t
    have hpos : (0 : ℝ) < ((L - t.val : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    unfold zdist
    rcases le_total t.val (L - t.val) with h | h
    · rw [min_eq_left h]
      have : ((t.val : ℝ) + W)⁻¹ ≤ ((t.val : ℝ) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by linarith)
      have : (0 : ℝ) ≤ (((L - t.val : ℕ) : ℝ))⁻¹ := inv_nonneg.2 hpos.le
      linarith
    · rw [min_eq_right h]
      have : (((L - t.val : ℕ) : ℝ) + W)⁻¹ ≤ (((L - t.val : ℕ) : ℝ))⁻¹ :=
        inv_anti₀ hpos (by linarith)
      have : (0 : ℝ) ≤ ((t.val : ℝ) + 1)⁻¹ := inv_nonneg.2 (by positivity)
      linarith
  have hH : ∑ k ∈ Finset.range L, ((k : ℝ) + 1)⁻¹ ≤ 1 + Real.log L := by
    have h := harmonic_le_one_add_log L
    have e : ((harmonic L : ℚ) : ℝ) = ∑ k ∈ Finset.range L, ((k : ℝ) + 1)⁻¹ := by
      simp [harmonic]
    rw [e] at h
    exact h
  have h1 : ∑ t : ZMod L, ((t.val : ℝ) + 1)⁻¹ ≤ 1 + Real.log L :=
    (sum_val_le L (fun k => ((k : ℝ) + 1)⁻¹) fun k => by positivity).trans hH
  have h2 : ∑ t : ZMod L, (((L - t.val : ℕ) : ℝ))⁻¹ ≤ 1 + Real.log L := by
    refine (sum_val_le L (fun k => (((L - k : ℕ) : ℝ))⁻¹) fun k => by positivity).trans ?_
    rw [← Finset.sum_range_reflect]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun k hk => ?_) hH
    have hk' := Finset.mem_range.1 hk
    congr 1
    rw [show L - (L - 1 - k) = k + 1 by omega]
    push_cast
    ring
  calc ∑ t : ZMod L, ((zdist L t : ℝ) + W)⁻¹
      ≤ ∑ t : ZMod L, (((t.val : ℝ) + 1)⁻¹ + (((L - t.val : ℕ) : ℝ))⁻¹) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ = ∑ t : ZMod L, ((t.val : ℝ) + 1)⁻¹ + ∑ t : ZMod L, (((L - t.val : ℕ) : ℝ))⁻¹ :=
        Finset.sum_add_distrib
    _ ≤ 2 + 2 * Real.log L := by linarith

/-- `Σ_y ⟨x − y⟩^{−d} ≤ (2 + 2 log L)^d` for `W ≥ 1`. -/
private theorem brk_sum (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (x : Zd d L) :
    ∑ y, brk d L W x y ^ (-(d : ℝ)) ≤ (2 + 2 * Real.log L) ^ d := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set h : ZMod L → ℝ := fun t => ((zdist L t : ℝ) + W)⁻¹ with hh
  have hpt : ∀ y, brk d L W x y ^ (-(d : ℝ)) ≤ ∏ i, h ((x - y) i) := by
    intro y
    have hb0 : 0 < brk d L W x y := by unfold brk; positivity
    rw [Real.rpow_neg hb0.le, Real.rpow_natCast]
    simp only [hh]
    rw [Finset.prod_inv_distrib]
    refine inv_anti₀ (Finset.prod_pos fun i _ => by positivity) ?_
    calc ∏ i, ((zdist L ((x - y) i) : ℝ) + W) ≤ ∏ _i : Fin d, brk d L W x y := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          unfold brk
          have := zdist_le_zdistInf d L (x - y) i
          have : (zdist L ((x - y) i) : ℝ) ≤ zdistInf d L (x - y) := by exact_mod_cast this
          linarith
      _ = brk d L W x y ^ d := by simp
  calc ∑ y, brk d L W x y ^ (-(d : ℝ)) ≤ ∑ y, ∏ i, h ((x - y) i) :=
        Finset.sum_le_sum fun y _ => hpt y
    _ = ∑ u : Zd d L, ∏ i, h (u i) :=
        Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => rfl
    _ = ∏ _i : Fin d, ∑ t : ZMod L, h t := by
        rw [← Finset.sum_prod_piFinset (Finset.univ : Finset (ZMod L)) fun _ t => h t,
          Fintype.piFinset_univ]
    _ = (∑ t : ZMod L, h t) ^ d := by simp
    _ ≤ (2 + 2 * Real.log L) ^ d :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun t _ => by positivity) (sum_zdist_inv L W hW) d

/-- `⟨x − y⟩ = ⟨y − x⟩`. -/
private theorem brk_comm (d L W : ℕ) [NeZero L] (x y : Zd d L) :
    brk d L W x y = brk d L W y x := by
  unfold brk
  rw [← zdistInf_neg d L (x - y), neg_sub]

/-- `B_{xy} ≥ 0`. -/
private theorem bB_nonneg (d L W : ℕ) [NeZero L] (x y : Zd d L) : 0 ≤ bB d L W x y := by
  unfold bB; positivity

/-- `B_{xy} ≤ W^{−d}`. -/
private theorem bB_le (d L W : ℕ) [NeZero L] (hd : 2 ≤ d) (hW : (1 : ℝ) ≤ W) (x y : Zd d L) :
    bB d L W x y ≤ (W : ℝ) ^ (-(d : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold bB
  have hz0 : (0 : ℝ) ≤ zdistInf d L (x - y) := Nat.cast_nonneg _
  have h1 : ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) ≤ (W : ℝ) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hW0 (by linarith) (by linarith)
  calc (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))
      ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (2 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (W : ℝ) ^ (-(d : ℝ)) := by rw [← Real.rpow_add hW0]; ring_nf

/-- `B_{xy} ≥ (2L)^{−d}` for `1 ≤ W ≤ L`. -/
private theorem bB_ge (d L W : ℕ) [NeZero L] (hd : 2 ≤ d) (hW : (1 : ℝ) ≤ W) (hWL : (W : ℝ) ≤ L)
    (x y : Zd d L) : (2 * (L : ℝ)) ^ (-(d : ℝ)) ≤ bB d L W x y := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hz : (zdistInf d L (x - y) : ℝ) ≤ L := by
    have := zdistInf_le_half d L (x - y)
    have : zdistInf d L (x - y) ≤ L := this.trans (Nat.div_le_self _ _)
    exact_mod_cast this
  have hb0 : (0 : ℝ) < (zdistInf d L (x - y) : ℝ) + W := by positivity
  unfold bB
  have h1 : (2 * (L : ℝ)) ^ (2 - (d : ℝ)) ≤ ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb0 (by linarith) (by linarith)
  have h2 : (2 * (L : ℝ)) ^ (-2 : ℝ) ≤ (W : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hW0 (by linarith) (by norm_num)
  calc (2 * (L : ℝ)) ^ (-(d : ℝ)) = (2 * (L : ℝ)) ^ (-2 : ℝ) * (2 * (L : ℝ)) ^ (2 - (d : ℝ)) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
    _ ≤ _ := mul_le_mul h2 h1 (by positivity) (by positivity)

/-- A word with letters `≥ 4` has sum at least four times its length. -/
private theorem four_mul_length_le (o : List ℕ) (h : ∀ l ∈ o, 4 ≤ l) : 4 * o.length ≤ o.sum := by
  induction o with
  | nil => simp
  | cons a o ih =>
    simp only [List.length_cons, List.sum_cons]
    have := h a List.mem_cons_self
    have := ih fun l hl => h l (List.mem_cons_of_mem _ hl)
    omega

/-- The scaling factor of a labelled `Θ` edge with labels `≥ 4` is at most `(W^{−d})^k`, `k` the
length of the label. -/
private theorem chain_exp_le (d : ℕ) (w : ℝ) (hw : 1 ≤ w) (o : List ℕ) (h : ∀ l ∈ o, 4 ≤ l) :
    w ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) ≤ (w ^ (-(d : ℝ))) ^ o.length := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hw ?_
  have hs : (4 : ℝ) * o.length ≤ o.sum := by exact_mod_cast four_mul_length_le o h
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e : (((Kind.theta o).ord : ℤ) : ℝ) = (o.sum : ℝ) + 2 - 2 * o.length := by
    simp only [Kind.ord, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat]
  rw [e]
  nlinarith

/-- A uniform choice of thresholds: if `F i` works for each `i ∈ s`, then `Σ_{i ∈ s} |F i|` works
for all of them. -/
private theorem le_sum_abs {α : Type*} (s : Finset α) (F : α → ℝ) {i : α} (hi : i ∈ s) :
    F i ≤ ∑ j ∈ s, |F j| :=
  (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (F j)) hi)

/-! ## The exponent table -/

/-- The scalar conditions of the exponent table at `w = W`, `ℓ = L` with `1 ≤ ℓ`, `w ≤ ℓ`,
`ℓ^c ≤ w`, for `w` above an explicit threshold, with `e = W^σ`, `ω = W^{−d}`,
`R = (2 + 2 log L)^d` and `n = N + 1`: `n e ω R ≤ 1/2`, `n ω ≤ 1/2`, the remainder
`(n e ω R)^K · 2 e ω ≤ L^τ (2L)^{−d} / 2` for `K ≥ d/c + 1`, `4 e ≤ L^τ` and
`10 n² e² R ≤ L^τ`. -/
private theorem scalars (d N Kw : ℕ) (hd : 8 ≤ d) (c σ τ w ℓ : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 4) (hστ : 4 * σ ≤ τ) (hKw : (d : ℝ) / c + 1 ≤ Kw) (hℓ : 1 ≤ ℓ)
    (hwℓ : w ≤ ℓ) (hℓw : ℓ ^ c ≤ w)
    (hw : max (2 ^ (d + 2)) (max (2 * ((N : ℝ) + 1)) (max (((N : ℝ) + 1) *
      (2 + 2 / (c * σ / d)) ^ d) ((10 * ((N : ℝ) + 1) ^ 2 * (2 + 2 / (c * σ / d)) ^ d) ^ σ⁻¹)))
        ≤ w) :
    ((N : ℝ) + 1) * w ^ σ * w ^ (-(d : ℝ)) * (2 + 2 * Real.log ℓ) ^ d ≤ 1 / 2 ∧
    ((N : ℝ) + 1) * w ^ (-(d : ℝ)) ≤ 1 / 2 ∧
    (∀ β : ℝ, (2 * ℓ) ^ (-(d : ℝ)) ≤ β →
      (((N : ℝ) + 1) * w ^ σ * w ^ (-(d : ℝ)) * (2 + 2 * Real.log ℓ) ^ d) ^ Kw *
        (2 * (w ^ σ * w ^ (-(d : ℝ)))) ≤ ℓ ^ τ / 2 * β) ∧
    4 * w ^ σ ≤ ℓ ^ τ ∧
    10 * ((N : ℝ) + 1) ^ 2 * (w ^ σ) ^ 2 * (2 + 2 * Real.log ℓ) ^ d ≤ ℓ ^ τ := by
  set n : ℝ := (N : ℝ) + 1 with hn
  set δ : ℝ := c * σ / d with hδ
  set C : ℝ := (2 + 2 / δ) ^ d with hC
  set R : ℝ := (2 + 2 * Real.log ℓ) ^ d with hR
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hδ0 : 0 < δ := by positivity
  have hn1 : 1 ≤ n := by rw [hn]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hδ2 : 0 < 2 / δ := by positivity
  have hC1 : 1 ≤ C := one_le_pow₀ (by linarith)
  have hw2 : (2 : ℝ) ^ (d + 2) ≤ w := le_trans (le_max_left _ _) hw
  have h4 : (4 : ℝ) ≤ 2 ^ (d + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (d + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hwn : 2 * n ≤ w := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hw
  have hwC : n * C ≤ w :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hw
  have hwE : (10 * n ^ 2 * C) ^ σ⁻¹ ≤ w :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hw
  set e : ℝ := w ^ σ with he_def
  set ω : ℝ := w ^ (-(d : ℝ)) with hω_def
  have hE0 : 0 ≤ 10 * n ^ 2 * C := by positivity
  have he : 10 * n ^ 2 * C ≤ e := by
    have := Real.rpow_le_rpow (by positivity) hwE hσ.le
    rwa [Real.rpow_inv_rpow hE0 hσ.ne'] at this
  have hE10 : 10 ≤ 10 * n ^ 2 * C := by
    have : 1 ≤ n ^ 2 * C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) hC1
    nlinarith
  have he4 : 4 ≤ e := by linarith
  have he0 : 0 ≤ e := by linarith
  have hω0 : 0 ≤ ω := by positivity
  have hwτ : w ^ τ ≤ ℓ ^ τ := Real.rpow_le_rpow hw0.le hwℓ (by linarith)
  -- `R ≤ C e`
  have hRle : R ≤ C * e := by
    have hlog0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
    have hlog : Real.log ℓ ≤ ℓ ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ0
    have hℓδ : 1 ≤ ℓ ^ δ := Real.one_le_rpow hℓ hδ0.le
    have hb : 2 + 2 * Real.log ℓ ≤ (2 + 2 / δ) * ℓ ^ δ := by
      have e1 : 2 * (ℓ ^ δ / δ) = 2 / δ * ℓ ^ δ := by ring
      have : 0 ≤ 2 / δ := by positivity
      nlinarith
    calc R ≤ ((2 + 2 / δ) * ℓ ^ δ) ^ d := pow_le_pow_left₀ (by linarith) hb d
      _ = C * (ℓ ^ δ) ^ d := by rw [mul_pow]
      _ = C * (ℓ ^ c) ^ σ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
          congr 2
          rw [hδ]
          field_simp
      _ ≤ C * e := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hℓw hσ.le) (by positivity)
  -- `e² ω ≤ w^{−2}` and `ρ ≤ w⁻¹`
  have hee : e * e = w ^ (2 * σ) := by rw [he_def, ← Real.rpow_add hw0]; ring_nf
  have heeω : e * e * ω ≤ w ^ (-2 : ℝ) := by
    rw [hee, hω_def, ← Real.rpow_add hw0]
    exact Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
  have hw2' : w ^ (-2 : ℝ) = w⁻¹ * w⁻¹ := by
    rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.rpow_add hw0, Real.rpow_neg_one]
  have hρ : n * e * ω * R ≤ w⁻¹ := by
    have hwi : 0 ≤ w⁻¹ := by positivity
    calc n * e * ω * R ≤ n * e * ω * (C * e) :=
          mul_le_mul_of_nonneg_left hRle (by positivity)
      _ = (n * C) * (e * e * ω) := by ring
      _ ≤ w * (w⁻¹ * w⁻¹) := by
          rw [← hw2']; exact mul_le_mul hwC heeω (by positivity) hw0.le
      _ = w⁻¹ := by field_simp
  have hwinv : w⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ hw0 (by norm_num)]; linarith
  have hρ0 : 0 ≤ n * e * ω * R := by
    have : 0 ≤ R := by rw [hR]; exact pow_nonneg (by linarith [Real.log_nonneg hℓ]) _
    positivity
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · -- `n ω ≤ 1/2`
    have : ω ≤ w⁻¹ := by
      rw [hω_def, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
    calc n * ω ≤ n * w⁻¹ := mul_le_mul_of_nonneg_left this (by linarith)
      _ ≤ (w / 2) * w⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 2 := by field_simp
  · -- the remainder
    intro β hβ
    have hKw0 : (0 : ℝ) ≤ Kw := Nat.cast_nonneg _
    have hpow : (n * e * ω * R) ^ Kw ≤ w ^ (-(Kw : ℝ)) := by
      calc (n * e * ω * R) ^ Kw ≤ (w⁻¹) ^ Kw := pow_le_pow_left₀ hρ0 hρ Kw
        _ = w ^ (-(Kw : ℝ)) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]; ring_nf
    have heω : e * ω = w ^ (σ + -(d : ℝ)) := by rw [Real.rpow_add hw0]
    have hX : w ^ (-(Kw : ℝ)) * (2 * (e * ω)) ≤ 2 * (w ^ (-((d : ℝ) / c)) * w⁻¹) := by
      rw [heω, ← Real.rpow_neg_one, ← Real.rpow_add hw0]
      have : w ^ (-(Kw : ℝ)) * (2 * w ^ (σ + -(d : ℝ))) =
          2 * w ^ (-(Kw : ℝ) + (σ + -(d : ℝ))) := by simp only [Real.rpow_add hw0]; ring
      rw [this]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw1 ?_) (by norm_num)
      linarith
    have hℓc : 0 < ℓ ^ c := Real.rpow_pos_of_pos (by linarith) c
    have hℓd : w ^ (-((d : ℝ) / c)) ≤ ℓ ^ (-(d : ℝ)) := by
      have e1 : ℓ ^ (-(d : ℝ)) = (ℓ ^ c) ^ (-((d : ℝ) / c)) := by
        rw [← Real.rpow_mul (by linarith)]; congr 1; field_simp
      rw [e1]
      exact Real.rpow_le_rpow_of_nonpos hℓc hℓw (by
        have : 0 ≤ (d : ℝ) / c := by positivity
        linarith)
    have h2ℓ : (2 * ℓ) ^ (-(d : ℝ)) = (2 : ℝ) ^ (-(d : ℝ)) * ℓ ^ (-(d : ℝ)) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h2d : (2 : ℝ) ^ (-(d : ℝ)) = ((2 : ℝ) ^ d)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have hwi2 : w⁻¹ ≤ ((2 : ℝ) ^ d)⁻¹ / 4 := by
      have : ((2 : ℝ) ^ d)⁻¹ / 4 = ((2 : ℝ) ^ (d + 2))⁻¹ := by rw [pow_add]; field_simp; norm_num
      rw [this]
      exact inv_anti₀ (by positivity) hw2
    have hLτ : 1 ≤ ℓ ^ τ := Real.one_le_rpow hℓ (by linarith)
    have hβ0 : 0 ≤ β := le_trans (by positivity) hβ
    have hwd0 : 0 ≤ w ^ (-((d : ℝ) / c)) := by positivity
    have h2p : 0 < ((2 : ℝ) ^ d)⁻¹ := by positivity
    calc (n * e * ω * R) ^ Kw * (2 * (e * ω))
        ≤ w ^ (-(Kw : ℝ)) * (2 * (e * ω)) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ 2 * (w ^ (-((d : ℝ) / c)) * w⁻¹) := hX
      _ ≤ 2 * (w ^ (-((d : ℝ) / c)) * (((2 : ℝ) ^ d)⁻¹ / 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwi2 hwd0) (by norm_num)
      _ = 1 / 2 * (((2 : ℝ) ^ d)⁻¹ * w ^ (-((d : ℝ) / c))) := by ring
      _ ≤ 1 / 2 * (((2 : ℝ) ^ d)⁻¹ * ℓ ^ (-(d : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓd h2p.le) (by norm_num)
      _ = 1 / 2 * (2 * ℓ) ^ (-(d : ℝ)) := by rw [h2ℓ, h2d]
      _ ≤ ℓ ^ τ / 2 * β := by
          have : (2 * ℓ) ^ (-(d : ℝ)) ≤ ℓ ^ τ * β :=
            hβ.trans (le_mul_of_one_le_left hβ0 hLτ)
          linarith
  · -- `4 e ≤ L^τ`
    have h1 : 4 * e ≤ e * e := mul_le_mul_of_nonneg_right he4 he0
    have h2 : w ^ (2 * σ) ≤ w ^ τ := Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
    linarith
  · -- `10 n² e² R ≤ L^τ`
    have h1 : 10 * n ^ 2 * e ^ 2 * R ≤ (10 * n ^ 2 * C) * (e * e * e) := by
      have := mul_le_mul_of_nonneg_left hRle (show 0 ≤ 10 * n ^ 2 * e ^ 2 by positivity)
      nlinarith
    have h2 : (10 * n ^ 2 * C) * (e * e * e) ≤ e * (e * e * e) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    have h3 : e * (e * e * e) = w ^ (4 * σ) := by
      rw [he_def, ← Real.rpow_add hw0, ← Real.rpow_add hw0, ← Real.rpow_add hw0]; ring_nf
    have h4' : w ^ (4 * σ) ≤ w ^ τ := Real.rpow_le_rpow_of_exponent_le hw1 hστ
    linarith

end Model

end ThetaM

open ThetaM in
/-- **[I, Theorem 1.5]**: (1.24), (1.26), (1.27), the invertibility of
`1 − |m|² S (1 + Σ̃^{(M)})` ([I, (8.18)–(8.19)]), and the change of order `M ≤ N`:
`|Θ^{(N)}_{xy} − Θ^{(M)}_{xy}| ≤ L^τ W^{−(M+1)d/2}` and the same for `(1 − X |m|² S)⁻¹`
([I, (1.23)], [I, (1.29)]). -/
theorem thetaMBounds : thetaMStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M N hMN τ hτ
  by_cases hc0 : 1 ≤ c₀
  · refine ⟨2, fun W L _ hL hadm z hz => ?_⟩
    exfalso
    have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    have h1 : 1 < (L : ℝ) ^ c₁ := Real.one_lt_rpow (by linarith) hc₁
    have h2 : (L : ℝ) ^ (1 - c₀) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    linarith [hadm.1, hadm.2]
  push Not at hc0
  set c₁' : ℝ := min c₁ ((1 - c₀) / 2) with hc1'
  have hc1'0 : 0 < c₁' := lt_min hc₁ (by linarith)
  have hcc : c₀ + c₁' < 1 := by have := min_le_right c₁ ((1 - c₀) / 2); linarith
  set σ : ℝ := min τ 1 / 4 with hσ_def
  have hσ : 0 < σ := by have := lt_min hτ one_pos; rw [hσ_def]; positivity
  have hσ1 : σ ≤ 1 / 4 := by have := min_le_right τ 1; rw [hσ_def]; linarith
  have hστ : 4 * σ ≤ τ := by have := min_le_left τ 1; rw [hσ_def]; linarith
  set Kf : KerFamily d := sigKer (smatVar P) Sig with hKf
  have hIS : ∀ l, 4 ≤ l → IsSelfEnergy d (smatVar P) Sig l := by
    intro l hl
    rcases Nat.even_or_odd l with he | ho
    · exact hSE l hl he
    · exact isSelfEnergy_nil d (smatVar P) Sig l (G13.shape_odd_nil ho (hSg.1 l hl))
  have hKS : ∀ l, KerSymm Kf l := kerSymm_sigKer_smatVar d P Sig
  have hKB : ∀ l, 4 ≤ l → KerBound Kf l := fun l hl => (hIS l hl).2.2
  obtain ⟨W₁, hW₁⟩ := Smat_symm_nonneg d P c₀ c₁' hc₀ hc1'0
  obtain ⟨W₂, hW₂⟩ := Smat_doublyStochastic_adm d P c₀ c₁' hc₀
  have hts := fun l (hl : 4 ≤ l) =>
    thetaSigma d (by omega) P c₀ c₁' κ ε hc₀ hc1'0 hcc hκ hε Kf l (hKS l) (hKB l hl) σ hσ
  choose! F₃ hF₃ using hts
  have hch := fun (o : List ℕ) (ho : ∀ l ∈ o, 4 ≤ l) =>
    chain d (by omega) P c₀ c₁' κ ε hc₀ hc1'0 hcc hκ hε Kf o
      (fun l hl => ⟨hKS l, hKB l (ho l hl)⟩) σ hσ
  choose! F₄ hF₄ using hch
  have hse := fun l (hl : 4 ≤ l) => (hIS l hl).2.2 κ ε c₀ c₁' hκ hε hc₀ hc1'0 hcc τ hτ
  choose! F₅ hF₅ using hse
  set Kw : ℕ := ⌈(d : ℝ) / c₁'⌉₊ + 1 with hKw
  set allW : Finset (List ℕ) := ((List.range Kw).flatMap (words M)).toFinset with hallW
  set Wstar : ℝ := max (2 ^ (d + 2)) (max (2 * ((N : ℝ) + 1)) (max (((N : ℝ) + 1) *
      (2 + 2 / (c₁' * σ / d)) ^ d) ((10 * ((N : ℝ) + 1) ^ 2 * (2 + 2 / (c₁' * σ / d)) ^ d) ^ σ⁻¹)))
    with hWstar
  set W₃ : ℝ := ∑ l ∈ Finset.Icc 4 N, |F₃ l| with hW₃
  set W₄ : ℝ := ∑ o ∈ allW, |F₄ o| with hW₄
  set Wt : ℝ := max (max W₁ W₂) (max (max W₃ W₄) Wstar) with hWt
  have hWsWt : Wstar ≤ Wt := le_trans (le_max_right _ _) (le_max_right _ _)
  have hWt0 : 0 < Wt := lt_of_lt_of_le (lt_of_lt_of_le (by positivity) (le_max_left _ _)) hWsWt
  refine ⟨max (∑ l ∈ Finset.Icc 4 M, F₅ l) (max 2 ⌈Wt ^ c₁'⁻¹⌉₊),
    fun W L _ hL hadm z hz => ?_⟩
  have hL5 : ∑ l ∈ Finset.Icc 4 M, F₅ l ≤ L := le_trans (le_max_left _ _) hL
  have hLn2 : 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLc : ⌈Wt ^ c₁'⁻¹⌉₊ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hadm' : (W, L) ∈ adm c₀ c₁' :=
    ⟨le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (min_le_left _ _)) hadm.1, hadm.2⟩
  have hWtL : Wt ≤ (L : ℝ) ^ c₁' := by
    have h1 : Wt ^ c₁'⁻¹ ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hLc)
    have := Real.rpow_le_rpow (by positivity) h1 hc1'0.le
    rwa [Real.rpow_inv_rpow hWt0.le hc1'0.ne'] at this
  have hW : Wt ≤ (W : ℝ) := hWtL.trans hadm'.1
  have hWL : (W : ℝ) ≤ L := by
    refine hadm.2.trans ?_
    calc (L : ℝ) ^ (1 - c₀) ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one _
  have hWs : Wstar ≤ (W : ℝ) := hWsWt.trans hW
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_trans (by
      have : (1 : ℝ) ≤ 2 ^ (d + 2) := one_le_pow₀ (by norm_num)
      exact this) (le_max_left _ _)) hWs
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  -- the variance matrix
  obtain ⟨hSs, hS0⟩ := hW₁ W L hadm'
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW)
  have hDS := hW₂ W L hadm' (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW)
  have hS1 : ∀ x, ∑ y, Smat P.ψ W L x y = 1 := fun x => sum_row_of_mem_doublyStochastic hDS x
  have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  obtain ⟨hA, ha, hAT, hTA⟩ := theta_rel (Smat P.ψ W L) z hS0 hS1 hz0
  have hSgK : ∀ l, 4 ≤ l → Sg l W L z = Kf l W L z := by
    intro l hl
    rw [hSg.2.1 l hl W L z hSs]
    exact (sigKer_smatVar_eq_of_isSymm P Sig hSs l z).symm
  have hsig : ∀ M', sigTildeM Sg M' W L z = ∑ l ∈ Finset.Icc 4 M', Kf l W L z := fun M' =>
    Finset.sum_congr rfl fun l hl => hSgK l (Finset.mem_Icc.1 hl).1
  -- symmetry of `Θ` and of `Σ_l`
  have hTsym : ∀ x y, cmat (Theta (msc z) (Smat P.ψ W L)) x y =
      cmat (Theta (msc z) (Smat P.ψ W L)) y x := by
    intro x y
    have h := (transpose_propagators (Smat P.ψ W L) hSs.eq (msc z)).2.2
    have := congrFun (congrFun h y) x
    simp only [Matrix.transpose_apply] at this
    simp [cmat, this]
  have hKsym : ∀ l x y, Kf l W L z x y = Kf l W L z y x := by
    intro l x y
    obtain ⟨h1, h2⟩ := hKS l W L z hz0 x (y - x)
    obtain ⟨h3, -⟩ := hKS l W L z hz0 y (x - y)
    rw [add_sub_cancel] at h1 h3
    rw [h1, h2, neg_sub, h3]
  set T : Matrix (Zd d L) (Zd d L) ℂ := cmat (Theta (msc z) (Smat P.ψ W L)) with hT
  set K : ℕ → Matrix (Zd d L) (Zd d L) ℂ := fun l => Kf l W L z with hK
  have hTK : ∀ l, 4 ≤ l → l ≤ N → ∀ x y, ‖(T * K l) x y‖ ≤
      (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * brk d L W x y ^ (-(d : ℝ)) := by
    intro l hl4 hlN x y
    have hW3 : F₃ l ≤ W := le_trans (le_sum_abs _ F₃ (Finset.mem_Icc.2 ⟨hl4, hlN⟩))
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hW))
    exact hF₃ l hl4 W L hadm' hW3 z hz x y
  have hKT : ∀ l, 4 ≤ l → l ≤ N → ∀ x y, ‖(K l * T) x y‖ ≤
      (W : ℝ) ^ σ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * brk d L W y x ^ (-(d : ℝ)) := by
    intro l hl4 hlN x y
    have e : (K l * T) x y = (T * K l) y x := by
      simp only [Matrix.mul_apply, hK]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hKsym l x w, hTsym w y, mul_comm]
    rw [e]
    exact hTK l hl4 hlN y x
  have hd2 : 2 ≤ d := by omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hwt : ∀ l : ℕ, 4 ≤ l → (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) ≤ (W : ℝ) ^ (-(d : ℝ)) := by
    intro l hl
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    have : (4 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hwt' : ∀ l : ℕ, M + 1 ≤ l → (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) ≤
      (W : ℝ) ^ (-(((M : ℝ) - 1) * d / 2)) := by
    intro l hl
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    have : (M : ℝ) + 1 ≤ l := by exact_mod_cast hl
    nlinarith
  have hbrkW : ∀ x y : Zd d L, (W : ℝ) ≤ brk d L W x y := fun x y => by
    unfold brk; have := Nat.cast_nonneg (α := ℝ) (zdistInf d L (x - y)); linarith
  have hb0 : ∀ x y : Zd d L, 0 ≤ brk d L W x y ^ (-(d : ℝ)) := fun x y =>
    Real.rpow_nonneg (by linarith [hbrkW x y]) _
  have hbω : ∀ x y : Zd d L, brk d L W x y ^ (-(d : ℝ)) ≤ (W : ℝ) ^ (-(d : ℝ)) := fun x y =>
    Real.rpow_le_rpow_of_nonpos hW0 (hbrkW x y) (by linarith)
  have hbr : ∀ x, ∑ y, brk d L W x y ^ (-(d : ℝ)) ≤ (2 + 2 * Real.log L) ^ d :=
    brk_sum d L W hWn
  have hbc : ∀ y, ∑ x, brk d L W x y ^ (-(d : ℝ)) ≤ (2 + 2 * Real.log L) ^ d := by
    intro y
    simp only [brk_comm d L W _ y]
    exact brk_sum d L W hWn y
  have hchB : ∀ k < Kw, ∀ o ∈ words M k, ∀ x y,
      ‖chainM T K o x y‖ ≤ (W : ℝ) ^ σ * ((W : ℝ) ^ (-(d : ℝ))) ^ k * bB d L W x y := by
    intro k hk o ho x y
    obtain ⟨hlen, hlet⟩ := words_mem ho
    have hmem : o ∈ allW := List.mem_toFinset.2 (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ho⟩)
    have hW4 : F₄ o ≤ W := le_trans (le_sum_abs _ F₄ hmem)
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hW))
    have h := hF₄ o (fun l hl => (hlet l hl).1) W L hadm' hW4 z hz x y
    have hex := chain_exp_le d W hW1 o (fun l hl => (hlet l hl).1)
    rw [hlen] at hex
    calc ‖chainM T K o x y‖ = ‖(detData (Smat P.ψ W L) z (fun l => Kf l W L z)).chain o x y‖ :=
          rfl
      _ ≤ _ := h
      _ ≤ (W : ℝ) ^ σ * ((W : ℝ) ^ (-(d : ℝ))) ^ k * bB d L W x y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex (by positivity))
            (bB_nonneg d L W x y)
  have hKwR : (d : ℝ) / c₁' + 1 ≤ Kw := by
    rw [hKw]; push_cast
    linarith [Nat.le_ceil ((d : ℝ) / c₁')]
  obtain ⟨s1, s2, s3, s4, s5⟩ :=
    scalars d N Kw hd c₁' σ τ W L hc1'0 hσ hσ1 hστ hKwR hL1 hWL hadm'.1 hWs
  have he1 : (1 : ℝ) ≤ (W : ℝ) ^ σ := Real.one_le_rpow hW1 hσ.le
  have hR1 : (1 : ℝ) ≤ (2 + 2 * Real.log L) ^ d :=
    one_le_pow₀ (by linarith [Real.log_nonneg hL1])
  obtain ⟨c1, c2, c3, c4⟩ := core (amat (Smat P.ψ W L) z) T K M N Kw hMN (Nat.succ_pos _)
    (fun x y => brk d L W x y ^ (-(d : ℝ))) (bB d L W)
    (fun l => (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) (‖msc z‖ ^ 2) ((W : ℝ) ^ σ)
    ((2 + 2 * Real.log L) ^ d) ((W : ℝ) ^ (-(d : ℝ))) ((W : ℝ) ^ (-(((M : ℝ) - 1) * d / 2)))
    ((L : ℝ) ^ τ) hA ha hAT hTA hTK hKT hwt hwt' hb0 hbω hbr hbc (bB_nonneg d L W)
    (bB_le d L W hd2 hW1) hchB he1 hR1 (by positivity) (by positivity) s1 s2
    (fun x y => s3 _ (bB_ge d L W hd2 hW1 hWL x y)) s4 s5
  have hωω : (W : ℝ) ^ (-(((M : ℝ) - 1) * d / 2)) * (W : ℝ) ^ (-(d : ℝ)) =
      (W : ℝ) ^ (-(((M : ℝ) + 1) * d / 2)) := by
    rw [← Real.rpow_add hW0]; ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsig M]; exact c1
  · intro x y
    simp only [thetaM]
    rw [hsig M]
    exact c2 x y
  · intro l hl4 hlM x
    rw [hSgK l hl4]
    have hl5 : F₅ l ≤ L := le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (F₅ i))
      (Finset.mem_Icc.2 ⟨hl4, hlM⟩)) hL5
    exact (hF₅ l hl4 W L hl5 hadm' z hz).1 x
  · intro l hl4 hlM
    rw [hSgK l hl4]
    have hl5 : F₅ l ≤ L := le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (F₅ i))
      (Finset.mem_Icc.2 ⟨hl4, hlM⟩)) hL5
    exact (hF₅ l hl4 W L hl5 hadm' z hz).2
  · intro x y
    simp only [thetaM]
    rw [hsig N, hsig M, ← hωω]
    exact c3 x y
  · intro x y
    simp only [resM]
    rw [hsig N, hsig M, ← hωω]
    exact c4 x y

end RBM8D
