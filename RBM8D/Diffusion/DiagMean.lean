import RBM8D.Diffusion.Defs
import RBM8D.Bound.GraphSum
import RBM8D.Kernel.Decay
import RBM8D.Prob.PartialPoly
import RBM8D.Graph.Local.Model

/-!
# The expectation of the diagonal resolvent entries

`diagMeanStmt`: from the local law [I, Theorem 1.4, (1.19)], `|E G_{bb} − m| ≤ W^τ W^{−3d/2}`
on `𝐃(κ, ε)` along `adm(c₀, c₁)`; this is the diagonal term `m δ_{xb} E(Ḡ_{bb} − m̄)` of the local
correction of [I, (8.16)], bounded as [I, (1.28)] requires (`B_{bb}^{3/2} = W^{−3d/2}`).

Write `Δ_x = G_{xx} − m`, `g_x = E Δ_x`, `C_{αb} = E[Δ_α Δ_b]` and `S^+ = m² S (1 − m² S)⁻¹`.
* By `G − m = −m (H + m) G` ([I, (1.39)]) and the Gaussian integration by parts,
  `(1 − m² S) g = m v` with `v_x = Σ_α s_{xα} C_{αx}`, and `(1 − m² S) C_{·b} = m F_{·b}` with
  `F_{αb} = E Σ_k s_{αk} (Δ_k Δ_α Δ_b + G_{kα} G_{bk} G_{αb})`.
* `(1 − m² S)⁻¹ = 1 + S^+`, and `S^+` has entries `O(W^{−d})` and row sums `O(W^{τ'})`
  ([I, Lemma 2.2]).
* On the event of the local law every `|G_{xy} − m δ_{xy}|` is at most `W^{τ'/2} W^{−d/2}`, so that
  `F_{αb} = O(W^{3τ'/2} W^{−3d/2})` for `α ≠ b` and `F_{bb} = O(W^{τ'} W^{−d})`; off the event
  `|G_{xy}| ≤ η⁻¹ ≤ L²`, and the complement of the event has probability at most `L^{2d} L^{−D}`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Complex Matrix
open scoped BigOperators

namespace RBM8D

open Graphs

namespace DiagMean

/-! ## Test functions and integration by parts -/

section IBP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma tf_G {z : ℂ} (hz : z.im ≠ 0) (x y : ι) :
    TestFn fun ω : Sample ι => green (hmat ω) z x y :=
  testFn_green z hz x y

private lemma tf_mul {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) :
    TestFn fun ω => F ω * G ω :=
  testFn_closed.2.2.1 F G hF hG

private lemma tf_const (c : ℂ) : TestFn fun _ : Sample ι => c :=
  testFn_closed.1 c

private lemma tf_add {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) :
    TestFn fun ω => F ω + G ω :=
  testFn_closed.2.1 F G hF hG

private lemma tf_sub {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) :
    TestFn fun ω => F ω - G ω := by
  have e : (fun ω => F ω - G ω) = fun ω => F ω + (-1 : ℂ) * G ω := by
    funext ω; ring
  rw [e]
  exact tf_add hF (tf_mul (tf_const _) hG)

private lemma tf_neg {F : Sample ι → ℂ} (hF : TestFn F) : TestFn fun ω => -F ω := by
  have e : (fun ω => -F ω) = fun ω => (-1 : ℂ) * F ω := by
    funext ω; ring
  rw [e]
  exact tf_mul (tf_const _) hF

private lemma tf_dh (a b : ι) {F : Sample ι → ℂ} (hF : TestFn F) : TestFn (dh a b F) :=
  testFn_closed.2.2.2.2.1 a b F hF

/-- `Δ_x = G_{xx} − m` is a test function. -/
private lemma tf_D {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    TestFn fun ω : Sample ι => green (hmat ω) z x x - msc z :=
  tf_sub (tf_G hz x x) (tf_const _)

private lemma integ (S : Matrix ι ι ℝ) {F : Sample ι → ℂ} (hF : TestFn F) :
    Integrable F (gaussLaw S) :=
  integrable_of_polyMeas S F (polyMeas_of_testFn F hF)

/-- `G_{aa} − m = −m Σ_k h_{ak} G_{ka} − m² G_{aa}`, from `(H − z) G = 1` and
`m² + z m + 1 = 0` ([I, (1.39)]). -/
private lemma delta_eq {z : ℂ} (hz : z.im ≠ 0) (ω : Sample ι) (a : ι) :
    green (hmat ω) z a a - msc z =
      -msc z * ∑ k, hmat ω a k * green (hmat ω) z k a - msc z ^ 2 * green (hmat ω) z a a := by
  have h1 := congrFun (congrFun (sub_mul_green (hmat_isHermitian ω) hz) a) a
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
  have hm := msc_mul z
  linear_combination (msc z) * h1 + green (hmat ω) z a a * hm

/-- The integration by parts of the proof: for a test function `Ψ`,
`E[Δ_a Ψ] = Σ_k s_{ak} E[m² Δ_k Ψ + m (Δ_k Δ_a Ψ − G_{ka} ∂_{h_{ka}} Ψ)]`. -/
private theorem ibp (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hz : z.im ≠ 0) (a : ι) (Ψ : Sample ι → ℂ)
    (hΨ : TestFn Ψ) :
    ∫ ω, (green (hmat ω) z a a - msc z) * Ψ ω ∂(gaussLaw S) =
      ∑ k, (S a k : ℂ) * ∫ ω, (msc z ^ 2 * ((green (hmat ω) z k k - msc z) * Ψ ω) +
        msc z * ((green (hmat ω) z k k - msc z) * (green (hmat ω) z a a - msc z) * Ψ ω -
          green (hmat ω) z k a * dh k a Ψ ω)) ∂(gaussLaw S) := by
  set m := msc z with hm
  set T : ι → Sample ι → ℂ := fun k ω =>
    -(green (hmat ω) z k k * green (hmat ω) z a a * Ψ ω) +
      green (hmat ω) z k a * dh k a Ψ ω with hT
  have hTt : ∀ k, TestFn (T k) := fun k =>
    tf_add (tf_neg (tf_mul (tf_mul (tf_G hz k k) (tf_G hz a a)) hΨ))
      (tf_mul (tf_G hz k a) (tf_dh k a hΨ))
  have hI := fun {F : Sample ι → ℂ} (hF : TestFn F) => integ S hF
  -- the derivative of `G_{ka} Ψ` along `h_{ka}`
  have hdh : ∀ k, dh k a (fun ω => green (hmat ω) z k a * Ψ ω) = T k := by
    intro k
    have h := dh_mul k a (fun ω => green (hmat ω) z k a) Ψ (tf_G hz k a) hΨ
    funext ω
    have h' := congrFun h ω
    simp only [Pi.add_apply, Pi.mul_apply] at h'
    rw [show (fun ω => green (hmat ω) z k a * Ψ ω) = (fun ω => green (hmat ω) z k a) * Ψ from rfl,
      h', dh_green z hz k a k a ω]
    simp only [hT]
    ring
  -- integration by parts in each `h_{ak}`
  have hibp : ∀ k, ∫ ω, hmat ω a k * (green (hmat ω) z k a * Ψ ω) ∂(gaussLaw S) =
      (S a k : ℂ) * ∫ ω, T k ω ∂(gaussLaw S) := by
    intro k
    rw [integral_hmat_mul S hS hS0 a k _ (tf_mul (tf_G hz k a) hΨ), hdh k]
  have hHint : ∀ k, Integrable (fun ω => hmat ω a k * (green (hmat ω) z k a * Ψ ω))
      (gaussLaw S) := by
    intro k
    obtain ⟨hmeas, C, hC⟩ := testFn_closed.2.2.2.2.2 _ (tf_mul (tf_G hz k a) hΨ)
    exact (integrable_of_polyMeas S _ (polyMeas_hmat a k)).mul_bdd hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  -- the left side
  have hL : ∫ ω, (green (hmat ω) z a a - m) * Ψ ω ∂(gaussLaw S) =
      ∑ k, -m * ((S a k : ℂ) * ∫ ω, T k ω ∂(gaussLaw S)) -
        m ^ 2 * ∫ ω, green (hmat ω) z a a * Ψ ω ∂(gaussLaw S) := by
    have hpt : ∀ ω, (green (hmat ω) z a a - m) * Ψ ω =
        ∑ k, -m * (hmat ω a k * (green (hmat ω) z k a * Ψ ω)) -
          m ^ 2 * (green (hmat ω) z a a * Ψ ω) := by
      intro ω
      rw [hm, delta_eq hz ω a, sub_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    simp_rw [hpt]
    rw [integral_sub (integrable_finsetSum _ fun k _ => (hHint k).const_mul _)
      ((hI (tf_mul (tf_G hz a a) hΨ)).const_mul _), integral_finsetSum _
      fun k _ => (hHint k).const_mul _, integral_const_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, hibp k]
  -- the right side, term by term
  have hR : ∀ k, ∫ ω, (m ^ 2 * ((green (hmat ω) z k k - m) * Ψ ω) +
        m * ((green (hmat ω) z k k - m) * (green (hmat ω) z a a - m) * Ψ ω -
          green (hmat ω) z k a * dh k a Ψ ω)) ∂(gaussLaw S) =
      -m * ∫ ω, T k ω ∂(gaussLaw S) - m ^ 2 * ∫ ω, green (hmat ω) z a a * Ψ ω ∂(gaussLaw S) := by
    intro k
    have hpt : ∀ ω, m ^ 2 * ((green (hmat ω) z k k - m) * Ψ ω) +
        m * ((green (hmat ω) z k k - m) * (green (hmat ω) z a a - m) * Ψ ω -
          green (hmat ω) z k a * dh k a Ψ ω) =
        -m * T k ω - m ^ 2 * (green (hmat ω) z a a * Ψ ω) := by
      intro ω; simp only [hT]; ring
    simp_rw [hpt]
    rw [integral_sub ((hI (hTt k)).const_mul _) ((hI (tf_mul (tf_G hz a a) hΨ)).const_mul _),
      integral_const_mul, integral_const_mul]
  have hS1c : ∑ k, (S a k : ℂ) = 1 := by exact_mod_cast hS1 a
  rw [hL]
  simp_rw [hR]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hS1c, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `Δ_x = G_{xx} − m` at the sample `ω`. -/
private def dlt (z : ℂ) (ω : Sample ι) (x : ι) : ℂ := green (hmat ω) z x x - msc z

/-- `X_{k,αb} = Δ_k Δ_α Δ_b + G_{kα} G_{bk} G_{αb}` at the sample `ω`. -/
private def xk (z : ℂ) (ω : Sample ι) (k a b : ι) : ℂ :=
  dlt z ω k * dlt z ω a * dlt z ω b +
    green (hmat ω) z k a * green (hmat ω) z b k * green (hmat ω) z a b

/-- `F_{αb} = E Σ_k s_{αk} X_{k,αb}`. -/
private def fv (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι) : ℂ :=
  ∫ ω, ∑ k, (S a k : ℂ) * xk z ω k a b ∂(gaussLaw S)

private lemma tf_dlt {z : ℂ} (hz : z.im ≠ 0) (x : ι) : TestFn fun ω : Sample ι => dlt z ω x :=
  tf_D hz x

private lemma tf_xk {z : ℂ} (hz : z.im ≠ 0) (k a b : ι) : TestFn fun ω : Sample ι => xk z ω k a b :=
  tf_add (tf_mul (tf_mul (tf_dlt hz k) (tf_dlt hz a)) (tf_dlt hz b))
    (tf_mul (tf_mul (tf_G hz k a) (tf_G hz b k)) (tf_G hz a b))

/-- The first identity of the proof: `E Δ_x = Σ_k m² s_{xk} E Δ_k + m Σ_k s_{xk} E[Δ_k Δ_x]`,
that is `(1 − m² S) g = m v`. -/
private theorem step1 (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hz : z.im ≠ 0) (x : ι) :
    ∫ ω, dlt z ω x ∂(gaussLaw S) =
      ∑ k, msc z ^ 2 * (S x k : ℂ) * ∫ ω, dlt z ω k ∂(gaussLaw S) +
        msc z * ∑ k, (S x k : ℂ) * ∫ ω, dlt z ω k * dlt z ω x ∂(gaussLaw S) := by
  have h := ibp S hS hS0 hS1 hz x (fun _ => 1) (tf_const 1)
  have h0 : ∀ k, dh k x (fun _ : Sample ι => (1 : ℂ)) = 0 := fun k => dh_const k x 1
  simp only [mul_one, h0, Pi.zero_apply, mul_zero, sub_zero] at h
  simp only [dlt]
  rw [h, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_add ((integ S (tf_D hz k)).const_mul _)
    ((integ S (tf_mul (tf_D hz k) (tf_D hz x))).const_mul _), integral_const_mul,
    integral_const_mul]
  ring

/-- The second identity of the proof: `E[Δ_α Δ_b] = Σ_k m² s_{αk} E[Δ_k Δ_b] + m F_{αb}`, that is
`(1 − m² S) C_{·b} = m F_{·b}`. -/
private theorem step2 (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hz : z.im ≠ 0) (a b : ι) :
    ∫ ω, dlt z ω a * dlt z ω b ∂(gaussLaw S) =
      ∑ k, msc z ^ 2 * (S a k : ℂ) * ∫ ω, dlt z ω k * dlt z ω b ∂(gaussLaw S) +
        msc z * fv S z a b := by
  have h := ibp S hS hS0 hS1 hz a (fun ω => dlt z ω b) (tf_dlt hz b)
  have h0 : ∀ k ω, dh k a (fun ω => dlt z ω b) ω =
      -(green (hmat ω) z b k * green (hmat ω) z a b) := by
    intro k ω
    have e : (fun ω => dlt z ω b) = (fun ω => green (hmat ω) z b b) + fun _ => -msc z := by
      funext ω; simp [dlt, sub_eq_add_neg]
    rw [e, dh_add k a _ _ (tf_G hz b b) (tf_const _), dh_const, add_zero,
      dh_green z hz k a b b ω]
  simp only [h0] at h
  simp only [dlt] at h ⊢
  rw [h, fv, integral_finsetSum _ fun k _ => (integ S (tf_xk hz k a b)).const_mul _,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpt : ∀ ω, msc z ^ 2 * ((green (hmat ω) z k k - msc z) * (green (hmat ω) z b b - msc z)) +
      msc z * ((green (hmat ω) z k k - msc z) * (green (hmat ω) z a a - msc z) *
        (green (hmat ω) z b b - msc z) - green (hmat ω) z k a *
          -(green (hmat ω) z b k * green (hmat ω) z a b)) =
      msc z ^ 2 * ((green (hmat ω) z k k - msc z) * (green (hmat ω) z b b - msc z)) +
        msc z * xk z ω k a b := by
    intro ω; simp only [xk, dlt]; ring
  simp_rw [hpt]
  rw [integral_add ((integ S (tf_mul (tf_D hz k) (tf_D hz b))).const_mul _)
    ((integ S (tf_xk hz k a b)).const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

end IBP

/-! ## The inversion of `1 − m² S` -/

section Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖Σ_k s_{xk} c_k‖ ≤ Σ_k s_{xk} ‖c_k‖` for `S ≥ 0`. -/
private lemma norm_wsum_le (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y) (x : ι) (c : ι → ℂ) :
    ‖∑ k, (S x k : ℂ) * c k‖ ≤ ∑ k, S x k * ‖c k‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hS0 x k)]

/-- For `S ≥ 0` with row sums `1` and `|m| < 1`, the matrix `1 − m² S` is invertible. -/
private lemma isUnit_one_sub (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {m : ℂ} (hm : ‖m‖ < 1) : IsUnit (1 - m ^ 2 • cmat S) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hv0⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  apply hv
  have hfix : ∀ x, v x = m ^ 2 * ∑ y, (S x y : ℂ) * v y := by
    intro x
    have h := congrFun hv0 x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at h
    rw [h]
    simp [Matrix.mulVec, dotProduct, cmat]
  rcases isEmpty_or_nonempty ι with hι | hι
  · funext x; exact isEmptyElim x
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max fun x => ‖v x‖
  have hm2 : ‖m‖ ^ 2 < 1 := by nlinarith [norm_nonneg m]
  have hle : ‖v x₀‖ ≤ ‖m‖ ^ 2 * ‖v x₀‖ := by
    calc ‖v x₀‖ = ‖m‖ ^ 2 * ‖∑ y, (S x₀ y : ℂ) * v y‖ := by
          rw [hfix x₀, norm_mul, norm_pow]
      _ ≤ ‖m‖ ^ 2 * ∑ y, S x₀ y * ‖v y‖ :=
          mul_le_mul_of_nonneg_left (norm_wsum_le S hS0 x₀ v) (by positivity)
      _ ≤ ‖m‖ ^ 2 * ∑ y, S x₀ y * ‖v x₀‖ := by
          gcongr with y _
          · exact hS0 x₀ y
          · exact hx₀ y
      _ = ‖m‖ ^ 2 * ‖v x₀‖ := by rw [← Finset.sum_mul, hS1 x₀, one_mul]
  have h0 : ‖v x₀‖ = 0 := by nlinarith [norm_nonneg (v x₀)]
  funext x
  exact norm_le_zero_iff.mp ((hx₀ x).trans h0.le)

/-- `(1 + S^+)(1 − m² S) = 1` when `1 − m² S` is invertible. -/
private lemma one_add_mul_one_sub (S : Matrix ι ι ℝ) (m : ℂ) (hU : IsUnit (1 - m ^ 2 • cmat S)) :
    (1 + Splus m S) * (1 - m ^ 2 • cmat S) = 1 := by
  obtain ⟨u, hu⟩ := hU
  have h2 : Ring.inverse (1 - m ^ 2 • cmat S) * (1 - m ^ 2 • cmat S) = 1 := by
    rw [← hu, Ring.inverse_mul_cancel _ u.isUnit]
  rw [Splus, add_mul, one_mul, mul_assoc, h2, mul_one]
  abel

/-- If `u = A u + w` and `(1 + R)(1 − A) = 1`, then `u = w + R w`. -/
private lemma solve (A R : Matrix ι ι ℂ) (h : (1 + R) * (1 - A) = 1) (u w : ι → ℂ)
    (hu : ∀ x, u x = ∑ k, A x k * u k + w x) (x : ι) : u x = w x + ∑ y, R x y * w y := by
  have hw : (1 - A) *ᵥ u = w := by
    funext y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hu y]
    simp [Matrix.mulVec, dotProduct]
  have h' : (((1 + R) * (1 - A)) *ᵥ u) x = ((1 : Matrix ι ι ℂ) *ᵥ u) x := by rw [h]
  rw [← Matrix.mulVec_mulVec, hw, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at h'
  rw [← h']
  simp [Matrix.mulVec, dotProduct]

/-- The deterministic chain of the proof: from `(1 − m² S) g = m v`, `v_x = Σ_k s_{xk} C_{kx}`,
`(1 − m² S) C_{·b} = m F_{·b}`, `|F_{αb}| ≤ β₁ + δ_{αb} β₂`, `|S^+_{xy}| ≤ r₀`,
`Σ_y |S^+_{xy}| ≤ r₁` and `s_{xx} ≤ s₀`: `|g_b| ≤ (1 + r₁)((1 + r₁) β₁ + (s₀ + r₀) β₂)`. -/
private theorem chain (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : ∀ x, ∑ y, S x y = 1)
    (m : ℂ) (hm : ‖m‖ ≤ 1) (R : Matrix ι ι ℂ) (hR : (1 + R) * (1 - m ^ 2 • cmat S) = 1)
    (g : ι → ℂ) (C F : ι → ι → ℂ)
    (h1 : ∀ x, g x = ∑ k, m ^ 2 * (S x k : ℂ) * g k + m * ∑ k, (S x k : ℂ) * C k x)
    (h2 : ∀ a b, C a b = ∑ k, m ^ 2 * (S a k : ℂ) * C k b + m * F a b)
    (β₁ β₂ r₀ r₁ s₀ : ℝ) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hr₁ : 0 ≤ r₁)
    (hF : ∀ a b, ‖F a b‖ ≤ β₁ + if a = b then β₂ else 0)
    (hR0 : ∀ x y, ‖R x y‖ ≤ r₀) (hR1 : ∀ x, ∑ y, ‖R x y‖ ≤ r₁) (hs : ∀ x, S x x ≤ s₀)
    (b : ι) :
    ‖g b‖ ≤ (1 + r₁) * ((1 + r₁) * β₁ + (s₀ + r₀) * β₂) := by
  have hA : ∀ x k, (m ^ 2 • cmat S) x k = m ^ 2 * (S x k : ℂ) := fun x k => by
    simp [cmat]
  -- `|w + R w|` for `|w_y| ≤ c + δ_{y y₀} c'`
  have hres : ∀ (w : ι → ℂ) (c c' : ℝ) (y₀ : ι), 0 ≤ c → 0 ≤ c' →
      (∀ y, ‖w y‖ ≤ c + if y = y₀ then c' else 0) → ∀ x,
        ‖w x + ∑ y, R x y * w y‖ ≤ (1 + r₁) * c + (if x = y₀ then c' else 0) + r₀ * c' := by
    intro w c c' y₀ hc hc' hw x
    have hsum : ‖∑ y, R x y * w y‖ ≤ r₁ * c + r₀ * c' := by
      calc ‖∑ y, R x y * w y‖ ≤ ∑ y, ‖R x y‖ * (c + if y = y₀ then c' else 0) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hw y) (norm_nonneg _)
        _ = (∑ y, ‖R x y‖) * c + ‖R x y₀‖ * c' := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_ite, mul_zero,
              Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        _ ≤ r₁ * c + r₀ * c' := by
            gcongr
            · exact hR1 x
            · exact hR0 x y₀
    calc ‖w x + ∑ y, R x y * w y‖ ≤ ‖w x‖ + ‖∑ y, R x y * w y‖ := norm_add_le _ _
      _ ≤ (c + if x = y₀ then c' else 0) + (r₁ * c + r₀ * c') := add_le_add (hw x) hsum
      _ = _ := by ring
  -- the columns of `C`
  have hC : ∀ a b, ‖C a b‖ ≤ (1 + r₁) * β₁ + (if a = b then β₂ else 0) + r₀ * β₂ := by
    intro a b
    have hsol := solve (m ^ 2 • cmat S) R hR (fun a => C a b) (fun a => m * F a b)
      (fun a => by simp only [hA]; exact h2 a b) a
    rw [hsol]
    refine hres (fun a => m * F a b) β₁ β₂ b hβ₁ hβ₂ (fun y => ?_) a
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (hF y b)
  -- the vector `v`
  set V := (1 + r₁) * β₁ + (s₀ + r₀) * β₂ with hV
  have hV0 : 0 ≤ (1 + r₁) * β₁ := by positivity
  have hv : ∀ x, ‖m * ∑ k, (S x k : ℂ) * C k x‖ ≤ V := by
    intro x
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hm).trans ?_
    calc ‖∑ k, (S x k : ℂ) * C k x‖ ≤ ∑ k, S x k * ‖C k x‖ := norm_wsum_le S hS0 x _
      _ ≤ ∑ k, S x k * ((1 + r₁) * β₁ + (if k = x then β₂ else 0) + r₀ * β₂) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hC k x) (hS0 x k)
      _ = ∑ k, (S x k * ((1 + r₁) * β₁ + r₀ * β₂) + if k = x then S x k * β₂ else 0) :=
          Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
      _ = ((1 + r₁) * β₁ + r₀ * β₂) * ∑ k, S x k + S x x * β₂ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_mul]
          simp only [Finset.mem_univ, ite_true]
          ring
      _ ≤ V := by
          rw [hS1 x, mul_one, hV]
          nlinarith [hs x]
  have hsol := solve (m ^ 2 • cmat S) R hR g (fun x => m * ∑ k, (S x k : ℂ) * C k x)
    (fun x => by simp only [hA]; exact h1 x) b
  rw [hsol]
  have hVn : 0 ≤ V := le_trans (norm_nonneg _) (hv b)
  have := hres (fun x => m * ∑ k, (S x k : ℂ) * C k x) V 0 b hVn le_rfl
    (fun y => by simp only [ite_self, add_zero]; exact hv y) b
  simp only [ite_self, add_zero, mul_zero] at this
  exact this

end Linear

/-! ## The bound at fixed `(W, L)` -/

section Fixed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖E F‖ ≤ A + M P(Bad)` for `|F| ≤ M` everywhere and `|F| ≤ A` off `Bad` (any set `Bad`,
through a measurable superset of the same measure). -/
private lemma norm_integral_le_good {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℂ) (Bad : Set Ω) (A M : ℝ)
    (hA : 0 ≤ A) (hM : ∀ ω, ‖F ω‖ ≤ M) (hgood : ∀ ω, ω ∉ Bad → ‖F ω‖ ≤ A) :
    ‖∫ ω, F ω ∂μ‖ ≤ A + M * (μ Bad).toReal := by
  set T := toMeasurable μ Bad with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable μ Bad
  have hbd : ∀ ω, ‖F ω‖ ≤ A + M * T.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      linarith [hM ω]
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact hgood ω fun h => hω (subset_toMeasurable μ Bad h)
  have h2 : Integrable (fun ω => M * T.indicator (1 : Ω → ℝ) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hTm).const_mul M
  have hint : Integrable (fun ω => A + M * T.indicator 1 ω) μ := (integrable_const A).add h2
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbd)).trans (le_of_eq ?_)
  rw [integral_add (integrable_const A) h2, integral_const, integral_const_mul,
    integral_indicator_one hTm, hT]
  simp [measureReal_def, measure_toMeasurable]

/-- `‖abc‖ ≤ ABC` from `‖a‖ ≤ A`, `‖b‖ ≤ B`, `‖c‖ ≤ C`. -/
private lemma norm_mul3_le {a b c : ℂ} {A B C : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) :
    ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  have hA : 0 ≤ A := (norm_nonneg _).trans ha
  have hB : 0 ≤ B := (norm_nonneg _).trans hb
  exact mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hA) hc (norm_nonneg _) (by positivity)

/-- On a sample with `|G_{xy} − m δ_{xy}| ≤ ρ ≤ 1` for all `x, y` and `|m| ≤ 1`:
`|X_{k,αb}| ≤ 2ρ³ + 2ρ² (δ_{kα} + δ_{kb}) + δ_{αb} (2ρ² + 8 δ_{kb})`. -/
private lemma norm_xk_good {z : ℂ} (hm : ‖msc z‖ ≤ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ω : Sample ι) (hω : ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (k a b : ι) :
    ‖xk z ω k a b‖ ≤ 2 * ρ ^ 3 + 2 * ρ ^ 2 * ((if k = a then 1 else 0) + (if k = b then 1 else 0)) +
      (if a = b then 2 * ρ ^ 2 + (if k = b then 8 else 0) else 0) := by
  have hoff : ∀ x y, x ≠ y → ‖green (hmat ω) z x y‖ ≤ ρ := fun x y h => by
    have := hω x y; simpa [entryErr, h] using this
  have hd : ∀ x, ‖dlt z ω x‖ ≤ ρ := fun x => by
    have := hω x x; simpa [entryErr, dlt] using this
  have hdiag : ∀ x, ‖green (hmat ω) z x x‖ ≤ 2 := fun x => by
    have e : green (hmat ω) z x x = dlt z ω x + msc z := by simp [dlt]
    rw [e]
    linarith [norm_add_le (dlt z ω x) (msc z), hd x]
  have hD3 : ‖dlt z ω k * dlt z ω a * dlt z ω b‖ ≤ ρ * ρ * ρ := norm_mul3_le (hd k) (hd a) (hd b)
  have hsplit : ‖xk z ω k a b‖ ≤ ρ * ρ * ρ +
      ‖green (hmat ω) z k a * green (hmat ω) z b k * green (hmat ω) z a b‖ :=
    (norm_add_le _ _).trans (add_le_add hD3 le_rfl)
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  have hρ3 : ρ ^ 3 ≤ ρ ^ 2 := by nlinarith
  refine hsplit.trans ?_
  by_cases hab : a = b
  · subst hab
    by_cases hk : k = a
    · subst hk
      have h3 := norm_mul3_le (hdiag k) (hdiag k) (hdiag k)
      simp only [ite_true]
      nlinarith
    · have h3 := norm_mul3_le (hoff k a hk) (hoff a k (Ne.symm hk)) (hdiag a)
      simp only [hk, ite_true, ite_false]
      nlinarith
  · by_cases hka : k = a
    · subst hka
      have h3 := norm_mul3_le (hdiag k) (hoff b k (Ne.symm hab)) (hoff k b hab)
      simp only [hab, ite_true, ite_false]
      nlinarith
    · by_cases hkb : k = b
      · subst hkb
        have h3 := norm_mul3_le (hoff k a hka) (hdiag k) (hoff a k (Ne.symm hka))
        simp only [hab, hka, ite_true, ite_false]
        nlinarith
      · have h3 := norm_mul3_le (hoff k a hka) (hoff b k (Ne.symm hkb)) (hoff a b hab)
        simp only [hab, hka, hkb, ite_false]
        nlinarith

/-- On a sample of the local-law event, `|Σ_k s_{αk} X_{k,αb}| ≤ 2ρ³ + 4ρ² s₀ + δ_{αb}(2ρ² + 8s₀)`
for `s_{xy} ≤ s₀`. -/
private lemma norm_sum_xk_good (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hm : ‖msc z‖ ≤ 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ω : Sample ι)
    (hω : ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (a b : ι) :
    ‖∑ k, (S a k : ℂ) * xk z ω k a b‖ ≤
      2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + (if a = b then 2 * ρ ^ 2 + 8 * s₀ else 0) := by
  refine (norm_wsum_le S hS0 a _).trans ?_
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  calc ∑ k, S a k * ‖xk z ω k a b‖
      ≤ ∑ k, S a k * (2 * ρ ^ 3 + 2 * ρ ^ 2 * ((if k = a then 1 else 0) +
          (if k = b then 1 else 0)) + (if a = b then 2 * ρ ^ 2 + (if k = b then 8 else 0)
            else 0)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (norm_xk_good hm hρ0 hρ1 ω hω k a b) (hS0 a k)
    _ = 2 * ρ ^ 3 * ∑ k, S a k + 2 * ρ ^ 2 * (S a a + S a b) +
        (if a = b then 2 * ρ ^ 2 * ∑ k, S a k + 8 * S a b else 0) := by
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        split_ifs with h
        · subst h
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
            ← Finset.sum_mul]
          ring
        · simp only [Finset.sum_const_zero, ← Finset.sum_mul]
          ring
    _ ≤ 2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + (if a = b then 2 * ρ ^ 2 + 8 * s₀ else 0) := by
        rw [hS1 a]
        have h1 := hs a a
        have h2 := hs a b
        split_ifs <;> nlinarith

/-- Everywhere, `|Σ_k s_{αk} X_{k,αb}| ≤ 9 Λ³` for `|G_{xy}| ≤ Λ` and `1 ≤ Λ`. -/
private lemma norm_sum_xk_le (S : Matrix ι ι ℝ) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {z : ℂ} (hm : ‖msc z‖ ≤ 1) {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω : Sample ι)
    (hG : ∀ x y, ‖green (hmat ω) z x y‖ ≤ Λ) (a b : ι) :
    ‖∑ k, (S a k : ℂ) * xk z ω k a b‖ ≤ 9 * Λ ^ 3 := by
  have hd : ∀ x, ‖dlt z ω x‖ ≤ 2 * Λ := fun x =>
    (norm_sub_le _ _).trans (by linarith [hG x x])
  have hx : ∀ k, ‖xk z ω k a b‖ ≤ 9 * Λ ^ 3 := fun k => by
    have h1 := norm_mul3_le (hd k) (hd a) (hd b)
    have h2 := norm_mul3_le (hG k a) (hG b k) (hG a b)
    have := norm_add_le (dlt z ω k * dlt z ω a * dlt z ω b)
      (green (hmat ω) z k a * green (hmat ω) z b k * green (hmat ω) z a b)
    simp only [xk]
    nlinarith
  refine (norm_wsum_le S hS0 a _).trans ?_
  calc ∑ k, S a k * ‖xk z ω k a b‖ ≤ ∑ k, S a k * (9 * Λ ^ 3) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (hS0 a k)
    _ = 9 * Λ ^ 3 := by rw [← Finset.sum_mul, hS1 a, one_mul]

/-- The bound at a fixed variance matrix `S ≥ 0` (symmetric, row sums `1`, `s_{xy} ≤ s₀`) and
`z` with `0 < Im z ≤ 1`, for `|S^+_{xy}| ≤ r₀`, `Σ_y |S^+_{xy}| ≤ r₁` and a set `Bad` off which
`|G_{xy} − m δ_{xy}| ≤ ρ ≤ 1`:
`|E G_{bb} − m| ≤ (1 + r₁)((1 + r₁)(2ρ³ + 4ρ² s₀ + 9 η⁻³ P(Bad)) + (s₀ + r₀)(2ρ² + 8 s₀))`. -/
private theorem fixed_bound (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y)
    (hS1 : ∀ x, ∑ y, S x y = 1) {s₀ : ℝ} (hs : ∀ x y, S x y ≤ s₀) {z : ℂ} (hz : 0 < z.im)
    (hz1 : z.im ≤ 1) {r₀ r₁ : ℝ} (hr₁ : 0 ≤ r₁)
    (hR0 : ∀ x y, ‖Splus (msc z) S x y‖ ≤ r₀) (hR1 : ∀ x, ∑ y, ‖Splus (msc z) S x y‖ ≤ r₁)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Bad : Set (Sample ι))
    (hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ ρ) (b : ι) :
    ‖∫ ω, green (hmat ω) z b b ∂(gaussLaw S) - msc z‖ ≤
      (1 + r₁) * ((1 + r₁) * (2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ +
        9 * z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal) + (s₀ + r₀) * (2 * ρ ^ 2 + 8 * s₀)) := by
  have hz0 : z.im ≠ 0 := hz.ne'
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have := isProbabilityMeasure_gaussLaw S
  have hR := one_add_mul_one_sub S (msc z) (isUnit_one_sub S hS0 hS1 hm1)
  set Λ := z.im⁻¹ with hΛdef
  have hΛ : 1 ≤ Λ := one_le_inv_iff₀.mpr ⟨hz, hz1⟩
  have hG : ∀ (ω : Sample ι) x y, ‖green (hmat ω) z x y‖ ≤ Λ := fun ω x y => by
    have := norm_green_entry_le (hmat_isHermitian ω) hz0 x y
    rwa [abs_of_pos hz] at this
  have hs0 : 0 ≤ s₀ := (hS0 b b).trans (hs b b)
  set β₁ := 2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + 9 * Λ ^ 3 * (gaussLaw S Bad).toReal with hβ₁
  set β₂ := 2 * ρ ^ 2 + 8 * s₀ with hβ₂
  have hF : ∀ a c, ‖fv S z a c‖ ≤ β₁ + if a = c then β₂ else 0 := by
    intro a c
    have h := norm_integral_le_good (gaussLaw S) (fun ω => ∑ k, (S a k : ℂ) * xk z ω k a c) Bad
      (2 * ρ ^ 3 + 4 * ρ ^ 2 * s₀ + (if a = c then 2 * ρ ^ 2 + 8 * s₀ else 0)) (9 * Λ ^ 3)
      (by split_ifs <;> positivity)
      (fun ω => norm_sum_xk_le S hS0 hS1 hm1.le hΛ ω (hG ω) a c)
      (fun ω hω => norm_sum_xk_good S hS0 hS1 hs hm1.le hρ0 hρ1 ω (hgood ω hω) a c)
    refine h.trans (le_of_eq ?_)
    rw [hβ₁, hβ₂]
    ring
  have hchain := chain S hS0 hS1 (msc z) hm1.le (Splus (msc z) S) hR
    (fun x => ∫ ω, dlt z ω x ∂(gaussLaw S)) (fun k x => ∫ ω, dlt z ω k * dlt z ω x ∂(gaussLaw S))
    (fv S z) (fun x => step1 S hS hS0 hS1 hz0 x) (fun a c => step2 S hS hS0 hS1 hz0 a c)
    β₁ β₂ r₀ r₁ s₀ (by positivity) (by positivity) hr₁ hF hR0 hR1 (fun x => hs x x) b
  have he : ∫ ω, dlt z ω b ∂(gaussLaw S) = ∫ ω, green (hmat ω) z b b ∂(gaussLaw S) - msc z := by
    simp only [dlt]
    rw [integral_sub (integ S (tf_G hz0 b b)) (integrable_const _), integral_const]
    simp
  rw [← he]
  exact hchain

end Fixed

/-! ## The propagator `S^+` on `Z_L^d` -/

section Lattice

/-- `splusBound W τ D x y ≤ 2 W^{−d}` for `W ≥ 1` and `D ≥ d`. -/
private lemma splusBound_le_two {d L : ℕ} [NeZero L] {W : ℕ} (hW : 1 ≤ W) (τs D : ℝ)
    (hD : (d : ℝ) ≤ D) (x y : Zd d L) :
    splusBound W τs D x y ≤ 2 * (W : ℝ) ^ (-(d : ℝ)) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWd : ((W : ℝ) ^ d)⁻¹ = (W : ℝ) ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
  have ht : (W : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + W := by
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]
  have h2 : ((zdistInf d L (x - y) : ℝ) + W) ^ (-D) ≤ (W : ℝ) ^ (-(d : ℝ)) :=
    calc ((zdistInf d L (x - y) : ℝ) + W) ^ (-D) ≤ (W : ℝ) ^ (-D) :=
          Real.rpow_le_rpow_of_nonpos hW0 ht (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
      _ ≤ (W : ℝ) ^ (-(d : ℝ)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have h1 : (if (zdistInf d L (x - y) : ℝ) ≤ (W : ℝ) ^ (1 + τs) then ((W : ℝ) ^ d)⁻¹ else 0) ≤
      (W : ℝ) ^ (-(d : ℝ)) := by
    split_ifs
    · rw [hWd]
    · positivity
  unfold splusBound
  linarith

/-- The row sums of `splusBound` at `D = 2d − 4`: `Σ_y splusBound W τ (2d − 4) x y ≤ C W^{τ(2d−4)}`
for `d ≥ 8`, `W ≥ 1`, `τ ≥ 0`, from `Σ_y B_{xy}² ≤ C W^{−d}` ([II, (8.33)]). -/
private lemma splusBound_rowSum (d : ℕ) (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ τs : ℝ, 0 ≤ τs → ∀ x : Zd d L,
      ∑ y, splusBound W τs (2 * (d : ℝ) - 4) x y ≤ C * (W : ℝ) ^ (τs * (2 * (d : ℝ) - 4)) := by
  obtain ⟨CB, hCB⟩ := bSum.2 d (by omega)
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set D : ℝ := 2 * (d : ℝ) - 4 with hD
  refine ⟨|CB| * (2 ^ D + 1), by positivity, fun L W _ hW τs hτs x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  -- each term against `⟨x − y⟩^{−D}`
  have hterm : ∀ y, splusBound W τs D x y ≤
      (2 ^ D * (W : ℝ) ^ ((1 + τs) * D - d) + 1) * brk d L W x y ^ (-D) := by
    intro y
    have ht0 : (W : ℝ) ≤ brk d L W x y := le_brk₁ x y
    have htp : 0 < brk d L W x y := lt_of_lt_of_le hW0 ht0
    have hsb : splusBound W τs D x y =
        (if (zdistInf d L (x - y) : ℝ) ≤ (W : ℝ) ^ (1 + τs) then ((W : ℝ) ^ d)⁻¹ else 0) +
          brk d L W x y ^ (-D) := rfl
    rw [hsb, add_mul, one_mul]
    refine add_le_add ?_ le_rfl
    split_ifs with hr
    · have hWτ : (W : ℝ) ≤ (W : ℝ) ^ (1 + τs) := by
        calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      have ht2 : brk d L W x y ≤ 2 * (W : ℝ) ^ (1 + τs) := by
        unfold brk; linarith
      have hpow : brk d L W x y ^ D ≤ 2 ^ D * (W : ℝ) ^ ((1 + τs) * D) := by
        calc brk d L W x y ^ D ≤ (2 * (W : ℝ) ^ (1 + τs)) ^ D :=
              Real.rpow_le_rpow htp.le ht2 (by linarith)
          _ = 2 ^ D * (W : ℝ) ^ ((1 + τs) * D) := by
              rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le]
      have e1 : ((W : ℝ) ^ d)⁻¹ = (W : ℝ) ^ ((1 + τs) * D - d) *
          (W : ℝ) ^ (-((1 + τs) * D)) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_neg hW0.le]
        ring_nf
      have e2 : brk d L W x y ^ (-D) = (brk d L W x y ^ D)⁻¹ := Real.rpow_neg htp.le D
      rw [e1, e2, mul_comm (2 ^ D) _, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [Real.rpow_neg hW0.le, le_mul_inv_iff₀ (by positivity), mul_comm]
      rw [mul_inv_le_iff₀ (by positivity)]
      exact hpow
    · positivity
  -- `Σ_y ⟨x − y⟩^{−D} = W⁴ Σ_y B_{xy} B_{yx} ≤ |C| W^{−(d−4)}`
  have hBB : ∀ y, brk d L W x y ^ (-D) = (W : ℝ) ^ (4 : ℝ) * (bB d L W x y * bB d L W y x) := by
    intro y
    have htp : 0 < brk d L W x y := lt_of_lt_of_le hW0 (le_brk₁ x y)
    rw [← bB_comm' x y]
    have hb : bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (2 - (d : ℝ)) := rfl
    rw [hb]
    calc brk d L W x y ^ (-D) = ((W : ℝ) ^ (4 : ℝ) * (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ)) *
          (brk d L W x y ^ (2 - (d : ℝ)) * brk d L W x y ^ (2 - (d : ℝ))) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add htp]
          norm_num
          rw [hD]; ring_nf
      _ = _ := by ring
  have hxx : brk d L W x x = W := by
    unfold brk
    rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl, Nat.cast_zero, zero_add]
  have hsumt : ∑ y, brk d L W x y ^ (-D) ≤ |CB| * (W : ℝ) ^ (-((d : ℝ) - 4)) := by
    simp_rw [hBB]
    rw [← Finset.mul_sum]
    have h := hCB L W hW x x
    rw [hxx] at h
    calc (W : ℝ) ^ (4 : ℝ) * ∑ y, bB d L W x y * bB d L W y x
        ≤ (W : ℝ) ^ (4 : ℝ) * (CB * (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = CB * (W : ℝ) ^ (-((d : ℝ) - 4)) := by
          rw [show (W : ℝ) ^ (4 : ℝ) * (CB * (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4))) =
            CB * ((W : ℝ) ^ (4 : ℝ) * (W : ℝ) ^ (-4 : ℝ)) * (W : ℝ) ^ (-((d : ℝ) - 4)) by ring,
            ← Real.rpow_add hW0]
          norm_num
      _ ≤ |CB| * (W : ℝ) ^ (-((d : ℝ) - 4)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hτD : 1 ≤ (W : ℝ) ^ (τs * D) := Real.one_le_rpow hW1 (by rw [hD]; nlinarith)
  have hsmall : (W : ℝ) ^ (-((d : ℝ) - 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hcomb : (W : ℝ) ^ ((1 + τs) * D - d) * (W : ℝ) ^ (-((d : ℝ) - 4)) = (W : ℝ) ^ (τs * D) := by
    rw [← Real.rpow_add hW0, hD]; ring_nf
  calc ∑ y, splusBound W τs D x y
      ≤ ∑ y, (2 ^ D * (W : ℝ) ^ ((1 + τs) * D - d) + 1) * brk d L W x y ^ (-D) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = (2 ^ D * (W : ℝ) ^ ((1 + τs) * D - d) + 1) * ∑ y, brk d L W x y ^ (-D) := by
        rw [Finset.mul_sum]
    _ ≤ (2 ^ D * (W : ℝ) ^ ((1 + τs) * D - d) + 1) * (|CB| * (W : ℝ) ^ (-((d : ℝ) - 4))) :=
        mul_le_mul_of_nonneg_left hsumt (by positivity)
    _ = |CB| * (2 ^ D * (W : ℝ) ^ (τs * D) + (W : ℝ) ^ (-((d : ℝ) - 4))) := by
        rw [← hcomb]; ring
    _ ≤ |CB| * (2 ^ D * (W : ℝ) ^ (τs * D) + (W : ℝ) ^ (τs * D)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (hsmall.trans hτD)) (abs_nonneg _)
    _ = |CB| * (2 ^ D + 1) * (W : ℝ) ^ (τs * D) := by ring

end Lattice

/-! ## The exponent count -/

/-- The bound at fixed `(W, L)` in the variables `w = W^{τ/8} ≥ 1` and `q = W^{−d/2} ≤ 1`, with
`ρ = wq`, `s₀ = C_s q²`, `r₀ = 2K q²`, `r₁ = K_r w` and `μ' = η⁻³ P(Bad)`: it is at most
`w⁸ q³ = W^τ W^{−3d/2}` once `w³` exceeds a constant and `μ'` is small against `q³`. -/
private lemma final_ineq (w q Kr Cs K μ' : ℝ) (hw : 1 ≤ w) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hKr : 0 ≤ Kr) (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hμ : 0 ≤ μ')
    (h1 : 2 * ((1 + Kr) * ((1 + Kr) * (2 + 4 * Cs) + (Cs + 2 * K) * (2 + 8 * Cs))) ≤ w ^ 3)
    (h2 : 2 * (9 * (1 + Kr) ^ 2) * μ' ≤ q ^ 3) :
    (1 + Kr * w) * ((1 + Kr * w) * (2 * (w * q) ^ 3 + 4 * (w * q) ^ 2 * (Cs * q ^ 2) + 9 * μ') +
      (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2))) ≤ w ^ 8 * q ^ 3 := by
  set A := 1 + Kr with hA
  have hA1 : 1 ≤ A := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hq3 : 0 ≤ q ^ 3 := by positivity
  have hw23 : w ^ 2 ≤ w ^ 3 := pow_le_pow_right₀ hw (by norm_num)
  have hw35 : w ^ 3 ≤ w ^ 5 := pow_le_pow_right₀ hw (by norm_num)
  have hw28 : w ^ 2 ≤ w ^ 8 := pow_le_pow_right₀ hw (by norm_num)
  have hq43 : q ^ 4 ≤ q ^ 3 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have ha : 1 + Kr * w ≤ A * w := by rw [hA]; nlinarith
  have ha0 : 0 ≤ 1 + Kr * w := by positivity
  have hT1 : 2 * (w * q) ^ 3 + 4 * (w * q) ^ 2 * (Cs * q ^ 2) + 9 * μ' ≤
      (2 + 4 * Cs) * w ^ 3 * q ^ 3 + 9 * μ' := by
    have : Cs * (w ^ 2 * q ^ 4) ≤ Cs * (w ^ 3 * q ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hw23 hq43 (by positivity) (by positivity)) hCs
    nlinarith
  have hT2 : (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2)) ≤
      (Cs + 2 * K) * (2 + 8 * Cs) * w ^ 2 * q ^ 3 := by
    have e : (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2)) =
        (Cs + 2 * K) * (2 * w ^ 2 + 8 * Cs) * q ^ 4 := by ring
    have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
    have h8 : 2 * w ^ 2 + 8 * Cs ≤ (2 + 8 * Cs) * w ^ 2 := by nlinarith
    rw [e]
    calc (Cs + 2 * K) * (2 * w ^ 2 + 8 * Cs) * q ^ 4
        ≤ (Cs + 2 * K) * ((2 + 8 * Cs) * w ^ 2) * q ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h8 (by positivity)) hq43 (by positivity)
            (by positivity)
      _ = _ := by ring
  have hT1' : 0 ≤ 2 * (w * q) ^ 3 + 4 * (w * q) ^ 2 * (Cs * q ^ 2) + 9 * μ' := by positivity
  have hT2' : 0 ≤ (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2)) := by
    positivity
  calc (1 + Kr * w) * ((1 + Kr * w) * (2 * (w * q) ^ 3 + 4 * (w * q) ^ 2 * (Cs * q ^ 2) + 9 * μ') +
        (Cs * q ^ 2 + 2 * K * q ^ 2) * (2 * (w * q) ^ 2 + 8 * (Cs * q ^ 2)))
      ≤ (A * w) * ((A * w) * ((2 + 4 * Cs) * w ^ 3 * q ^ 3 + 9 * μ') +
        (Cs + 2 * K) * (2 + 8 * Cs) * w ^ 2 * q ^ 3) := by
        gcongr
    _ = A ^ 2 * (2 + 4 * Cs) * w ^ 5 * q ^ 3 + A * (Cs + 2 * K) * (2 + 8 * Cs) * w ^ 3 * q ^ 3 +
        9 * A ^ 2 * w ^ 2 * μ' := by ring
    _ ≤ A ^ 2 * (2 + 4 * Cs) * w ^ 5 * q ^ 3 + A * (Cs + 2 * K) * (2 + 8 * Cs) * w ^ 5 * q ^ 3 +
        9 * A ^ 2 * w ^ 2 * μ' := by
        gcongr
    _ = (A * (A * (2 + 4 * Cs) + (Cs + 2 * K) * (2 + 8 * Cs))) * w ^ 5 * q ^ 3 +
        w ^ 2 * (9 * A ^ 2 * μ') := by ring
    _ ≤ (w ^ 3 / 2) * w ^ 5 * q ^ 3 + w ^ 8 * (q ^ 3 / 2) := by
        gcongr
        · linarith
        · linarith
    _ = w ^ 8 * q ^ 3 := by ring

end DiagMean

/-! ## The statement -/

open DiagMean in
/-- **The diagonal term of [I, (8.16)]**, `diagMeanStmt`: from the local law [I, (1.19)], for
`d ≥ 8`, a profile and `c₀, c₁, κ, ε, τ > 0` there is `L₀` such that
`|E G_{bb}(z) − m(z)| ≤ W^τ W^{−3d/2}` for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)` and
every `b ∈ Z_L^d`. -/
theorem diagMean : diagMeanStmt := by
  intro hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε τ hτ
  -- `W ≥ 1` on the window
  have hW1of : ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → (1 : ℝ) ≤ W := by
    intro W L _ hadm
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact (Real.one_le_rpow hL1 hc₁.le).trans hadm.1
  -- it suffices to take `τ ≤ 1`
  suffices key : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L →
      (W, L) ∈ adm c₀ c₁ → ∀ z ∈ specDom κ ε W L, ∀ b : Zd d L,
        ‖expC d P W L (fun ω => green (hmat ω) z b b) - msc z‖ ≤
          (W : ℝ) ^ τ * (W : ℝ) ^ (-(3 * (d : ℝ) / 2)) by
    obtain ⟨L₀, hL₀⟩ := key (min τ 1) (lt_min hτ one_pos) (min_le_right _ _)
    refine ⟨L₀, fun W L _ hL hadm z hz b => (hL₀ W L hL hadm z hz b).trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (hW1of W L hadm) (min_le_left _ _)) (by positivity)
  intro τ hτ hτ1
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set D : ℝ := 2 * (d : ℝ) - 4 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set τs : ℝ := τ / (8 * D) with hτsdef
  have hτs : 0 < τs := by positivity
  have hτsD : τs * D = τ / 8 := by rw [hτsdef]; field_simp
  set Dll : ℝ := 4 * (d : ℝ) + 7 with hDll
  -- the inputs
  obtain ⟨W₁, hsym⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  obtain ⟨Cs, hCs⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨Csym, hCsym⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨W₃, hker⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨K, W₄, hK⟩ := Splus_decay_msc d c₀ c₁ hc₀ hc₁ P.ψ c' hc' Csym κ τs D hκ hτs hD0
  obtain ⟨CR, hCR0, hCR⟩ := splusBound_rowSum d hd
  obtain ⟨L₁, hL₁⟩ := hLL d hd P c₀ c₁ κ hc₀ hc₁ hκ ε (τ / 4) Dll hε (by positivity)
    (by rw [hDll]; positivity)
  -- the constants
  set Cs' := |Cs| with hCs'
  set K' := |K| with hK'
  set Kr := K' * CR with hKr
  set K₁ := (1 + Kr) * ((1 + Kr) * (2 + 4 * Cs') + (Cs' + 2 * K') * (2 + 8 * Cs')) with hK₁
  set K₂ := 9 * (1 + Kr) ^ 2 with hK₂
  have hKr0 : 0 ≤ Kr := by positivity
  have hK₁0 : 0 ≤ K₁ := by positivity
  set W₀ : ℝ := max (max W₁ W₂) (max (max W₃ W₄) (max 1 ((2 * K₁) ^ (8 / (3 * τ))))) with hW₀
  have hW₀1 : 1 ≤ W₀ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨max L₁ (max ⌈W₀ ^ (1 / c₁)⌉₊ ⌈2 * K₂ + 1⌉₊), ?_⟩
  intro W L _ hL hadm z hz b
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hW1 : (1 : ℝ) ≤ W := hW1of W L hadm
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hLL₁ : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hWW₀ : W₀ ≤ W := by
    have h1 : W₀ ^ (1 / c₁) ≤ (L : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) (le_trans
        (le_max_right _ _) hL))
    have h2 : W₀ = (W₀ ^ (1 / c₁)) ^ c₁ := by
      rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hc₁.ne', Real.rpow_one]
    calc W₀ = (W₀ ^ (1 / c₁)) ^ c₁ := h2
      _ ≤ (L : ℝ) ^ c₁ := Real.rpow_le_rpow (by positivity) h1 hc₁.le
      _ ≤ W := hadm.1
  have hWi : ∀ i, i ≤ W₀ → i ≤ (W : ℝ) := fun i hi => hi.trans hWW₀
  have hW₁ : W₁ ≤ (W : ℝ) := hWi _ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hW₂ : W₂ ≤ (W : ℝ) := hWi _ (le_trans (le_max_right _ _) (le_max_left _ _))
  have hW₃ : W₃ ≤ (W : ℝ) := hWi _ (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_right _ _)))
  have hW₄ : W₄ ≤ (W : ℝ) := hWi _ (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_right _ _)))
  have hWK : (2 * K₁) ^ (8 / (3 * τ)) ≤ (W : ℝ) := hWi _ (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hWL : (W : ℝ) ≤ L := hadm.2.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : 1 - c₀ ≤ 1))
  -- the spectral parameter
  have hzim : 0 < z.im := lt_of_lt_of_le (by positivity) hz.2.1
  have hz1 : z.im ≤ 1 := hz.2.2
  have hzre : |z.re| < 2 - κ := hz.1
  -- the variance matrix
  set S := Smat P.ψ W L with hSdef
  obtain ⟨hSs, hS0⟩ := hsym W L hadm hW₁
  have hS1 : ∀ x, ∑ y, S x y = 1 := fun x => sum_row_of_mem_doublyStochastic (hds W L hadm hW₂) x
  -- the scales `w = W^{τ/8}` and `q = W^{−d/2}`
  set w : ℝ := (W : ℝ) ^ (τ / 8) with hw
  set q : ℝ := (W : ℝ) ^ (-((d : ℝ) / 2)) with hq
  have hw1 : 1 ≤ w := Real.one_le_rpow hW1 (by positivity)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hq2 : q ^ 2 = (W : ℝ) ^ (-(d : ℝ)) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hw2 : w ^ 2 = (W : ℝ) ^ (τ / 4) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
  have hwq : w ^ 8 * q ^ 3 = (W : ℝ) ^ τ * (W : ℝ) ^ (-(3 * (d : ℝ) / 2)) := by
    rw [hw, hq, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hW0.le]
    ring_nf
  have hρ1 : w * q ≤ 1 := by
    rw [hw, hq, ← Real.rpow_add hW0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  -- `s_{xy} ≤ |C_s| W^{−d}`
  have hs : ∀ x y, S x y ≤ Cs' * q ^ 2 := by
    intro x y
    have h := hCs W L hadm (x - y)
    rw [pow_zero, one_mul] at h
    have e : S x y = fWL P.ψ W L (x - y) := rfl
    rw [e, hq2, Real.rpow_neg hW0.le, Real.rpow_natCast, ← div_eq_mul_inv]
    exact (le_abs_self _).trans (h.trans (div_le_div_of_nonneg_right (le_abs_self _)
      (by positivity)))
  -- `S^+`
  have hSp : ∀ x y, ‖Splus (msc z) S x y‖ ≤ K' * splusBound W τs D x y := fun x y =>
    ((hK W L hadm hW₄ S (hker W L hadm hW₃) (hCsym W L hadm) z hzim hzre x y).1).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by unfold splusBound; positivity))
  have hR0 : ∀ x y, ‖Splus (msc z) S x y‖ ≤ 2 * K' * q ^ 2 := fun x y => by
    refine (hSp x y).trans ?_
    have h := mul_le_mul_of_nonneg_left (splusBound_le_two (L := L) hWn τs D
      (by rw [hD]; linarith) x y) (abs_nonneg K)
    rw [hq2]
    linarith
  have hR1 : ∀ x, ∑ y, ‖Splus (msc z) S x y‖ ≤ Kr * w := fun x => by
    calc ∑ y, ‖Splus (msc z) S x y‖ ≤ ∑ y, K' * splusBound W τs D x y :=
          Finset.sum_le_sum fun y _ => hSp x y
      _ = K' * ∑ y, splusBound W τs D x y := by rw [Finset.mul_sum]
      _ ≤ K' * (CR * (W : ℝ) ^ (τs * D)) :=
          mul_le_mul_of_nonneg_left (hCR L W hWn τs hτs.le x) (abs_nonneg _)
      _ = Kr * w := by rw [hτsD, hKr, hw]; ring
  -- the event of the local law
  set bad : Zd d L → Zd d L → Set (Sample (Zd d L)) := fun x y => {ω | ∃ E : ℝ,
    E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ, (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
      (W : ℝ) ^ (τ / 4) * bB d L W x y <
        ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I)) (msc ((E : ℂ) + (η : ℂ) * I)) x y‖ ^ 2}
    with hbad
  have hbadμ : ∀ x y, gaussLaw S (bad x y) ≤ ENNReal.ofReal ((L : ℝ) ^ (-Dll)) :=
    fun x y => hL₁ ⟨(W, L), NeZero.ne L⟩ hLL₁ hadm x y
  set Bad := ⋃ x, ⋃ y, bad x y with hBad
  have hgood : ∀ ω, ω ∉ Bad → ∀ x y, ‖entryErr (green (hmat ω) z) (msc z) x y‖ ≤ w * q := by
    intro ω hω x y
    have hxy : ω ∉ bad x y := fun h => hω (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, h⟩⟩)
    have hle : ‖entryErr (green (hmat ω) z) (msc z) x y‖ ^ 2 ≤
        (W : ℝ) ^ (τ / 4) * bB d L W x y := by
      by_contra hlt
      push Not at hlt
      refine hxy ⟨z.re, ⟨by linarith [neg_abs_le z.re], by linarith [le_abs_self z.re]⟩, z.im,
        hz.2.1, hz1, ?_⟩
      rwa [Complex.re_add_im]
    have hB : (W : ℝ) ^ (τ / 4) * bB d L W x y ≤ (w * q) ^ 2 := by
      rw [mul_pow, hw2, hq2]
      exact mul_le_mul_of_nonneg_left (bB_le_rpow (by omega) hWn x y) (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (hle.trans hB)
  -- `P(Bad) ≤ L^{2d} L^{−D}`
  have hμ : (gaussLaw S Bad).toReal ≤
      (L : ℝ) ^ (d : ℝ) * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ (-Dll)) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc gaussLaw S Bad ≤ ∑ x, gaussLaw S (⋃ y, bad x y) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ x : Zd d L, ∑ y : Zd d L, ENNReal.ofReal ((L : ℝ) ^ (-Dll)) :=
          Finset.sum_le_sum fun x _ => (measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun y _ => hbadμ x y)
      _ = ENNReal.ofReal ((L : ℝ) ^ (d : ℝ) * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ (-Dll))) := by
          simp only [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            Real.rpow_natCast, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  -- `η⁻¹ ≤ L²`
  have hΛ : z.im⁻¹ ≤ (L : ℝ) ^ (2 : ℝ) := by
    have h1 : (L : ℝ) ^ (-(2 - ε)) ≤ z.im := by
      calc (L : ℝ) ^ (-(2 - ε)) = 1 / (L : ℝ) ^ (2 - ε) := by rw [Real.rpow_neg hLpos.le, one_div]
        _ ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) :=
            div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ ≤ z.im := hz.2.1
    calc z.im⁻¹ ≤ ((L : ℝ) ^ (-(2 - ε)))⁻¹ := inv_anti₀ (by positivity) h1
      _ = (L : ℝ) ^ (2 - ε) := by rw [Real.rpow_neg hLpos.le, inv_inv]
      _ ≤ (L : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  set μ' := z.im⁻¹ ^ 3 * (gaussLaw S Bad).toReal with hμ'
  have hμ'0 : 0 ≤ μ' := by positivity
  have hμ'le : μ' ≤ (L : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (-(2 * (d : ℝ))) := by
    calc μ' ≤ ((L : ℝ) ^ (2 : ℝ)) ^ 3 *
          ((L : ℝ) ^ (d : ℝ) * ((L : ℝ) ^ (d : ℝ) * (L : ℝ) ^ (-Dll))) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hΛ 3) hμ ENNReal.toReal_nonneg
            (by positivity)
      _ = (L : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (-(2 * (d : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le, ← Real.rpow_add hLpos,
            ← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos, hDll]
          ring_nf
  have h2 : 2 * K₂ * μ' ≤ q ^ 3 := by
    have hLK : 2 * K₂ + 1 ≤ (L : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) (le_trans
        (le_max_right _ _) hL))
    have hinv : 2 * K₂ * (L : ℝ) ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_one hLpos]
      linarith
    have hq3 : (L : ℝ) ^ (-(2 * (d : ℝ))) ≤ q ^ 3 := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      calc (L : ℝ) ^ (-(2 * (d : ℝ))) ≤ (L : ℝ) ^ (-((d : ℝ) / 2) * ((3 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
        _ ≤ (W : ℝ) ^ (-((d : ℝ) / 2) * ((3 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hW0 hWL (by push_cast; linarith)
    have hK₂0 : 0 ≤ K₂ := by positivity
    calc 2 * K₂ * μ' ≤ 2 * K₂ * ((L : ℝ) ^ (-1 : ℝ) * (L : ℝ) ^ (-(2 * (d : ℝ)))) :=
          mul_le_mul_of_nonneg_left hμ'le (by positivity)
      _ = (2 * K₂ * (L : ℝ) ^ (-1 : ℝ)) * (L : ℝ) ^ (-(2 * (d : ℝ))) := by ring
      _ ≤ 1 * (L : ℝ) ^ (-(2 * (d : ℝ))) := mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ q ^ 3 := by rw [one_mul]; exact hq3
  have h1 : 2 * K₁ ≤ w ^ 3 := by
    have e : w ^ 3 = (W : ℝ) ^ (3 * τ / 8) := by
      rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    rw [e]
    calc 2 * K₁ = ((2 * K₁) ^ (8 / (3 * τ))) ^ (3 * τ / 8) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show 8 / (3 * τ) * (3 * τ / 8) = (1 : ℝ) by field_simp, Real.rpow_one]
      _ ≤ (W : ℝ) ^ (3 * τ / 8) := Real.rpow_le_rpow (by positivity) hWK (by positivity)
  -- the bound at `(W, L, z)`
  have hfix := fixed_bound S hSs hS0 hS1 hs hzim hz1 (by positivity : 0 ≤ Kr * w) hR0 hR1
    (by positivity : 0 ≤ w * q) hρ1 Bad hgood b
  have hfin := final_ineq w q Kr Cs' K' μ' hw1 hq0 hq1 hKr0 (abs_nonneg _) (abs_nonneg _) hμ'0
    h1 h2
  rw [← hwq]
  refine (show ‖expC d P W L (fun ω => green (hmat ω) z b b) - msc z‖ =
    ‖∫ ω, green (hmat ω) z b b ∂(gaussLaw S) - msc z‖ from rfl).trans_le (hfix.trans ?_)
  refine le_of_eq_of_le ?_ hfin
  rw [hμ']
  ring

end RBM8D
