import RBM8D.Prob.Model
import RBM8D.Basic.Resolvent
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Wirtinger derivatives and test functions

The derivative ∂_{h_ab} along a matrix entry (h_ab and h_ba = conj h_ab treated as independent), the class of test functions, and the derivative of resolvent entries, ∂_{h_ab} G_xy = −G_xa G_by ([I, (3.8)]).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

universe u v w

namespace RBM8D

/-! ## Wirtinger derivatives and test functions -/

section Wirtinger

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The real partial derivative along the coordinate `c`. -/
def partialCoord (c : Coord ι) (F : Sample ι → ℂ) (ω : Sample ι) : ℂ :=
  deriv (fun t : ℝ => F (Function.update ω c t)) (ω c)

/-- The Wirtinger derivative `∂_{h_ab}`, with `h_ab` and `h_ba = conj h_ab` treated as
independent: `(∂_Re - i ∂_Im) / 2` if `h_ab = Re + i Im`, `(∂_Re + i ∂_Im) / 2` if
`h_ab = Re - i Im`, and the real derivative on the diagonal. -/
def dh (a b : ι) (F : Sample ι → ℂ) (ω : Sample ι) : ℂ :=
  if h : idxKey ι a < idxKey ι b then
    (1 / 2 : ℂ) * (partialCoord (.inr (⟨(a, b), h⟩, true)) F ω -
      I * partialCoord (.inr (⟨(a, b), h⟩, false)) F ω)
  else if h' : idxKey ι b < idxKey ι a then
    (1 / 2 : ℂ) * (partialCoord (.inr (⟨(b, a), h'⟩, true)) F ω +
      I * partialCoord (.inr (⟨(b, a), h'⟩, false)) F ω)
  else partialCoord (.inl a) F ω

/-- Test functions: smooth, with every iterated derivative bounded. -/
def TestFn (F : Sample ι → ℂ) : Prop :=
  ∀ n : ℕ, ContDiff ℝ n F ∧ ∃ C : ℝ, ∀ ω, ‖iteratedFDeriv ℝ n F ω‖ ≤ C

end Wirtinger

/-! ## Derivatives of the resolvent -/

section Resolvent

/-- Complex matrices with the `L^∞` operator norm, a normed algebra over `ℝ`; a type synonym
that carries the norm structure used for the derivative of the inverse. -/
private def Mat (ι : Type u) [Fintype ι] [DecidableEq ι] : Type u := Matrix ι ι ℂ

private instance {ι : Type u} [Fintype ι] [DecidableEq ι] : NormedRing (Mat ι) :=
  Matrix.linftyOpNormedRing

private instance {ι : Type u} [Fintype ι] [DecidableEq ι] : NormedAlgebra ℝ (Mat ι) :=
  Matrix.linftyOpNormedAlgebra

private instance {ι : Type u} [Fintype ι] [DecidableEq ι] : FiniteDimensional ℝ (Mat ι) :=
  inferInstanceAs (Module.Finite ℝ (Matrix ι ι ℂ))

private instance {ι : Type u} [Fintype ι] [DecidableEq ι] : CompleteSpace (Mat ι) :=
  FiniteDimensional.complete ℝ (Mat ι)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma hmat_add (ω η : Sample ι) : hmat (ω + η) = hmat ω + hmat η := by
  ext p q
  simp only [hmat, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp [Pi.add_apply] <;> ring

omit [DecidableEq ι] in
private lemma hmat_smul (r : ℝ) (ω : Sample ι) : hmat (r • ω) = (r : ℂ) • hmat ω := by
  ext p q
  simp only [hmat, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp [Pi.smul_apply] <;> ring

/-- `ω ↦ H(ω)` as a continuous real-linear map into `Mat ι`. -/
private def hmatCLM : Sample ι →L[ℝ] Mat ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ω => hmat ω
      map_add' := hmat_add
      map_smul' := fun r ω => by
        change hmat (r • ω) = ((r • hmat ω : Matrix ι ι ℂ))
        simpa using hmat_smul r ω }

/-- The entry `(x, y)` as a continuous real-linear map. -/
private def entryCLM (x y : ι) : Mat ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M : Matrix ι ι ℂ) x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The shift `z · 1` as an element of `Mat ι`. -/
private def zmat (z : ℂ) : Mat ι := z • (1 : Matrix ι ι ℂ)

/-- The Green function `G(z)` of `H(ω)` as an element of `Mat ι`. -/
private def greenMat (z : ℂ) (ω : Sample ι) : Mat ι := green (hmat ω) z

private lemma greenMat_eq_inverse (z : ℂ) (ω : Sample ι) :
    greenMat z ω = Ring.inverse (hmatCLM ω - zmat z) := by
  unfold greenMat green
  rw [Matrix.nonsing_inv_eq_ringInverse]
  rfl

private lemma isUnit_hmatCLM_sub {z : ℂ} (hz : z.im ≠ 0) (ω : Sample ι) :
    IsUnit (hmatCLM ω - zmat z) :=
  isUnit_sub_smul_of_isHermitian (hmat_isHermitian ω) hz

/-- The derivative of `ω ↦ (H(ω) - z)⁻¹` is `v ↦ -G H(v) G`. -/
private lemma hasFDerivAt_greenMat {z : ℂ} (hz : z.im ≠ 0) (ω : Sample ι) :
    HasFDerivAt (greenMat z)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Mat ι) (greenMat z ω) (greenMat z ω))).comp
        hmatCLM) ω := by
  have hu := isUnit_hmatCLM_sub hz ω
  have h1 : HasFDerivAt (fun ω' : Sample ι => hmatCLM ω' - zmat z) hmatCLM ω :=
    hmatCLM.hasFDerivAt.sub_const _
  have h2 := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have hinv := Ring.inverse_unit hu.unit
  rw [hu.unit_spec] at h2 hinv
  have h3 := h2.comp ω h1
  have hG : ((hu.unit⁻¹ : (Mat ι)ˣ) : Mat ι) = greenMat z ω := by
    rw [greenMat_eq_inverse]; exact hinv.symm
  rw [hG] at h3
  exact h3.congr_of_eventuallyEq (Eventually.of_forall fun ω' => greenMat_eq_inverse z ω')

private lemma contDiff_greenMat {z : ℂ} (hz : z.im ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (greenMat z : Sample ι → Mat ι) := by
  rw [contDiff_iff_contDiffAt]
  intro ω
  have hu := isUnit_hmatCLM_sub hz ω
  have h2 := contDiffAt_ringInverse ℝ (n := (⊤ : ℕ∞)) hu.unit
  rw [hu.unit_spec] at h2
  have h0 : ContDiff ℝ (⊤ : ℕ∞) fun ω' : Sample ι => hmatCLM ω' :=
    (hmatCLM (ι := ι)).contDiff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun ω' : Sample ι => hmatCLM ω' - zmat z :=
    h0.sub contDiff_const
  have h3 := h2.comp ω h1.contDiffAt
  exact h3.congr_of_eventuallyEq (Eventually.of_forall fun ω' => greenMat_eq_inverse z ω')

/-- The entries of the resolvent are `C^∞` functions of the sample. -/
private lemma contDiff_green_entry {z : ℂ} (hz : z.im ≠ 0) (x y : ι) :
    ContDiff ℝ (⊤ : ℕ∞) fun ω : Sample ι => green (hmat ω) z x y :=
  (entryCLM x y).contDiff.comp (contDiff_greenMat hz)

/-- The derivative of a resolvent entry in the direction `v` is `-(G H(v) G)_{xy}`. -/
private lemma fderiv_green_entry {z : ℂ} (hz : z.im ≠ 0) (x y : ι) (ω v : Sample ι) :
    fderiv ℝ (fun ω' : Sample ι => green (hmat ω') z x y) ω v =
      -(green (hmat ω) z * hmat v * green (hmat ω) z) x y := by
  have h := (entryCLM x y).hasFDerivAt.comp ω (hasFDerivAt_greenMat hz ω)
  have h' : HasFDerivAt (fun ω' : Sample ι => green (hmat ω') z x y) _ ω := h
  rw [h'.fderiv]
  rfl

end Resolvent

/-! ## The partial derivative along a coordinate -/

section Coordinate

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private lemma hasDerivAt_updateCoord (ω : Sample ι) (c : Coord ι) :
    HasDerivAt (fun t : ℝ => Function.update ω c t) (Pi.single c 1) (ω c) := by
  rw [hasDerivAt_pi]
  intro j
  by_cases h : j = c
  · subst h
    simpa using hasDerivAt_id' (ω j)
  · simpa [Function.update_of_ne h, Pi.single_eq_of_ne h] using hasDerivAt_const (ω c) (ω j)

/-- For a differentiable `F`, `∂_c F` is the Fréchet derivative in the direction of the `c`-th
unit vector. -/
private lemma partialCoord_eq {F : Sample ι → ℂ} {ω : Sample ι} (hF : DifferentiableAt ℝ F ω)
    (c : Coord ι) : partialCoord c F ω = fderiv ℝ F ω (Pi.single c 1) := by
  unfold partialCoord
  have h1 : HasFDerivAt F (fderiv ℝ F ω) (Function.update ω c (ω c)) := by
    rw [Function.update_eq_self]; exact hF.hasFDerivAt
  exact (h1.comp_hasDerivAt (ω c) (hasDerivAt_updateCoord ω c)).deriv

omit [DecidableEq ι] in
private lemma hmat_of_lt (ω : Sample ι) {p q : ι} (h : idxKey ι p < idxKey ι q) :
    hmat ω p q = (ω (.inr (⟨(p, q), h⟩, true)) : ℂ) + I * (ω (.inr (⟨(p, q), h⟩, false)) : ℂ) := by
  simp [hmat, h]

omit [DecidableEq ι] in
private lemma hmat_of_gt (ω : Sample ι) {p q : ι} (h : idxKey ι q < idxKey ι p) :
    hmat ω p q = (ω (.inr (⟨(q, p), h⟩, true)) : ℂ) - I * (ω (.inr (⟨(q, p), h⟩, false)) : ℂ) := by
  simp [hmat, h, lt_asymm h]

omit [DecidableEq ι] in
private lemma hmat_of_eq (ω : Sample ι) (p : ι) : hmat ω p p = (ω (.inl p) : ℂ) := by
  simp [hmat]

/-- `H` along the diagonal coordinate `a` is the matrix unit `E_aa`. -/
private lemma hmat_single_diag (a : ι) :
    hmat (Pi.single (Sum.inl a : Coord ι) (1 : ℝ)) = Matrix.single a a (1 : ℂ) := by
  ext p q
  rcases lt_trichotomy (idxKey ι p) (idxKey ι q) with h | h | h
  · rw [hmat_of_lt _ h]
    simp only [Matrix.single_apply, Pi.single_apply, reduceCtorEq, ite_false,
      Complex.ofReal_zero, mul_zero, add_zero]
    grind
  · obtain rfl := idxKey_injective h
    rw [hmat_of_eq]
    simp only [Matrix.single_apply, Pi.single_apply, Sum.inl.injEq, apply_ite ((↑) : ℝ → ℂ),
      Complex.ofReal_one, Complex.ofReal_zero]
    grind
  · rw [hmat_of_gt _ h]
    simp only [Matrix.single_apply, Pi.single_apply, reduceCtorEq, ite_false,
      Complex.ofReal_zero, mul_zero, sub_zero]
    grind

/-- `H` along `Re h_ab` is `E_ab + E_ba`. -/
private lemma hmat_single_re {a b : ι} (h : idxKey ι a < idxKey ι b) :
    hmat (Pi.single (Sum.inr (⟨(a, b), h⟩, true) : Coord ι) (1 : ℝ)) =
      Matrix.single a b (1 : ℂ) + Matrix.single b a (1 : ℂ) := by
  ext p q
  rcases lt_trichotomy (idxKey ι p) (idxKey ι q) with h' | h' | h'
  · rw [hmat_of_lt _ h']
    simp only [Matrix.single_apply, Pi.single_apply, Matrix.add_apply, Sum.inr.injEq,
      Prod.mk.injEq, Subtype.mk.injEq, apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one,
      Complex.ofReal_zero, Bool.false_eq_true, and_false, and_true, ite_false, mul_zero, add_zero]
    grind
  · obtain rfl := idxKey_injective h'
    rw [hmat_of_eq]
    simp only [Matrix.single_apply, Pi.single_apply, Matrix.add_apply, reduceCtorEq, ite_false,
      Complex.ofReal_zero]
    grind
  · rw [hmat_of_gt _ h']
    simp only [Matrix.single_apply, Pi.single_apply, Matrix.add_apply, Sum.inr.injEq,
      Prod.mk.injEq, Subtype.mk.injEq, apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one,
      Complex.ofReal_zero, Bool.false_eq_true, and_false, and_true, ite_false, mul_zero, sub_zero]
    grind

/-- `H` along `Im h_ab` is `i (E_ab - E_ba)`. -/
private lemma hmat_single_im {a b : ι} (h : idxKey ι a < idxKey ι b) :
    hmat (Pi.single (Sum.inr (⟨(a, b), h⟩, false) : Coord ι) (1 : ℝ)) =
      Matrix.single a b I - Matrix.single b a I := by
  ext p q
  rcases lt_trichotomy (idxKey ι p) (idxKey ι q) with h' | h' | h'
  · rw [hmat_of_lt _ h']
    simp only [Matrix.single_apply, Pi.single_apply, Matrix.sub_apply, Sum.inr.injEq,
      Prod.mk.injEq, Subtype.mk.injEq, apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one,
      Complex.ofReal_zero, Bool.true_eq_false, and_false, and_true, ite_false, zero_add]
    grind
  · obtain rfl := idxKey_injective h'
    rw [hmat_of_eq]
    simp only [Matrix.single_apply, Pi.single_apply, Matrix.sub_apply, reduceCtorEq, ite_false,
      Complex.ofReal_zero]
    grind
  · rw [hmat_of_gt _ h']
    simp only [Matrix.single_apply, Pi.single_apply, Matrix.sub_apply, Sum.inr.injEq,
      Prod.mk.injEq, Subtype.mk.injEq, apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one,
      Complex.ofReal_zero, Bool.true_eq_false, and_false, and_true, ite_false, zero_sub]
    grind

/-- The `(x, y)` entry of `G E_ab G`, scaled by `s`. -/
private lemma mul_single_mul_apply (G : Matrix ι ι ℂ) (a b x y : ι) (s : ℂ) :
    (G * Matrix.single a b s * G) x y = G x a * s * G b y := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul, mul_ite]

end Coordinate

/-! ## The derivative of resolvent entries -/

section Entries

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private lemma differentiable_green_entry {z : ℂ} (hz : z.im ≠ 0) (x y : ι) :
    Differentiable ℝ fun ω : Sample ι => green (hmat ω) z x y :=
  (contDiff_green_entry hz x y).differentiable (by simp)

/-- The real partial derivative of a resolvent entry along the coordinate `c`. -/
private lemma partialCoord_green {z : ℂ} (hz : z.im ≠ 0) (x y : ι) (c : Coord ι)
    (ω : Sample ι) :
    partialCoord c (fun ω' => green (hmat ω') z x y) ω =
      -(green (hmat ω) z * hmat (Pi.single c 1) * green (hmat ω) z) x y := by
  rw [partialCoord_eq (differentiable_green_entry hz x y ω), fderiv_green_entry hz]

end Entries

theorem dh_green :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (z : ℂ), z.im ≠ 0 → ∀ (a b x y : ι) (ω : Sample ι),
    dh a b (fun ω' => green (hmat ω') z x y) ω = -(green (hmat ω) z x a * green (hmat ω) z b y) := by
  intro ι _ _ z hz a b x y ω
  unfold dh
  split_ifs with h h'
  · rw [partialCoord_green hz, partialCoord_green hz, hmat_single_re, hmat_single_im]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_apply,
      Matrix.sub_apply, mul_single_mul_apply]
    linear_combination (1 / 2 * (green (hmat ω) z x a * green (hmat ω) z b y -
      green (hmat ω) z x b * green (hmat ω) z a y)) * Complex.I_sq
  · rw [partialCoord_green hz, partialCoord_green hz, hmat_single_re, hmat_single_im]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.add_apply,
      Matrix.sub_apply, mul_single_mul_apply]
    linear_combination (-(1 / 2) * (green (hmat ω) z x b * green (hmat ω) z a y -
      green (hmat ω) z x a * green (hmat ω) z b y)) * Complex.I_sq
  · obtain rfl : a = b := idxKey_injective (le_antisymm (not_lt.mp h') (not_lt.mp h))
    rw [partialCoord_green hz, hmat_single_diag]
    simp only [mul_single_mul_apply]
    ring

/-! ## Conjugation -/

section Conjugate

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma deriv_star_real (g : ℝ → ℂ) (t : ℝ) :
    deriv (fun s => star (g s)) t = star (deriv g t) := by
  by_cases hg : DifferentiableAt ℝ g t
  · have h := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hg.hasDerivAt
    exact h.deriv
  · have hs : ¬ DifferentiableAt ℝ (fun s => star (g s)) t := fun h => hg (by
      have h2 : DifferentiableAt ℝ (fun s => Complex.conjCLE (star (g s))) t :=
        Complex.conjCLE.differentiableAt.comp t h
      have h3 : (fun s => Complex.conjCLE (star (g s))) = g := by
        funext s; simp
      exact h3 ▸ h2)
    rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hs]
    simp

private lemma partialCoord_star (c : Coord ι) (F : Sample ι → ℂ) (ω : Sample ι) :
    partialCoord c (fun ω' => star (F ω')) ω = star (partialCoord c F ω) := by
  unfold partialCoord
  exact deriv_star_real _ _

/-- Conjugating a function swaps the two Wirtinger derivatives `∂_{h_ab}` and `∂_{h_ba}`. -/
private lemma dh_star (a b : ι) (F : Sample ι → ℂ) (ω : Sample ι) :
    dh a b (fun ω' => star (F ω')) ω = star (dh b a F ω) := by
  rcases lt_trichotomy (idxKey ι a) (idxKey ι b) with h | h | h
  · unfold dh
    simp only [h, lt_asymm h, dite_true, dite_false, partialCoord_star, star_mul', star_add]
    simp
    ring
  · obtain rfl := idxKey_injective h
    unfold dh
    simp only [lt_irrefl, dite_false, partialCoord_star]
  · unfold dh
    simp only [h, lt_asymm h, dite_true, dite_false, partialCoord_star, star_mul']
    simp

end Conjugate

/-! ## Test functions -/

section TestFunctions

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private lemma natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- Smooth, with the iterated derivatives of order at most `n` bounded by one constant. -/
private def Bd (n : ℕ) (F : Sample ι → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) F ∧ ∃ C : ℝ, ∀ k ≤ n, ∀ ω, ‖iteratedFDeriv ℝ k F ω‖ ≤ C

omit [DecidableEq ι] in
private lemma testFn_iff {F : Sample ι → ℂ} :
    TestFn F ↔ ContDiff ℝ (⊤ : ℕ∞) F ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ ω, ‖iteratedFDeriv ℝ n F ω‖ ≤ C :=
  ⟨fun h => ⟨contDiff_infty.mpr fun n => (h n).1, fun n => (h n).2⟩,
    fun h n => ⟨(contDiff_infty.mp h.1) n, h.2 n⟩⟩

omit [DecidableEq ι] in
private lemma testFn_iff_bd {F : Sample ι → ℂ} : TestFn F ↔ ∀ n, Bd n F := by
  rw [testFn_iff]
  constructor
  · rintro ⟨hs, hb⟩ n
    choose C hC using hb
    refine ⟨hs, ∑ i ∈ Finset.range (n + 1), |C i|, fun k hk ω => ?_⟩
    exact (hC k ω).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))))
  · intro h
    exact ⟨(h 0).1, fun n => by
      obtain ⟨C, hC⟩ := (h n).2
      exact ⟨C, hC n le_rfl⟩⟩

omit [DecidableEq ι] in
private lemma Bd.add {n : ℕ} {F G : Sample ι → ℂ} (hF : Bd n F) (hG : Bd n G) : Bd n (F + G) := by
  obtain ⟨hFs, C, hC⟩ := hF
  obtain ⟨hGs, D, hD⟩ := hG
  refine ⟨hFs.add hGs, C + D, fun k hk ω => ?_⟩
  rw [iteratedFDeriv_add_apply (hFs.contDiffAt.of_le (natCast_le_infty k))
    (hGs.contDiffAt.of_le (natCast_le_infty k))]
  exact (norm_add_le _ _).trans (add_le_add (hC k hk ω) (hD k hk ω))

omit [DecidableEq ι] in
private lemma Bd.mul {n : ℕ} {F G : Sample ι → ℂ} (hF : Bd n F) (hG : Bd n G) : Bd n (F * G) := by
  obtain ⟨hFs, C, hC⟩ := hF
  obtain ⟨hGs, D, hD⟩ := hG
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (Nat.zero_le _) 0)
  refine ⟨hFs.mul hGs, 2 ^ n * C * D, fun k hk ω => ?_⟩
  have h1 := norm_iteratedFDeriv_mul_le hFs hGs ω (natCast_le_infty k)
  refine (h1.trans ?_)
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i F ω‖ *
        ‖iteratedFDeriv ℝ (k - i) G ω‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C * D := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have := hC i (hi'.trans hk) ω
        have := hD (k - i) ((Nat.sub_le _ _).trans hk) ω
        gcongr
    _ = 2 ^ k * C * D := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose k
    _ ≤ 2 ^ n * C * D := by
        gcongr
        norm_num

omit [DecidableEq ι] in
private lemma testFn_const (c : ℂ) : TestFn fun _ : Sample ι => c := by
  rw [testFn_iff]
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun ω => ?_⟩⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [iteratedFDeriv_const_of_ne hn.ne']
    simp

omit [DecidableEq ι] in
private lemma testFn_add {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) : TestFn (F + G) :=
  testFn_iff_bd.mpr fun n => (testFn_iff_bd.mp hF n).add (testFn_iff_bd.mp hG n)

omit [DecidableEq ι] in
private lemma testFn_mul {F G : Sample ι → ℂ} (hF : TestFn F) (hG : TestFn G) : TestFn (F * G) :=
  testFn_iff_bd.mpr fun n => (testFn_iff_bd.mp hF n).mul (testFn_iff_bd.mp hG n)

omit [DecidableEq ι] in
private lemma testFn_const_mul (c : ℂ) {F : Sample ι → ℂ} (hF : TestFn F) :
    TestFn fun ω => c * F ω :=
  testFn_mul (testFn_const c) hF

omit [DecidableEq ι] in
private lemma testFn_star {F : Sample ι → ℂ} (hF : TestFn F) : TestFn fun ω => star (F ω) := by
  rw [testFn_iff] at hF ⊢
  obtain ⟨hs, hb⟩ := hF
  have hfun : (fun ω => star (F ω)) = Complex.conjLIE ∘ F := by
    funext ω; simp [Complex.conjLIE_apply]
  rw [hfun]
  refine ⟨Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp hs, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hb n
  exact ⟨C, fun ω => by rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]; exact hC ω⟩

omit [DecidableEq ι] in
/-- The directional derivative of a test function is a test function. -/
private lemma testFn_dirD {F : Sample ι → ℂ} (hF : TestFn F) (v : Sample ι) :
    TestFn fun ω => fderiv ℝ F ω v := by
  rw [testFn_iff] at hF ⊢
  obtain ⟨hs, hb⟩ := hF
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hs.fderiv_right (by simp)
  have hcomp : (fun ω => fderiv ℝ F ω v) = (ContinuousLinearMap.apply ℝ ℂ v) ∘ (fderiv ℝ F) :=
    rfl
  rw [hcomp]
  refine ⟨(ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp hd, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hb (n + 1)
  refine ⟨‖ContinuousLinearMap.apply ℝ ℂ v‖ * C, fun ω => ?_⟩
  calc ‖iteratedFDeriv ℝ n ((ContinuousLinearMap.apply ℝ ℂ v) ∘ (fderiv ℝ F)) ω‖
      ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ F) ω‖ :=
        (ContinuousLinearMap.apply ℝ ℂ v).norm_iteratedFDeriv_comp_left hd.contDiffAt
          (natCast_le_infty n)
    _ = ‖ContinuousLinearMap.apply ℝ ℂ v‖ * ‖iteratedFDeriv ℝ (n + 1) F ω‖ := by
        rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖ContinuousLinearMap.apply ℝ ℂ v‖ * C :=
        mul_le_mul_of_nonneg_left (hC ω) (ContinuousLinearMap.opNorm_nonneg _)

/-- `∂_{h_ab} F` is a complex-linear combination of two directional derivatives. -/
private lemma dh_eq_comb (a b : ι) {F : Sample ι → ℂ} (hF : Differentiable ℝ F) :
    ∃ (c₁ c₂ : ℂ) (v₁ v₂ : Sample ι),
      dh a b F = fun ω => c₁ * fderiv ℝ F ω v₁ + c₂ * fderiv ℝ F ω v₂ := by
  by_cases h : idxKey ι a < idxKey ι b
  · refine ⟨1 / 2, -(I / 2), Pi.single (Sum.inr (⟨(a, b), h⟩, true)) 1,
      Pi.single (Sum.inr (⟨(a, b), h⟩, false)) 1, ?_⟩
    funext ω
    simp only [dh, h, dite_true, partialCoord_eq (hF ω)]
    ring
  · by_cases h' : idxKey ι b < idxKey ι a
    · refine ⟨1 / 2, I / 2, Pi.single (Sum.inr (⟨(b, a), h'⟩, true)) 1,
        Pi.single (Sum.inr (⟨(b, a), h'⟩, false)) 1, ?_⟩
      funext ω
      simp only [dh, h, h', dite_true, dite_false, partialCoord_eq (hF ω)]
      ring
    · refine ⟨1, 0, Pi.single (Sum.inl a) 1, 0, ?_⟩
      funext ω
      simp only [dh, h, h', dite_false, partialCoord_eq (hF ω)]
      simp

private lemma testFn_dh (a b : ι) {F : Sample ι → ℂ} (hF : TestFn F) : TestFn (dh a b F) := by
  have hdiff : Differentiable ℝ F :=
    ((testFn_iff.mp hF).1).differentiable (by simp)
  obtain ⟨c₁, c₂, v₁, v₂, h⟩ := dh_eq_comb a b hdiff
  rw [h]
  exact testFn_add (testFn_const_mul c₁ (testFn_dirD hF v₁))
    (testFn_const_mul c₂ (testFn_dirD hF v₂))

omit [DecidableEq ι] in
private lemma testFn_bddMeas {F : Sample ι → ℂ} (hF : TestFn F) : BddMeas F := by
  refine ⟨(hF 0).1.continuous.measurable, ?_⟩
  obtain ⟨C, hC⟩ := (hF 0).2
  exact ⟨C, fun ω => by simpa [norm_iteratedFDeriv_zero] using hC ω⟩

end TestFunctions

/-! ## Iterated derivatives of resolvent entries -/

section GreenBounds

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The continuous real-linear map `w ↦ (v ↦ -w · H(v)_{pq})`. -/
private def entryDeriv (p : ι × ι) : ℂ →L[ℝ] (Sample ι →L[ℝ] ℂ) :=
  (-((ContinuousLinearMap.compL ℝ (Sample ι) ℂ ℂ).flip
    ((entryCLM p.1 p.2).comp hmatCLM))).comp (ContinuousLinearMap.mul ℝ ℂ)

private lemma entryDeriv_apply (p : ι × ι) (w : ℂ) (v : Sample ι) :
    entryDeriv p w v = -(w * hmat v p.1 p.2) := rfl

omit [DecidableEq ι] in
private lemma mul_mul_apply (G M : Matrix ι ι ℂ) (x y : ι) :
    (G * M * G) x y = ∑ p : ι × ι, G x p.1 * G p.2 y * M p.1 p.2 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The derivative of a resolvent entry is a sum of products of two resolvent entries, with
constant coefficients. -/
private lemma fderiv_green_entry_eq {z : ℂ} (hz : z.im ≠ 0) (x y : ι) :
    fderiv ℝ (fun ω : Sample ι => green (hmat ω) z x y) =
      fun ω => ∑ p : ι × ι,
        entryDeriv p (green (hmat ω) z x p.1 * green (hmat ω) z p.2 y) := by
  funext ω
  ext v
  rw [fderiv_green_entry hz, mul_mul_apply, sum_apply]
  simp only [entryDeriv_apply, Finset.sum_neg_distrib]

private lemma bd_green {z : ℂ} (hz : z.im ≠ 0) :
    ∀ (n : ℕ) (x y : ι), Bd n fun ω : Sample ι => green (hmat ω) z x y := by
  intro n
  induction n with
  | zero =>
    intro x y
    refine ⟨contDiff_green_entry hz x y, |z.im|⁻¹, fun k hk ω => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    rw [norm_iteratedFDeriv_zero]
    exact norm_green_entry_le (hmat_isHermitian ω) hz x y
  | succ n ih =>
    intro x y
    obtain ⟨hs, C, hC⟩ := ih x y
    have hQ : ∀ p : ι × ι, Bd n ((fun ω : Sample ι => green (hmat ω) z x p.1) *
        (fun ω : Sample ι => green (hmat ω) z p.2 y)) := fun p => (ih x p.1).mul (ih p.2 y)
    choose hQs CQ hCQ using hQ
    refine ⟨hs, max C (∑ p : ι × ι, ‖entryDeriv p‖ * CQ p), fun k hk ω => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact (hC k (Nat.lt_succ_iff.mp hlt) ω).trans (le_max_left _ _)
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      refine le_trans ?_ (le_max_right _ _)
      rw [← norm_iteratedFDeriv_fderiv, fderiv_green_entry_eq hz]
      rw [iteratedFDeriv_fun_sum_apply (f := fun (p : ι × ι) (ω : Sample ι) =>
        entryDeriv p (green (hmat ω) z x p.1 * green (hmat ω) z p.2 y)) (fun p _ =>
        ((entryDeriv p).contDiff.comp (hQs p)).contDiffAt.of_le (natCast_le_infty n))]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      exact ((entryDeriv p).norm_iteratedFDeriv_comp_left (hQs p).contDiffAt
        (natCast_le_infty n)).trans
        (mul_le_mul_of_nonneg_left (hCQ p n le_rfl ω) (ContinuousLinearMap.opNorm_nonneg _))

end GreenBounds

theorem dh_conj_green :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (z : ℂ), z.im ≠ 0 → ∀ (a b x y : ι) (ω : Sample ι),
    dh a b (fun ω' => star (green (hmat ω') z x y)) ω =
      -(star (green (hmat ω) z x b) * star (green (hmat ω) z a y)) := by
  intro ι _ _ z hz a b x y ω
  rw [dh_star, dh_green z hz b a x y ω, star_neg, star_mul']

theorem testFn_green :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (z : ℂ), z.im ≠ 0 → ∀ x y : ι,
    TestFn fun ω : Sample ι => green (hmat ω) z x y := by
  intro ι _ _ z hz x y
  exact testFn_iff_bd.mpr fun n => bd_green hz n x y

theorem testFn_closed :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι],
    (∀ c : ℂ, TestFn fun _ : Sample ι => c) ∧
    (∀ F G : Sample ι → ℂ, TestFn F → TestFn G → TestFn (F + G)) ∧
    (∀ F G : Sample ι → ℂ, TestFn F → TestFn G → TestFn (F * G)) ∧
    (∀ F : Sample ι → ℂ, TestFn F → TestFn fun ω => star (F ω)) ∧
    (∀ (a b : ι) (F : Sample ι → ℂ), TestFn F → TestFn (dh a b F)) ∧
    (∀ F : Sample ι → ℂ, TestFn F → BddMeas F) := by
  intro ι _ _
  exact ⟨testFn_const, fun _ _ hF hG => testFn_add hF hG, fun _ _ hF hG => testFn_mul hF hG,
    fun _ hF => testFn_star hF, fun a b _ hF => testFn_dh a b hF, fun _ hF => testFn_bddMeas hF⟩

section Instance

end Instance

end RBM8D
