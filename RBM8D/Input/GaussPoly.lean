module

public import RBM8D.Prob.Model
public import RBM8D.Prob.Stein

@[expose] public section

/-!
# Gaussian integration by parts for functions of polynomial growth

For the law of [I, Assumption 1.1] on a finite index set: the class of continuous functions of
the sample dominated by a polynomial in finitely many coordinates, its closure under the ring
operations and conjugation, the finiteness of all polynomial moments, and the one-coordinate
Gaussian integration by parts `E[ω_c g] = v_c E[∂_c g]` for such `g` (the real form of
[I, Lemma 2.4] for unbounded integrands).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace RBM8D

variable {ι : Type} [Fintype ι]

/-! ### Finite dependence -/

/-- `g` is determined by the coordinates in some finite set `I`. -/
def gaussPoly_FinDep {V : Type*} (g : Sample ι → V) : Prop :=
  ∃ I : Finset (Coord ι), ∀ ω ω' : Sample ι, (∀ e ∈ I, ω e = ω' e) → g ω = g ω'

variable {S : Matrix ι ι ℝ}

/-! ### Polynomial weights -/

/-- The polynomial weight `1 + ∑_{c ∈ I} |ω_c|`. -/
noncomputable def gaussPoly_polyW (I : Finset (Coord ι)) (ω : Sample ι) : ℝ :=
  1 + ∑ c ∈ I, |ω c|

private theorem one_le_polyW (I : Finset (Coord ι)) (ω : Sample ι) : 1 ≤ gaussPoly_polyW I ω := by
  have : (0 : ℝ) ≤ ∑ c ∈ I, |ω c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold gaussPoly_polyW; linarith

private theorem polyW_pos (I : Finset (Coord ι)) (ω : Sample ι) : 0 < gaussPoly_polyW I ω :=
  lt_of_lt_of_le zero_lt_one (one_le_polyW I ω)

private theorem polyW_nonneg (I : Finset (Coord ι)) (ω : Sample ι) : 0 ≤ gaussPoly_polyW I ω :=
  le_trans zero_le_one (one_le_polyW I ω)

private theorem polyW_mono {I J : Finset (Coord ι)} (h : I ⊆ J) (ω : Sample ι) :
    gaussPoly_polyW I ω ≤ gaussPoly_polyW J ω := by
  have : ∑ c ∈ I, |ω c| ≤ ∑ c ∈ J, |ω c| :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => abs_nonneg _
  unfold gaussPoly_polyW; linarith

private theorem polyW_pow_le {I J : Finset (Coord ι)} (hIJ : I ⊆ J) {n m : ℕ} (hnm : n ≤ m)
    (ω : Sample ι) :
    gaussPoly_polyW I ω ^ n ≤ gaussPoly_polyW J ω ^ m :=
  le_trans (pow_le_pow_left₀ (polyW_nonneg _ _) (polyW_mono hIJ ω) n)
    (pow_le_pow_right₀ (one_le_polyW J ω) hnm)

/-! ### An elementary Young inequality with natural exponents

`(q+1) a b^q ≤ a^{q+1} + q b^{q+1}` for `a, b ≥ 0`: the arithmetic–geometric mean inequality for
the `q+1` numbers `a, b, …, b`, proved from `a^n - b^n = (a-b)∑ a^i b^{n-1-i}`.  Only natural
powers occur. -/
theorem gaussPoly_young_pow (q : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((q : ℝ) + 1) * (a * b ^ q) ≤ a ^ (q + 1) + (q : ℝ) * b ^ (q + 1) := by
  have hgs : (∑ i ∈ Finset.range (q + 1), a ^ i * b ^ (q + 1 - 1 - i)) * (a - b)
      = a ^ (q + 1) - b ^ (q + 1) := geom_sum₂_mul a b (q + 1)
  set Sm := ∑ i ∈ Finset.range (q + 1), a ^ i * b ^ (q + 1 - 1 - i) with hS
  have hconst : ∑ _i ∈ Finset.range (q + 1), b ^ q = ((q : ℝ) + 1) * b ^ q := by
    rw [Finset.sum_const, Finset.card_range]
    ring
  have key : ((q : ℝ) + 1) * b ^ q * (a - b) ≤ a ^ (q + 1) - b ^ (q + 1) := by
    rcases le_total b a with hab | hab
    · have hge : ((q : ℝ) + 1) * b ^ q ≤ Sm := by
        rw [hS, ← hconst]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
        have hsplit : b ^ q = b ^ i * b ^ (q - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, show q + 1 - 1 - i = q - i from by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hab i) (by positivity)
      have hmul := mul_le_mul_of_nonneg_right hge (sub_nonneg.mpr hab)
      rw [hgs] at hmul
      exact hmul
    · have hle : Sm ≤ ((q : ℝ) + 1) * b ^ q := by
        rw [hS, ← hconst]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
        have hsplit : b ^ q = b ^ i * b ^ (q - i) := by
          rw [← pow_add]; congr 1; omega
        rw [hsplit, show q + 1 - 1 - i = q - i from by omega]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab i) (by positivity)
      have hmul := mul_le_mul_of_nonpos_right hle (sub_nonpos.mpr hab)
      rw [hgs] at hmul
      exact hmul
  have expand : ((q : ℝ) + 1) * b ^ q * (a - b)
      = ((q : ℝ) + 1) * (a * b ^ q) - ((q : ℝ) + 1) * b ^ (q + 1) := by
    rw [pow_succ]; ring
  rw [expand] at key
  linarith

/-! ### Continuous functions of polynomial growth

The class is closed under the ring operations and under complex conjugation; all its members are
integrable for the law of [I, Assumption 1.1]. -/

/-- `f` is **tame**: continuous, reading only finitely many coordinates, and dominated by a
polynomial in finitely many coordinates. -/
structure gaussPoly_Tame (f : Sample ι → ℂ) : Prop where
  /-- `f` is continuous. -/
  cont : Continuous f
  /-- `f` reads only finitely many coordinates. -/
  findep : gaussPoly_FinDep f
  /-- `f` is dominated by a polynomial in finitely many coordinates. -/
  poly : ∃ (I : Finset (Coord ι)) (n : ℕ) (C : ℝ), ∀ ω, ‖f ω‖ ≤ C * gaussPoly_polyW I ω ^ n

namespace gaussPoly_Tame

variable {f g : Sample ι → ℂ}

theorem const (z : ℂ) : gaussPoly_Tame (fun _ : Sample ι => z) :=
  ⟨continuous_const, ⟨∅, fun _ _ _ => rfl⟩, ⟨∅, 0, ‖z‖, fun ω => by simp⟩⟩

theorem coord (c : Coord ι) : gaussPoly_Tame (fun ω : Sample ι => (ω c : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp (continuous_apply c),
    ⟨{c}, fun ω ω' h => by
      show ((ω c : ℂ)) = ((ω' c : ℂ))
      rw [h c (Finset.mem_singleton_self c)]⟩, ⟨{c}, 1, 1, fun ω => ?_⟩⟩
  have : |ω c| ≤ gaussPoly_polyW ({c} : Finset (Coord ι)) ω := by
    unfold gaussPoly_polyW; simp
  simpa [Complex.norm_real] using this

theorem add (hf : gaussPoly_Tame f) (hg : gaussPoly_Tame g) :
    gaussPoly_Tame (fun ω => f ω + g ω) := by
  classical
  obtain ⟨I₁, n₁, C₁, h₁⟩ := hf.poly
  obtain ⟨I₂, n₂, C₂, h₂⟩ := hg.poly
  obtain ⟨J₁, hJ₁⟩ := hf.findep
  obtain ⟨J₂, hJ₂⟩ := hg.findep
  refine ⟨hf.cont.add hg.cont, ⟨J₁ ∪ J₂, fun ω ω' h => ?_⟩,
    ⟨I₁ ∪ I₂, max n₁ n₂, C₁ + C₂, fun ω => ?_⟩⟩
  · show f ω + g ω = f ω' + g ω'
    rw [hJ₁ ω ω' fun e he => h e (Finset.mem_union_left _ he),
      hJ₂ ω ω' fun e he => h e (Finset.mem_union_right _ he)]
  · have hC₁ : 0 ≤ C₁ := by
      have hp : (0 : ℝ) < gaussPoly_polyW I₁ ω ^ n₁ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f ω), h₁ ω]
    have hC₂ : 0 ≤ C₂ := by
      have hp : (0 : ℝ) < gaussPoly_polyW I₂ ω ^ n₂ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (g ω), h₂ ω]
    have e₁ : C₁ * gaussPoly_polyW I₁ ω ^ n₁ ≤ C₁ * gaussPoly_polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ :=
      mul_le_mul_of_nonneg_left
        (polyW_pow_le Finset.subset_union_left (le_max_left _ _) ω) hC₁
    have e₂ : C₂ * gaussPoly_polyW I₂ ω ^ n₂ ≤ C₂ * gaussPoly_polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ :=
      mul_le_mul_of_nonneg_left
        (polyW_pow_le Finset.subset_union_right (le_max_right _ _) ω) hC₂
    calc ‖f ω + g ω‖ ≤ ‖f ω‖ + ‖g ω‖ := norm_add_le _ _
      _ ≤ C₁ * gaussPoly_polyW I₁ ω ^ n₁ + C₂ * gaussPoly_polyW I₂ ω ^ n₂ :=
          add_le_add (h₁ ω) (h₂ ω)
      _ ≤ (C₁ + C₂) * gaussPoly_polyW (I₁ ∪ I₂) ω ^ max n₁ n₂ := by linarith

theorem mul (hf : gaussPoly_Tame f) (hg : gaussPoly_Tame g) :
    gaussPoly_Tame (fun ω => f ω * g ω) := by
  classical
  obtain ⟨I₁, n₁, C₁, h₁⟩ := hf.poly
  obtain ⟨I₂, n₂, C₂, h₂⟩ := hg.poly
  obtain ⟨J₁, hJ₁⟩ := hf.findep
  obtain ⟨J₂, hJ₂⟩ := hg.findep
  refine ⟨hf.cont.mul hg.cont, ⟨J₁ ∪ J₂, fun ω ω' h => ?_⟩,
    ⟨I₁ ∪ I₂, n₁ + n₂, C₁ * C₂, fun ω => ?_⟩⟩
  · show f ω * g ω = f ω' * g ω'
    rw [hJ₁ ω ω' fun e he => h e (Finset.mem_union_left _ he),
      hJ₂ ω ω' fun e he => h e (Finset.mem_union_right _ he)]
  · have hC₁ : 0 ≤ C₁ := by
      have hp : (0 : ℝ) < gaussPoly_polyW I₁ ω ^ n₁ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f ω), h₁ ω]
    have hC₂ : 0 ≤ C₂ := by
      have hp : (0 : ℝ) < gaussPoly_polyW I₂ ω ^ n₂ := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (g ω), h₂ ω]
    have e₁ : gaussPoly_polyW I₁ ω ^ n₁ ≤ gaussPoly_polyW (I₁ ∪ I₂) ω ^ n₁ :=
      polyW_pow_le Finset.subset_union_left le_rfl ω
    have e₂ : gaussPoly_polyW I₂ ω ^ n₂ ≤ gaussPoly_polyW (I₁ ∪ I₂) ω ^ n₂ :=
      polyW_pow_le Finset.subset_union_right le_rfl ω
    have hp₁ : (0 : ℝ) ≤ gaussPoly_polyW (I₁ ∪ I₂) ω ^ n₁ := le_of_lt (pow_pos (polyW_pos _ _) _)
    have hp₂ : (0 : ℝ) ≤ gaussPoly_polyW (I₁ ∪ I₂) ω ^ n₂ := le_of_lt (pow_pos (polyW_pos _ _) _)
    calc ‖f ω * g ω‖ = ‖f ω‖ * ‖g ω‖ := norm_mul _ _
      _ ≤ (C₁ * gaussPoly_polyW I₁ ω ^ n₁) * (C₂ * gaussPoly_polyW I₂ ω ^ n₂) :=
          mul_le_mul (h₁ ω) (h₂ ω) (norm_nonneg _)
            (mul_nonneg hC₁ (le_of_lt (pow_pos (polyW_pos _ _) _)))
      _ ≤ (C₁ * C₂) * gaussPoly_polyW (I₁ ∪ I₂) ω ^ (n₁ + n₂) := by
          rw [pow_add]
          have hkey := mul_le_mul e₁ e₂ (le_of_lt (pow_pos (polyW_pos _ _) _)) hp₁
          calc C₁ * gaussPoly_polyW I₁ ω ^ n₁ * (C₂ * gaussPoly_polyW I₂ ω ^ n₂)
              = C₁ * C₂ * (gaussPoly_polyW I₁ ω ^ n₁ * gaussPoly_polyW I₂ ω ^ n₂) := by ring
            _ ≤ C₁ * C₂ * (gaussPoly_polyW (I₁ ∪ I₂) ω ^ n₁ * gaussPoly_polyW (I₁ ∪ I₂) ω ^ n₂) :=
                mul_le_mul_of_nonneg_left hkey (mul_nonneg hC₁ hC₂)

theorem neg (hf : gaussPoly_Tame f) : gaussPoly_Tame (fun ω => -f ω) := by
  obtain ⟨I, n, C, h⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  exact ⟨hf.cont.neg, ⟨J, fun ω ω' hh => by show -f ω = -f ω'; rw [hJ ω ω' hh]⟩,
    ⟨I, n, C, fun ω => by simpa using h ω⟩⟩

theorem sub (hf : gaussPoly_Tame f) (hg : gaussPoly_Tame g) :
    gaussPoly_Tame (fun ω => f ω - g ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem conj (hf : gaussPoly_Tame f) : gaussPoly_Tame (fun ω => (starRingEnd ℂ) (f ω)) := by
  obtain ⟨I, n, C, h⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  exact ⟨Complex.continuous_conj.comp hf.cont,
    ⟨J, fun ω ω' hh => by
      show (starRingEnd ℂ) (f ω) = (starRingEnd ℂ) (f ω'); rw [hJ ω ω' hh]⟩,
    ⟨I, n, C, fun ω => by simpa using h ω⟩⟩

theorem pow (hf : gaussPoly_Tame f) (n : ℕ) : gaussPoly_Tame (fun ω => f ω ^ n) := by
  induction n with
  | zero => simpa using gaussPoly_Tame.const (ι := ι) 1
  | succ n ih => simpa [_root_.pow_succ] using ih.mul hf

theorem sum {α : Type*} (s : Finset α) {F : α → Sample ι → ℂ} (h : ∀ i ∈ s, gaussPoly_Tame (F i)) :
    gaussPoly_Tame (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using gaussPoly_Tame.const (ι := ι) 0
  | insert i₀ s hi₀ ih =>
    have h₀ := h i₀ (Finset.mem_insert_self _ _)
    have hs := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert hi₀] using h₀.add hs

/-- A continuous, finitely dependent, globally bounded function is tame. -/
theorem ofBdd {C : ℝ} (hc : Continuous f) (hd : gaussPoly_FinDep f) (hb : ∀ ω, ‖f ω‖ ≤ C) :
    gaussPoly_Tame f :=
  ⟨hc, hd, ∅, 0, C, fun ω => by simpa using hb ω⟩

end gaussPoly_Tame

variable [DecidableEq ι]

/-! ### Gaussian integration by parts -/

/-- The Gaussian calculus of the law of [I, Assumption 1.1] on continuous functions of polynomial
growth: the one-coordinate integration by parts `E[ω_c g] = v_c E[∂_c g]`, with `v_c` the variance
of the coordinate `c`, and the finiteness of all polynomial moments. -/
structure gaussPoly_GaussIBP (S : Matrix ι ι ℝ) : Prop where
  /-- `E[ω_c g] = v_c E[∂_c g]` for tame `g`. -/
  stein : ∀ (c : Coord ι) (g g' : Sample ι → ℂ), gaussPoly_Tame g → gaussPoly_Tame g' →
    (∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c)) →
    ∫ ω, (ω c : ℂ) * g ω ∂(gaussLaw S) = (coordVar S c : ℝ) * ∫ ω, g' ω ∂(gaussLaw S)
  /-- All polynomial moments of `gaussLaw S` are finite. -/
  polyInt : ∀ (I : Finset (Coord ι)) (n : ℕ),
    Integrable (fun ω => gaussPoly_polyW I ω ^ n) (gaussLaw S)

/-- Every tame function is integrable. -/
theorem gaussPoly_Tame.integrable (hG : gaussPoly_GaussIBP S) {f : Sample ι → ℂ}
    (hf : gaussPoly_Tame f) :
    Integrable f (gaussLaw S) := by
  obtain ⟨I, n, C, hb⟩ := hf.poly
  have hC : 0 ≤ C := by
    have hp : (0 : ℝ) < gaussPoly_polyW I (fun _ => 0) ^ n := pow_pos (polyW_pos _ _) _
    nlinarith [norm_nonneg (f fun _ => 0), hb fun _ => 0]
  refine Integrable.mono ((hG.polyInt I n).const_mul C) hf.cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hp : (0 : ℝ) ≤ C * gaussPoly_polyW I ω ^ n :=
    mul_nonneg hC (le_of_lt (pow_pos (polyW_pos _ _) _))
  have : ‖C * gaussPoly_polyW I ω ^ n‖ = C * gaussPoly_polyW I ω ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
  rw [this]
  exact hb ω

section Moments

open scoped ENNReal

/-- Every polynomial is integrable against a real Gaussian. -/
private theorem integrable_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) (k : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  have h := hmem.integrable_norm_pow' (p := k)
  refine h.mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Integrability against a centred Gaussian, transferred to the product with its density. -/
private theorem integrable_mul_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 v)) :
    Integrable fun x : ℝ => g x * gaussianPDFReal 0 v x := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at hg
  simpa [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    mul_comm] using hg

end Moments

/-! ### Updating one coordinate -/

/-- `upd c (ω, t)` is `ω` with its coordinate `c` replaced by `t`. -/
private def upd (c : Coord ι) (p : Sample ι × ℝ) : Sample ι := Function.update p.1 c p.2

@[simp] private theorem upd_self (c : Coord ι) (p : Sample ι × ℝ) : upd c p c = p.2 :=
  Function.update_self _ _ _

private theorem upd_of_ne (c : Coord ι) (p : Sample ι × ℝ) {i : Coord ι} (h : i ≠ c) :
    upd c p i = p.1 i :=
  Function.update_of_ne h _ _

private theorem measurable_upd (c : Coord ι) : Measurable (upd c) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [upd_self] using measurable_snd
  · simpa only [upd_of_ne c _ h, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

/-- Replacing the coordinate `c` of a sample by an independent copy of its own law leaves the
law of [I, Assumption 1.1] unchanged. -/
private theorem P_map_update (S : Matrix ι ι ℝ) (c : Coord ι) :
    ((gaussLaw S).prod (gaussianReal 0 (coordVar S c))).map (upd c) = gaussLaw S := by
  have hm : Measurable (upd c) := measurable_upd c
  unfold gaussLaw
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : upd c ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s c Set.univ) ×ˢ s c := by
    ext ⟨ω, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, upd]
    constructor
    · intro h
      refine ⟨fun d => ?_, by simpa using h c⟩
      by_cases hd : d = c
      · subst hd; simp
      · simpa [Function.update_of_ne hd] using h d
    · rintro ⟨h1, h2⟩ d
      by_cases hd : d = c
      · subst hd; simpa using h2
      · simpa [Function.update_of_ne hd] using h1 d
  have hprod : (fun d => gaussianReal 0 (coordVar S d) (Function.update s c Set.univ d))
      = Function.update (fun d => gaussianReal 0 (coordVar S d) (s d)) c 1 := by
    funext d
    by_cases hd : d = c
    · subst hd; simp
    · simp [Function.update_of_ne hd]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, hprod,
    Finset.prod_update_of_mem (Finset.mem_univ c),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ c)]
  ring

omit [DecidableEq ι] in
/-- Every coordinate has finite moments of every order. -/
private theorem integrable_pow_coord (S : Matrix ι ι ℝ) (c : Coord ι) (k : ℕ) :
    Integrable (fun ω : Sample ι => (ω c) ^ k) (gaussLaw S) := by
  have hmp : MeasurePreserving (fun ω : Sample ι => ω c) (gaussLaw S)
      (gaussianReal 0 (coordVar S c)) :=
    measurePreserving_eval (fun c => gaussianReal 0 (coordVar S c)) c
  exact (hmp.integrable_comp (measurable_id.pow_const k).aestronglyMeasurable).mpr
    (integrable_pow_gaussianReal _ k)


/-! ### An elementary inequality -/

/-- `(a+b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
private theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h0 : 0 ≤ max a b := le_max_of_le_left ha
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by linarith) hmax n
    _ = 2 ^ n * max a b ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]
          have : (0 : ℝ) ≤ a ^ n := pow_nonneg ha n
          linarith
        · rw [max_eq_left h]
          have : (0 : ℝ) ≤ b ^ n := pow_nonneg hb n
          linarith

/-! ### All polynomial moments are finite -/

omit [DecidableEq ι] in
/-- `|ω_c|^n` is integrable. -/
private theorem integrable_abs_pow_coord (S : Matrix ι ι ℝ) (c : Coord ι) (n : ℕ) :
    Integrable (fun ω : Sample ι => |ω c| ^ n) (gaussLaw S) := by
  have h := (integrable_pow_coord S c n).abs
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  change |ω c ^ n| = |ω c| ^ n
  rw [abs_pow]

omit [DecidableEq ι] in
private theorem continuous_polyW (I : Finset (Coord ι)) :
    Continuous fun ω : Sample ι => gaussPoly_polyW I ω := by
  refine continuous_const.add ?_
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).abs

omit [DecidableEq ι] in
/-- Every polynomial moment of the law is finite. -/
private theorem integrable_polyW_pow (S : Matrix ι ι ℝ) (I : Finset (Coord ι)) (n : ℕ) :
    Integrable (fun ω : Sample ι => gaussPoly_polyW I ω ^ n) (gaussLaw S) := by
  classical
  induction I using Finset.induction generalizing n with
  | empty =>
      have h : ∀ ω : Sample ι, gaussPoly_polyW (∅ : Finset (Coord ι)) ω ^ n = 1 := by
        intro ω; simp [gaussPoly_polyW]
      simp only [h]
      exact integrable_const 1
  | insert c I hc ih =>
      have hsplit : ∀ ω : Sample ι,
          gaussPoly_polyW (insert c I) ω = gaussPoly_polyW I ω + |ω c| := by
        intro ω
        change 1 + ∑ x ∈ insert c I, |ω x| = (1 + ∑ x ∈ I, |ω x|) + |ω c|
        rw [Finset.sum_insert hc]
        ring
      have hmaj : Integrable
          (fun ω : Sample ι => 2 ^ n * (gaussPoly_polyW I ω ^ n + |ω c| ^ n)) (gaussLaw S) :=
        ((ih n).add (integrable_abs_pow_coord S c n)).const_mul _
      refine Integrable.mono' hmaj
        (((continuous_polyW (insert c I)).pow n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      have hp : (0 : ℝ) ≤ gaussPoly_polyW I ω := (polyW_nonneg I ω)
      have hq : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      have hb := add_pow_le_two_pow_mul hp hq n
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (polyW_nonneg (insert c I) ω) n), hsplit ω]
      exact hb

/-! ### One-dimensional Stein identity with integrability hypotheses against the measure -/

/-- The real one-dimensional Stein identity, hypotheses stated against the Gaussian measure. -/
private theorem integral_mul_gaussianReal_int {var : ℝ≥0} (hv : var ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal 0 var))
    (hxfi : Integrable (fun x : ℝ => x * f x) (gaussianReal 0 var))
    (hf'i : Integrable f' (gaussianReal 0 var)) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var)
      = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  refine integral_mul_gaussianReal hv hf ?_ (integrable_mul_gaussianPDFReal hv hf'i)
    (integrable_mul_gaussianPDFReal hv hfi)
  have hv' : (var : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h := integrable_mul_gaussianPDFReal hv (hxfi.const_mul (-(1 / (var : ℝ))))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  change -(1 / (var : ℝ)) * (x * f x) * gaussianPDFReal 0 var x
    = f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x)
  field_simp

/-- The complex one-dimensional Stein identity, hypotheses stated against the Gaussian measure
and with no restriction on the variance. -/
private theorem integral_mul_gaussianReal_complex_int {var : ℝ≥0} {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal 0 var))
    (hxfi : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var))
    (hf'i : Integrable f' (gaussianReal 0 var)) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  -- real and imaginary parts
  have hre : ∀ x, HasDerivAt (fun y : ℝ => (f y).re) ((f' x).re) x := by
    intro x
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have him : ∀ x, HasDerivAt (fun y : ℝ => (f y).im) ((f' x).im) x := by
    intro x
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simpa only [Function.comp_def, Complex.imCLM_apply] using h
  have hxre : Integrable (fun x : ℝ => x * (f x).re) (gaussianReal 0 var) := by
    refine hxfi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    change ((x : ℂ) * f x).re = x * (f x).re
    simp [Complex.mul_re]
  have hxim : Integrable (fun x : ℝ => x * (f x).im) (gaussianReal 0 var) := by
    refine hxfi.im.congr (Filter.Eventually.of_forall fun x => ?_)
    change ((x : ℂ) * f x).im = x * (f x).im
    simp [Complex.mul_im]
  have hR := integral_mul_gaussianReal_int hv hre hfi.re hxre hf'i.re
  have hI := integral_mul_gaussianReal_int hv him hfi.im hxim hf'i.im
  -- assemble
  have hIl : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var) := hxfi
  have hlre : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, x * (f x).re ∂(gaussianReal 0 var) := by
    have h := (Complex.reCLM.integral_comp_comm hIl).symm
    simp only [Complex.reCLM_apply] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.mul_re])
  have hlim : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, x * (f x).im ∂(gaussianReal 0 var) := by
    have h := (Complex.imCLM.integral_comp_comm hIl).symm
    simp only [Complex.imCLM_apply] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.mul_im])
  have hrre : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, (f' x).re ∂(gaussianReal 0 var) := by
    have h := (Complex.reCLM.integral_comp_comm hf'i).symm
    simpa only [Complex.reCLM_apply] using h
  have hrim : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, (f' x).im ∂(gaussianReal 0 var) := by
    have h := (Complex.imCLM.integral_comp_comm hf'i).symm
    simpa only [Complex.imCLM_apply] using h
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hlre, hrre]
    exact hR
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hlim, hrim]
    exact hI

/-! ### The fibrewise argument -/

/-- `|x|^k` is integrable for a centred Gaussian. -/
private theorem integrable_abs_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have h := (integrable_pow_gaussianReal v k).abs
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  change |x ^ k| = |x| ^ k
  rw [abs_pow]

/-- Updating one coordinate increases the polynomial weight by at most `|t|`. -/
private theorem polyW_upd_le (c : Coord ι) (I : Finset (Coord ι))
    (p : Sample ι × ℝ) :
    gaussPoly_polyW I (upd c p) ≤ gaussPoly_polyW I p.1 + |p.2| := by
  classical
  have hterm : ∀ x ∈ I, |(upd c p) x|
      ≤ |p.1 x| + (if x = c then |p.2| else 0) := by
    intro x _
    by_cases hx : x = c
    · subst hx
      rw [upd_self]
      simp
    · rw [upd_of_ne c p hx, ite_eq_right hx]
      simp
  have hsum : ∑ x ∈ I, |(upd c p) x|
      ≤ ∑ x ∈ I, (|p.1 x| + (if x = c then |p.2| else 0)) :=
    Finset.sum_le_sum hterm
  have hsplit : ∑ x ∈ I, (|p.1 x| + (if x = c then |p.2| else 0))
      = (∑ x ∈ I, |p.1 x|) + ∑ x ∈ I, (if x = c then |p.2| else 0) :=
    Finset.sum_add_distrib
  have hlast : (∑ x ∈ I, (if x = c then |p.2| else 0)) ≤ |p.2| := by
    by_cases hc : c ∈ I
    · rw [Finset.sum_ite_eq' I c fun _ => |p.2|, ite_eq_left hc]
    · rw [Finset.sum_ite_eq' I c fun _ => |p.2|, ite_eq_right hc]
      exact abs_nonneg _
  change 1 + ∑ x ∈ I, |(upd c p) x| ≤ (1 + ∑ x ∈ I, |p.1 x|) + |p.2|
  rw [hsplit] at hsum
  linarith

/-- A polynomial majorant after updating one coordinate. -/
private theorem norm_le_of_tame_upd (c : Coord ι) {f : Sample ι → ℂ}
    {I : Finset (Coord ι)}
    {n : ℕ} {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C * gaussPoly_polyW I ω ^ n) (hC : 0 ≤ C)
    (p : Sample ι × ℝ) :
    ‖f (upd c p)‖ ≤ C * 2 ^ n * (gaussPoly_polyW I p.1 ^ n + |p.2| ^ n) := by
  refine (hb _).trans ?_
  have h1 : gaussPoly_polyW I (upd c p) ^ n ≤ (gaussPoly_polyW I p.1 + |p.2|) ^ n :=
    pow_le_pow_left₀ (polyW_nonneg _ _) (polyW_upd_le c I p) n
  have h2 : (gaussPoly_polyW I p.1 + |p.2|) ^ n ≤ 2 ^ n * (gaussPoly_polyW I p.1 ^ n + |p.2| ^ n) :=
    add_pow_le_two_pow_mul (polyW_nonneg _ _) (abs_nonneg _) n
  calc C * gaussPoly_polyW I (upd c p) ^ n ≤ C * ((gaussPoly_polyW I p.1 + |p.2|) ^ n) :=
        mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * (2 ^ n * (gaussPoly_polyW I p.1 ^ n + |p.2| ^ n)) := mul_le_mul_of_nonneg_left h2 hC
    _ = C * 2 ^ n * (gaussPoly_polyW I p.1 ^ n + |p.2| ^ n) := by ring

/-- The law of [I, Assumption 1.1] satisfies the Gaussian integration by parts on continuous
functions of polynomial growth, for every variance matrix `S` (resampling one coordinate and the
one-dimensional Stein identity on each fibre). -/
theorem gaussPoly_gaussIBP (S : Matrix ι ι ℝ) : gaussPoly_GaussIBP S := by
  refine ⟨fun c g g' hg hg' hderiv => ?_, integrable_polyW_pow S⟩
  classical
  obtain ⟨Ig, ng, Cg, hgb0⟩ := hg.poly
  obtain ⟨Ig', ng', Cg', hg'b0⟩ := hg'.poly
  -- the constants may be taken nonnegative
  have hCg : (0 : ℝ) ≤ max Cg 0 := le_max_right _ _
  have hCg' : (0 : ℝ) ≤ max Cg' 0 := le_max_right _ _
  have hgb : ∀ ω, ‖g ω‖ ≤ max Cg 0 * gaussPoly_polyW Ig ω ^ ng := fun ω =>
    (hgb0 ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (polyW_nonneg _ _) _))
  have hg'b : ∀ ω, ‖g' ω‖ ≤ max Cg' 0 * gaussPoly_polyW Ig' ω ^ ng' := fun ω =>
    (hg'b0 ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (polyW_nonneg _ _) _))
  have hUm : Measurable (upd c) :=
    measurable_upd c
  have hgm : Measurable g := hg.cont.measurable
  have hg'm : Measurable g' := hg'.cont.measurable
  have hfib : ∀ (ω : Sample ι) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s)) (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  -- the three integrability facts on the product
  have hprodg : Integrable (fun p : Sample ι × ℝ => g (upd c p))
      ((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) := by
    refine Integrable.mono'
      ((((integrable_polyW_pow S Ig ng).comp_fst _).add
        ((integrable_abs_pow_gaussianReal (coordVar S c) ng).comp_snd _)).const_mul
          (max Cg 0 * 2 ^ ng))
      ((hgm.comp hUm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using norm_le_of_tame_upd c hgb hCg p
  have hprodg' : Integrable (fun p : Sample ι × ℝ => g' (upd c p))
      ((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) := by
    refine Integrable.mono'
      ((((integrable_polyW_pow S Ig' ng').comp_fst _).add
        ((integrable_abs_pow_gaussianReal (coordVar S c) ng').comp_snd _)).const_mul
          (max Cg' 0 * 2 ^ ng'))
      ((hg'm.comp hUm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using norm_le_of_tame_upd c hg'b hCg' p
  have hprodx : Integrable
      (fun p : Sample ι × ℝ => (p.2 : ℂ) * g (upd c p))
      ((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) := by
    have hmaj : Integrable
        (fun p : Sample ι × ℝ => max Cg 0 * 2 ^ ng *
          (gaussPoly_polyW Ig p.1 ^ ng * |p.2| + 1 * |p.2| ^ (ng + 1)))
        ((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.add ?_ ?_
      · exact (integrable_polyW_pow S Ig ng).mul_prod
          (by simpa using integrable_abs_pow_gaussianReal (coordVar S c) 1)
      · exact (integrable_const (1 : ℝ)).mul_prod
          (integrable_abs_pow_gaussianReal (coordVar S c) (ng + 1))
    refine Integrable.mono' hmaj
      (((Complex.continuous_ofReal.measurable.comp measurable_snd).mul
        (hgm.comp hUm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have hb := norm_le_of_tame_upd c hgb hCg p
    have habs : (0 : ℝ) ≤ |p.2| := abs_nonneg _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |p.2| * ‖g (upd c p)‖
        ≤ |p.2| * (max Cg 0 * 2 ^ ng * (gaussPoly_polyW Ig p.1 ^ ng + |p.2| ^ ng)) :=
          mul_le_mul_of_nonneg_left hb habs
      _ = max Cg 0 * 2 ^ ng * (gaussPoly_polyW Ig p.1 ^ ng * |p.2| + 1 * |p.2| ^ (ng + 1)) := by
          rw [pow_succ]; ring
  -- both sides through the resampling map
  have hL : ∫ ω, (ω c : ℂ) * g ω ∂(gaussLaw S)
      = ∫ p : Sample ι × ℝ, (p.2 : ℂ) * g (upd c p)
          ∂((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) := by
    conv_lhs => rw [← P_map_update S c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update S c]
      exact ((Complex.continuous_ofReal.measurable.comp
        (measurable_pi_apply c)).mul hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(gaussLaw S)
      = ∫ p : Sample ι × ℝ, g' (upd c p)
          ∂((gaussLaw S).prod (gaussianReal 0 (coordVar S c))) := by
    conv_lhs => rw [← P_map_update S c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update S c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hprodx, integral_prod _ hprodg', ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hprodx.prod_right_ae, hprodg.prod_right_ae, hprodg'.prod_right_ae]
    with ω h1 h2 h3
  exact integral_mul_gaussianReal_complex_int (hfib ω) h2 h1 h3
end RBM8D
