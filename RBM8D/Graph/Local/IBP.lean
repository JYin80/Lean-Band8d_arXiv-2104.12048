import RBM8D.Graph.Local.Basic

/-!
# Identities from Gaussian integration by parts

[I, Lemma 2.4] (2.5), [I, (3.3), (3.11), (3.14), (3.15)], [II, (4.23)] under the model relations `ModelAdm`, and [I, Lemma 2.5] (2.7)–(2.9).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section TestClosure

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-! ### Closure of the test functions -/

private theorem test_mul' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω * g ω :=
  A.test_mul f g hf hg

private theorem test_add' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω + g ω :=
  A.test_add f g hf hg

private theorem test_const' (c : ℂ) : A.Test fun _ => c := A.test_const c

private theorem test_sub' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω - g ω := by
  have e : (fun ω => f ω - g ω) = fun ω => f ω + (-1 : ℂ) * g ω := funext fun ω => by ring
  rw [e]
  exact test_add' A hf (test_mul' A (test_const' A _) hg)

private theorem test_neg' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => -f ω := by
  have e : (fun ω => -f ω) = fun ω => (-1 : ℂ) * f ω := funext fun ω => by ring
  rw [e]
  exact test_mul' A (test_const' A _) hf

private theorem test_star' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => star (f ω) :=
  A.test_star f hf

private theorem test_G (a b : ι) : A.Test fun ω => A.G ω a b := by
  have h := A.test_entry a b
  have e : (fun ω => (D ω).Gm ∅ a b) = fun ω => A.G ω a b :=
    funext fun ω => by rw [A.data_G]; rfl
  rwa [e] at h

private theorem test_dh' (a b : ι) {F : Ω → ℂ} (hF : A.Test F) :
    A.Test fun ω => A.dh a b F ω :=
  A.test_dh a b F hF

end TestClosure

/-- Proves `A.Test f` for `f` built from resolvent entries, conjugates, derivatives, sums,
products and constants. -/
local macro "test_tac" A:term : tactic =>
  `(tactic| repeat' (first
    | with_reducible assumption
    | with_reducible apply test_G $A
    | with_reducible apply test_star4 $A
    | with_reducible apply test_dh' $A
    | with_reducible apply test_star' $A
    | with_reducible apply test_mul' $A
    | with_reducible apply test_sub' $A
    | with_reducible apply test_add' $A
    | with_reducible apply test_neg' $A
    | with_reducible apply test_sum' $A
    | with_reducible apply test_const' $A
    | intro))

/-- Proves `A.Good f` for a test function `f`. -/
local macro "good_tac" A:term : tactic =>
  `(tactic| (apply ($A).test_good; test_tac $A))

section Aux

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-! ### Linearity of `P_x` on `Good` -/

private theorem P_add' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω + g ω) ω = PF.P x f ω + PF.P x g ω :=
  congrFun (A.laws.add x f g hf hg) ω

private theorem P_cmul' {f : Ω → ℂ} (c : ℂ) (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => c * f ω) ω = c * PF.P x f ω :=
  congrFun (A.laws.smul x c f hf) ω

include A in
private theorem P_zero' (x : ι) (ω : Ω) : PF.P x (fun _ => 0) ω = 0 := by
  have h := P_cmul' A 0 (A.laws.good_const 0) x ω
  simpa using h

private theorem P_neg' {f : Ω → ℂ} (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => -f ω) ω = -PF.P x f ω := by
  have h := P_cmul' A (-1) hf x ω
  simpa using h

private theorem P_sub' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω - g ω) ω = PF.P x f ω - PF.P x g ω := by
  have hg' : A.Good fun ω => -g ω := by
    have e : (fun ω => -g ω) = fun ω => (-1 : ℂ) * g ω := funext fun ω => by ring
    rw [e]
    exact A.laws.good_mul _ _ (A.laws.good_const _) hg
  have h := P_add' A hf hg' x ω
  rw [P_neg' A hg x ω] at h
  simpa [sub_eq_add_neg] using h

private theorem good_sum' {κ : Type} (s : Finset κ) {f : κ → Ω → ℂ} (h : ∀ i, A.Good (f i)) :
    A.Good fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using A.laws.good_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact A.laws.good_add _ _ (h a) ih

private theorem P_sum' {κ : Type} (s : Finset κ) {f : κ → Ω → ℂ} (h : ∀ i, A.Good (f i))
    (x : ι) (ω : Ω) :
    PF.P x (fun ω => ∑ i ∈ s, f i ω) ω = ∑ i ∈ s, PF.P x (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using P_zero' A x ω
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [P_add' A (h a) (good_sum' A s h) x ω, ih]

omit [Fintype ι] [DecidableEq ι] in
private theorem P_congr' {f g : Ω → ℂ} (h : ∀ ω, f ω = g ω) (x : ι) :
    PF.P x f = PF.P x g := by
  rw [funext h]

/-! ### Derivatives -/

private theorem dh_mul' (a b : ι) {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.dh a b (fun ω => f ω * g ω) = fun ω => A.dh a b f ω * g ω + f ω * A.dh a b g ω :=
  A.dh_mul a b f g hf hg

private theorem dh_G (a b x y : ι) :
    A.dh a b (fun ω => A.G ω x y) = fun ω => -(A.G ω x a * A.G ω b y) :=
  A.dh_green a b x y

private theorem dh_starG (a b x y : ι) :
    A.dh a b (fun ω => star (A.G ω x y)) = fun ω => -(star (A.G ω x b) * star (A.G ω a y)) :=
  A.dh_conj_green a b x y

/-! ### The resolvent equations -/

private theorem H_mul_G (ω : Ω) (a b : ι) :
    ∑ β, A.H ω a β * A.G ω β b = (if a = b then 1 else 0) + A.z * A.G ω a b := by
  have hz : A.z.im ≠ 0 := ne_of_gt A.im_pos
  have h := congrFun (congrFun (sub_mul_green (A.isHermitian ω) hz) a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul,
    Finset.sum_sub_distrib, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  unfold ModelAdm.G
  linear_combination h

private theorem rowSum' (p : ι) : ∑ β, (A.S p β : ℂ) = 1 := by
  have h := A.rowSum p
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

/-! ### One integration by parts in a row or a column -/

/-- The expansion `G_{pb} = m δ_{pb} - m² G_{pb} - m ∑_β h_{pβ} G_{βb}` followed by Gaussian
integration by parts in `P_p` ([I, (3.8)], [I, Lemma 2.4]). -/
private theorem ibp_row (p b : ι) {K : Ω → ℂ} (hK : A.Test K) (ω : Ω) :
    PF.P p (fun ω => A.G ω p b * K ω) ω =
      msc A.z * (if p = b then 1 else 0) * PF.P p K ω
      + msc A.z * ∑ β, (A.S p β : ℂ) *
          PF.P p (fun ω => (A.G ω β β - msc A.z) * A.G ω p b * K ω) ω
      - msc A.z * ∑ β, (A.S p β : ℂ) * PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω := by
  set m := msc A.z with hm
  have hmz : m * (m + A.z) = -1 := msc_mul A.z
  have hpt : ∀ ω, A.G ω p b * K ω = -m ^ 2 * (A.G ω p b * K ω) +
      (m * (if p = b then 1 else 0)) * K ω + (-m) * ∑ β, A.H ω p β * (A.G ω β b * K ω) := by
    intro ω
    have h := H_mul_G A ω p b
    have e : ∑ β, A.H ω p β * (A.G ω β b * K ω) = (∑ β, A.H ω p β * A.G ω β b) * K ω := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [e, h]
    linear_combination (A.G ω p b * K ω) * hmz
  have hGH : ∀ β, A.Good fun ω => A.H ω p β * (A.G ω β b * K ω) := fun β =>
    A.laws.good_mul _ _ (A.good_H p β) (by good_tac A)
  have hibp : ∀ β, PF.P p (fun ω => A.H ω p β * (A.G ω β b * K ω)) ω =
      (A.S p β : ℂ) * (-PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω +
        PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω) := by
    intro β
    rw [A.ibp p p β (Or.inl rfl) (fun ω => A.G ω β b * K ω) (by test_tac A)]
    beta_reduce
    rw [dh_mul' A β p (test_G A β b) hK, dh_G]
    beta_reduce
    rw [P_add' A (by good_tac A) (by good_tac A), ← P_neg' A (by good_tac A)]
    congr 3
    funext ω
    ring
  have hX : PF.P p (fun ω => A.G ω p b * K ω) ω =
      -m ^ 2 * PF.P p (fun ω => A.G ω p b * K ω) ω + (m * (if p = b then 1 else 0)) *
        PF.P p K ω + (-m) * ∑ β, (A.S p β : ℂ) *
          (-PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω +
            PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω) := by
    conv_lhs => rw [P_congr' hpt p]
    rw [P_add' A (by good_tac A)
        (by exact A.laws.good_mul _ _ (A.laws.good_const _) (good_sum' A _ hGH)),
      P_add' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A),
      P_cmul' A _ (A.test_good _ hK), P_cmul' A _ (good_sum' A _ hGH), P_sum' A _ hGH]
    simp only [hibp]
  have hsplit : ∀ β, PF.P p (fun ω => (A.G ω β β - m) * A.G ω p b * K ω) ω =
      PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω -
        m * PF.P p (fun ω => A.G ω p b * K ω) ω := by
    intro β
    rw [P_congr' (g := fun ω => A.G ω β β * A.G ω p b * K ω - m * (A.G ω p b * K ω))
      (fun ω => by ring), P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A)]
  simp only [hsplit]
  have hs := rowSum' A p
  simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib] at hX ⊢
  rw [← Finset.sum_mul, hs]
  linear_combination hX

/-! ### Linear algebra -/

/-- `P_x[c ∑_i d_i f_i] = c ∑_i d_i P_x[f_i]`. -/
private theorem P_csum' {κ : Type} (c : ℂ) (s : Finset κ) (d : κ → ℂ) {f : κ → Ω → ℂ}
    (h : ∀ i, A.Good (f i)) (x : ι) (ω : Ω) :
    PF.P x (fun ω => c * ∑ i ∈ s, d i * f i ω) ω = c * ∑ i ∈ s, d i * PF.P x (f i) ω := by
  have hd : ∀ i, A.Good fun ω => d i * f i ω := fun i =>
    A.laws.good_mul _ _ (A.laws.good_const _) (h i)
  rw [P_cmul' A c (good_sum' A s hd), P_sum' A s hd]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => P_cmul' A _ (h i) x ω)

/-- If `M b = 1` and `M v = R`, then `v = b R`. -/
private theorem solve_left (M b : Matrix ι ι ℂ) (h : M * b = 1) (v R : ι → ℂ)
    (hv : ∀ α, ∑ β, M α β * v β = R α) (x : ι) : v x = ∑ α, b x α * R α := by
  classical
  have hb : b * M = 1 := mul_eq_one_comm.mp h
  have hR : M.mulVec v = R := funext fun α => hv α
  have e : v = b.mulVec (M.mulVec v) := by
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec]
  rw [e, hR]
  rfl

/-- Inversion of `1 - m² S` by `b = 1 + S⁺`. -/
private theorem solve_Sp (ω : Ω) (v R : ι → ℂ)
    (hv : ∀ α, v α - msc A.z ^ 2 * ∑ β, (A.S α β : ℂ) * v β = R α) (x : ι) :
    v x = ∑ α, (1 + (D ω).Sp) x α * R α := by
  refine solve_left _ _ (A.data_Sp ω) v R (fun α => ?_) x
  rw [← hv α, A.data_S ω]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]

/-- The relation `Θ (1 - |m|² S) = |m|² S` in entries. -/
private theorem theta_entry (ω : Ω) (x α : ι) :
    ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) * (A.S x α : ℂ) =
      (D ω).Theta x α - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) * ∑ γ, (D ω).Theta x γ * (A.S γ α : ℂ) := by
  have h := congrFun (congrFun (A.data_Theta ω) x) α
  rw [A.data_S ω] at h
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [← h, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun γ _ => by ring

omit [Fintype ι] [DecidableEq ι] in
private theorem Q_apply' (x : ι) (f : Ω → ℂ) (ω : Ω) :
    PF.op .Q x f ω = f ω - PF.P x f ω := rfl

omit [DecidableEq ι] in
private theorem dsum_eq' (u : ι → ℂ) (c : ℂ) (w : ι → ι → ℂ) :
    ∑ α, u α * (c * ∑ β, w α β) = c * ∑ α, ∑ β, u α * w α β := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

end Aux

/-! ## The identities -/

/-- **[I, Lemma 2.4]** ([I, (2.5)]): for a test function `F`, `|m|² ∑_α s_{xα} G_{αy} Ḡ_{αy'} F =
m Θ_{xy} Ḡ_{yy'} F + m ∑ Θ_{xα} s_{αβ} (G_{ββ} - m) G_{αy} Ḡ_{αy'} F + m ∑ Θ_{xα} s_{αβ}
(Ḡ_{αα} - m̄) G_{βy} Ḡ_{βy'} F - m ∑ Θ_{xα} s_{αβ} G_{βy} Ḡ_{αy'} ∂_{h_{βα}} F + 𝒬_Θ`, pointwise
on `Ω`, where `𝒬_Θ` is the sum of the five `Q` terms of [I, (2.5)]. -/
theorem thetaExpansion (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (A : ModelAdm Ω ι PF D) (x y y' : ι) (F : Ω → ℂ) :
    A.Test F → ∀ ω,
    let m := msc A.z
    let s : ι → ι → ℂ := fun a b => (A.S a b : ℂ)
    let Θ := (D ω).Theta
    ((‖m‖ ^ 2 : ℝ) : ℂ) * ∑ α, s x α * A.G ω α y * star (A.G ω α y') * F ω =
      m * Θ x y * star (A.G ω y y') * F ω
      + m * ∑ α, ∑ β, Θ x α * s α β * (A.G ω β β - m) * A.G ω α y * star (A.G ω α y') * F ω
      + m * ∑ α, ∑ β, Θ x α * s α β * (star (A.G ω α α) - star m) * A.G ω β y *
          star (A.G ω β y') * F ω
      - m * ∑ α, ∑ β, Θ x α * s α β * A.G ω β y * star (A.G ω α y') * A.dh β α F ω
      + (∑ α, Θ x α * PF.op .Q α (fun ω' => A.G ω' α y * star (A.G ω' α y') * F ω') ω
        - m * Θ x y * PF.op .Q y (fun ω' => star (A.G ω' y y') * F ω') ω
        - ∑ α, ∑ β, m * Θ x α * s α β *
            PF.op .Q α (fun ω' => (A.G ω' β β - m) * A.G ω' α y * star (A.G ω' α y') * F ω') ω
        - ∑ α, ∑ β, m * Θ x α * s α β *
            PF.op .Q α (fun ω' => star (A.G ω' α α) * A.G ω' β y * star (A.G ω' β y') * F ω') ω
        + ∑ α, ∑ β, m * Θ x α * s α β *
            PF.op .Q α (fun ω' => A.G ω' β y * star (A.G ω' α y') * A.dh β α F ω') ω) := by
  intro hF ω
  dsimp only
  have hα : ∀ α, (D ω).Theta x α * (A.G ω α y * star (A.G ω α y') * F ω) =
      (D ω).Theta x α *
      (PF.op .Q α (fun ω' => A.G ω' α y * star (A.G ω' α y') * F ω') ω
      + msc A.z * (if α = y then 1 else 0) * (star (A.G ω α y') * F ω -
          PF.op .Q α (fun ω' => star (A.G ω' α y') * F ω') ω)
      + msc A.z * ∑ β, (A.S α β : ℂ) *
          ((A.G ω β β - msc A.z) * A.G ω α y * star (A.G ω α y') * F ω -
            PF.op .Q α (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' α y * star (A.G ω' α y') *
              F ω') ω)
      + msc A.z * ∑ β, (A.S α β : ℂ) *
          (star (A.G ω α α) * A.G ω β y * star (A.G ω β y') * F ω -
            PF.op .Q α (fun ω' => star (A.G ω' α α) * A.G ω' β y * star (A.G ω' β y') * F ω') ω)
      - msc A.z * ∑ β, (A.S α β : ℂ) *
          (A.G ω β y * star (A.G ω α y') * A.dh β α F ω -
            PF.op .Q α (fun ω' => A.G ω' β y * star (A.G ω' α y') * A.dh β α F ω') ω)) := by
    intro α
    congr 1
    have hK : A.Test fun ω' => star (A.G ω' α y') * F ω' := by test_tac A
    have hp : ∀ β, PF.P α (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' α y *
          (star (A.G ω' α y') * F ω')) ω =
        PF.P α (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' α y * star (A.G ω' α y') * F ω') ω :=
      fun β => congrFun (P_congr' (fun ω' => by ring) α) ω
    have hc : ∀ β, PF.P α (fun ω' => A.G ω' β y *
          A.dh β α (fun ω'' => star (A.G ω'' α y') * F ω'') ω') ω =
        -PF.P α (fun ω' => star (A.G ω' α α) * A.G ω' β y * star (A.G ω' β y') * F ω') ω
        + PF.P α (fun ω' => A.G ω' β y * star (A.G ω' α y') * A.dh β α F ω') ω := by
      intro β
      rw [dh_mul' A β α (test_star' A (test_G A α y')) hF, dh_starG]
      beta_reduce
      rw [P_congr' (f := fun ω' => A.G ω' β y * (-(star (A.G ω' α α) * star (A.G ω' β y')) * F ω' +
            star (A.G ω' α y') * A.dh β α F ω'))
          (g := fun ω' => -(star (A.G ω' α α) * A.G ω' β y * star (A.G ω' β y') * F ω') +
            A.G ω' β y * star (A.G ω' α y') * A.dh β α F ω') (fun ω' => by ring),
        P_add' A (by good_tac A) (by good_tac A), P_neg' A (by good_tac A)]
    have hlin : ∀ (u a e : ι → ℂ), ∑ β, u β * (-a β + e β) =
        -∑ β, u β * a β + ∑ β, u β * e β := by
      intro u a e
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    simp only [Q_apply', sub_sub_cancel]
    rw [P_congr' (f := fun ω' => A.G ω' α y * star (A.G ω' α y') * F ω')
        (g := fun ω' => A.G ω' α y * (star (A.G ω' α y') * F ω')) (fun ω' => by ring),
      ibp_row A α y hK ω]
    simp only [hp, hc]
    rw [hlin]
    ring
  have hL : ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) *
        ∑ α, (A.S x α : ℂ) * A.G ω α y * star (A.G ω α y') * F ω =
      ∑ α, (D ω).Theta x α * (A.G ω α y * star (A.G ω α y') * F ω) -
        ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) * ∑ α, ∑ β, (D ω).Theta x α * (A.S α β : ℂ) *
          (A.G ω β y * star (A.G ω β y') * F ω) := by
    have h1 : ∀ α, ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) *
        ((A.S x α : ℂ) * A.G ω α y * star (A.G ω α y') * F ω) =
        (D ω).Theta x α * (A.G ω α y * star (A.G ω α y') * F ω) -
          ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) * ∑ γ, (D ω).Theta x γ * (A.S γ α : ℂ) *
            (A.G ω α y * star (A.G ω α y') * F ω) := by
      intro α
      have h := theta_entry A ω x α
      rw [← Finset.sum_mul]
      linear_combination (A.G ω α y * star (A.G ω α y') * F ω) * h
    rw [Finset.mul_sum, Finset.sum_congr rfl fun α _ => h1 α, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_comm]
  have hcm : ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) = msc A.z * star (msc A.z) := by
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  have hmain3 : msc A.z * ∑ α, ∑ β, (D ω).Theta x α * (A.S α β : ℂ) *
        (star (A.G ω α α) * A.G ω β y * star (A.G ω β y') * F ω) -
      ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) * ∑ α, ∑ β, (D ω).Theta x α * (A.S α β : ℂ) *
        (A.G ω β y * star (A.G ω β y') * F ω) =
      msc A.z * ∑ α, ∑ β, (D ω).Theta x α * (A.S α β : ℂ) * (star (A.G ω α α) - star (msc A.z)) *
        A.G ω β y * star (A.G ω β y') * F ω := by
    rw [hcm, mul_assoc, ← mul_sub]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun β _ => by ring
  have E : ∀ (u q a c d e : ι → ℂ), ∑ α, u α * (q α + a α + c α + d α - e α) =
      ∑ α, u α * q α + ∑ α, u α * a α + ∑ α, u α * c α + ∑ α, u α * d α - ∑ α, u α * e α := by
    intro u q a c d e
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hδ : ∑ α, (D ω).Theta x α * (msc A.z * (if α = y then 1 else 0) *
      (star (A.G ω α y') * F ω - PF.op .Q α (fun ω' => star (A.G ω' α y') * F ω') ω)) =
      msc A.z * (D ω).Theta x y * star (A.G ω y y') * F ω -
        msc A.z * (D ω).Theta x y * PF.op .Q y (fun ω' => star (A.G ω' y y') * F ω') ω := by
    rw [Finset.sum_eq_single y (fun β _ hβ => by simp [hβ]) (fun h => absurd (Finset.mem_univ y) h)]
    simp only [ite_true]
    ring
  have hds : ∀ (u : ι → ℂ) (c : ℂ) (w a q : ι → ι → ℂ),
      ∑ α, u α * (c * ∑ β, w α β * (a α β - q α β)) =
        c * ∑ α, ∑ β, u α * w α β * a α β - ∑ α, ∑ β, c * u α * w α β * q α β := by
    intro u c w a q
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun β _ => by ring
  rw [hL]
  simp only [hα]
  rw [E, hδ, hds, hds, hds]
  rw [← hmain3]
  simp only [mul_assoc]
  ring

/-- **[I, Lemma 3.5]** ([I, (3.3)]): with `b = 1 + S⁺`, for a test function `F`,
`(G_{xx} - m) F = m ∑ b_{xα} s_{αβ} (G_{αα} - m)(G_{ββ} - m) F - m ∑ b_{xα} s_{αβ} P_α[G_{βα}
∂_{h_{βα}} F] + ∑ b_{xα} Q_α[(G_{αα} - m) F] - m ∑ b_{xα} s_{αβ} Q_α[(G_{ββ} - m) G_{αα} F]`,
pointwise on `Ω`. -/
theorem weightIdentity (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (A : ModelAdm Ω ι PF D) (x : ι) (F : Ω → ℂ) :
    A.Test F → ∀ ω,
    let m := msc A.z
    let s : ι → ι → ℂ := fun a b => (A.S a b : ℂ)
    let b := 1 + (D ω).Sp
    (A.G ω x x - m) * F ω =
      m * ∑ α, ∑ β, b x α * s α β * (A.G ω α α - m) * (A.G ω β β - m) * F ω
      - m * ∑ α, ∑ β, b x α * s α β * PF.P α (fun ω' => A.G ω' β α * A.dh β α F ω') ω
      + ∑ α, b x α * PF.op .Q α (fun ω' => (A.G ω' α α - m) * F ω') ω
      - m * ∑ α, ∑ β, b x α * s α β *
          PF.op .Q α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω := by
  intro hF ω
  dsimp only
  set m := msc A.z with hm
  have key := solve_Sp A ω (fun α => (A.G ω α α - m) * F ω)
    (fun α => PF.op .Q α (fun ω' => (A.G ω' α α - m) * F ω') ω
      + m * ∑ β, (A.S α β : ℂ) * ((A.G ω α α - m) * (A.G ω β β - m) * F ω)
      - m * ∑ β, (A.S α β : ℂ) * PF.P α (fun ω' => A.G ω' β α * A.dh β α F ω') ω
      - m * ∑ β, (A.S α β : ℂ) *
          PF.op .Q α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω)
    (fun α => by
      have hP : PF.P α (fun ω' => (A.G ω' α α - m) * F ω') ω =
          m * PF.P α F ω + m * ∑ β, (A.S α β : ℂ) *
            PF.P α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω
          - m * ∑ β, (A.S α β : ℂ) * PF.P α (fun ω' => A.G ω' β α * A.dh β α F ω') ω
          - m * PF.P α F ω := by
        rw [P_congr' (f := fun ω' => (A.G ω' α α - m) * F ω')
            (g := fun ω' => A.G ω' α α * F ω' - m * F ω') (fun ω' => by ring),
          P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A),
          ibp_row A α α hF ω]
        simp only [ite_true]
        ring
      have hQ : ∑ β, (A.S α β : ℂ) *
            PF.op .Q α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω =
          ∑ β, (A.S α β : ℂ) * ((A.G ω β β - m) * A.G ω α α * F ω) -
            ∑ β, (A.S α β : ℂ) * PF.P α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun β _ => by rw [Q_apply']; ring
      have hS : ∑ β, (A.S α β : ℂ) * ((A.G ω α α - m) * (A.G ω β β - m) * F ω) -
            ∑ β, (A.S α β : ℂ) * ((A.G ω β β - m) * A.G ω α α * F ω) =
          -m * ∑ β, (A.S α β : ℂ) * ((A.G ω β β - m) * F ω) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => by ring
      rw [Q_apply', hQ, hP]
      linear_combination (-m) * hS) x
  beta_reduce at key
  rw [key]
  have E : ∀ (u q a c d : ι → ℂ), ∑ α, u α * (q α + a α - c α - d α) =
      ∑ α, u α * q α + ∑ α, u α * a α - ∑ α, u α * c α - ∑ α, u α * d α := by
    intro u q a c d
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [E]
  simp only [dsum_eq', mul_assoc]
  ring

/-- **[II, (4.23)]**: for a test function `F`, `P_x[(G_{xx} - m) F] = P_x[m² ∑_α s_{xα}
(G_{αα} - m) F + m ∑_α s_{xα} (G_{αα} - m)(G_{xx} - m) F] - P_x[m ∑_α s_{xα} G_{αx}
∂_{h_{αx}} F]`, an identity of functions on `Ω`. -/
theorem weightP (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (A : ModelAdm Ω ι PF D) (x : ι) (F : Ω → ℂ) :
    A.Test F →
    let m := msc A.z
    let s : ι → ι → ℂ := fun a b => (A.S a b : ℂ)
    PF.P x (fun ω => (A.G ω x x - m) * F ω) =
      PF.P x (fun ω => m ^ 2 * ∑ α, s x α * (A.G ω α α - m) * F ω +
        m * ∑ α, s x α * (A.G ω α α - m) * (A.G ω x x - m) * F ω)
      - PF.P x (fun ω => m * ∑ α, s x α * A.G ω α x * A.dh α x F ω) := by
  intro hF
  dsimp only
  funext ω
  set m := msc A.z with hm
  rw [Pi.sub_apply,
    P_congr' (f := fun ω => (A.G ω x x - m) * F ω)
      (g := fun ω => A.G ω x x * F ω - m * F ω) (fun ω => by ring),
    P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A), ibp_row A x x hF ω,
    P_congr' (f := fun ω => m ^ 2 * ∑ α, (A.S x α : ℂ) * (A.G ω α α - m) * F ω +
        m * ∑ α, (A.S x α : ℂ) * (A.G ω α α - m) * (A.G ω x x - m) * F ω)
      (g := fun ω => m * ∑ α, (A.S x α : ℂ) * ((A.G ω α α - m) * A.G ω x x * F ω))
      (fun ω => by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun α _ => by ring),
    P_congr' (f := fun ω => m * ∑ α, (A.S x α : ℂ) * A.G ω α x * A.dh α x F ω)
      (g := fun ω => m * ∑ α, (A.S x α : ℂ) * (A.G ω α x * A.dh α x F ω))
      (fun ω => by
        congr 1
        exact Finset.sum_congr rfl fun α _ => by ring),
    P_csum' A _ _ _ (fun α => by good_tac A), P_csum' A _ _ _ (fun α => by good_tac A)]
  simp only [ite_true]
  ring

/-- **[I, Lemma 3.14]** ([I, (3.15)]): with `b = 1 + S⁺`, for `y, y' ≠ x` and a test function
`F`, `G_{xy} G_{y'x} F = m b_{xy} P_y[G_{y'y} F] + m ∑ b_{xα} s_{αβ} P_α[(G_{ββ} - m) G_{αy}
G_{y'α} F] + m ∑ b_{xα} s_{αβ} P_α[(G_{αα} - m) G_{βy} G_{y'β} F] - m ∑ b_{xα} s_{αβ}
P_α[G_{βy} G_{y'α} ∂_{h_{βα}} F] + ∑ b_{xα} Q_α[G_{αy} G_{y'α} F] - m² ∑ b_{xα} s_{αβ}
Q_α[G_{βy} G_{y'β} F]`, pointwise on `Ω`. -/
theorem ggIdentity (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (A : ModelAdm Ω ι PF D) (x y y' : ι) (F : Ω → ℂ) :
    A.Test F → y ≠ x → y' ≠ x → ∀ ω,
    let m := msc A.z
    let s : ι → ι → ℂ := fun a b => (A.S a b : ℂ)
    let b := 1 + (D ω).Sp
    A.G ω x y * A.G ω y' x * F ω =
      m * b x y * PF.P y (fun ω' => A.G ω' y' y * F ω') ω
      + m * ∑ α, ∑ β, b x α * s α β *
          PF.P α (fun ω' => (A.G ω' β β - m) * A.G ω' α y * A.G ω' y' α * F ω') ω
      + m * ∑ α, ∑ β, b x α * s α β *
          PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β y * A.G ω' y' β * F ω') ω
      - m * ∑ α, ∑ β, b x α * s α β *
          PF.P α (fun ω' => A.G ω' β y * A.G ω' y' α * A.dh β α F ω') ω
      + ∑ α, b x α * PF.op .Q α (fun ω' => A.G ω' α y * A.G ω' y' α * F ω') ω
      - m ^ 2 * ∑ α, ∑ β, b x α * s α β *
          PF.op .Q α (fun ω' => A.G ω' β y * A.G ω' y' β * F ω') ω := by
  intro hF _ _ ω
  dsimp only
  set m := msc A.z with hm
  have key := solve_Sp A ω (fun α => A.G ω α y * A.G ω y' α * F ω)
    (fun α => m * (if α = y then 1 else 0) * PF.P α (fun ω' => A.G ω' y' α * F ω') ω
      + m * ∑ β, (A.S α β : ℂ) *
          PF.P α (fun ω' => (A.G ω' β β - m) * A.G ω' α y * (A.G ω' y' α * F ω')) ω
      + m * ∑ β, (A.S α β : ℂ) *
          PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β y * A.G ω' y' β * F ω') ω
      - m * ∑ β, (A.S α β : ℂ) *
          PF.P α (fun ω' => A.G ω' β y * A.G ω' y' α * A.dh β α F ω') ω
      + PF.op .Q α (fun ω' => A.G ω' α y * A.G ω' y' α * F ω') ω
      - m ^ 2 * ∑ β, (A.S α β : ℂ) *
          PF.op .Q α (fun ω' => A.G ω' β y * A.G ω' y' β * F ω') ω)
    (fun α => by
      have hK : A.Test fun ω' => A.G ω' y' α * F ω' := by test_tac A
      have hc : ∀ β, PF.P α (fun ω' => A.G ω' β y * A.dh β α (fun ω'' => A.G ω'' y' α * F ω'') ω')
            ω = -PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β y * A.G ω' y' β * F ω') ω
            - m * PF.P α (fun ω' => A.G ω' β y * A.G ω' y' β * F ω') ω
            + PF.P α (fun ω' => A.G ω' β y * A.G ω' y' α * A.dh β α F ω') ω := by
        intro β
        rw [dh_mul' A β α (test_G A y' α) hF, dh_G]
        beta_reduce
        rw [P_congr' (f := fun ω' => A.G ω' β y * (-(A.G ω' y' β * A.G ω' α α) * F ω' +
              A.G ω' y' α * A.dh β α F ω'))
            (g := fun ω' => -((A.G ω' α α - m) * A.G ω' β y * A.G ω' y' β * F ω') -
              m * (A.G ω' β y * A.G ω' y' β * F ω') +
              A.G ω' β y * A.G ω' y' α * A.dh β α F ω') (fun ω' => by ring),
          P_add' A (by good_tac A) (by good_tac A), P_sub' A (by good_tac A) (by good_tac A),
          P_neg' A (by good_tac A), P_cmul' A _ (by good_tac A)]
      have hlin : ∀ (u a z c : ι → ℂ) (k : ℂ), ∑ β, u β * (-a β - k * z β + c β) =
          -∑ β, u β * a β - k * ∑ β, u β * z β + ∑ β, u β * c β := by
        intro u a z c k
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun β _ => by ring
      have hQ : ∑ β, (A.S α β : ℂ) * PF.op .Q α (fun ω' => A.G ω' β y * A.G ω' y' β * F ω') ω =
          ∑ β, (A.S α β : ℂ) * (A.G ω β y * A.G ω y' β * F ω) -
            ∑ β, (A.S α β : ℂ) * PF.P α (fun ω' => A.G ω' β y * A.G ω' y' β * F ω') ω := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun β _ => by rw [Q_apply']; ring
      rw [Q_apply', hQ,
        P_congr' (f := fun ω' => A.G ω' α y * A.G ω' y' α * F ω')
          (g := fun ω' => A.G ω' α y * (A.G ω' y' α * F ω')) (fun ω' => by ring),
        ibp_row A α y hK ω]
      simp only [hc]
      rw [hlin]
      ring) x
  beta_reduce at key
  rw [key]
  have E : ∀ (u p a c d q e : ι → ℂ), ∑ α, u α * (p α + a α + c α - d α + q α - e α) =
      ∑ α, u α * p α + ∑ α, u α * a α + ∑ α, u α * c α - ∑ α, u α * d α + ∑ α, u α * q α
        - ∑ α, u α * e α := by
    intro u p a c d q e
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hδ : ∑ α, (1 + (D ω).Sp) x α *
      (m * (if α = y then 1 else 0) * PF.P α (fun ω' => A.G ω' y' α * F ω') ω) =
      m * (1 + (D ω).Sp) x y * PF.P y (fun ω' => A.G ω' y' y * F ω') ω := by
    rw [Finset.sum_eq_single y (fun β _ hβ => by simp [hβ]) (fun h => absurd (Finset.mem_univ y) h)]
    simp only [ite_true]
    ring
  rw [E, hδ]
  simp only [dsum_eq', mul_assoc]

/-- A sum over the labellings of one atom is a sum over `ι`. -/
private theorem sum_fin_one_fun {ι : Type} [Fintype ι] (f : (Fin 1 → ι) → ℂ) :
    ∑ s, f s = ∑ a, f ![a] := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun s => ?_
  congr 1
  funext i
  fin_cases i
  rfl

/-- A sum over the labellings of two atoms is a double sum. -/
private theorem sum_fin_two_fun' {ι : Type} [Fintype ι] (f : (Fin 2 → ι) → ℂ) :
    ∑ s, f s = ∑ a, ∑ b, f ![a, b] := by
  rw [← (piFinTwoEquiv fun _ => ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- **[I, Lemma 2.5]** ([I, (2.7)–(2.9)]): under the model relations, the value of
`T_{a,b₁b₂} = |m|² ∑_x s_{ax} G_{xb₁} Ḡ_{xb₂}` equals the value of the formal sum
`secondOrderExp` of `m Θ_{ab₁} Ḡ_{b₁b₂}`, the two graphs of `A^{(>2)}` and the four graphs of
`Q^{(2)}`, for all external labels `e = (a, b₁, b₂)`. -/
theorem secondOrderT (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) :
    modelAdm Ω ι PF D → ∀ e : Fin 3 → ι, secondOrderExp.valR PF D e = tGraph.valR PF D e := by
  rintro ⟨A⟩ e
  funext ω
  have h := thetaExpansion Ω ι PF D A (e 0) (e 1) (e 2) (fun _ => 1) (A.test_const 1) ω
  have hd : ∀ a b, A.dh a b (fun _ => (1 : ℂ)) = fun _ => 0 := fun a b => A.dh_const a b 1
  have hQ0 : ∀ a, PF.op .Q a (fun _ => (0 : ℂ)) ω = 0 := fun a => by
    rw [Q_apply', P_zero' A]
    simp
  have hcm : ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) = msc A.z * star (msc A.z) := by
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  simp only [hd] at h
  rw [hcm] at h
  simp [ModelAdm.G, hQ0] at h
  simp [Expansion.valR, Graph.valR, Graph.termR, Graph.labels, secondOrderExp, tGraph, mkC, labelQs,
    Comp.labelQ, Comp.val, Coeff.eval, cm, cmb, Charge.apply, Data.chain, A.data_G, A.data_S,
    A.data_m, sum_fin_two_fun', sum_fin_one_fun, Kind.isRandom, CVar.eval]
  simp only [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm] at h ⊢
  linear_combination -h

section Instances

open Complex

end Instances

end RBM8D.Graphs
