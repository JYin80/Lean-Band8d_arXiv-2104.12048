import RBM8D.Input.GaussPoly

/-!
# Moments of a quadratic form in one row of Gaussian entries

Hanson–Wright type moment bounds, used for the quadratic large deviation estimate in the proof
of [I, Lemma 5.1]: for a row `h_k = r(ω_{a_k} + ε_k i ω_{b_k})` of independent centred complex
Gaussian entries of the law of [I, Assumption 1.1] and a bounded continuous matrix `B` free of
the row coordinates, the chaos `Q = Σ_{k,l} h_k B_{kl} \bar h_l − Σ_k σ_k B_{kk}` satisfies
`E|Q|^{2p} ≤ ((2p−1)(4p−2))^p E[V^p]` with `V = Σ_{k,l} σ_k |B_{kl}|² σ_l`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace RBM8D

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}


/-- The data of a *row chaos*: the Gaussian row `h_k = r(ω_{co k tt} + ε_k i ω_{co k ff})` and a
bounded matrix `B` that does not read the coordinates of the row. -/
structure chaos_RowChaos (S : Matrix ι ι ℝ) (κ : Type*) [Fintype κ] [DecidableEq κ] where
  /-- The two coordinates carrying the real and imaginary part of the row entry `h_k`. -/
  co : κ → Bool → Coord ι
  /-- Distinct indices and tags use distinct coordinates. -/
  co_inj : Function.Injective fun p : κ × Bool => co p.1 p.2
  /-- Both tags of `k` carry the same variance. -/
  gvar_tag : ∀ k, (coordVar S (co k false) : ℝ) = (coordVar S (co k true) : ℝ)
  /-- The sign `±1` fixing the orientation of the imaginary part. -/
  eps : κ → ℝ
  /-- `eps k = ±1`. -/
  eps_sq : ∀ k, eps k ^ 2 = 1
  /-- The global scale of the row. -/
  r : ℝ
  /-- The matrix of the quadratic form. -/
  B : Sample ι → κ → κ → ℂ
  /-- `B` is continuous entrywise. -/
  B_cont : ∀ k l, Continuous fun ω => B ω k l
  /-- A global bound for `B`. -/
  Bbd : ℝ
  /-- `B` is globally bounded. -/
  B_bdd : ∀ ω k l, ‖B ω k l‖ ≤ Bbd
  /-- The witness set of coordinates `B` reads. -/
  Ifree : Finset (Coord ι)
  /-- **Row independence**: the witness set contains no coordinate of the row. -/
  Ifree_free : ∀ k b, co k b ∉ Ifree
  /-- `B` is determined by the coordinates in `Ifree`. -/
  B_free : ∀ ω ω', (∀ c ∈ Ifree, ω c = ω' c) → B ω = B ω'

namespace chaos_RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : chaos_RowChaos S κ)

/-- The variance of each of the two coordinates of the index `k`. -/
noncomputable def w (k : κ) : ℝ := (coordVar S (C.co k true) : ℝ)

/-- `σ_k = E|h_k|² = 2 r² w_k`. -/
noncomputable def sg (k : κ) : ℝ := 2 * C.r ^ 2 * C.w k

theorem w_nonneg (k : κ) : 0 ≤ C.w k := (coordVar S (C.co k true)).coe_nonneg

theorem sg_nonneg (k : κ) : 0 ≤ C.sg k := by
  have := C.w_nonneg k; unfold sg; positivity

/-- The row entry `h_k = r (ω_{co k tt} + ε_k i ω_{co k ff})`. -/
noncomputable def h (ω : Sample ι) (k : κ) : ℂ :=
  (C.r : ℂ) * ((ω (C.co k true) : ℂ) + ((C.eps k : ℂ) * Complex.I) * (ω (C.co k false) : ℂ))

/-- `U_k = ∑_l B_{kl} conj(h_l)`. -/
noncomputable def U (ω : Sample ι) (k : κ) : ℂ := ∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)

/-- `V_k = ∑_m h_m B_{mk}`. -/
noncomputable def V (ω : Sample ι) (k : κ) : ℂ := ∑ m, C.h ω m * C.B ω m k

/-- The centring constant `∑_k σ_k B_{kk}` (random, but not reading the row). -/
noncomputable def cen (ω : Sample ι) : ℂ := ∑ k, (C.sg k : ℂ) * C.B ω k k

/-- **The chaos** `Q = ∑_{k,l} h_k B_{kl} conj(h_l) − ∑_k σ_k B_{kk}`. -/
noncomputable def chaos (ω : Sample ι) : ℂ :=
  (∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l)) - C.cen ω

/-- `∂ Q / ∂ ω_{co k tt}`. -/
noncomputable def dA (ω : Sample ι) (k : κ) : ℂ := (C.r : ℂ) * (C.U ω k + C.V ω k)

/-- `∂ Q / ∂ ω_{co k ff}`. -/
noncomputable def dB (ω : Sample ι) (k : κ) : ℂ :=
  ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)

/-- `T = ∑_k σ_k (‖U_k‖² + ‖V_k‖²)`, the random bound of the recursion. -/
noncomputable def Tq (ω : Sample ι) : ℝ := ∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)

/-- `R = ∑_k σ_k U_k V_k`, the off-diagonal term of the recursion; `‖R‖ ≤ T/2`. -/
noncomputable def Rq (ω : Sample ι) : ℂ := ∑ k, (C.sg k : ℂ) * C.U ω k * C.V ω k

theorem Tq_nonneg (ω : Sample ι) : 0 ≤ C.Tq ω :=
  Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)

theorem norm_Rq_le (ω : Sample ι) : ‖C.Rq ω‖ ≤ C.Tq ω / 2 := by
  have hterm : ∀ k : κ, ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖
      ≤ C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by
    intro k
    have h2 : ‖C.U ω k‖ * ‖C.V ω k‖ ≤ (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖C.U ω k‖ - ‖C.V ω k‖)]
    have := mul_le_mul_of_nonneg_left h2 (C.sg_nonneg k)
    calc ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖
        = C.sg k * (‖C.U ω k‖ * ‖C.V ω k‖) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (C.sg_nonneg k), mul_assoc]
      _ ≤ C.sg k * ((‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2) := this
      _ = C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := by ring
  calc ‖C.Rq ω‖ ≤ ∑ k, ‖(C.sg k : ℂ) * C.U ω k * C.V ω k‖ := norm_sum_le _ _
    _ ≤ ∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) / 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = C.Tq ω / 2 := by rw [← Finset.sum_div]; rfl

/-! #### Elementary consequences of the data -/

theorem co_ne_of_index_ne {k m : κ} (hm : m ≠ k) (b b' : Bool) : C.co m b' ≠ C.co k b :=
  fun hh => hm (congrArg Prod.fst (C.co_inj (a₁ := (m, b')) (a₂ := (k, b)) hh))

theorem co_false_ne_co_true (k m : κ) : C.co m false ≠ C.co k true := fun hh => by
  simpa using congrArg Prod.snd (C.co_inj (a₁ := (m, false)) (a₂ := (k, true)) hh)

theorem co_true_ne_co_false (k m : κ) : C.co m true ≠ C.co k false := fun hh => by
  simpa using congrArg Prod.snd (C.co_inj (a₁ := (m, true)) (a₂ := (k, false)) hh)

/-- **Row independence in the form used**: moving a coordinate of the row does not move `B`. -/
theorem B_update (ω : Sample ι) (k : κ) (b : Bool) (t : ℝ) :
    C.B (Function.update ω (C.co k b) t) = C.B ω := by
  refine C.B_free _ _ fun c hc => ?_
  have hne : c ≠ C.co k b := by
    rintro rfl
    exact C.Ifree_free k b hc
  exact Function.update_of_ne hne _ _

theorem tameB (k l : κ) : gaussPoly_Tame (fun ω => C.B ω k l) :=
  gaussPoly_Tame.ofBdd (C.B_cont k l)
    ⟨C.Ifree, fun ω ω' h => congrFun (congrFun (C.B_free ω ω' h) k) l⟩
    (fun ω => C.B_bdd ω k l)

theorem tameh (k : κ) : gaussPoly_Tame (fun ω => C.h ω k) :=
  (gaussPoly_Tame.const (ι := ι) (C.r : ℂ)).mul
    ((gaussPoly_Tame.coord (C.co k true)).add
      ((gaussPoly_Tame.const (ι := ι) ((C.eps k : ℂ) * Complex.I)).mul
        (gaussPoly_Tame.coord (C.co k false))))

theorem tameU (k : κ) : gaussPoly_Tame (fun ω => C.U ω k) :=
  gaussPoly_Tame.sum _ fun l _ => (C.tameB k l).mul (C.tameh l).conj

theorem tameV (k : κ) : gaussPoly_Tame (fun ω => C.V ω k) :=
  gaussPoly_Tame.sum _ fun m _ => (C.tameh m).mul (C.tameB m k)

theorem tamecen : gaussPoly_Tame C.cen :=
  gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) (C.sg k : ℂ)).mul (C.tameB k k)

theorem tamechaos : gaussPoly_Tame C.chaos :=
  (gaussPoly_Tame.sum _ fun k _ => gaussPoly_Tame.sum _ fun l _ =>
    ((C.tameh k).mul (C.tameB k l)).mul (C.tameh l).conj).sub C.tamecen

theorem tamedA (k : κ) : gaussPoly_Tame (fun ω => C.dA ω k) :=
  (gaussPoly_Tame.const (ι := ι) (C.r : ℂ)).mul ((C.tameU k).add (C.tameV k))

theorem tamedB (k : κ) : gaussPoly_Tame (fun ω => C.dB ω k) :=
  (gaussPoly_Tame.const (ι := ι) ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)).mul
    ((C.tameU k).sub (C.tameV k))

/-! #### The coordinate derivatives -/

/-- `∂ h_m / ∂ ω_{co k tt}`. -/
noncomputable def delA (k m : κ) : ℂ := if m = k then (C.r : ℂ) else 0

/-- `∂ h_m / ∂ ω_{co k ff}`. -/
noncomputable def delB (k m : κ) : ℂ :=
  if m = k then (C.r : ℂ) * (C.eps k : ℂ) * Complex.I else 0

theorem conj_delA (k m : κ) : (starRingEnd ℂ) (C.delA k m) = C.delA k m := by
  unfold delA; split_ifs <;> simp

theorem conj_delB (k m : κ) : (starRingEnd ℂ) (C.delB k m) = -C.delB k m := by
  unfold delB; split_ifs <;> simp

theorem hasDerivAt_conj' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (starRingEnd ℂ) (f s)) ((starRingEnd ℂ) f') t :=
  (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

theorem hasDerivAt_ofReal_id (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

theorem hasDerivAt_h_true (k m : κ) (ω : Sample ι) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => C.h (Function.update ω (C.co k true) s) m) (C.delA k m) s₀ := by
  by_cases hm : m = k
  · subst hm
    have e : ∀ s : ℝ, C.h (Function.update ω (C.co m true) s) m
        = (C.r : ℂ) * ((s : ℂ) + ((C.eps m : ℂ) * Complex.I) * (ω (C.co m false) : ℂ)) := by
      intro s
      show (C.r : ℂ) * _ = _
      rw [Function.update_self, Function.update_of_ne (C.co_false_ne_co_true m m)]
    simp only [e]
    have h1 := (hasDerivAt_ofReal_id s₀).add_const
      (((C.eps m : ℂ) * Complex.I) * (ω (C.co m false) : ℂ))
    simpa [delA] using HasDerivAt.const_mul (C.r : ℂ) h1
  · have e : ∀ s : ℝ, C.h (Function.update ω (C.co k true) s) m = C.h ω m := by
      intro s
      show (C.r : ℂ) * _ = (C.r : ℂ) * _
      rw [Function.update_of_ne (C.co_ne_of_index_ne hm _ _),
        Function.update_of_ne (C.co_ne_of_index_ne hm _ _)]
    simp only [e, delA, ite_eq_right hm]
    exact hasDerivAt_const _ _

theorem hasDerivAt_h_false (k m : κ) (ω : Sample ι) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => C.h (Function.update ω (C.co k false) s) m) (C.delB k m) s₀ := by
  by_cases hm : m = k
  · subst hm
    have e : ∀ s : ℝ, C.h (Function.update ω (C.co m false) s) m
        = (C.r : ℂ) * ((ω (C.co m true) : ℂ) + ((C.eps m : ℂ) * Complex.I) * (s : ℂ)) := by
      intro s
      show (C.r : ℂ) * _ = _
      rw [Function.update_self, Function.update_of_ne (C.co_true_ne_co_false m m)]
    simp only [e]
    have h1 := HasDerivAt.const_mul ((C.eps m : ℂ) * Complex.I) (hasDerivAt_ofReal_id s₀)
    have h2 := h1.const_add ((ω (C.co m true) : ℂ))
    have := HasDerivAt.const_mul (C.r : ℂ) h2
    simpa [delB, mul_assoc] using this
  · have e : ∀ s : ℝ, C.h (Function.update ω (C.co k false) s) m = C.h ω m := by
      intro s
      show (C.r : ℂ) * _ = (C.r : ℂ) * _
      rw [Function.update_of_ne (C.co_ne_of_index_ne hm _ _),
        Function.update_of_ne (C.co_ne_of_index_ne hm _ _)]
    simp only [e, delB, ite_eq_right hm]
    exact hasDerivAt_const _ _

theorem cen_update (ω : Sample ι) (k : κ) (b : Bool) (t : ℝ) :
    C.cen (Function.update ω (C.co k b) t) = C.cen ω := by
  unfold cen
  exact Finset.sum_congr rfl fun m _ => by rw [C.B_update ω k b t]

theorem sum_ite_mul_left {a : ℂ} (k : κ) (F : κ → ℂ) :
    ∑ m, (if m = k then a else 0) * F m = a * F k := by
  have e : ∀ m : κ, (if m = k then a else 0) * F m = if m = k then a * F m else 0 := by
    intro m; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun m _ => e m,
    Finset.sum_ite_eq' Finset.univ k fun m => a * F m]
  simp

theorem sum_mul_ite_right {a : ℂ} (k : κ) (F : κ → ℂ) :
    ∑ l, F l * (if l = k then a else 0) = F k * a := by
  have e : ∀ l : κ, F l * (if l = k then a else 0) = if l = k then F l * a else 0 := by
    intro l; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun l _ => e l,
    Finset.sum_ite_eq' Finset.univ k fun l => F l * a]
  simp

omit [DecidableEq κ] in
theorem sum_mul_const (F : κ → ℂ) (a : ℂ) : ∑ m, F m * a = (∑ m, F m) * a :=
  (Finset.sum_mul _ _ _).symm

/-- The value of the derivative of the chaos along the real tag of the row index `k`. -/
theorem sum_delA_eq (k : κ) (ω : Sample ι) :
    (∑ m, ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l))) = C.dA ω k := by
  have e1 : ∀ m : κ, ∑ l, C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      = C.delA k m * C.U ω m := by
    intro m
    show _ = C.delA k m * ∑ l, C.B ω m l * (starRingEnd ℂ) (C.h ω l)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have e2 : ∀ m : κ, ∑ l, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)
      = (C.h ω m * C.B ω m k) * (C.r : ℂ) := by
    intro m
    have e : ∀ l : κ, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)
        = (C.h ω m * C.B ω m l) * (if l = k then (C.r : ℂ) else 0) := fun l => by
      rw [C.conj_delA]; rfl
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.h ω m * C.B ω m l]
  have e3 : ∑ m, C.delA k m * C.U ω m = (C.r : ℂ) * C.U ω k := by
    have e : ∀ m : κ, C.delA k m * C.U ω m = (if m = k then (C.r : ℂ) else 0) * C.U ω m :=
      fun m => rfl
    rw [Finset.sum_congr rfl fun m _ => e m, sum_ite_mul_left k fun m => C.U ω m]
  have e4 : ∑ m, (C.h ω m * C.B ω m k) * (C.r : ℂ) = (C.r : ℂ) * C.V ω k := by
    rw [sum_mul_const]
    show (C.V ω k) * (C.r : ℂ) = _
    ring
  calc (∑ m, ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)))
      = ∑ m, (C.delA k m * C.U ω m + (C.h ω m * C.B ω m k) * (C.r : ℂ)) :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, e1 m, e2 m]
    _ = (C.r : ℂ) * C.U ω k + (C.r : ℂ) * C.V ω k := by rw [Finset.sum_add_distrib, e3, e4]
    _ = C.dA ω k := by unfold dA; ring

/-- The value of the derivative of the chaos along the imaginary tag of the row index `k`. -/
theorem sum_delB_eq (k : κ) (ω : Sample ι) :
    (∑ m, ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l))) = C.dB ω k := by
  set a : ℂ := (C.r : ℂ) * (C.eps k : ℂ) * Complex.I with ha
  have e1 : ∀ m : κ, ∑ l, C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
      = C.delB k m * C.U ω m := by
    intro m
    show _ = C.delB k m * ∑ l, C.B ω m l * (starRingEnd ℂ) (C.h ω l)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _)
  have e2 : ∀ m : κ, ∑ l, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)
      = (C.h ω m * C.B ω m k) * (-a) := by
    intro m
    have e : ∀ l : κ, C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)
        = (C.h ω m * C.B ω m l) * (if l = k then -a else 0) := by
      intro l
      rw [C.conj_delB]
      unfold delB
      split_ifs <;> simp [ha]
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.h ω m * C.B ω m l]
  have e3 : ∑ m, C.delB k m * C.U ω m = a * C.U ω k := by
    have e : ∀ m : κ, C.delB k m * C.U ω m = (if m = k then a else 0) * C.U ω m :=
      fun m => rfl
    rw [Finset.sum_congr rfl fun m _ => e m, sum_ite_mul_left k fun m => C.U ω m]
  have e4 : ∑ m, (C.h ω m * C.B ω m k) * (-a) = -a * C.V ω k := by
    rw [sum_mul_const]
    show (C.V ω k) * (-a) = _
    ring
  calc (∑ m, ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)))
      = ∑ m, (C.delB k m * C.U ω m + (C.h ω m * C.B ω m k) * (-a)) :=
        Finset.sum_congr rfl fun m _ => by rw [Finset.sum_add_distrib, e1 m, e2 m]
    _ = a * C.U ω k + -a * C.V ω k := by rw [Finset.sum_add_distrib, e3, e4]
    _ = C.dB ω k := by unfold dB; rw [ha]; ring

/-- **`∂ Q / ∂ ω_{co k tt} = dA`.** -/
theorem hasDerivAt_chaos_true (k : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k true) s))
      (C.dA ω k) (ω (C.co k true)) := by
  have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
    Function.update_eq_self _ ω
  have hterm : ∀ m l : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k true) s) m *
          C.B (Function.update ω (C.co k true) s) m l *
          (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
      (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)) (ω (C.co k true)) := by
    intro m l
    have h1 := C.hasDerivAt_h_true k m ω (ω (C.co k true))
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_true k l ω (ω (C.co k true)))
    have h2 : HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l) 0
        (ω (C.co k true)) := by
      have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l)
          = fun _ => C.B ω m l := by
        funext s; rw [C.B_update ω k true s]
      rw [hfun]; exact hasDerivAt_const _ _
    have hmul := (h1.fun_mul h2).fun_mul h3
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ))
    (A := fun m s => ∑ l, C.h (Function.update ω (C.co k true) s) m *
        C.B (Function.update ω (C.co k true) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
    (A' := fun m => ∑ l, (C.delA k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delA k l)))
    (fun m _ => HasDerivAt.fun_sum fun l _ => hterm m l)
  have hcen : HasDerivAt (fun s : ℝ => C.cen (Function.update ω (C.co k true) s)) 0
      (ω (C.co k true)) := by
    have hfun : (fun s : ℝ => C.cen (Function.update ω (C.co k true) s)) = fun _ => C.cen ω := by
      funext s; rw [C.cen_update ω k true s]
    rw [hfun]; exact hasDerivAt_const _ _
  have := hsum.sub hcen
  rw [sub_zero, C.sum_delA_eq k ω] at this
  exact this

/-- **`∂ Q / ∂ ω_{co k ff} = dB`.** -/
theorem hasDerivAt_chaos_false (k : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.chaos (Function.update ω (C.co k false) s))
      (C.dB ω k) (ω (C.co k false)) := by
  have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
    Function.update_eq_self _ ω
  have hterm : ∀ m l : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k false) s) m *
          C.B (Function.update ω (C.co k false) s) m l *
          (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
      (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)) (ω (C.co k false)) := by
    intro m l
    have h1 := C.hasDerivAt_h_false k m ω (ω (C.co k false))
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_false k l ω (ω (C.co k false)))
    have h2 : HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l) 0
        (ω (C.co k false)) := by
      have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l)
          = fun _ => C.B ω m l := by
        funext s; rw [C.B_update ω k false s]
      rw [hfun]; exact hasDerivAt_const _ _
    have hmul := (h1.fun_mul h2).fun_mul h3
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ))
    (A := fun m s => ∑ l, C.h (Function.update ω (C.co k false) s) m *
        C.B (Function.update ω (C.co k false) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
    (A' := fun m => ∑ l, (C.delB k m * C.B ω m l * (starRingEnd ℂ) (C.h ω l)
        + C.h ω m * C.B ω m l * (starRingEnd ℂ) (C.delB k l)))
    (fun m _ => HasDerivAt.fun_sum fun l _ => hterm m l)
  have hcen : HasDerivAt (fun s : ℝ => C.cen (Function.update ω (C.co k false) s)) 0
      (ω (C.co k false)) := by
    have hfun : (fun s : ℝ => C.cen (Function.update ω (C.co k false) s)) = fun _ => C.cen ω := by
      funext s; rw [C.cen_update ω k false s]
    rw [hfun]; exact hasDerivAt_const _ _
  have := hsum.sub hcen
  rw [sub_zero, C.sum_delB_eq k ω] at this
  exact this

/-! #### The derivatives of `U`, `V`, `dA`, `dB` -/

theorem hasDerivAt_B_const (k : κ) (b : Bool) (m l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.B (Function.update ω (C.co k b) s) m l) 0 (ω (C.co k b)) := by
  have hfun : (fun s : ℝ => C.B (Function.update ω (C.co k b) s) m l) = fun _ => C.B ω m l := by
    funext s; rw [C.B_update ω k b s]
  rw [hfun]; exact hasDerivAt_const _ _

theorem hasDerivAt_U_true (k m : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.U (Function.update ω (C.co k true) s) m)
      (C.B ω m k * (C.r : ℂ)) (ω (C.co k true)) := by
  have hself := Function.update_eq_self (C.co k true) ω
  have hterm : ∀ l : κ, HasDerivAt
      (fun s : ℝ => C.B (Function.update ω (C.co k true) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k true) s) l))
      (C.B ω m l * (starRingEnd ℂ) (C.delA k l)) (ω (C.co k true)) := by
    intro l
    have h2 := C.hasDerivAt_B_const k true m l ω
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_true k l ω (ω (C.co k true)))
    have hmul := h2.fun_mul h3
    simp only [hself, zero_mul, zero_add] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun l _ => hterm l
  have hval : ∑ l, C.B ω m l * (starRingEnd ℂ) (C.delA k l) = C.B ω m k * (C.r : ℂ) := by
    have e : ∀ l : κ, C.B ω m l * (starRingEnd ℂ) (C.delA k l)
        = C.B ω m l * (if l = k then (C.r : ℂ) else 0) := fun l => by rw [C.conj_delA]; rfl
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.B ω m l]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_V_true (k m : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.V (Function.update ω (C.co k true) s) m)
      ((C.r : ℂ) * C.B ω k m) (ω (C.co k true)) := by
  have hself := Function.update_eq_self (C.co k true) ω
  have hterm : ∀ j : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k true) s) j *
        C.B (Function.update ω (C.co k true) s) j m)
      (C.delA k j * C.B ω j m) (ω (C.co k true)) := by
    intro j
    have h1 := C.hasDerivAt_h_true k j ω (ω (C.co k true))
    have h2 := C.hasDerivAt_B_const k true j m ω
    have hmul := h1.fun_mul h2
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun j _ => hterm j
  have hval : ∑ j, C.delA k j * C.B ω j m = (C.r : ℂ) * C.B ω k m := by
    have e : ∀ j : κ, C.delA k j * C.B ω j m = (if j = k then (C.r : ℂ) else 0) * C.B ω j m :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => e j, sum_ite_mul_left k fun j => C.B ω j m]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_U_false (k m : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.U (Function.update ω (C.co k false) s) m)
      (C.B ω m k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I))) (ω (C.co k false)) := by
  have hself := Function.update_eq_self (C.co k false) ω
  have hterm : ∀ l : κ, HasDerivAt
      (fun s : ℝ => C.B (Function.update ω (C.co k false) s) m l *
        (starRingEnd ℂ) (C.h (Function.update ω (C.co k false) s) l))
      (C.B ω m l * (starRingEnd ℂ) (C.delB k l)) (ω (C.co k false)) := by
    intro l
    have h2 := C.hasDerivAt_B_const k false m l ω
    have h3 := hasDerivAt_conj' (C.hasDerivAt_h_false k l ω (ω (C.co k false)))
    have hmul := h2.fun_mul h3
    simp only [hself, zero_mul, zero_add] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun l _ => hterm l
  have hval : ∑ l, C.B ω m l * (starRingEnd ℂ) (C.delB k l)
      = C.B ω m k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) := by
    have e : ∀ l : κ, C.B ω m l * (starRingEnd ℂ) (C.delB k l)
        = C.B ω m l * (if l = k then -((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) else 0) := by
      intro l
      rw [C.conj_delB]
      unfold delB
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun l _ => e l, sum_mul_ite_right k fun l => C.B ω m l]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_V_false (k m : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.V (Function.update ω (C.co k false) s) m)
      (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k m) (ω (C.co k false)) := by
  have hself := Function.update_eq_self (C.co k false) ω
  have hterm : ∀ j : κ, HasDerivAt
      (fun s : ℝ => C.h (Function.update ω (C.co k false) s) j *
        C.B (Function.update ω (C.co k false) s) j m)
      (C.delB k j * C.B ω j m) (ω (C.co k false)) := by
    intro j
    have h1 := C.hasDerivAt_h_false k j ω (ω (C.co k false))
    have h2 := C.hasDerivAt_B_const k false j m ω
    have hmul := h1.fun_mul h2
    simp only [hself, mul_zero, add_zero] at hmul
    exact hmul
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun j _ => hterm j
  have hval : ∑ j, C.delB k j * C.B ω j m
      = ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k m := by
    have e : ∀ j : κ, C.delB k j * C.B ω j m
        = (if j = k then (C.r : ℂ) * (C.eps k : ℂ) * Complex.I else 0) * C.B ω j m :=
      fun j => rfl
    rw [Finset.sum_congr rfl fun j _ => e j, sum_ite_mul_left k fun j => C.B ω j m]
  rw [hval] at hsum
  exact hsum

theorem hasDerivAt_dA_true (k : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.dA (Function.update ω (C.co k true) s) k)
      (2 * (C.r : ℂ) ^ 2 * C.B ω k k) (ω (C.co k true)) := by
  have hU := C.hasDerivAt_U_true k k ω
  have hV := C.hasDerivAt_V_true k k ω
  have := HasDerivAt.const_mul (C.r : ℂ) (hU.add hV)
  have he : (C.r : ℂ) * (C.B ω k k * (C.r : ℂ) + (C.r : ℂ) * C.B ω k k)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω k k := by ring
  rw [he] at this
  exact this

theorem hasDerivAt_dB_false (k : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.dB (Function.update ω (C.co k false) s) k)
      (2 * (C.r : ℂ) ^ 2 * C.B ω k k) (ω (C.co k false)) := by
  have hU := C.hasDerivAt_U_false k k ω
  have hV := C.hasDerivAt_V_false k k ω
  have hd := HasDerivAt.const_mul ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) (hU.sub hV)
  have hes : ((C.eps k : ℂ)) ^ 2 = 1 := by
    have := C.eps_sq k
    have : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [this]
    push_cast at this
    exact this
  have he : ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) *
      (C.B ω k k * (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I))
        - ((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * C.B ω k k)
      = 2 * (C.r : ℂ) ^ 2 * C.B ω k k := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-2 * (C.r : ℂ) ^ 2 * C.B ω k k * (C.eps k : ℂ) ^ 2) * hI
      + (2 * (C.r : ℂ) ^ 2 * C.B ω k k) * hes
  rw [he] at hd
  exact hd

/-! #### The Euler identity -/

theorem conj_h (ω : Sample ι) (k : κ) : (starRingEnd ℂ) (C.h ω k)
    = (C.r : ℂ) * ((ω (C.co k true) : ℂ)
      - ((C.eps k : ℂ) * Complex.I) * (ω (C.co k false) : ℂ)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * _) = _
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem coord_mul_dA_add_dB (ω : Sample ι) (k : κ) :
    (ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k
      = C.h ω k * C.U ω k + (starRingEnd ℂ) (C.h ω k) * C.V ω k := by
  rw [C.conj_h ω k]
  show _ = ((C.r : ℂ) * _) * _ + _
  unfold dA dB
  ring

/-- **Euler's identity for the chaos**: `∑_α ω_α ∂_α Q = 2 (Q + ∑_k σ_k B_{kk})`. -/
theorem sum_coord_mul_deriv (ω : Sample ι) :
    ∑ k, ((ω (C.co k true) : ℂ) * C.dA ω k + (ω (C.co k false) : ℂ) * C.dB ω k)
      = 2 * (C.chaos ω + C.cen ω) := by
  have hD : C.chaos ω + C.cen ω
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    unfold chaos; ring
  have e1 : ∑ k, C.h ω k * C.U ω k
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) :=
    Finset.sum_congr rfl fun k _ => by
      show C.h ω k * (∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l)) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
  have e2 : ∑ k, (starRingEnd ℂ) (C.h ω k) * C.V ω k
      = ∑ k, ∑ l, C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) := by
    have step : ∀ k : κ, (starRingEnd ℂ) (C.h ω k) * C.V ω k
        = ∑ m, C.h ω m * C.B ω m k * (starRingEnd ℂ) (C.h ω k) := by
      intro k
      show (starRingEnd ℂ) (C.h ω k) * (∑ m, C.h ω m * C.B ω m k) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun k _ => step k]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun k _ => C.coord_mul_dA_add_dB ω k, Finset.sum_add_distrib, e1, e2,
    hD]
  ring

end chaos_RowChaos

namespace chaos_RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : chaos_RowChaos S κ)

/-! #### The master integration-by-parts identity -/

section IBP

variable (hG : gaussPoly_GaussIBP S)
include hG

/-- **The master identity.**  For any tame `F` whose derivatives along the two coordinates of
each row index are `FA k`, `FB k`,

`2 ∫ Q F = ∑_k w_k ∫ (∂_{a_k}Q · ∂_{a_k}F + ∂_{b_k}Q · ∂_{b_k}F)`.

This is Gaussian integration by parts applied once to each of the `2|κ|` coordinates of the row,
using Euler's identity `∑_α ω_α ∂_α Q = 2(Q + ∑_k σ_k B_{kk})` to produce `Q` on the left and
`∂_α ∂_α Q = 2 r² B_{kk}` to cancel the centring constant. -/
theorem integral_chaos_mul {F : Sample ι → ℂ} {FA FB : κ → Sample ι → ℂ}
    (hF : gaussPoly_Tame F) (hFA : ∀ k, gaussPoly_Tame (FA k)) (hFB : ∀ k, gaussPoly_Tame (FB k))
    (hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)))
    (hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false))) :
    2 * ∫ ω, C.chaos ω * F ω ∂(gaussLaw S)
      = ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S) := by
  classical
  have htB : ∀ k : κ, gaussPoly_Tame fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω := fun k =>
    ((gaussPoly_Tame.const (ι := ι) (2 * (C.r : ℂ) ^ 2)).mul (C.tameB k k)).mul hF
  have htsg : ∀ k : κ, gaussPoly_Tame fun ω => (C.sg k : ℂ) * C.B ω k k * F ω := fun k =>
    ((gaussPoly_Tame.const (ι := ι) ((C.sg k : ℂ))).mul (C.tameB k k)).mul hF
  have hcast : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2) = ((C.sg k : ℝ) : ℂ) := by
    intro k
    have : C.sg k = 2 * C.r ^ 2 * C.w k := rfl
    rw [this]; push_cast; ring
  -- the two Stein identities at the row index `k`
  have hIA : ∀ k : κ, ∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(gaussLaw S)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(gaussLaw S) := by
    intro k
    have hst := hG.stein (C.co k true) (fun ω => C.dA ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dA ω k * FA k ω)
      ((C.tamedA k).mul hF) ((htB k).add ((C.tamedA k).mul (hFA k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedA k).mul (hFA k)).integrable hG), mul_add]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dA_true k ω).fun_mul (hdFA k ω)
      simp only [hself] at hmul
      exact hmul
  have hIB : ∀ k : κ, ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(gaussLaw S)
      = ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(gaussLaw S) := by
    intro k
    have hst := hG.stein (C.co k false) (fun ω => C.dB ω k * F ω)
      (fun ω => 2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω + C.dB ω k * FB k ω)
      ((C.tamedB k).mul hF) ((htB k).add ((C.tamedB k).mul (hFB k))) ?_
    · rw [hst, MeasureTheory.integral_add ((htB k).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG), mul_add]
      have hgv : ((coordVar S (C.co k false) : ℝ) : ℂ) = ((C.w k : ℝ) : ℂ) := by
        rw [C.gvar_tag k]; rfl
      rw [hgv]
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      have hpt : ((C.w k : ℝ) : ℂ) * (2 * (C.r : ℂ) ^ 2 * C.B ω k k * F ω)
          = ((C.sg k : ℝ) : ℂ) * C.B ω k k * F ω := by rw [← hcast k]; ring
      exact hpt
    · intro ω
      have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
        Function.update_eq_self _ ω
      have hmul := (C.hasDerivAt_dB_false k ω).fun_mul (hdFB k ω)
      simp only [hself] at hmul
      exact hmul
  -- the left-hand side, by Euler's identity
  have hEuler : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(gaussLaw S)
      = ∑ k, (∫ ω, (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) ∂(gaussLaw S)
        + ∫ ω, (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) ∂(gaussLaw S)) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
          + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) := by
      intro ω
      rw [← C.sum_coord_mul_deriv ω, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hti : ∀ k : κ, gaussPoly_Tame fun ω => (ω (C.co k true) : ℂ) * (C.dA ω k * F ω) :=
      fun k => (gaussPoly_Tame.coord (C.co k true)).mul ((C.tamedA k).mul hF)
    have hti' : ∀ k : κ, gaussPoly_Tame fun ω => (ω (C.co k false) : ℂ) * (C.dB ω k * F ω) :=
      fun k => (gaussPoly_Tame.coord (C.co k false)).mul ((C.tamedB k).mul hF)
    calc ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(gaussLaw S)
        = ∫ ω, ∑ k, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(gaussLaw S) := by
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = ∑ k, ∫ ω, ((ω (C.co k true) : ℂ) * (C.dA ω k * F ω)
            + (ω (C.co k false) : ℂ) * (C.dB ω k * F ω)) ∂(gaussLaw S) :=
          MeasureTheory.integral_finsetSum _ fun k _ => ((hti k).add (hti' k)).integrable hG
      _ = _ := Finset.sum_congr rfl fun k _ =>
          MeasureTheory.integral_add ((hti k).integrable hG) ((hti' k).integrable hG)
  -- the left-hand side, expanded
  have hsplit : ∫ ω, (2 * (C.chaos ω + C.cen ω) * F ω) ∂(gaussLaw S)
      = 2 * ∫ ω, C.chaos ω * F ω ∂(gaussLaw S) + 2 * ∫ ω, C.cen ω * F ω ∂(gaussLaw S) := by
    have hptw : ∀ ω, 2 * (C.chaos ω + C.cen ω) * F ω
        = 2 * (C.chaos ω * F ω) + 2 * (C.cen ω * F ω) := fun ω => by ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw),
      MeasureTheory.integral_add
        (((gaussPoly_Tame.const (ι := ι) 2).mul (C.tamechaos.mul hF)).integrable hG)
        (((gaussPoly_Tame.const (ι := ι) 2).mul (C.tamecen.mul hF)).integrable hG),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the centring constant
  have hcen : ∑ k, ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
      = ∫ ω, C.cen ω * F ω ∂(gaussLaw S) := by
    rw [← MeasureTheory.integral_finsetSum _ fun k _ => (htsg k).integrable hG]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show _ = (∑ k, (C.sg k : ℂ) * C.B ω k k) * F ω
    rw [Finset.sum_mul]
  -- put everything together
  have hkey := hEuler
  rw [hsplit] at hkey
  rw [Finset.sum_congr rfl fun k _ => by rw [hIA k, hIB k]] at hkey
  have hrearr : ∑ k, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
        + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(gaussLaw S))
      + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
        + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(gaussLaw S)))
      = 2 * ∫ ω, C.cen ω * F ω ∂(gaussLaw S)
        + ∑ k, (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S) := by
    have hstep : ∀ k : κ, ((∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
          + (C.w k : ℂ) * ∫ ω, C.dA ω k * FA k ω ∂(gaussLaw S))
        + (∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
          + (C.w k : ℂ) * ∫ ω, C.dB ω k * FB k ω ∂(gaussLaw S)))
        = 2 * ∫ ω, (C.sg k : ℂ) * C.B ω k k * F ω ∂(gaussLaw S)
          + (C.w k : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S) := by
      intro k
      rw [MeasureTheory.integral_add (((C.tamedA k).mul (hFA k)).integrable hG)
        (((C.tamedB k).mul (hFB k)).integrable hG)]
      ring
    rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_add_distrib, ← Finset.mul_sum, hcen]
  rw [hrearr] at hkey
  have := hkey
  linear_combination this

end IBP

/-! #### The two quadratic sums -/

theorem eps_sq_complex (k : κ) : ((C.eps k : ℂ)) ^ 2 = 1 := by
  have h := C.eps_sq k
  have h2 : ((C.eps k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [h]
  push_cast at h2
  exact h2

theorem sg_complex (k : κ) : ((C.sg k : ℝ) : ℂ) = 2 * (C.r : ℂ) ^ 2 * ((C.w k : ℝ) : ℂ) := by
  show ((2 * C.r ^ 2 * C.w k : ℝ) : ℂ) = _
  push_cast; ring

theorem conj_dA (ω : Sample ι) (k : κ) : (starRingEnd ℂ) (C.dA ω k)
    = (C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) ((C.r : ℂ) * (C.U ω k + C.V ω k)) = _
  simp [Complex.conj_ofReal]

theorem conj_dB (ω : Sample ι) (k : κ) : (starRingEnd ℂ) (C.dB ω k)
    = (-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
      ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)) := by
  show (starRingEnd ℂ) (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) = _
  simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `∑_k w_k ((∂_{a_k}Q)² + (∂_{b_k}Q)²) = 2 R`. -/
theorem sum_w_sq (ω : Sample ι) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2) = 2 * C.Rq ω := by
  have hR : (2 : ℂ) * C.Rq ω = ∑ k, 2 * (((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) := by
    show (2 : ℂ) * (∑ k, ((C.sg k : ℝ) : ℂ) * C.U ω k * C.V ω k) = _
    rw [Finset.mul_sum]
  rw [hR]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hes := C.eps_sq_complex k
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [C.sg_complex k]
  show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) ^ 2
      + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) ^ 2) = _
  linear_combination (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2
      * (C.eps k : ℂ) ^ 2) * hI
    - (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.U ω k - C.V ω k) ^ 2) * hes

/-- `∑_k w_k (|∂_{a_k}Q|² + |∂_{b_k}Q|²) = T`. -/
theorem sum_w_normSq (ω : Sample ι) :
    ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) = ((C.Tq ω : ℝ) : ℂ) := by
  have hstep : ∀ k : κ, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
      + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))
      = ((C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) := by
    intro k
    have hU : ((‖C.U ω k‖ ^ 2 : ℝ) : ℂ) = C.U ω k * (starRingEnd ℂ) (C.U ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have hV : ((‖C.V ω k‖ ^ 2 : ℝ) : ℂ) = C.V ω k * (starRingEnd ℂ) (C.V ω k) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    rw [Complex.ofReal_mul, Complex.ofReal_add, hU, hV, C.sg_complex k, C.conj_dA, C.conj_dB]
    have hes := C.eps_sq_complex k
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    show ((C.w k : ℝ) : ℂ) * (((C.r : ℂ) * (C.U ω k + C.V ω k)) *
          ((C.r : ℂ) * ((starRingEnd ℂ) (C.U ω k) + (starRingEnd ℂ) (C.V ω k)))
        + (((C.r : ℂ) * (C.eps k : ℂ) * Complex.I) * (C.U ω k - C.V ω k)) *
          ((-((C.r : ℂ) * (C.eps k : ℂ) * Complex.I)) *
            ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) = _
    linear_combination (-(((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2 * (C.eps k : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k))))) * hI
      + (((C.w k : ℝ) : ℂ) * (C.r : ℂ) ^ 2
        * ((C.U ω k - C.V ω k) * ((starRingEnd ℂ) (C.U ω k) - (starRingEnd ℂ) (C.V ω k)))) * hes
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Complex.ofReal_sum]
  rfl

theorem tameRq : gaussPoly_Tame C.Rq :=
  gaussPoly_Tame.sum _ fun k _ =>
    (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul (C.tameU k) |>.mul (C.tameV k)

theorem tameTq : gaussPoly_Tame fun ω => ((C.Tq ω : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω : ℝ) : ℂ))
      = fun ω => ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
        + C.dB ω k * (starRingEnd ℂ) (C.dB ω k)) := by
    funext ω; rw [C.sum_w_normSq ω]
  rw [hfun]
  exact gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.w k : ℝ) : ℂ)).mul
    (((C.tamedA k).mul (C.tamedA k).conj).add ((C.tamedB k).mul (C.tamedB k).conj))

/-! #### The moment recursion -/

section Recursion

variable (hG : gaussPoly_GaussIBP S)
include hG

/-- **The moment recursion.**  Integration by parts once in each row coordinate, applied to
`F = Q^q \bar Q^{q+1}`, gives

`2 E[|Q|^{2(q+1)}] = 2q E[R Q^{q-1} \bar Q^{q+1}] + (q+1) E[T Q^q \bar Q^q]`,

with `R = ∑_k σ_k U_k V_k` and `T = ∑_k σ_k (|U_k|² + |V_k|²)`.  Since `‖R‖ ≤ T/2` this is the
Hanson–Wright recursion `E|Q|^{2p} ≤ (2p-1)/2 · E[T |Q|^{2p-2}]`. -/
theorem moment_recursion (q : ℕ) :
    2 * ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(gaussLaw S)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(gaussLaw S)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(gaussLaw S) := by
  classical
  set F : Sample ι → ℂ :=
    fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) with hFdef
  set FA : κ → Sample ι → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dA ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dA ω k)) with hFAdef
  set FB : κ → Sample ι → ℂ := fun k ω =>
    ((q : ℕ) : ℂ) * C.chaos ω ^ (q - 1) * C.dB ω k * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)
      + C.chaos ω ^ q * (((q + 1 : ℕ) : ℂ) * (starRingEnd ℂ) (C.chaos ω) ^ q
        * (starRingEnd ℂ) (C.dB ω k)) with hFBdef
  have hFt : gaussPoly_Tame F := (C.tamechaos.pow q).mul (C.tamechaos.conj.pow (q + 1))
  have hFAt : ∀ k, gaussPoly_Tame (FA k) := fun k =>
    ((((gaussPoly_Tame.const (ι := ι) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedA k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((gaussPoly_Tame.const (ι := ι) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedA k).conj))
  have hFBt : ∀ k, gaussPoly_Tame (FB k) := fun k =>
    ((((gaussPoly_Tame.const (ι := ι) ((q : ℕ) : ℂ)).mul (C.tamechaos.pow (q - 1))).mul
        (C.tamedB k)).mul (C.tamechaos.conj.pow (q + 1))).add
      ((C.tamechaos.pow q).mul
        (((gaussPoly_Tame.const (ι := ι) (((q + 1 : ℕ) : ℂ))).mul (C.tamechaos.conj.pow q)).mul
          (C.tamedB k).conj))
  have hdFA : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k true) s)) (FA k ω)
      (ω (C.co k true)) := by
    intro k ω
    have hself : Function.update ω (C.co k true) (ω (C.co k true)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_true k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hdFB : ∀ k ω, HasDerivAt (fun s : ℝ => F (Function.update ω (C.co k false) s)) (FB k ω)
      (ω (C.co k false)) := by
    intro k ω
    have hself : Function.update ω (C.co k false) (ω (C.co k false)) = ω :=
      Function.update_eq_self _ ω
    have h1 := C.hasDerivAt_chaos_false k ω
    have h2 := h1.fun_pow q
    have h3 := (hasDerivAt_conj' h1).fun_pow (q + 1)
    have hmul := h2.fun_mul h3
    simp only [hself, Nat.add_sub_cancel] at hmul
    exact hmul
  have hmain := C.integral_chaos_mul hG hFt hFAt hFBt hdFA hdFB
  -- the left-hand side
  have hL : ∫ ω, C.chaos ω * F ω ∂(gaussLaw S)
      = ∫ ω, C.chaos ω ^ (q + 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1) ∂(gaussLaw S) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show C.chaos ω * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) = _
    ring
  -- the right-hand side, pointwise
  have hptw : ∀ ω : Sample ι, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
      = 2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
        + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q)) := by
    intro ω
    have hsplit : ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω)
        = ((q : ℂ) * (C.chaos ω ^ (q - 1) * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k ^ 2 + C.dB ω k ^ 2))
          + (((q + 1 : ℕ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q))
            * (∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * (starRingEnd ℂ) (C.dA ω k)
                + C.dB ω k * (starRingEnd ℂ) (C.dB ω k))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hFAdef, hFBdef]
      ring
    rw [hsplit, C.sum_w_sq ω, C.sum_w_normSq ω]
    push_cast
    ring
  -- assemble
  have htR : gaussPoly_Tame fun ω => C.Rq ω * (C.chaos ω ^ (q - 1)
      * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) :=
    C.tameRq.mul ((C.tamechaos.pow (q - 1)).mul (C.tamechaos.conj.pow (q + 1)))
  have htT : gaussPoly_Tame fun ω => ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
      * (starRingEnd ℂ) (C.chaos ω) ^ q) :=
    C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))
  have htk : ∀ k : κ, gaussPoly_Tame fun ω =>
      ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) := fun k =>
    (gaussPoly_Tame.const (ι := ι) ((C.w k : ℝ) : ℂ)).mul
      (((C.tamedA k).mul (hFAt k)).add ((C.tamedB k).mul (hFBt k)))
  have hR : ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S)
      = 2 * (q : ℂ) * ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
          * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(gaussLaw S)
        + ((q : ℕ) + 1 : ℂ) * ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
          * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(gaussLaw S) := by
    calc ∑ k, ((C.w k : ℝ) : ℂ) * ∫ ω, (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S)
        = ∑ k, ∫ ω, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S) :=
          Finset.sum_congr rfl fun k _ => (MeasureTheory.integral_const_mul _ _).symm
      _ = ∫ ω, ∑ k, ((C.w k : ℝ) : ℂ) * (C.dA ω k * FA k ω + C.dB ω k * FB k ω) ∂(gaussLaw S) :=
          (MeasureTheory.integral_finsetSum _ fun k _ => (htk k).integrable hG).symm
      _ = ∫ ω, (2 * (q : ℂ) * (C.Rq ω * (C.chaos ω ^ (q - 1)
              * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)))
            + ((q : ℕ) + 1 : ℂ) * (((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q
              * (starRingEnd ℂ) (C.chaos ω) ^ q))) ∂(gaussLaw S) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)
      _ = _ := by
          rw [MeasureTheory.integral_add
            (((gaussPoly_Tame.const (ι := ι) (2 * (q : ℂ))).mul htR).integrable hG)
            (((gaussPoly_Tame.const (ι := ι) ((q : ℕ) + 1 : ℂ)).mul htT).integrable hG),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hL] at hmain
  rw [hmain, hR]

end Recursion

/-! #### The real form of the recursion -/

/-- `E|Q|^{2q}`. -/
noncomputable def mom (q : ℕ) : ℝ := ∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(gaussLaw S)

/-- `E[T |Q|^{2q}]`, the right-hand side of the recursion. -/
noncomputable def momT (q : ℕ) : ℝ := ∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(gaussLaw S)

theorem ofReal_norm_pow (ω : Sample ι) (q : ℕ) :
    ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) = C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q := by
  have h2 : ((‖C.chaos ω‖ ^ 2 : ℝ) : ℂ) = C.chaos ω * (starRingEnd ℂ) (C.chaos ω) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [pow_mul, Complex.ofReal_pow, h2, mul_pow]

theorem tame_ofReal_norm_pow (q : ℕ) :
    gaussPoly_Tame fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q :=
    funext fun ω => C.ofReal_norm_pow ω q
  rw [hfun]
  exact (C.tamechaos.pow q).mul (C.tamechaos.conj.pow q)

theorem tame_ofReal_Tq_mul (q : ℕ) :
    gaussPoly_Tame fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ) := by
  have hfun : (fun ω => ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ))
      = fun ω => ((C.Tq ω : ℝ) : ℂ) *
        (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) := by
    funext ω
    rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]
  rw [hfun]
  exact C.tameTq.mul ((C.tamechaos.pow q).mul (C.tamechaos.conj.pow q))

omit [DecidableEq κ] in
theorem ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.sq_norm]

theorem mom_nonneg (q : ℕ) : 0 ≤ C.mom q :=
  MeasureTheory.integral_nonneg fun ω => by positivity

theorem momT_nonneg (q : ℕ) : 0 ≤ C.momT q :=
  MeasureTheory.integral_nonneg fun ω => mul_nonneg (C.Tq_nonneg ω) (by positivity)

omit [DecidableEq κ] in
theorem integral_ofReal' (f : Sample ι → ℝ) :
    ∫ ω, ((f ω : ℝ) : ℂ) ∂(gaussLaw S) = ((∫ ω, f ω ∂(gaussLaw S) : ℝ) : ℂ) := by
  have h := _root_.integral_ofReal (𝕜 := ℂ) (f := f) (μ := gaussLaw S)
  simpa using h

theorem integral_chaos_pow (q : ℕ) :
    ∫ ω, C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q ∂(gaussLaw S) = ((C.mom q : ℝ) : ℂ) := by
  show _ = ((∫ ω, ‖C.chaos ω‖ ^ (2 * q) ∂(gaussLaw S) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => ‖C.chaos ω‖ ^ (2 * q))]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun ω => (C.ofReal_norm_pow ω q).symm)

theorem integral_Tq_chaos_pow (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q) ∂(gaussLaw S)
      = ((C.momT q : ℝ) : ℂ) := by
  show _ = ((∫ ω, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) ∂(gaussLaw S) : ℝ) : ℂ)
  rw [← integral_ofReal' (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ((C.Tq ω : ℝ) : ℂ) * (C.chaos ω ^ q * (starRingEnd ℂ) (C.chaos ω) ^ q)
    = ((C.Tq ω * ‖C.chaos ω‖ ^ (2 * q) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, C.ofReal_norm_pow ω q]

section Real

variable (hG : gaussPoly_GaussIBP S)
include hG

theorem integrable_of_tame_ofReal {f : Sample ι → ℝ}
    (hf : gaussPoly_Tame fun ω => ((f ω : ℝ) : ℂ)) :
    Integrable f (gaussLaw S) := by
  simpa using (hf.integrable hG).re

theorem integrable_norm_pow (q : ℕ) :
    Integrable (fun ω => ‖C.chaos ω‖ ^ (2 * q)) (gaussLaw S) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_norm_pow q)

theorem integrable_Tq_mul (q : ℕ) :
    Integrable (fun ω => C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)) (gaussLaw S) :=
  integrable_of_tame_ofReal hG (C.tame_ofReal_Tq_mul q)

/-- The cross term of the recursion is dominated by half the bound `T`. -/
theorem norm_integral_Rq_le (p : ℕ) :
    ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(gaussLaw S)‖
      ≤ C.momT (p + 1) / 2 := by
  have htR : gaussPoly_Tame fun ω => C.Rq ω * (C.chaos ω ^ p
      * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) :=
    C.tameRq.mul ((C.tamechaos.pow p).mul (C.tamechaos.conj.pow (p + 2)))
  have hbnd : ∀ ω : Sample ι,
      ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖
        ≤ 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) := by
    intro ω
    have hnorm : ‖C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)‖
        = ‖C.chaos ω‖ ^ (2 * (p + 1)) := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
      congr 1
      omega
    rw [norm_mul, hnorm]
    have h1 := C.norm_Rq_le ω
    have h2 : (0 : ℝ) ≤ ‖C.chaos ω‖ ^ (2 * (p + 1)) := by positivity
    nlinarith
  calc ‖∫ ω, C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2)) ∂(gaussLaw S)‖
      ≤ ∫ ω, ‖C.Rq ω * (C.chaos ω ^ p * (starRingEnd ℂ) (C.chaos ω) ^ (p + 2))‖ ∂(gaussLaw S) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 1 / 2 * (C.Tq ω * ‖C.chaos ω‖ ^ (2 * (p + 1))) ∂(gaussLaw S) :=
        MeasureTheory.integral_mono ((htR.integrable hG).norm)
          ((C.integrable_Tq_mul hG (p + 1)).const_mul _) hbnd
    _ = C.momT (p + 1) / 2 := by
        rw [MeasureTheory.integral_const_mul]
        show 1 / 2 * C.momT (p + 1) = _
        ring

/-- **The Hanson–Wright recursion, real form**:
`2 E|Q|^{2(q+1)} ≤ (2q+1) E[T |Q|^{2q}]`. -/
theorem two_mul_mom_succ_le (q : ℕ) :
    2 * C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) * C.momT q := by
  have hrec := C.moment_recursion hG q
  rw [C.integral_chaos_pow (q + 1), C.integral_Tq_chaos_pow q] at hrec
  set X : ℂ := ∫ ω, C.Rq ω * (C.chaos ω ^ (q - 1)
    * (starRingEnd ℂ) (C.chaos ω) ^ (q + 1)) ∂(gaussLaw S) with hX
  have hXb : 2 * (q : ℝ) * ‖X‖ ≤ (q : ℝ) * C.momT q := by
    rcases q with _ | p
    · simp
    · have hq : ‖X‖ ≤ C.momT (p + 1) / 2 := by
        rw [hX]
        have hidx : (p + 1 : ℕ) - 1 = p := by omega
        have hidx2 : (p + 1 : ℕ) + 1 = p + 2 := by omega
        rw [hidx, hidx2]
        exact C.norm_integral_Rq_le hG p
      have hm : 0 ≤ C.momT (p + 1) := C.momT_nonneg (p + 1)
      push_cast
      nlinarith [norm_nonneg X]
  have hnorm : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖
      ≤ 2 * (q : ℝ) * ‖X‖ + ((q : ℝ) + 1) * C.momT q := by
    rw [hrec]
    have h1 : ‖2 * (q : ℂ) * X + ((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖
        ≤ ‖2 * (q : ℂ) * X‖ + ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ := norm_add_le _ _
    have h2 : ‖2 * (q : ℂ) * X‖ = 2 * (q : ℝ) * ‖X‖ := by
      rw [norm_mul, norm_mul]
      simp
    have h3 : ‖((q : ℕ) + 1 : ℂ) * ((C.momT q : ℝ) : ℂ)‖ = ((q : ℝ) + 1) * C.momT q := by
      have hc : ((q : ℕ) + 1 : ℂ) = (((q : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (C.momT_nonneg q),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)]
    linarith
  have hlhs : ‖2 * ((C.mom (q + 1) : ℝ) : ℂ)‖ = 2 * C.mom (q + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (C.mom_nonneg (q + 1))]
    simp
  rw [hlhs] at hnorm
  linarith

/-! #### The variance bound `Vq` -/

/-- The variance bound `∑_{k,l} σ_k ‖B_{kl}‖² σ_l` of the quadratic large deviation estimate. -/
noncomputable def Vq (ω : Sample ι) : ℝ := ∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l

omit hG in
theorem Vq_complex (ω : Sample ι) : ((C.Vq ω : ℝ) : ℂ)
    = ∑ k, ∑ l, ((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ) *
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)) := by
  show ((∑ k, ∑ l, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ofReal_normSq]
  ring

omit hG in
theorem tame_ofReal_Vq : gaussPoly_Tame fun ω => ((C.Vq ω : ℝ) : ℂ) := by
  rw [funext fun ω => C.Vq_complex ω]
  exact gaussPoly_Tame.sum _ fun k _ => gaussPoly_Tame.sum _ fun l _ =>
    (gaussPoly_Tame.const (ι := ι) (((C.sg k : ℝ) : ℂ) * ((C.sg l : ℝ) : ℂ))).mul
      ((C.tameB k l).mul (C.tameB k l).conj)

omit hG in
theorem Tq_complex (ω : Sample ι) : ((C.Tq ω : ℝ) : ℂ)
    = ∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.U ω k)
      + C.V ω k * (starRingEnd ℂ) (C.V ω k)) := by
  show ((∑ k, C.sg k * (‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]

/-! #### Closing the recursion: `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` -/

/-- `E[T^q]`, the positive-chaos moment that the recursion reduces everything to. -/
noncomputable def momTpow (q : ℕ) : ℝ := ∫ ω, C.Tq ω ^ q ∂(gaussLaw S)

theorem integrable_Tq_pow (q : ℕ) : Integrable (fun ω => C.Tq ω ^ q) (gaussLaw S) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω => ((C.Tq ω ^ q : ℝ) : ℂ)) = fun ω => ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tameTq.pow q

omit hG in
theorem momTpow_nonneg (q : ℕ) : 0 ≤ C.momTpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Tq_nonneg ω) q

/-- **Hanson–Wright, the moment bound.**  `E|Q|^{2p} ≤ (2p−1)^p E[T^p]` for `p ≥ 1`.

The recursion `2E|Q|^{2(q+1)} ≤ (2q+1)E[T|Q|^{2q}]` is closed by the pointwise Young inequality
`gaussPoly_young_pow` with the *rational* parameter `K = 2q+1`, which keeps every exponent a
natural number and needs no Hölder inequality. -/
theorem mom_succ_le (q : ℕ) :
    C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := by
  set K : ℝ := 2 * (q : ℝ) + 1 with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  -- the pointwise Young inequality
  have hpt : ∀ ω : Sample ι, C.Tq ω * ‖C.chaos ω‖ ^ (2 * q)
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1)) := by
    intro ω
    have hT := C.Tq_nonneg ω
    have hy := gaussPoly_young_pow q (mul_nonneg hT hK0.le) (sq_nonneg ‖C.chaos ω‖)
    rw [mul_pow] at hy
    have hg : ∀ j : ℕ, ‖C.chaos ω‖ ^ (2 * j) = (‖C.chaos ω‖ ^ 2) ^ j := fun j => pow_mul _ 2 j
    rw [hg q, hg (q + 1)]
    have hmul : (0 : ℝ) < ((q : ℝ) + 1) * K := by positivity
    refine le_of_mul_le_mul_left ?_ hmul
    have hleft : ((q : ℝ) + 1) * K * (C.Tq ω * (‖C.chaos ω‖ ^ 2) ^ q)
        = ((q : ℝ) + 1) * (C.Tq ω * K * (‖C.chaos ω‖ ^ 2) ^ q) := by ring
    have hrhs : ((q : ℝ) + 1) * K * ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
          + ((q : ℝ) / (((q : ℝ) + 1) * K)) * (‖C.chaos ω‖ ^ 2) ^ (q + 1))
        = C.Tq ω ^ (q + 1) * K ^ (q + 1) + (q : ℝ) * (‖C.chaos ω‖ ^ 2) ^ (q + 1) := by
      field_simp
      ring
    rw [hleft, hrhs]
    exact hy
  -- integrate
  have hi1 := C.integrable_Tq_pow hG (q + 1)
  have hi2 := C.integrable_norm_pow hG (q + 1)
  have hmomT : C.momT q ≤ (K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
      + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1) := by
    calc C.momT q ≤ ∫ ω, ((K ^ q / ((q : ℝ) + 1)) * C.Tq ω ^ (q + 1)
            + ((q : ℝ) / (((q : ℝ) + 1) * K)) * ‖C.chaos ω‖ ^ (2 * (q + 1))) ∂(gaussLaw S) :=
          MeasureTheory.integral_mono (C.integrable_Tq_mul hG q)
            ((hi1.const_mul _).add (hi2.const_mul _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
  -- close the recursion
  have hrec := C.two_mul_mom_succ_le hG q
  rw [← hKdef] at hrec
  have hm := C.mom_nonneg (q + 1)
  have ht := C.momTpow_nonneg (q + 1)
  have hKmul : K * ((K ^ q / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.mom (q + 1))
      = (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    field_simp
    ring
  have hchain : 2 * C.mom (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.mom (q + 1) := by
    refine hrec.trans ?_
    rw [← hKmul]
    exact mul_le_mul_of_nonneg_left hmomT hK0.le
  have hB : (q : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hq1]; linarith
  have hA : K ^ (q + 1) / ((q : ℝ) + 1) ≤ K ^ (q + 1) := by
    rw [div_le_iff₀ hq1]
    nlinarith [pow_nonneg hK0.le (q + 1), Nat.cast_nonneg (α := ℝ) q]
  have h1 : (q : ℝ) / ((q : ℝ) + 1) * C.mom (q + 1) ≤ C.mom (q + 1) := by
    nlinarith [hm, hB]
  have h3 : K ^ (q + 1) / ((q : ℝ) + 1) * C.momTpow (q + 1)
      ≤ K ^ (q + 1) * C.momTpow (q + 1) := mul_le_mul_of_nonneg_right hA ht
  linarith

end Real

end chaos_RowChaos

namespace chaos_RowChaos

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (C : chaos_RowChaos S κ)

/-! ### The Wirtinger derivation along the row -/

/-- `D_l Z = r(∂_{a_l}Z − ε_l i ∂_{b_l}Z)`, as a function of the two partials `a`, `b`. -/
noncomputable def wirtVal (l : κ) (a b : ℂ) : ℂ :=
  (C.r : ℂ) * (a - ((C.eps l : ℂ) * Complex.I) * b)

variable {C}

theorem wirtVal_add (l : κ) (a b a' b' : ℂ) :
    C.wirtVal l (a + a') (b + b') = C.wirtVal l a b + C.wirtVal l a' b' := by
  simp only [wirtVal]; ring

theorem wirtVal_smul (l : κ) (z a b : ℂ) :
    C.wirtVal l (z * a) (z * b) = z * C.wirtVal l a b := by
  simp only [wirtVal]; ring

theorem wirtVal_sum {α : Type*} (s : Finset α) (l : κ) (A B : α → ℂ) :
    C.wirtVal l (∑ j ∈ s, A j) (∑ j ∈ s, B j) = ∑ j ∈ s, C.wirtVal l (A j) (B j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wirtVal]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
        wirtVal_add, ih]

/-! ### The master identity `∫ \bar h_l Z = w_l ∫ D_l Z` -/

variable (C)

/-- **Gaussian integration by parts along one row entry.**  For every tame `Z` whose partials
along the two coordinates of the index `l` are `ZA`, `ZB`,

`∫ \bar h_l · Z = w_l ∫ D_l Z`,  `D_l Z = r(ZA − ε_l i ZB)`.

This is the field `stein` of `gaussPoly_GaussIBP` applied once to each of the two coordinates,
combined with `\bar h_l = r(ω_{a_l} − ε_l i ω_{b_l})`. -/
theorem integral_conj_h_mul_gen (hG : gaussPoly_GaussIBP S) {Z ZA ZB : Sample ι → ℂ} (l : κ)
    (hZ : gaussPoly_Tame Z) (hZA : gaussPoly_Tame ZA) (hZB : gaussPoly_Tame ZB)
    (hdA : ∀ ω, HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co l true) s)) (ZA ω)
      (ω (C.co l true)))
    (hdB : ∀ ω, HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co l false) s)) (ZB ω)
      (ω (C.co l false))) :
    ∫ ω, (starRingEnd ℂ) (C.h ω l) * Z ω ∂(gaussLaw S)
      = (C.w l : ℂ) * ∫ ω, C.wirtVal l (ZA ω) (ZB ω) ∂(gaussLaw S) := by
  have hA : ∫ ω, (ω (C.co l true) : ℂ) * Z ω ∂(gaussLaw S)
      = (C.w l : ℂ) * ∫ ω, ZA ω ∂(gaussLaw S) :=
    hG.stein (C.co l true) Z ZA hZ hZA hdA
  have hB : ∫ ω, (ω (C.co l false) : ℂ) * Z ω ∂(gaussLaw S)
      = (C.w l : ℂ) * ∫ ω, ZB ω ∂(gaussLaw S) := by
    have h := hG.stein (C.co l false) Z ZB hZ hZB hdB
    have hgv : ((coordVar S (C.co l false) : ℝ) : ℂ) = ((C.w l : ℝ) : ℂ) := by
      rw [C.gvar_tag l]; rfl
    rw [h, hgv]
  have hi1 : Integrable (fun ω : Sample ι => (ω (C.co l true) : ℂ) * Z ω) (gaussLaw S) :=
    ((gaussPoly_Tame.coord (C.co l true)).mul hZ).integrable hG
  have hi2 : Integrable (fun ω : Sample ι => (ω (C.co l false) : ℂ) * Z ω) (gaussLaw S) :=
    ((gaussPoly_Tame.coord (C.co l false)).mul hZ).integrable hG
  have hiA : Integrable ZA (gaussLaw S) := hZA.integrable hG
  have hiB : Integrable ZB (gaussLaw S) := hZB.integrable hG
  calc ∫ ω, (starRingEnd ℂ) (C.h ω l) * Z ω ∂(gaussLaw S)
      = ∫ ω, ((C.r : ℂ) * ((ω (C.co l true) : ℂ) * Z ω)
          - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) *
            ((ω (C.co l false) : ℂ) * Z ω)) ∂(gaussLaw S) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [C.conj_h]; ring
    _ = (C.r : ℂ) * ∫ ω, (ω (C.co l true) : ℂ) * Z ω ∂(gaussLaw S)
        - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) *
          ∫ ω, (ω (C.co l false) : ℂ) * Z ω ∂(gaussLaw S) := by
        rw [integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = (C.w l : ℂ) * ((C.r : ℂ) * ∫ ω, ZA ω ∂(gaussLaw S)
          - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) * ∫ ω, ZB ω ∂(gaussLaw S)) := by
        rw [hA, hB]; ring
    _ = (C.w l : ℂ) * ∫ ω, C.wirtVal l (ZA ω) (ZB ω) ∂(gaussLaw S) := by
        congr 1
        rw [show (fun ω => C.wirtVal l (ZA ω) (ZB ω))
            = fun ω => (C.r : ℂ) * ZA ω
              - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) * ZB ω from by
          funext ω; simp only [wirtVal]; ring]
        rw [integral_sub (hiA.const_mul _) (hiB.const_mul _), integral_const_mul,
          integral_const_mul]

/-- Right-hand scalar: `D_l (a·z, b·z) = (D_l(a,b))·z`. -/
theorem wirtVal_mul_right (l : κ) (z a b : ℂ) :
    C.wirtVal l (a * z) (b * z) = C.wirtVal l a b * z := by
  simp only [wirtVal]; ring

/-! ### The partials of `T` along the row -/

/-- `∂T/∂a_l`, in complex form. -/
noncomputable def TA (l : κ) (ω : Sample ι) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
      + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
      + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k))

/-- `∂T/∂b_l`, in complex form. -/
noncomputable def TB (l : κ) (ω : Sample ι) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
      + C.U ω k *
        (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
      + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k *
        (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k))

theorem tameTA (l : κ) : gaussPoly_Tame (C.TA l) :=
  gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul
    (((((C.tameB k l).mul (gaussPoly_Tame.const (ι := ι) ((C.r : ℂ)))).mul (C.tameU k).conj).add
      ((C.tameU k).mul (((C.tameB k l).mul (gaussPoly_Tame.const (ι := ι) ((C.r : ℂ)))).conj))).add
      (((gaussPoly_Tame.const (ι := ι) ((C.r : ℂ))).mul (C.tameB l k)).mul (C.tameV k).conj) |>.add
      ((C.tameV k).mul (((gaussPoly_Tame.const (ι := ι) ((C.r : ℂ))).mul (C.tameB l k)).conj)))

theorem tameTB (l : κ) : gaussPoly_Tame (C.TB l) :=
  gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul
    (((((C.tameB k l).mul (gaussPoly_Tame.const (ι := ι)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).mul (C.tameU k).conj).add
      ((C.tameU k).mul (((C.tameB k l).mul (gaussPoly_Tame.const (ι := ι)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).conj))).add
      (((gaussPoly_Tame.const (ι := ι) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
        (C.tameB l k)).mul (C.tameV k).conj) |>.add
      ((C.tameV k).mul (((gaussPoly_Tame.const (ι := ι)
        ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul (C.tameB l k)).conj)))

theorem hasDerivAt_Tq_true (l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => ((C.Tq (Function.update ω (C.co l true) s) : ℝ) : ℂ))
      (C.TA l ω) (ω (C.co l true)) := by
  have hfun : (fun s : ℝ => ((C.Tq (Function.update ω (C.co l true) s) : ℝ) : ℂ))
      = fun s : ℝ => ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l true) s) k)) := by
    funext s; exact C.Tq_complex _
  rw [hfun]
  have hself := Function.update_eq_self (C.co l true) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l true) s) k)))
      (((C.sg k : ℝ) : ℂ) *
        ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
          + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
          + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
          + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k)))
      (ω (C.co l true)) := by
    intro k
    have hU := C.hasDerivAt_U_true l k ω
    have hV := C.hasDerivAt_V_true l k ω
    have hUc := hasDerivAt_conj' hU
    have hVc := hasDerivAt_conj' hV
    have h1 := hU.fun_mul hUc
    have h2 := hV.fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k
  exact hsum

theorem hasDerivAt_Tq_false (l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => ((C.Tq (Function.update ω (C.co l false) s) : ℝ) : ℂ))
      (C.TB l ω) (ω (C.co l false)) := by
  have hfun : (fun s : ℝ => ((C.Tq (Function.update ω (C.co l false) s) : ℝ) : ℂ))
      = fun s : ℝ => ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l false) s) k)) := by
    funext s; exact C.Tq_complex _
  rw [hfun]
  have hself := Function.update_eq_self (C.co l false) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l false) s) k)))
      (((C.sg k : ℝ) : ℂ) *
        ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
          + C.U ω k *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
          + C.V ω k *
            (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k)))
      (ω (C.co l false)) := by
    intro k
    have hU := C.hasDerivAt_U_false l k ω
    have hV := C.hasDerivAt_V_false l k ω
    have hUc := hasDerivAt_conj' hU
    have hVc := hasDerivAt_conj' hV
    have h1 := hU.fun_mul hUc
    have h2 := hV.fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k
  exact hsum

variable {C}

/-- The `k`-th summand of `D_l T`: `D_l(U_k\bar U_k + V_k\bar V_k)
= 2r²(U_k\bar B_{kl} + B_{lk}\bar V_k)`. -/
theorem wirtVal_term (l k : κ) (ω : Sample ι) :
    C.wirtVal l
      ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
        + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
        + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k))
      ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
        + C.U ω k *
          (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
        + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
        + C.V ω k *
          (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k))
      = 2 * (C.r : ℂ) ^ 2 *
        (C.U ω k * (starRingEnd ℂ) (C.B ω k l) + C.B ω l k * (starRingEnd ℂ) (C.V ω k)) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination ((C.r : ℂ) ^ 2 *
    (C.B ω k l * (starRingEnd ℂ) (C.U ω k) - C.U ω k * (starRingEnd ℂ) (C.B ω k l)
      - C.B ω l k * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k * (starRingEnd ℂ) (C.B ω l k))) * hq

/-- **`D_l T = 2r² ∑_k σ_k (U_k \bar B_{kl} + B_{lk} \bar V_k)`.**  Both `U` and `\bar V` are
killed by `D_l`, so only `B` survives — this is the whole point of the derivation. -/
theorem wirtVal_TA_TB (l : κ) (ω : Sample ι) :
    C.wirtVal l (C.TA l ω) (C.TB l ω)
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.V ω k)) := by
  rw [TA, TB, wirtVal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wirtVal_smul, wirtVal_term]
  ring

/-! ### `T` as a linear form in the row: `T = ∑_l \bar h_l W_l` -/

variable (C)

/-- `W_l = ∑_k σ_k(B_{kl}\bar U_k + V_k \bar B_{lk})`, the coefficient of `\bar h_l` in `T`. -/
noncomputable def Wt (l : κ) (ω : Sample ι) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.U ω k)
    + C.V ω k * (starRingEnd ℂ) (C.B ω l k))

theorem tameWt (l : κ) : gaussPoly_Tame (C.Wt l) :=
  gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul (C.tameU k).conj).add ((C.tameV k).mul (C.tameB l k).conj))

variable {C}

/-- **`T` is a linear form in the conjugated row.**  Both `U_k\bar U_k` and `V_k\bar V_k`
contain exactly one factor `\bar h`, so `T = ∑_l \bar h_l W_l`.  This is what makes the
integration by parts of `E[T^{q+1}]` possible. -/
theorem Tq_eq_sum_conj_h_mul (ω : Sample ι) :
    ((C.Tq ω : ℝ) : ℂ) = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω := by
  have hU : ∀ k : κ, C.U ω k = ∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l) := fun _ => rfl
  have hV : ∀ k : κ, (starRingEnd ℂ) (C.V ω k)
      = ∑ l, (starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.B ω l k) := by
    intro k
    change (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => map_mul _ _ _
  have hexp : (∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω)
      = ∑ l, ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.U ω k)
          + C.V ω k * ((starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.B ω l k))) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Wt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [C.Tq_complex ω, hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  nth_rewrite 1 [hU k]
  rw [hV k, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The `k`-th summand of `D_l W_l`. -/
theorem wirtVal_termW (l k : κ) (ω : Sample ι) :
    C.wirtVal l
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
        + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
          (starRingEnd ℂ) (C.B ω l k))
      = 2 * (C.r : ℂ) ^ 2 * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
        + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (-((C.r : ℂ) ^ 2 *
    (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
      + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)))) * hq

/-- **`D_l W_l = 2r² ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²)`.** -/
theorem wirtVal_Wt (l : κ) (ω : Sample ι) :
    C.wirtVal l
      (∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k)))
      (∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
            (starRingEnd ℂ) (C.B ω l k)))
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) := by
  rw [wirtVal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wirtVal_smul, wirtVal_termW]
  ring

/-! ### The partials of `W_l` -/

variable (C)

/-- `∂W_l/∂a_l`. -/
noncomputable def WA (l : κ) (ω : Sample ι) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
    + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))

/-- `∂W_l/∂b_l`. -/
noncomputable def WB (l : κ) (ω : Sample ι) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
      + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))

theorem tameWA (l : κ) : gaussPoly_Tame (C.WA l) :=
  gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul ((C.tameB k l).mul (gaussPoly_Tame.const (ι := ι) ((C.r : ℂ)))).conj).add
      (((gaussPoly_Tame.const (ι := ι) ((C.r : ℂ))).mul (C.tameB l k)).mul (C.tameB l k).conj))

theorem tameWB (l : κ) : gaussPoly_Tame (C.WB l) :=
  gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul ((C.tameB k l).mul (gaussPoly_Tame.const (ι := ι)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).conj).add
      (((gaussPoly_Tame.const (ι := ι) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
        (C.tameB l k)).mul (C.tameB l k).conj))

theorem hasDerivAt_Wt_true (l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.Wt l (Function.update ω (C.co l true) s)) (C.WA l ω)
      (ω (C.co l true)) := by
  have hself := Function.update_eq_self (C.co l true) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.B (Function.update ω (C.co l true) s) k l *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.B (Function.update ω (C.co l true) s) l k)))
      (((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k)))
      (ω (C.co l true)) := by
    intro k
    have hB1 := C.hasDerivAt_B_const l true k l ω
    have hB2 := C.hasDerivAt_B_const l true l k ω
    have hUc := hasDerivAt_conj' (C.hasDerivAt_U_true l k ω)
    have hVc := hasDerivAt_conj' hB2
    have h1 := hB1.fun_mul hUc
    have h2 := (C.hasDerivAt_V_true l k ω).fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    simp only [map_zero]
    ring
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k

theorem hasDerivAt_Wt_false (l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.Wt l (Function.update ω (C.co l false) s)) (C.WB l ω)
      (ω (C.co l false)) := by
  have hself := Function.update_eq_self (C.co l false) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.B (Function.update ω (C.co l false) s) k l *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.B (Function.update ω (C.co l false) s) l k)))
      (((C.sg k : ℝ) : ℂ) *
        (C.B ω k l *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
            (starRingEnd ℂ) (C.B ω l k)))
      (ω (C.co l false)) := by
    intro k
    have hB1 := C.hasDerivAt_B_const l false k l ω
    have hB2 := C.hasDerivAt_B_const l false l k ω
    have hUc := hasDerivAt_conj' (C.hasDerivAt_U_false l k ω)
    have hVc := hasDerivAt_conj' hB2
    have h1 := hB1.fun_mul hUc
    have h2 := (C.hasDerivAt_V_false l k ω).fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    simp only [map_zero]
    ring
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k

variable {C}

/-- `D_l W_l = 2r² ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²)`, in terms of `WA`/`WB`. -/
theorem wirtVal_WA_WB (l : κ) (ω : Sample ι) :
    C.wirtVal l (C.WA l ω) (C.WB l ω)
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) :=
  C.wirtVal_Wt l ω

/-! ### The integration by parts of `E[T^{q+1}]` -/

variable (C)

/-- `Z_{q,l} = W_l · T^q`, the coefficient of `\bar h_l` in `T^{q+1}`. -/
noncomputable def Zt (q : ℕ) (l : κ) (ω : Sample ι) : ℂ :=
  C.Wt l ω * ((C.Tq ω : ℝ) : ℂ) ^ q

/-- `∂Z_{q,l}/∂a_l`. -/
noncomputable def ZA (q : ℕ) (l : κ) (ω : Sample ι) : ℂ :=
  C.WA l ω * ((C.Tq ω : ℝ) : ℂ) ^ q
    + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) * C.TA l ω)

/-- `∂Z_{q,l}/∂b_l`. -/
noncomputable def ZB (q : ℕ) (l : κ) (ω : Sample ι) : ℂ :=
  C.WB l ω * ((C.Tq ω : ℝ) : ℂ) ^ q
    + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) * C.TB l ω)

theorem tameZt (q : ℕ) (l : κ) : gaussPoly_Tame (C.Zt q l) :=
  (C.tameWt l).mul (C.tameTq.pow q)

theorem tameZA (q : ℕ) (l : κ) : gaussPoly_Tame (C.ZA q l) :=
  ((C.tameWA l).mul (C.tameTq.pow q)).add
    ((C.tameWt l).mul
      (((gaussPoly_Tame.const (ι := ι) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul (C.tameTA l)))

theorem tameZB (q : ℕ) (l : κ) : gaussPoly_Tame (C.ZB q l) :=
  ((C.tameWB l).mul (C.tameTq.pow q)).add
    ((C.tameWt l).mul
      (((gaussPoly_Tame.const (ι := ι) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul (C.tameTB l)))

variable {C}

theorem Tq_pow_succ_eq_sum (q : ℕ) (ω : Sample ι) :
    ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω := by
  have h := Tq_eq_sum_conj_h_mul (C := C) ω
  calc ((C.Tq ω : ℝ) : ℂ) ^ (q + 1)
      = ((C.Tq ω : ℝ) : ℂ) ^ q * ((C.Tq ω : ℝ) : ℂ) := pow_succ _ _
    _ = ((C.Tq ω : ℝ) : ℂ) ^ q * ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω := by rw [← h]
    _ = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [Zt]; ring

variable (C)

theorem hasDerivAt_Zt_true (q : ℕ) (l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.Zt q l (Function.update ω (C.co l true) s)) (C.ZA q l ω)
      (ω (C.co l true)) := by
  have hself := Function.update_eq_self (C.co l true) ω
  have hW := C.hasDerivAt_Wt_true l ω
  have hT := (C.hasDerivAt_Tq_true l ω).fun_pow q
  have hmul := hW.fun_mul hT
  simp only [hself] at hmul
  exact hmul

theorem hasDerivAt_Zt_false (q : ℕ) (l : κ) (ω : Sample ι) :
    HasDerivAt (fun s : ℝ => C.Zt q l (Function.update ω (C.co l false) s)) (C.ZB q l ω)
      (ω (C.co l false)) := by
  have hself := Function.update_eq_self (C.co l false) ω
  have hW := C.hasDerivAt_Wt_false l ω
  have hT := (C.hasDerivAt_Tq_false l ω).fun_pow q
  have hmul := hW.fun_mul hT
  simp only [hself] at hmul
  exact hmul

variable {C}

/-- **`D_l Z_{q,l}`**: the diagonal term (which will sum to `2V_q T^q`) plus the cross term. -/
theorem wirtVal_ZA_ZB (q : ℕ) (l : κ) (ω : Sample ι) :
    C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)
      = (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
            (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
              + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q
        + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
            (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
              (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
                + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))) := by
  rw [ZA, ZB, wirtVal_add, wirtVal_mul_right, wirtVal_WA_WB, wirtVal_smul, wirtVal_smul,
    wirtVal_TA_TB]

/-- **The integration by parts of `E[T^{q+1}]`.**  `T^{q+1} = ∑_l \bar h_l Z_{q,l}`, and each
`\bar h_l` is integrated by parts against `Z_{q,l}`. -/
theorem integral_Tq_pow_succ (hG : gaussPoly_GaussIBP S) (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(gaussLaw S)
      = ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(gaussLaw S) := by
  have hint : ∀ l : κ,
      Integrable (fun ω => (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω) (gaussLaw S) :=
    fun l => (((C.tameh l).conj).mul (C.tameZt q l)).integrable hG
  calc ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(gaussLaw S)
      = ∫ ω, ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω ∂(gaussLaw S) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => Tq_pow_succ_eq_sum q ω)
    _ = ∑ l, ∫ ω, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω ∂(gaussLaw S) :=
        integral_finsetSum _ fun l _ => hint l
    _ = ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(gaussLaw S) :=
        Finset.sum_congr rfl fun l _ =>
          C.integral_conj_h_mul_gen hG l (C.tameZt q l) (C.tameZA q l) (C.tameZB q l)
            (C.hasDerivAt_Zt_true q l) (C.hasDerivAt_Zt_false q l)

/-! ### The diagonal term sums to `2 V_q` -/

/-- `∑_l σ_l ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²) = 2V_q`: the two double sums are the same after
swapping the indices. -/
theorem sum_sg_mul_normSq (ω : Sample ι) :
    ∑ l, C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) = 2 * C.Vq ω := by
  have e1 : ∑ l, C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)
      = (∑ l, ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l)
        + ∑ l, ∑ k, C.sg l * ‖C.B ω l k‖ ^ 2 * C.sg k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ l, ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) = C.Vq ω := by
    rw [Vq, Finset.sum_comm]
  have e3 : (∑ l, ∑ k, C.sg l * ‖C.B ω l k‖ ^ 2 * C.sg k) = C.Vq ω := rfl
  rw [e1, e2, e3]; ring

/-- The diagonal part of `∑_l w_l D_l Z_{q,l}` is `2 V_q T^q`. -/
theorem sum_w_diag (q : ℕ) (ω : Sample ι) :
    ∑ l, (C.w l : ℂ) * ((2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q)
      = ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) := by
  have hterm : ∀ l : κ, (C.w l : ℂ) * ((2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q)
      = ((C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) : ℝ) : ℂ)
        * ((C.Tq ω : ℝ) : ℂ) ^ q := by
    intro l
    have hk : ∀ k : κ, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))
        = ((C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) : ℝ) : ℂ) := by
      intro k
      rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Complex.ofReal_sum, Complex.ofReal_mul,
      C.sg_complex l]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_mul, ← Complex.ofReal_sum,
    C.sum_sg_mul_normSq ω, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-! ### The cross term -/

/-- Weighted Cauchy–Schwarz: `(∑ σ x y)² ≤ (∑ σ x²)(∑ σ y²)`. -/
private theorem weighted_cauchy {α : Type*} (s : Finset α) (σ x y : α → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    (∑ i ∈ s, σ i * (x i * y i)) ^ 2
      ≤ (∑ i ∈ s, σ i * x i ^ 2) * ∑ i ∈ s, σ i * y i ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => mul_nonneg (hσ i) (sq_nonneg _))
    (fun i _ => mul_nonneg (hσ i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))

/-- `q·x^{q-1}·x = q·x^q`, valid also at `q = 0`. -/
private theorem nat_mul_pow_pred (x : ℝ) (q : ℕ) : (q : ℝ) * x ^ (q - 1) * x = (q : ℝ) * x ^ q := by
  cases q with
  | zero => simp
  | succ n => simp [pow_succ]; ring

variable (C)

/-- The common majorant of `‖W_l‖` and of `‖D_l T‖/(2r²)`. -/
noncomputable def Arow (l : κ) (ω : Sample ι) : ℝ :=
  ∑ k, C.sg k * (‖C.B ω k l‖ * ‖C.U ω k‖ + ‖C.V ω k‖ * ‖C.B ω l k‖)

variable {C}

theorem Arow_nonneg (l : κ) (ω : Sample ι) : 0 ≤ C.Arow l ω :=
  Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)

theorem norm_Wt_le (l : κ) (ω : Sample ι) : ‖C.Wt l ω‖ ≤ C.Arow l ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.sg_nonneg k)]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (C.sg_nonneg k)
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]

theorem norm_sum_UV_le (l : κ) (ω : Sample ι) :
    ‖∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
      + C.B ω l k * (starRingEnd ℂ) (C.V ω k))‖ ≤ C.Arow l ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.sg_nonneg k)]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (C.sg_nonneg k)
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have h1 : ‖C.U ω k‖ * ‖C.B ω k l‖ = ‖C.B ω k l‖ * ‖C.U ω k‖ := mul_comm _ _
  have h2 : ‖C.B ω l k‖ * ‖C.V ω k‖ = ‖C.V ω k‖ * ‖C.B ω l k‖ := mul_comm _ _
  rw [h1, h2]

theorem sum_sg_normSq_U_le (ω : Sample ι) : ∑ k, C.sg k * ‖C.U ω k‖ ^ 2 ≤ C.Tq ω := by
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg ‖C.V ω k‖] : ‖C.U ω k‖ ^ 2 ≤ ‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)
    (C.sg_nonneg k)
  exact this

theorem sum_sg_normSq_V_le (ω : Sample ι) : ∑ k, C.sg k * ‖C.V ω k‖ ^ 2 ≤ C.Tq ω := by
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg ‖C.U ω k‖] : ‖C.V ω k‖ ^ 2 ≤ ‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)
    (C.sg_nonneg k)

/-- `A_l² ≤ 2T(∑_kσ_k‖B_{kl}‖² + ∑_kσ_k‖B_{lk}‖²)`, by Cauchy–Schwarz in `k`. -/
theorem sq_Arow_le (l : κ) (ω : Sample ι) :
    C.Arow l ω ^ 2
      ≤ 2 * C.Tq ω * ((∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) + ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2) := by
  set P : ℝ := ∑ k, C.sg k * (‖C.B ω k l‖ * ‖C.U ω k‖) with hP
  set Q : ℝ := ∑ k, C.sg k * (‖C.V ω k‖ * ‖C.B ω l k‖) with hQ
  have hsplit : C.Arow l ω = P + Q := by
    rw [hP, hQ, Arow, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPc : P ^ 2 ≤ (∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) * ∑ k, C.sg k * ‖C.U ω k‖ ^ 2 :=
    weighted_cauchy _ _ _ _ (fun k => C.sg_nonneg k)
  have hQc : Q ^ 2 ≤ (∑ k, C.sg k * ‖C.V ω k‖ ^ 2) * ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 :=
    weighted_cauchy _ _ _ _ (fun k => C.sg_nonneg k)
  have hB1 : (0 : ℝ) ≤ ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)
  have hB2 : (0 : ℝ) ≤ ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)
  have hU := C.sum_sg_normSq_U_le ω
  have hV := C.sum_sg_normSq_V_le ω
  have hP2 : P ^ 2 ≤ (∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) * C.Tq ω := by
    refine hPc.trans (mul_le_mul_of_nonneg_left hU hB1)
  have hQ2 : Q ^ 2 ≤ C.Tq ω * ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 := by
    refine hQc.trans (mul_le_mul_of_nonneg_right hV hB2)
  rw [hsplit]
  nlinarith [sq_nonneg (P - Q)]

/-! ### The cross term, bounded -/

variable (C)

/-- The cross term of `∑_l w_l D_l Z_{q,l}`. -/
noncomputable def crossT (q : ℕ) (ω : Sample ι) : ℂ :=
  ∑ l, (C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
    (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
      (C.U ω k * (starRingEnd ℂ) (C.B ω k l) + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))

variable {C}

theorem Vq_nonneg (ω : Sample ι) : 0 ≤ C.Vq ω :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (C.sg_nonneg k) (by positivity)) (C.sg_nonneg l)

/-- `∑_l w_l D_l Z_{q,l}` splits into the diagonal `2V_qT^q` and the cross term. -/
theorem sum_w_wirtVal_ZA_ZB (q : ℕ) (ω : Sample ι) :
    ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)
      = ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω := by
  rw [← C.sum_w_diag q ω, crossT, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by rw [wirtVal_ZA_ZB]; ring

/-- **The cross term is `≤ 4q V_q T^q`.**  Two Cauchy–Schwarz steps: first in `k`
(`sq_Arow_le`), then the sum over `l` against `σ_l` is `2V_q` (`sum_sg_mul_normSq`). -/
theorem norm_crossT_le (q : ℕ) (ω : Sample ι) :
    ‖C.crossT q ω‖ ≤ 4 * (q : ℝ) * C.Vq ω * C.Tq ω ^ q := by
  have hTn := C.Tq_nonneg ω
  have hTp : (0 : ℝ) ≤ C.Tq ω ^ (q - 1) := by positivity
  have hterm : ∀ l : κ, ‖(C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
        (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))‖
      ≤ C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) := by
    intro l
    have hw : ‖(C.w l : ℂ)‖ = C.w l := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.w_nonneg l)]
    have hqn : ‖(q : ℂ)‖ = (q : ℝ) := by simp
    have hT : ‖((C.Tq ω : ℝ) : ℂ) ^ (q - 1)‖ = C.Tq ω ^ (q - 1) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTn]
    have hr : ‖(2 : ℂ) * (C.r : ℂ) ^ 2‖ = 2 * C.r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      norm_num
    have hA := C.Arow_nonneg l ω
    have hr2 : (0 : ℝ) ≤ 2 * C.r ^ 2 := by positivity
    calc ‖(C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
          (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
            (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
              + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))‖
        = C.w l * (‖C.Wt l ω‖ * ((q : ℝ) * C.Tq ω ^ (q - 1) *
            (2 * C.r ^ 2 * ‖∑ k, ((C.sg k : ℝ) : ℂ) *
              (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
                + C.B ω l k * (starRingEnd ℂ) (C.V ω k))‖))) := by
          simp only [norm_mul, hw, hqn, hT, hr]
      _ ≤ C.w l * (C.Arow l ω * ((q : ℝ) * C.Tq ω ^ (q - 1) *
            (2 * C.r ^ 2 * C.Arow l ω))) := by
          gcongr
          · exact C.w_nonneg l
          · exact norm_Wt_le l ω
          · exact norm_sum_UV_le l ω
      _ = C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) := by
          change C.w l * _ = 2 * C.r ^ 2 * C.w l * _
          ring
  have hstep1 : ‖C.crossT q ω‖
      ≤ ∑ l, C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm l)
  have hstep2 : ∑ l, C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2)
      = (q : ℝ) * C.Tq ω ^ (q - 1) * ∑ l, C.sg l * C.Arow l ω ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hstep3 : ∑ l, C.sg l * C.Arow l ω ^ 2 ≤ 2 * C.Tq ω * (2 * C.Vq ω) := by
    have hbound : ∀ l : κ, C.sg l * C.Arow l ω ^ 2
        ≤ 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := by
      intro l
      have h := C.sq_Arow_le l ω
      have hmerge : ((∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) + ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2)
          = ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hmerge] at h
      have := mul_le_mul_of_nonneg_left h (C.sg_nonneg l)
      calc C.sg l * C.Arow l ω ^ 2
          ≤ C.sg l * (2 * C.Tq ω *
              ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := this
        _ = 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k *
              (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := by ring
    calc ∑ l, C.sg l * C.Arow l ω ^ 2
        ≤ ∑ l, 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k *
            (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := Finset.sum_le_sum fun l _ => hbound l
      _ = 2 * C.Tq ω * ∑ l, C.sg l * ∑ k, C.sg k *
            (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * C.Tq ω * (2 * C.Vq ω) := by rw [C.sum_sg_mul_normSq ω]
  have hqT : (0 : ℝ) ≤ (q : ℝ) * C.Tq ω ^ (q - 1) := by positivity
  calc ‖C.crossT q ω‖
      ≤ (q : ℝ) * C.Tq ω ^ (q - 1) * ∑ l, C.sg l * C.Arow l ω ^ 2 := by
        rw [← hstep2]; exact hstep1
    _ ≤ (q : ℝ) * C.Tq ω ^ (q - 1) * (2 * C.Tq ω * (2 * C.Vq ω)) :=
        mul_le_mul_of_nonneg_left hstep3 hqT
    _ = 4 * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Tq ω) * C.Vq ω := by ring
    _ = 4 * (q : ℝ) * C.Vq ω * C.Tq ω ^ q := by
        rw [nat_mul_pow_pred (C.Tq ω) q]; ring

/-! ### `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]` -/

variable (C)

theorem tameCrossT (q : ℕ) : gaussPoly_Tame (C.crossT q) :=
  gaussPoly_Tame.sum _ fun l _ => (gaussPoly_Tame.const (ι := ι) ((C.w l : ℂ))).mul
    ((C.tameWt l).mul (((gaussPoly_Tame.const (ι := ι) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul
      ((gaussPoly_Tame.const (ι := ι) (2 * (C.r : ℂ) ^ 2)).mul
        (gaussPoly_Tame.sum _ fun k _ => (gaussPoly_Tame.const (ι := ι) ((C.sg k : ℝ) : ℂ)).mul
          (((C.tameU k).mul (C.tameB k l).conj).add
            ((C.tameB l k).mul (C.tameV k).conj))))))

theorem tameWirt (q : ℕ) (l : κ) :
    gaussPoly_Tame fun ω => C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) :=
  (gaussPoly_Tame.const (ι := ι) ((C.r : ℂ))).mul
    ((C.tameZA q l).sub
      ((gaussPoly_Tame.const (ι := ι) ((C.eps l : ℂ) * Complex.I)).mul (C.tameZB q l)))

/-- `V_q T^q` is integrable. -/
theorem integrable_Vq_mul_Tq_pow (hG : gaussPoly_GaussIBP S) (q : ℕ) :
    Integrable (fun ω => C.Vq ω * C.Tq ω ^ q) (gaussLaw S) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω : Sample ι => ((C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
      = fun ω => ((C.Vq ω : ℝ) : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hfun]
  exact C.tame_ofReal_Vq.mul (C.tameTq.pow q)

/-- `V_q^q` is integrable. -/
theorem integrable_Vq_pow (hG : gaussPoly_GaussIBP S) (q : ℕ) :
    Integrable (fun ω => C.Vq ω ^ q) (gaussLaw S) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω : Sample ι => ((C.Vq ω ^ q : ℝ) : ℂ))
      = fun ω => ((C.Vq ω : ℝ) : ℂ) ^ q := by funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tame_ofReal_Vq.pow q

/-- `E[V_q^q]`. -/
noncomputable def momVpow (q : ℕ) : ℝ := ∫ ω, C.Vq ω ^ q ∂(gaussLaw S)

theorem momVpow_nonneg (q : ℕ) : 0 ≤ C.momVpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Vq_nonneg ω) q

variable {C}

/-- **The recursion for the positive chaos**: `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]`.  The diagonal
term of the integration by parts is `2E[V_qT^q]`; the cross term is at most `4qE[V_qT^q]`. -/
theorem momTpow_succ_le (hG : gaussPoly_GaussIBP S) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) * ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(gaussLaw S) := by
  set I1 : ℝ := ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(gaussLaw S) with hI1
  have hiVT := C.integrable_Vq_mul_Tq_pow hG q
  have hiCross : Integrable (C.crossT q) (gaussLaw S) := (C.tameCrossT q).integrable hG
  have hiW : ∀ l : κ, Integrable (fun ω => (C.w l : ℂ) *
      C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)) (gaussLaw S) :=
    fun l => ((gaussPoly_Tame.const (ι := ι) ((C.w l : ℂ))).mul (C.tameWirt q l)).integrable hG
  have hiDiag :
      Integrable (fun ω : Sample ι => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
        (gaussLaw S) := by
    have : (fun ω : Sample ι => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
        = fun ω => ((2 * (C.Vq ω * C.Tq ω ^ q) : ℝ) : ℂ) := by
      funext ω; norm_num; ring_nf
    rw [this]
    exact (MeasureTheory.Integrable.ofReal (hiVT.const_mul 2))
  -- the complex identity
  have hId : ((C.momTpow (q + 1) : ℝ) : ℂ)
      = ((2 * I1 : ℝ) : ℂ) + ∫ ω, C.crossT q ω ∂(gaussLaw S) := by
    have h1 : ((C.momTpow (q + 1) : ℝ) : ℂ)
        = ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(gaussLaw S) := by
      rw [momTpow, ← integral_ofReal']
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ω => Complex.ofReal_pow _ _)
    have h2 : ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(gaussLaw S)
        = ∫ ω, ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(gaussLaw S) := by
      rw [MeasureTheory.integral_finsetSum _ fun l _ => hiW l]
      exact Finset.sum_congr rfl fun l _ => (MeasureTheory.integral_const_mul _ _).symm
    have h3 : ∫ ω, ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(gaussLaw S)
        = ∫ ω, (((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω) ∂(gaussLaw S) :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ω => sum_w_wirtVal_ZA_ZB q ω)
    have h4 : ∫ ω, (((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω) ∂(gaussLaw S)
        = ((2 * I1 : ℝ) : ℂ) + ∫ ω, C.crossT q ω ∂(gaussLaw S) := by
      rw [MeasureTheory.integral_add hiDiag hiCross]
      congr 1
      rw [integral_ofReal']
      congr 1
      rw [hI1, ← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, integral_Tq_pow_succ hG, h2, h3, h4]
  -- the cross term is small
  have hcross : ‖∫ ω, C.crossT q ω ∂(gaussLaw S)‖ ≤ 4 * (q : ℝ) * I1 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖C.crossT q ω‖ ∂(gaussLaw S)
        ≤ ∫ ω, 4 * (q : ℝ) * (C.Vq ω * C.Tq ω ^ q) ∂(gaussLaw S) :=
          MeasureTheory.integral_mono hiCross.norm (hiVT.const_mul (4 * (q : ℝ)))
            (fun ω => (norm_crossT_le (C := C) q ω).trans_eq (by ring))
      _ = 4 * (q : ℝ) * I1 := by
          rw [hI1, MeasureTheory.integral_const_mul]
  have hsub : ((C.momTpow (q + 1) - 2 * I1 : ℝ) : ℂ) = ∫ ω, C.crossT q ω ∂(gaussLaw S) := by
    rw [Complex.ofReal_sub, hId]; ring
  have habs : |C.momTpow (q + 1) - 2 * I1| ≤ 4 * (q : ℝ) * I1 := by
    have := hcross
    rw [← hsub, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have := (abs_le.1 habs).2
  linarith

/-! ### Closing the recursion: `E[T^p] ≤ (4p−2)^p E[V_q^p]` -/

/-- **The positive chaos moment bound.**  `E[T^{q+1}] ≤ (4q+2)^{q+1} E[V_q^{q+1}]`.

The recursion `E[T^{q+1}] ≤ (4q+2)E[V_qT^q]` is closed by the same pointwise Young inequality
`gaussPoly_young_pow` that closes `mom_succ_le`, with the rational parameter
`K = 4q+2`; every exponent stays a natural number. -/
theorem momTpow_le (hG : gaussPoly_GaussIBP S) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) ^ (q + 1) * C.momVpow (q + 1) := by
  set K : ℝ := 4 * (q : ℝ) + 2 with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hpt : ∀ ω : Sample ι, C.Vq ω * C.Tq ω ^ q
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.Vq ω ^ (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.Tq ω ^ (q + 1) := by
    intro ω
    have hV := C.Vq_nonneg ω
    have hT := C.Tq_nonneg ω
    have hy := gaussPoly_young_pow q (mul_nonneg hV hK0.le) hT
    have hmul : (0 : ℝ) < ((q : ℝ) + 1) * K := by positivity
    refine le_of_mul_le_mul_left ?_ hmul
    have hleft : ((q : ℝ) + 1) * K * (C.Vq ω * C.Tq ω ^ q)
        = ((q : ℝ) + 1) * (C.Vq ω * K * C.Tq ω ^ q) := by ring
    have hrhs : ((q : ℝ) + 1) * K * ((K ^ q / ((q : ℝ) + 1)) * C.Vq ω ^ (q + 1)
          + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.Tq ω ^ (q + 1))
        = (C.Vq ω * K) ^ (q + 1) + (q : ℝ) * C.Tq ω ^ (q + 1) := by
      rw [mul_pow]
      field_simp
      ring
    rw [hleft, hrhs]
    exact hy
  have hi1 := C.integrable_Vq_pow hG (q + 1)
  have hi2 := C.integrable_Tq_pow hG (q + 1)
  have hA : (∫ ω, C.Vq ω * C.Tq ω ^ q ∂(gaussLaw S))
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.momTpow (q + 1) := by
    calc ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(gaussLaw S)
        ≤ ∫ ω, ((K ^ q / ((q : ℝ) + 1)) * C.Vq ω ^ (q + 1)
            + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.Tq ω ^ (q + 1)) ∂(gaussLaw S) :=
          MeasureTheory.integral_mono (C.integrable_Vq_mul_Tq_pow hG q)
            ((hi1.const_mul _).add (hi2.const_mul _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
  have hKne : K ≠ 0 := ne_of_gt hK0
  have hqne : ((q : ℝ) + 1) ≠ 0 := ne_of_gt hq1
  have hM := C.momTpow_succ_le hG q
  rw [← hKdef] at hM
  have hN := C.momVpow_nonneg (q + 1)
  have hT0 := C.momTpow_nonneg (q + 1)
  have hKmul : K * ((K ^ q / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.momTpow (q + 1))
      = (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.momTpow (q + 1) := by
    rw [pow_succ]
    field_simp
  have hchain : C.momTpow (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.momTpow (q + 1) := by
    refine hM.trans ?_
    rw [← hKmul]
    exact mul_le_mul_of_nonneg_left hA hK0.le
  have hA' : K ^ (q + 1) / ((q : ℝ) + 1) ≤ K ^ (q + 1) := by
    rw [div_le_iff₀ hq1]
    nlinarith [pow_nonneg hK0.le (q + 1), Nat.cast_nonneg (α := ℝ) q]
  have hstep : (1 - (q : ℝ) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1) := by nlinarith [hchain]
  have hone : (1 : ℝ) - (q : ℝ) / ((q : ℝ) + 1) = 1 / ((q : ℝ) + 1) := by
    rw [eq_div_iff hqne, sub_mul, div_mul_cancel₀ _ hqne, one_mul]
    ring
  rw [hone] at hstep
  have := mul_le_mul_of_nonneg_left hstep hq1.le
  have hl : ((q : ℝ) + 1) * (1 / ((q : ℝ) + 1) * C.momTpow (q + 1)) = C.momTpow (q + 1) := by
    field_simp
  have hr : ((q : ℝ) + 1) * ((K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1))
      = K ^ (q + 1) * C.momVpow (q + 1) := by field_simp
  rw [hl, hr] at this
  exact this

/-- **Hanson–Wright moment bound for the Gaussian row chaos.**  Combining the recursion of
`mom_succ_le` with the positive chaos bound,

`E|Q|^{2(q+1)} ≤ ((2q+1)(4q+2))^{q+1} E[V_q^{q+1}]`,

with `V_q = ∑_{k,l}σ_k‖B_{kl}‖²σ_l`: the moment form of the quadratic large deviation estimate
used in the proof of [I, Lemma 5.1]. -/
theorem mom_le_momVpow (hG : gaussPoly_GaussIBP S) (q : ℕ) :
    C.mom (q + 1)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * C.momVpow (q + 1) := by
  have h1 := C.mom_succ_le hG q
  have h2 := C.momTpow_le hG q
  have hc : (0 : ℝ) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) := by positivity
  calc C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := h1
    _ ≤ (2 * (q : ℝ) + 1) ^ (q + 1) *
        ((4 * (q : ℝ) + 2) ^ (q + 1) * C.momVpow (q + 1)) :=
          mul_le_mul_of_nonneg_left h2 hc
    _ = ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * C.momVpow (q + 1) := by
        rw [mul_pow]; ring

end chaos_RowChaos

end RBM8D
