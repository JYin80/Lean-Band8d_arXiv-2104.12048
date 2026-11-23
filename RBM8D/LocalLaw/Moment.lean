module

public import RBM8D.LocalLaw.Defs
public import RBM8D.LocalLaw.LabelRemoval
public import RBM8D.Kernel.Decay

@[expose] public section

/-!
# The high moment bound [II, Lemma 8.1]: auxiliary facts

Facts used toward the high moment bound [II, Lemma 8.1] for `E T_{𝔞𝔟}^q` ([II, (8.18)–(8.28)]):

* the sizes `(W, L)` of `adm(c₀, c₁)` and of the condition [II, (3.15)] hold eventually along
  `llFilter`, and the bounds `B_{xy} ≤ 1` and `B_{xy} ≥ W^{−C}` on `adm`;
* the data record of the model is admissible and consistent with the self-energies
  (`Moment_sigConsistent`), the value of a graph and its modulus bound on a data record, and the
  identity of `T_{𝔞𝔟}` with the sum over the chain of lower orders;
* the dotted blocks of a graph as the connected components of its dotted edges, and the
  identification of `Graph.DiagRecoll` with the recollision and `⊕⊖`-block conditions;
* the a priori bound of a graph on the event `‖ω‖ > W`, and the measurability of `T`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

section StochDomAlg

variable {Par : Type*} {Ω : Par → Type*} [∀ p, MeasurableSpace (Ω p)] {U : Par → Type*}
  {F : Filter Par} {size : Par → ℝ} {Pr : ∀ p, Measure (Ω p)}

end StochDomAlg

/-! ## The filter of the local law -/

/-- Eventually along the filter, `(W, L) ∈ adm(c₀, c₁)`. -/
private lemma Moment_ev_adm (d n : ℕ) (c₀ c₁ c₀T : ℝ) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, p.1 ∈ adm c₀ c₁ :=
  (tendsto_comap.eventually (inf_le_left (a := 𝓟 (adm c₀ c₁)) (Filter.mem_principal_self _))
    : ∀ᶠ p in admFilterL c₀ c₁, p.1 ∈ adm c₀ c₁).filter_mono inf_le_left

/-- Eventually along the filter, [II, (3.15)] holds. -/
private lemma Moment_ev_thr (d n : ℕ) (c₀ c₁ c₀T : ℝ) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, p ∈ thrSet d n c₀T :=
  mem_inf_of_right (mem_principal_self _)

/-- `W → ∞` along the filter. -/
private lemma Moment_tendsto (d n : ℕ) (c₀ c₁ c₀T : ℝ) :
    Tendsto sizeW (llFilter d n c₀ c₁ c₀T) atTop :=
  (tendsto_sizeW_admFilterL c₀ c₁).mono_left inf_le_left

/-- On `adm(c₀, c₁)` with `c₀ > 0`, `W ≤ L`. -/
private lemma Moment_W_le_L {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (p : SizeL) (hp : p.1 ∈ adm c₀ c₁) :
    (p.1.1 : ℝ) ≤ p.1.2 := by
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  calc (p.1.1 : ℝ) ≤ (p.1.2 : ℝ) ^ (1 - c₀) := hp.2
    _ ≤ (p.1.2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = p.1.2 := Real.rpow_one _

/-- For `n ≤ 1` the filter is eventually empty: `L²/W² ≥ 1 > W^{(n−1)d/2 − c₀ᵀ}` for `W > 1`. -/
private lemma Moment_small_n (d n : ℕ) (c₀ c₁ c₀T : ℝ) (hc₀ : 0 < c₀) (hc₀T : 0 < c₀T)
    (hn : n ≤ 1) : ∀ᶠ _p in llFilter d n c₀ c₁ c₀T, False := by
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, Moment_ev_thr d n c₀ c₁ c₀T,
    (Moment_tendsto d n c₀ c₁ c₀T).eventually (eventually_gt_atTop 1)] with p hp ht hW
  change (1 : ℝ) < p.1.1 at hW
  have hWL := Moment_W_le_L hc₀ p hp
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have h1 : (1 : ℝ) ≤ (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hW0.le hWL 2
  have hn' : ((n : ℝ) - 1) * d / 2 - c₀T < 0 := by
    have : (n : ℝ) ≤ 1 := by exact_mod_cast hn
    have : ((n : ℝ) - 1) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  have h2 : (p.1.1 : ℝ) ^ (((n : ℝ) - 1) * d / 2 - c₀T) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hW hn'
  have h3 : (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ (((n : ℝ) - 1) * d / 2 - c₀T) := ht
  linarith

/-! ## The identity [II, (3.1)] on the data record of the model -/

/-- `(B⁻¹).map ofReal = (B.map ofReal)⁻¹` for the ring inverse. -/
private lemma Moment_map_ringInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) :
    (Ring.inverse B).map ((↑) : ℝ → ℂ) = Ring.inverse (B.map ((↑) : ℝ → ℂ)) := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  change f (Ring.inverse B) = Ring.inverse (f B)
  by_cases h : IsUnit B
  · obtain ⟨u, rfl⟩ := h
    have : f (u : Matrix ι ι ℝ) = ((Units.map f.toMonoidHom u : (Matrix ι ι ℂ)ˣ) :
        Matrix ι ι ℂ) := rfl
    rw [this, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (f B) := by
      rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
      have e : (f B).det = Complex.ofRealHom B.det := (RingHom.map_det _ _).symm
      rw [e]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0; apply hu; rw [h0, map_zero]
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

/-- The matrix `Θ` of the data record of the model is `Θ(m)` of [I, (1.16)]. -/
private lemma Moment_theta_eq {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (z : ℂ) (H : Sample ι → Matrix ι ι ℂ) (ω : Sample ι) :
    (modelData S z H ω).Theta = cmat (Theta (msc z) S) := by
  simp only [modelData, cmat, Theta]
  rw [Matrix.nonsing_inv_eq_ringInverse]
  have e1 : ((‖msc z‖ ^ 2 • S) * Ring.inverse (1 - ‖msc z‖ ^ 2 • S)).map ((↑) : ℝ → ℂ) =
      (‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) *
        (Ring.inverse (1 - ‖msc z‖ ^ 2 • S)).map ((↑) : ℝ → ℂ) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [e1, Moment_map_ringInverse]
  have e2 : (‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) =
      ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ) := by
    ext i j; simp
  have e3 : (1 - ‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) =
      1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ) := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [e2, e3]

/-- The data record of the model is admissible ([I, §1.4], `modelAdm_gauss`): its self-energy
field is not constrained. -/
private lemma Moment_modelAdm (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (hS : (Smat P.ψ W L).IsSymm) (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y)
    (hrow : ∀ x, ∑ y, Smat P.ψ W L x y = 1) (hz : 0 < z.im) :
    modelAdm (Sample (Zd d L)) (Zd d L) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) := by
  obtain ⟨A⟩ := modelAdm_gauss (Zd d L) (Smat P.ψ W L) z hS hnn hrow hz
  exact ⟨{ A with }⟩


/-- The self-energy matrices below order `k` are the matrices `Σ_l`. -/
private lemma Moment_sigUpTo_eq {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2)
    (S : Matrix ι ι ℝ) (z : ℂ) : ∀ k l, l < k → sigUpTo Sig S z k l = sigMat Sig S z l := by
  intro k
  induction k with
  | zero => intro l hl; omega
  | succ k ih =>
    intro l hl
    simp only [sigUpTo]
    by_cases h : l = k
    · subst h
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne h]
      exact ih l (by omega)

/-- The chain `Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ` depends only on `Θ` and on the matrices `Σ_{oᵢ}`. -/
private lemma Moment_chain_congr {ι : Type} [Fintype ι] (D₁ D₂ : Data ι)
    (hΘ : D₁.Theta = D₂.Theta) (o : List ℕ) (hS : ∀ l ∈ o, D₁.Sig l = D₂.Sig l) :
    D₁.chain o = D₂.chain o := by
  unfold Data.chain
  rw [hΘ]
  have key : ∀ (o : List ℕ), (∀ l ∈ o, D₁.Sig l = D₂.Sig l) → ∀ A : Matrix ι ι ℂ,
      o.foldl (fun M l => M * D₁.Sig l * D₂.Theta) A =
        o.foldl (fun M l => M * D₂.Sig l * D₂.Theta) A := by
    intro o
    induction o with
    | nil => intro _ A; rfl
    | cons l o ih =>
      intro h A
      simp only [List.foldl_cons]
      rw [h l (List.mem_cons_self ..)]
      exact ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) _
  exact key o hS _

/-- The factor of a deterministic component depends only on `S`, `S^±` and the chains. -/
private lemma Moment_compVal_det {ι V : Type} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (D₁ D₂ : Data ι) (σ : V → ι) (c : Comp V) (hc : c.isDetKind N = true)
    (hS : D₁.S = D₂.S) (hSp : D₁.Sp = D₂.Sp) (hSm : D₁.Sm = D₂.Sm)
    (hch : ∀ o, labelOK N o = true → D₁.chain o = D₂.chain o) :
    Comp.val D₁ σ c = Comp.val D₂ σ c := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ with
  | waved w => cases w <;> simp [Comp.val, hS, hSp, hSm]
  | theta o =>
    have ho : labelOK N o = true := by
      simp only [Comp.isDetKind, Bool.and_eq_true] at hc
      exact hc.2
    simp [Comp.val, hch o ho]
  | dot => simp [Comp.val]
  | xdot => simp [Comp.val]
  | _ => simp [Comp.isDetKind] at hc

/-- The value of a deterministic graph depends only on `m`, `S`, `S^±` and the chains. -/
private lemma Moment_graphVal_det {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} (N : ℕ)
    (Γ : Graph k n) (hΓ : Γ.comps.all (Comp.isDetKind N) = true) (D₁ D₂ : Data ι)
    (hm : D₁.m = D₂.m) (hS : D₁.S = D₂.S) (hSp : D₁.Sp = D₂.Sp) (hSm : D₁.Sm = D₂.Sm)
    (hch : ∀ o, labelOK N o = true → D₁.chain o = D₂.chain o) (e : Fin k → ι) :
    Γ.val D₁ e = Γ.val D₂ e := by
  unfold Graph.val Graph.term
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hm]
  congr 2
  refine List.map_congr_left fun c hc => ?_
  exact Moment_compVal_det N D₁ D₂ _ c (List.all_eq_true.1 hΓ c hc) hS hSp hSm hch

/-- The data record of the model is consistent with `Sig` up to order `n`: its self-energy
matrices `Σ_k` are the values of `Sig k` on the record itself. -/
lemma Moment_sigConsistent (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (n : ℕ)
    (hsh : SelfEnergyShapesUpTo Sig n) (W L : ℕ) [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) :
    SigConsistent Sig (n + 1) (rbmData d P Sig W L z ω) := by
  intro k h4 hlt hev
  change sigMat Sig (Smat P.ψ W L) z k = _
  ext x y
  simp only [sigMat, Matrix.of_apply, Expansion.val]
  congr 1
  refine List.map_congr_left fun g hg => ?_
  have hall := (hsh k h4 (by omega) hev g hg).2.1
  have hSp : (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z k)).Sp =
      (rbmData d P Sig W L z ω).Sp := by
    change Splus (msc z) (Smat P.ψ W L) = (msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ))⁻¹
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hSm : (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z k)).Sm =
      (rbmData d P Sig W L z ω).Sm := by
    change Sminus (msc z) (Smat P.ψ W L) = ((msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ))⁻¹).map star
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hch : ∀ o, labelOK (k - 1) o = true →
      (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z k)).chain o =
        (rbmData d P Sig W L z ω).chain o := by
    intro o ho
    refine Moment_chain_congr _ _ ?_ o fun l hl => ?_
    · exact (Moment_theta_eq (Smat P.ψ W L) z hmat ω).symm
    · have hl' : l ≤ k - 1 := by
        have := List.all_eq_true.1 ho l hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.2
      change sigUpTo Sig (Smat P.ψ W L) z k l = sigMat Sig (Smat P.ψ W L) z l
      exact Moment_sigUpTo_eq Sig _ z k l (by omega)
  have hm : (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z k)).m =
      (rbmData d P Sig W L z ω).m := rfl
  have hS : (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z k)).S =
      (rbmData d P Sig W L z ω).S := rfl
  exact Moment_graphVal_det (k - 1) g.2 hall _ _ hm hS hSp hSm hch _

/-- The resolvent of the data record of the model. -/
private lemma Moment_Gm_empty (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) :
    (rbmData d P Sig W L z ω).Gm ∅ = green (hmat ω) z := by
  have h : ¬ ∃ x : Zd d L, (∅ : Finset (Zd d L)) = {x} := by
    rintro ⟨x, hx⟩
    exact Finset.singleton_ne_empty x hx.symm
  simp only [rbmData, modelData, dite_eq_right h]

/-- The value of the graph `T_{𝔞,𝔟𝔟}` on the data record of the model is `T_{𝔞𝔟}`. -/
private lemma Moment_tGraph_val (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (a b : Zd d L) (ω : Sample (Zd d L)) :
    tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω =
      ((Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) a b : ℝ) : ℂ) := by
  have hG := Moment_Gm_empty d P Sig W L z ω
  simp only [Graph.valR, Graph.termR, tGraph, Graph.labels, mkC, List.filterMap_cons,
    List.filterMap_nil, List.dedup_nil, List.map_nil, List.prod_nil, mul_one,
    List.filter_cons, Option.isNone_none, ite_true, List.filter_nil, List.map_cons,
    List.prod_cons]
  rw [← (Equiv.funUnique (Fin 1) (Zd d L)).symm.sum_comp]
  simp only [Comp.val, List.map_nil, List.toFinset_nil, hG, Tvar, Coeff.eval]
  simp only [map_mul, MvPolynomial.eval_X, Equiv.funUnique_symm_apply, Fin.isValue, Sum.elim_inl,
    Matrix.cons_val_zero, Sum.elim_inr, uniqueElim_const, Matrix.cons_val_one, Matrix.cons_val,
    ofReal_mul, ofReal_pow, ofReal_sum, CVar.eval, Charge.apply, Finset.mul_sum]
  change ∑ x, msc z * (starRingEnd ℂ) (msc z) * (((Smat P.ψ W L a x : ℝ) : ℂ) *
    (green (hmat ω) z x b * (starRingEnd ℂ) (green (hmat ω) z x b))) = _
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring


/-! ## A priori bounds and measurability of graph values -/

/-- `|P_x F| ≤ B` when `|F| ≤ B` everywhere. -/
private lemma Moment_Pexp_le {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (x : ι)
    (f : Sample ι → ℂ) (B : ℝ) (hf : ∀ ω, ‖f ω‖ ≤ B) (ω : Sample ι) : ‖Pexp S x f ω‖ ≤ B := by
  have := isProbabilityMeasure_gaussLaw S
  unfold Pexp partialExp
  have h := norm_integral_le_of_norm_le_const (μ := gaussLaw S)
    (f := fun η => f ((rowCoords x).piecewise η ω)) (C := B) (Eventually.of_forall fun η => hf _)
  simpa using h

/-- A product of factors bounded by `A ≥ 0` is bounded by `A^length`. -/
private lemma Moment_prod_le {α : Type*} (l : List α) (f : α → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ a ∈ l, ‖f a‖ ≤ A) : ‖(l.map f).prod‖ ≤ A ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [norm_mul, mul_comm]
    exact mul_le_mul (ih fun b hb => h b (List.mem_cons_of_mem _ hb))
      (h a (List.mem_cons_self ..)) (norm_nonneg _) (pow_nonneg hA _)

/-- The factor of a component with the kinds of [II, Def 3.2] is bounded by `2M` when the entries
read are bounded by `M ≥ 1` and `|m| ≤ 1`. -/
private lemma Moment_compVal_le {ι V : Type} [Fintype ι] [DecidableEq ι] (N : ℕ) (D : Data ι)
    (σ : V → ι) (c : Comp V) (hc : c.isTKind N = true) (M : ℝ) (hM1 : 1 ≤ M) (hm : ‖D.m‖ ≤ 1)
    (hG : ∀ x y, ‖D.Gm ∅ x y‖ ≤ M) (hS : ∀ x y, ‖D.S x y‖ ≤ M) (hSp : ∀ x y, ‖D.Sp x y‖ ≤ M)
    (hSm : ∀ x y, ‖D.Sm x y‖ ≤ M) (hch : ∀ o, c.kind = .theta o → ∀ x y, ‖D.chain o x y‖ ≤ M) :
    ‖Comp.val D σ c‖ ≤ 2 * M := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  have hmi : mi = [] := by
    simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at hc
    exact hc.1
  subst hmi
  have hch' := hch
  cases κ with
  | G ch => cases ch <;> simp [Comp.val, Charge.apply] <;> linarith [hG (σ x) (σ y)]
  | weight ch => cases ch <;> simp [Comp.val, Charge.apply] <;> linarith [hG (σ x) (σ x)]
  | light ch =>
    have h1 : ‖D.Gm ∅ (σ x) (σ x) - D.m‖ ≤ 2 * M := by
      have := norm_sub_le (D.Gm ∅ (σ x) (σ x)) D.m
      linarith [hG (σ x) (σ x)]
    cases ch
    · simpa [Comp.val, Charge.apply] using h1
    · simp only [Comp.val, Charge.apply, List.map_nil, List.toFinset_nil]
      rw [norm_star]
      exact h1
  | waved w =>
    cases w <;> simp [Comp.val]
    · linarith [hS (σ x) (σ y)]
    · linarith [hSp (σ x) (σ y)]
    · linarith [hSm (σ x) (σ y)]
  | theta o =>
    simp only [Comp.val]
    linarith [hch o rfl (σ x) (σ y)]
  | dot => simp only [Comp.val]; split_ifs <;> simp <;> linarith
  | xdot => simp only [Comp.val]; split_ifs <;> simp <;> linarith
  | _ => simp [Comp.isTKind] at hc

/-- A priori bound of the value of a graph with the kinds of [II, Def 3.2] and `P`/`Q` labels read
by the partial expectations `P_x`: every factor is bounded by `A = 2M`, so
`|Γ| ≤ |ι|^n |coeff| A^c (2A^c)^c` with `c` the number of components. -/
private lemma Moment_valR_le {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} (N : ℕ)
    (Γ : Graph k n) (hΓ : Γ.TKinds N) (S : Matrix ι ι ℝ) (D : Sample ι → Data ι) (M : ℝ)
    (hM1 : 1 ≤ M) (hm : ∀ ω, (D ω).m = (D 0).m) (hm1 : ‖(D 0).m‖ ≤ 1)
    (hG : ∀ ω x y, ‖(D ω).Gm ∅ x y‖ ≤ M) (hS : ∀ ω x y, ‖(D ω).S x y‖ ≤ M)
    (hSp : ∀ ω x y, ‖(D ω).Sp x y‖ ≤ M) (hSm : ∀ ω x y, ‖(D ω).Sm x y‖ ≤ M)
    (hch : ∀ ω, ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ x y, ‖(D ω).chain o x y‖ ≤ M)
    (e : Fin k → ι) (ω : Sample ι) :
    ‖Γ.valR ⟨Pexp S⟩ D e ω‖ ≤ (Fintype.card ι : ℝ) ^ n * (‖Γ.coeff.eval (D 0).m‖ *
      (2 * M) ^ Γ.comps.length * (2 * (2 * M) ^ Γ.comps.length) ^ Γ.comps.length) := by
  set A := 2 * M with hA
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  set c := Γ.comps.length with hc
  have hTK : ∀ c' ∈ Γ.comps, c'.isTKind N = true := List.all_eq_true.1 hΓ
  have hcomp : ∀ ω' (σ : Atom k n → ι), ∀ c' ∈ Γ.comps, ‖Comp.val (D ω') σ c'‖ ≤ A :=
    fun ω' σ c' hc' => Moment_compVal_le N (D ω') σ c' (hTK c' hc') M hM1 ((hm ω').symm ▸ hm1)
      (hG ω') (hS ω') (hSp ω') (hSm ω') (hch ω' c' hc')
  have hsub : ∀ (p : Comp (Atom k n) → Bool) ω' (σ : Atom k n → ι),
      ‖((Γ.comps.filter p).map (Comp.val (D ω') σ)).prod‖ ≤ A ^ c := by
    intro p ω' σ
    refine (Moment_prod_le _ _ A hA0 fun c' hc' =>
      hcomp ω' σ c' (List.mem_of_mem_filter hc')).trans ?_
    exact pow_le_pow_right₀ hA1 (List.length_filter_le _ _)
  have hterm : ∀ σ : Atom k n → ι, ‖Γ.termR ⟨Pexp S⟩ D σ ω‖ ≤
      ‖Γ.coeff.eval (D 0).m‖ * A ^ c * (2 * A ^ c) ^ c := by
    intro σ
    unfold Graph.termR
    rw [norm_mul, norm_mul, hm ω]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (hsub _ ω σ) (norm_nonneg _)) ?_ (norm_nonneg _)
      (by positivity)
    have hlab : Γ.labels.length ≤ c := by
      unfold Graph.labels
      exact (List.dedup_sublist _).length_le.trans (List.length_filterMap_le _ _)
    refine (Moment_prod_le _ _ (2 * A ^ c) (by positivity) fun ℓ _ => ?_).trans
      (pow_le_pow_right₀ (by nlinarith [one_le_pow₀ (n := c) hA1]) hlab)
    have hP : ∀ ω'', ‖PFamily.P ⟨Pexp S⟩ (σ ℓ.2) (fun ω' =>
        ((Γ.comps.filter fun c' => decide (c'.label = some ℓ)).map
          (Comp.val (D ω') σ)).prod) ω''‖ ≤ A ^ c :=
      fun ω'' => Moment_Pexp_le S _ _ _ (fun ω' => hsub _ ω' σ) ω''
    have hA' : 0 ≤ A ^ c := pow_nonneg hA0 _
    rcases ℓ with ⟨pq, u⟩
    cases pq
    · exact (hP ω).trans (by linarith)
    · simp only [PFamily.op, Pi.sub_apply]
      refine (norm_sub_le _ _).trans ?_
      linarith [hP ω, hsub (fun c' => decide (c'.label = some (PQ.Q, u))) ω σ]
  unfold Graph.valR
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun s _ => hterm _).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact le_rfl


/-- The values of the graphs with the kinds of [II, Def 3.2] on the data record of the model have
polynomial growth; in particular they are measurable. -/
private lemma Moment_polyMeas_valR (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y) {k n N : ℕ} (Γ : Graph k n) (hΓ : Γ.TKinds N)
    (e : Fin k → Zd d L) :
    PolyMeas (Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e) := by
  have hL := pqLaws_Pexp_poly (Smat P.ψ W L) hS hnn
  have hGm := Moment_Gm_empty d P Sig W L z
  have hgreen : ∀ x y, PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z x y :=
    fun x y => polyMeas_of_testFn _ (testFn_green z hz.ne' x y)
  have hconst : ∀ (f : Sample (Zd d L) → ℂ) (a : ℂ), (∀ ω, f ω = a) → PolyMeas f := by
    intro f a h
    have : f = fun _ => a := funext h
    rw [this]; exact hL.adm_const a
  have hcomp : ∀ (σ : Atom k n → Zd d L), ∀ c ∈ Γ.comps,
      PolyMeas fun ω => Comp.val (rbmData d P Sig W L z ω) σ c := by
    intro σ c hc
    have hc' := List.all_eq_true.1 hΓ c hc
    rcases c with ⟨κ, x, y, mi, lab⟩
    have hmi : mi = [] := by
      simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at hc'
      exact hc'.1
    subst hmi
    cases κ with
    | G ch =>
      cases ch
      · simpa [Comp.val, Charge.apply, hGm] using hgreen (σ x) (σ y)
      · simpa [Comp.val, Charge.apply, hGm] using hL.adm_conj _ (hgreen (σ x) (σ y))
    | weight ch =>
      cases ch
      · simpa [Comp.val, Charge.apply, hGm] using hgreen (σ x) (σ x)
      · simpa [Comp.val, Charge.apply, hGm] using hL.adm_conj _ (hgreen (σ x) (σ x))
    | light ch =>
      have h1 : PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z (σ x) (σ x) - msc z := by
        have := hL.adm_add _ _ (hgreen (σ x) (σ x)) (hL.adm_const (-msc z))
        refine (congrArg PolyMeas ?_).mp this
        funext ω
        simp [sub_eq_add_neg]
      cases ch
      · simpa [Comp.val, Charge.apply, hGm, rbmData, modelData] using h1
      · simpa [Comp.val, Charge.apply, hGm, rbmData, modelData] using hL.adm_conj _ h1
    | waved w => cases w <;> exact hconst _ _ fun ω => rfl
    | theta o => exact hconst _ ((rbmData d P Sig W L z 0).chain o (σ x) (σ y)) fun ω => rfl
    | dot => exact hconst _ _ fun ω => rfl
    | xdot => exact hconst _ _ fun ω => rfl
    | _ => simp [Comp.isTKind] at hc'
  have hprod : ∀ (σ : Atom k n → Zd d L) (l : List (Comp (Atom k n))), (∀ c ∈ l, c ∈ Γ.comps) →
      PolyMeas fun ω => (l.map (Comp.val (rbmData d P Sig W L z ω) σ)).prod := by
    intro σ l hl
    induction l with
    | nil => simpa using hL.adm_const 1
    | cons c l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact hL.adm_mul _ _ (hcomp σ c (hl c (List.mem_cons_self ..)))
        (ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
  have hterm : ∀ σ : Atom k n → Zd d L,
      PolyMeas fun ω => Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) σ ω := by
    intro σ
    unfold Graph.termR
    refine hL.adm_mul _ _ (hL.adm_mul _ _ (hconst _ (Γ.coeff.eval (msc z)) fun ω => rfl)
      (hprod σ _ fun c hc => List.mem_of_mem_filter hc)) ?_
    have hlab : ∀ (ls : List (PQ × Atom k n)), PolyMeas fun ω => (ls.map fun ℓ =>
        PFamily.op ⟨Pexp (Smat P.ψ W L)⟩ ℓ.1 (σ ℓ.2) (fun ω' =>
          ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
            (Comp.val (rbmData d P Sig W L z ω') σ)).prod) ω).prod := by
      intro ls
      induction ls with
      | nil => simpa using hL.adm_const 1
      | cons ℓ ls ih =>
        simp only [List.map_cons, List.prod_cons]
        refine hL.adm_mul _ _ ?_ ih
        have hf := hprod σ (Γ.comps.filter fun c => decide (c.label = some ℓ))
          (fun c hc => List.mem_of_mem_filter hc)
        rcases ℓ with ⟨pq, u⟩
        cases pq
        · exact hL.adm_P _ _ hf
        · have := hL.adm_add _ _ hf (hL.adm_mul _ _ (hL.adm_const (-1)) (hL.adm_P (σ u) _ hf))
          refine (congrArg PolyMeas ?_).mp this
          funext ω
          simp only [PFamily.op, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
          ring
    exact hlab _
  unfold Graph.valR
  have hsum : ∀ (A : Finset (Fin n → Zd d L)), PolyMeas fun ω =>
      ∑ s ∈ A, Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (Sum.elim e s) ω := by
    intro A
    induction A using Finset.induction_on with
    | empty => simpa using hL.adm_const 0
    | insert a A ha ih =>
      have := hL.adm_add _ _ (hterm (Sum.elim e a)) ih
      refine (congrArg PolyMeas ?_).mp this
      funext ω
      simp only [Pi.add_apply, Finset.sum_insert ha]
  exact hsum Finset.univ


/-! ## The leading terms `m Θ^{[o]}_{𝔞𝔟} Ḡ_{𝔟𝔟}` ([II, (8.19)]) -/

/-- Eventually along the filter, `S` is symmetric, nonnegative, with row sums `1`. -/
private lemma Moment_ev_Smat (d n : ℕ) (P : Profile d) (c₀ c₁ c₀T : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, (Smat P.ψ p.1.1 p.1.2).IsSymm ∧
      (∀ x y, 0 ≤ Smat P.ψ p.1.1 p.1.2 x y) ∧ (∀ x, ∑ y, Smat P.ψ p.1.1 p.1.2 x y = 1) := by
  obtain ⟨W₁, h₁⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, h₂⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T,
    (Moment_tendsto d n c₀ c₁ c₀T).eventually (eventually_ge_atTop (max W₁ W₂))] with p hp hW
  change max W₁ W₂ ≤ (p.1.1 : ℝ) at hW
  obtain ⟨hs, hn⟩ := h₁ p.1.1 p.1.2 hp ((le_max_left _ _).trans hW)
  obtain ⟨-, hrow, -⟩ :=
    mem_doublyStochastic_iff_sum.mp (h₂ p.1.1 p.1.2 hp ((le_max_right _ _).trans hW))
  exact ⟨hs, hn, hrow⟩

/-- `0 ≤ B_{xy} ≤ 1` for `W ≥ 1`, `d ≥ 2`. -/
private lemma Moment_bB_le_one (d L W : ℕ) (hd : 2 ≤ d) (hW : 1 ≤ (W : ℝ)) (x y : Zd d L) :
    0 ≤ bB d L W x y ∧ bB d L W x y ≤ 1 := by
  unfold bB
  have h0 : (0 : ℝ) ≤ (zdistInf d L (x - y) : ℝ) := Nat.cast_nonneg _
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨by positivity, ?_⟩
  have h1 : (W : ℝ) ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num)
  have h2 : ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h3 : 0 ≤ ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) := by positivity
  calc (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) ≤ 1 * 1 :=
        mul_le_mul h1 h2 h3 zero_le_one
    _ = 1 := one_mul 1

private lemma Moment_mem_chainLabelsAux_succ {f b : ℕ} {o : List ℕ} :
    o ∈ chainLabelsAux (f + 1) b ↔ ∃ j, j ≤ b ∧ 2 ≤ j ∧ j % 2 = 0 ∧
      (o = [j + 2] ∨ ∃ o' ∈ chainLabelsAux f (b - j), (j + 2) :: o' = o) := by
  simp only [chainLabelsAux, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
    List.mem_map, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨j, ⟨hj, h2, h3⟩, h⟩
    exact ⟨j, by omega, h2, h3, h⟩
  · rintro ⟨j, hj, h2, h3, h⟩
    exact ⟨j, ⟨by omega, h2, h3⟩, h⟩

private lemma Moment_chainLabelsAux_entries :
    ∀ f b, ∀ o ∈ chainLabelsAux f b, ∀ e ∈ o, 4 ≤ e ∧ e ≤ b + 2 ∧ e % 2 = 0 := by
  intro f
  induction f with
  | zero => intro b o ho; simp [chainLabelsAux] at ho
  | succ f ih =>
    intro b o ho e he
    obtain ⟨j, hj, h2, h3, h | ⟨o', ho', h⟩⟩ := Moment_mem_chainLabelsAux_succ.1 ho <;> subst h
    · obtain rfl : e = j + 2 := by simpa using he
      omega
    · rcases List.mem_cons.1 he with rfl | he
      · omega
      · have := ih _ o' ho' e he
        omega

/-- The labels of `Σ_T^{(n)}` have entries even in `[4, n]` ([II, (3.3)–(3.4)]). -/
private lemma Moment_chainLabels_entries (n : ℕ) :
    ∀ o ∈ chainLabels n, ∀ l ∈ o, 4 ≤ l ∧ l ≤ n ∧ Even l := by
  intro o ho l hl
  obtain ⟨h1, h2, h3⟩ := Moment_chainLabelsAux_entries _ _ o ho l hl
  exact ⟨h1, by omega, Nat.even_iff.2 h3⟩

/-- The scaling order of a labelled `Θ` edge with entries `≥ 2` is at least `2`. -/
private lemma Moment_theta_ord (o : List ℕ) (ho : ∀ l ∈ o, 2 ≤ l) :
    (2 : ℤ) ≤ (Kind.theta o).ord := by
  have h : 2 * o.length ≤ o.sum := by
    induction o with
    | nil => simp
    | cons l o ih =>
      simp only [List.length_cons, List.sum_cons]
      have := ho l (List.mem_cons_self ..)
      have := ih fun l' hl' => ho l' (List.mem_cons_of_mem _ hl')
      omega
  simp only [Kind.ord]
  omega

/-- The chain of the data record of the model is the chain of the deterministic record of the
self-energies `Σ_l`. -/
private lemma Moment_chain_eq (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (o : List ℕ) (ω : Sample (Zd d L)) :
    (rbmData d P Sig W L z ω).chain o =
      (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)).chain o :=
  Moment_chain_congr _ _ (Moment_theta_eq (Smat P.ψ W L) z hmat ω) o fun _ _ => rfl

/-! ## Dotted blocks -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
private def Moment_dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
private lemma Moment_dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    Moment_dotRel cs ≤ Moment_dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

omit [DecidableEq V] in
private lemma Moment_flatten_map_singleton (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private lemma Moment_joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
private def Moment_blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

private lemma Moment_dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = Moment_blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, Moment_blockStep]

private lemma Moment_dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

private lemma Moment_dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [Moment_dotBlocks_nil, Moment_flatten_map_singleton]
  | append_singleton cs c ih =>
    rw [Moment_dotBlocks_snoc, Moment_blockStep]
    split_ifs
    · exact (Moment_joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

/-- Two atoms of one block are joined by a path of dotted edges. -/
private lemma Moment_dotBlocks_conn (as : List V) (cs : List (Comp V)) :
    ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, Relation.EqvGen (Moment_dotRel cs) u v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB u hu v hv
    rw [Moment_dotBlocks_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact Relation.EqvGen.refl _
  | append_singleton cs c ih =>
    have hmono : ∀ u v, Relation.EqvGen (Moment_dotRel cs) u v →
        Relation.EqvGen (Moment_dotRel (cs ++ [c])) u v := fun u v h =>
      Relation.EqvGen.mono (Moment_dotRel_mono fun c' hc' => List.mem_append_left _ hc') u v h
    intro B hB u hu v hv
    rw [Moment_dotBlocks_snoc, Moment_blockStep] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact hmono _ _ (ih B (List.mem_of_mem_filter hB) u hu v hv)
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : Relation.EqvGen (Moment_dotRel (cs ++ [c])) c.x c.y :=
          Relation.EqvGen.rel _ _ ⟨c, List.mem_append_right _ (List.mem_singleton_self _), hk,
            rfl, rfl⟩
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, Relation.EqvGen (Moment_dotRel (cs ++ [c])) z c.x := by
          intro w hw z hz
          have hw' := List.mem_filter.1 hw
          have hcont := hw'.2
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hcont
          rcases hcont with hx | hy
          · exact hmono _ _ (ih w hw'.1 z hz _ hx)
          · exact (hmono _ _ (ih w hw'.1 z hz _ hy)).trans _ _ _ hxy.symm
        rw [List.mem_flatten] at hu hv
        obtain ⟨w₁, hw₁, hu⟩ := hu
        obtain ⟨w₂, hw₂, hv⟩ := hv
        exact (key w₁ hw₁ u hu).trans _ _ _ (key w₂ hw₂ v hv).symm
    · exact hmono _ _ (ih B hB u hu v hv)

/-- The two ends of a dotted edge lie in one block. -/
private lemma Moment_dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [Moment_dotBlocks_snoc, Moment_blockStep]
    have hmem : ∀ a ∈ as, ∃ B ∈ dotBlocks as cs, a ∈ B := by
      intro a ha
      have := (Moment_dotBlocks_flatten_perm as cs).mem_iff.2 ha
      rwa [List.mem_flatten] at this
    split_ifs with hk
    · rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨B, hB, hx, hy⟩ := ih' c' hc' hk'
        by_cases hcB : (B.contains c.x || B.contains c.y) = true
        · refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c.x || B.contains c.y).flatten,
            ?_, ?_, ?_⟩
          · unfold joinBlocks
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hx⟩
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hy⟩
        · refine ⟨B, ?_, hx, hy⟩
          unfold joinBlocks
          refine List.mem_append_left _ (List.mem_filter.2 ⟨hB, ?_⟩)
          simpa using hcB
      · rw [List.mem_singleton] at hc'
        subst hc'
        obtain ⟨hxa, hya⟩ := hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨B₁, hB₁, hx⟩ := hmem _ hxa
        obtain ⟨B₂, hB₂, hy⟩ := hmem _ hya
        refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c'.x || B.contains c'.y).flatten,
          ?_, ?_, ?_⟩
        · unfold joinBlocks
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [List.mem_flatten]
          exact ⟨B₁, List.mem_filter.2 ⟨hB₁, by simp [hx]⟩, hx⟩
        · rw [List.mem_flatten]
          exact ⟨B₂, List.mem_filter.2 ⟨hB₂, by simp [hy]⟩, hy⟩
    · rcases List.mem_append.1 hc' with hc' | hc'
      · exact ih' c' hc' hk'
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact absurd hk' hk

omit [DecidableEq V] in
/-- Reachability in the graph of a relation is the equivalence generated by it. -/
private lemma Moment_reachable_fromRel_iff (r : V → V → Prop) (u v : V) :
    (SimpleGraph.fromRel r).Reachable u v ↔ Relation.EqvGen r u v := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Relation.EqvGen.refl _
    | cons hadj _ ih =>
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact (Relation.EqvGen.rel _ _ h).trans _ _ _ ih
      · exact (Relation.EqvGen.rel _ _ h).symm.trans _ _ _ ih
  · intro h
    induction h with
    | rel a b hab =>
      by_cases hne : a = b
      · rw [hne]
      · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hab⟩).reachable
    | refl a => exact SimpleGraph.Reachable.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end Blocks

private lemma Moment_mem_allAtoms {k n : ℕ} (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | b <;> simp [allAtoms]

private lemma Moment_allAtoms_nodup {k n : ℕ} : (allAtoms k n).Nodup := by
  unfold allAtoms
  refine List.Nodup.append ((List.nodup_finRange k).map Sum.inl_injective)
    ((List.nodup_finRange n).map Sum.inr_injective) ?_
  simp [List.disjoint_left]

/-- An atom lies in at most one block. -/
private lemma Moment_block_unique {k n : ℕ} (cs : List (Comp (Atom k n))) {B₁ B₂ : List (Atom k n)}
    (h₁ : B₁ ∈ dotBlocks (allAtoms k n) cs) (h₂ : B₂ ∈ dotBlocks (allAtoms k n) cs)
    {v : Atom k n} (hv₁ : v ∈ B₁) (hv₂ : v ∈ B₂) : B₁ = B₂ := by
  have hnd : (dotBlocks (allAtoms k n) cs).flatten.Nodup :=
    (Moment_dotBlocks_flatten_perm _ cs).nodup_iff.2 Moment_allAtoms_nodup
  rw [List.nodup_flatten] at hnd
  by_contra hne
  have := hnd.2.forall h₁ h₂ hne
  exact this hv₁ hv₂

/-- Two atoms joined by a path of dotted edges lie in one block. -/
private lemma Moment_mem_block_of_sameBlock {k n : ℕ} (Γ : Graph k n) {u v : Atom k n}
    (h : Γ.SameBlock u v) : ∃ B ∈ dotBlocks (allAtoms k n) Γ.comps, u ∈ B ∧ v ∈ B := by
  unfold Graph.SameBlock Graph.dotGraph at h
  rw [Moment_reachable_fromRel_iff] at h
  induction h with
  | rel a b hab =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hab
    exact Moment_dotBlocks_joined _ _ (fun c _ => ⟨Moment_mem_allAtoms _, Moment_mem_allAtoms _⟩)
      c hc hk
  | refl a =>
    have := (Moment_dotBlocks_flatten_perm (allAtoms k n) Γ.comps).mem_iff.2
      (Moment_mem_allAtoms a)
    rw [List.mem_flatten] at this
    obtain ⟨B, hB, ha⟩ := this
    exact ⟨B, hB, ha, ha⟩
  | symm a b _ ih =>
    obtain ⟨B, hB, ha, hb⟩ := ih
    exact ⟨B, hB, hb, ha⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨B₁, hB₁, ha, hb⟩ := ih1
    obtain ⟨B₂, hB₂, hb', hc⟩ := ih2
    obtain rfl := Moment_block_unique Γ.comps hB₁ hB₂ hb hb'
    exact ⟨B₁, hB₁, ha, hc⟩

/-- Two atoms of one block are joined by a path of dotted edges. -/
private lemma Moment_sameBlock_of_mem_block {k n : ℕ} (Γ : Graph k n) {B : List (Atom k n)}
    (hB : B ∈ dotBlocks (allAtoms k n) Γ.comps) {u v : Atom k n} (hu : u ∈ B) (hv : v ∈ B) :
    Γ.SameBlock u v := by
  unfold Graph.SameBlock Graph.dotGraph
  rw [Moment_reachable_fromRel_iff]
  exact Moment_dotBlocks_conn _ _ B hB u hu v hv

/-- A `⊕/⊖`-recollision graph ([II, Def 3.1 (i)]) is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`. -/
private lemma Moment_diagRecoll_of_recoll {n : ℕ} (Γ : Graph 3 n)
    (h : Γ.IsRecollision {1, 2}) : Γ.DiagRecoll := by
  obtain ⟨c, hc, hk, hxy⟩ := h
  obtain ⟨B, hB, hx, hy⟩ := Moment_dotBlocks_joined (allAtoms 3 n) Γ.comps
    (fun c _ => ⟨Moment_mem_allAtoms _, Moment_mem_allAtoms _⟩) c hc hk
  unfold Graph.DiagRecoll
  rw [List.any_eq_true]
  refine ⟨B, hB, ?_⟩
  rcases hxy with ⟨⟨b, hb, hbx⟩, hr⟩ | ⟨⟨b, hb, hby⟩, hr⟩
  · have hBb : B.contains (Sum.inl 1) = true ∨ B.contains (Sum.inl 2) = true := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · left; rw [← hbx]; simpa using hx
      · right; rw [← hbx]; simpa using hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
    exact ⟨hBb, c.y, hy, hr⟩
  · have hBb : B.contains (Sum.inl 1) = true ∨ B.contains (Sum.inl 2) = true := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · left; rw [← hby]; simpa using hy
      · right; rw [← hby]; simpa using hy
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
    exact ⟨hBb, c.x, hx, hr⟩

/-- Under the clause on the external atoms, `⊕` and `⊖` in one dotted block force an internal
atom in that block. -/
private lemma Moment_diagRecoll_of_pmBlock {n : ℕ} (Γ : Graph 3 n) (hE : Γ.ExtClause)
    (h : Γ.PMBlock) : Γ.DiagRecoll := by
  unfold Graph.PMBlock Graph.pmBlockB at h
  rw [List.any_eq_true] at h
  obtain ⟨B, hB, hpm⟩ := h
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hpm
  have hs := Moment_sameBlock_of_mem_block Γ hB hpm.1 hpm.2
  obtain ⟨b, hb⟩ := hE.1 (.inl 1) (.inl 2) (by simp) hs
  obtain ⟨B', hB', h1, h2⟩ := Moment_mem_block_of_sameBlock Γ hb
  unfold Graph.DiagRecoll
  rw [List.any_eq_true]
  refine ⟨B', hB', ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem]
  exact ⟨Or.inl h1, .inr b, h2, rfl⟩


/-! ## Exponents -/

/-- On `adm(c₀, c₁)` with `W ≥ 2^{d}`: `B_{xy} ≥ W^{−(3 + (d−2)/c₁)}`. -/
private lemma Moment_bB_lower (d : ℕ) (hd : 2 ≤ d) (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (p : SizeL) (hp : p.1 ∈ adm c₀ c₁) (hW : (2 : ℝ) ^ d ≤ p.1.1) (x y : Zd d p.1.2) :
    (p.1.1 : ℝ) ^ (-(3 + ((d : ℝ) - 2) / c₁)) ≤ bB d p.1.2 p.1.1 x y := by
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hW1 : 1 ≤ W := le_trans h2d hW
  have hW0 : 0 < W := by linarith
  have hWL : W ≤ L := Moment_W_le_L hc₀ p hp
  have hL0 : 0 < L := by linarith
  have hLc : L ^ c₁ ≤ W := hp.1
  have hLW : L ≤ W ^ (1 / c₁) := by
    calc L = (L ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul hL0.le, mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ W ^ (1 / c₁) := Real.rpow_le_rpow (Real.rpow_nonneg hL0.le _) hLc (by positivity)
  have hdist : (zdistInf d p.1.2 (x - y) : ℝ) + W ≤ 2 * L := by
    have h := zdistInf_le_half d p.1.2 (x - y)
    have h' : (zdistInf d p.1.2 (x - y) : ℝ) ≤ L := by
      have : zdistInf d p.1.2 (x - y) ≤ p.1.2 := h.trans (Nat.div_le_self _ _)
      rw [hLdef]; exact_mod_cast this
    linarith
  have hpos : 0 < (zdistInf d p.1.2 (x - y) : ℝ) + W := by positivity
  have he : 2 - (d : ℝ) ≤ 0 := by linarith
  have h1 : (2 * L) ^ (2 - (d : ℝ)) ≤ ((zdistInf d p.1.2 (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hdist he
  have h2 : (2 * W ^ (1 / c₁)) ^ (2 - (d : ℝ)) ≤ (2 * L) ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) he
  have h3 : (2 * W ^ (1 / c₁)) ^ (2 - (d : ℝ)) =
      (2 : ℝ) ^ (2 - (d : ℝ)) * W ^ ((2 - (d : ℝ)) / c₁) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le]
    congr 2; ring
  have h4 : W ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (2 - (d : ℝ)) := by
    have e1 : (2 : ℝ) ^ (2 - (d : ℝ)) = ((2 : ℝ) ^ (d - 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; ring_nf
    have e2 : W ^ (-1 : ℝ) = W⁻¹ := Real.rpow_neg_one W
    rw [e1, e2]
    refine inv_anti₀ (by positivity) ?_
    calc (2 : ℝ) ^ (d - 2 : ℝ) ≤ (2 : ℝ) ^ (d : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (2 : ℝ) ^ d := Real.rpow_natCast _ _
      _ ≤ W := hW
  unfold bB
  calc W ^ (-(3 + ((d : ℝ) - 2) / c₁))
      = W ^ (-2 : ℝ) * (W ^ (-1 : ℝ) * W ^ ((2 - (d : ℝ)) / c₁)) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; congr 1; ring
    _ ≤ W ^ (-2 : ℝ) * ((2 : ℝ) ^ (2 - (d : ℝ)) * W ^ ((2 - (d : ℝ)) / c₁)) := by
        gcongr
    _ ≤ W ^ (-2 : ℝ) * ((zdistInf d p.1.2 (x - y) : ℝ) + W) ^ (2 - (d : ℝ)) := by
        gcongr
        rw [← h3]
        exact h2.trans h1

/-- A larger exponent factor `a ≥ b` with a negative rate `e` gives a smaller power. -/
private lemma Moment_rpow_mul_le (W : ℝ) (hW : 1 ≤ W) (a b e : ℝ) (he : e ≤ 0) (hab : b ≤ a) :
    W ^ (a * e) ≤ W ^ (b * e) :=
  Real.rpow_le_rpow_of_exponent_le hW (by nlinarith)


/-! ## A priori bounds along the filter -/

/-- On `adm(c₀, c₁)` with `W ≥ 1`, every `z ∈ 𝐃(κ, ε)` has `0 < Im z` and `(Im z)⁻¹ ≤ W^{2/c₁}`. -/
private lemma Moment_im_inv {c₀ c₁ κ ε : ℝ} (hc₁ : 0 < c₁) (hε : 0 < ε) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (hW : (1 : ℝ) ≤ p.1.1) (z : ℂ) (hz : z ∈ specDom κ ε p.1.1 p.1.2) :
    0 < z.im ∧ (z.im)⁻¹ ≤ (p.1.1 : ℝ) ^ (2 / c₁) := by
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by rw [hLdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hW0 : 0 < W := by linarith
  have hL0 : 0 < L := by linarith
  have hLe : 0 < L ^ (2 - ε) := Real.rpow_pos_of_pos hL0 _
  have hlow : W ^ 2 / L ^ (2 - ε) ≤ z.im := hz.2.1
  have hpos : 0 < W ^ 2 / L ^ (2 - ε) := by positivity
  have him : 0 < z.im := lt_of_lt_of_le hpos hlow
  refine ⟨him, ?_⟩
  have h1 : (z.im)⁻¹ ≤ (W ^ 2 / L ^ (2 - ε))⁻¹ := inv_anti₀ hpos hlow
  have h2 : (W ^ 2 / L ^ (2 - ε))⁻¹ ≤ L ^ (2 - ε) := by
    rw [inv_div, div_le_iff₀ (by positivity)]
    have : 1 ≤ W ^ 2 := one_le_pow₀ hW
    nlinarith
  have h3 : L ^ (2 - ε) ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLc : L ^ c₁ ≤ W := hp.1
  have h4 : L ^ (2 : ℝ) ≤ W ^ (2 / c₁) := by
    calc L ^ (2 : ℝ) = (L ^ c₁) ^ (2 / c₁) := by
          rw [← Real.rpow_mul hL0.le]; congr 1; field_simp
      _ ≤ W ^ (2 / c₁) := Real.rpow_le_rpow (Real.rpow_nonneg hL0.le _) hLc (by positivity)
  linarith

/-- The generators of the coefficient ring at `m(z)`, `z ∈ 𝐃(κ, ε)`, are bounded by
`max(4, 4/√(2κ))` ([I, Def 2.6]). -/
private lemma Moment_cvar_le {κ ε : ℝ} (hκ : 0 < κ) {W L : ℕ} (z : ℂ) (hz : z ∈ specDom κ ε W L)
    (him : 0 < z.im) (i : CVar) :
    ‖CVar.eval (msc z) i‖ ≤ max 4 (4 / Real.sqrt (2 * κ)) := by
  have hre : |z.re| < 2 - κ := hz.1
  have him1 : z.im ≤ 1 := hz.2.2
  have hz3 : ‖z‖ ≤ 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos him] at this
    linarith
  have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_lt_one him).le
  have hm4 : 1 / 4 ≤ ‖msc z‖ := norm_msc_ge_quarter z him hz3
  have hr := norm_one_sub_msc_sq_ge κ hκ z hre him him1
  have hs : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  have hinv : ‖(msc z)⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    calc ‖msc z‖⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hm4
      _ = 4 := by norm_num
  have hrinv : ‖(1 - msc z ^ 2)⁻¹‖ ≤ 4 / Real.sqrt (2 * κ) := by
    rw [norm_inv]
    calc ‖1 - msc z ^ 2‖⁻¹ ≤ (Real.sqrt (2 * κ) / 4)⁻¹ := inv_anti₀ (by positivity) hr
      _ = 4 / Real.sqrt (2 * κ) := by rw [inv_div]
  cases i with
  | m => exact hm1.trans (by norm_num : (1 : ℝ) ≤ 4) |>.trans (le_max_left _ _)
  | mInv => exact hinv.trans (le_max_left _ _)
  | r => exact hrinv.trans (le_max_right _ _)
  | mBar =>
    simp only [CVar.eval, norm_star]
    exact hm1.trans (by norm_num : (1 : ℝ) ≤ 4) |>.trans (le_max_left _ _)
  | mBarInv =>
    simp only [CVar.eval]
    rw [← star_inv₀, norm_star]
    exact hinv.trans (le_max_left _ _)
  | rBar =>
    simp only [CVar.eval]
    have : (1 - star (msc z) ^ 2)⁻¹ = star ((1 - msc z ^ 2)⁻¹) := by
      rw [star_inv₀, star_sub, star_one, star_pow]
    rw [this, norm_star]
    exact hrinv.trans (le_max_right _ _)

/-- A coefficient evaluated at generators bounded by `K₀` is bounded by a constant. -/
private lemma Moment_coeff_le (q : Coeff) (X : CVar → ℂ) (K₀ : ℝ) (hK : ∀ i, ‖X i‖ ≤ K₀) :
    ‖MvPolynomial.eval X q‖ ≤ ∑ s ∈ q.support, ‖q.coeff s‖ * ∏ i ∈ s.support, K₀ ^ s i := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hK i) _

/-- Eventually along the filter, `|S^±_{xy}| ≤ K` at every `z ∈ 𝐃(κ, ε)` ([I, Lemma 2.2]). -/
private lemma Moment_ev_Sp (d n : ℕ) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε) (U : SizeL → Type) (z : ∀ p, U p → ℂ)
    (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) :
    ∃ K : ℝ, ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ (u : U p) (x y : Zd d p.1.2),
      ‖Splus (msc (z p u)) (Smat P.ψ p.1.1 p.1.2) x y‖ ≤ K ∧
        ‖Sminus (msc (z p u)) (Smat P.ψ p.1.1 p.1.2) x y‖ ≤ K := by
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨C, hC⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨W₁, h1⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨Ks, W₂, hS⟩ := Splus_decay_msc d c₀ c₁ hc₀ hc₁ P.ψ c' hc' C κ 1 1 hκ one_pos one_pos
  refine ⟨2 * |Ks|, ?_⟩
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, (Moment_tendsto d n c₀ c₁ c₀T).eventually
    (eventually_ge_atTop (max 1 (max W₁ W₂)))] with p hp hW u x y
  change max 1 (max W₁ W₂) ≤ (p.1.1 : ℝ) at hW
  have hW1 : (1 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
  have hW₁ : W₁ ≤ p.1.1 := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW₂ : W₂ ≤ p.1.1 := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨him, -⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 (z p u) (hz p u)
  obtain ⟨hp1, hp2⟩ := hS p.1.1 p.1.2 hp hW₂ _ (h1 p.1.1 p.1.2 hp hW₁) (hC p.1.1 p.1.2 hp)
    (z p u) him (hz p u).1 x y
  have hb : splusBound (d := d) (L := p.1.2) p.1.1 1 1 x y ≤ 2 := by
    unfold splusBound
    have hdW : (1 : ℝ) ≤ (zdistInf d p.1.2 (x - y) : ℝ) + p.1.1 := by
      have := (Nat.cast_nonneg (α := ℝ) (zdistInf d p.1.2 (x - y))); linarith
    have e2 : ((zdistInf d p.1.2 (x - y) : ℝ) + p.1.1) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hdW (by norm_num)
    have e1 : (if (zdistInf d p.1.2 (x - y) : ℝ) ≤ (p.1.1 : ℝ) ^ (1 + (1 : ℝ)) then
        (((p.1.1 : ℝ)) ^ d)⁻¹ else 0) ≤ 1 := by
      split_ifs
      · exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
      · norm_num
    linarith
  have hb0 : 0 ≤ splusBound (d := d) (L := p.1.2) p.1.1 1 1 x y := by
    unfold splusBound
    have : 0 ≤ (if (zdistInf d p.1.2 (x - y) : ℝ) ≤ (p.1.1 : ℝ) ^ (1 + (1 : ℝ)) then
        (((p.1.1 : ℝ)) ^ d)⁻¹ else 0) := by split_ifs <;> positivity
    positivity
  have hK : Ks * splusBound (d := d) (L := p.1.2) p.1.1 1 1 x y ≤ 2 * |Ks| := by
    calc Ks * splusBound (d := d) (L := p.1.2) p.1.1 1 1 x y
        ≤ |Ks| * splusBound (d := d) (L := p.1.2) p.1.1 1 1 x y :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hb0
      _ ≤ |Ks| * 2 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = 2 * |Ks| := by ring
  exact ⟨hp1.trans hK, hp2.trans hK⟩

/-- Eventually along the filter, the chain of a label with entries even in `[4, n]` is bounded by
`W` at every `z ∈ 𝐃(κ, ε)` ([I, Lemma 6.2]). -/
private lemma Moment_ev_chain (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (n : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig n) (U : SizeL → Type)
    (z : ∀ p, U p → ℂ) (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) (o : List ℕ)
    (ho : labelOK n o = true) :
    ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ (u : U p) (ω : Sample (Zd d p.1.2)) (x y : Zd d p.1.2),
      ‖(rbmData d P Sig p.1.1 p.1.2 (z p u) ω).chain o x y‖ ≤ (p.1.1 : ℝ) := by
  have ho' : ∀ l ∈ o, 4 ≤ l ∧ l ≤ n ∧ Even l := by
    intro l hl
    have := List.all_eq_true.1 ho l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, Nat.even_iff.2 this.2⟩
  obtain ⟨W₀, hW₀⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (sigKer (smatVar P) Sig) o
    (fun l hl => ⟨(hSE l (ho' l hl).1 (ho' l hl).2.1 (ho' l hl).2.2).2.1,
      (hSE l (ho' l hl).1 (ho' l hl).2.1 (ho' l hl).2.2).2.2⟩) 1 one_pos
  obtain ⟨W₁, hW₁⟩ := detData_smatVar_eq_on_adm d P Sig c₀ c₁ hc₀ hc₁
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, (Moment_tendsto d n c₀ c₁ c₀T).eventually
    (eventually_ge_atTop (max 1 (max W₀ W₁)))] with p hp hW u ω x y
  change max 1 (max W₀ W₁) ≤ (p.1.1 : ℝ) at hW
  have hW1 : (1 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
  rw [Moment_chain_eq, ← hW₁ p.1.1 p.1.2 hp ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
    (z p u)]
  refine (hW₀ p.1.1 p.1.2 hp ((le_max_left _ _).trans ((le_max_right _ _).trans hW)) (z p u)
    (hz p u) x y).trans ?_
  have hord : (p.1.1 : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hW1 ?_
    have h2 : (2 : ℝ) ≤ (((Kind.theta o).ord : ℤ) : ℝ) := by
      exact_mod_cast Moment_theta_ord o fun l hl => by have := (ho' l hl).1; omega
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have : 0 ≤ ((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d := mul_nonneg (by linarith) hd0
    linarith
  obtain ⟨hB0, hB1⟩ := Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 x y
  rw [Real.rpow_one]
  calc (p.1.1 : ℝ) * (p.1.1 : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        bB d p.1.2 p.1.1 x y ≤ (p.1.1 : ℝ) * 1 * 1 := by gcongr
    _ = p.1.1 := by ring


/-- Finitely many eventual statements hold eventually together. -/
private lemma Moment_ev_list {α β : Type*} {F : Filter β} (l : List α) {Q : α → β → Prop}
    (h : ∀ x ∈ l, ∀ᶠ p in F, Q x p) : ∀ᶠ p in F, ∀ x ∈ l, Q x p := by
  induction l with
  | nil => exact Eventually.of_forall fun p x hx => by simp at hx
  | cons a l ih =>
    filter_upwards [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
      with p ha hl x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact hl x hx

/-- `(W^b)^m = W^{b m}`. -/
private lemma Moment_rpow_pow (W : ℝ) (hW : 0 ≤ W) (b : ℝ) (m : ℕ) :
    (W ^ b) ^ m = W ^ (b * m) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]

/-- The fields `S^±` of the data record of the model are `S^±(m)` of [I, (2.1)]. -/
private lemma Moment_Sp_eq (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L]
    (z : ℂ) (ω : Sample (Zd d L)) :
    (rbmData d P Sig W L z ω).Sp = Splus (msc z) (Smat P.ψ W L) ∧
      (rbmData d P Sig W L z ω).Sm = Sminus (msc z) (Smat P.ψ W L) := by
  constructor
  · change (msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ))⁻¹ = Splus (msc z) (Smat P.ψ W L)
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  · change ((msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • (Smat P.ψ W L).map fun r => (r : ℂ))⁻¹).map star =
        Sminus (msc z) (Smat P.ψ W L)
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl

/-- A priori bound, polynomial in `W`, of the value of a graph with the kinds of [II, Def 3.2] on
the data record of the model, eventually along the filter and uniformly in `u, 𝔞, 𝔟` and the
sample. -/
private lemma Moment_apriori_graph (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (n : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig n) (U : SizeL → Type)
    (z : ∀ p, U p → ℂ) (hz : ∀ p u, z p u ∈ specDom κ ε p.1.1 p.1.2) {nI : ℕ} (g : Graph 3 nI)
    (hK : g.TKinds n) :
    ∃ K : ℝ, ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ (u : U p) (a b : Zd d p.1.2)
      (ω : Sample (Zd d p.1.2)),
      ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p u)) ![a, b, b] ω‖ ≤
        (p.1.1 : ℝ) ^ K := by
  set e : ℝ := 2 / c₁ + 1 with he
  have he0 : 1 ≤ e := by have : 0 ≤ 2 / c₁ := by positivity
                         linarith
  set c := g.comps.length with hcdef
  set K₀ : ℝ := max 4 (4 / Real.sqrt (2 * κ)) with hK₀
  set Cg : ℝ := ∑ s ∈ g.coeff.support, ‖g.coeff.coeff s‖ * ∏ i ∈ s.support, K₀ ^ s i with hCg
  obtain ⟨KS, hKS⟩ := Moment_ev_Sp d n P c₀ c₁ κ ε c₀T hc₀ hc₁ hκ hε U z hz
  have hch : ∀ᶠ p in llFilter d n c₀ c₁ c₀T, ∀ c' ∈ g.comps, ∀ o, c'.kind = .theta o →
      ∀ (u : U p) (ω : Sample (Zd d p.1.2)) (x y : Zd d p.1.2),
        ‖(rbmData d P Sig p.1.1 p.1.2 (z p u) ω).chain o x y‖ ≤ (p.1.1 : ℝ) := by
    refine Moment_ev_list g.comps fun c' hc' => ?_
    by_cases h : ∃ o, c'.kind = .theta o
    · obtain ⟨o, ho⟩ := h
      have hok : labelOK n o = true := by
        have := List.all_eq_true.1 hK c' hc'
        simp only [Comp.isTKind, ho, Bool.and_eq_true] at this
        exact this.2
      filter_upwards [Moment_ev_chain d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε n Sig hSE U z hz o hok]
        with p hp o' ho'
      rw [ho] at ho'
      cases ho'
      exact hp
    · exact Eventually.of_forall fun p o ho => absurd ⟨o, ho⟩ h
  refine ⟨(d : ℝ) * nI / c₁ + 1 + (e + 1) * c + (e + 1) * (c + 1) * c, ?_⟩
  filter_upwards [Moment_ev_adm d n c₀ c₁ c₀T, Moment_ev_Smat d n P c₀ c₁ c₀T hc₀ hc₁, hKS, hch,
    (Moment_tendsto d n c₀ c₁ c₀T).eventually (eventually_ge_atTop (max 2 (max KS Cg)))]
    with p hp hSm hKSp hchp hW u a b ω
  change max 2 (max KS Cg) ≤ (p.1.1 : ℝ) at hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW2 : 2 ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hKSW : KS ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hCgW : Cg ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  obtain ⟨him, himW⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 (z p u) (hz p u)
  have hWe : W ≤ W ^ e := by
    calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
      _ ≤ W ^ e := Real.rpow_le_rpow_of_exponent_le hW1 he0
  have hM1 : 1 ≤ W ^ e := hW1.trans hWe
  have hbound := Moment_valR_le n g hK (Smat P.ψ p.1.1 p.1.2)
    (rbmData d P Sig p.1.1 p.1.2 (z p u)) (W ^ e) hM1 (fun _ => rfl)
    (norm_msc_lt_one him).le
    (fun ω' x y => by
      rw [Moment_Gm_empty]
      refine (norm_green_entry_le (hmat_isHermitian ω') him.ne' x y).trans ?_
      rw [abs_of_pos him]
      exact himW.trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)))
    (fun ω' x y => by
      change ‖((Smat P.ψ p.1.1 p.1.2 x y : ℝ) : ℂ)‖ ≤ W ^ e
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSm.2.1 x y)]
      have : Smat P.ψ p.1.1 p.1.2 x y ≤ ∑ y', Smat P.ψ p.1.1 p.1.2 x y' :=
        Finset.single_le_sum (fun y' _ => hSm.2.1 x y') (Finset.mem_univ y)
      rw [hSm.2.2 x] at this
      exact this.trans hM1)
    (fun ω' x y => by
      rw [(Moment_Sp_eq d P Sig p.1.1 p.1.2 (z p u) ω').1]
      exact (hKSp u x y).1.trans (hKSW.trans hWe))
    (fun ω' x y => by
      rw [(Moment_Sp_eq d P Sig p.1.1 p.1.2 (z p u) ω').2]
      exact (hKSp u x y).2.trans (hKSW.trans hWe))
    (fun ω' c' hc' o ho x y => (hchp c' hc' o ho u ω' x y).trans hWe) ![a, b, b] ω
  refine hbound.trans ?_
  -- the polynomial bound in `W`
  have hcard : (Fintype.card (Zd d p.1.2) : ℝ) ^ nI ≤ W ^ ((d : ℝ) * nI / c₁) := by
    rw [card_Zd]
    push_cast
    have hL0 : (0 : ℝ) < p.1.2 := by exact_mod_cast Nat.pos_of_ne_zero p.2
    have hLc : (p.1.2 : ℝ) ^ c₁ ≤ W := hp.1
    have hLW : (p.1.2 : ℝ) ≤ W ^ (1 / c₁) := by
      calc (p.1.2 : ℝ) = ((p.1.2 : ℝ) ^ c₁) ^ (1 / c₁) := by
            rw [← Real.rpow_mul hL0.le, mul_one_div_cancel hc₁.ne', Real.rpow_one]
        _ ≤ W ^ (1 / c₁) := Real.rpow_le_rpow (Real.rpow_nonneg hL0.le _) hLc (by positivity)
    calc ((p.1.2 : ℝ) ^ d) ^ nI ≤ ((W ^ (1 / c₁)) ^ d) ^ nI := by gcongr
      _ = W ^ ((d : ℝ) * nI / c₁) := by
        rw [Moment_rpow_pow W hW0.le, Moment_rpow_pow W hW0.le]; congr 1; field_simp
  have hcoef : ‖g.coeff.eval (msc (z p u))‖ ≤ W := by
    refine (Moment_coeff_le g.coeff _ K₀ fun i => Moment_cvar_le hκ (z p u) (hz p u) him i).trans
      hCgW
  have h2M : 2 * W ^ e ≤ W ^ (e + 1) := by
    have h := Real.rpow_add hW0 e 1
    rw [Real.rpow_one] at h
    rw [h]
    have : 0 ≤ W ^ e := Real.rpow_nonneg hW0.le _
    nlinarith
  have hA : (2 * W ^ e) ^ c ≤ W ^ ((e + 1) * c) := by
    rw [← Moment_rpow_pow W hW0.le]
    exact pow_le_pow_left₀ (by positivity) h2M c
  have hA2 : 2 * (2 * W ^ e) ^ c ≤ W ^ ((e + 1) * (c + 1)) := by
    calc 2 * (2 * W ^ e) ^ c ≤ W ^ (e + 1) * W ^ ((e + 1) * c) := by
          refine mul_le_mul ?_ hA (by positivity) (by positivity)
          refine hW2.trans ?_
          calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
            _ ≤ W ^ (e + 1) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = W ^ ((e + 1) * (c + 1)) := by rw [← Real.rpow_add hW0]; congr 1; ring
  have hA3 : (2 * (2 * W ^ e) ^ c) ^ c ≤ W ^ ((e + 1) * (c + 1) * c) := by
    rw [← Moment_rpow_pow W hW0.le]
    exact pow_le_pow_left₀ (by positivity) hA2 c
  calc (Fintype.card (Zd d p.1.2) : ℝ) ^ nI * (‖g.coeff.eval
        (rbmData d P Sig p.1.1 p.1.2 (z p u) 0).m‖ * (2 * W ^ e) ^ c *
        (2 * (2 * W ^ e) ^ c) ^ c)
      ≤ W ^ ((d : ℝ) * nI / c₁) * (W * W ^ ((e + 1) * c) * W ^ ((e + 1) * (c + 1) * c)) := by
        gcongr
        exact hcoef
    _ = W ^ ((d : ℝ) * nI / c₁ + 1 + (e + 1) * c + (e + 1) * (c + 1) * c) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]; ring

/-- The value of a formal sum with a first graph. -/
private lemma Moment_valR_cons {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Σ n : ℕ, Graph k n) (E : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) :
    Expansion.valR (g :: E) PF D e ω = g.2.valR PF D e ω + E.valR PF D e ω := by
  simp [Expansion.valR]

/-! ## The right side of [II, (8.18)] without the `Q`-graphs -/

/-- The value of a concatenation of formal sums. -/
private lemma Moment_valR_append {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (E F : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    (E ++ F).valR PF D e ω = E.valR PF D e ω + F.valR PF D e ω := by
  simp [Expansion.valR, List.map_append, List.sum_append]

/-- The norm of the value of a formal sum is at most the sum of the norms of the values. -/
private lemma Moment_norm_valR_le {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    ‖E.valR PF D e ω‖ ≤ (E.map fun g => ‖g.2.valR PF D e ω‖).sum := by
  induction E with
  | nil => simp [Expansion.valR]
  | cons g E ih =>
    rw [Moment_valR_cons, List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

/-! ## `T_{𝔞𝔟}` and the identity [II, (8.18)] -/

/-- `T_{xy}` is measurable in the sample. -/
private lemma Moment_meas_T (d L : ℕ) [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ)
    (hz : 0 < z.im) (x y : Zd d L) :
    Measurable fun ω : Sample (Zd d L) => Tvar S (green (hmat ω) z) (msc z) x y := by
  unfold Tvar
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun α _ => ?_
  exact ((polyMeas_of_testFn _ (testFn_green z hz.ne' α y)).1.norm.pow_const 2).const_mul _

/-- `0 ≤ T_{xy} ≤ M²` when `|m| ≤ 1` and `|G_{ab}| ≤ M`, for `S ≥ 0` with row sums `1`. -/
private lemma Moment_T_le {ι : Type} [Fintype ι] (S : Matrix ι ι ℝ)
    (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) (G : Matrix ι ι ℂ) (m : ℂ)
    (hm : ‖m‖ ≤ 1) (M : ℝ) (hG : ∀ a b, ‖G a b‖ ≤ M) (x y : ι) :
    0 ≤ Tvar S G m x y ∧ Tvar S G m x y ≤ M ^ 2 := by
  unfold Tvar
  have h0 : 0 ≤ ∑ α, S x α * ‖G α y‖ ^ 2 :=
    Finset.sum_nonneg fun α _ => mul_nonneg (hnn x α) (sq_nonneg _)
  refine ⟨mul_nonneg (sq_nonneg _) h0, ?_⟩
  have h1 : ∑ α, S x α * ‖G α y‖ ^ 2 ≤ ∑ α, S x α * M ^ 2 :=
    Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hG α y) 2) (hnn x α)
  rw [← Finset.sum_mul, hrow x, one_mul] at h1
  have h2 : ‖m‖ ^ 2 ≤ 1 := by
    have := norm_nonneg m
    nlinarith
  calc ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2 ≤ 1 * M ^ 2 :=
        mul_le_mul h2 h1 h0 zero_le_one
    _ = M ^ 2 := one_mul _

/-- [II, (8.18)] at `e = (𝔞, 𝔟, 𝔟)` on the data record of the model: `T_{𝔞𝔟}` is the value of the
leading terms, `Σ_T^{(n)}`, `R`, `A`, `Err` and of `Q` of [II, (3.1)]. -/
private lemma Moment_T_eq (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (n : ℕ) (𝒯 : TRec)
    (hId : 𝒯.Identity Sig n) (hsh : SelfEnergyShapesUpTo Sig n) (W L : ℕ) [NeZero L] (z : ℂ)
    (hS : (Smat P.ψ W L).IsSymm) (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y)
    (hrow : ∀ x, ∑ y, Smat P.ψ W L x y = 1) (hz : 0 < z.im) (a b : Zd d L)
    (ω : Sample (Zd d L)) :
    ((Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) a b : ℝ) : ℂ) =
      (leadExp ++ sigmaTExp n ++ 𝒯.R ++ 𝒯.A ++ 𝒯.Err).valR ⟨Pexp (Smat P.ψ W L)⟩
          (rbmData d P Sig W L z) ![a, b, b] ω +
        𝒯.Q.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω := by
  rw [← Moment_tGraph_val d P Sig W L z a b ω,
    ← hId (Sample (Zd d L)) (Zd d L) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z)
      (Moment_modelAdm d P Sig W L z hS hnn hrow hz)
      (fun ω' => Moment_sigConsistent d P Sig n hsh W L z ω') ![a, b, b] ω]
  simp only [TRec.rhs, Moment_valR_append]
  ring

end RBM8D
