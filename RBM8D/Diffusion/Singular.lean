import RBM8D.Diffusion.Rooting
import RBM8D.Prob.PartialPoly
import RBM8D.Graph.Local.ModelGauss

/-!
# The identity of [I, Corollary 1.6] at a singular variance matrix

`singularIdStmt`: for a `T`-equation `𝒬` and the Gaussian model of [I, Assumption 1.1] at every
real symmetric `S ≥ 0` with row sums `1`, singular or not,
`|G_{ab}|² − T_{a,bb} = Y'_{ab} + (Σ̃^{(n)} T)_{a,bb}` at every sample.

The proof follows the perturbation of [I, Corollary 1.6] (proof, the case of a singular `S`) at a
fixed sample `ω`:
* `S_ε = (S + ε)/(1 + ε)` is symmetric, `≥ 0`, with row sums `1`, and it is invertible for all
  small `ε > 0` (its determinant is a monic polynomial in `ε`, up to a factor);
* at an invertible `S_ε`, `Θ = |m|² S_ε (1 − |m|² S_ε)⁻¹` is invertible, so that the root `Θ` of
  the rooted `T`-equation [I, (8.14)] can be removed: with `T = |m|² S_ε |G|²` this is the
  identity at `S_ε`;
* every term of the identity is continuous in `ε` at `ε = 0`: `G`, its minors and `m` do not
  depend on `ε`; `S`, `S^±`, `Θ` and the self-energy matrices `Σ_l` are continuous in `S` at
  every `S ≥ 0` with row sums `1`; the partial expectations `P_x` of [I, §1.4] are Gaussian
  integrals whose variances are continuous in `ε`, of continuous functions of polynomial growth
  (the graphs of a `T`-equation have no minors, [II, Def 3.2]), and they converge by dominated
  convergence after the scaling `N(0, v) = √v N(0, 1)`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open MeasureTheory ProbabilityTheory Filter Topology Complex Matrix
open scoped BigOperators NNReal

namespace RBM8D

open Graphs

namespace Singular

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Invertibility of `1 − Y` and the perturbation `S_ε` -/

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

/-- `1 − c S` is invertible over `ℂ` for `S ≥ 0` with row sums `1` and `|c| < 1`. -/
private theorem isUnit_one_sub_smul_map (S : Matrix ι ι ℝ) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (c : ℂ) (hc : ‖c‖ < 1) :
    IsUnit (1 - c • S.map fun r => (r : ℂ)) := by
  refine isUnit_one_sub _ ‖c‖ (fun x => le_of_eq ?_) hc
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (hnn x _), ← Finset.mul_sum, hrow x, mul_one]

/-- `1 − c S` is invertible over `ℝ` for `S ≥ 0` with row sums `1` and `|c| < 1`. -/
private theorem isUnit_one_sub_smul_real (S : Matrix ι ι ℝ) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (c : ℝ) (hc : ‖c‖ < 1) : IsUnit (1 - c • S) := by
  refine isUnit_one_sub _ ‖c‖ (fun x => le_of_eq ?_) hc
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg (hnn x _),
    ← Finset.mul_sum, hrow x, mul_one]

/-- The perturbation `S_ε = (S + ε)/(1 + ε)` of [I, Corollary 1.6] (proof). -/
private def pert (S : Matrix ι ι ℝ) (ε : ℝ) : Matrix ι ι ℝ := (1 + ε)⁻¹ • (S + ε • 1)

private theorem pert_apply (S : Matrix ι ι ℝ) (ε : ℝ) (x y : ι) :
    pert S ε x y = (1 + ε)⁻¹ * (S x y + if x = y then ε else 0) := by
  simp [pert, Matrix.one_apply]

/-- `S_ε → S` as `ε → 0`. -/
private theorem tendsto_pert (S : Matrix ι ι ℝ) : Tendsto (pert S) (𝓝 0) (𝓝 S) := by
  refine tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => ?_
  have h : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹ * (S x y + if x = y then ε else 0)) 0 := by
    refine ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num)).mul ?_
    split_ifs
    · exact continuousAt_const.add continuousAt_id
    · exact continuousAt_const
  have h2 := h.tendsto
  simp only [pert_apply] at h2 ⊢
  simpa using h2

private theorem pert_isSymm {S : Matrix ι ι ℝ} (hS : S.IsSymm) (ε : ℝ) : (pert S ε).IsSymm := by
  ext x y
  rw [Matrix.transpose_apply, pert_apply, pert_apply, hS.apply x y]
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h]

private theorem pert_nonneg {S : Matrix ι ι ℝ} (hnn : ∀ x y, 0 ≤ S x y) {ε : ℝ} (hε : 0 < ε)
    (x y : ι) : 0 ≤ pert S ε x y := by
  rw [pert_apply]
  have := hnn x y
  split_ifs <;> positivity

private theorem pert_rowSum {S : Matrix ι ι ℝ} (hrow : ∀ x, ∑ y, S x y = 1) {ε : ℝ}
    (hε : 0 < ε) (x : ι) : ∑ y, pert S ε x y = 1 := by
  simp only [pert_apply, ← Finset.mul_sum, Finset.sum_add_distrib, hrow x, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  field_simp

/-- For all small `ε > 0`, `S_ε` is invertible: `det (S + ε)` is the characteristic polynomial
of `−S` at `ε`, a monic polynomial, with finitely many roots. -/
private theorem eventually_det_pert_ne (S : Matrix ι ι ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (pert S ε).det ≠ 0 := by
  set p := (-S).charpoly
  have hp : p ≠ 0 := (Matrix.charpoly_monic (-S)).ne_zero
  have hfin : {x | p.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hp
  have hU : ({x | p.IsRoot x} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.sdiff).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0 : ℝ) < ε := hpos
  have heval : p.eval ε = (S + ε • 1).det := by
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> ring
  intro h0
  have hdet : (S + ε • 1).det = 0 := by
    have h1 : pert S ε = (1 + ε)⁻¹ • (S + ε • 1) := rfl
    rw [h1, Matrix.det_smul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (pow_eq_zero_iff'.1 h).1 (by positivity)
    · exact h
  apply hε
  refine ⟨?_, ?_⟩
  · change p.IsRoot ε
    rw [Polynomial.IsRoot, heval, hdet]
  · simpa using hpos'.ne'

/-! ## The identity at an invertible variance matrix -/

/-- The model relations hold for the Gaussian model with the self-energy matrices of `Sig`: the
model relations do not constrain the self-energy field. -/
private theorem modelAdm_sig (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) (hS : S.IsSymm)
    (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) :
    modelAdm (Sample ι) ι ⟨Pexp S⟩ (modelDataSig Sig S z) := by
  obtain ⟨A⟩ := modelAdm_gauss ι S z hS hnn hrow hz
  exact ⟨{ A with }⟩

/-- `(B⁻¹).map ofReal = (B.map ofReal)⁻¹` for the ring inverse. -/
private theorem map_ringInverse (B : Matrix ι ι ℝ) :
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
private theorem theta_eq (S : Matrix ι ι ℝ) (z : ℂ) (H : Sample ι → Matrix ι ι ℂ)
    (ω : Sample ι) : (modelData S z H ω).Theta = cmat (Theta (msc z) S) := by
  simp only [modelData, cmat, Theta]
  rw [Matrix.nonsing_inv_eq_ringInverse]
  have e1 : ((‖msc z‖ ^ 2 • S) * Ring.inverse (1 - ‖msc z‖ ^ 2 • S)).map ((↑) : ℝ → ℂ) =
      (‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) *
        (Ring.inverse (1 - ‖msc z‖ ^ 2 • S)).map ((↑) : ℝ → ℂ) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [e1, map_ringInverse]
  have e2 : (‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) =
      ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ) := by
    ext i j; simp
  have e3 : (1 - ‖msc z‖ ^ 2 • S).map ((↑) : ℝ → ℂ) =
      1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ) := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [e2, e3]

/-- The self-energy matrices below order `k` are the matrices `Σ_l`. -/
private theorem sigUpTo_eq (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) :
    ∀ k l, l < k → sigUpTo Sig S z k l = sigMat Sig S z l := by
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
private theorem chain_congr (D₁ D₂ : Data ι) (hΘ : D₁.Theta = D₂.Theta) (o : List ℕ)
    (hS : ∀ l ∈ o, D₁.Sig l = D₂.Sig l) : D₁.chain o = D₂.chain o := by
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
private theorem compVal_det {V : Type} (N : ℕ) (D₁ D₂ : Data ι) (σ : V → ι) (c : Comp V)
    (hc : c.isDetKind N = true) (hS : D₁.S = D₂.S) (hSp : D₁.Sp = D₂.Sp) (hSm : D₁.Sm = D₂.Sm)
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
private theorem graphVal_det {k n : ℕ} (N : ℕ) (Γ : Graph k n)
    (hΓ : Γ.comps.all (Comp.isDetKind N) = true) (D₁ D₂ : Data ι) (hm : D₁.m = D₂.m)
    (hS : D₁.S = D₂.S) (hSp : D₁.Sp = D₂.Sp) (hSm : D₁.Sm = D₂.Sm)
    (hch : ∀ o, labelOK N o = true → D₁.chain o = D₂.chain o) (e : Fin k → ι) :
    Γ.val D₁ e = Γ.val D₂ e := by
  unfold Graph.val Graph.term
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hm]
  congr 2
  refine List.map_congr_left fun c hc => ?_
  exact compVal_det N D₁ D₂ _ c (List.all_eq_true.1 hΓ c hc) hS hSp hSm hch

/-- The data record of the model with the self-energy matrices of `Sig` is consistent with `Sig`
below order `n`, when the even orders `4, …, n − 1` of `Sig` have the shape of self-energies: the
self-energy matrices are deterministic graph values that read only `S`, `S^±`, `Θ` and the lower
orders. -/
private theorem sigConsistent (Sig : ℕ → Expansion 2) (n : ℕ)
    (hsh : SelfEnergyShapesUpTo Sig (n - 1)) (S : Matrix ι ι ℝ) (z : ℂ) (ω : Sample ι) :
    SigConsistent Sig n (modelDataSig Sig S z ω) := by
  intro k h4 hlt hev
  change sigMat Sig S z k = _
  ext x y
  simp only [sigMat, Matrix.of_apply, Expansion.val]
  congr 1
  refine List.map_congr_left fun g hg => ?_
  have hall := (hsh k h4 (by omega) hev g hg).2.1
  have hSp : (detData S z (sigUpTo Sig S z k)).Sp = (modelDataSig Sig S z ω).Sp := by
    change Splus (msc z) S = (msc z ^ 2 • S.map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • S.map fun r => (r : ℂ))⁻¹
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hSm : (detData S z (sigUpTo Sig S z k)).Sm = (modelDataSig Sig S z ω).Sm := by
    change Sminus (msc z) S = ((msc z ^ 2 • S.map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • S.map fun r => (r : ℂ))⁻¹).map star
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hch : ∀ o, labelOK (k - 1) o = true →
      (detData S z (sigUpTo Sig S z k)).chain o = (modelDataSig Sig S z ω).chain o := by
    intro o ho
    refine chain_congr _ _ ?_ o fun l hl => ?_
    · exact (theta_eq S z hmat ω).symm
    · have hl' : l ≤ k - 1 := by
        have := List.all_eq_true.1 ho l hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.2
      change sigUpTo Sig S z k l = sigMat Sig S z l
      exact sigUpTo_eq Sig S z k l (by omega)
  exact graphVal_det (k - 1) g.2 hall (detData S z (sigUpTo Sig S z k))
    (modelDataSig Sig S z ω) rfl rfl hSp hSm hch _

/-- The resolvent of the data record of the model. -/
private theorem gm_empty (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) (ω : Sample ι) :
    (modelDataSig Sig S z ω).Gm ∅ = green (hmat ω) z := by
  have h : ¬ ∃ x : ι, (∅ : Finset ι) = {x} := by
    rintro ⟨x, hx⟩
    exact Finset.singleton_ne_empty x hx.symm
  simp only [modelDataSig, modelData, dite_eq_right h]

/-- The value of the graph `T_{a,bb}` on the data record of the model is
`T_{ab} = |m|² Σ_x s_{ax} |G_{xb}|²` ([I, (1.21)]). -/
private theorem tGraph_val (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) (a b : ι)
    (ω : Sample ι) :
    tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![a, b, b] ω =
      ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (S a x : ℂ) * ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) := by
  have hG := gm_empty Sig S z ω
  simp only [Graph.valR, Graph.termR, tGraph, Graph.labels, mkC, List.filterMap_cons,
    List.filterMap_nil, List.dedup_nil, List.map_nil, List.prod_nil, mul_one,
    List.filter_cons, Option.isNone_none, ite_true, List.filter_nil, List.map_cons,
    List.prod_cons]
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  simp only [Comp.val, List.map_nil, List.toFinset_nil, hG, Coeff.eval]
  simp only [map_mul, MvPolynomial.eval_X, Equiv.funUnique_symm_apply, Fin.isValue, Sum.elim_inl,
    Matrix.cons_val_zero, Sum.elim_inr, uniqueElim_const, Matrix.cons_val_one, Matrix.cons_val,
    CVar.eval, Charge.apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  change msc z * (starRingEnd ℂ) (msc z) * ((S a x : ℂ) *
    (green (hmat ω) z x b * (starRingEnd ℂ) (green (hmat ω) z x b))) = _
  rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The identity at an invertible `S`: the root `Θ` of the rooted `T`-equation is removed, since
`Θ = A (1 − A)⁻¹` with `A = |m|² S` invertible and `T_{·b} = A |G_{·b}|²`. -/
private theorem identity_of_det_ne (Sig : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec)
    (hQ : 𝒬.IsTEqStruct Sig n D) (hno : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2)
    (S : Matrix ι ι ℝ) (z : ℂ) (hS : S.IsSymm) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) (hdet : S.det ≠ 0) (a b : ι)
    (ω : Sample ι) :
    ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) -
        tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![a, b, b] ω =
      yRoot 𝒬 ⟨Pexp S⟩ (modelDataSig Sig S z) a b ω +
        ∑ y, sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) a y *
          tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![y, b, b] ω := by
  set w : ι → ℂ := fun x => yRoot 𝒬 ⟨Pexp S⟩ (modelDataSig Sig S z) x b ω +
    ∑ y, sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) x y *
      tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![y, b, b] ω with hw
  set g : ι → ℂ := fun x => ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) with hg
  set c : ℂ := ((‖msc z‖ ^ 2 : ℝ) : ℂ) with hc
  set A : Matrix ι ι ℂ := c • S.map fun r => (r : ℂ) with hA
  have hroot := fun x => rootedTEq Sig n D 𝒬 hQ hno (Sample ι) ι ⟨Pexp S⟩ (modelDataSig Sig S z)
    (modelAdm_sig Sig S z hS hnn hrow hz) (sigConsistent Sig n hQ.2.2.1 S z) x b ω
  have htv : ∀ x, tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![x, b, b] ω = (A *ᵥ g) x := by
    intro x
    rw [tGraph_val]
    simp only [hA, hg, hc, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul]
  have hΘ : (modelDataSig Sig S z ω).Theta = A * (1 - A)⁻¹ := rfl
  have hm0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 (msc_ne_zero z))
  have hAu : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hA, Matrix.det_smul]
    have e : (S.map fun r => (r : ℂ)).det = Complex.ofRealHom S.det :=
      (RingHom.map_det Complex.ofRealHom S).symm
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hm0) (by simpa using hdet)
  have hU : IsUnit (1 - A) :=
    isUnit_one_sub_smul_map S hnn hrow c (by
      rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h1 := norm_msc_lt_one hz
      nlinarith [norm_nonneg (msc z)])
  have hUd : IsUnit (1 - A).det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hvec : A *ᵥ g = A *ᵥ ((1 - A)⁻¹ *ᵥ w) := by
    funext x
    rw [← htv x, hroot x, Matrix.mulVec_mulVec, ← hΘ]
    rfl
  have hg' : g = (1 - A)⁻¹ *ᵥ w := Matrix.mulVec_injective_iff_isUnit.2 hAu hvec
  have hw' : w = (1 - A) *ᵥ g := by
    rw [hg', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mulVec]
  have h := congrFun hw' a
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← htv a] at h
  exact h.symm

/-! ## Limits of data records -/

/-- A family of data records along a filter whose `m`, minors of `G` and remaining auxiliary
fields are constant and whose `S`, `S^±`, `Θ` and self-energy matrices converge. -/
private structure DLim (l : Filter ℝ) (D : ℝ → Data ι) (D0 : Data ι) : Prop where
  m : ∀ ε, (D ε).m = D0.m
  Gm : ∀ ε, (D ε).Gm = D0.Gm
  S : Tendsto (fun ε => (D ε).S) l (𝓝 D0.S)
  Sp : Tendsto (fun ε => (D ε).Sp) l (𝓝 D0.Sp)
  Sm : Tendsto (fun ε => (D ε).Sm) l (𝓝 D0.Sm)
  Theta : Tendsto (fun ε => (D ε).Theta) l (𝓝 D0.Theta)
  Sig : ∀ j, Tendsto (fun ε => (D ε).Sig j) l (𝓝 (D0.Sig j))
  ThetaErr : ∀ ε, (D ε).ThetaErr = D0.ThetaErr
  ghost : ∀ ε, (D ε).ghost = D0.ghost
  aux : ∀ ε, (D ε).aux = D0.aux

/-- Convergence of matrices gives convergence of the entries. -/
private theorem tendsto_entry {𝕜 : Type*} [TopologicalSpace 𝕜] {l : Filter ℝ}
    {f : ℝ → Matrix ι ι 𝕜} {M : Matrix ι ι 𝕜} (h : Tendsto f l (𝓝 M)) (a b : ι) :
    Tendsto (fun ε => f ε a b) l (𝓝 (M a b)) :=
  tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h a) b

/-- The chains `Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ` converge. -/
private theorem DLim.chain {l : Filter ℝ} {D : ℝ → Data ι} {D0 : Data ι} (h : DLim l D D0)
    (o : List ℕ) : Tendsto (fun ε => (D ε).chain o) l (𝓝 (D0.chain o)) := by
  unfold Data.chain
  have key : ∀ (o : List ℕ) (M : ℝ → Matrix ι ι ℂ) (M0 : Matrix ι ι ℂ), Tendsto M l (𝓝 M0) →
      Tendsto (fun ε => o.foldl (fun A j => A * (D ε).Sig j * (D ε).Theta) (M ε)) l
        (𝓝 (o.foldl (fun A j => A * D0.Sig j * D0.Theta) M0)) := by
    intro o
    induction o with
    | nil => intro M M0 hM; simpa using hM
    | cons j o ih =>
      intro M M0 hM
      simp only [List.foldl_cons]
      exact ih _ _ ((hM.mul (h.Sig j)).mul h.Theta)
  exact key o _ _ h.Theta

/-- The factor of every component converges. -/
private theorem DLim.compVal {l : Filter ℝ} {D : ℝ → Data ι} {D0 : Data ι} (h : DLim l D D0)
    {V : Type*} (σ : V → ι) (c : Comp V) :
    Tendsto (fun ε => Comp.val (D ε) σ c) l (𝓝 (Comp.val D0 σ c)) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ with
  | waved w =>
    cases w
    · exact tendsto_entry h.S (σ x) (σ y)
    · exact tendsto_entry h.Sp (σ x) (σ y)
    · exact tendsto_entry h.Sm (σ x) (σ y)
  | theta o => exact tendsto_entry (h.chain o) (σ x) (σ y)
  | _ =>
    simp only [Comp.val, h.m, h.Gm, h.ThetaErr, h.ghost, h.aux]
    exact tendsto_const_nhds

/-- The value of every graph without labels converges. -/
private theorem DLim.graphVal {l : Filter ℝ} {D : ℝ → Data ι} {D0 : Data ι} (h : DLim l D D0)
    {k n : ℕ} (Γ : Graph k n) (e : Fin k → ι) :
    Tendsto (fun ε => Γ.val (D ε) e) l (𝓝 (Γ.val D0 e)) := by
  unfold Graph.val Graph.term
  refine tendsto_finsetSum _ fun s _ => ?_
  simp only [h.m]
  exact tendsto_const_nhds.mul (tendsto_list_prod _ fun c _ => h.compVal _ c)

/-- The value of every formal sum without labels converges. -/
private theorem DLim.expVal {l : Filter ℝ} {D : ℝ → Data ι} {D0 : Data ι} (h : DLim l D D0)
    {k : ℕ} (E : Expansion k) (e : Fin k → ι) :
    Tendsto (fun ε => E.val (D ε) e) l (𝓝 (E.val D0 e)) := by
  unfold Expansion.val
  exact tendsto_list_sum _ fun g _ => h.graphVal g.2 e

/-- The inverse of a matrix is continuous at an invertible matrix. -/
private theorem tendsto_inv {𝕜 : Type*} [NormedField 𝕜] {l : Filter ℝ} {f : ℝ → Matrix ι ι 𝕜}
    {M : Matrix ι ι 𝕜} (h : Tendsto f l (𝓝 M)) (hM : IsUnit M) :
    Tendsto (fun ε => (f ε)⁻¹) l (𝓝 M⁻¹) := by
  have hd : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).1 hM).ne_zero
  have hc := continuousAt_matrix_inv M (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)
  exact hc.tendsto.comp h

/-- The ring inverse of a matrix is continuous at an invertible matrix. -/
private theorem tendsto_ringInverse {𝕜 : Type*} [NormedField 𝕜] {l : Filter ℝ}
    {f : ℝ → Matrix ι ι 𝕜} {M : Matrix ι ι 𝕜} (h : Tendsto f l (𝓝 M)) (hM : IsUnit M) :
    Tendsto (fun ε => Ring.inverse (f ε)) l (𝓝 (Ring.inverse M)) := by
  simp only [← Matrix.nonsing_inv_eq_ringInverse]
  exact tendsto_inv h hM

/-- `S ↦ S.map ofReal` is continuous. -/
private theorem tendsto_map_ofReal {l : Filter ℝ} {T : ℝ → Matrix ι ι ℝ} {S : Matrix ι ι ℝ}
    (hT : Tendsto T l (𝓝 S)) :
    Tendsto (fun ε => (T ε).map fun r => (r : ℂ)) l (𝓝 (S.map fun r => (r : ℂ))) :=
  ((continuous_id.matrix_map Complex.continuous_ofReal).tendsto S).comp hT

/-- `M ↦ M.map star` is continuous. -/
private theorem tendsto_map_star {l : Filter ℝ} {f : ℝ → Matrix ι ι ℂ} {M : Matrix ι ι ℂ}
    (h : Tendsto f l (𝓝 M)) : Tendsto (fun ε => (f ε).map star) l (𝓝 (M.map star)) :=
  ((continuous_id.matrix_map continuous_star).tendsto M).comp h

section Det

variable {l : Filter ℝ} {T : ℝ → Matrix ι ι ℝ} {S : Matrix ι ι ℝ} {z : ℂ}

/-- `S^+(T) → S^+(S)`. -/
private theorem tendsto_Splus (hT : Tendsto T l (𝓝 S)) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) :
    Tendsto (fun ε => Splus (msc z) (T ε)) l (𝓝 (Splus (msc z) S)) := by
  have hm : ‖msc z ^ 2‖ < 1 := by
    rw [norm_pow]
    have := norm_msc_lt_one hz
    nlinarith [norm_nonneg (msc z)]
  have hM := tendsto_map_ofReal hT
  unfold Splus cmat
  exact (tendsto_const_nhds.smul hM).mul (tendsto_ringInverse
    (tendsto_const_nhds.sub (tendsto_const_nhds.smul hM))
    (isUnit_one_sub_smul_map S hnn hrow _ hm))

/-- `Θ(T) → Θ(S)` (real matrices). -/
private theorem tendsto_Theta (hT : Tendsto T l (𝓝 S)) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) :
    Tendsto (fun ε => Theta (msc z) (T ε)) l (𝓝 (Theta (msc z) S)) := by
  have hm : ‖‖msc z‖ ^ 2‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    have := norm_msc_lt_one hz
    nlinarith [norm_nonneg (msc z)]
  unfold Theta
  exact (tendsto_const_nhds.smul hT).mul (tendsto_ringInverse
    (tendsto_const_nhds.sub (tendsto_const_nhds.smul hT))
    (isUnit_one_sub_smul_real S hnn hrow _ hm))

/-- The deterministic records `detData` converge with their self-energy matrices. -/
private theorem dlim_detData (hT : Tendsto T l (𝓝 S)) (hnn : ∀ x y, 0 ≤ S x y)
    (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) {Se : ℝ → ℕ → Matrix ι ι ℂ}
    {S0 : ℕ → Matrix ι ι ℂ} (hSe : ∀ j, Tendsto (fun ε => Se ε j) l (𝓝 (S0 j))) :
    DLim l (fun ε => detData (T ε) z (Se ε)) (detData S z S0) where
  m _ := rfl
  Gm _ := rfl
  S := tendsto_map_ofReal hT
  Sp := tendsto_Splus hT hnn hrow hz
  Sm := tendsto_map_star (tendsto_Splus hT hnn hrow hz)
  Theta := tendsto_map_ofReal (tendsto_Theta hT hnn hrow hz)
  Sig := hSe
  ThetaErr _ := rfl
  ghost _ := rfl
  aux _ := rfl

/-- The self-energy matrices below order `N` converge. -/
private theorem tendsto_sigUpTo (Sig : ℕ → Expansion 2) (hT : Tendsto T l (𝓝 S))
    (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) :
    ∀ N j, Tendsto (fun ε => sigUpTo Sig (T ε) z N j) l (𝓝 (sigUpTo Sig S z N j)) := by
  intro N
  induction N with
  | zero => intro j; exact tendsto_const_nhds
  | succ N ih =>
    intro j
    simp only [sigUpTo]
    by_cases hj : j = N
    · subst hj
      simp only [Function.update_self]
      refine tendsto_pi_nhds.2 fun x => tendsto_pi_nhds.2 fun y => ?_
      exact (dlim_detData hT hnn hrow hz ih).expVal (Sig j) ![x, y]
    · simp only [Function.update_of_ne hj]
      exact ih j

/-- The self-energy matrices `Σ_l` converge. -/
private theorem tendsto_sigMat (Sig : ℕ → Expansion 2) (hT : Tendsto T l (𝓝 S))
    (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) (j : ℕ) :
    Tendsto (fun ε => sigMat Sig (T ε) z j) l (𝓝 (sigMat Sig S z j)) := by
  simp only [← sigUpTo_eq Sig _ z (j + 1) j (Nat.lt_succ_self j)]
  exact tendsto_sigUpTo Sig hT hnn hrow hz (j + 1) j

/-- The records of the model converge at every sample, with constant `m` and `G`. -/
private theorem dlim_model (Sig : ℕ → Expansion 2) (hT : Tendsto T l (𝓝 S))
    (hnn : ∀ x y, 0 ≤ S x y) (hrow : ∀ x, ∑ y, S x y = 1) (hz : 0 < z.im) (ω : Sample ι) :
    DLim l (fun ε => modelDataSig Sig (T ε) z ω) (modelDataSig Sig S z ω) := by
  have hM := tendsto_map_ofReal hT
  have hm : ‖msc z ^ 2‖ < 1 := by
    rw [norm_pow]
    have := norm_msc_lt_one hz
    nlinarith [norm_nonneg (msc z)]
  have hm' : ‖((‖msc z‖ ^ 2 : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have := norm_msc_lt_one hz
    nlinarith [norm_nonneg (msc z)]
  have hSp : Tendsto (fun ε => (msc z ^ 2 • (T ε).map fun r => (r : ℂ)) *
      (1 - msc z ^ 2 • (T ε).map fun r => (r : ℂ))⁻¹) l
      (𝓝 ((msc z ^ 2 • S.map fun r => (r : ℂ)) * (1 - msc z ^ 2 • S.map fun r => (r : ℂ))⁻¹)) :=
    (tendsto_const_nhds.smul hM).mul (tendsto_inv
      (tendsto_const_nhds.sub (tendsto_const_nhds.smul hM))
      (isUnit_one_sub_smul_map S hnn hrow _ hm))
  exact {
    m := fun _ => rfl
    Gm := fun _ => rfl
    S := hM
    Sp := hSp
    Sm := tendsto_map_star hSp
    Theta := (tendsto_const_nhds.smul hM).mul (tendsto_inv
      (tendsto_const_nhds.sub (tendsto_const_nhds.smul hM))
      (isUnit_one_sub_smul_map S hnn hrow _ hm'))
    Sig := fun j => tendsto_sigMat Sig hT hnn hrow hz j
    ThetaErr := fun _ => rfl
    ghost := fun _ => rfl
    aux := fun _ => rfl }

end Det

/-! ## Continuous functions of polynomial growth -/

/-- Continuous functions of polynomial growth on the sample space. -/
private def Nice (F : Sample ι → ℂ) : Prop := Continuous F ∧ PolyMeas F

/-- The laws of the partial expectations at `S = 1`; only their closure properties of the class of
functions of polynomial growth are used. -/
private theorem laws1 :
    PQLaws (PolyMeas (ι := ι)) (fun F => ∫ ω, F ω ∂(gaussLaw (1 : Matrix ι ι ℝ)))
      (Pexp (1 : Matrix ι ι ℝ)) (fun x => FreeOf (rowCoords x)) :=
  pqLaws_Pexp_poly 1 Matrix.isSymm_one fun x y => by
    by_cases h : x = y <;> simp [Matrix.one_apply, h]

private theorem nice_const (c : ℂ) : Nice fun _ : Sample ι => c :=
  ⟨continuous_const, laws1.adm_const c⟩

private theorem nice_add {f g : Sample ι → ℂ} (hf : Nice f) (hg : Nice g) :
    Nice fun ω => f ω + g ω := by
  classical
  exact ⟨hf.1.add hg.1, laws1.adm_add _ _ hf.2 hg.2⟩

private theorem nice_mul {f g : Sample ι → ℂ} (hf : Nice f) (hg : Nice g) :
    Nice fun ω => f ω * g ω := by
  classical
  exact ⟨hf.1.mul hg.1, laws1.adm_mul _ _ hf.2 hg.2⟩

private theorem nice_star {f : Sample ι → ℂ} (hf : Nice f) : Nice fun ω => star (f ω) := by
  classical
  exact ⟨continuous_star.comp hf.1, laws1.adm_conj _ hf.2⟩

private theorem nice_sub {f g : Sample ι → ℂ} (hf : Nice f) (hg : Nice g) :
    Nice fun ω => f ω - g ω := by
  have h := nice_add hf (nice_mul (nice_const (-1)) hg)
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

private theorem nice_pow {f : Sample ι → ℂ} (hf : Nice f) (j : ℕ) : Nice fun ω => f ω ^ j := by
  induction j with
  | zero => simpa using nice_const (1 : ℂ)
  | succ j ih => simpa [pow_succ] using nice_mul ih hf

private theorem nice_sum {κ : Type*} (s : Finset κ) {f : κ → Sample ι → ℂ}
    (hf : ∀ j ∈ s, Nice (f j)) : Nice fun ω => ∑ j ∈ s, f j ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nice_const (0 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact nice_add (hf a (Finset.mem_insert_self a s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The resolvent entries are continuous, of polynomial growth. -/
private theorem nice_green {z : ℂ} (hz : 0 < z.im) (a b : ι) :
    Nice fun ω : Sample ι => green (hmat ω) z a b :=
  ⟨((testFn_green z hz.ne' a b) 0).1.continuous, polyMeas_of_testFn _ (testFn_green z hz.ne' a b)⟩

/-- `(G_{aa})⁻¹` is continuous, of polynomial growth. -/
private theorem nice_inv_green {z : ℂ} (hz : 0 < z.im) (a : ι) :
    Nice fun ω : Sample ι => (green (hmat ω) z a a)⁻¹ :=
  ⟨(nice_green hz a a).1.inv₀ fun ω => green_diag_ne_zero (hmat_isHermitian ω) hz a,
    polyMeas_inv_green_diag z hz a⟩

private theorem nice_charge {f : Sample ι → ℂ} (hf : Nice f) (ch : Charge) :
    Nice fun ω => ch.apply (f ω) := by
  cases ch
  · exact hf
  · exact nice_star hf

/-- A component without minor on the record of the model is either a continuous function of
polynomial growth of the sample alone (`G`, weights, `(G_{xx})⁻¹`, `W_D`), or does not depend on
the sample (the deterministic kinds). -/
private theorem comp_split (Sig : ℕ → Expansion 2) {z : ℂ} (hz : 0 < z.im) {V : Type*}
    (σ : V → ι) (c : Comp V) (hc : c.minor = []) :
    (∃ F : Sample ι → ℂ, Nice F ∧
      ∀ (T : Matrix ι ι ℝ) ω, Comp.val (modelDataSig Sig T z ω) σ c = F ω) ∨
    (∀ (T : Matrix ι ι ℝ) ω ω',
      Comp.val (modelDataSig Sig T z ω) σ c = Comp.val (modelDataSig Sig T z ω') σ c) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at hc
  subst hc
  have hG : ∀ (T : Matrix ι ι ℝ) ω,
      (modelDataSig Sig T z ω).Gm (([] : List V).map σ).toFinset = green (hmat ω) z := by
    intro T ω
    simpa using gm_empty Sig T z ω
  cases κ with
  | G ch =>
    exact Or.inl ⟨_, nice_charge (nice_green hz (σ x) (σ y)) ch, fun T ω => by
      simp only [Comp.val, hG]⟩
  | weight ch =>
    exact Or.inl ⟨_, nice_charge (nice_green hz (σ x) (σ x)) ch, fun T ω => by
      simp only [Comp.val, hG]⟩
  | light ch =>
    exact Or.inl ⟨_, nice_charge (nice_sub (nice_green hz (σ x) (σ x)) (nice_const (msc z))) ch,
      fun T ω => by simp only [Comp.val, hG]; rfl⟩
  | inv ch =>
    exact Or.inl ⟨_, nice_charge (nice_inv_green hz (σ x)) ch, fun T ω => by
      simp only [Comp.val, hG]⟩
  | wD ch d =>
    refine Or.inl ⟨_, nice_charge (nice_sub (nice_inv_green hz (σ x)) (nice_mul
      (nice_const (msc z)⁻¹) (nice_sum (Finset.range (d + 1)) fun j _ => nice_pow (nice_mul
        (nice_const (-(msc z)⁻¹)) (nice_sub (nice_green hz (σ x) (σ x)) (nice_const (msc z))))
        j))) ch, fun T ω => ?_⟩
    simp only [Comp.val, hG]
    congr 3
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change -(green (hmat ω) z (σ x) (σ x) - msc z) / msc z = _
    ring
  | waved w => exact Or.inr fun T ω ω' => by cases w <;> rfl
  | theta o => exact Or.inr fun T ω ω' => rfl
  | thetaErr n D => exact Or.inr fun T ω ω' => rfl
  | ghost => exact Or.inr fun T ω ω' => rfl
  | aux j r b => exact Or.inr fun T ω ω' => rfl
  | dot => exact Or.inr fun T ω ω' => rfl
  | xdot => exact Or.inr fun T ω ω' => rfl

/-- The product of the factors of components without minor, along a family `T(ε)` of variance
matrices: `κ(ε) F(ω)`, with `F` continuous of polynomial growth and `κ(ε)` convergent. -/
private theorem prod_split (Sig : ℕ → Expansion 2) {z : ℂ} (hz : 0 < z.im) {l : Filter ℝ}
    {T : ℝ → Matrix ι ι ℝ} {S : Matrix ι ι ℝ}
    (hD : ∀ ω, DLim l (fun ε => modelDataSig Sig (T ε) z ω) (modelDataSig Sig S z ω))
    {V : Type*} (σ : V → ι) (L : List (Comp V)) (hL : ∀ c ∈ L, c.minor = []) :
    ∃ (F : Sample ι → ℂ) (κ : ℝ → ℂ) (κ0 : ℂ), Nice F ∧ Tendsto κ l (𝓝 κ0) ∧
      (∀ ε ω, (L.map (Comp.val (modelDataSig Sig (T ε) z ω) σ)).prod = κ ε * F ω) ∧
      (∀ ω, (L.map (Comp.val (modelDataSig Sig S z ω) σ)).prod = κ0 * F ω) := by
  induction L with
  | nil => exact ⟨fun _ => 1, fun _ => 1, 1, nice_const 1, tendsto_const_nhds,
      fun _ _ => by simp, fun _ => by simp⟩
  | cons c L ih =>
    obtain ⟨F, κ, κ0, hF, hκ, h1, h2⟩ := ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')
    rcases comp_split Sig hz σ c (hL c List.mem_cons_self) with ⟨Fc, hFc, hc⟩ | hc
    · refine ⟨fun ω => Fc ω * F ω, κ, κ0, nice_mul hFc hF, hκ, fun ε ω => ?_, fun ω => ?_⟩
      · rw [List.map_cons, List.prod_cons, h1, hc]; ring
      · rw [List.map_cons, List.prod_cons, h2, hc]; ring
    · refine ⟨F, fun ε => Comp.val (modelDataSig Sig (T ε) z 0) σ c * κ ε,
        Comp.val (modelDataSig Sig S z 0) σ c * κ0, hF, ((hD 0).compVal σ c).mul hκ,
        fun ε ω => ?_, fun ω => ?_⟩
      · rw [List.map_cons, List.prod_cons, h1, hc (T ε) ω 0]; ring
      · rw [List.map_cons, List.prod_cons, h2, hc S ω 0]; ring

/-! ## Convergence of the partial expectations -/

/-- `N(0, v) = √v N(0, 1)`, coordinatewise. -/
private theorem pi_gauss_eq_map (v : Coord ι → ℝ≥0) :
    Measure.pi (fun c => gaussianReal 0 (v c)) =
      (Measure.pi fun _ : Coord ι => gaussianReal 0 1).map
        (fun ζ c => (NNReal.sqrt (v c) : ℝ) * ζ c) := by
  have key : ∀ c, (gaussianReal 0 1).map (fun x => (NNReal.sqrt (v c) : ℝ) * x) =
      gaussianReal 0 (v c) := by
    intro c
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  have : ∀ c, SigmaFinite ((gaussianReal 0 1).map (fun x => (NNReal.sqrt (v c) : ℝ) * x)) :=
    fun c => by rw [key c]; infer_instance
  rw [Measure.pi_map_pi (f := fun c x => (NNReal.sqrt (v c) : ℝ) * x)
    (fun c => (measurable_const_mul _).aemeasurable)]
  simp only [key]

/-- The matrix with diagonal `1` and off-diagonal entries `2`: every coordinate variance is `1`. -/
private def S1 : Matrix ι ι ℝ := Matrix.of fun x y => if x = y then 1 else 2

private theorem gaussLaw_S1 :
    gaussLaw (S1 : Matrix ι ι ℝ) = Measure.pi fun _ : Coord ι => gaussianReal 0 1 := by
  unfold gaussLaw
  congr 1
  funext c
  rcases c with x | ⟨e, b⟩
  · simp [coordVar, S1]
  · have hne : e.1.1 ≠ e.1.2 := fun h => by
      have := e.2
      rw [h] at this
      exact lt_irrefl _ this
    simp [coordVar, S1, hne]

/-- `(1 + ‖ζ‖)^k` is integrable for the standard Gaussian law on the sample space. -/
private theorem integrable_one_add_norm_pow (k : ℕ) :
    Integrable (fun ζ : Sample ι => (1 + ‖ζ‖) ^ k)
      (Measure.pi fun _ : Coord ι => gaussianReal 0 1) := by
  classical
  have hP : PolyMeas fun ζ : Sample ι => (((1 + ‖ζ‖) ^ k : ℝ) : ℂ) :=
    ⟨by fun_prop, 1, k, fun ζ => by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), one_mul]⟩
  have h := (integrable_of_polyMeas S1 _ hP).norm
  rw [gaussLaw_S1] at h
  refine h.congr (Eventually.of_forall fun ζ => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖ζ‖) ^ k)]

/-- `η ↦ A.piecewise η ω` is continuous. -/
private theorem continuous_piecewise_left (A : Finset (Coord ι)) (ω : Sample ι) :
    Continuous fun η : Sample ι => A.piecewise η ω := by
  refine continuous_pi fun c => ?_
  by_cases h : c ∈ A
  · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
    exact continuous_apply c
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
    exact continuous_const

/-- The scaling `ζ ↦ (√v_c ζ_c)_c` is continuous. -/
private theorem continuous_scale (v : Coord ι → ℝ≥0) :
    Continuous fun ζ : Sample ι => fun c => (NNReal.sqrt (v c) : ℝ) * ζ c :=
  continuous_pi fun c => continuous_const.mul (continuous_apply c)

/-- `1 + ‖A.piecewise η ω‖ ≤ (1 + ‖ω‖)(1 + ‖η‖)`. -/
private theorem one_add_norm_piecewise_le (A : Finset (Coord ι)) (η ω : Sample ι) :
    1 + ‖A.piecewise η ω‖ ≤ (1 + ‖ω‖) * (1 + ‖η‖) := by
  have h : ‖A.piecewise η ω‖ ≤ ‖ω‖ + ‖η‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c => ?_
    by_cases hc : c ∈ A
    · rw [Finset.piecewise_eq_of_mem _ _ _ hc]
      linarith [norm_le_pi_norm η c, norm_nonneg ω]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hc]
      linarith [norm_le_pi_norm ω c, norm_nonneg η]
  nlinarith [norm_nonneg ω, norm_nonneg η]

/-- The scaling by `√v_c ≤ 1` does not increase the norm. -/
private theorem norm_scale_le (v : Coord ι → ℝ≥0) (hv : ∀ c, v c ≤ 1) (ζ : Sample ι) :
    ‖fun c => (NNReal.sqrt (v c) : ℝ) * ζ c‖ ≤ ‖ζ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
  rw [norm_mul, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  have h1 : (NNReal.sqrt (v c) : ℝ) ≤ 1 := by exact_mod_cast NNReal.sqrt_le_one.2 (hv c)
  calc (NNReal.sqrt (v c) : ℝ) * ‖ζ c‖ ≤ 1 * ‖ζ c‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖ζ c‖ := one_mul _
    _ ≤ ‖ζ‖ := norm_le_pi_norm ζ c

/-- The partial expectations converge when the coordinate variances converge and stay `≤ 1`, on
continuous functions of polynomial growth: after the scaling `N(0, v) = √v N(0, 1)` this is
dominated convergence for the standard Gaussian law. -/
private theorem tendsto_partialExp {l : Filter ℝ} [l.IsCountablyGenerated]
    {T : ℝ → Matrix ι ι ℝ} {S : Matrix ι ι ℝ}
    (hv : ∀ c, Tendsto (fun ε => coordVar (T ε) c) l (𝓝 (coordVar S c)))
    (hv1 : ∀ᶠ ε in l, ∀ c, coordVar (T ε) c ≤ 1) {F : Sample ι → ℂ} (hF : Nice F)
    (A : Finset (Coord ι)) (ω : Sample ι) :
    Tendsto (fun ε => partialExp (T ε) A F ω) l (𝓝 (partialExp S A F ω)) := by
  set μ := Measure.pi fun _ : Coord ι => gaussianReal 0 1
  have hrepr : ∀ V : Matrix ι ι ℝ, partialExp V A F ω =
      ∫ ζ, F (A.piecewise (fun c => (NNReal.sqrt (coordVar V c) : ℝ) * ζ c) ω) ∂μ := by
    intro V
    unfold partialExp gaussLaw
    rw [pi_gauss_eq_map]
    refine integral_map (f := fun η => F (A.piecewise η ω))
      (continuous_scale _).measurable.aemeasurable ?_
    exact (hF.1.comp (continuous_piecewise_left A ω)).aestronglyMeasurable
  simp only [hrepr]
  obtain ⟨-, C, k, hC⟩ := hF.2
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    rw [norm_zero, add_zero, one_pow, mul_one] at h0
    exact (norm_nonneg _).trans h0
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ζ => C * (1 + ‖ω‖) ^ k * (1 + ‖ζ‖) ^ k) (Eventually.of_forall fun ε =>
      (hF.1.comp ((continuous_piecewise_left A ω).comp
        (continuous_scale _))).aestronglyMeasurable) ?_
    ((integrable_one_add_norm_pow k).const_mul _) (Eventually.of_forall fun ζ => ?_)
  · filter_upwards [hv1] with ε hε
    refine Eventually.of_forall fun ζ => ?_
    refine (hC _).trans ?_
    calc C * (1 + ‖A.piecewise (fun c => (NNReal.sqrt (coordVar (T ε) c) : ℝ) * ζ c) ω‖) ^ k
        ≤ C * ((1 + ‖ω‖) * (1 + ‖ζ‖)) ^ k := by
          gcongr
          refine (one_add_norm_piecewise_le A _ ω).trans ?_
          gcongr
          exact norm_scale_le _ hε ζ
      _ = C * (1 + ‖ω‖) ^ k * (1 + ‖ζ‖) ^ k := by rw [mul_pow, mul_assoc]
  · refine (hF.1.tendsto _).comp ?_
    refine tendsto_pi_nhds.2 fun c => ?_
    by_cases h : c ∈ A
    · simp only [Finset.piecewise_eq_of_mem _ _ _ h]
      exact ((NNReal.continuous_coe.comp NNReal.continuous_sqrt).tendsto _ |>.comp
        (hv c)).mul_const _
    · simp only [Finset.piecewise_eq_of_notMem _ _ _ h]
      exact tendsto_const_nhds

/-- The coordinate variances are continuous in the variance matrix. -/
private theorem tendsto_coordVar {l : Filter ℝ} {T : ℝ → Matrix ι ι ℝ} {S : Matrix ι ι ℝ}
    (hT : Tendsto T l (𝓝 S)) (c : Coord ι) :
    Tendsto (fun ε => coordVar (T ε) c) l (𝓝 (coordVar S c)) := by
  rcases c with x | ⟨e, b⟩
  · exact (continuous_real_toNNReal.tendsto _).comp (tendsto_entry hT x x)
  · exact (continuous_real_toNNReal.tendsto _).comp ((tendsto_entry hT e.1.1 e.1.2).div_const 2)

/-- For `S ≥ 0` with row sums `1`, every coordinate variance is `≤ 1`. -/
private theorem coordVar_le_one {V : Matrix ι ι ℝ} (hnn : ∀ x y, 0 ≤ V x y)
    (hrow : ∀ x, ∑ y, V x y = 1) (c : Coord ι) : coordVar V c ≤ 1 := by
  have hle : ∀ x y, V x y ≤ 1 := fun x y =>
    (hrow x) ▸ Finset.single_le_sum (fun y _ => hnn x y) (Finset.mem_univ y)
  rcases c with x | ⟨e, b⟩
  · exact Real.toNNReal_le_one.2 (hle x x)
  · exact Real.toNNReal_le_one.2 (by linarith [hle e.1.1 e.1.2])

/-! ## Convergence of the values of labelled graphs -/

section Values

variable (Sig : ℕ → Expansion 2) {z : ℂ} (hz : 0 < z.im) {l : Filter ℝ} [l.IsCountablyGenerated]
  {T : ℝ → Matrix ι ι ℝ} {S : Matrix ι ι ℝ}
  (hD : ∀ ω, DLim l (fun ε => modelDataSig Sig (T ε) z ω) (modelDataSig Sig S z ω))
  (hv : ∀ c, Tendsto (fun ε => coordVar (T ε) c) l (𝓝 (coordVar S c)))
  (hv1 : ∀ᶠ ε in l, ∀ c, coordVar (T ε) c ≤ 1)

include hz hD hv hv1 in
/-- The labelled term of a graph without minors converges: the unlabelled factors converge, and
for every label the product of its factors is `κ(ε) F`, so that `P_x` of it is `κ(ε) P_x F`. -/
private theorem tendsto_termR {k n : ℕ} (Γ : Graph k n) (hΓ : ∀ c ∈ Γ.comps, c.minor = [])
    (σ : Atom k n → ι) (ω : Sample ι) :
    Tendsto (fun ε => Γ.termR ⟨Pexp (T ε)⟩ (modelDataSig Sig (T ε) z) σ ω) l
      (𝓝 (Γ.termR ⟨Pexp S⟩ (modelDataSig Sig S z) σ ω)) := by
  unfold Graph.termR
  simp only [(hD ω).m]
  refine (tendsto_const_nhds.mul (tendsto_list_prod _ fun c _ => (hD ω).compVal σ c)).mul
    (tendsto_list_prod _ fun ℓ _ => ?_)
  obtain ⟨F, κ, κ0, hF, hκ, h1, h2⟩ := prod_split Sig hz hD σ
    (Γ.comps.filter fun c => decide (c.label = some ℓ))
    (fun c hc => hΓ c (List.mem_of_mem_filter hc))
  have e1 : ∀ ε, (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
      (Comp.val (modelDataSig Sig (T ε) z ω') σ)).prod) = fun ω' => κ ε * F ω' :=
    fun ε => funext (h1 ε)
  have e2 : (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
      (Comp.val (modelDataSig Sig S z ω') σ)).prod) = fun ω' => κ0 * F ω' := funext h2
  simp only [e1, e2]
  have hP : ∀ (V : Matrix ι ι ℝ) (a : ℂ) (x : ι),
      Pexp V x (fun ω' => a * F ω') ω = a * partialExp V (rowCoords x) F ω := by
    intro V a x
    simp only [Pexp, partialExp]
    exact integral_const_mul a _
  have hPl : ∀ x : ι, Tendsto (fun ε => Pexp (T ε) x (fun ω' => κ ε * F ω') ω) l
      (𝓝 (Pexp S x (fun ω' => κ0 * F ω') ω)) := by
    intro x
    simp only [hP]
    exact hκ.mul (tendsto_partialExp hv hv1 hF _ ω)
  rcases ℓ with ⟨pq, u⟩
  cases pq
  · exact hPl (σ u)
  · exact (hκ.mul tendsto_const_nhds).sub (hPl (σ u))

include hz hD hv hv1 in
/-- The value of a labelled graph without minors converges. -/
private theorem tendsto_valR {k n : ℕ} (Γ : Graph k n) (hΓ : ∀ c ∈ Γ.comps, c.minor = [])
    (e : Fin k → ι) (ω : Sample ι) :
    Tendsto (fun ε => Γ.valR ⟨Pexp (T ε)⟩ (modelDataSig Sig (T ε) z) e ω) l
      (𝓝 (Γ.valR ⟨Pexp S⟩ (modelDataSig Sig S z) e ω)) :=
  tendsto_finsetSum _ fun _ _ => tendsto_termR Sig hz hD hv hv1 Γ hΓ _ ω

end Values

/-- The graph `Graph.rootGraph` of a graph without minors has no minors. -/
private theorem rootGraph_minor {n : ℕ} (Γ : Graph 3 n) (h : ∀ c ∈ Γ.comps, c.minor = [])
    (v : Atom 3 n) : ∀ c ∈ (Γ.rootGraph v).2.comps, c.minor = [] := by
  rcases v with b | i
  · intro c' hc'
    change c' ∈ Γ.comps ++ [mkC .dot (.inl 0) (.inl b)] at hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · exact h c' hc'
    · rw [List.mem_singleton.1 hc']
      rfl
  · intro c' hc'
    change c' ∈ Γ.comps.map _ at hc'
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.1 hc'
    change c''.minor.map _ = []
    rw [h c'' hc'', List.map_nil]

/-- The rooted graph `𝒢_{x, b₁ b₂}` of a graph without minors has no minors. -/
private theorem rootRest_minor {n : ℕ} (Γ : Graph 3 n) (h : ∀ c ∈ Γ.comps, c.minor = []) :
    ∀ c ∈ (rootRest Γ).2.comps, c.minor = [] := by
  unfold rootRest
  split
  · exact rootGraph_minor _ (fun c' hc' => h c' (List.mem_of_mem_eraseIdx hc')) _
  · exact h

/-- The graphs of `R`, `A`, `Q`, `Err` of a `T`-equation have no minors ([II, Def 3.2]). -/
private theorem minor_nil_of_struct {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec}
    (hQ : 𝒬.IsTEqStruct Sig n D) :
    ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, ∀ c ∈ g.2.comps, c.minor = [] := by
  have hsh := hQ.2.2.2.2.1
  intro g hg c hc
  rcases List.mem_append.1 hg with hg | hg
  · have h1 := List.all_eq_true.1 (hsh.1.1 g hg).2.1 c hc
    simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at h1
    exact h1.1
  · have h1 := List.all_eq_true.1 (hsh.1.2 g hg).2.1 c hc
    simp only [Comp.isTKind, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at h1
    rcases h1 with h1 | h1
    · exact h1.1
    · exact h1.1

end Singular

open Singular in
/-- **The identity of [I, Corollary 1.6] at a singular `S`** (the perturbation argument of its
proof): for a `T`-equation `𝒬` without `P`/`Q` labels at `⊗` and the Gaussian model at every real
symmetric `S ≥ 0` with row sums `1`, `|G_{ab}|² − T_{a,bb} = Y'_{ab} + (Σ̃^{(n)} T)_{a,bb}` at every
sample. -/
theorem singularId : singularIdStmt := by
  intro Sig n D 𝒬 hQ hno ι _ _ S z hS hnn hrow hz a b ω
  have hT : Tendsto (pert S) (𝓝[>] (0 : ℝ)) (𝓝 S) :=
    (tendsto_pert S).mono_left nhdsWithin_le_nhds
  have hD := fun ω => dlim_model Sig hT hnn hrow hz ω
  have hv := fun c => tendsto_coordVar hT c
  have hv1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c, coordVar (pert S ε) c ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact coordVar_le_one (pert_nonneg hnn hε) (pert_rowSum hrow hε)
  have hmin := minor_nil_of_struct hQ
  have htG : ∀ c ∈ tGraph.comps, c.minor = [] := by simp [tGraph, mkC]
  have hL : Tendsto (fun ε => ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) -
      tGraph.valR ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) ![a, b, b] ω) (𝓝[>] 0)
      (𝓝 (((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) -
        tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![a, b, b] ω)) :=
    tendsto_const_nhds.sub (tendsto_valR Sig hz hD hv hv1 tGraph htG _ ω)
  have hY : Tendsto (fun ε => yRoot 𝒬 ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) a b ω)
      (𝓝[>] 0) (𝓝 (yRoot 𝒬 ⟨Pexp S⟩ (modelDataSig Sig S z) a b ω)) := by
    unfold yRoot gammaVal
    simp only [(hD ω).m, (hD ω).Gm]
    exact tendsto_const_nhds.add (tendsto_list_sum _ fun g hg =>
      tendsto_valR Sig hz hD hv hv1 _ (rootRest_minor g.2 (hmin g hg)) _ ω)
  have hsig : ∀ y, Tendsto (fun ε => sigTilde n 𝒬.SigN (modelDataSig Sig (pert S ε) z ω) a y)
      (𝓝[>] 0) (𝓝 (sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) a y)) := by
    intro y
    simp only [sigTilde, Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
    exact ((hD ω).expVal _ _).add (tendsto_finsetSum _ fun j _ => tendsto_entry ((hD ω).Sig j) a y)
  have hR : Tendsto (fun ε => yRoot 𝒬 ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) a b ω +
      ∑ y, sigTilde n 𝒬.SigN (modelDataSig Sig (pert S ε) z ω) a y *
        tGraph.valR ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) ![y, b, b] ω) (𝓝[>] 0)
      (𝓝 (yRoot 𝒬 ⟨Pexp S⟩ (modelDataSig Sig S z) a b ω +
        ∑ y, sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) a y *
          tGraph.valR ⟨Pexp S⟩ (modelDataSig Sig S z) ![y, b, b] ω)) :=
    hY.add (tendsto_finsetSum _ fun y _ =>
      (hsig y).mul (tendsto_valR Sig hz hD hv hv1 tGraph htG _ ω))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) -
      tGraph.valR ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) ![a, b, b] ω =
      yRoot 𝒬 ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) a b ω +
        ∑ y, sigTilde n 𝒬.SigN (modelDataSig Sig (pert S ε) z ω) a y *
          tGraph.valR ⟨Pexp (pert S ε)⟩ (modelDataSig Sig (pert S ε) z) ![y, b, b] ω := by
    filter_upwards [eventually_det_pert_ne S, self_mem_nhdsWithin] with ε hdet hε
    exact identity_of_det_ne Sig n D 𝒬 hQ hno (pert S ε) z (pert_isSymm hS ε) (pert_nonneg hnn hε)
      (pert_rowSum hrow hε) hz hdet a b ω
  exact tendsto_nhds_unique (hL.congr' hev) hR

end RBM8D
