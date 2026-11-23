module

public import RBM8D.AvgBound.Trace
public import RBM8D.Diffusion.ModelSymm
public import RBM8D.Kernel.ThetaDecay
public import RBM8D.Graph.ValueLemmas
public import Batteries.Tactic.OpenPrivate
public import RBM8D.Graph.Local.Model
import all RBM8D.Kernel.ThetaDecay
import all RBM8D.Graph.Local.Model
import all RBM8D.AvgBound.Trace

@[expose] public section

/-!
# The identities of [I, Lemma 5.11] that do not use the local law

On `Z_L^d`, at a variance kernel `S = S_{W,L}` ([I, Assumption 1.1]: symmetric, translation
invariant, nonnegative, row sums `1`) and `Im z > 0`, with the data record `rbmData` of the model,
the graph `T_{ab} = |m|² Σ_x s_{ax} G_{xb} Ḡ_{xb}` of [I, (2.4)] (`tGraph` at `(a, b, b)`) and the
leading term `m Θ_{ab} Ḡ_{bb}` (`leadExp`):

* `MainCancelId.expQ_zero`: `E Q = 0` for `Q`-graphs with the kinds of [II, Def 3.2] ([I, (5.44)]);
  `MainCancelId.tGraph_valR_integrable`: `T`-graphs are integrable;
* `MainCancelId.expG_diag`: `E G_{xx} = E G_{00}`;
* `MainCancelId.ward_row`, `MainCancelId.expT_row`, `MainCancelId.expT_total`: the Ward identity
  [I, (5.16)] gives `Σ_{a,b} T_{ab} = |m|² Σ_α Im G_{αα}/η`, and with `E G_{xx} = E G_{00}` the
  expectations `Σ_b E T_{ab} = |m|² Im(E G_{00})/η` ([I, (5.45)]);
* `MainCancelId.theta_colSum`, `MainCancelId.expLead_total`: the column sums of `Θ` are
  `|m|²/(1 − |m|²)`, and `Σ_{a,b} E(m Θ_{ab} Ḡ_{bb}) = L^d (|m|²/(1 − |m|²)) m conj(E G_{00})`
  ([I, (5.46)]);
* `MainCancelId.msc_ratio`: `|m|²/(1 − |m|²) = Im m/η` ([I, (5.53)]);
* `MainCancelId.sigma_term`: `Σ_{a,x,b} (Θ K)_{ax} E T_{xb}` for a translation invariant `K`
  ([I, (5.49)], first line).

The statements hold at every `(W, L)` where `S_{W,L}` is a variance kernel and every `z` with
`Im z > 0`; none uses the local law.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

open scoped BigOperators Matrix
open MeasureTheory

namespace RBM8D

open Graphs

open private ThetaDecay_ratio from RBM8D.Kernel.ThetaDecay
open private det_one_sub_smul_ne_zero from RBM8D.Graph.Local.Model
open private Trace_val_ghostOne from RBM8D.AvgBound.Trace

namespace MainCancelId

section Basic0
/-- The resolvent entries are integrable. -/
theorem integrable_green {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ)
    (hz : 0 < z.im) (x y : Zd d L) :
    Integrable (fun ω => green (hmat ω) z x y) (gaussLaw S) :=
  integrable_of_polyMeas S _ (polyMeas_of_testFn _ (testFn_green z hz.ne' x y))


/-- The conjugates of the resolvent entries are integrable. -/
theorem integrable_star_green {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ)
    (hz : 0 < z.im) (x y : Zd d L) :
    Integrable (fun ω => star (green (hmat ω) z x y)) (gaussLaw S) :=
  integrable_of_polyMeas S _
    (polyMeas_of_testFn _ (testFn_closed.2.2.2.1 _ (testFn_green z hz.ne' x y)))


/-- The imaginary parts of the resolvent entries are integrable. -/
theorem integrable_im_green {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ)
    (hz : 0 < z.im) (x y : Zd d L) :
    Integrable (fun ω => (green (hmat ω) z x y).im) (gaussLaw S) :=
  (integrable_green S z hz x y).im

/-- The expectation of the imaginary part of a resolvent entry is the imaginary part of its
expectation. -/
theorem integral_im_green {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (z : ℂ)
    (hz : 0 < z.im) (x y : Zd d L) :
    ∫ ω, (green (hmat ω) z x y).im ∂(gaussLaw S) = (∫ ω, green (hmat ω) z x y ∂(gaussLaw S)).im :=
  (integral_im (integrable_green S z hz x y))

/-- The row sums of a translation invariant kernel are equal. -/
theorem sum_transInv {d L : ℕ} [NeZero L] {K : Matrix (Zd d L) (Zd d L) ℂ} (hK : TransInv K)
    (y : Zd d L) :
    ∑ x, K y x = ∑ x, K 0 x := by
  have h : ∀ x, K y x = K 0 (x - y) := fun x => by
    have := hK y x (-y)
    rw [add_neg_cancel, ← sub_eq_add_neg] at this
    exact this.symm
  simp_rw [h]
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x => rfl

end Basic0

section Basic

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ)

/-- The graph `T_{a,b₁b₂} = |m|² Σ_x s_{ax} G_{x b₁} Ḡ_{x b₂}` ([I, (2.4)]) at `b₁ = b₂ = b`,
read on the data record of the model, is the real number `T_{ab} = |m|² Σ_α s_{aα} |G_{αb}|²` of
[I, (1.21)], at every sample. -/
theorem tGraph_valR_eq (a b : Zd d L) (ω : Sample (Zd d L)) :
    tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω =
      ((Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) a b : ℝ) : ℂ) := by
  have hl : tGraph.LabelFree := by
    intro c hc
    simp only [tGraph, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rfl
  rw [Graph.valR_of_labelFree 3 1 tGraph _ _ _ _ _ hl]
  simp [Graph.val, Graph.term, tGraph, Comp.val, Coeff.eval, rbmData, modelData, Tvar, cm, cmb, mkC]
  have h1 : ∀ w : ℂ, w * star w = ((‖w‖ : ℝ) : ℂ) ^ 2 := fun w => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Zd d L)) _
    (fun x => (msc z * star (msc z)) * ((Smat P.ψ W L a x : ℂ) *
      (green (hmat ω) z x b * star (green (hmat ω) z x b)))) (fun s => by
        simp [CVar.eval, Charge.apply])]
  rw [Finset.mul_sum, h1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1]


/-- The column sums of the field `Θ` of the data record of the model are
`Σ_a Θ_{ab} = |m|²/(1 − |m|²) = Im m/η` ([I, (5.46)] with the row sums of `Θ`, [I, (1.16)]), for a
variance kernel `S` ([I, Assumption 1.1]) and `η = Im z > 0`. -/
theorem theta_colSum (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im)
    (ω : Sample (Zd d L)) (b : Zd d L) :
    ∑ a, (rbmData d P Sig W L z ω).Theta a b = (((msc z).im / z.im : ℝ) : ℂ) := by
  set S := Smat P.ψ W L with hSdef
  set M : ℂ := ((‖msc z‖ ^ 2 : ℝ) : ℂ) with hM
  set A : Matrix (Zd d L) (Zd d L) ℂ := M • S.map fun r => (r : ℂ) with hA
  have hm1 := norm_msc_lt_one hz
  have hM1 : ‖msc z‖ ^ 2 < 1 := by nlinarith [norm_nonneg (msc z)]
  have hcol : ∀ c, ∑ a, S a c = 1 := fun c => by
    rw [← hS.rowSum c]
    exact Finset.sum_congr rfl fun a _ => hS.symm a c
  have hAcol : ∀ c, ∑ a, A a c = M := fun c => by
    simp only [hA, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, hcol c]
    simp
  have hdet := det_one_sub_smul_ne_zero S M
    (by rw [hM, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hM1)
    hS.nonneg hS.rowSum
  have hU : IsUnit (1 - A) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hΘ := modelData_Theta S z hmat ω hS.nonneg hS.rowSum hz
  change (rbmData d P Sig W L z ω).Theta * (1 - A) = A at hΘ
  set Θ := (rbmData d P Sig W L z ω).Theta with hΘdef
  have hone : ∀ c, ∑ a, (1 - A) a c = 1 - M := fun c => by
    simp only [Matrix.sub_apply]
    rw [Finset.sum_sub_distrib, hAcol c]
    simp [Matrix.one_apply]
  set u : Zd d L → ℂ := fun c => ∑ a, Θ a c with hu
  have hL : u ᵥ* (1 - A) = fun c => M := by
    have : (fun _ => (1 : ℂ)) ᵥ* (Θ * (1 - A)) = fun c => M := by
      rw [hΘ]; funext c; simp [Matrix.vecMul, dotProduct, hAcol c]
    rw [← this, ← Matrix.vecMul_vecMul]
    congr 1
    funext c; simp [Matrix.vecMul, dotProduct, hu]
  set c₀ : ℂ := M / (1 - M) with hc₀
  have hM1' : (1 - M) ≠ 0 := by
    rw [hM]; norm_cast; linarith
  have hR : (fun _ => c₀) ᵥ* (1 - A) = fun c => M := by
    funext c
    simp only [Matrix.vecMul, dotProduct]
    rw [← Finset.mul_sum, hone c, hc₀]
    field_simp
  have heq : u = fun _ => c₀ := (Matrix.vecMul_injective_iff_isUnit.2 hU) (hL.trans hR.symm)
  have := congrFun heq b
  simp only [hu] at this
  rw [this, hc₀, hM]
  have hr := ThetaDecay_ratio hz
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, ← hr]


/-- `E G_{xx} = E G_{00}` for every `x` ([I, (5.45)]): translation invariance of the model at
a variance kernel and `Im z > 0`. -/
theorem expG_diag (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) (x : Zd d L) :
    ∫ ω, green (hmat ω) z x x ∂(gaussLaw (Smat P.ψ W L)) =
      ∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L)) := by
  have hs : (Smat P.ψ W L).IsSymm := Matrix.IsSymm.ext fun i j => hS.symm j i
  have h := (modelTransInv d P (fun _ => []) ⟨[], [], [], [], []⟩ W L z hs hz).2.2.1 0 0 x
  have hprob := isProbabilityMeasure_gaussLaw (Smat P.ψ W L)
  have key : ∀ y : Zd d L, expC d P W L (fun ω => star (green (hmat ω) z y y) - star (msc z)) =
      star (∫ ω, green (hmat ω) z y y ∂(gaussLaw (Smat P.ψ W L))) - star (msc z) := by
    intro y
    change ∫ ω, (star (green (hmat ω) z y y) - star (msc z)) ∂(gaussLaw (Smat P.ψ W L)) = _
    rw [integral_sub, integral_const]
    · simp only [Complex.star_def, probReal_univ, one_smul]
      rw [integral_conj]
    · exact integrable_star_green _ z hz y y
    · exact integrable_const _
  have hg : ∀ x b : Zd d L, expC d P W L (gammaVal (([] : Expansion 3)) ⟨Pexp (Smat P.ψ W L)⟩
      (rbmData d P (fun _ => []) W L z) x b) = 0 := fun x b => by
    have : gammaVal (([] : Expansion 3)) ⟨Pexp (Smat P.ψ W L)⟩
      (rbmData d P (fun _ => []) W L z) x b = fun _ => 0 := by
      funext ω; simp [gammaVal]
    rw [this]; simp [expC]
  simp only [corrMat, Matrix.of_apply, key, List.filter_nil, List.append_nil, hg, add_zero] at h
  have h2 := mul_left_cancel₀ (msc_ne_zero z) h
  have h3 := sub_left_inj.1 h2
  have h4 := congrArg star h3
  simpa using h4


/-- The graphs `T_{a,bb}` are integrable for the law of [I, Assumption 1.1]. -/
theorem tGraph_valR_integrable (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im)
    (a b : Zd d L) :
    Integrable (tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b])
      (gaussLaw (Smat P.ψ W L)) := by
  have hs : (Smat P.ψ W L).IsSymm := Matrix.IsSymm.ext fun i j => hS.symm j i
  refine integrable_of_polyMeas _ _ (QTerm_polyMeas_valR d P Sig W L z hz hs hS.nonneg
    (N := 0) tGraph ?_ _)
  decide

/-- The sum over `b` of `T_{ab} = |m|² Σ_α s_{aα} |G_{αb}|²`, grouped by `α`. -/
theorem tvar_row {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ)
    (m : ℂ) (a : ι) :
    ∑ b, Tvar S G m a b = ‖m‖ ^ 2 * ∑ α, S a α * ∑ b, ‖G α b‖ ^ 2 := by
  simp only [Tvar]
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun α _ => by rw [Finset.mul_sum]

/-- The sum over `b` of `T_{ab}` at every sample: `Σ_b T_{ab} = |m|² Σ_α s_{aα} Im G_{αα}/η`
(Ward identity [I, (5.16)]). -/
theorem ward_row (hz : 0 < z.im) (ω : Sample (Zd d L))
    (a : Zd d L) :
    ∑ b, tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω =
      (((‖msc z‖ ^ 2 * ∑ α, Smat P.ψ W L a α * ((green (hmat ω) z α α).im / z.im) : ℝ)) : ℂ) := by
  simp only [tGraph_valR_eq]
  simp only [← Complex.ofReal_sum]
  congr 1
  rw [tvar_row]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sum_norm_sq_green_row (hmat_isHermitian ω) hz α]


/-- **[I, (5.45)]** for a variance kernel `S` and `Im z > 0`: for every `a`,
`Σ_b E T_{ab} = |m|² Im(E G_{00})/η`, with `T = tGraph` at `(a, b, b)`. -/
theorem expT_row (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) (a : Zd d L) :
    ∑ b, ∫ ω, tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω
        ∂(gaussLaw (Smat P.ψ W L)) =
      ((‖msc z‖ ^ 2 * (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))).im / z.im : ℝ) :
        ℂ) := by
  have hprob := isProbabilityMeasure_gaussLaw (Smat P.ψ W L)
  rw [← integral_finsetSum _ fun b _ => tGraph_valR_integrable P Sig W L z hS hz a b]
  have h1 : (fun ω => ∑ b, tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z)
      ![a, b, b] ω) = fun ω => (((‖msc z‖ ^ 2 / z.im * ∑ α, Smat P.ψ W L a α *
        (green (hmat ω) z α α).im : ℝ)) : ℂ) := by
    funext ω
    rw [ward_row P Sig W L z hz ω a]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [h1, integral_complex_ofReal]
  congr 1
  have hI : ∀ α : Zd d L, ∫ ω, (green (hmat ω) z α α).im ∂(gaussLaw (Smat P.ψ W L)) =
      (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))).im := fun α => by
    rw [← expG_diag P W L z hS hz α]
    exact integral_im_green _ z hz α α
  rw [integral_const_mul, integral_finsetSum _ fun α _ =>
    ((integrable_im_green _ z hz α α).const_mul _)]
  simp_rw [integral_const_mul, hI]
  rw [← Finset.sum_mul, hS.rowSum a]
  ring


/-- The leading term `m Θ_{a b₁} Ḡ_{b₁ b₂}` of [I, (2.7)] at `b₁ = b₂ = b` on the data record of
the model: `m Θ_{ab} Ḡ_{bb}`, at every sample. -/
theorem leadExp_valR_eq (a b : Zd d L) (ω : Sample (Zd d L)) :
    leadExp.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω =
      msc z * (rbmData d P Sig W L z ω).Theta a b * star (green (hmat ω) z b b) := by
  have hl : (thetaLabelGraph []).LabelFree := by
    intro c hc
    simp only [thetaLabelGraph, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  simp only [leadExp, Expansion.valR, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  rw [Graph.valR_of_labelFree 3 0 _ _ _ _ _ _ hl]
  simp [Graph.val, Graph.term, thetaLabelGraph, Comp.val, Coeff.eval, rbmData, modelData,
    Data.chain, cm, mkC, CVar.eval, Charge.apply]
  ring


/-- **[I, (5.45)]** summed over `a`: `Σ_{a,b} E T_{ab} = L^d |m|² Im(E G_{00})/η`. -/
theorem expT_total (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) :
    ∑ a, ∑ b, ∫ ω, tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω
        ∂(gaussLaw (Smat P.ψ W L)) =
      (((L : ℝ) ^ d * (‖msc z‖ ^ 2 * (∫ ω, green (hmat ω) z 0 0
        ∂(gaussLaw (Smat P.ψ W L))).im / z.im) : ℝ) : ℂ) := by
  simp_rw [expT_row P Sig W L z hS hz]
  rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  push_cast
  rfl

/-- **[I, (5.46)]** for a variance kernel `S` and `Im z > 0`:
`Σ_{a,b} E(m Θ_{ab} Ḡ_{bb}) = L^d (|m|²/(1 − |m|²)) m conj(E G_{00})`; the ratio is `Im m/η` by
`msc_ratio`. -/
theorem expLead_total (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) :
    ∑ a, ∑ b, ∫ ω, leadExp.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![a, b, b] ω
        ∂(gaussLaw (Smat P.ψ W L)) =
      ((L : ℝ) ^ d : ℝ) * ((((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) * msc z *
        star (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L)))) := by
  have hint : ∀ a b : Zd d L, ∫ ω, leadExp.valR ⟨Pexp (Smat P.ψ W L)⟩
      (rbmData d P Sig W L z) ![a, b, b] ω ∂(gaussLaw (Smat P.ψ W L)) =
      msc z * (rbmData d P Sig W L z 0).Theta a b *
        star (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))) := by
    intro a b
    simp_rw [leadExp_valR_eq]
    change ∫ ω, (msc z * (rbmData d P Sig W L z 0).Theta a b) * star (green (hmat ω) z b b)
      ∂(gaussLaw (Smat P.ψ W L)) = _
    rw [integral_const_mul]
    have : ∫ ω, star (green (hmat ω) z b b) ∂(gaussLaw (Smat P.ψ W L)) =
        star (∫ ω, green (hmat ω) z b b ∂(gaussLaw (Smat P.ψ W L))) := by
      simp only [Complex.star_def]
      exact integral_conj
    rw [this, expG_diag P W L z hS hz b]
  simp_rw [hint]
  have hc : ∀ b : Zd d L, ∑ a, msc z * (rbmData d P Sig W L z 0).Theta a b *
      star (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))) =
      msc z * star (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))) *
        (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) := by
    intro b
    have h1 : ∀ w : ℂ, ∑ a, msc z * (rbmData d P Sig W L z 0).Theta a b * w =
        (∑ a, (rbmData d P Sig W L z 0).Theta a b) * (msc z * w) := fun w => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, theta_colSum P Sig W L z hS hz 0 b, ← ThetaDecay_ratio hz]
    ring
  rw [Finset.sum_comm]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  push_cast
  ring


/-- **[I, (5.53)]**: `|m|²/(1 − |m|²) = Im m/η` for `η = Im z > 0`. -/
theorem msc_ratio (hz : 0 < z.im) :
    ‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) = (msc z).im / z.im := ThetaDecay_ratio hz

/-- **[I, (5.44)]: `E Q = 0`**. For a variance kernel `S`, `Im z > 0` and a `Q`-graph
([I, Def 2.14 (ii)]) whose components have the kinds of [II, Def 3.2], the expectation of its value
on the data record of the model vanishes, for every labelling `e` of the external atoms. -/
theorem expQ_zero (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) {k n N : ℕ}
    (Γ : Graph k n) (hΓ : Γ.TKinds N) (hQ : Γ.IsQGraph) (e : Fin k → Zd d L) :
    ∫ ω, Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e ω
      ∂(gaussLaw (Smat P.ψ W L)) = 0 := by
  have hs : (Smat P.ψ W L).IsSymm := Matrix.IsSymm.ext fun i j => hS.symm j i
  obtain ⟨u, hu⟩ := hQ
  have hcomp : ∀ c ∈ Γ.comps, c.isTKind N = true ∨ (c.kind = .ghost ∧ c.label = none) :=
    fun c hc => Or.inl (List.all_eq_true.1 hΓ c hc)
  have h := Trace_E_Q d P Sig W L z hz hs hS.nonneg Γ hcomp u hu e
  have hng : ∀ c ∈ Γ.comps, c.kind ≠ .ghost := fun c hc hg => by
    have := List.all_eq_true.1 hΓ c hc
    simp [Comp.isTKind, hg] at this
  rw [← h]
  congr 1
  funext ω
  simp only [Graph.valR]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Graph.termR]
  have hv : ∀ (ω' : Sample (Zd d L)) (c : Comp (Atom k n)), c ∈ Γ.comps →
      Comp.val (rbmData d P Sig W L z ω').ghostOne (Sum.elim e σ) c =
        Comp.val (rbmData d P Sig W L z ω') (Sum.elim e σ) c :=
    fun ω' c hc => Trace_val_ghostOne _ _ c (hng c hc)
  have hm : ∀ ω', (rbmData d P Sig W L z ω').ghostOne.m = (rbmData d P Sig W L z ω').m :=
    fun ω' => rfl
  rw [hm]
  have e1 : List.map (Comp.val (rbmData d P Sig W L z ω).ghostOne (Sum.elim e σ))
      (List.filter (fun c => c.label.isNone) Γ.comps) =
      List.map (Comp.val (rbmData d P Sig W L z ω) (Sum.elim e σ))
        (List.filter (fun c => c.label.isNone) Γ.comps) :=
    List.map_congr_left fun c hc => hv ω c (List.mem_of_mem_filter hc)
  have e2 : ∀ ℓ : PQ × Atom k n, (fun ω' => (List.map
      (Comp.val (rbmData d P Sig W L z ω').ghostOne (Sum.elim e σ))
      (List.filter (fun c => decide (c.label = some ℓ)) Γ.comps)).prod) =
      fun ω' => (List.map (Comp.val (rbmData d P Sig W L z ω') (Sum.elim e σ))
        (List.filter (fun c => decide (c.label = some ℓ)) Γ.comps)).prod := fun ℓ => by
    funext ω'
    congr 1
    exact List.map_congr_left fun c hc => hv ω' c (List.mem_of_mem_filter hc)
  rw [e1]
  simp only [e2]

/-- **[I, (5.49)]**, first line, for every translation invariant matrix `K` (in [I, (5.49)] the
matrix `Σ̃^{(n)}`): `Σ_{a,x,b} (Θ K)_{ax} E T_{xb} =
L^d (|m|²/(1 − |m|²)) (|m|² Im(E G_{00})/η) Σ_α K_{0α}`. -/
theorem sigma_term (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im)
    (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K) :
    ∑ a, ∑ x, ∑ b, ((rbmData d P Sig W L z 0).Theta * K) a x *
        ∫ ω, tGraph.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![x, b, b] ω
          ∂(gaussLaw (Smat P.ψ W L)) =
      ((L : ℝ) ^ d : ℝ) * ((((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) *
        (((‖msc z‖ ^ 2 * (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))).im / z.im : ℝ)
          : ℂ) * ∑ α, K 0 α)) := by
  simp_rw [← Finset.mul_sum, expT_row P Sig W L z hS hz]
  set c' : ℂ := ((‖msc z‖ ^ 2 * (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))).im /
    z.im : ℝ) : ℂ) with hc'
  set Θ := (rbmData d P Sig W L z 0).Theta with hΘ
  have hcol : ∀ y : Zd d L,
      ∑ a, Θ a y = (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) := fun y => by
    rw [hΘ, theta_colSum P Sig W L z hS hz 0 y, msc_ratio z hz]
  have h1 : ∀ x : Zd d L, ∑ a, (Θ * K) a x * c' =
      (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) * (∑ y, K y x) * c' := fun x => by
    simp only [Matrix.mul_apply]
    rw [← Finset.sum_mul, Finset.sum_comm]
    congr 1
    simp_rw [← Finset.sum_mul, hcol]
    rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [h1]
  have h2 : ∑ x, (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) * (∑ y, K y x) * c' =
      (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) * c' * ∑ y, ∑ x, K y x := by
    calc ∑ x, (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) * (∑ y, K y x) * c'
        = (((‖msc z‖ ^ 2 / (1 - ‖msc z‖ ^ 2) : ℝ)) : ℂ) * c' * ∑ x, ∑ y, K y x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by rw [Finset.sum_comm]
  rw [h2]
  simp_rw [sum_transInv hK]
  rw [Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
  push_cast
  ring

end Basic

end MainCancelId

end RBM8D
