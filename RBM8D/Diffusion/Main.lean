import Batteries.Tactic.OpenPrivate
import RBM8D.Diffusion.LocalCorr
import RBM8D.Diffusion.Fourier
import RBM8D.Diffusion.SelfEnergy

/-!
# Quantum diffusion: [I, Theorem 1.5], [I, Corollary 1.6] and [I, Corollary 1.7]

`quantumDiffusion_of : quantumDiffusion_ofStmt`: from the local law [I, Theorem 1.4] and, for
every `d ≥ 8` and profile `P`, a construction with one family of self-energies with `H(n)` for
every `n ≥ 2` ([II, Theorem 3.7, Corollary 3.8, Lemma 3.9]), the joint statement
`quantumDiffusionStmt`. This is the conditional form: the local law and the self-energy family
are hypotheses.

* The self-energies `Σ_l` and their matrices are those of `selfEnergyFamily`. For the order `M`
  the local correction `𝒢^{(M)}` is `corrMat` ([I, (8.16)]) of the `n`-th order `T`-equation with
  error order `n + 2`, `n = max(M + 2, 4)`.
* The invertibility, (1.24), (1.26) and (1.27) at order `M` are those of `thetaMBounds`, and
  (1.28) is `localCorr`.
* [I, (8.15)] at every entry `(a, 𝔟)` (from `singularIdStmt` and `E Q = 0`) reads
  `(1 − X_n |m|² S) E|G|² = |m|² + 𝒢 + Err` with `X_n = 1 + Σ̃^{(n)}`, so that
  `E|G|² = (1 − X_n |m|² S)⁻¹(|m|² + 𝒢 + Err)` and `E T = Θ^{(n)}(|m|² + 𝒢 + Err)` exactly,
  without an inverse of `S` ([I, (8.18)–(8.19)]).
* (1.22) and (1.29) follow from the change of order `n → M` of `thetaMStmt`,
  `Σ_z B_{zy}^{3/2} ≤ C (log₂(L/W) + 2) W^{−d/2}`, [I, (8.17)] (`errBoundStmt`) and the row sums
  of `X_n` from (1.26).
* (1.35): `e₁ = 𝒢̂(p)` and `e₃` is the Fourier sum of the remainder of (1.22), of size
  `L^d W^{−Md/2} ≤ W^{−M}` for `W^M ≥ L⁴`.
* (1.36): `(1 − X̂Â)⁻¹ = Θ̂^{(M)}/Â` with `Θ̂^{(M)} = r(1 + u)/(η + W² p·𝒟_eff p + e)` of
  [I, (1.33)] (`symbolThetaMStmt`), and
  `η + W² p·𝒟_eff p + e₂ = Â(η + W² p·𝒟_eff p + e)/(1 + u)`; the sizes of `Â − 1` and of
  `W² p·𝒟_eff p` come from the second moments of `S` and of `Σ̃^{(M)}`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D

open Graphs

open private LocalCorr_gammaInt LocalCorr_rootRest_tKinds LocalCorr_rootRest_qGraph
  LocalCorr_sigTilde LocalCorr_tf_Gc LocalCorr_rowSum from RBM8D.Diffusion.LocalCorr
open private gm_empty tGraph_val from RBM8D.Diffusion.Singular
open private tf_G tf_mul integ from RBM8D.Diffusion.DiagMean
open private bB_pos₁ im_pos_of_specDom from RBM8D.Bound.Doubly
open private ErrMain_L₀ from RBM8D.Diffusion.ErrMain

open private moment_S moment_sig slack sum_even_eq cos_sum_bounds phase_sum_bounds norm_Q_le
  qform_diffEff im_msc_eq msc_im_sub_le rE_ge phase norm_zfreq_le from RBM8D.Diffusion.Fourier

open ErrForms

section Identity

private theorem Main_sq (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl

private theorem Main_integrable_sq {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) {z : ℂ}
    (hz : 0 < z.im) (x y : Zd d L) :
    Integrable (fun (ω : Sample (Zd d L)) => ((‖green (hmat ω) z x y‖ ^ 2 : ℝ) : ℂ))
      (gaussLaw S) :=
  (integ S (tf_mul (tf_G hz.ne' x y) (LocalCorr_tf_Gc hz.ne' x y))).congr
    (Eventually.of_forall fun ω => (Main_sq _).symm)

private theorem Main_expG2_eq {d : ℕ} (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ)
    (x y : Zd d L) :
    (expG2 d P W L z x y : ℂ) =
      ∫ ω, ((‖green (hmat ω) z x y‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw (Smat P.ψ W L)) := by
  rw [integral_complex_ofReal]; rfl

private theorem Main_expT_eq {d : ℕ} (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ)
    (x y : Zd d L) :
    (expT d P W L z x y : ℂ) = ∫ ω, ∑ α, ((‖msc z‖ ^ 2 : ℝ) : ℂ) * (Smat P.ψ W L x α : ℂ) *
      ((‖green (hmat ω) z α y‖ ^ 2 : ℝ) : ℂ) ∂(gaussLaw (Smat P.ψ W L)) := by
  have h : (expT d P W L z x y : ℂ) = ∫ ω, ((Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) x y :
      ℝ) : ℂ) ∂(gaussLaw (Smat P.ψ W L)) := by
    rw [integral_complex_ofReal]; rfl
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Tvar, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun α _ => by ring

/-- `E T = |m|² S E|G|²` as matrices ([I, (1.21)]). -/
private theorem Main_expT_mul {d : ℕ} (P : Profile d) (W L : ℕ) [NeZero L] {z : ℂ}
    (hz : 0 < z.im) :
    (Matrix.of fun x y => (expT d P W L z x y : ℂ)) =
      amat (Smat P.ψ W L) z * Matrix.of fun x y => (expG2 d P W L z x y : ℂ) := by
  ext x y
  rw [Matrix.of_apply, Main_expT_eq, integral_finsetSum _ fun α _ =>
    (Main_integrable_sq _ hz α y).const_mul _]
  simp only [Matrix.mul_apply, amat, cmat, mAbs2, Matrix.smul_apply, Matrix.map_apply,
    Matrix.of_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_const_mul, Main_expG2_eq, mul_assoc]

/-- **The identity of [I, (8.15)] at the entry `(a, 𝔟)`**, from `singularIdStmt` and `E Q = 0`: for
an `n`-th order `T`-equation with `n ≥ 4`, at a variance kernel `S_{W,L}` and `Im z > 0`,
`E|G_{a𝔟}|² − E T_{a𝔟} = |m|² δ_{a𝔟} + 𝒢_{a𝔟} + Σ_y Σ̃^{(n)}_{ay} E T_{y𝔟}
+ E(Γ_A + Γ_Err)_{a,𝔟𝔟}`. -/
private theorem Main_entryId {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {n D : ℕ}
    {𝒬 : TEqRec} (hn : 4 ≤ n) (hS : 𝒬.IsTEqStruct Sig n D)
    (hNR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) (W L : ℕ) [NeZero L] (z : ℂ)
    (hVK : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) (a b : Zd d L) :
    (expG2 d P W L z a b : ℂ) - (expT d P W L z a b : ℂ) =
      (if a = b then mAbs2 z else 0) + corrMat d P Sig 𝒬 W L z a b +
      ∑ y, (sigMat (Function.update Sig n 𝒬.SigN) (Smat P.ψ W L) z n +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig (Smat P.ψ W L) z l) a y *
        (expT d P W L z y b : ℂ) + errMat d P Sig 𝒬 W L z a b := by
  set S := Smat P.ψ W L with hSdef
  set μ := gaussLaw S with hμ
  have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_gaussLaw S
  have hsym : S.IsSymm := Matrix.IsSymm.ext fun i j => hVK.symm j i
  have hz0 : z.im ≠ 0 := hz.ne'
  set PF : PFamily (Sample (Zd d L)) (Zd d L) := ⟨Pexp S⟩ with hPF
  set Dt := rbmData d P Sig W L z with hDt
  set M := sigMat (Function.update Sig n 𝒬.SigN) S z n +
    ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l with hM
  have hS₀ := hS
  obtain ⟨-, -, hsh, hshN, hShape, hTR, -⟩ := hS
  have hKE : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, g.2.ThetaRooted ∧ g.2.TKindsErr (n - 1) := by
    obtain ⟨⟨h1, h2⟩, -⟩ := hShape
    intro g hg
    refine ⟨hTR g hg, ?_⟩
    rcases List.mem_append.1 hg with hg | hg
    · exact Graph.tKindsErr_of_tKinds _ _ (h1 g hg).2.1
    · exact (h2 g hg).2.1
  have hsub : ∀ l : Expansion 3, (∀ g ∈ l, g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) →
      ∀ g ∈ l, g.2.ThetaRooted ∧ g.2.TKindsErr (n - 1) := fun l hl g hg => hKE g (hl g hg)
  set v : (Σ n, Graph 3 n) → ℂ := fun g => ∫ ω, (rootRest g.2).2.valR PF Dt ![a, b, b] ω ∂μ
    with hv
  have hQ0 : ∀ g ∈ 𝒬.Q, v g = 0 := by
    intro g hg
    have hall : g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err := by simp [hg]
    obtain ⟨j, w, -, hk, -, hlab, hxy, hrest, -⟩ := hTR g hall
    obtain ⟨⟨h1, -⟩, -, -, hQ, -⟩ := hShape
    have hK := (h1 g (List.mem_append_right _ hg)).2.1
    exact MainCancelId.expQ_zero P Sig W L z hVK hz _
      (LocalCorr_rootRest_tKinds g.2 j w hk hxy (fun c hc => (hrest c hc).1) hK)
      (LocalCorr_rootRest_qGraph g.2 j w hk hlab hxy (fun c hc => (hrest c hc).1) (hQ g hg).1)
      ![a, b, b]
  have hall := LocalCorr_gammaInt P Sig W L z hVK hz (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) hKE a b
  have hRA := LocalCorr_gammaInt P Sig W L z hVK hz (𝒬.R ++ 𝒬.A.filter fun g => g.2.pmBlockB)
    (hsub _ fun g hg => by
      rcases List.mem_append.1 hg with h | h
      · simp [h]
      · simp [(List.mem_filter.1 h).1]) a b
  have hAE := LocalCorr_gammaInt P Sig W L z hVK hz
    (𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err)
    (hsub _ fun g hg => by
      rcases List.mem_append.1 hg with h | h
      · simp [(List.mem_filter.1 h).1]
      · simp [h]) a b
  have hsplit : ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map v).sum =
      ((𝒬.R ++ 𝒬.A.filter fun g => g.2.pmBlockB).map v).sum +
        ((𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err).map v).sum := by
    have hA : (𝒬.A.map v).sum = ((𝒬.A.filter fun g => g.2.pmBlockB).map v).sum +
        ((𝒬.A.filter fun g => !g.2.pmBlockB).map v).sum := by
      rw [← List.sum_append, ← List.map_append]
      exact (((List.filter_append_perm _ 𝒬.A).map v).sum_eq).symm
    have hQ : (𝒬.Q.map v).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      exact hQ0 g hg
    simp only [List.map_append, List.sum_append, hA, hQ]
    ring
  set fT : Zd d L → Sample (Zd d L) → ℂ := fun y ω => ∑ x, ((‖msc z‖ ^ 2 : ℝ) : ℂ) *
    (S y x : ℂ) * ((‖green (hmat ω) z x b‖ ^ 2 : ℝ) : ℂ) with hfT
  have hsT : ∀ ω, sigTilde n 𝒬.SigN (modelDataSig Sig S z ω) = M := fun ω =>
    LocalCorr_sigTilde P Sig n hn 𝒬.SigN hsh hshN W L z ω
  have hid : ∀ ω, ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) - fT a ω =
      ((if a = b then msc z * star (green (hmat ω) z b b) else 0) +
        gammaVal (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) PF Dt a b ω) +
        ∑ y, M a y * fT y ω := by
    intro ω
    have h := singularId Sig n D 𝒬 hS₀ hNR (Zd d L) S z hsym hVK.nonneg hVK.rowSum hz a b ω
    simp only [tGraph_val, yRoot, hsT, gm_empty] at h
    exact h
  have hiA : Integrable (fun ω => ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ)) μ :=
    Main_integrable_sq S hz a b
  have hiT : ∀ y, Integrable (fT y) μ := fun y =>
    integrable_finsetSum _ fun x _ => (Main_integrable_sq S hz x b).const_mul _
  have hiY : Integrable (fun ω => if a = b then msc z * star (green (hmat ω) z b b) else 0) μ := by
    by_cases hab : a = b
    · simp only [hab, ite_true]
      exact (integ S (LocalCorr_tf_Gc hz0 b b)).const_mul _
    · simp only [hab, ite_false]
      exact integrable_zero _ _ _
  have hiS : Integrable (fun ω => ∑ y, M a y * fT y ω) μ :=
    integrable_finsetSum _ fun y _ => (hiT y).const_mul _
  have hE := congrArg (fun F : Sample (Zd d L) → ℂ => ∫ ω, F ω ∂μ) (funext hid)
  have hiYγ : Integrable (fun ω => (if a = b then msc z * star (green (hmat ω) z b b) else 0) +
      gammaVal (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) PF Dt a b ω) μ := hiY.add hall.1
  rw [integral_sub hiA (hiT a), integral_add hiYγ hiS, integral_add hiY hall.1,
    hall.2, hsplit, ← hRA.2, ← hAE.2,
    integral_finsetSum _ fun y _ => (hiT y).const_mul _] at hE
  simp only [integral_const_mul] at hE
  have hYi : ∫ ω, (if a = b then msc z * star (green (hmat ω) z b b) else 0) ∂μ =
      if a = b then msc z * ∫ ω, star (green (hmat ω) z b b) ∂μ else 0 := by
    split_ifs
    · exact integral_const_mul _ _
    · exact integral_zero _ _
  have hC : corrMat d P Sig 𝒬 W L z a b =
      msc z * (if a = b then (∫ ω, star (green (hmat ω) z b b) ∂μ - star (msc z)) else 0) +
        ∫ ω, gammaVal (𝒬.R ++ 𝒬.A.filter fun g => g.2.pmBlockB) PF Dt a b ω ∂μ := by
    simp only [corrMat, Matrix.of_apply]
    congr 1
    congr 1
    split_ifs
    · change ∫ ω, (star (green (hmat ω) z b b) - star (msc z)) ∂μ = _
      rw [integral_sub (integ S (LocalCorr_tf_Gc hz0 b b)) (integrable_const _), integral_const]
      simp
      rfl
    · rfl
  have hEr : errMat d P Sig 𝒬 W L z a b =
      ∫ ω, gammaVal (𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err) PF Dt a b ω ∂μ := rfl
  have hG : (expG2 d P W L z a b : ℂ) = ∫ ω, ((‖green (hmat ω) z a b‖ ^ 2 : ℝ) : ℂ) ∂μ :=
    Main_expG2_eq P W L z a b
  have hT : ∀ y, (expT d P W L z y b : ℂ) = ∫ ω, fT y ω ∂μ := fun y => Main_expT_eq P W L z y b
  rw [hC, hEr, hG, hT a]
  simp only [hT]
  rw [hYi] at hE
  unfold mAbs2
  rw [Main_sq (msc z)]
  split_ifs at hE ⊢ <;> linear_combination hE

/-- `Σ̃^{(n)}` of an `n`-th order `T`-equation with `Σ_n = Sig n` on the model is `Σ_{l=4}^{n} Σ_l`
for the matrices `Σ_l` of `SigmaOf`, where `S_{W,L}` is symmetric: the odd orders vanish. -/
private theorem Main_sigTilde_eq {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (Sg : SigmaFam d)
    (hSg : SigmaOf d P Sig Sg) {n : ℕ} (hn : 4 ≤ n) (W L : ℕ) [NeZero L] (z : ℂ)
    (hS : (Smat P.ψ W L).IsSymm) :
    sigMat (Function.update Sig n (Sig n)) (Smat P.ψ W L) z n +
        ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig (Smat P.ψ W L) z l =
      sigTildeM Sg n W L z := by
  have hodd : ∀ l, 4 ≤ l → ¬ Even l → sigMat Sig (Smat P.ψ W L) z l = 0 := by
    intro l hl he
    have h0 : Sig l = [] := G13.shape_odd_nil (Nat.not_even_iff_odd.1 he) (hSg.1 l hl)
    ext x y
    simp [sigMat, h0, Expansion.val]
  rw [Function.update_eq_self, sigTildeM, ← Finset.Ico_insert_right hn,
    Finset.sum_insert (by simp), hSg.2.1 n hn W L z hS]
  congr 1
  rw [Finset.sum_filter_of_ne]
  · exact Finset.sum_congr rfl fun l hl => (hSg.2.1 l (Finset.mem_Ico.1 hl).1 W L z hS).symm
  · intro l hl h
    by_contra he
    exact h (hodd l (Finset.mem_Ico.1 hl).1 he)

/-- **Solving the identity** in a ring: from `T = A G` and `G − T = V + (X − 1) T` with
`1 − A X` invertible, `G = (1 − X A)⁻¹ V` and `T = (1 − A X)⁻¹ A V`. -/
private theorem Main_solve {R : Type*} [Ring R] (A X G T V : R) (hU : IsUnit (1 - A * X))
    (hT : T = A * G) (hid : G - T = V + (X - 1) * T) :
    G = Ring.inverse (1 - X * A) * V ∧ T = Ring.inverse (1 - A * X) * A * V := by
  obtain ⟨u, hu⟩ := hU
  have h1 : (1 - A * X) * Ring.inverse (1 - A * X) = 1 := by
    rw [← hu, Ring.mul_inverse_cancel _ u.isUnit]
  have h2 : Ring.inverse (1 - A * X) * (1 - A * X) = 1 := by
    rw [← hu, Ring.inverse_mul_cancel _ u.isUnit]
  have hR := G16.inverse_one_sub_mul A X ⟨u, hu⟩
  set w := Ring.inverse (1 - A * X)
  have hV : (1 - X * A) * G = V := by
    have : (1 - X * A) * G = G - T - (X - 1) * T := by rw [hT]; noncomm_ring
    rw [this, hid]; abel
  have hL : (1 + X * w * A) * (1 - X * A) = 1 := by
    have : (1 + X * w * A) * (1 - X * A) = 1 - X * A + X * (w * (1 - A * X)) * A := by
      noncomm_ring
    rw [this, h2]
    noncomm_ring
  have hG : G = Ring.inverse (1 - X * A) * V := by
    rw [hR, ← hV, ← mul_assoc, hL, one_mul]
  refine ⟨hG, ?_⟩
  rw [hT, hG, hR, ← mul_assoc]
  congr 1
  have hw : w = 1 + A * X * w :=
    calc w = (1 - A * X) * w + A * X * w := by noncomm_ring
      _ = 1 + A * X * w := by rw [h1]
  calc A * (1 + X * w * A) = (1 + A * X * w) * A := by noncomm_ring
    _ = w * A := by rw [← hw]

/-- `1 − X A` is invertible with `1 − A X`, for square matrices. -/
private theorem Main_isUnit_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (A X : Matrix ι ι ℂ)
    (hU : IsUnit (1 - A * X)) : IsUnit (1 - X * A) := by
  rw [Matrix.isUnit_iff_isUnit_det] at hU ⊢
  rwa [Matrix.det_one_sub_mul_comm]

/-- **[I, (8.15)] solved** ([I, (8.18)–(8.19)] with `n` in place of `M`): on the model at a
variance kernel and `Im z > 0`, for an `n`-th order `T`-equation (`n ≥ 4`) with `Σ_n = Sig n` and
`1 − |m|² S (1 + Σ̃^{(n)})` invertible, `E T = Θ^{(n)}(|m|² + 𝒢 + Err)` and
`E|G|² = (1 − X_n |m|² S)⁻¹ (|m|² + 𝒢 + Err)`. -/
private theorem Main_solved {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (Sg : SigmaFam d)
    (hSg : SigmaOf d P Sig Sg) {n D : ℕ} {𝒬 : TEqRec} (hn : 4 ≤ n) (hS : 𝒬.IsTEqStruct Sig n D)
    (hNR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) (hSN : 𝒬.SigN = Sig n)
    (W L : ℕ) [NeZero L] (z : ℂ) (hVK : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im)
    (hU : IsUnit (1 - amat (Smat P.ψ W L) z * (1 + sigTildeM Sg n W L z))) :
    (Matrix.of fun x y => (expG2 d P W L z x y : ℂ)) =
        resM (Smat P.ψ W L) (1 + sigTildeM Sg n W L z) z *
          (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z + errMat d P Sig 𝒬 W L z) ∧
      (Matrix.of fun x y => (expT d P W L z x y : ℂ)) =
        thetaM (Smat P.ψ W L) (1 + sigTildeM Sg n W L z) z *
          (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z + errMat d P Sig 𝒬 W L z) := by
  have hsym : (Smat P.ψ W L).IsSymm := Matrix.IsSymm.ext fun i j => hVK.symm j i
  have hM := Main_sigTilde_eq P Sig Sg hSg hn W L z hsym
  rw [← hSN] at hM
  have hid : (Matrix.of fun x y => (expG2 d P W L z x y : ℂ)) -
      (Matrix.of fun x y => (expT d P W L z x y : ℂ)) =
      (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z + errMat d P Sig 𝒬 W L z) +
        ((1 + sigTildeM Sg n W L z) - 1) * Matrix.of fun x y => (expT d P W L z x y : ℂ) := by
    ext a b
    have h := Main_entryId P Sig hn hS hNR W L z hVK hz a b
    rw [hM] at h
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, add_sub_cancel_left, Matrix.mul_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h ⊢
    rw [h]
    ring
  obtain ⟨h1, h2⟩ := Main_solve _ _ _ _ _ hU (Main_expT_mul P W L hz) hid
  refine ⟨h1, ?_⟩
  rw [h2, thetaM]

end Identity

section Remainder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem Main_mul_le (P Q : Matrix ι ι ℂ) (x y : ι) :
    ‖(P * Q) x y‖ ≤ ∑ z, ‖P x z‖ * ‖Q z y‖ := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  rw [norm_mul]

/-- **The remainders of [I, (1.22)] and [I, (1.29)]** from the entry bounds: with
`V' = c + 𝒢`, `V = V' + Err`, `|c| ≤ 1`, `|(Θ_n − Θ_M)_{xy}|, |(R_n − R_M)_{xy}| ≤ λβ`,
`|Θ_n| ≤ λB`, `Σ_z |𝒢_{zy}| ≤ K₁`, `|Err| ≤ ε₁`, `Σ_z B_{xz} |Err_{zy}| ≤ ε₂`,
`Σ_w |X_{xw}| ≤ K₂` and `R_n = 1 + X Θ_n`: the entries of `Θ_n V − Θ_M V'` are at most
`λβ(1 + K₁) + λε₂`, those of `R_n V − R_M V'` at most `λβ(1 + K₁) + ε₁ + K₂ λ ε₂`. -/
private theorem Main_rem (Θn ΘM Rn RM X Gc Er : Matrix ι ι ℂ) (c : ℂ) (B : ι → ι → ℝ)
    (lam β K₁ K₂ ε₁ ε₂ : ℝ) (hc : ‖c‖ ≤ 1) (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (hε₂ : 0 ≤ ε₂)
    (hΘn : ∀ x y, ‖Θn x y‖ ≤ lam * B x y)
    (hdΘ : ∀ x y, ‖(Θn - ΘM) x y‖ ≤ lam * β) (hdR : ∀ x y, ‖(Rn - RM) x y‖ ≤ lam * β)
    (hGc : ∀ y, ∑ z, ‖Gc z y‖ ≤ K₁) (hEr1 : ∀ x y, ‖Er x y‖ ≤ ε₁)
    (hEr2 : ∀ x y, ∑ z, B x z * ‖Er z y‖ ≤ ε₂) (hX : ∀ x, ∑ w, ‖X x w‖ ≤ K₂)
    (hRn : Rn = 1 + X * Θn) (x y : ι) :
    ‖(Θn * (c • 1 + Gc + Er) - ΘM * (c • 1 + Gc)) x y‖ ≤ lam * β * (1 + K₁) + lam * ε₂ ∧
      ‖(Rn * (c • 1 + Gc + Er) - RM * (c • 1 + Gc)) x y‖ ≤
        lam * β * (1 + K₁) + ε₁ + K₂ * (lam * ε₂) := by
  set V' := c • (1 : Matrix ι ι ℂ) + Gc with hV'
  have hcol : ∀ y, ∑ z, ‖V' z y‖ ≤ 1 + K₁ := by
    intro y
    have h1 : ∀ z, ‖V' z y‖ ≤ ‖(c • (1 : Matrix ι ι ℂ)) z y‖ + ‖Gc z y‖ := fun z => by
      rw [hV', Matrix.add_apply]; exact norm_add_le _ _
    have h2 : ∑ z, ‖(c • (1 : Matrix ι ι ℂ)) z y‖ = ‖c‖ := by
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single y (fun z _ hz => by simp [hz]) (by simp)]
      simp
    calc ∑ z, ‖V' z y‖ ≤ ∑ z, (‖(c • (1 : Matrix ι ι ℂ)) z y‖ + ‖Gc z y‖) :=
          Finset.sum_le_sum fun z _ => h1 z
      _ ≤ 1 + K₁ := by rw [Finset.sum_add_distrib, h2]; linarith [hGc y]
  have hD : ∀ (P : Matrix ι ι ℂ), (∀ x y, ‖P x y‖ ≤ lam * β) → ∀ x y,
      ‖(P * V') x y‖ ≤ lam * β * (1 + K₁) := by
    intro P hP x y
    refine (Main_mul_le P V' x y).trans ?_
    calc ∑ z, ‖P x z‖ * ‖V' z y‖ ≤ ∑ z, lam * β * ‖V' z y‖ :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hP x z) (norm_nonneg _)
      _ = lam * β * ∑ z, ‖V' z y‖ := by rw [Finset.mul_sum]
      _ ≤ lam * β * (1 + K₁) := mul_le_mul_of_nonneg_left (hcol y) (by positivity)
  have hTE : ∀ x y, ‖(Θn * Er) x y‖ ≤ lam * ε₂ := by
    intro x y
    refine (Main_mul_le Θn Er x y).trans ?_
    calc ∑ z, ‖Θn x z‖ * ‖Er z y‖ ≤ ∑ z, lam * (B x z * ‖Er z y‖) :=
          Finset.sum_le_sum fun z _ => by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hΘn x z) (norm_nonneg _)
      _ = lam * ∑ z, B x z * ‖Er z y‖ := by rw [Finset.mul_sum]
      _ ≤ lam * ε₂ := mul_le_mul_of_nonneg_left (hEr2 x y) hlam
  have e1 : Θn * (V' + Er) - ΘM * V' = (Θn - ΘM) * V' + Θn * Er := by noncomm_ring
  have e2 : Rn * (V' + Er) - RM * V' = (Rn - RM) * V' + (Er + X * (Θn * Er)) := by
    rw [hRn]; noncomm_ring
  constructor
  · rw [e1, Matrix.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hD _ hdΘ x y) (hTE x y))
  · rw [e2, Matrix.add_apply, Matrix.add_apply]
    refine (norm_add_le _ _).trans ?_
    have h3 : ‖(X * (Θn * Er)) x y‖ ≤ K₂ * (lam * ε₂) := by
      refine (Main_mul_le X _ x y).trans ?_
      calc ∑ w, ‖X x w‖ * ‖(Θn * Er) w y‖ ≤ ∑ w, ‖X x w‖ * (lam * ε₂) :=
            Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hTE w y) (norm_nonneg _)
        _ = (∑ w, ‖X x w‖) * (lam * ε₂) := by rw [Finset.sum_mul]
        _ ≤ K₂ * (lam * ε₂) := mul_le_mul_of_nonneg_right (hX x) (by positivity)
    have := hD _ hdR x y
    have := hEr1 x y
    linarith [norm_add_le (Er x y) ((X * (Θn * Er)) x y)]

end Remainder

section Sums

/-- `Σ_z B_{zy}^{3/2} ≤ C (log₂(L/W) + 2) W^{−d/2}` for `d ≥ 8`, `W ≥ 1`, `L ≥ 2W`
([I, (6.32)] with one factor `B`). -/
private theorem Main_sumB32 {d : ℕ} (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L → ∀ y : Zd d L,
      ∑ z, bB d L W z y ^ ((3 : ℝ) / 2) ≤ C * logF L W * (W : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, h⟩ := keyobs3 d 1 2 (by omega) one_pos two_pos (by linarith) 1 le_rfl
  obtain ⟨C₀, hC₀, hw⟩ := weak_sqrtB hd
  refine ⟨max C 0 * C₀, by positivity, fun L W _ hW hWL y => ?_⟩
  have h1 := h L W hW hWL (fun p q => Real.sqrt (bB d L W p q)) y ![y]
  have hwn := hw L W hW 1 zero_le_one (fun p q => Real.sqrt (bB d L W p q))
    (fun p q => by rw [abs_of_nonneg (Real.sqrt_nonneg _), one_mul])
  rw [gammaB_one] at h1
  have hlhs : ∑ z, bB d L W z y ^ ((3 : ℝ) / 2) =
      ∑ x, |Real.sqrt (bB d L W x y)| * ∏ i : Fin 1, bB d L W x (![y] i) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Fin.prod_univ_one, bB_three_halves hW]
    simp only [Matrix.cons_val_zero]
    ring
  rw [hlhs]
  refine h1.trans ?_
  have hl := logF_nonneg hW (by omega : W ≤ L)
  have hw0 := weak_sqrtB_nonneg (d := d) hW y
  have e : -(1 * (d : ℝ) / 2) = -((d : ℝ) / 2) := by ring
  rw [e, pow_one, mul_one]
  calc C * logF L W * (W : ℝ) ^ (-((d : ℝ) / 2)) *
        weakNorm d L W 1 2 (fun p q => Real.sqrt (bB d L W p q))
      ≤ max C 0 * logF L W * (W : ℝ) ^ (-((d : ℝ) / 2)) * (C₀ * 1) := by
        gcongr
        exact le_max_left _ _
    _ = _ := by ring

/-- The row sums of `1 + Σ̃^{(n)}` from [I, (1.26)] and translation invariance:
`Σ_w |(1 + Σ̃^{(n)})_{xw}| ≤ 1 + n A C W^{−d}`. -/
private theorem Main_rowX {d : ℕ} (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (Sg : SigmaFam d) (n : ℕ) (z : ℂ) (A : ℝ), 0 ≤ A →
      (∀ l, 4 ≤ l → ∀ x a : Zd d L, Sg l W L z x (x + a) = Sg l W L z 0 a) →
      (∀ l, 4 ≤ l → l ≤ n → ∀ x : Zd d L, ‖Sg l W L z 0 x‖ ≤
        A * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
          (if x = 0 then A * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) →
      ∀ x : Zd d L, ∑ w, ‖(1 + sigTildeM Sg n W L z) x w‖ ≤
        1 + n * (A * C * (W : ℝ) ^ (-(d : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := LocalCorr_rowSum hd
  refine ⟨C, hC0, fun L W _ hW Sg n z A hA hT hB x => ?_⟩
  have hrow : ∀ l ∈ Finset.Icc 4 n, ∑ w, ‖Sg l W L z x w‖ ≤ A * C * (W : ℝ) ^ (-(d : ℝ)) := by
    intro l hl
    obtain ⟨hl4, hln⟩ := Finset.mem_Icc.1 hl
    have e : ∑ w, ‖Sg l W L z x w‖ = ∑ a, ‖Sg l W L z 0 a‖ := by
      rw [← Fintype.sum_equiv (Equiv.addLeft x) (fun a => ‖Sg l W L z x (x + a)‖) _
        (fun a => rfl)]
      exact Finset.sum_congr rfl fun a _ => by rw [hT l hl4 x a]
    rw [e]
    exact hC L W hW _ A l hl4 hA (hB l hl4 hln)
  have hcard : ((Finset.Icc 4 n).card : ℝ) ≤ n := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : n + 1 - 4 ≤ n)
  have hK : 0 ≤ A * C * (W : ℝ) ^ (-(d : ℝ)) := by positivity
  calc ∑ w, ‖(1 + sigTildeM Sg n W L z) x w‖
      ≤ ∑ w, (‖(1 : Matrix (Zd d L) (Zd d L) ℂ) x w‖ +
          ∑ l ∈ Finset.Icc 4 n, ‖Sg l W L z x w‖) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [Matrix.add_apply, sigTildeM, Matrix.sum_apply]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = 1 + ∑ l ∈ Finset.Icc 4 n, ∑ w, ‖Sg l W L z x w‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        rw [Finset.sum_eq_single x (fun w _ hw => by simp [Ne.symm hw])
          (by simp)]
        simp
    _ ≤ 1 + ∑ _l ∈ Finset.Icc 4 n, A * C * (W : ℝ) ^ (-(d : ℝ)) := by
        gcongr with l hl; exact hrow l hl
    _ = 1 + (Finset.Icc 4 n).card * (A * C * (W : ℝ) ^ (-(d : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 + n * (A * C * (W : ℝ) ^ (-(d : ℝ))) := by gcongr

end Sums

section Part2

/-- **[I, (1.22)] and [I, (1.29)]** for the local correction `𝒢^{(M)}` of an `n`-th order
`T`-equation with `n ≥ max(M + 2, 4)` and error order `n + 2`: there are `C`, `L₀` such that
`|E T_{xy} − (Θ^{(M)}(|m|² + 𝒢))_{xy}| ≤ C W^{−Md/2}` and
`|E|G_{xy}|² − ((1 − X_M|m|²S)⁻¹(|m|² + 𝒢))_{xy}| ≤ C W^{−Md/2}` for `L ≥ L₀`,
`(W, L) ∈ adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)`. -/
private theorem Main_part2 (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε)
    (Sig : ℕ → Expansion 2) (hSE : ∀ l, 4 ≤ l → Even l → IsSelfEnergy d (smatVar P) Sig l)
    (Sg : SigmaFam d) (hSg : SigmaOf d P Sig Sg) (M : ℕ) {n : ℕ} (hMn : M + 2 ≤ n)
    (hn : 4 ≤ n) {𝒬 : TEqRec} (hS : 𝒬.IsTEqStruct Sig n (n + 2))
    (hNR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2) (hSN : 𝒬.SigN = Sig n)
    (hSEn : SelfEnergiesUpTo d (smatVar P) Sig n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
        ‖(expT d P W L z x y : ℂ) - (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
            (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z)) x y‖ ≤
          C * (W : ℝ) ^ (-((M : ℝ) * d / 2)) ∧
        ‖(expG2 d P W L z x y : ℂ) - (resM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
            (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z)) x y‖ ≤
          C * (W : ℝ) ^ (-((M : ℝ) * d / 2)) := by
  set c₀' := min c₀ (1 / 2) with hc₀'def
  have hc₀' : 0 < c₀' := lt_min hc₀ (by norm_num)
  have hc₀'1 : c₀' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set τ₀ : ℝ := min c₁ 1 / 8 with hτ₀
  have hτ₀0 : 0 < τ₀ := by positivity
  have hτ₀8 : τ₀ ≤ 1 / 8 := by
    have := min_le_right c₁ 1; rw [hτ₀]; linarith
  have hτ₀c : τ₀ / c₁ ≤ 1 / 8 := by
    rw [div_le_iff₀ hc₁]; have := min_le_left c₁ 1; rw [hτ₀]; linarith
  obtain ⟨L₁, hL₁⟩ := thetaMBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M n
    (by omega) τ₀ hτ₀0
  obtain ⟨L₂, hL₂⟩ := thetaMBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg n n le_rfl τ₀
    hτ₀0
  obtain ⟨L₃, hL₃⟩ := localCorr hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n (n + 2) 𝒬 hn le_rfl hS
    hNR hSEn τ₀ hτ₀0
  obtain ⟨L₄, hL₄⟩ := errBound hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n (n + 2) 𝒬 hn le_rfl hS
    hNR hSEn τ₀ hτ₀0
  obtain ⟨W_VK, hVK⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨C₁, hC₁0, hB32⟩ := Main_sumB32 hd
  obtain ⟨CX, hCX0, hXrow⟩ := Main_rowX hd
  obtain ⟨Wl, -, hlog⟩ := logF_le_rpow (c₀ := c₀) hc₁ (δ := 1 / 8) (by norm_num)
  obtain ⟨W₂, -, htwo⟩ := two_mul_le_of_adm (c₁ := c₁) hc₀' hc₀'1
  obtain ⟨L₅, hL₅⟩ := ErrMain_L₀ (c₀ := c₀) hc₁ (max (max 1 W_VK) (max Wl W₂))
  refine ⟨3 + C₁ + n * CX, by positivity, max (max L₁ L₂) (max (max L₃ L₄) L₅),
    fun W L _ hL hadm z hz x y => ?_⟩
  have hLi : ∀ {i}, i ≤ max (max L₁ L₂) (max (max L₃ L₄) L₅) → i ≤ L := fun h => h.trans hL
  have hW := hL₅ W L (hLi (le_max_of_le_right (le_max_right _ _))) hadm
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hVKW := hVK W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hzim : 0 < z.im := im_pos_of_specDom hWn hz
  have hadm' : (W, L) ∈ adm c₀' c₁ := ⟨hadm.1, hadm.2.trans
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_left c₀ (1 / 2)]))⟩
  have hL2 : 2 * W ≤ L := htwo W L hadm' ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  have hlogW : logF L W ≤ (W : ℝ) ^ (1 / 8 : ℝ) :=
    hlog W L hadm ((le_max_left _ _).trans ((le_max_right _ _).trans hW)) (by exact_mod_cast hL1)
  obtain ⟨-, -, -, -, hdΘ, hdR⟩ :=
    hL₁ W L (hLi (le_max_of_le_left (le_max_left _ _))) hadm z hz
  obtain ⟨hUn, hΘn, h126n, -, -, -⟩ :=
    hL₂ W L (hLi (le_max_of_le_left (le_max_right _ _))) hadm z hz
  have hGc := hL₃ W L (hLi (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))) hadm z hz
  have hEr := hL₄ W L (hLi (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))) hadm z hz
  obtain ⟨hG2, hET⟩ := Main_solved P Sig Sg hSg hn hS hNR hSN W L z hVKW hzim hUn
  -- the sizes
  set w : ℝ := (W : ℝ) with hw
  set a8 : ℝ := w ^ (1 / 8 : ℝ) with ha8
  have ha81 : 1 ≤ a8 := Real.one_le_rpow hW1 (by norm_num)
  set lam : ℝ := (L : ℝ) ^ τ₀ with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam8 : lam ≤ a8 := by
    calc lam = ((L : ℝ) ^ c₁) ^ (τ₀ / c₁) := by
          rw [hlam, ← Real.rpow_mul (by positivity), mul_div_cancel₀ _ hc₁.ne']
      _ ≤ w ^ (τ₀ / c₁) := Real.rpow_le_rpow (by positivity) hadm.1 (by positivity)
      _ ≤ a8 := Real.rpow_le_rpow_of_exponent_le hW1 hτ₀c
  have hwτ : w ^ τ₀ ≤ a8 := Real.rpow_le_rpow_of_exponent_le hW1 hτ₀8
  set β : ℝ := w ^ (-(((M : ℝ) + 1) * d / 2)) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hMn' : (M : ℝ) + 2 ≤ n := by exact_mod_cast hMn
  set ε₁ : ℝ := w ^ τ₀ * w ^ (-(((n : ℝ) - 1) * d / 2)) with hε₁
  set ε₂ : ℝ := w ^ τ₀ * w ^ (-(((n : ℝ) + 1) * d / 2)) with hε₂
  have hε₂0 : 0 ≤ ε₂ := by positivity
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have e1 : ((M : ℝ) + 1) * d ≤ ((n : ℝ) - 1) * d := mul_le_mul_of_nonneg_right (by linarith) hd0
  have e2 : ((M : ℝ) + 1) * d ≤ ((n : ℝ) + 1) * d := mul_le_mul_of_nonneg_right (by linarith) hd0
  have hε₁b : ε₁ ≤ a8 * β := mul_le_mul hwτ (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
    (by positivity) (by positivity)
  have hε₂b : ε₂ ≤ a8 * β := mul_le_mul hwτ (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
    (by positivity) (by positivity)
  set K₁ : ℝ := lam * (C₁ * logF L W * w ^ (-((d : ℝ) / 2))) with hK₁
  have hK₁b : K₁ ≤ C₁ := by
    have h1 : lam * logF L W * w ^ (-((d : ℝ) / 2)) ≤ 1 := by
      calc lam * logF L W * w ^ (-((d : ℝ) / 2)) ≤ a8 * a8 * w ^ (-((d : ℝ) / 2)) := by
            gcongr
            exact logF_nonneg hWn (by omega)
        _ = w ^ ((1 / 4 : ℝ) + -((d : ℝ) / 2)) := by
            rw [ha8, ← Real.rpow_add hW0, ← Real.rpow_add hW0]; norm_num
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
    calc K₁ = C₁ * (lam * logF L W * w ^ (-((d : ℝ) / 2))) := by rw [hK₁]; ring
      _ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left h1 hC₁0
      _ = C₁ := mul_one _
  set K₂ : ℝ := 1 + n * (lam * CX * w ^ (-(d : ℝ))) with hK₂
  have hK₂b : K₂ ≤ 1 + n * CX := by
    have h1 : lam * w ^ (-(d : ℝ)) ≤ 1 := by
      calc lam * w ^ (-(d : ℝ)) ≤ w ^ (1 / 8 : ℝ) * w ^ (-(d : ℝ)) := by gcongr
        _ = w ^ ((1 / 8 : ℝ) + -(d : ℝ)) := by rw [← Real.rpow_add hW0]
        _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
    have : lam * CX * w ^ (-(d : ℝ)) ≤ CX := by
      calc lam * CX * w ^ (-(d : ℝ)) = CX * (lam * w ^ (-(d : ℝ))) := by ring
        _ ≤ CX * 1 := mul_le_mul_of_nonneg_left h1 hCX0
        _ = CX := mul_one _
    rw [hK₂]; gcongr
  have hfin : a8 * a8 * β ≤ w ^ (-((M : ℝ) * d / 2)) := by
    rw [ha8, hβ, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by ring_nf; linarith)
  -- the entry bounds
  have hRn : resM (Smat P.ψ W L) (1 + sigTildeM Sg n W L z) z =
      1 + (1 + sigTildeM Sg n W L z) * thetaM (Smat P.ψ W L) (1 + sigTildeM Sg n W L z) z := by
    rw [resM, thetaM, G16.inverse_one_sub_mul _ _ hUn, mul_assoc]
  have hc : ‖mAbs2 z‖ ≤ 1 := by
    rw [mAbs2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (norm_nonneg _) (norm_msc_lt_one hzim).le
  have hGcol : ∀ y, ∑ z', ‖corrMat d P Sig 𝒬 W L z z' y‖ ≤ K₁ := by
    intro y
    calc ∑ z', ‖corrMat d P Sig 𝒬 W L z z' y‖ ≤ ∑ z', lam * bB d L W z' y ^ ((3 : ℝ) / 2) :=
          Finset.sum_le_sum fun z' _ => hGc z' y
      _ = lam * ∑ z', bB d L W z' y ^ ((3 : ℝ) / 2) := by rw [Finset.mul_sum]
      _ ≤ K₁ := mul_le_mul_of_nonneg_left (hB32 L W hWn hL2 y) hlam0
  have hX := hXrow L W hWn Sg n z lam hlam0
    (fun l hl x a => (hSg.2.2 l hl W L z x a).1) h126n
  obtain ⟨r1, r2⟩ := Main_rem _ _ _ _ _ _ _ (mAbs2 z) (bB d L W) lam β K₁ K₂ ε₁ ε₂ hc hlam0 hβ0
    hε₂0 hΘn hdΘ hdR hGcol (fun a b => (hEr a b).1) (fun a b => (hEr a b).2) hX hRn x y
  have eT : (expT d P W L z x y : ℂ) = (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg n W L z) z *
      (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z + errMat d P Sig 𝒬 W L z)) x y := by
    rw [← hET, Matrix.of_apply]
  have eG : (expG2 d P W L z x y : ℂ) = (resM (Smat P.ψ W L) (1 + sigTildeM Sg n W L z) z *
      (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z + errMat d P Sig 𝒬 W L z)) x y := by
    rw [← hG2, Matrix.of_apply]
  rw [eT, eG, ← Matrix.sub_apply, ← Matrix.sub_apply]
  have hC0 : 0 ≤ C₁ := hC₁0
  have hlb : lam * β ≤ a8 * a8 * β := by
    have : lam ≤ a8 * a8 := hlam8.trans (le_mul_of_one_le_left (by linarith) ha81)
    exact mul_le_mul_of_nonneg_right this hβ0
  have hK₁0 : 0 ≤ K₁ := by
    have := logF_nonneg hWn (by omega : W ≤ L)
    positivity
  have h1 : lam * β * (1 + K₁) ≤ a8 * a8 * β * (1 + C₁) :=
    mul_le_mul hlb (by linarith) (by linarith) (by positivity)
  have h2 : lam * ε₂ ≤ a8 * a8 * β := by
    calc lam * ε₂ ≤ a8 * (a8 * β) := mul_le_mul hlam8 hε₂b hε₂0 (by linarith)
      _ = a8 * a8 * β := by ring
  have h3 : ε₁ ≤ a8 * a8 * β := hε₁b.trans (by
    have := mul_le_mul_of_nonneg_right ha81 (by positivity : 0 ≤ a8 * β)
    linarith [show a8 * a8 * β = a8 * (a8 * β) by ring])
  have hK₂0 : 0 ≤ K₂ := by positivity
  have h4 : K₂ * (lam * ε₂) ≤ (1 + n * CX) * (a8 * a8 * β) :=
    mul_le_mul hK₂b h2 (by positivity) (by positivity)
  have hfin' : 0 ≤ a8 * a8 * β := by positivity
  have hn0 : (0 : ℝ) ≤ n * CX := by positivity
  constructor
  · refine r1.trans ?_
    calc lam * β * (1 + K₁) + lam * ε₂ ≤ a8 * a8 * β * (1 + C₁) + a8 * a8 * β := add_le_add h1 h2
      _ = (2 + C₁) * (a8 * a8 * β) := by ring
      _ ≤ (3 + C₁ + n * CX) * (a8 * a8 * β) :=
          mul_le_mul_of_nonneg_right (by linarith) hfin'
      _ ≤ (3 + C₁ + n * CX) * w ^ (-((M : ℝ) * d / 2)) := by gcongr
  · refine r2.trans ?_
    calc lam * β * (1 + K₁) + ε₁ + K₂ * (lam * ε₂)
        ≤ a8 * a8 * β * (1 + C₁) + a8 * a8 * β + (1 + n * CX) * (a8 * a8 * β) := by
          gcongr
      _ = (3 + C₁ + n * CX) * (a8 * a8 * β) := by ring
      _ ≤ (3 + C₁ + n * CX) * w ^ (-((M : ℝ) * d / 2)) := by gcongr

end Part2

section Fraction

/-- **[I, (1.36)] from [I, (1.33)]**: with `Θ̂ = Â/(1 − ÂX̂) = r(1 + u)/(η + q + e)` and
`R̂ = (1 − X̂Â)⁻¹`, the choice `e₂ = Â(η + q + e)/(1 + u) − η − q` gives
`R̂(c + e₁) = r(c + e₁)/(η + q + e₂)` with a nonzero denominator. -/
private theorem Main_frac (Ah Xh Θh Rh u e q c e₁ : ℂ) (r η : ℝ) (hr : r ≠ 0) (hAh : Ah ≠ 0)
    (hu : 1 + u ≠ 0) (hD : (η : ℂ) + q + e ≠ 0) (hΘ : Θh = Ah / (1 - Ah * Xh))
    (hR : Rh = (1 - Xh * Ah)⁻¹) (hΘ' : Θh = r * (1 + u) / ((η : ℂ) + q + e)) :
    (η : ℂ) + q + (Ah * ((η : ℂ) + q + e) / (1 + u) - η - q) ≠ 0 ∧
      Rh * (c + e₁) =
        r * (c + e₁) / ((η : ℂ) + q + (Ah * ((η : ℂ) + q + e) / (1 + u) - η - q)) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have h1 : 1 - Ah * Xh ≠ 0 := by
    intro h
    rw [h, div_zero] at hΘ
    rw [hΘ] at hΘ'
    exact (div_ne_zero (mul_ne_zero hr' hu) hD) hΘ'.symm
  have e1 : (η : ℂ) + q + (Ah * ((η : ℂ) + q + e) / (1 + u) - η - q) =
      Ah * ((η : ℂ) + q + e) / (1 + u) := by ring
  rw [e1]
  refine ⟨div_ne_zero (mul_ne_zero hAh hD) hu, ?_⟩
  have e2 : Rh = Θh / Ah := by
    rw [hR, hΘ, mul_comm Xh Ah]
    field_simp
  rw [e2, hΘ']
  field_simp

/-- The size of `e₂ = Â(η + q + e)/(1 + u) − η − q`: `|e₂| ≤ C(η² + Vη + Y³)` from
`|Â − 1| ≤ C_a(η + Y²)`, `|u| ≤ C_u(η + Y²)`, `|u| ≤ 1/2`, `|q| ≤ C_q Y²`, `|Â| ≤ 1` and
`|e| ≤ C_e(η² + Vη + Y³)`, for `η, Y ∈ [0, 1]`. -/
private theorem Main_e2_bound (Ah u e q : ℂ) (η Y V Ca Cu Cq Ce : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hV : 0 ≤ V) (hCa : 0 ≤ Ca) (hCu : 0 ≤ Cu) (hCq : 0 ≤ Cq)
    (hCe : 0 ≤ Ce) (hA1 : ‖Ah‖ ≤ 1) (hA : ‖Ah - 1‖ ≤ Ca * (η + Y ^ 2))
    (hu : ‖u‖ ≤ Cu * (η + Y ^ 2)) (hu2 : ‖u‖ ≤ 1 / 2) (hq : ‖q‖ ≤ Cq * Y ^ 2)
    (he : ‖e‖ ≤ Ce * (η ^ 2 + V * η + Y ^ 3)) :
    ‖Ah * ((η : ℂ) + q + e) / (1 + u) - η - q‖ ≤
      (4 * (Ca + Cu) * (1 + Cq) + 2 * Ce) * (η ^ 2 + V * η + Y ^ 3) := by
  have hu1 : 1 / 2 ≤ ‖1 + u‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-u)
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have hu0 : 1 + u ≠ 0 := fun h => by rw [h, norm_zero] at hu1; linarith
  have e1 : Ah * ((η : ℂ) + q + e) / (1 + u) - η - q =
      ((Ah - 1 - u) * ((η : ℂ) + q) + Ah * e) / (1 + u) := by
    field_simp; ring
  set T : ℝ := η ^ 2 + V * η + Y ^ 3 with hT
  have hT0 : 0 ≤ T := by positivity
  have hX : (η + Y ^ 2) ^ 2 ≤ 2 * T := by
    have h1 : Y ^ 4 ≤ Y ^ 3 := by
      have := pow_le_pow_of_le_one hY0 hY1 (by norm_num : 3 ≤ 4); linarith
    have h2 : 2 * η * Y ^ 2 ≤ η ^ 2 + Y ^ 4 := by nlinarith [sq_nonneg (η - Y ^ 2)]
    have h3 : 0 ≤ V * η := mul_nonneg hV hη0
    nlinarith
  have hηq : ‖(η : ℂ) + q‖ ≤ (1 + Cq) * (η + Y ^ 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0]
    have : 0 ≤ Cq * η := mul_nonneg hCq hη0
    nlinarith
  have hnum : ‖(Ah - 1 - u) * ((η : ℂ) + q) + Ah * e‖ ≤
      (2 * (Ca + Cu) * (1 + Cq) + Ce) * T := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hAu : ‖Ah - 1 - u‖ ≤ (Ca + Cu) * (η + Y ^ 2) := by
      refine (norm_sub_le _ _).trans ?_
      linarith
    have h1 : ‖Ah - 1 - u‖ * ‖(η : ℂ) + q‖ ≤ (Ca + Cu) * (1 + Cq) * (2 * T) := by
      calc ‖Ah - 1 - u‖ * ‖(η : ℂ) + q‖ ≤ ((Ca + Cu) * (η + Y ^ 2)) * ((1 + Cq) * (η + Y ^ 2)) :=
            mul_le_mul hAu hηq (norm_nonneg _) (by positivity)
        _ = (Ca + Cu) * (1 + Cq) * (η + Y ^ 2) ^ 2 := by ring
        _ ≤ (Ca + Cu) * (1 + Cq) * (2 * T) := by gcongr
    have h2 : ‖Ah‖ * ‖e‖ ≤ Ce * T := by
      calc ‖Ah‖ * ‖e‖ ≤ 1 * (Ce * T) := mul_le_mul hA1 he (norm_nonneg _) zero_le_one
        _ = Ce * T := one_mul _
    linarith
  rw [e1, norm_div]
  rw [div_le_iff₀ (by linarith)]
  calc ‖(Ah - 1 - u) * ((η : ℂ) + q) + Ah * e‖ ≤ (2 * (Ca + Cu) * (1 + Cq) + Ce) * T := hnum
    _ = (4 * (Ca + Cu) * (1 + Cq) + 2 * Ce) * T * (1 / 2) := by ring
    _ ≤ (4 * (Ca + Cu) * (1 + Cq) + 2 * Ce) * T * ‖1 + u‖ := by gcongr

/-- `|Σ_x e^{ip·x} f(x)| ≤ C W^{−M}` from `|f(x)| ≤ C W^{−Md/2}` and `L⁴ ≤ W^M`, for `d ≥ 4`. -/
private theorem Main_e3 {d L : ℕ} [NeZero L] (hd : 4 ≤ d) (W M : ℕ) (hW : (1 : ℝ) ≤ W)
    (hLW : (L : ℝ) ^ 4 ≤ (W : ℝ) ^ M) (C : ℝ) (hC : 0 ≤ C) (f : Zd d L → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ C * (W : ℝ) ^ (-((M : ℝ) * d / 2))) (k : Zd d L) :
    ‖∑ x, zchar k x * f x‖ ≤ C * (W : ℝ) ^ (-(M : ℝ)) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hcard : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by simp [Zd]
  have hLd : (L : ℝ) ^ d ≤ (W : ℝ) ^ ((M : ℝ) * d / 4) := by
    calc (L : ℝ) ^ d = ((L : ℝ) ^ 4) ^ ((d : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1; push_cast; ring
      _ ≤ ((W : ℝ) ^ M) ^ ((d : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hLW (by positivity)
      _ = (W : ℝ) ^ ((M : ℝ) * d / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
  calc ‖∑ x, zchar k x * f x‖ ≤ ∑ x, ‖zchar k x * f x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Zd d L, C * (W : ℝ) ^ (-((M : ℝ) * d / 2)) :=
        Finset.sum_le_sum fun x _ => by rw [norm_mul, norm_zchar, one_mul]; exact hf x
    _ = (L : ℝ) ^ d * (C * (W : ℝ) ^ (-((M : ℝ) * d / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
    _ ≤ (W : ℝ) ^ ((M : ℝ) * d / 4) * (C * (W : ℝ) ^ (-((M : ℝ) * d / 2))) := by gcongr
    _ = C * (W : ℝ) ^ ((M : ℝ) * d / 4 + -((M : ℝ) * d / 2)) := by
        rw [Real.rpow_add hW0]; ring
    _ ≤ C * (W : ℝ) ^ (-(M : ℝ)) := by
        have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW (by nlinarith)) hC

end Fraction

section Cor17

/-- **[I, Corollary 1.7]** for the local correction `𝒢^{(M)}` of an `n`-th order `T`-equation
(`n ≥ 4`, error order `n + 2`), from [I, (1.22)], [I, (1.29)] in the form of `Main_part2`'s
conclusion, [I, (1.28)] and [I, (1.33)]: (1.35) with `e₁ = 𝒢̂(p)` and (1.36) with
`η + q + e₂ = Â(η + q + e)/(1 + u)`. -/
private theorem Main_cor17 (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε)
    (Sig : ℕ → Expansion 2) (hSE : ∀ l, 4 ≤ l → Even l → IsSelfEnergy d (smatVar P) Sig l)
    (Sg : SigmaFam d) (hSg : SigmaOf d P Sig Sg) (M : ℕ) {n : ℕ} (hn : 4 ≤ n) {𝒬 : TEqRec}
    (hS : 𝒬.IsTEqStruct Sig n (n + 2))
    (hNR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, noRootLabel g.2)
    (hSEn : SelfEnergiesUpTo d (smatVar P) Sig n)
    (hP2 : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
        ‖(expT d P W L z x y : ℂ) - (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
            (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z)) x y‖ ≤
          C * (W : ℝ) ^ (-((M : ℝ) * d / 2)) ∧
        ‖(expG2 d P W L z x y : ℂ) - (resM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
            (mAbs2 z • 1 + corrMat d P Sig 𝒬 W L z)) x y‖ ≤
          C * (W : ℝ) ^ (-((M : ℝ) * d / 2))) :
    cor17Concl d P c₀ c₁ κ ε Sg M := by
  intro δ τ hδ hτ
  obtain ⟨C₂, hC₂0, L₂, hP⟩ := hP2
  set c₀' := min c₀ (1 / 2) with hc₀'def
  have hc₀' : 0 < c₀' := lt_min hc₀ (by norm_num)
  have hc₀'1 : c₀' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set τ₁ : ℝ := c₁ * (τ / 2) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  obtain ⟨L₃, hLC⟩ := localCorr hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n (n + 2) 𝒬 hn le_rfl hS
    hNR hSEn τ₁ hτ₁0
  obtain ⟨Cs, Ls, hSym⟩ := symbolThetaM d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M δ τ hδ hτ
  obtain ⟨L₄, hTM⟩ := thetaMBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M M le_rfl c₁ hc₁
  obtain ⟨W_VK, hVK⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨C₁, hC₁0, hB32⟩ := Main_sumB32 hd
  obtain ⟨Wl, -, hlog⟩ := logF_le_rpow (c₀ := c₀) hc₁ (δ := τ / 2) (by positivity)
  obtain ⟨W₂, -, htwo⟩ := two_mul_le_of_adm (c₁ := c₁) hc₀' hc₀'1
  obtain ⟨CS2, hCS20, hCS2⟩ := moment_S d P c₀ c₁ hc₀ 2
  obtain ⟨L₁, hL₁⟩ := slack d hd c₁ M hc₁ (Nat.cast_nonneg M)
  set r₀ : ℝ := Real.sqrt (2 * κ) / 2 with hr₀
  have hr₀0 : 0 < r₀ := by rw [hr₀]; have := Real.sqrt_pos.2 (by linarith : 0 < 2 * κ); linarith
  set A₂ : ℝ := (d : ℝ) ^ 2 * CS2 / 2 with hA₂
  set B₂ : ℝ := (d : ℝ) ^ 2 / 2 with hB₂
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  set Cs' : ℝ := max Cs 0 with hCs'
  have hCs'0 : 0 ≤ Cs' := le_max_right _ _
  set Ca : ℝ := A₂ + 2 / r₀ with hCa
  have hCa0 : 0 ≤ Ca := by positivity
  set Cq : ℝ := A₂ + B₂ with hCq
  have hCq0 : 0 ≤ Cq := by positivity
  set K : ℝ := max (max (4 * Cs') (2 * A₂ + 2)) (2 / r₀ ^ 2) with hK
  obtain ⟨L₅, hL₅⟩ := ErrMain_L₀ (c₀ := c₀) hc₁
    (max (max (max 1 W_VK) (max Wl W₂)) ((max 1 K) ^ (1 / δ)))
  refine ⟨C₁ + C₂ + (4 * (Ca + Cs') * (1 + Cq) + 2 * Cs'),
    max (max (max L₂ L₃) (max Ls L₄)) (max L₁ (max L₅ 1)),
    fun W L _ hL hadm hLW E η hE hη1 hη2 k hk => ?_⟩
  have hLi : ∀ {i}, i ≤ max (max (max L₂ L₃) (max Ls L₄)) (max L₁ (max L₅ 1)) → i ≤ L :=
    fun h => h.trans hL
  have hW := hL₅ W L (hLi (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))) hadm
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hW))
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast hLi (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  have hL0 : (0 : ℝ) < L := by linarith
  set z : ℂ := (E : ℂ) + η * I with hzdef
  have hzre : z.re = E := by simp [hzdef]
  have hzim : z.im = η := by simp [hzdef]
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hWδ : (W : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hηle : η ≤ 1 := hη2.trans hWδ
  have hz : z ∈ specDom κ ε W L := ⟨by rw [hzre]; exact hE, by rw [hzim]; exact hη1,
    by rw [hzim]; exact hηle⟩
  have hzim0 : 0 < z.im := by rw [hzim]; exact hη0
  have hVKW := hVK W L hadm ((le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hW)))
  have hsym : (Smat P.ψ W L).IsSymm := Matrix.IsSymm.ext fun i j => hVKW.symm j i
  have hadm' : (W, L) ∈ adm c₀' c₁ := ⟨hadm.1, hadm.2.trans
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_left c₀ (1 / 2)]))⟩
  have hL2 : 2 * W ≤ L := htwo W L hadm' ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hW)))
  have hlogW : logF L W ≤ (W : ℝ) ^ (τ / 2) :=
    hlog W L hadm ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hW)))
      (by exact_mod_cast hL1)
  have hKW : K ≤ (W : ℝ) ^ δ := const_le_rpow' hδ ((le_max_right _ _).trans hW)
  have hRem := hP W L (hLi (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))) hadm z hz
  have hGc := hLC W L (hLi (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))) hadm z hz
  obtain ⟨hUM, -, h126, -, -, -⟩ :=
    hTM W L (hLi (le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))) hadm z hz
  obtain ⟨u, e, hu, he, hDne, hΘeq⟩ :=
    hSym W L (hLi (le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))) hadm E η hE hη1 hη2
      k hk
  -- translation invariance
  set S := Smat P.ψ W L with hSdef
  set σ := sigTildeM Sg M W L z with hσdef
  set Gc := corrMat d P Sig 𝒬 W L z with hGcdef
  have hσx : ∀ x, σ 0 x = ∑ l ∈ Finset.Icc 4 M, Sg l W L z 0 x := fun x =>
    Matrix.sum_apply _ _ _ _
  have hTS : TransInv (cmat S) := fun x y a => by
    simp only [cmat, Matrix.map_apply, hSdef, Smat_transInv d L P.ψ W x y a]
  have hTA : TransInv (amat S z) := fun x y a => by
    simp only [amat, Matrix.smul_apply, hTS x y a]
  have hTl : ∀ l ∈ Finset.Icc 4 M, TransInv (Sg l W L z) := by
    intro l hl x y a
    have hl4 := (Finset.mem_Icc.1 hl).1
    have h1 := (hSg.2.2 l hl4 W L z (x + a) (y - x)).1
    have h2 := (hSg.2.2 l hl4 W L z x (y - x)).1
    rw [show x + a + (y - x) = y + a by abel] at h1
    rw [show x + (y - x) = y by abel] at h2
    rw [h1, h2]
  have hTσ : TransInv σ := fun x y a => by
    simp only [hσdef, sigTildeM, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun l hl => hTl l hl x y a
  have hTX : TransInv (1 + σ) := fun x y a => by
    simp only [Matrix.add_apply, Matrix.one_apply, add_left_inj, hTσ x y a]
  have hTAX : TransInv (amat S z * (1 + σ)) := TransInv_mul _ _ hTA hTX
  have hTXA : TransInv ((1 + σ) * amat S z) := TransInv_mul _ _ hTX hTA
  have hT1 : TransInv (1 - (1 + σ) * amat S z) := fun x y a => by
    simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, hTXA x y a]
  have hT1' : TransInv (1 - amat S z * (1 + σ)) := fun x y a => by
    simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, hTAX x y a]
  have hTΘ : TransInv (thetaM S (1 + σ) z) :=
    TransInv_mul _ _ (TransInv_ringInverse _ hT1') hTA
  have hTR : TransInv (resM S (1 + σ) z) := TransInv_ringInverse _ hT1
  have hTGc : TransInv Gc := (modelTransInv d P Sig 𝒬 W L z hsym hzim0).2.2.1
  have hTV : TransInv (mAbs2 z • (1 : Matrix (Zd d L) (Zd d L) ℂ) + Gc) := fun x y a => by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, add_left_inj, hTGc x y a]
  -- the symbols
  set Sh := symbol (cmat S) k with hShdef
  set Xh := symbol (1 + σ) k with hXhdef
  set a := ‖msc z‖ ^ 2 with hadef
  set μ := (msc z).im with hμdef
  set r := rE E with hrdef
  have hAh : symbol (amat S z) k = (a : ℂ) * Sh := (symbol_add_smul (cmat S) (cmat S) _ k).2
  have hsymV : symbol (mAbs2 z • (1 : Matrix (Zd d L) (Zd d L) ℂ) + Gc) k =
      mAbs2 z + symbol Gc k := by
    rw [(symbol_add_smul _ Gc 1 k).1, (symbol_add_smul 1 1 (mAbs2 z) k).2, symbol_one, mul_one]
  have hΘh : symbol (thetaM S (1 + σ) z) k =
      symbol (amat S z) k / (1 - symbol (amat S z) k * Xh) := by
    unfold thetaM
    exact G16.symbol_inv_mul _ _ hTA hTX hUM k
  have hRh : symbol (resM S (1 + σ) z) k = (1 - Xh * symbol (amat S z) k)⁻¹ := by
    unfold resM
    rw [symbol_ringInverse _ hT1 (Main_isUnit_swap _ _ hUM) k]
    congr 1
    have : symbol (1 - (1 + σ) * amat S z) k = symbol 1 k - symbol ((1 + σ) * amat S z) k := by
      simp only [symbol, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [this, symbol_one, symbol_mul _ _ hTX hTA]
  -- the symbol sums
  have hsum_symbol : ∀ (K' : Matrix (Zd d L) (Zd d L) ℂ), ∑ x, zchar k x * K' 0 x = symbol K' k :=
    fun K' => Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hsplit : ∀ (F : Zd d L → ℂ) (K' : Matrix (Zd d L) (Zd d L) ℂ),
      ∑ x, zchar k x * F x = symbol K' k + ∑ x, zchar k x * (F x - K' 0 x) := by
    intro F K'
    rw [← hsum_symbol, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  -- `e₁`
  have he₁ : ‖symbol Gc k‖ ≤ C₁ * (W : ℝ) ^ (-((d : ℝ) / 2) + τ) := by
    have hLτ : (L : ℝ) ^ τ₁ ≤ (W : ℝ) ^ (τ / 2) := by
      rw [hτ₁, Real.rpow_mul hL0.le]
      exact Real.rpow_le_rpow (by positivity) hadm.1 (by positivity)
    calc ‖symbol Gc k‖ ≤ ∑ x, ‖Gc 0 x * zchar k x‖ := norm_sum_le _ _
      _ ≤ ∑ x, (L : ℝ) ^ τ₁ * bB d L W x 0 ^ ((3 : ℝ) / 2) :=
          Finset.sum_le_sum fun x _ => by
            rw [norm_mul, norm_zchar, mul_one, bB_comm x 0]; exact hGc 0 x
      _ = (L : ℝ) ^ τ₁ * ∑ x, bB d L W x 0 ^ ((3 : ℝ) / 2) := by rw [Finset.mul_sum]
      _ ≤ (W : ℝ) ^ (τ / 2) * (C₁ * (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-((d : ℝ) / 2))) := by
          refine mul_le_mul hLτ ((hB32 L W hWn hL2 0).trans ?_)
            (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (bB_pos₁ hWn x 0).le _) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogW hC₁0) (by positivity)
      _ = C₁ * (W : ℝ) ^ (-((d : ℝ) / 2) + τ) := by
          rw [Real.rpow_add hW0, show (W : ℝ) ^ τ = (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) by
            rw [← Real.rpow_add hW0]; ring_nf]
          ring
  have hC₁le : C₁ ≤ C₁ + C₂ + (4 * (Ca + Cs') * (1 + Cq) + 2 * Cs') := by
    have : 0 ≤ 4 * (Ca + Cs') * (1 + Cq) + 2 * Cs' := by positivity
    linarith
  have hC₂le : C₂ ≤ C₁ + C₂ + (4 * (Ca + Cs') * (1 + Cq) + 2 * Cs') := by
    have : 0 ≤ 4 * (Ca + Cs') * (1 + Cq) + 2 * Cs' := by positivity
    linarith
  have hd4 : 4 ≤ d := by omega
  constructor
  · -- (1.35)
    refine ⟨symbol Gc k, ∑ x, zchar k x * ((expT d P W L z 0 x : ℂ) -
      (thetaM S (1 + σ) z * (mAbs2 z • 1 + Gc)) 0 x), ?_, ?_, ?_⟩
    · exact he₁.trans (mul_le_mul_of_nonneg_right hC₁le (by positivity))
    · exact (Main_e3 hd4 W M hW1 hLW C₂ hC₂0 _ (fun x => (hRem 0 x).1) k).trans
        (mul_le_mul_of_nonneg_right hC₂le (by positivity))
    · rw [hsplit _ (thetaM S (1 + σ) z * (mAbs2 z • 1 + Gc)), symbol_mul _ _ hTΘ hTV, hsymV]
  · -- (1.36): the symbol of `S`, the quadratic form and the semicircle law
    have hS0 : ∀ x y, 0 ≤ S x y := hVKW.nonneg
    have hS1 : ∑ x, S 0 x = 1 := hVKW.rowSum 0
    have hSe : ∀ x : Zd d L, S 0 (-x) = S 0 x := by
      intro x
      have h1 := hsym.apply 0 x
      simp only [hSdef, Smat, Matrix.of_apply, zero_sub, sub_zero, neg_neg] at h1 ⊢
      exact h1
    have hShc : Sh = ∑ x, ((S 0 x : ℝ) : ℂ) * (Real.cos (phase k x) : ℂ) := by
      rw [hShdef]
      simp only [symbol, cmat, Matrix.map_apply]
      exact sum_even_eq (fun x => ((S 0 x : ℝ) : ℂ)) (fun x => by simp only [hSe]) k
    obtain ⟨cs1, -⟩ := cos_sum_bounds (fun x => ((S 0 x : ℝ) : ℂ)) k
    obtain ⟨ps2, -⟩ := phase_sum_bounds (fun x => ((S 0 x : ℝ) : ℂ)) k
    obtain ⟨pg2, -⟩ := phase_sum_bounds (fun x => σ 0 x) k
    have qs := norm_Q_le (fun x => ((S 0 x : ℝ) : ℂ)) k
    have qg := norm_Q_le (fun x => σ 0 x) k
    have hnS : ∀ x, ‖((S 0 x : ℝ) : ℂ)‖ = |S 0 x| := fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [hnS] at cs1 ps2 qs
    have m2 := hCS2 W L hadm hWn
    set p := ‖zfreq k‖ with hpdef
    have hp0 : 0 ≤ p := norm_nonneg _
    set Y : ℝ := (W : ℝ) * p with hYdef
    have hY0 : 0 ≤ Y := by positivity
    have hYt : Y ≤ (W : ℝ) ^ (-δ) := by
      have h1 : (W : ℝ) * p ≤ (W : ℝ) * (W : ℝ) ^ (-1 - δ) := mul_le_mul_of_nonneg_left hk hW0.le
      have h2 : (W : ℝ) * (W : ℝ) ^ (-1 - δ) = (W : ℝ) ^ (-δ) := by
        rw [← Real.rpow_one_add' hW0.le (by ring_nf; exact neg_ne_zero.2 hδ.ne')]; ring_nf
      rw [hYdef]; exact h1.trans h2.le
    have hY1 : Y ≤ 1 := hYt.trans hWδ
    have hY2le : Y ^ 2 ≤ Y :=
      calc Y ^ 2 = Y * Y := sq Y
        _ ≤ Y * 1 := mul_le_mul_of_nonneg_left hY1 hY0
        _ = Y := mul_one Y
    have hsl : (M : ℝ) * (L : ℝ) ^ c₁ * (2 + 2 * Real.log L) ^ d ≤ (W : ℝ) ^ d := by
      have h1 := hL₁ L (hLi (le_max_of_le_right (le_max_left _ _)))
      have h3 : (L : ℝ) ^ (c₁ * d) ≤ (W : ℝ) ^ d := by
        rw [Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) hadm.1 d
      exact h1.trans h3
    have hσ2 : ∑ x, ‖σ 0 x‖ * (zdistInf d L x : ℝ) ^ 2 ≤ (W : ℝ) ^ 2 := by
      have h := moment_sig d L W M hWn 2 (by norm_num) (by omega) ((L : ℝ) ^ c₁) (by positivity)
        (fun l x => Sg l W L z 0 x) (fun l => (L : ℝ) ^ c₁ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)))
        h126
      simp only [← hσx] at h
      refine h.trans ?_
      have e : (W : ℝ) ^ (((2 : ℕ) : ℝ) - d) * (W : ℝ) ^ d = (W : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast W d, ← Real.rpow_add hW0, ← Real.rpow_natCast]; ring_nf
      calc (M : ℝ) * (L : ℝ) ^ c₁ * (W : ℝ) ^ (((2 : ℕ) : ℝ) - d) * (2 + 2 * Real.log L) ^ d
          = (W : ℝ) ^ (((2 : ℕ) : ℝ) - d) * ((M : ℝ) * (L : ℝ) ^ c₁ *
              (2 + 2 * Real.log L) ^ d) := by ring
        _ ≤ (W : ℝ) ^ (((2 : ℕ) : ℝ) - d) * (W : ℝ) ^ d := by gcongr
        _ = _ := e
    set Qs : ℂ := ∑ x, ((S 0 x : ℝ) : ℂ) * ((phase k x ^ 2 / 2 : ℝ) : ℂ) with hQsdef
    set Qg : ℂ := ∑ x, σ 0 x * ((phase k x ^ 2 / 2 : ℝ) : ℂ) with hQgdef
    have hsumS : ∑ x, ((S 0 x : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sum, hS1, Complex.ofReal_one]
    have hSabs : ∀ x, |S 0 x| = S 0 x := fun x => abs_of_nonneg (hS0 0 x)
    have hm2 : ∑ x, |S 0 x| * (zdistInf d L x : ℝ) ^ 2 ≤ CS2 * (W : ℝ) ^ 2 := m2
    have hY2 : A₂ * Y ^ 2 = (d : ℝ) ^ 2 * p ^ 2 / 2 * (CS2 * (W : ℝ) ^ 2) := by
      rw [hA₂, hYdef]; ring
    have hSh : ‖Sh‖ ≤ 1 := by
      rw [hShc]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ x, ‖((S 0 x : ℝ) : ℂ) * (Real.cos (phase k x) : ℂ)‖ ≤ ∑ x, S 0 x := by
            refine Finset.sum_le_sum fun x _ => ?_
            rw [norm_mul, hnS, hSabs, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_of_le_one_right (hS0 0 x) (Real.abs_cos_le_one _)
        _ = 1 := hS1
    have h1 : ‖Sh - 1‖ ≤ A₂ * Y ^ 2 := by
      rw [hShc, ← hsumS, hY2]
      refine cs1.trans (ps2.trans ?_)
      gcongr
    have hQs : ‖Qs‖ ≤ A₂ * Y ^ 2 := by
      rw [hY2]
      refine qs.trans (ps2.trans ?_)
      gcongr
    have hQg : ‖Qg‖ ≤ B₂ * Y ^ 2 := by
      refine qg.trans (pg2.trans ?_)
      rw [hB₂, hYdef]
      calc (d : ℝ) ^ 2 * p ^ 2 / 2 * ∑ x, ‖σ 0 x‖ * (zdistInf d L x : ℝ) ^ 2
          ≤ (d : ℝ) ^ 2 * p ^ 2 / 2 * (W : ℝ) ^ 2 := by gcongr
        _ = _ := by ring
    have hWne : W ≠ 0 := by omega
    have hq : qform W k (diffEff P Sg M W L z) = (r : ℂ) * Qs + (r : ℂ) * Qg := by
      rw [qform_diffEff P Sg M W L hWne z k, hzre]
    -- the semicircle law
    have hμ0 : 0 < μ := msc_im_pos hzim0
    have ha : a * (η + μ) = μ := by
      have := im_msc_eq z
      rw [hzim] at this
      exact this.symm
    have hμr : |μ - r| ≤ η / r := by
      have := msc_im_sub_le hzim0 (by rw [hzre]; exact hE.trans (sub_lt_self 2 hκ))
      rwa [hzre, hzim] at this
    have hr : r₀ ≤ r := rE_ge hκ hE
    have hr0 : 0 < r := lt_of_lt_of_le hr₀0 hr
    have hr1 : r ≤ 1 := by
      rw [hrdef, rE, div_le_one (by norm_num)]
      calc Real.sqrt (4 - E ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith [sq_nonneg E])
        _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have ha0 : 0 < a := by
      rw [hadef]; exact pow_pos (norm_pos_iff.2 (msc_ne_zero z)) 2
    have ha1 : a ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_msc_lt_one hzim0).le
    -- the size `t = W^{−δ}`
    set t : ℝ := (W : ℝ) ^ (-δ) with htdef
    have ht0 : 0 ≤ t := by positivity
    have hKt : K * t ≤ 1 := by
      have : (W : ℝ) ^ δ * t = 1 := by
        rw [htdef, ← Real.rpow_add hW0, add_neg_cancel, Real.rpow_zero]
      calc K * t ≤ (W : ℝ) ^ δ * t := mul_le_mul_of_nonneg_right hKW ht0
        _ = 1 := this
    have hK1 : 4 * Cs' * t ≤ 1 :=
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) ht0).trans hKt
    have hK2 : (2 * A₂ + 2) * t ≤ 1 :=
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) ht0).trans hKt
    have hK3 : 2 / r₀ ^ 2 * t ≤ 1 :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ht0).trans hKt
    have hηt : η ≤ t := hη2
    have hηr : η ≤ r₀ ^ 2 / 2 := by
      have : 2 / r₀ ^ 2 * η ≤ 1 := (mul_le_mul_of_nonneg_left hηt (by positivity)).trans hK3
      rw [div_mul_eq_mul_div, div_le_one (by positivity)] at this
      linarith
    have hμ2 : r₀ / 2 ≤ μ := by
      have h1 : η / r ≤ r / 2 := by
        rw [div_le_iff₀ hr0]
        have : r₀ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr₀0.le hr 2
        linarith [show r / 2 * r = r ^ 2 / 2 by ring]
      have := (abs_le.1 hμr).1
      linarith
    have h1a : 1 - a ≤ 2 / r₀ * η := by
      have e1 : (1 - a) * μ = a * η := by linarith
      have e2 : (1 - a) * μ ≤ η := by rw [e1]; exact mul_le_of_le_one_left hη0.le ha1
      have e3 : (1 - a) * (r₀ / 2) ≤ η := by
        rcases le_or_gt (1 - a) 0 with h | h
        · linarith [mul_nonpos_of_nonpos_of_nonneg h (by positivity : (0 : ℝ) ≤ r₀ / 2)]
        · exact (mul_le_mul_of_nonneg_left hμ2 h.le).trans e2
      rw [div_mul_eq_mul_div, le_div_iff₀ hr₀0]
      linarith
    -- the bounds of `Â`, `u`, `q`
    set Ah := symbol (amat S z) k with hAhdef
    have hAh1 : ‖Ah‖ ≤ 1 := by
      rw [hAh, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
      calc a * ‖Sh‖ ≤ 1 * 1 := mul_le_mul ha1 hSh (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    have hAhb : ‖Ah - 1‖ ≤ Ca * (η + Y ^ 2) := by
      have e : Ah - 1 = (a : ℂ) * (Sh - 1) - ((1 - a : ℝ) : ℂ) := by rw [hAh]; push_cast; ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos ha0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a)]
      have : a * ‖Sh - 1‖ ≤ A₂ * Y ^ 2 :=
        (mul_le_of_le_one_left (norm_nonneg _) ha1).trans h1
      rw [hCa]
      have : 0 ≤ A₂ * η := by positivity
      have : 0 ≤ 2 / r₀ * Y ^ 2 := by positivity
      linarith [show (A₂ + 2 / r₀) * (η + Y ^ 2) = A₂ * η + A₂ * Y ^ 2 + 2 / r₀ * η +
        2 / r₀ * Y ^ 2 by ring]
    have hu' : ‖u‖ ≤ Cs' * (η + Y ^ 2) := hu.trans (by
      rw [hYdef, mul_pow]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hu2 : ‖u‖ ≤ 1 / 2 := by
      refine hu'.trans ?_
      have : η + Y ^ 2 ≤ 2 * t := by linarith
      calc Cs' * (η + Y ^ 2) ≤ Cs' * (2 * t) := mul_le_mul_of_nonneg_left this hCs'0
        _ ≤ 1 / 2 := by linarith
    have he' : ‖e‖ ≤ Cs' * (η ^ 2 + (W : ℝ) ^ (-(d : ℝ) + τ) * η + Y ^ 3) := he.trans (by
      rw [hYdef, mul_pow]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hqb : ‖qform W k (diffEff P Sg M W L z)‖ ≤ Cq * Y ^ 2 := by
      rw [hq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      calc r * ‖Qs‖ + r * ‖Qg‖ ≤ 1 * (A₂ * Y ^ 2) + 1 * (B₂ * Y ^ 2) := by
            gcongr
        _ = Cq * Y ^ 2 := by rw [hCq]; ring
    have hSh0 : Sh ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg, norm_one] at h1
      have : A₂ * Y ^ 2 ≤ A₂ * t := mul_le_mul_of_nonneg_left (hY2le.trans hYt) hA₂0
      linarith
    have hAh0 : Ah ≠ 0 := by
      rw [hAh]; exact mul_ne_zero (by exact_mod_cast ha0.ne') hSh0
    have hu0 : 1 + u ≠ 0 := by
      intro h
      have : u = -1 := by linear_combination h
      rw [this, norm_neg, norm_one] at hu2
      linarith
    obtain ⟨hden, heq⟩ := Main_frac Ah Xh (symbol (thetaM S (1 + σ) z) k)
      (symbol (resM S (1 + σ) z) k) u e (qform W k (diffEff P Sg M W L z)) (mAbs2 z)
      (symbol Gc k) r η hr0.ne' hAh0 hu0 hDne hΘh hRh hΘeq
    refine ⟨symbol Gc k, Ah * ((η : ℂ) + qform W k (diffEff P Sg M W L z) + e) / (1 + u) - η -
      qform W k (diffEff P Sg M W L z), ∑ x, zchar k x * ((expG2 d P W L z 0 x : ℂ) -
      (resM S (1 + σ) z * (mAbs2 z • 1 + Gc)) 0 x), ?_, ?_, ?_, hden, ?_⟩
    · exact he₁.trans (mul_le_mul_of_nonneg_right hC₁le (by positivity))
    · refine (Main_e2_bound Ah u e _ η Y ((W : ℝ) ^ (-(d : ℝ) + τ)) Ca Cs' Cq Cs' hη0.le hηle
        hY0 hY1 (by positivity) hCa0 hCs'0 hCq0 hCs'0 hAh1 hAhb hu' hu2 hqb he').trans ?_
      rw [hYdef, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    · exact (Main_e3 hd4 W M hW1 hLW C₂ hC₂0 _ (fun x => (hRem 0 x).2) k).trans
        (mul_le_mul_of_nonneg_right hC₂le (by positivity))
    · rw [hsplit _ (resM S (1 + σ) z * (mAbs2 z • 1 + Gc)), symbol_mul _ _ hTR hTV, hsymV, heq]

end Cor17

/-! ## [I, Theorem 1.5], [I, Corollary 1.6] and [I, Corollary 1.7] -/

/-- **[I, Theorem 1.5] + [I, Corollary 1.6] + [I, Corollary 1.7]** (joint), from the local law
[I, Theorem 1.4] and, for every `d ≥ 8` and profile `P`, a construction `Strat` with one family
of self-energies with `H(n)` for every `n ≥ 2` ([II, Theorem 3.7, Corollary 3.8, Lemma 3.9]).
The self-energies `Σ_l` are those of the family; for the order `M` the local correction `𝒢^{(M)}`
is that of [I, (8.16)] for the `n`-th order `T`-equation with error order `n + 2`,
`n = max(M + 2, 4)`. -/
theorem quantumDiffusion_of : quantumDiffusion_ofStmt := by
  intro hLL hJ d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε
  obtain ⟨Strat, hJS⟩ := hJ d hd P
  obtain ⟨Sig, hH, Sg, hSg⟩ := selfEnergyFamily d P Strat hJS
  have hSE : ∀ l, 4 ≤ l → Even l → IsSelfEnergy d (smatVar P) Sig l :=
    fun l hl he => (hH l (by omega)).1 l hl le_rfl he
  refine ⟨Sg, ⟨Sig, hSg⟩, fun M => ?_⟩
  set n := max (M + 2) 4 with hndef
  have hMn : M + 2 ≤ n := le_max_left _ _
  have hn : 4 ≤ n := le_max_right _ _
  obtain ⟨hSEn, 𝒬f, 𝒯f, hF⟩ := hH n (by omega)
  have hS : (𝒬f n (n + 2)).IsTEqStruct Sig n (n + 2) :=
    (hF.1 n (n + 2) (by omega) le_rfl (by omega)).1
  have hSN : (𝒬f n (n + 2)).SigN = Sig n := hF.2.1 n (n + 2) (by omega) le_rfl (by omega)
  have hNR : ∀ g ∈ (𝒬f n (n + 2)).R ++ (𝒬f n (n + 2)).A ++ (𝒬f n (n + 2)).Q ++
      (𝒬f n (n + 2)).Err, noRootLabel g.2 :=
    fun g hg => (hS.2.2.2.2.2.1 g hg).label_ne_root
  have hP2 := Main_part2 hLL hd P hc₀ hc₁ hκ hε Sig hSE Sg hSg M hMn hn hS hNR hSN hSEn
  refine ⟨fun W L _ z => corrMat d P Sig (𝒬f n (n + 2)) W L z, ⟨?_, ?_⟩,
    Main_cor17 hLL hd P hc₀ hc₁ hκ hε Sig hSE Sg hSg M hn hS hNR hSEn hP2⟩
  · intro τ hτ
    obtain ⟨L₁, h1⟩ := thetaMBounds d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig hSE Sg hSg M M le_rfl τ hτ
    obtain ⟨L₂, h2⟩ := localCorr hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n (n + 2) _ hn le_rfl hS
      hNR hSEn τ hτ
    refine ⟨max L₁ L₂, fun W L _ hL hadm z hz => ?_⟩
    obtain ⟨hU, hΘ, h126, h127, -, -⟩ := h1 W L ((le_max_left _ _).trans hL) hadm z hz
    exact ⟨hU, hΘ, h126, h127, h2 W L ((le_max_right _ _).trans hL) hadm z hz⟩
  · obtain ⟨C, -, L₀, h⟩ := hP2
    exact ⟨C, L₀, h⟩

end RBM8D
