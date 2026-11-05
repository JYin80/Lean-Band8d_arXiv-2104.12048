import RBM8D.SelfEnergy.Step
import RBM8D.SelfEnergy.Lem512Zero
import RBM8D.SelfEnergy.MainCancelId
import Batteries.Tactic.OpenPrivate

/-!
# [I, Lemma 5.11]: the cancellation of the row sum of `Σ_n` at the sizes `L_n`

`G13.mainCancel`: under `H(n − 1)`, `n`-th order `T`-equations with one `Σ_n = E` for every error
order `D > n`, and the local law `localLawTExpStmt'`, for `0 < c₀ < d/4` and with `c = c₀/2`,
`ε₀ = c₀/8`, for `0 < ε ≤ ε₀` and `|E'| < 2`, along the sizes `L_n` of [I, (5.39)] and at
`z_n = E' + i W^{2+ε}/L_n²`, `|Σ_x Σ_n(0, x)(z_n)| ≤ W^{-(n-2)d/2 - c}` ([I, (5.40)]).

The proof at an even order `n`:

* [I, (5.44)] at `𝔟₁ = 𝔟₂`, in expectation and summed over `𝔞, 𝔟`, on the data record with
  `Σ_n = E`; the matrix `Σ̃^{(n)}` is deterministic, and [I, (5.45)], (5.46), (5.49) and
  `E Q = 0` evaluate the terms;
* the graphs of `R`, `A` and of `Err` without internal atoms are bounded by [I, Lemma 5.12] under
  the local law at order `n − 1`; a graph of `Err` with internal atoms is bounded by the label
  removal and [II, Claim 8.6], in the weak form `W^δ L^{2d+2} W^{−(n_𝔟−2)d/4}`, which is
  absorbed by the choice of the error order `D`;
* `|E G₀₀ − m| ≤ W^{−d/2+δ}` from the local law at `(0, 0)`, and the lower orders by [I, (1.27)];
* the identity is solved for the row sum as in [I, (5.52)–(5.53)] (`MainCancel.solve`), with
  `Im m(E' + iη) ≥ (1 − E'²/4)/2` for `η ≤ 1` (`MainCancel.msc_im_ge`).

At an odd order `Σ_n = 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

open private Moment_ev_adm Moment_tendsto Moment_W_le_L Moment_bB_le_one Moment_im_inv
  Moment_coeff_le Moment_cvar_le Moment_modelAdm Moment_ev_list from RBM8D.LocalLaw.Moment
open private LabelRemoval_card_coord LabelRemoval_coordVar_le from RBM8D.LocalLaw.LabelRemoval
open private Entrywise_base Entrywise_Phi Entrywise_Phi_zero Entrywise_Phi_nonneg
  from RBM8D.LocalLaw.Entrywise
open private Lem512Zero_comp_le Lem512Zero_valR_le Lem512Zero_integral_le Lem512Zero_h77
  Lem512Zero_h78 from RBM8D.SelfEnergy.Lem512Zero

/-! ## Integrability of the graphs of `Err` -/

/-- The values of the graphs with the kinds of `Err` (the kinds of [II, Def 3.2] and the weights
`W_d` of [II, (4.21)]) on the data record of the model have polynomial growth. -/
private theorem MainCancel_polyMeas_valR (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2)
    (W L : ℕ) [NeZero L] (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y) {k n N : ℕ} (Γ : Graph k n) (hΓ : Γ.TKindsErr N)
    (e : Fin k → Zd d L) :
    PolyMeas (Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e) := by
  have hL := pqLaws_Pexp_poly (Smat P.ψ W L) hS hnn
  have hGm := QTerm_Gm_empty d P Sig W L z
  have hgreen : ∀ x y, PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z x y :=
    fun x y => polyMeas_of_testFn _ (testFn_green z hz.ne' x y)
  have hconst : ∀ (f : Sample (Zd d L) → ℂ) (a : ℂ), (∀ ω, f ω = a) → PolyMeas f := by
    intro f a h
    have : f = fun _ => a := funext h
    rw [this]; exact hL.adm_const a
  have hmul : ∀ f g : Sample (Zd d L) → ℂ, PolyMeas f → PolyMeas g →
      PolyMeas fun ω => f ω * g ω := fun f g hf hg => hL.adm_mul _ _ hf hg
  have hadd : ∀ f g : Sample (Zd d L) → ℂ, PolyMeas f → PolyMeas g →
      PolyMeas fun ω => f ω + g ω := fun f g hf hg => hL.adm_add _ _ hf hg
  have hpow : ∀ f : Sample (Zd d L) → ℂ, PolyMeas f → ∀ j : ℕ, PolyMeas fun ω => f ω ^ j := by
    intro f hf j
    induction j with
    | zero => simpa using hL.adm_const 1
    | succ j ih => simpa [pow_succ] using hmul _ _ ih hf
  have hsumr : ∀ F : ℕ → Sample (Zd d L) → ℂ, (∀ j, PolyMeas (F j)) → ∀ r : ℕ,
      PolyMeas fun ω => ∑ j ∈ Finset.range r, F j ω := by
    intro F hF r
    induction r with
    | zero => simpa using hL.adm_const 0
    | succ r ih => simpa [Finset.sum_range_succ] using hadd _ _ ih (hF r)
  have hcomp : ∀ (σ : Atom k n → Zd d L), ∀ c ∈ Γ.comps,
      PolyMeas fun ω => Comp.val (rbmData d P Sig W L z ω) σ c := by
    intro σ c hc
    have hc' := List.all_eq_true.1 hΓ c hc
    rcases c with ⟨κ, x, y, mi, lab⟩
    have hmi : mi = [] := by
      simp only [Bool.or_eq_true, Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at hc'
      rcases hc' with h | h
      · exact h.1
      · exact h.1
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
    | wD ch D' =>
      have hq : PolyMeas fun ω : Sample (Zd d L) =>
          -(green (hmat ω) z (σ x) (σ x) - msc z) / msc z := by
        have := hmul _ _ (hadd _ _ (hgreen (σ x) (σ x)) (hL.adm_const (-msc z)))
          (hL.adm_const (-(msc z)⁻¹))
        refine (congrArg PolyMeas ?_).mp this
        funext ω
        simp only [div_eq_mul_inv]
        ring
      have h1 : PolyMeas fun ω : Sample (Zd d L) => (green (hmat ω) z (σ x) (σ x))⁻¹ -
          (msc z)⁻¹ * ∑ j ∈ Finset.range (D' + 1),
            (-(green (hmat ω) z (σ x) (σ x) - msc z) / msc z) ^ j := by
        have := hadd _ _ (polyMeas_inv_green_diag z hz (σ x))
          (hmul _ _ (hL.adm_const (-(msc z)⁻¹))
            (hsumr _ (fun j => hpow _ hq j) (D' + 1)))
        refine (congrArg PolyMeas ?_).mp this
        funext ω
        simp only [sub_eq_add_neg, neg_mul]
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

/-- The value of a graph with the kinds of `Err` on the data record of the model is integrable
for the law of [I, Assumption 1.1] (a variance kernel `S`, `Im z > 0`). -/
private theorem MainCancel_valR_integrable_err {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2)
    (W L : ℕ) [NeZero L] (z : ℂ) (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) {k n N : ℕ}
    (Γ : Graph k n) (hΓ : Γ.TKindsErr N) (e : Fin k → Zd d L) :
    Integrable (Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e)
      (gaussLaw (Smat P.ψ W L)) :=
  have hs : (Smat P.ψ W L).IsSymm := Matrix.IsSymm.ext fun i j => hS.symm j i
  integrable_of_polyMeas _ _ (MainCancel_polyMeas_valR d P Sig W L z hz hs hS.nonneg Γ hΓ e)

/-! ## The graphs of `Err` with internal atoms -/

/-- `W ≤ L` on `adm(c₀, c₁)` with `c₀ > 0`. -/
private theorem MainCancel_W_le_L {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) {W L : ℕ} (hL : L ≠ 0)
    (hp : (W, L) ∈ adm c₀ c₁) : (W : ℝ) ≤ L := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hL
  calc (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := hp.2
    _ ≤ (L : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = L := Real.rpow_one _

/-- A priori bound of a graph with the kinds of `Err` and `nI` internal atoms: eventually along
the filter, `|𝒢_{𝔞,𝔟𝔟}| ≤ W^K (1 + ‖ω‖)^q` at every `z ∈ 𝐃(κ, ε)` and every sample. -/
private theorem MainCancel_apriori (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ)
    (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig N) {nI : ℕ}
    (g : Graph 3 nI) (hK : g.TKindsErr N) :
    ∃ (K : ℝ) (q : ℕ), 0 ≤ K ∧ ∀ᶠ p in llFilter d N c₀ c₁ c₀T,
      ∀ (u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2}) (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
        ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 u.1) ![a, b, b] ω‖ ≤
          (p.1.1 : ℝ) ^ K * (1 + ‖ω‖) ^ q := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := Lem512Zero_comp_le d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE g hK
  set c := g.comps.length with hcdef
  set Cst : ℝ := 2 ^ (2 * c) * (1 + LabelRemoval.gaussMoment (2 * c)) with hCst
  have hg : 0 ≤ LabelRemoval.gaussMoment (2 * c) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hCst0 : 0 ≤ Cst := by positivity
  set K₁ : ℝ := max 4 (4 / Real.sqrt (2 * κ)) with hK₁
  set Cg : ℝ := ∑ s ∈ g.coeff.support, ‖g.coeff.coeff s‖ * ∏ i ∈ s.support, K₁ ^ s i with hCg
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  set E₁ : ℝ := K₀ * c + 2 + 2 * d / c₁ with hE₁
  refine ⟨nI * (d / c₁) + (1 + K₀ * c + E₁ * c), 2 * c * (c + 1), by positivity, ?_⟩
  filter_upwards [hK₀, Moment_ev_adm d N c₀ c₁ c₀T, (Moment_tendsto d N c₀ c₁ c₀T).eventually
    (eventually_ge_atTop (max 4 (max W₂ (max Cg (3 * Cst + 1)))))] with p hcomp hp hW u a b ω
  change max 4 (max W₂ (max Cg (3 * Cst + 1))) ≤ (p.1.1 : ℝ) at hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW4 : 4 ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hW₂ : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hCgW : Cg ≤ W :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  have hCstW : 3 * Cst + 1 ≤ W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  have hS1 : ∀ c', coordVar (Smat P.ψ p.1.1 p.1.2) c' ≤ 1 :=
    LabelRemoval_coordVar_le _ (hds p.1.1 p.1.2 hp hW₂)
  obtain ⟨him, -⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 u.1 u.2
  have hA1 : 1 ≤ W ^ K₀ := Real.one_le_rpow hW1 hK₀0
  have h := Lem512Zero_valR_le g (Smat P.ψ p.1.1 p.1.2) hS1
    (rbmData d P Sig p.1.1 p.1.2 u.1) (W ^ K₀) hA1 (fun _ => rfl)
    (fun ω' σ c' hc' => hcomp u ω' σ c' hc') ![a, b, b] ω
  refine h.trans ?_
  have hcoef : ‖g.coeff.eval (rbmData d P Sig p.1.1 p.1.2 u.1 0).m‖ ≤ W :=
    (Moment_coeff_le g.coeff _ K₁ fun i => Moment_cvar_le hκ u.1 u.2 him i).trans hCgW
  have hcard : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) :=
    card_Zd_le_adm d c₀ c₁ hc₁ p hp
  have hcardC : (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * W ^ (2 * (d : ℝ) / c₁) := by
    refine LabelRemoval_card_coord.trans ?_
    have h2 : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
      calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
        _ = W ^ (2 * (d : ℝ) / c₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    linarith
  have hX1 : 1 ≤ W ^ (2 * (d : ℝ) / c₁) := Real.one_le_rpow hW1 (by positivity)
  have hB : 1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ W ^ (1 + 2 * (d : ℝ) / c₁) := by
    rw [Real.rpow_add hW0, Real.rpow_one]
    have e1 : Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * Cst * W ^ (2 * (d : ℝ) / c₁) := by
      nlinarith
    nlinarith
  have hAc : (W ^ K₀) ^ c = W ^ (K₀ * c) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hY : 2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ)) ≤ W ^ E₁ := by
    rw [hAc, hE₁]
    have e2 : W ^ (K₀ * c + 2 + 2 * d / c₁) = W ^ (K₀ * c) * W * W ^ (1 + 2 * (d : ℝ) / c₁) := by
      rw [(show K₀ * c + 2 + 2 * d / c₁ = K₀ * c + 1 + (1 + 2 * d / c₁) by ring),
        Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]
    rw [e2]
    have : 0 ≤ W ^ (K₀ * c) := Real.rpow_nonneg hW0.le _
    have h2W : 2 * W ^ (K₀ * c) ≤ W ^ (K₀ * c) * W := by nlinarith
    exact mul_le_mul h2W hB (by positivity) (by positivity)
  have hYc : (2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ))) ^ c ≤
      W ^ (E₁ * c) :=
    (pow_le_pow_left₀ (by positivity) hY c).trans
      (le_of_eq (by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]))
  have hcardn : (Fintype.card (Zd d p.1.2) : ℝ) ^ nI ≤ W ^ (nI * ((d : ℝ) / c₁)) := by
    calc (Fintype.card (Zd d p.1.2) : ℝ) ^ nI ≤ (W ^ ((d : ℝ) / c₁)) ^ nI :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hcard nI
      _ = W ^ (nI * ((d : ℝ) / c₁)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, mul_comm]
  have hR1 : (0 : ℝ) ≤ (1 + ‖ω‖) ^ (2 * c * (c + 1)) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ hR1
  rw [← hCst, Real.rpow_add hW0]
  refine mul_le_mul hcardn ?_ (by positivity) (by positivity)
  calc ‖g.coeff.eval (rbmData d P Sig p.1.1 p.1.2 u.1 0).m‖ * (W ^ K₀) ^ c *
        (2 * (W ^ K₀) ^ c * (1 + Cst * (Fintype.card (Coord (Zd d p.1.2)) : ℝ))) ^ c
      ≤ W * W ^ (K₀ * c) * W ^ (E₁ * c) := by
        rw [hAc] at hYc ⊢
        gcongr
  _ = W ^ (1 + K₀ * c + E₁ * c) := by
        rw [Real.rpow_add hW0, Real.rpow_add hW0, Real.rpow_one]

set_option maxHeartbeats 4000000 in
-- the final count instantiates several eventual statements at once
/-- **[I, Lemma 5.12], (5.43) for a graph of `Err` with internal atoms**, in a weak form: with the
hypotheses of `Lem512Zero.errRowStmt` on `d`, `P`, the constants, `Σ`, the local law, `F` and `z`,
for a graph `𝒢` with `nI ≠ 0` internal atoms, normal regular, with the kinds of `Err`, with
[II, Def 3.2 (9)], doubly connected, with only diffusive components at `⊗`, dotted edges forming
a forest, rooted at the external atoms unless it is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`, and
with `n_𝔟 ≥ 2`: for every `δ > 0`, eventually along `F`,
`Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^{2d+2} W^{−(n_𝔟−2)d/4}`. The weights `W_d` are replaced by
`d + 1` light weights, the labels are removed by the resampled row (`labelRemovalErr`), and the
label-free graphs are bounded by [II, Claim 8.6] (`graphSum''`). -/
private theorem MainCancel_errRow (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (hc₀T : 0 < c₀T)
    (N : ℕ) (Sig : ℕ → Expansion 2) (hSE : SelfEnergiesUpTo d (smatVar P) Sig N)
    (hLL : StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2))
    (F : Filter SizeL) (hF : F ≤ llFilter d N c₀ c₁ c₀T) (z : SizeL → ℂ)
    (hz : ∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2)
    {nI : ℕ} (C : ℕ) (g : Graph 3 nI) (hnI : nI ≠ 0) (hN : g.Normal C) (hK : g.TKindsErr N)
    (hAE : g.AtExternals) (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive)
    (hDA : g.DotsAcyclic) (hR : ¬ g.DiagRecoll → g.RootedAtExt) (h2 : 2 ≤ g.diagOrd)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ p in F, ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
      ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
      (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ (2 * d + 2) *
        (p.1.1 : ℝ) ^ (-(((g.diagOrd : ℝ) - 2) * d / 4)) := by
  classical
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set nb : ℝ := (g.diagOrd : ℝ) with hnb
  have hnb2 : (2 : ℝ) ≤ nb := by rw [hnb]; exact_mod_cast h2
  set e : ℝ := (nb - 2) * d / 4 with he
  have he0 : 0 ≤ e := by rw [he]; have : 0 ≤ nb - 2 := by linarith
                         positivity
  -- the loss `ε₀` of the label removal
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ, ε₀ = min (c₀T / ((N : ℝ) + 1)) ((d : ℝ) / 40) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; exact lt_min (by positivity) (by positivity)
  have hε₀2 : ε₀ ≤ c₀T / ((N : ℝ) + 1) := by rw [hε₀def]; exact min_le_left _ _
  have hε₀3 : ε₀ ≤ (d : ℝ) / 40 := by rw [hε₀def]; exact min_le_right _ _
  have hε₀n : ((N : ℝ) - 1) * ε₀ < c₀T := by
    have : ε₀ * ((N : ℝ) + 1) ≤ c₀T := (le_div_iff₀ hN1).1 hε₀2
    nlinarith
  have hε₀d : ε₀ < (d : ℝ) / 20 := by linarith
  have hrate : -((d : ℝ) / 2) + ε₀ ≤ -((d : ℝ) / 4) := by linarith
  have hτ₀0 : 0 < δ / 8 := by positivity
  -- the light weights and their label-free graphs
  obtain ⟨hNw, hKw, hAEw, hDCw, hTDw, hDAw, hDRw, hRtw, -, hdow⟩ :=
    G11.wDLights_props g N C hK hN hAE hDC hTD hDA
  set g' := g.wDLights with hg'
  have hRw : nI ≠ 0 → ¬ g'.DiagRecoll → g'.RootedAtExt := fun _ h' =>
    hRtw.2 (hR fun h'' => h' (hDRw.2 h''))
  set k := g'.pathElig.card with hk
  have hrow : ∀ S : Finset (Fin g'.comps.length), ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ,
      S ⊆ g'.pathElig → ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ z' ∈ specDom κ ε W L, ∀ (G : Matrix (Zd d L) (Zd d L) ℂ) (Φ' : ℝ), 0 ≤ Φ' →
          weakNorm d L W 1 2 (errAbs G z') ≤ (W : ℝ) ^ (ε₀ + τ') →
          (∀ x y, ‖entryErr G (msc z') x y‖ ≤ (W : ℝ) ^ τ' * (Real.sqrt (bB d L W x y) + Φ')) →
          ∀ a b : Zd d L, (g'.pathRepl S).absVal (gData (Smat P.ψ W L) z' Sig G) ![a, b, b] ≤
            (W : ℝ) ^ (δ / 8) * (W : ℝ) ^ (-e) *
              (((L : ℝ) ^ 2 / (W : ℝ) ^ 2) * (bB d L W a b + Φ' ^ 2)) := by
    intro S
    by_cases hS : S ⊆ g'.pathElig
    · obtain ⟨⟨C', hN'⟩, hK', hAE', hDC', hTD', hDA', -, -, hdr, hR', -, hdord⟩ :=
        labelPaths nI _ N g' hNw hKw hAEw hDCw hTDw hDAw hRw S hS
      obtain ⟨τ', hτ', W₀, hW₀⟩ := graphSum'' d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE nI C'
        (g'.pathRepl S) hN' hK' hAE' hDC' hTD' hDA' ε₀ hε₀.le (by linarith) (δ / 8) hτ₀0
      refine ⟨τ', hτ', max W₀ 1, fun _ W L hL hadm hW z' hz' G Φ' hΦ'0 hwn hent a b => ?_⟩
      have hW1' : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
      have hW0 : (0 : ℝ) < W := by linarith
      obtain ⟨r1, -, r3⟩ := hW₀ W L hadm (le_trans (le_max_left _ _) hW) z' hz' G Φ' hΦ'0 hwn hent
      have hB := (Moment_bB_le_one d L W (by omega) hW1' a b).1
      have hSd : nb ≤ ((g'.pathRepl S).diagOrd : ℝ) := by
        have h1 : g'.diagOrd + (S.card : ℤ) ≤ (g'.pathRepl S).diagOrd := hdord
        have h2' : g.diagOrd ≤ (g'.pathRepl S).diagOrd := by rw [← hdow]; omega
        rw [hnb]; exact_mod_cast h2'
      have hx : (W : ℝ) ^ ((((g'.pathRepl S).diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀)) ≤
          (W : ℝ) ^ (-e) := by
        refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
        rw [he]
        have h0 : 0 ≤ ((g'.pathRepl S).diagOrd : ℝ) - 2 := by linarith
        have : (((g'.pathRepl S).diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + ε₀) ≤
            (((g'.pathRepl S).diagOrd : ℝ) - 2) * (-((d : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hrate h0
        have : (((g'.pathRepl S).diagOrd : ℝ) - 2) * (-((d : ℝ) / 4)) ≤
            (nb - 2) * (-((d : ℝ) / 4)) :=
          mul_le_mul_of_nonpos_right (by linarith) (by linarith)
        linarith
      have hLW : (1 : ℝ) ≤ (L : ℝ) ^ 2 / (W : ℝ) ^ 2 := by
        have hWL := MainCancel_W_le_L hc₀ (NeZero.ne L) hadm
        rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ hW0.le hWL 2
      have hBΦ : bB d L W a b ≤ ((L : ℝ) ^ 2 / (W : ℝ) ^ 2) * (bB d L W a b + Φ' ^ 2) := by
        have : bB d L W a b ≤ bB d L W a b + Φ' ^ 2 := by nlinarith [sq_nonneg Φ']
        calc bB d L W a b ≤ 1 * (bB d L W a b + Φ' ^ 2) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_right hLW (by positivity)
      have hτW : (0 : ℝ) ≤ (W : ℝ) ^ (δ / 8) := Real.rpow_nonneg hW0.le _
      by_cases hdr0 : g'.DiagRecoll
      · have hdS := hdr.2 hdr0
        have h2S : 2 ≤ (g'.pathRepl S).diagOrd := by
          have : (2 : ℝ) ≤ ((g'.pathRepl S).diagOrd : ℝ) := by linarith
          exact_mod_cast this
        refine (r1 hdS h2S a b).trans ?_
        calc (W : ℝ) ^ (δ / 8) * (W : ℝ) ^ ((((g'.pathRepl S).diagOrd : ℝ) - 2) *
              (-((d : ℝ) / 2) + ε₀)) * bB d L W a b
            ≤ (W : ℝ) ^ (δ / 8) * (W : ℝ) ^ (-e) * bB d L W a b := by gcongr
          _ ≤ _ := mul_le_mul_of_nonneg_left hBΦ (by positivity)
      · have hdS : ¬ (g'.pathRepl S).DiagRecoll := fun h => hdr0 (hdr.1 h)
        refine (r3 hnI hdS (hR' hnI hdS) a b).trans ?_
        have h0 : (0 : ℝ) ≤ ((L : ℝ) ^ 2 / (W : ℝ) ^ 2) * (bB d L W a b + Φ' ^ 2) := by
          positivity
        calc (W : ℝ) ^ (δ / 8) * (W : ℝ) ^ ((((g'.pathRepl S).diagOrd : ℝ) - 2) *
              (-((d : ℝ) / 2) + ε₀)) * ((L : ℝ) ^ 2 / (W : ℝ) ^ 2) * (bB d L W a b + Φ' ^ 2)
            = (W : ℝ) ^ (δ / 8) * (W : ℝ) ^ ((((g'.pathRepl S).diagOrd : ℝ) - 2) *
              (-((d : ℝ) / 2) + ε₀)) * (((L : ℝ) ^ 2 / (W : ℝ) ^ 2) *
                (bB d L W a b + Φ' ^ 2)) := by ring
          _ ≤ _ := by gcongr
    · exact ⟨1, one_pos, 0, fun h => absurd h hS⟩
  choose τ'f hτ'f W₀f hW₀f using hrow
  set τ' := Finset.univ.inf' Finset.univ_nonempty τ'f with hτ'def
  set W₀ := Finset.univ.sup' Finset.univ_nonempty W₀f with hW₀def
  have hτ' : 0 < τ' := (Finset.lt_inf'_iff _).2 fun S _ => hτ'f S
  set U : SizeL → Type := fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2} with hU
  set Φ : SizeL → ℝ := fun p => Entrywise_Phi d N c₀T ε₀ 0 p with hΦdef
  set β : ∀ p : SizeL, U p → Zd d p.1.2 → Zd d p.1.2 → ℝ := fun p _ a b =>
    (2 : ℝ) ^ k * ((p.1.1 : ℝ) ^ (δ / 8) * (p.1.1 : ℝ) ^ (-e) *
      (((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) * (bB d p.1.2 p.1.1 a b + Φ p ^ 2))) with hβdef
  have hsz := Moment_tendsto d N c₀ c₁ c₀T
  have hβ : ∀ᶠ p in llFilter d N c₀ c₁ c₀T, ∀ (u : U p) (a b : Zd d p.1.2)
      (G : Matrix (Zd d p.1.2) (Zd d p.1.2) ℂ),
      weakNorm d p.1.2 p.1.1 1 2 (errAbs G u.1) ≤ (p.1.1 : ℝ) ^ (ε₀ + τ') →
      (∀ x y, ‖entryErr G (msc u.1) x y‖ ≤
        (p.1.1 : ℝ) ^ τ' * (Real.sqrt (bB d p.1.2 p.1.1 x y) + Φ p)) →
      ∑ S ∈ g'.pathElig.powerset, (g'.pathRepl S).absVal
          (gData (Smat P.ψ p.1.1 p.1.2) u.1 Sig G) ![a, b, b] ≤ β p u a b := by
    filter_upwards [Moment_ev_adm d N c₀ c₁ c₀T, hsz.eventually (eventually_ge_atTop W₀),
      hsz.eventually (eventually_ge_atTop 1)] with p hp hW hW1p u a b G hwn hent
    change (1 : ℝ) ≤ p.1.1 at hW1p
    have hle : ∀ S ∈ g'.pathElig.powerset, (g'.pathRepl S).absVal
        (gData (Smat P.ψ p.1.1 p.1.2) u.1 Sig G) ![a, b, b] ≤
        (p.1.1 : ℝ) ^ (δ / 8) * (p.1.1 : ℝ) ^ (-e) *
          (((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) * (bB d p.1.2 p.1.1 a b + Φ p ^ 2)) := by
      intro S hS
      have hτS : τ' ≤ τ'f S := Finset.inf'_le _ (Finset.mem_univ S)
      have hWS : W₀f S ≤ W₀ := Finset.le_sup' _ (Finset.mem_univ S)
      refine hW₀f S (Finset.mem_powerset.1 hS) p.1.1 p.1.2 hp (hWS.trans hW) u.1 u.2 G (Φ p)
        (Entrywise_Phi_nonneg _ _ _ _ _ _) ?_ ?_ a b
      · exact hwn.trans (Real.rpow_le_rpow_of_exponent_le hW1p (by linarith))
      · intro x y
        refine (hent x y).trans (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hW1p hτS) ?_)
        have := Entrywise_Phi_nonneg d N c₀T ε₀ 0 p
        positivity
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    push_cast
    exact le_rfl
  -- the hypotheses of the label removal
  have h77 := Lem512Zero_h77 (by omega) P hLL ε₀ hε₀.le
  have h78 := Lem512Zero_h78 (by omega) P hLL ε₀ hε₀.le
  have h81 := Entrywise_base hd P (κ := κ) (ε := ε) (c₀T := c₀T) (ε₀ := ε₀) (n := N) hc₀ hc₁
    (U' := U) (fun _ u => u.1) (fun _ u => u.2) h77
  have hδΦ : 0 < (d : ℝ) / 2 - ε₀ := by linarith
  have hΦ : ∀ᶠ p in llFilter d N c₀ c₁ c₀T, ∀ _u : U p,
      0 ≤ Entrywise_Phi d N c₀T ε₀ 0 p ∧
        Entrywise_Phi d N c₀T ε₀ 0 p ≤ (p.1.1 : ℝ) ^ (-((d : ℝ) / 2 - ε₀)) :=
    Eventually.of_forall fun p _ => ⟨Entrywise_Phi_nonneg _ _ _ _ _ _, by
      rw [Entrywise_Phi_zero]; exact le_of_eq (by congr 1; ring)⟩
  have hD' : 0 < δ / 8 + e + 1 := by linarith
  have hLR := labelRemovalErr d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε hc₀T N Sig ε₀ hε₀ hε₀n hε₀d
    U (fun _ u => u.1) (fun _ u => u.2) h77 h78 (fun p _ => Entrywise_Phi d N c₀T ε₀ 0 p)
    ((d : ℝ) / 2 - ε₀) hδΦ hΦ h81 N nI g hK τ' hτ' β hβ _ hD'
  -- the a priori bound and the exponents of the exceptional event
  obtain ⟨Ka, q, hKa0, hap⟩ :=
    MainCancel_apriori d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE g hK
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈Ka + 2 * d / c₁ + e + 2⌉₊ := ⟨_, rfl⟩
  have hjge : Ka + 2 * d / c₁ + e + 2 ≤ (j : ℝ) := by rw [hj]; exact Nat.le_ceil _
  obtain ⟨Cq, hCq⟩ : ∃ Cq : ℝ, Cq = 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) :=
    ⟨_, rfl⟩
  have hgm : 0 ≤ LabelRemoval.gaussMoment (q + j) :=
    integral_nonneg fun x => pow_nonneg (abs_nonneg x) _
  have hCq0 : 0 ≤ Cq := by rw [hCq]; positivity
  have hDd : 0 < Ka + 2 * q + e + 1 := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  obtain ⟨W₂, hds⟩ := Smat_doublyStochastic_adm d P c₀ c₁ hc₀
  have hszF : Tendsto sizeW F atTop := hsz.mono_left hF
  have hpow : ∀ r : ℝ, 0 < r → ∀ M : ℝ, ∀ᶠ p in F, M ≤ (p.1.1 : ℝ) ^ r := fun r hr M =>
    ((tendsto_rpow_atTop hr).comp hszF).eventually (eventually_ge_atTop M)
  filter_upwards [hz, (hLR (δ / 8) hτ₀0 _ hDd).filter_mono hF, hap.filter_mono hF,
    (Moment_ev_adm d N c₀ c₁ c₀T).filter_mono hF,
    hszF.eventually (eventually_ge_atTop (max 3 (max W₂ (3 * Cq + 1)))),
    hpow (δ / 8) hτ₀0 ((2 : ℝ) ^ (k + 1) + 1)] with
    p hzp hbad happ hadm hW hWk
  change max 3 (max W₂ (3 * Cq + 1)) ≤ (p.1.1 : ℝ) at hW
  have hW3 : (3 : ℝ) ≤ p.1.1 := (le_max_left _ _).trans hW
  have hW1n : 1 ≤ p.1.1 := by
    have h : (1 : ℝ) ≤ (p.1.1 : ℝ) := by linarith
    exact_mod_cast h
  have hS1 : ∀ c', coordVar (Smat P.ψ p.1.1 p.1.2) c' ≤ 1 :=
    LabelRemoval_coordVar_le _ (hds p.1.1 p.1.2 hadm ((le_max_left _ _).trans
      ((le_max_right _ _).trans hW)))
  have hCqW : 3 * Cq + 1 ≤ (p.1.1 : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by rw [hLdef]; exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  have hWL : W ≤ L := MainCancel_W_le_L hc₀ p.2 hadm
  have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
  set u₀ : U p := ⟨z p, hzp⟩ with hu₀
  have hB01 : ∀ a b : Zd d p.1.2, 0 ≤ bB d p.1.2 p.1.1 a b ∧ bB d p.1.2 p.1.1 a b ≤ 1 :=
    fun a b => Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b
  have hΦ01 : 0 ≤ Φ p ∧ Φ p ≤ 1 := by
    refine ⟨Entrywise_Phi_nonneg _ _ _ _ _ _, ?_⟩
    simp only [hΦdef, Entrywise_Phi_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hβ0 : ∀ a b, 0 ≤ β p u₀ a b := fun a b => by
    simp only [hβdef]
    have := (hB01 a b).1
    have := hΦ01.1
    positivity
  have hβle : ∀ a b, β p u₀ a b ≤ (2 : ℝ) ^ (k + 1) * (W ^ (δ / 8) * W ^ (-e) * L ^ 2) := by
    intro a b
    simp only [hβdef]
    have hLW2 : L ^ 2 / W ^ 2 ≤ L ^ 2 := div_le_self (by positivity) (one_le_pow₀ hW1)
    have hBΦ : bB d p.1.2 p.1.1 a b + Φ p ^ 2 ≤ 2 := by
      have := (hB01 a b).2
      have : Φ p ^ 2 ≤ 1 := pow_le_one₀ hΦ01.1 hΦ01.2
      linarith
    have h0 : 0 ≤ W ^ (δ / 8) * W ^ (-e) := by positivity
    calc (2 : ℝ) ^ k * (W ^ (δ / 8) * W ^ (-e) * (L ^ 2 / W ^ 2 * (bB d p.1.2 p.1.1 a b +
          Φ p ^ 2)))
        ≤ (2 : ℝ) ^ k * (W ^ (δ / 8) * W ^ (-e) * (L ^ 2 * 2)) := by
          gcongr
          · have := (hB01 a b).1; have := hΦ01.1; positivity
      _ = _ := by rw [pow_succ]; ring
  -- the expectation of one entry
  set R₂ : ℝ := W ^ (δ / 8) * W ^ (-(δ / 8 + e + 1)) +
    W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + e + 1)) +
    W ^ Ka * ((1 + W) ^ j)⁻¹ *
      (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
        Fintype.card (Coord (Zd d p.1.2))) with hR₂
  have hent : ∀ a b : Zd d p.1.2,
      ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤ W ^ (δ / 8) * β p u₀ a b + R₂ := by
    intro a b
    have h := Lem512Zero_integral_le (Smat P.ψ p.1.1 p.1.2) hS1
      (fun ω => ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖)
      {ω | ∃ v : U p × Zd d p.1.2 × Zd d p.1.2,
        sizeW p ^ (δ / 8) * (β p v.1 v.2.1 v.2.2 + sizeW p ^ (-(δ / 8 + e + 1))) <
        ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 v.1.1)
          ![v.2.1, v.2.2, v.2.2] ω‖}
      (W ^ (δ / 8) * (β p u₀ a b + W ^ (-(δ / 8 + e + 1)))) (W ^ Ka) W
      (W ^ (-(Ka + 2 * q + e + 1))) q j
      (mul_nonneg (by positivity) (add_nonneg (hβ0 a b) (by positivity))) (by positivity)
      hW0.le (by positivity) hbad (fun ω => norm_nonneg _)
      (fun ω hω => by
        by_contra hcon
        exact hω ⟨(u₀, a, b), lt_of_not_ge hcon⟩)
      (fun ω => happ u₀ a b ω)
    refine h.trans (le_of_eq ?_)
    rw [hR₂]
    ring
  -- the small terms
  have hR₂le : R₂ ≤ W ^ (-e) := by
    set Y : ℝ := e with hY
    have t1 : W ^ (δ / 8) * W ^ (-(δ / 8 + e + 1)) = W ^ (-(Y + 1)) := by
      rw [← Real.rpow_add hW0, hY]; congr 1; ring
    have h1W : 1 + W ≤ W ^ 2 := by nlinarith
    have t2 : W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + e + 1)) ≤ W ^ (-(Y + 1)) := by
      have : (1 + W) ^ q ≤ W ^ ((2 * q : ℕ) : ℝ) := by
        rw [Real.rpow_natCast, pow_mul]
        exact pow_le_pow_left₀ (by linarith) h1W q
      calc W ^ Ka * (1 + W) ^ q * W ^ (-(Ka + 2 * q + e + 1))
          ≤ W ^ Ka * W ^ ((2 * q : ℕ) : ℝ) * W ^ (-(Ka + 2 * q + e + 1)) := by gcongr
        _ = W ^ (-(Y + 1)) := by
            rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, hY]; congr 1; push_cast; ring
    have hcard : (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ 3 * W ^ (2 * (d : ℝ) / c₁) := by
      refine LabelRemoval_card_coord.trans ?_
      have h0 : (Fintype.card (Zd d p.1.2) : ℝ) ≤ W ^ ((d : ℝ) / c₁) :=
        card_Zd_le_adm d c₀ c₁ hc₁ p hadm
      have h2 : (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ W ^ (2 * (d : ℝ) / c₁) := by
        calc (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) h0 2
          _ = W ^ (2 * (d : ℝ) / c₁) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      linarith
    have hX1 : 1 ≤ W ^ (2 * (d : ℝ) / c₁) := Real.one_le_rpow hW1 (by positivity)
    have hMq : 1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
        (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤ W ^ (2 * (d : ℝ) / c₁ + 1) := by
      rw [Real.rpow_add hW0, Real.rpow_one, ← hCq]
      have e1 : Cq * (Fintype.card (Coord (Zd d p.1.2)) : ℝ) ≤
          3 * Cq * W ^ (2 * (d : ℝ) / c₁) := by nlinarith
      nlinarith
    have t3 : W ^ Ka * ((1 + W) ^ j)⁻¹ *
        (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
          Fintype.card (Coord (Zd d p.1.2))) ≤ W ^ (-(Y + 1)) := by
      have hinv : ((1 + W) ^ j)⁻¹ ≤ W ^ (-(j : ℝ)) := by
        rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hW0.le (by linarith) j)
      calc W ^ Ka * ((1 + W) ^ j)⁻¹ *
            (1 + 2 ^ (q + j) * (1 + LabelRemoval.gaussMoment (q + j)) *
              Fintype.card (Coord (Zd d p.1.2)))
          ≤ W ^ Ka * W ^ (-(j : ℝ)) * W ^ (2 * (d : ℝ) / c₁ + 1) := by gcongr
        _ = W ^ (Ka - j + (2 * (d : ℝ) / c₁ + 1)) := by
            rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
        _ ≤ W ^ (-(Y + 1)) := Real.rpow_le_rpow_of_exponent_le hW1 (by rw [hY]; linarith)
    have hsum3 : 3 * W ^ (-(Y + 1)) ≤ W ^ (-Y) := by
      have e' : W ^ (-Y) = W ^ (-(Y + 1)) * W := by
        rw [← Real.rpow_add_one hW0.ne']; congr 1; ring
      rw [e']
      have : 0 ≤ W ^ (-(Y + 1)) := Real.rpow_nonneg hW0.le _
      nlinarith
    rw [hR₂]
    linarith
  -- one entry, then the sum
  have hent' : ∀ a b : Zd d p.1.2,
      ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤ W ^ δ * L ^ 2 * W ^ (-e) := by
    intro a b
    refine (hent a b).trans ?_
    have hWe : 0 ≤ W ^ (-e) := by positivity
    have hk1 : (2 : ℝ) ^ (k + 1) + 1 ≤ W ^ (δ / 8) := hWk
    have h8 : W ^ (δ / 8) * W ^ (δ / 8) * W ^ (δ / 8) ≤ W ^ δ := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    have h88 : 1 ≤ W ^ (δ / 8) := Real.one_le_rpow hW1 hτ₀0.le
    have hβ' := hβle a b
    calc W ^ (δ / 8) * β p u₀ a b + R₂
        ≤ W ^ (δ / 8) * ((2 : ℝ) ^ (k + 1) * (W ^ (δ / 8) * W ^ (-e) * L ^ 2)) +
            W ^ (-e) := by gcongr
      _ ≤ W ^ (δ / 8) * ((2 : ℝ) ^ (k + 1) * (W ^ (δ / 8) * W ^ (-e) * L ^ 2)) +
            W ^ (δ / 8) * (1 * (W ^ (δ / 8) * W ^ (-e) * L ^ 2)) := by
          have : W ^ (-e) ≤ W ^ (δ / 8) * (1 * (W ^ (δ / 8) * W ^ (-e) * L ^ 2)) := by
            have h1 : W ^ (-e) ≤ W ^ (-e) * L ^ 2 := le_mul_of_one_le_right hWe hL2
            have h2 : W ^ (-e) * L ^ 2 ≤ W ^ (δ / 8) * (W ^ (δ / 8) * (W ^ (-e) * L ^ 2)) := by
              have h3 : 0 ≤ W ^ (-e) * L ^ 2 := by positivity
              have h4 : W ^ (-e) * L ^ 2 ≤ W ^ (δ / 8) * (W ^ (-e) * L ^ 2) :=
                le_mul_of_one_le_left h3 h88
              have h5 : W ^ (δ / 8) * (W ^ (-e) * L ^ 2) ≤
                  W ^ (δ / 8) * (W ^ (δ / 8) * (W ^ (-e) * L ^ 2)) :=
                le_mul_of_one_le_left (by positivity) h88
              linarith
            calc W ^ (-e) ≤ W ^ (δ / 8) * (W ^ (δ / 8) * (W ^ (-e) * L ^ 2)) := h1.trans h2
              _ = _ := by ring
          linarith
      _ = ((2 : ℝ) ^ (k + 1) + 1) * (W ^ (δ / 8) * W ^ (δ / 8)) * (L ^ 2 * W ^ (-e)) := by ring
      _ ≤ W ^ (δ / 8) * (W ^ (δ / 8) * W ^ (δ / 8)) * (L ^ 2 * W ^ (-e)) := by gcongr
      _ ≤ W ^ δ * (L ^ 2 * W ^ (-e)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← mul_assoc]; exact h8
      _ = _ := by ring
  have hcard : (Fintype.card (Zd d p.1.2) : ℝ) = L ^ d := by rw [card_Zd]; push_cast; rfl
  calc ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
        ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
          ![a, b, b] ω‖ ∂(rbmLaw d P p)
      ≤ ∑ _a : Zd d p.1.2, ∑ _b : Zd d p.1.2, W ^ δ * L ^ 2 * W ^ (-e) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hent' a b
    _ = W ^ δ * L ^ (2 * d + 2) * W ^ (-e) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring

/-! ## The semicircle law and the solving step of [I, (5.52)–(5.53)] -/

/-- In the bulk the imaginary part of `m(z)` is bounded below uniformly in `0 < η ≤ 1`:
`Im m(E + iη) ≥ (1 − E²/4)/2`. From the real part of `m (m + z) = −1`,
`(Re m + E/2)² + 1 − E²/4 = (Im m)² + η Im m ≤ 2 Im m`. -/
theorem MainCancel.msc_im_ge {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    (1 - z.re ^ 2 / 4) / 2 ≤ (msc z).im := by
  have h := congrArg Complex.re (msc_mul z)
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.one_re] at h
  have him := msc_im_pos hz
  have hlt := norm_msc_lt_one hz
  have him1 : (msc z).im ≤ 1 := (Complex.im_le_norm _).trans hlt.le
  nlinarith [sq_nonneg ((msc z).re + z.re / 2), mul_le_mul_of_nonneg_left hz1 him.le]

/-- **The solving step of [I, (5.52)–(5.53)]**: if
`N |m|² Im g/η = N (Im m/η) m ḡ + ρ + N (Im m/η)(|m|² Im g/η) K` with `N, η > 0`, `|m| ≤ 1`,
`Im m ≥ q/2 > 0` and `|g − m| ≤ q/4`, then `|K| ≤ (32/q⁴)(2η|g − m| + η²|ρ|/N)`. At `g = m` the
first two terms cancel, `|m|² Im m/η = (Im m/η) m m̄`. -/
theorem MainCancel.solve (m g K ρ : ℂ) (η N q : ℝ) (hη : 0 < η) (hN : 0 < N) (hq : 0 < q)
    (hm1 : ‖m‖ ≤ 1) (hmq : q / 2 ≤ m.im) (hδ : ‖g - m‖ ≤ q / 4)
    (hid : (N : ℂ) * ((‖m‖ ^ 2 * g.im / η : ℝ) : ℂ) =
      (N : ℂ) * (((m.im / η : ℝ) : ℂ) * m * star g) + ρ +
        (N : ℂ) * (((m.im / η : ℝ) : ℂ) * ((‖m‖ ^ 2 * g.im / η : ℝ) : ℂ) * K)) :
    ‖K‖ ≤ 32 / q ^ 4 * (2 * η * ‖g - m‖ + η ^ 2 * ‖ρ‖ / N) := by
  set μ : ℝ := m.im / η with hμ
  set t : ℝ := ‖m‖ ^ 2 * g.im / η with ht
  have hmim1 : m.im ≤ 1 := (Complex.im_le_norm m).trans hm1
  have hmnorm : q / 2 ≤ ‖m‖ := hmq.trans (Complex.im_le_norm m)
  have hgim : q / 4 ≤ g.im := by
    have h1 : |(g - m).im| ≤ ‖g - m‖ := Complex.abs_im_le_norm _
    have h2 : (g - m).im = g.im - m.im := Complex.sub_im g m
    have := neg_abs_le (g - m).im
    linarith
  have hμ0 : q / (2 * η) ≤ μ := by
    rw [hμ, div_le_div_iff₀ (by positivity) hη]; nlinarith
  have ht0 : q ^ 3 / (16 * η) ≤ t := by
    rw [ht, div_le_div_iff₀ (by positivity) hη]
    have hq2 : q ^ 2 / 4 ≤ ‖m‖ ^ 2 := by nlinarith
    have : q ^ 2 / 4 * (q / 4) ≤ ‖m‖ ^ 2 * g.im :=
      mul_le_mul hq2 hgim (by positivity) (by positivity)
    nlinarith
  have hμt : q ^ 4 / (32 * η ^ 2) ≤ μ * t := by
    have := mul_le_mul hμ0 ht0 (by positivity) (by linarith [show 0 < q / (2 * η) by positivity])
    calc q ^ 4 / (32 * η ^ 2) = q / (2 * η) * (q ^ 3 / (16 * η)) := by field_simp; ring
      _ ≤ μ * t := this
  have hμt0 : 0 < μ * t := lt_of_lt_of_le (by positivity) hμt
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hK : ((μ * t : ℝ) : ℂ) * K = ((t : ℝ) : ℂ) - ((μ : ℝ) : ℂ) * m * star g - ρ / (N : ℂ) := by
    refine mul_left_cancel₀ hN' ?_
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ hN']
    push_cast at hid ⊢
    linear_combination -hid
  have hmm : m * star m = ((‖m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcan : ((t : ℝ) : ℂ) - ((μ : ℝ) : ℂ) * m * star g =
      ((‖m‖ ^ 2 * (g - m).im / η : ℝ) : ℂ) - ((μ : ℝ) : ℂ) * m * star (g - m) := by
    have him : (g - m).im = g.im - m.im := Complex.sub_im g m
    rw [him, star_sub, ht, hμ]
    have e : ((m.im / η : ℝ) : ℂ) * m * (star g - star m) =
        ((m.im / η : ℝ) : ℂ) * m * star g - ((m.im / η : ℝ) : ℂ) * (m * star m) := by ring
    rw [e, hmm]
    push_cast
    ring
  have hlead : ‖((t : ℝ) : ℂ) - ((μ : ℝ) : ℂ) * m * star g‖ ≤ 2 * ‖g - m‖ / η := by
    rw [hcan]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((‖m‖ ^ 2 * (g - m).im / η : ℝ) : ℂ)‖ ≤ ‖g - m‖ / η := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hη,
        abs_of_nonneg (by positivity)]
      refine div_le_div_of_nonneg_right ?_ hη.le
      have : ‖m‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hm1
      calc ‖m‖ ^ 2 * |(g - m).im| ≤ 1 * ‖g - m‖ :=
            mul_le_mul this (Complex.abs_im_le_norm _) (abs_nonneg _) zero_le_one
        _ = ‖g - m‖ := one_mul _
    have h2 : ‖((μ : ℝ) : ℂ) * m * star (g - m)‖ ≤ ‖g - m‖ / η := by
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, hμ,
        abs_div, abs_of_pos hη, abs_of_pos (by linarith : 0 < m.im)]
      have : m.im / η * ‖m‖ ≤ 1 / η := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ hη.le
        nlinarith
      calc m.im / η * ‖m‖ * ‖g - m‖ ≤ 1 / η * ‖g - m‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = ‖g - m‖ / η := by ring
    have : 2 * ‖g - m‖ / η = ‖g - m‖ / η + ‖g - m‖ / η := by ring
    linarith
  have hKn : (μ * t) * ‖K‖ ≤ 2 * ‖g - m‖ / η + ‖ρ‖ / N := by
    have := congrArg norm hK
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμt0] at this
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    linarith
  have hK0 : ‖K‖ ≤ (2 * ‖g - m‖ / η + ‖ρ‖ / N) / (μ * t) := by
    rw [le_div_iff₀ hμt0]; linarith
  refine hK0.trans ?_
  rw [div_le_iff₀ hμt0]
  calc 2 * ‖g - m‖ / η + ‖ρ‖ / N = 32 / q ^ 4 * (2 * η * ‖g - m‖ + η ^ 2 * ‖ρ‖ / N) *
        (q ^ 4 / (32 * η ^ 2)) := by field_simp
    _ ≤ 32 / q ^ 4 * (2 * η * ‖g - m‖ + η ^ 2 * ‖ρ‖ / N) * (μ * t) := by
        gcongr

/-- An expectation split on an event: `f ≤ A` off `bad`, `0 ≤ f ≤ K` everywhere and
`P(bad) ≤ β` give `E f ≤ A + K β`. -/
private theorem MainCancel_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (bad : Set Ω) (A K β : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hβ : 0 ≤ β) (hbad : μ bad ≤ ENNReal.ofReal β)
    (hgood : ∀ ω, ω ∉ bad → f ω ≤ A) (hall : ∀ ω, f ω ≤ K) :
    ∫ ω, f ω ∂μ ≤ A + K * β := by
  set s := toMeasurable μ bad with hs
  have hsm : MeasurableSet s := measurableSet_toMeasurable _ bad
  set h : Ω → ℝ := fun ω => A + s.indicator (fun _ => K) ω with hh
  have hint : Integrable h μ := (integrable_const A).add ((integrable_const _).indicator hsm)
  have hle : ∀ ω, f ω ≤ h ω := by
    intro ω
    by_cases hω : ω ∈ s
    · simp only [hh, Set.indicator_of_mem hω]; linarith [hall ω]
    · have hω' : ω ∉ bad := fun h' => hω (subset_toMeasurable μ bad h')
      simp only [hh, Set.indicator_of_notMem hω]; linarith [hgood ω hω']
  have hμs : μ.real s ≤ β := by
    rw [Measure.real, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hβ hbad
  have hI : ∫ ω, h ω ∂μ = A + μ.real s * K := by
    simp only [hh]
    rw [integral_add (integrable_const A) ((integrable_const _).indicator hsm), integral_const,
      integral_indicator_const _ hsm]
    simp [smul_eq_mul]
  by_cases hf : Integrable f μ
  · refine (integral_mono hf hint hle).trans ?_
    rw [hI]; nlinarith
  · rw [integral_undef hf]
    have : 0 ≤ μ.real s * K := by positivity
    nlinarith

/-! ## The self-energies below order `n` -/

/-- The self-energy matrices below order `k` read only `Sig j`, `j < k`. -/
private theorem MainCancel_sigUpTo_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sig Sig' : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) :
    ∀ k, (∀ j, j < k → Sig j = Sig' j) → sigUpTo Sig S z k = sigUpTo Sig' S z k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [sigUpTo]
    rw [ih fun j hj => h j (by omega), h k (by omega)]

/-- `Σ_k` reads only `Sig j`, `j ≤ k`. -/
private theorem MainCancel_sigMat_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sig Sig' : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) (k : ℕ)
    (h : ∀ j, j ≤ k → Sig j = Sig' j) : sigMat Sig S z k = sigMat Sig' S z k := by
  unfold sigMat
  rw [MainCancel_sigUpTo_congr Sig Sig' S z k fun j hj => h j hj.le, h k le_rfl]

/-- Self-energies of the orders `4 ≤ k ≤ N` for `Sig` are self-energies for every family that
agrees with `Sig` up to order `N`. -/
private theorem MainCancel_selfEnergiesUpTo_congr {d : ℕ} (Svar : VarFamily d)
    (Sig Sig' : ℕ → Expansion 2) (N : ℕ) (h : ∀ j, j ≤ N → Sig j = Sig' j)
    (hSE : SelfEnergiesUpTo d Svar Sig N) : SelfEnergiesUpTo d Svar Sig' N := by
  intro k hk4 hkN hev
  obtain ⟨hsh, hsy, hbd⟩ := hSE k hk4 hkN hev
  have hm : ∀ (W L : ℕ) [NeZero L] (z : ℂ),
      sigMat Sig (Svar W L) z k = sigMat Sig' (Svar W L) z k :=
    fun W L _ z => MainCancel_sigMat_congr Sig Sig' _ z k fun j hj => h j (hj.trans hkN)
  refine ⟨?_, ?_, ?_⟩
  · rw [← h k hkN]; exact hsh
  · intro W L _ z hz x a
    simp only [← hm]
    exact hsy W L z hz x a
  · intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
    obtain ⟨L₀, hL₀⟩ := hbd κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
    refine ⟨L₀, fun W L _ hL hadm z hz => ?_⟩
    simp only [← hm]
    exact hL₀ W L hL hadm z hz

/-! ## [I, (5.44)] summed over `𝔞, 𝔟` -/

/-- Integrability and the expectation of a formal sum of graphs with the kinds of `Err`. -/
private theorem MainCancel_integral_expansion {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2)
    (W L : ℕ) [NeZero L] (z : ℂ) (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) {k N : ℕ}
    (E : Expansion k) (hE : ∀ g ∈ E, g.2.TKindsErr N) (e : Fin k → Zd d L) :
    Integrable (E.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e)
        (gaussLaw (Smat P.ψ W L)) ∧
      ∫ ω, E.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e ω
          ∂(gaussLaw (Smat P.ψ W L)) =
        (E.map fun g => ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e ω
          ∂(gaussLaw (Smat P.ψ W L))).sum := by
  induction E with
  | nil =>
    have : Expansion.valR ([] : Expansion k) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e =
        fun _ => 0 := by funext ω; simp [Expansion.valR]
    rw [this]
    exact ⟨integrable_zero _ _ _, by simp⟩
  | cons g E ih =>
    have h1 := MainCancel_valR_integrable_err P Sig W L z hS hz g.2 (hE g List.mem_cons_self) e
    obtain ⟨h2, h3⟩ := ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    have : Expansion.valR (g :: E) ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e =
        fun ω => g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e ω +
          Expansion.valR E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e ω := by
      funext ω; simp [Expansion.valR]
    rw [this]
    refine ⟨h1.add h2, ?_⟩
    rw [integral_add h1 h2, h3, List.map_cons, List.sum_cons]

/-- `Σ_l` at a symmetric `S_{W,L}` and `Im z > 0` is translation invariant ([I, (1.25)]). -/
private theorem MainCancel_transInv_sigMat {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2)
    (W L : ℕ) [NeZero L] (z : ℂ) (hz : 0 < z.im) (hsym : (Smat P.ψ W L).IsSymm) (l : ℕ) :
    TransInv (sigMat Sig (Smat P.ψ W L) z l) := by
  have h := selfEnergySymm_smatVar d P Sig l W L z hz
  rw [smatVar_eq_of_isSymm P hsym] at h
  intro x y a
  have e1 := (h (x + a) (y - x)).1
  have e2 := (h x (y - x)).1
  rw [show x + a + (y - x) = y + a by abel] at e1
  rw [show x + (y - x) = y by abel] at e2
  rw [e1, e2]

set_option maxHeartbeats 1000000 in
-- the integrals of the three parts of the identity are rewritten at every pair `(𝔞, 𝔟)`
/-- **[I, (5.44)] in expectation, summed over `𝔞, 𝔟`**, on the data record with `Σ_n = E`, with
[I, (5.45)], (5.46), (5.49) and (5.53): for an `n`-th order `T`-equation with `Σ_n = E`, `n ≥ 4`
even, a variance kernel `S_{W,L}` and `η = Im z > 0`, with `g = E G₀₀`,
`L^d |m|² Im g/η = L^d (Im m/η) m ḡ + Σ_{𝔞,𝔟} E(R + A + Q + Err)_{𝔞,𝔟𝔟} +
L^d (Im m/η)(|m|² Im g/η) Σ_x Σ̃^{(n)}(0, x)`. -/
private theorem MainCancel_identity {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2)
    (E : Expansion 2) (n D : ℕ) (𝒬 : TEqRec) (hn4 : 4 ≤ n) (hn : Even n) (hE : 𝒬.SigN = E)
    (h𝒬 : 𝒬.IsTEqStruct Sig n D) (W L : ℕ) [NeZero L] (z : ℂ)
    (hS : IsVarKernel (Smat P.ψ W L)) (hz : 0 < z.im) :
    (((L : ℝ) ^ d : ℝ) : ℂ) * ((‖msc z‖ ^ 2 *
        (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))).im / z.im : ℝ) : ℂ) =
      (((L : ℝ) ^ d : ℝ) : ℂ) * ((((msc z).im / z.im : ℝ) : ℂ) * msc z *
        star (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L)))) +
      (∑ a, ∑ b, ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
        ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P (Function.update Sig n E) W L z)
          ![a, b, b] ω ∂(gaussLaw (Smat P.ψ W L))).sum) +
      (((L : ℝ) ^ d : ℝ) : ℂ) * ((((msc z).im / z.im : ℝ) : ℂ) * ((‖msc z‖ ^ 2 *
        (∫ ω, green (hmat ω) z 0 0 ∂(gaussLaw (Smat P.ψ W L))).im / z.im : ℝ) : ℂ) *
        ∑ x, (sigMat (Function.update Sig n E) (Smat P.ψ W L) z n 0 x +
          ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig (Smat P.ψ W L) z l 0 x)) := by
  set S := Smat P.ψ W L with hSdef
  set Sig' := Function.update Sig n E with hSig'
  have hprob : IsProbabilityMeasure (gaussLaw S) := isProbabilityMeasure_gaussLaw S
  have hsym : S.IsSymm := Matrix.IsSymm.ext fun i j => hS.symm j i
  have hSn : Sig' n = E := Function.update_self ..
  have hSl : ∀ l, l < n → Sig' l = Sig l := fun l hl => Function.update_of_ne (Nat.ne_of_lt hl) ..
  have hsh : SelfEnergyShapesUpTo Sig' n := by
    intro k hk4 hkn hev
    rcases Nat.lt_or_ge k n with hlt | hge
    · rw [hSl k hlt]
      exact h𝒬.2.2.1 k hk4 (by omega) hev
    · obtain rfl : k = n := le_antisymm hkn hge
      rw [hSn, ← hE]; exact h𝒬.2.2.2.1
  have hcons : ∀ ω, SigConsistent Sig' (n + 1) (rbmData d P Sig' W L z ω) :=
    fun ω => Moment_sigConsistent d P Sig' n hsh W L z ω
  have hcons' : ∀ ω, SigConsistent Sig n (rbmData d P Sig' W L z ω) := by
    intro ω k hk4 hkn hev
    have h := hcons ω k hk4 (by omega) hev
    rwa [hSl k hkn] at h
  have hadm := Moment_modelAdm d P Sig' W L z hsym hS.nonneg hS.rowSum hz
  set M : Matrix (Zd d L) (Zd d L) ℂ :=
    sigMat Sig' S z n + ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig' S z l with hM
  have hsig : ∀ ω, sigTilde n 𝒬.SigN (rbmData d P Sig' W L z ω) = M := by
    intro ω
    have h := hcons ω n hn4 (Nat.lt_succ_self n) hn
    rw [hSn] at h
    rw [hE]
    unfold sigTilde
    rw [← h]
    rfl
  have hMT : TransInv M := by
    intro x y a
    simp only [hM, Matrix.add_apply, Matrix.sum_apply]
    rw [MainCancel_transInv_sigMat P Sig' W L z hz hsym n x y a]
    congr 1
    exact Finset.sum_congr rfl fun l _ => MainCancel_transInv_sigMat P Sig' W L z hz hsym l x y a
  have hid := h𝒬.2.1 (Sample (Zd d L)) (Zd d L) ⟨Pexp S⟩ (rbmData d P Sig' W L z) hadm hcons'
  have hKE : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, g.2.TKindsErr (n - 1) := by
    obtain ⟨⟨h1, h2⟩, -⟩ := h𝒬.2.2.2.2.1
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact Graph.tKindsErr_of_tKinds _ _ (h1 g hg).2.1
    · exact (h2 g hg).2.1
  have hlead : ∀ g ∈ leadExp, g.2.TKindsErr 0 := by
    intro g hg
    simp only [leadExp, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    unfold Graph.TKindsErr
    decide
  set Θ := (rbmData d P Sig' W L z 0).Theta with hΘ
  -- one pair `(a, b)`
  have hab : ∀ a b : Zd d L,
      ∫ ω, tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω ∂(gaussLaw S) =
        ∫ ω, leadExp.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω ∂(gaussLaw S) +
        ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
          ∫ ω, g.2.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω ∂(gaussLaw S)).sum +
        ∑ x, (Θ * M) a x *
          ∫ ω, tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![x, b, b] ω ∂(gaussLaw S) := by
    intro a b
    obtain ⟨hi1, he1⟩ := MainCancel_integral_expansion P Sig' W L z hS hz leadExp hlead ![a, b, b]
    obtain ⟨hi2, he2⟩ := MainCancel_integral_expansion P Sig' W L z hS hz _ hKE ![a, b, b]
    have hfun : tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] = fun ω =>
        leadExp.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω +
        (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω +
        ∑ x, (Θ * M) a x * tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![x, b, b] ω := by
      funext ω
      rw [hid ![a, b, b] ω, hsig ω]
      simp only [Expansion.valR, List.map_append, List.sum_append, List.append_assoc]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rfl
    have hi3 : Integrable (fun ω => ∑ x, (Θ * M) a x *
        tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![x, b, b] ω) (gaussLaw S) :=
      integrable_finsetSum _ fun x _ =>
        (MainCancelId.tGraph_valR_integrable P Sig' W L z hS hz x b).const_mul _
    have hi12 : Integrable (fun ω =>
        leadExp.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω +
        (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω)
        (gaussLaw S) := hi1.add hi2
    rw [hfun, integral_add hi12 hi3, integral_add hi1 hi2, he2,
      integral_finsetSum _ fun x _ =>
        (MainCancelId.tGraph_valR_integrable P Sig' W L z hS hz x b).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun x _ => integral_const_mul _ _
  have h1 := MainCancelId.expT_total P Sig' W L z hS hz
  have h2 := MainCancelId.expLead_total P Sig' W L z hS hz
  have h3 := MainCancelId.sigma_term P Sig' W L z hS hz M hMT
  rw [MainCancelId.msc_ratio z hz] at h2 h3
  have hrow : ∑ α, M 0 α = ∑ x, (sigMat Sig' S z n 0 x +
      ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l 0 x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hM, Matrix.add_apply, Matrix.sum_apply]
    have e : ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig' S z l 0 x =
        ∑ l ∈ (Finset.Ico 4 n).filter Even, sigMat Sig S z l 0 x := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l < n := (Finset.mem_Ico.1 (Finset.mem_filter.1 hl).1).2
      rw [MainCancel_sigMat_congr Sig' Sig S z l fun j hj => hSl j (by omega)]
    rw [e]
  rw [hrow] at h3
  have hsum : ∑ a, ∑ b, ∫ ω, tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω
      ∂(gaussLaw S) =
      ∑ a, ∑ b, ∫ ω, leadExp.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω
        ∂(gaussLaw S) +
      ∑ a, ∑ b, ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
          ∫ ω, g.2.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![a, b, b] ω ∂(gaussLaw S)).sum +
      ∑ a, ∑ x, ∑ b, (Θ * M) a x *
          ∫ ω, tGraph.valR ⟨Pexp S⟩ (rbmData d P Sig' W L z) ![x, b, b] ω ∂(gaussLaw S) := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hab a b]
    simp only [Finset.sum_add_distrib]
    refine (add_right_inj _).2 ?_
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [h1, h2, h3] at hsum
  push_cast at hsum ⊢
  linear_combination hsum

/-- Sums over `𝔞, 𝔟` commute with a sum over a list of graphs. -/
private theorem MainCancel_sum_list {α ι : Type*} [Fintype ι] (l : List α) (F : α → ι → ι → ℂ) :
    ∑ a, ∑ b, (l.map fun g => F g a b).sum = (l.map fun g => ∑ a, ∑ b, F g a b).sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- A sum over a list is at most the sum of the bounds of its terms. -/
private theorem MainCancel_norm_list {α : Type*} (l : List α) (ψ : α → ℂ) (φ : α → ℝ)
    (h : ∀ g ∈ l, ‖ψ g‖ ≤ φ g) : ‖(l.map ψ).sum‖ ≤ (l.map φ).sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h g List.mem_cons_self)
      (ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')))

/-- A sum over a list of graphs splits into the graphs with and without internal atoms. -/
private theorem MainCancel_split (l : Expansion 3) (φ : (Σ n : ℕ, Graph 3 n) → ℝ) :
    (l.map φ).sum = ((l.filter fun g => g.1 ≠ 0).map φ).sum +
      ((l.filter fun g => g.1 = 0).map φ).sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
    by_cases h : g.1 = 0
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, h, ne_eq, not_true_eq_false,
        decide_false, decide_true, ih]
      simp; ring
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, h, ne_eq, not_false_eq_true,
        decide_false, decide_true, ih]
      simp; ring

/-- **The remainder `R + A + Q + Err` of [I, (5.44)] summed over `𝔞, 𝔟`**: by `E Q = 0` its norm is
at most the sum of `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}|` over the graphs of `R`, of `A` and of `Err`, the last two
split into the graphs with and without internal atoms. -/
private theorem MainCancel_rho_le {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (p : SizeL)
    (z : ℂ) (hS : IsVarKernel (Smat P.ψ p.1.1 p.1.2)) (hz : 0 < z.im) (N : ℕ) (𝒬 : TEqRec)
    (hQ : ∀ g ∈ 𝒬.Q, g.2.TKinds N ∧ g.2.IsQGraph) :
    ‖∑ a, ∑ b, ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
        ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω
          ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))).sum‖ ≤
      (𝒬.R.map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2, ∫ ω, ‖g.2.valR
          ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩
          (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω‖ ∂(rbmLaw d P p)).sum +
      ((𝒬.A.filter fun g => g.1 ≠ 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2, ∫ ω, ‖g.2.valR
          ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω‖
            ∂(rbmLaw d P p)).sum +
      ((𝒬.A.filter fun g => g.1 = 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2, ∫ ω, ‖g.2.valR
          ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω‖
            ∂(rbmLaw d P p)).sum +
      ((𝒬.Err.filter fun g => g.1 ≠ 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR
          ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω‖
            ∂(rbmLaw d P p)).sum +
      ((𝒬.Err.filter fun g => g.1 = 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR
          ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω‖
            ∂(rbmLaw d P p)).sum := by
  set ψ : (Σ n : ℕ, Graph 3 n) → ℂ := fun g => ∑ a, ∑ b, ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩
    (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2)) with hψ
  set φ : (Σ n : ℕ, Graph 3 n) → ℝ := fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
    ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 z) ![a, b, b] ω‖
      ∂(rbmLaw d P p) with hφ
  have hle : ∀ g : (Σ n : ℕ, Graph 3 n), ‖ψ g‖ ≤ φ g := fun g =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b _ => norm_integral_le_integral_norm _))
  have hQ0 : (𝒬.Q.map ψ).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    exact MainCancelId.expQ_zero P Sig p.1.1 p.1.2 z hS hz g.2 (hQ g hg).1 (hQ g hg).2 _
  rw [MainCancel_sum_list, List.map_append, List.map_append, List.map_append, List.sum_append,
    List.sum_append, List.sum_append]
  change ‖(𝒬.R.map ψ).sum + (𝒬.A.map ψ).sum + (𝒬.Q.map ψ).sum + (𝒬.Err.map ψ).sum‖ ≤ _
  rw [hQ0, add_zero]
  have hA := MainCancel_split 𝒬.A φ
  have hE := MainCancel_split 𝒬.Err φ
  have h1 := MainCancel_norm_list 𝒬.R ψ φ fun g _ => hle g
  have h2 := MainCancel_norm_list 𝒬.A ψ φ fun g _ => hle g
  have h3 := MainCancel_norm_list 𝒬.Err ψ φ fun g _ => hle g
  have h4 := norm_add₃_le (a := (𝒬.R.map ψ).sum) (b := (𝒬.A.map ψ).sum) (c := (𝒬.Err.map ψ).sum)
  linarith

/-! ## `E G₀₀ − m` -/

/-- **`E G₀₀ = m + O(W^{−d/2+δ})`**: under the local law `|G_{xy} − m δ_{xy}|² ≺ B_{xy}` along a
filter `F` below its filter, at spectral parameters `z_p ∈ 𝐃(κ, ε)`, for every `δ > 0`, eventually
along `F`, `|E G₀₀(z_p) − m(z_p)| ≤ W^{−d/2+δ}`. On the event of the local law
`|G₀₀ − m|² ≤ W^{δ} B₀₀ = W^{δ−d}`; off it `|G₀₀ − m| ≤ η⁻¹ + 1`. -/
private theorem MainCancel_expG (d : ℕ) (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ)
    (hc₁ : 0 < c₁) (hε : 0 < ε) (N : ℕ)
    (hLL : StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2))
    (F : Filter SizeL) (hF : F ≤ llFilter d N c₀ c₁ c₀T) (z : SizeL → ℂ)
    (hz : ∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ p in F, ‖(∫ ω, green (hmat ω) (z p) 0 0 ∂(rbmLaw d P p)) - msc (z p)‖ ≤
      (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + δ) := by
  have hsz : Tendsto sizeW F atTop := (Moment_tendsto d N c₀ c₁ c₀T).mono_left hF
  have hD : (0 : ℝ) < 2 / c₁ + d / 2 + 1 := by positivity
  filter_upwards [hz, (hLL δ hδ _ hD).filter_mono hF, (Moment_ev_adm d N c₀ c₁ c₀T).filter_mono hF,
    hsz.eventually (eventually_ge_atTop 2),
    ((tendsto_rpow_atTop (by positivity : 0 < δ / 2)).comp hsz).eventually
      (eventually_ge_atTop 2)] with p hzp hbad hp hW2 hWδ
  change (2 : ℝ) ≤ p.1.1 at hW2
  change (2 : ℝ) ≤ (p.1.1 : ℝ) ^ (δ / 2) at hWδ
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  obtain ⟨him, hinv⟩ := Moment_im_inv (c₀ := c₀) hc₁ hε p hp hW1 (z p) hzp
  have hprob : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
  set m := msc (z p) with hm
  have hm1 : ‖m‖ ≤ 1 := (norm_msc_lt_one him).le
  set f : Sample (Zd d p.1.2) → ℝ := fun ω => ‖green (hmat ω) (z p) 0 0 - m‖ with hf
  have hB : bB d p.1.2 p.1.1 0 0 = W ^ (-(d : ℝ)) := by
    have h0 : zdistInf d p.1.2 ((0 : Zd d p.1.2) - 0) = 0 := by simp [zdistInf, zdist]
    unfold bB
    rw [h0, Nat.cast_zero, zero_add, ← Real.rpow_add hW0]
    congr 1; ring
  set A : ℝ := W ^ ((δ - d) / 2) with hA
  have hA2 : A ^ 2 = W ^ δ * W ^ (-(d : ℝ)) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le, ← Real.rpow_add hW0]
    congr 1; push_cast; ring
  have hgood : ∀ ω, ω ∉ {ω | ∃ u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} ×
      Zd d p.1.2 × Zd d p.1.2, sizeW p ^ δ * bB d p.1.2 p.1.1 u.2.1 u.2.2 <
        ‖entryErr (green (hmat ω) u.1.1) (msc u.1.1) u.2.1 u.2.2‖ ^ 2} → f ω ≤ A := by
    intro ω hω
    have hsq : f ω ^ 2 ≤ A ^ 2 := by
      by_contra hcon
      refine hω ⟨(⟨z p, hzp⟩, 0, 0), ?_⟩
      change W ^ δ * bB d p.1.2 p.1.1 0 0 < _
      rw [hB, ← hA2]
      simpa [entryErr, hf] using lt_of_not_ge hcon
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hall : ∀ ω, f ω ≤ W ^ (2 / c₁) + 1 := by
    intro ω
    have h1 := norm_green_entry_le (hmat_isHermitian ω) him.ne' (0 : Zd d p.1.2) 0
    rw [abs_of_pos him] at h1
    exact (norm_sub_le _ _).trans (add_le_add (h1.trans hinv) hm1)
  have hint := MainCancel_integral_le (rbmLaw d P p) f _ A (W ^ (2 / c₁) + 1)
    (W ^ (-(2 / c₁ + d / 2 + 1))) (by positivity) (by positivity) (by positivity) hbad hgood hall
  have hsub : (∫ ω, green (hmat ω) (z p) 0 0 ∂(rbmLaw d P p)) - m =
      ∫ ω, (green (hmat ω) (z p) 0 0 - m) ∂(rbmLaw d P p) := by
    have hi : Integrable (fun ω => green (hmat ω) (z p) 0 0) (rbmLaw d P p) :=
      MainCancelId.integrable_green (Smat P.ψ p.1.1 p.1.2) (z p) him 0 0
    rw [integral_sub hi (integrable_const _), integral_const]
    simp
  rw [hsub]
  refine (norm_integral_le_integral_norm _).trans (hint.trans ?_)
  have hK : (W ^ (2 / c₁) + 1) * W ^ (-(2 / c₁ + d / 2 + 1)) ≤ W ^ (-((d : ℝ) / 2)) := by
    have h1 : 1 ≤ W ^ (2 / c₁) := Real.one_le_rpow hW1 (by positivity)
    have h2 : W ^ (2 / c₁) * W ^ (-(2 / c₁ + d / 2 + 1)) * W = W ^ (-((d : ℝ) / 2)) := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add_one hW0.ne']; congr 1; ring
    have h3 : 0 ≤ W ^ (-(2 / c₁ + d / 2 + 1)) := by positivity
    have h4 : 0 ≤ W ^ (2 / c₁) * W ^ (-(2 / c₁ + d / 2 + 1)) := by positivity
    nlinarith
  have hAd : W ^ (-((d : ℝ) / 2)) ≤ A :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hfin : W ^ (δ / 2) * A = W ^ (-((d : ℝ) / 2) + δ) := by
    rw [hA, ← Real.rpow_add hW0]; congr 1; ring
  have hA0 : 0 ≤ A := by positivity
  nlinarith

/-! ## The sizes `L_n` of [I, (5.39)] -/

/-- In the window `W^a ≤ L²/W² ≤ W^b` with `ε < a`, `b > 0`, `η = W^{2+ε}/L²` satisfies
`η · L²/W² = W^ε`, `0 < η ≤ W^{ε−a} ≤ 1`, and `L ≤ W^{(2+b)/2}`. -/
private theorem MainCancel_window {a b ε W L : ℝ} (hW : 1 ≤ W) (hL : 1 ≤ L) (ha : ε < a)
    (h1 : W ^ a ≤ L ^ 2 / W ^ 2) (h2 : L ^ 2 / W ^ 2 ≤ W ^ b) :
    W ^ (2 + ε) / L ^ 2 * (L ^ 2 / W ^ 2) = W ^ ε ∧ 0 < W ^ (2 + ε) / L ^ 2 ∧
      W ^ (2 + ε) / L ^ 2 ≤ W ^ (ε - a) ∧ W ^ (2 + ε) / L ^ 2 ≤ 1 ∧ L ≤ W ^ ((2 + b) / 2) := by
  have hW0 : 0 < W := by linarith
  have hL0 : 0 < L := by linarith
  have hW2 : W ^ (2 + ε) = W ^ 2 * W ^ ε := by
    rw [Real.rpow_add hW0, Real.rpow_two]
  have he : W ^ (2 + ε) / L ^ 2 * (L ^ 2 / W ^ 2) = W ^ ε := by
    rw [hW2]; field_simp
  have hpos : 0 < W ^ (2 + ε) / L ^ 2 := by positivity
  have hΛ0 : 0 < L ^ 2 / W ^ 2 := by positivity
  have hle : W ^ (2 + ε) / L ^ 2 ≤ W ^ (ε - a) := by
    have h3 : W ^ (2 + ε) / L ^ 2 = W ^ ε / (L ^ 2 / W ^ 2) := by
      rw [eq_div_iff hΛ0.ne', he]
    rw [h3, Real.rpow_sub hW0]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  refine ⟨he, hpos, hle, hle.trans (Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)), ?_⟩
  have hL2 : L ^ 2 ≤ (W ^ ((2 + b) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast (W ^ ((2 + b) / 2)), ← Real.rpow_mul hW0.le]
    have : L ^ 2 ≤ W ^ b * W ^ 2 := (div_le_iff₀ (by positivity)).1 h2
    calc L ^ 2 ≤ W ^ b * W ^ 2 := this
      _ = W ^ ((2 + b) / 2 * ((2 : ℕ) : ℝ)) := by
          rw [← Real.rpow_two, ← Real.rpow_add hW0]; congr 1; push_cast; ring
  exact (pow_le_pow_iff_left₀ hL0.le (by positivity) two_ne_zero).1 hL2

/-- `η² · W^δ N Λ W^{−x} / N ≤ W^{δ+2ε−a−x}` for `η Λ = W^ε`, `η ≤ W^{ε−a}`. -/
private theorem MainCancel_rpow1 {W η Λ N ε a δ x : ℝ} (hW : 0 < W) (hN : 0 < N)
    (hηΛ : η * Λ = W ^ ε) (hη : η ≤ W ^ (ε - a)) :
    η ^ 2 * (W ^ δ * N * Λ * W ^ (-x)) / N ≤ W ^ (δ + 2 * ε - a - x) := by
  have e : η ^ 2 * (W ^ δ * N * Λ * W ^ (-x)) / N = η * (W ^ δ * W ^ ε * W ^ (-x)) := by
    field_simp; rw [← hηΛ]; ring
  rw [e]
  calc η * (W ^ δ * W ^ ε * W ^ (-x)) ≤ W ^ (ε - a) * (W ^ δ * W ^ ε * W ^ (-x)) :=
        mul_le_mul_of_nonneg_right hη (by positivity)
    _ = W ^ (δ + 2 * ε - a - x) := by
        rw [← Real.rpow_add hW, ← Real.rpow_add hW, ← Real.rpow_add hW]; congr 1; ring

/-- `η² · W^δ N Λ² W^{−x} / N = W^{δ+2ε−x}` for `η Λ = W^ε`. -/
private theorem MainCancel_rpow2 {W η Λ N ε δ x : ℝ} (hW : 0 < W) (hN : 0 < N)
    (hηΛ : η * Λ = W ^ ε) :
    η ^ 2 * (W ^ δ * N * Λ ^ 2 * W ^ (-x)) / N = W ^ (δ + 2 * ε - x) := by
  have e : η ^ 2 * (W ^ δ * N * Λ ^ 2 * W ^ (-x)) / N = (η * Λ) ^ 2 * W ^ δ * W ^ (-x) := by
    field_simp
  rw [e, hηΛ, ← Real.rpow_natCast, ← Real.rpow_mul hW.le, ← Real.rpow_add hW,
    ← Real.rpow_add hW]
  congr 1; push_cast; ring

/-- `η² · W^δ L^{2d+2} W^{−y} / L^d ≤ W^{δ + (d+2)(2+b)/2 − y}` for `η ≤ 1` and
`1 ≤ L ≤ W^{(2+b)/2}`. -/
private theorem MainCancel_rpow3 {W η L b δ y : ℝ} (d : ℕ) (hW : 0 < W) (hL : 1 ≤ L)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hLW : L ≤ W ^ ((2 + b) / 2)) :
    η ^ 2 * (W ^ δ * L ^ (2 * d + 2) * W ^ (-y)) / L ^ d ≤
      W ^ (δ + (d + 2) * ((2 + b) / 2) - y) := by
  have hL0 : 0 < L := by linarith
  have e : η ^ 2 * (W ^ δ * L ^ (2 * d + 2) * W ^ (-y)) / L ^ d =
      η ^ 2 * (W ^ δ * L ^ (d + 2) * W ^ (-y)) := by
    rw [show 2 * d + 2 = d + (d + 2) by ring, pow_add]; field_simp
  rw [e]
  have h1 : η ^ 2 ≤ 1 := pow_le_one₀ hη0 hη1
  have h2 : L ^ (d + 2) ≤ W ^ (((d : ℝ) + 2) * ((2 + b) / 2)) := by
    calc L ^ (d + 2) ≤ (W ^ ((2 + b) / 2)) ^ (d + 2) := pow_le_pow_left₀ hL0.le hLW _
      _ = W ^ (((d : ℝ) + 2) * ((2 + b) / 2)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; congr 1; push_cast; ring
  calc η ^ 2 * (W ^ δ * L ^ (d + 2) * W ^ (-y)) ≤ 1 * (W ^ δ * L ^ (d + 2) * W ^ (-y)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ W ^ δ * W ^ (((d : ℝ) + 2) * ((2 + b) / 2)) * W ^ (-y) := by
        rw [one_mul]; gcongr
    _ = W ^ (δ + (d + 2) * ((2 + b) / 2) - y) := by
        rw [← Real.rpow_add hW, ← Real.rpow_add hW]; congr 1

set_option maxHeartbeats 8000000 in
-- the final step instantiates the rows of [I, Lemma 5.12] and the local law at once
/-- **[I, Lemma 5.11] at an even order `n ≥ 4`**, at `c = c₀/2`, `ε ≤ c₀/8`. -/
private theorem MainCancel_even (hLL : localLawTExpStmt') (d : ℕ) (hd : 8 ≤ d) (P : Profile d)
    (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ) (hn4 : 4 ≤ n) (hev : Even n)
    (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec)
    (hH : HWith d (smatVar P) Strat Sig (n - 1))
    (hT : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D))
    (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀d : c₀ < d / 4) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ c₀ / 8)
    (E' : ℝ) (hE' : |E'| < 2) :
    ∀ᶠ p in G13.windowFilter d n c₀,
      ‖∑ x : Zd d p.1.2, sigMat (Function.update Sig n E) (smatVar P p.1.1 p.1.2)
          ((E' : ℂ) + Complex.I * (((p.1.1 : ℝ) ^ (2 + ε) / (p.1.2 : ℝ) ^ 2 : ℝ) : ℂ)) n 0 x‖ ≤
        (p.1.1 : ℝ) ^ (-(((n : ℝ) - 2) * d / 2) - c₀ / 2) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  set T : ℝ := ((n : ℝ) - 2) * d / 2 with hTdef
  set a : ℝ := ((n : ℝ) - 3) * d / 2 + c₀ with ha
  set b : ℝ := ((n : ℝ) - 2) * d / 2 - c₀ with hb
  have haT : a + d / 2 = T + c₀ := by rw [ha, hTdef]; ring
  have hbT : b = T - c₀ := by rw [hb, hTdef]
  have hT0 : (d : ℝ) ≤ T := by rw [hTdef]; nlinarith
  have hab : a < b := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hεa : ε < a := by linarith
  -- the exponents of `adm`
  set c₀' := G13.c0w d n c₀ with hc₀'
  set c₁' := G13.c1w d n c₀ with hc₁'
  have e0 : c₀' = a / (2 + a) := by simp only [hc₀', G13.c0w, ha]; ring
  have e1 : c₁' = 2 / (2 + b) := by simp only [hc₁', G13.c1w, hb]; ring
  have hc₀'0 : 0 < c₀' := by rw [e0]; positivity
  have hc₁'0 : 0 < c₁' := by rw [e1]; positivity
  have hsum : c₀' + c₁' < 1 := by
    rw [e0, e1, div_add_div _ _ (by positivity) (by positivity), div_lt_one (by positivity)]
    nlinarith
  -- the parameters
  set κ : ℝ := (2 - |E'|) / 2 with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  set ε'' : ℝ := 2 * ε / (2 + b) with hε''def
  have hε'' : 0 < ε'' := by positivity
  set δ : ℝ := c₀ / 16 with hδdef
  have hδ : 0 < δ := by positivity
  set τ : ℝ := c₀ / (8 * (2 + b)) with hτdef
  have hτ : 0 < τ := by positivity
  have hτb : (2 + b) / 2 * τ = c₀ / 16 := by rw [hτdef]; field_simp; ring
  have hεb : (2 + b) / 2 * ε'' = ε := by rw [hε''def]; field_simp
  set q : ℝ := 1 - E' ^ 2 / 4 with hqdef
  have hq : 0 < q := by
    have h1 := sq_abs E'
    have h2 : |E'| ^ 2 < 4 := by nlinarith [abs_nonneg E']
    rw [hqdef]; linarith
  -- the error order `D` of the `T`-equation
  obtain ⟨M, hM⟩ : ∃ M : ℕ, δ + ((d : ℝ) + 2) * ((2 + b) / 2) + T + c₀ ≤ M :=
    ⟨_, Nat.le_ceil _⟩
  set D : ℕ := n + 3 + M with hDdef
  have hDn : n < D := by omega
  have hD3 : ((D : ℝ) - 3) = n + M := by rw [hDdef]; push_cast; ring
  have hDexp : δ + ((d : ℝ) + 2) * ((2 + b) / 2) - ((D : ℝ) - 3) * d / 4 ≤ -T - c₀ := by
    rw [hD3]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    nlinarith
  obtain ⟨hSigN, hSEq, h𝒬⟩ := hT D hDn
  set 𝒬 := 𝒬n D with h𝒬def
  set Sig' := Function.update Sig n E with hSig'
  have hSE' : SelfEnergiesUpTo d (smatVar P) Sig' (n - 1) :=
    MainCancel_selfEnergiesUpTo_congr _ Sig Sig' (n - 1)
      (fun j hj => (Function.update_of_ne (by omega) _ _).symm) hSEq
  -- the local law at order `n − 1`
  obtain ⟨hSEH, 𝒬h, 𝒯h, hfam⟩ := hH
  have hfam' : ∀ D' : ℕ, n - 1 + 2 ≤ D' → ∃ (Sig₁ : ℕ → Expansion 2) (𝒯 : TRec),
      IsTExpansion d (smatVar P) Sig₁ (n - 1) D' 𝒯 ∧ 𝒯.Def63G11 := fun D' hD' =>
    have h := (hfam.1 (n - 1) D' (by omega) le_rfl (by omega)).2.1
    ⟨Sig, 𝒯h (n - 1) D', ⟨hSEH, h⟩, TRec.def63G11_of_def63 _ h.2.2.2.2⟩
  have hLLn := hLL d hd P c₀' c₁' κ ε'' c₀ hc₀'0 hc₁'0 hsum hκ hε'' hc₀ (n - 1) hfam'
  -- the filter
  set F := G13.windowFilter d n c₀ with hFdef
  have hF : F ≤ llFilter d (n - 1) c₀' c₁' c₀ := G13.windowFilter_le_llFilter d n (by omega) c₀
  have hsz : Tendsto sizeW F atTop := (Moment_tendsto d (n - 1) c₀' c₁' c₀).mono_left hF
  have hwin : ∀ᶠ p in F, p ∈ G13.window d n c₀ :=
    Filter.mem_inf_of_right (Filter.mem_principal_self _)
  have hadm : ∀ᶠ p in F, p.1 ∈ adm c₀' c₁' :=
    (Moment_ev_adm d (n - 1) c₀' c₁' c₀).filter_mono hF
  have hW1 : ∀ᶠ p in F, (1 : ℝ) ≤ p.1.1 := hsz.eventually (eventually_ge_atTop 1)
  set z : SizeL → ℂ := fun p =>
    (E' : ℂ) + Complex.I * (((p.1.1 : ℝ) ^ (2 + ε) / (p.1.2 : ℝ) ^ 2 : ℝ) : ℂ) with hzdef
  have hzim : ∀ p, (z p).im = (p.1.1 : ℝ) ^ (2 + ε) / (p.1.2 : ℝ) ^ 2 := fun p => by
    simp only [hzdef, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
  have hzre : ∀ p, (z p).re = E' := fun p => by
    simp only [hzdef, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, sub_zero, add_zero, mul_zero]
  have hz : ∀ᶠ p in F, z p ∈ specDom κ ε'' p.1.1 p.1.2 := by
    filter_upwards [hwin, hW1] with p hp hW
    have hL : (1 : ℝ) ≤ p.1.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
    have hW0 : (0 : ℝ) < p.1.1 := by linarith
    have hL0 : (0 : ℝ) < p.1.2 := by linarith
    obtain ⟨-, -, -, hη1, hLW⟩ := MainCancel_window hW hL hεa hp.1 hp.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hzre, hκdef]; linarith [le_abs_self E']
    · rw [hzim]
      have hLe : (p.1.2 : ℝ) ^ ε'' ≤ (p.1.1 : ℝ) ^ ε := by
        calc (p.1.2 : ℝ) ^ ε'' ≤ ((p.1.1 : ℝ) ^ ((2 + b) / 2)) ^ ε'' :=
              Real.rpow_le_rpow hL0.le hLW hε''.le
          _ = (p.1.1 : ℝ) ^ ε := by rw [← Real.rpow_mul hW0.le, hεb]
      calc (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε'') =
            (p.1.1 : ℝ) ^ 2 * (p.1.2 : ℝ) ^ ε'' / (p.1.2 : ℝ) ^ 2 := by
            rw [Real.rpow_sub hL0, Real.rpow_two]; field_simp
        _ ≤ (p.1.1 : ℝ) ^ 2 * (p.1.1 : ℝ) ^ ε / (p.1.2 : ℝ) ^ 2 := by gcongr
        _ = (p.1.1 : ℝ) ^ (2 + ε) / (p.1.2 : ℝ) ^ 2 := by rw [Real.rpow_add hW0, Real.rpow_two]
    · rw [hzim]; exact hη1
  -- the rows of [I, Lemma 5.12]
  have hShape := h𝒬.2.2.2.2.1
  have hDef := h𝒬.2.2.2.2.2.2
  have hDefG := TRec.def63G11_of_def63 _ hDef
  have hR := Lem512.recordRows d hd P c₀' c₁' κ ε'' c₀ hc₀'0 hc₁'0 hsum hκ hε'' (n - 1) n D Sig'
    𝒬.toTRec (by omega) hSE' hShape hDef hLLn F hF z hz δ hδ
  have hZ := Lem512Zero.recordRows d hd P c₀' c₁' κ ε'' c₀ hc₀'0 hc₁'0 hsum hκ hε'' hc₀ (n - 1) n D
    Sig' 𝒬.toTRec hSE' hShape hDefG hLLn F hF z hz δ hδ
  have hE1 : ∀ g ∈ 𝒬.Err.filter (fun g => g.1 ≠ 0), ∀ᶠ p in F,
      ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2, ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩
        (rbmData d P Sig' p.1.1 p.1.2 (z p)) ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
      (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ (2 * d + 2) * (p.1.1 : ℝ) ^ (-(((D : ℝ) - 3) * d / 4)) := by
    intro g hg
    obtain ⟨hgE, hg0⟩ := List.mem_filter.1 hg
    have hg0' : g.1 ≠ 0 := by simpa using hg0
    obtain ⟨⟨C, hN⟩, hK, hAE, hDC⟩ := hShape.1.2 g hgE
    obtain ⟨hTD, hDA⟩ := hDefG.1 g (List.mem_append_right _ hgE)
    have hRt := hDefG.2.2 g (List.mem_append_right _ hgE) hg0'
    have hord : (D : ℤ) < g.2.ord := hShape.2.2.2.2 g hgE
    have hdo : g.2.ord - 2 ≤ g.2.diagOrd := by unfold Graph.diagOrd; split_ifs <;> omega
    have h2 : 2 ≤ g.2.diagOrd := by omega
    have h3 : ((D : ℝ) - 3) ≤ (g.2.diagOrd : ℝ) - 2 := by
      have : ((D : ℤ) : ℝ) - 1 ≤ (g.2.diagOrd : ℝ) := by
        exact_mod_cast (show (D : ℤ) - 1 ≤ g.2.diagOrd by omega)
      push_cast at this
      linarith
    have hrow := MainCancel_errRow d hd P c₀' c₁' κ ε'' c₀ hc₀'0 hc₁'0 hsum hκ hε'' hc₀ (n - 1)
      Sig' hSE' hLLn F hF z hz C g.2 hg0' hN hK hAE hDC hTD hDA hRt h2 δ hδ
    filter_upwards [hrow, hW1] with p hp hW
    refine hp.trans ?_
    gcongr
  -- the lower orders `4 ≤ l ≤ n − 1`: the row sums of [I, (1.27)]
  set S := (Finset.Ico 4 n).filter Even with hSdef
  have hlow : ∀ l ∈ S, ∀ᶠ p in F,
      ‖∑ x : Zd d p.1.2, sigMat Sig (smatVar P p.1.1 p.1.2) (z p) l 0 x‖ ≤
        (p.1.2 : ℝ) ^ τ * (z p).im * (p.1.1 : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
    intro l hl
    obtain ⟨hlI, hle⟩ := Finset.mem_filter.1 hl
    obtain ⟨hl4, hln⟩ := Finset.mem_Ico.1 hlI
    obtain ⟨L₀, hL₀⟩ :=
      (hSEq l hl4 (by omega) hle).2.2 κ ε'' c₀' c₁' hκ hε'' hc₀'0 hc₁'0 hsum τ hτ
    filter_upwards [hz, hadm, hsz.eventually (eventually_ge_atTop (L₀ : ℝ))] with p hzp hp hW
    have hWL := MainCancel_W_le_L hc₀'0 p.2 hp
    have hL : L₀ ≤ p.1.2 := by
      have : (L₀ : ℝ) ≤ p.1.2 := le_trans hW hWL
      exact_mod_cast this
    exact (hL₀ p.1.1 p.1.2 hL hp (z p) hzp).2
  -- `E G₀₀ − m`, and the sizes
  obtain ⟨W₀, hW₀⟩ := Smat_isVarKernel_adm d P c₀' c₁' hc₀'0 hc₁'0
  have hG := MainCancel_expG d P c₀' c₁' κ ε'' c₀ hc₁'0 hε'' (n - 1) hLLn F hF z hz δ hδ
  set cntE : ℕ := (𝒬.Err.filter fun g => g.1 ≠ 0).length with hcntE
  set C : ℝ := 32 / q ^ 4 * (2 + 5 + cntE) + S.card with hC
  have hsmall : ∀ᶠ p in F, (p.1.1 : ℝ) ^ (-((d : ℝ) / 2) + δ) < q / 4 := by
    have e : -((d : ℝ) / 2) + δ = -((d : ℝ) / 2 - δ) := by ring
    rw [e]
    exact (tendsto_order.1 ((tendsto_rpow_neg_atTop (by linarith)).comp hsz)).2 (q / 4)
      (by positivity)
  have hbig : ∀ᶠ p in F, C ≤ (p.1.1 : ℝ) ^ (c₀ / 8) :=
    ((tendsto_rpow_atTop (by positivity)).comp hsz).eventually (eventually_ge_atTop C)
  filter_upwards [hwin, hadm, hW1, hz, hR, hZ, Moment_ev_list _ hE1,
    (Filter.eventually_all_finset S).2 hlow, hG, hsmall, hbig,
    hsz.eventually (eventually_ge_atTop W₀)] with p hp hpa hW hzp hRp hZp hEp hlowp hGp hsmallp
    hbigp hW₀p
  change W₀ ≤ (p.1.1 : ℝ) at hW₀p
  simp only [TEqRec.toTRec] at hRp hZp
  change ‖∑ x : Zd d p.1.2, sigMat Sig' (smatVar P p.1.1 p.1.2) (z p) n 0 x‖ ≤ _
  have hVK : IsVarKernel (Smat P.ψ p.1.1 p.1.2) := hW₀ p.1.1 p.1.2 hpa hW₀p
  have hsym : (Smat P.ψ p.1.1 p.1.2).IsSymm := Matrix.IsSymm.ext fun i j => hVK.symm j i
  have hsv : smatVar P p.1.1 p.1.2 = Smat P.ψ p.1.1 p.1.2 := smatVar_eq_of_isSymm P hsym
  rw [hsv]
  simp only [hsv] at hlowp
  have hL1 : (1 : ℝ) ≤ (p.1.2 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 p.2
  obtain ⟨hηΛ, hη0, hηa, hη1, hLW⟩ := MainCancel_window hW hL1 hεa hp.1 hp.2
  rw [← hzim p] at hηΛ hη0 hηa hη1
  have hW0 : (0 : ℝ) < p.1.1 := by linarith
  have hN : (0 : ℝ) < (p.1.2 : ℝ) ^ d := by positivity
  -- the identity and the solving step
  have hid := MainCancel_identity P Sig E n D 𝒬 hn4 hev hSigN h𝒬 p.1.1 p.1.2 (z p) hVK hη0
  have hm1 : ‖msc (z p)‖ ≤ 1 := (norm_msc_lt_one hη0).le
  have hmq : q / 2 ≤ (msc (z p)).im := by
    have := MainCancel.msc_im_ge hη0 hη1
    rw [hzre] at this; rw [hqdef]; linarith
  have hδg : ‖(∫ ω, green (hmat ω) (z p) 0 0 ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))) - msc (z p)‖ ≤
      q / 4 := hGp.trans hsmallp.le
  have hsol := MainCancel.solve _ _ _ _ (z p).im ((p.1.2 : ℝ) ^ d) q hη0 hN hq hm1 hmq hδg hid
  have hρ := MainCancel_rho_le P Sig' p (z p) hVK hη0 (n - 1) 𝒬 fun g hg =>
    ⟨(hShape.1.1 g (List.mem_append_right _ hg)).2.1, (hShape.2.2.2.1 g hg).1⟩
  -- `K = X + Σ_l X_l`
  set X : ℂ := ∑ x : Zd d p.1.2, sigMat Sig' (Smat P.ψ p.1.1 p.1.2) (z p) n 0 x with hX
  set Y : ℂ := ∑ l ∈ S, ∑ x : Zd d p.1.2, sigMat Sig (Smat P.ψ p.1.1 p.1.2) (z p) l 0 x with hY
  have hKXY : ∑ x : Zd d p.1.2, (sigMat Sig' (Smat P.ψ p.1.1 p.1.2) (z p) n 0 x +
      ∑ l ∈ S, sigMat Sig (Smat P.ψ p.1.1 p.1.2) (z p) l 0 x) = X + Y := by
    rw [Finset.sum_add_distrib, Finset.sum_comm]
  rw [hKXY] at hsol
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  set η : ℝ := (z p).im with hηdef
  set t' : ℝ := -T - c₀ / 2 - c₀ / 8 with ht'
  -- the lower orders
  have hYle : ‖Y‖ ≤ S.card * W ^ t' := by
    have h1 : ∀ l ∈ S, ‖∑ x : Zd d p.1.2, sigMat Sig (Smat P.ψ p.1.1 p.1.2) (z p) l 0 x‖ ≤
        W ^ t' := by
      intro l hl
      obtain ⟨hlI, -⟩ := Finset.mem_filter.1 hl
      have hl4 : (4 : ℝ) ≤ l := by exact_mod_cast (Finset.mem_Ico.1 hlI).1
      refine (hlowp l hl).trans ?_
      have hLτ : L ^ τ ≤ W ^ (c₀ / 16) := by
        calc L ^ τ ≤ (W ^ ((2 + b) / 2)) ^ τ := Real.rpow_le_rpow (by linarith) hLW hτ.le
          _ = W ^ (c₀ / 16) := by rw [← Real.rpow_mul hW0.le, hτb]
      calc L ^ τ * η * W ^ (-(((l : ℝ) - 2) * d / 2))
          ≤ W ^ (c₀ / 16) * W ^ (ε - a) * W ^ (-(((l : ℝ) - 2) * d / 2)) := by gcongr
        _ = W ^ (c₀ / 16 + (ε - a) + (-(((l : ℝ) - 2) * d / 2))) := by
            rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
        _ ≤ W ^ t' := Real.rpow_le_rpow_of_exponent_le hW (by rw [ht']; nlinarith)
    calc ‖Y‖ ≤ ∑ l ∈ S, ‖∑ x : Zd d p.1.2, sigMat Sig (Smat P.ψ p.1.1 p.1.2) (z p) l 0 x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _l ∈ S, W ^ t' := Finset.sum_le_sum h1
      _ = S.card * W ^ t' := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the remainder
  have hEsum := List.sum_le_length_nsmul _ _ (by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    exact hEp g hg)
  rw [List.length_map, nsmul_eq_mul] at hEsum
  set BR := W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-((d : ℝ) / 2)) with hBR
  set BA := W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-(((n : ℝ) - 3) * d / 2)) with hBA
  set BA2 := W ^ δ * L ^ d * (L ^ 2 / W ^ 2) ^ 2 * W ^ (-(((n : ℝ) - 1) * d / 2)) with hBA2
  set BE := W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-(((D : ℝ) - 3) * d / 2)) with hBE
  set BE1 := W ^ δ * L ^ (2 * d + 2) * W ^ (-(((D : ℝ) - 3) * d / 4)) with hBE1
  have hA1 : W ^ δ * L ^ d * (L ^ 2 / W ^ 2 * W ^ (-(((n : ℝ) - 3) * d / 2)) +
      (L ^ 2 / W ^ 2) ^ 2 * W ^ (-(((n : ℝ) - 1) * d / 2))) = BA + BA2 := by
    rw [hBA, hBA2]; ring
  have hρle : ‖∑ a, ∑ b, ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
      ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig' p.1.1 p.1.2 (z p))
        ![a, b, b] ω ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))).sum‖ ≤
      BR + (BA + BA2) + BA + cntE * BE1 + BE := by
    rw [← hA1]
    linarith [hRp.1, hRp.2, hZp.1, hZp.2]
  -- the exponents
  have hdn : (d : ℝ) / 2 ≤ ((n : ℝ) - 3) * d / 2 := by nlinarith
  have hn1 : ((n : ℝ) - 1) * d / 2 = T + d / 2 := by rw [hTdef]; ring
  have hD4 : (d : ℝ) / 2 ≤ ((D : ℝ) - 3) * d / 2 := by
    have : (1 : ℝ) ≤ (D : ℝ) - 3 := by rw [hD3]; have := Nat.cast_nonneg (α := ℝ) M; linarith
    nlinarith
  have hpow : ∀ e : ℝ, e ≤ t' → W ^ e ≤ W ^ t' := fun e he =>
    Real.rpow_le_rpow_of_exponent_le hW he
  have hT1 : η * ‖(∫ ω, green (hmat ω) (z p) 0 0 ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))) -
      msc (z p)‖ ≤ W ^ t' := by
    calc η * ‖(∫ ω, green (hmat ω) (z p) 0 0 ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))) - msc (z p)‖
        ≤ W ^ (ε - a) * W ^ (-((d : ℝ) / 2) + δ) :=
          mul_le_mul hηa hGp (norm_nonneg _) (by positivity)
      _ = W ^ (ε - a + (-((d : ℝ) / 2) + δ)) := (Real.rpow_add hW0 _ _).symm
      _ ≤ W ^ t' := hpow _ (by rw [ht']; linarith)
  have hNR := MainCancel_rpow1 (δ := δ) (x := (d : ℝ) / 2) hW0 hN hηΛ hηa
  have hNA := MainCancel_rpow1 (δ := δ) (x := ((n : ℝ) - 3) * d / 2) hW0 hN hηΛ hηa
  have hNE := MainCancel_rpow1 (δ := δ) (x := ((D : ℝ) - 3) * d / 2) hW0 hN hηΛ hηa
  have hNA2 := MainCancel_rpow2 (δ := δ) (x := ((n : ℝ) - 1) * d / 2) hW0 hN hηΛ
  have hNE1 := MainCancel_rpow3 (b := b) (δ := δ) (y := ((D : ℝ) - 3) * d / 4) d hW0 hL1 hη0.le
    hη1 hLW
  have hρ2 : η ^ 2 * ‖∑ a, ∑ b, ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
      ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig' p.1.1 p.1.2 (z p))
        ![a, b, b] ω ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))).sum‖ / L ^ d ≤
      (5 + cntE) * W ^ t' := by
    have h1 : η ^ 2 * ‖∑ a, ∑ b, ((𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).map fun g =>
        ∫ ω, g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig' p.1.1 p.1.2 (z p))
          ![a, b, b] ω ∂(gaussLaw (Smat P.ψ p.1.1 p.1.2))).sum‖ / L ^ d ≤
        η ^ 2 * (BR + (BA + BA2) + BA + cntE * BE1 + BE) / L ^ d := by gcongr
    have h2 : η ^ 2 * (BR + (BA + BA2) + BA + cntE * BE1 + BE) / L ^ d =
        η ^ 2 * BR / L ^ d + 2 * (η ^ 2 * BA / L ^ d) + η ^ 2 * BA2 / L ^ d +
          cntE * (η ^ 2 * BE1 / L ^ d) + η ^ 2 * BE / L ^ d := by ring
    have hcnt : (0 : ℝ) ≤ cntE := Nat.cast_nonneg _
    have eR : η ^ 2 * BR / L ^ d ≤ W ^ t' := hNR.trans (hpow _ (by rw [ht']; linarith))
    have eA : η ^ 2 * BA / L ^ d ≤ W ^ t' := hNA.trans (hpow _ (by rw [ht']; linarith))
    have eE : η ^ 2 * BE / L ^ d ≤ W ^ t' := hNE.trans (hpow _ (by rw [ht']; linarith))
    have eA2 : η ^ 2 * BA2 / L ^ d ≤ W ^ t' := hNA2.le.trans (hpow _ (by rw [ht']; linarith))
    have eE1 : η ^ 2 * BE1 / L ^ d ≤ W ^ t' := hNE1.trans (hpow _ (by rw [ht']; linarith))
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left eE1 hcnt
    linarith
  have hK := hsol.trans (mul_le_mul_of_nonneg_left (add_le_add
    (show 2 * η * _ ≤ 2 * W ^ t' by rw [mul_assoc]; linarith) hρ2) (by positivity))
  have hXle : ‖X‖ ≤ C * W ^ t' := by
    have h1 : ‖X‖ ≤ ‖X + Y‖ + ‖Y‖ := by
      have := norm_sub_le (X + Y) Y
      rwa [add_sub_cancel_right] at this
    rw [hC]
    have e : 32 / q ^ 4 * (2 * W ^ t' + (5 + cntE) * W ^ t') =
        32 / q ^ 4 * (2 + 5 + cntE) * W ^ t' := by ring
    nlinarith
  calc ‖X‖ ≤ C * W ^ t' := hXle
    _ ≤ W ^ (c₀ / 8) * W ^ t' := mul_le_mul_of_nonneg_right hbigp (by positivity)
    _ = W ^ (-T - c₀ / 2) := by rw [← Real.rpow_add hW0, ht']; ring_nf

/-! ## [I, Lemma 5.11] -/

/-- **[I, Lemma 5.11]** under `H(n − 1)`, `n`-th order `T`-equations with one `Σ_n = E` for every
`D > n` and the local law `localLawTExpStmt'`: for `0 < c₀ < d/4` there are `c > 0` and `ε₀ > 0`
such that for `0 < ε ≤ ε₀` and `|E'| < 2`, along the sizes `L_n` of [I, (5.39)] and at
`z_n = E' + i W^{2+ε}/L_n²`, `|Σ_x Σ_n(0, x)(z_n)| ≤ W^{-(n-2)d/2 - c}` ([I, (5.40)]). -/
def Graphs.G13.mainCancelStmt : Prop :=
  localLawTExpStmt' →
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ), 4 ≤ n →
    ∀ (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec),
      HWith d (smatVar P) Strat Sig (n - 1) →
      (∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D)) →
      ∀ c₀ : ℝ, 0 < c₀ → c₀ < d / 4 → ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ E' : ℝ, |E'| < 2 →
          ∀ᶠ p in G13.windowFilter d n c₀,
            ‖∑ x : Zd d p.1.2, sigMat (Function.update Sig n E) (smatVar P p.1.1 p.1.2)
                ((E' : ℂ) + Complex.I * (((p.1.1 : ℝ) ^ (2 + ε) / (p.1.2 : ℝ) ^ 2 : ℝ) : ℂ))
                n 0 x‖ ≤
              (p.1.1 : ℝ) ^ (-(((n : ℝ) - 2) * d / 2) - c)

/-- **[I, Lemma 5.11]**, with `c = c₀/2` and `ε₀ = c₀/8`. At an odd order `Σ_n = 0`
(`G13.shape_odd_nil`). At an even order the expectation of [I, (5.44)], summed over `𝔞, 𝔟`, is
evaluated by [I, (5.45)], (5.46), (5.49) and `E Q = 0`; the graphs of `R`, `A`, `Err` are bounded
by [I, Lemma 5.12] under the local law at order `n − 1`, `E G₀₀ − m` by the local law at `(0, 0)`,
the lower orders by [I, (1.27)], and the identity is solved for `Σ_x Σ_n(0, x)` as in
[I, (5.52)–(5.53)], with `Im m(z_n) ≥ (1 − E'²/4)/2`. -/
theorem Graphs.G13.mainCancel : Graphs.G13.mainCancelStmt := by
  intro hLL d hd P Strat n hn4 Sig E 𝒬n hH hT c₀ hc₀ hc₀d
  refine ⟨c₀ / 2, by positivity, c₀ / 8, by positivity, fun ε hε hεle E' hE' => ?_⟩
  rcases Nat.even_or_odd n with hev | hodd
  · exact MainCancel_even hLL d hd P Strat n hn4 hev Sig E 𝒬n hH hT c₀ hc₀ hc₀d ε hε hεle E' hE'
  · obtain ⟨hSN, -, h𝒬⟩ := hT (n + 1) (Nat.lt_succ_self n)
    have hE : E = [] := G13.shape_odd_nil hodd (hSN ▸ h𝒬.2.2.2.1)
    refine Eventually.of_forall fun p => ?_
    have h0 : ∀ x : Zd d p.1.2, sigMat (Function.update Sig n E) (smatVar P p.1.1 p.1.2)
        ((E' : ℂ) + Complex.I * (((p.1.1 : ℝ) ^ (2 + ε) / (p.1.2 : ℝ) ^ 2 : ℝ) : ℂ)) n 0 x =
        0 := by
      intro x
      simp [sigMat, hE, Expansion.val]
    simp only [h0, Finset.sum_const_zero, norm_zero]
    positivity

end RBM8D
