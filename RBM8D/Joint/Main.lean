import RBM8D.Joint.Chain
import RBM8D.Joint.Remainder
import RBM8D.Joint.Struct
import RBM8D.TExp.Closure
import RBM8D.TExp.Second
import RBM8D.LocalLaw.Primed
import RBM8D.Bound.Doubly
import RBM8D.Bound.GraphSum
import RBM8D.Deloc.Defs
import RBM8D.LocalLaw.Bridge

/-!
# The joint induction and the local law

[I, §5.1, §5.5, Theorem 2.1, §8] and [II, Theorem 3.7, Corollary 3.8, §6.1].

* `solve`: [II, Corollary 3.8] = [I, Lemma 5.13] for every dimension and every variance family
  (`solveStmt`), from the five statements of the solution ([II, (6.1)–(6.3)]).
* `G14.jointH_of_parts`: the joint induction [II, Theorem 3.7] from the `T`-equation, the
  self-energy step and `solveStmt`.
* `G14.family_of_jointH`: the family of `T`-expansions of every order `n ≥ 2` and every error
  order `D ≥ n + 2` from `H(n)`.
* `G14.localLaw_of_tExp`: the local law [I, Theorem 1.4], (1.19) (`LocalLawStmt`) from
  [II, Theorem 3.6] in the form `localLawTExpStmt'` at the order `n = ⌈2/c₁⌉ + 2`.
-/

noncomputable section

open MeasureTheory Filter Complex

namespace RBM8D

open Graphs

/-- `Sig l` is a self-energy for `Sig` and for every family that agrees with `Sig` up to `l`. -/
private theorem G14_isSelfEnergy_congr (d : ℕ) (Svar : VarFamily d) (Sig Sig' : ℕ → Expansion 2)
    (l : ℕ) (h : ∀ k ≤ l, Sig' k = Sig k) :
    IsSelfEnergy d Svar Sig l → IsSelfEnergy d Svar Sig' l := by
  have hU : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ) (N : ℕ),
      N ≤ l → sigUpTo Sig' S z N = sigUpTo Sig S z N := by
    intro ι _ _ S z N
    induction N with
    | zero => intro _; rfl
    | succ N ih =>
      intro hN
      simp only [sigUpTo, ih (by omega), h N (by omega)]
  have hm : ∀ (W L : ℕ) [NeZero L] (z : ℂ),
      sigMat Sig' (Svar W L) z l = sigMat Sig (Svar W L) z l := fun W L _ z => by
    simp only [sigMat, hU (Svar W L) z l le_rfl, h l le_rfl]
  rintro ⟨hsh, hsy, hbd⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h l le_rfl]; exact hsh
  · unfold SelfEnergySymm
    simp only [hm]
    exact hsy
  · unfold SelfEnergyBound
    simp only [hm]
    exact hbd

/-- **[II, Corollary 3.8] = [I, Lemma 5.13]** from the five statements of the solution
([II, (6.1)–(6.3)]): the `T`-expansion with error order `D > n` is `G14.solveRec` with the
`⌈D/2⌉`-fold iteration and the remainder of `G14.remainderStmt`. -/
theorem G14.solve_of_parts (hR : G14.remainderStmt) (hI : G14.solveRec_identityStmt)
    (hS : G14.solveRec_structStmt) (hC : G14.solveRec_coherentStmt)
    (hA : G14.solveRec_agreeStmt) : ∀ (d : ℕ) (Svar : VarFamily d), solveStmt d Svar := by
  intro d Svar n hn Sig E 𝒬n hTE hAg hSE
  classical
  have hE : SelfEnergyShape n E := by
    have := hSE.1
    rwa [Function.update_self] at this
  have hrem : ∀ D, n < D → ∃ Rem : Expansion 3,
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
        modelAdm Ω ι PF Dt → (∀ ω, SigConsistent (Function.update Sig n E) (n + 1) (Dt ω)) →
        ∀ (e : Fin 3 → ι) (ω : Ω),
          Rem.valR PF Dt e ω =
            ∑ x, (((Dt ω).Theta * sigTilde n E (Dt ω)) ^ ((D + 1) / 2 + 1)) (e 0) x *
              tGraph.valR PF Dt ![x, e 1, e 2] ω) ∧
      (⟨[], [], [], Rem⟩ : TRec).Shape n n D ∧ (⟨[], [], [], Rem⟩ : TRec).Def63 :=
    fun D hD => hR n hn Sig E D ((D + 1) / 2) hD (by omega) (hTE D hD).2.2.2.2.1 hE
  let Rem : ℕ → Expansion 3 := fun D => if h : n < D then Classical.choose (hrem D h) else []
  have hRem : ∀ D (h : n < D), Rem D = Classical.choose (hrem D h) := fun D h => by simp [Rem, h]
  refine ⟨fun D => G14.solveRec n ((D + 1) / 2) (𝒬n D) (Rem D), fun D hD => ?_⟩
  obtain ⟨hsig, hse, hst⟩ := hTE D hD
  have hspec := Classical.choose_spec (hrem D hD)
  rw [← hRem D hD] at hspec
  obtain ⟨hval, hsh, hdef⟩ := hspec
  have hval' := hval
  rw [← hsig] at hval'
  obtain ⟨hstr, hdef'⟩ := hS n hn Sig D ((D + 1) / 2) (𝒬n D) (Rem D) hD (by omega) hst hsh hdef
  obtain ⟨hcoh, hcpm⟩ := hC n hn Sig D ((D + 1) / 2) (𝒬n D) (Rem D) hD (by omega) hst
  have hid := hI n hn Sig D ((D + 1) / 2) (𝒬n D) (Rem D) hD (by omega) hst hval'
  rw [hsig] at hid
  refine ⟨⟨fun k hk4 hkn hke => ?_, hD, hid, fun k hk4 hkn hke => ?_, hstr, hdef'⟩, hcoh, hcpm,
    fun D' hDD' => ?_⟩
  · rcases Nat.lt_or_ge k n with hkn' | hkn'
    · exact G14_isSelfEnergy_congr d Svar Sig _ k
        (fun j hj => Function.update_of_ne (by omega) _ _) (hse k hk4 (by omega) hke)
    · obtain rfl : k = n := le_antisymm hkn hkn'
      exact hSE
  · rcases Nat.lt_or_ge k n with hkn' | hkn'
    · rw [Function.update_of_ne (by omega)]
      exact hst.2.2.1 k hk4 (by omega) hke
    · obtain rfl : k = n := le_antisymm hkn hkn'
      rw [Function.update_self]
      exact hE
  · have hD' : n < D' := lt_of_lt_of_le hD hDD'
    obtain ⟨hval2, hsh2, -⟩ := (hRem D' hD') ▸ Classical.choose_spec (hrem D' hD')
    refine hA n hn Sig D D' _ _ (𝒬n D) (𝒬n D') (Rem D) (Rem D') hD hDD' (by omega) (by omega)
      hst (hTE D' hD').2.2 (hAg D D' hD hDD') (fun g hg => hsh.2.2.2.2 g hg) (fun g hg => ?_)
    have := hsh2.2.2.2.2 g hg
    have : (D : ℤ) ≤ D' := by exact_mod_cast hDD'
    omega

/-! ## The joint induction and the local law -/

/-- **[II, Theorem 3.7]** with one family of self-energies for all orders, from the three
statements of [II, Theorem 3.7, Lemma 3.9, Corollary 3.8]: `H(2)` (`h2`), the induction step
(`inductionStep_of_parts`) and the recursion (`jointH_of_step`). -/
theorem G14.jointH_of_parts (hT : tEquationStmt) {d : ℕ} (Svar : VarFamily d)
    (hS : selfEnergyStepStmt d Svar) (hV : solveStmt d Svar) :
    ∃ Strat : ℕ → ℕ → TRec → TEqRec, jointHStmt d Svar Strat := by
  obtain ⟨Strat, hstep⟩ := inductionStep_of_parts d Svar hT hS hV
  exact ⟨Strat, jointH_of_step d Svar Strat ⟨fun _ => [], h2 d Svar Strat _⟩ hstep⟩

/-- From `H(n)` for every `n ≥ 2` over one family `Sig`: for every `n ≥ 2` and every error order
`D ≥ n + 2` an `n`-th order `T`-expansion with `D`-th order error over `Sig` with the clauses
`TRec.Def63G11` (the record `𝒯 n D` of the family of `H(n)`). -/
theorem G14.family_of_jointH {d : ℕ} {Svar : VarFamily d} {Strat : ℕ → ℕ → TRec → TEqRec}
    (h : jointHStmt d Svar Strat) :
    ∃ Sig : ℕ → Expansion 2, ∀ n : ℕ, 2 ≤ n → ∀ D : ℕ, n + 2 ≤ D →
      ∃ 𝒯 : TRec, IsTExpansion d Svar Sig n D 𝒯 ∧ 𝒯.Def63G11 := by
  obtain ⟨Sig, hSig⟩ := h
  refine ⟨Sig, fun n hn D hD => ?_⟩
  obtain ⟨hSE, 𝒬, 𝒯, hF⟩ := hSig n hn
  have hT := (hF.1 n D hn le_rfl (by omega)).2.1
  exact ⟨𝒯 n D, ⟨hSE, hT⟩, TRec.def63G11_of_def63 _ hT.2.2.2.2⟩

/-- **[I, Theorem 1.4], (1.19)** from [II, Theorem 3.6] in the form `localLawTExpStmt'` and a
`T`-expansion of every order `n ≥ 2` and every error order `D ≥ n + 2` ([I, §8], proof of
Theorem 1.4): with `c₀' = min(c₀, 1/3)`, `c₁' = min(c₁, 1/3)`, `c₀ᵀ = 1` and
`n = ⌈2/c₁⌉ + 2`, every `(W, L) ∈ adm(c₀, c₁)` lies in `adm(c₀', c₁')` and satisfies
[II, (3.15)]; the stochastic domination at the exponent `D/c₁` gives the probability bound
`W^{-D/c₁} ≤ L^{-D}`, and `L ≥ ⌈W₀^{1/c₁}⌉` gives `W ≥ L^{c₁} ≥ W₀`. -/
theorem G14.localLaw_of_tExp (hLL : localLawTExpStmt')
    (hfam : ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ n : ℕ, 2 ≤ n → ∀ D : ℕ, n + 2 ≤ D →
      ∃ (Sig : ℕ → Expansion 2) (𝒯 : TRec), IsTExpansion d (smatVar P) Sig n D 𝒯 ∧
        𝒯.Def63G11) :
    LocalLawStmt := by
  intro d hd P c₀ c₁ κ hc₀ hc₁ hκ ε τ D hε hτ hD
  set c₀' : ℝ := min c₀ (1 / 3) with hc₀'
  set c₁' : ℝ := min c₁ (1 / 3) with hc₁'
  set n : ℕ := ⌈2 / c₁⌉₊ + 2 with hn
  have hc₀'p : 0 < c₀' := lt_min hc₀ (by norm_num)
  have hc₁'p : 0 < c₁' := lt_min hc₁ (by norm_num)
  have hsum : c₀' + c₁' < 1 := by
    have := min_le_right c₀ (1 / 3 : ℝ)
    have := min_le_right c₁ (1 / 3 : ℝ)
    linarith
  have hSD := hLL d hd P c₀' c₁' κ ε 1 hc₀'p hc₁'p hsum hκ hε one_pos n
    (hfam d hd P n (by omega))
  have hev := hSD τ hτ (D / c₁) (div_pos hD hc₁)
  simp only [llFilter, admFilterL, admFilter] at hev
  rw [Filter.eventually_inf_principal, Filter.eventually_comap, inf_comm,
    Filter.eventually_inf_principal, Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨W₀, hW₀⟩ := hev
  refine ⟨max 2 ⌈(W₀ : ℝ) ^ c₁⁻¹⌉₊, fun p hL hadm x y => ?_⟩
  obtain ⟨⟨W, L⟩, hL0⟩ := p
  simp only at hL hadm x y ⊢
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_of_max_le_left hL
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0' : (0 : ℝ) ≤ L := by linarith
  have hLW : (L : ℝ) ^ c₁ ≤ W := hadm.1
  have hLc : 0 < (L : ℝ) ^ c₁ := Real.rpow_pos_of_pos (by linarith) _
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le hLc hLW
  have hW1 : (1 : ℝ) ≤ W := le_trans (Real.one_le_rpow hL1 hc₁.le) hLW
  -- `W ≥ W₀`
  have hWW₀ : W₀ ≤ W := by
    have h1 : (W₀ : ℝ) ^ c₁⁻¹ ≤ L :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_of_max_le_right hL)
    have h2 : ((W₀ : ℝ) ^ c₁⁻¹) ^ c₁ ≤ (L : ℝ) ^ c₁ :=
      Real.rpow_le_rpow (by positivity) h1 hc₁.le
    rw [Real.rpow_inv_rpow (by positivity) hc₁.ne'] at h2
    exact_mod_cast le_trans h2 hLW
  -- `(W, L) ∈ adm(c₀', c₁')`
  have hadm' : (W, L) ∈ adm c₀' c₁' := by
    refine ⟨le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (min_le_left _ _)) hLW,
      le_trans hadm.2 (Real.rpow_le_rpow_of_exponent_le hL1 ?_)⟩
    have := min_le_left c₀ (1 / 3 : ℝ)
    linarith
  -- [II, (3.15)] at order `n` with `c₀ᵀ = 1`
  have hthr : (⟨(W, L), hL0⟩ : SizeL) ∈ thrSet d n 1 := by
    change (L : ℝ) ^ 2 / (W : ℝ) ^ 2 ≤ (W : ℝ) ^ (((n : ℝ) - 1) * d / 2 - 1)
    have hLle : (L : ℝ) ≤ (W : ℝ) ^ c₁⁻¹ := by
      have := Real.rpow_le_rpow (by positivity) hLW (inv_nonneg.2 hc₁.le)
      rwa [Real.rpow_rpow_inv hL0' hc₁.ne'] at this
    have hL2W : (L : ℝ) ^ 2 ≤ (W : ℝ) ^ (2 * c₁⁻¹) := by
      rw [mul_comm, Real.rpow_mul hWpos.le, Real.rpow_two]
      exact pow_le_pow_left₀ hL0' hLle 2
    have hdiv : (L : ℝ) ^ 2 / (W : ℝ) ^ 2 ≤ (W : ℝ) ^ (2 * c₁⁻¹ - 2) := by
      rw [Real.rpow_sub hWpos, Real.rpow_two]
      exact div_le_div_of_nonneg_right hL2W (by positivity)
    refine le_trans hdiv (Real.rpow_le_rpow_of_exponent_le hW1 ?_)
    have hceil : 2 / c₁ ≤ (⌈2 / c₁⌉₊ : ℝ) := Nat.le_ceil _
    have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast hd
    have hnR : (n : ℝ) = (⌈2 / c₁⌉₊ : ℝ) + 2 := by rw [hn]; push_cast; ring
    have hinv : 2 * c₁⁻¹ = 2 / c₁ := by ring
    rw [hinv, hnR]
    nlinarith
  have hbd := hW₀ W hWW₀ (W, L) rfl hadm' ⟨(W, L), hL0⟩ rfl hthr
  refine le_trans (measure_mono ?_) (le_trans hbd (ENNReal.ofReal_le_ofReal ?_))
  · rintro ω ⟨E, hE, η, hη1, hη2, hlt⟩
    refine ⟨⟨⟨(E : ℂ) + (η : ℂ) * I, ?_⟩, x, y⟩, hlt⟩
    refine ⟨?_, by simpa using hη1, by simpa using hη2⟩
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    exact abs_lt.2 ⟨by linarith [hE.1], hE.2⟩
  · change (W : ℝ) ^ (-(D / c₁)) ≤ (L : ℝ) ^ (-D)
    calc (W : ℝ) ^ (-(D / c₁)) ≤ ((L : ℝ) ^ c₁) ^ (-(D / c₁)) :=
          Real.rpow_le_rpow_of_nonpos hLc hLW (by have := div_pos hD hc₁; linarith)
      _ = (L : ℝ) ^ (-D) := by
          rw [← Real.rpow_mul hL0']
          congr 1
          field_simp

/-- **[II, Corollary 3.8] = [I, Lemma 5.13]**: for every dimension `d` and every variance family
the `n`-th order `T`-equation with error order `D` yields the `T`-expansion of error order `D`
(`solveStmt`), by the `⌈D/2⌉`-fold iteration of [II, (3.5)] ([II, (6.1)–(6.3)]). -/
theorem solve : ∀ (d : ℕ) (Svar : VarFamily d), solveStmt d Svar :=
  G14.solve_of_parts G14.remainder_stmt G14.solveRec_identity G14.solveRec_struct
    G14.solveRec_coherent G14.solveRec_agree

section Instances

end Instances

end RBM8D

end
