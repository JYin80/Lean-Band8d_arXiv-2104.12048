module

public import RBM8D.GlobalExp.RunOtimes
public import Batteries.Tactic.OpenPrivate
public import RBM8D.GlobalExp.TerminationC2
public import RBM8D.GlobalExp.GlobalGoodB
public import RBM8D.GlobalExp.Termination
public import RBM8D.TExp.Second
public import RBM8D.GlobalExp.RunCompare
import all RBM8D.GlobalExp.TerminationC2
import all RBM8D.GlobalExp.GlobalGoodB
import all RBM8D.GlobalExp.Termination
import all RBM8D.TExp.Second
import all RBM8D.GlobalExp.RunCompare

@[expose] public section

/-!
# The invariant of a run and the run kinds on the output graphs of the selector

For a family `𝔈` of `Q`-expansions of [II, Lemma 4.15] (`QExpFamilyStmt`), a cutoff order `n ≥ 3`
and an `(n - 1)`-th order `T`-expansion `𝒯` with error order `D`, on the output graphs of the run of
[II, Strategy 6.6] driven by the selector `TerminationC_sel` from the graphs of `A` and `Q` of the
second order `T`-expansion ([II, Lemma 6.8]):

* `RunExports.selRun_exports`: an output graph of scaling order `≤ D` has the invariant of a run
  `TerminationC_RI`; every output graph has the run kinds `Graph.RunKinds (n - 1)` (no
  `Θ^{(n)}_err` edge, no ghost edge, no auxiliary edge, and `Θ` labels with entries even in
  `[4, n - 1]`, [II, Def 3.2 (2)]); an output graph of the class `Graph.LeafDet` of scaling order
  `≤ D` that is a `⊕/⊖`-recollision graph is of the class `Graph.LeafR` ([II, Def 6.3 (1)]);
* `RunExports.selRun_labelFree_ord`: an output graph without labels has scaling order `≥ 3`;
* `RunExports.selRun_pmBlock_ord`: an output graph without labels of scaling order `≤ D` with `⊕`,
  `⊖` in one dotted block has scaling order `≥ 5` ([II, Def 6.3 (1)]).

Every graph of the run is an output of scaling order `> D` (the class `Err` of [II, Def 6.3]) or a
graph of the run with a rank that every step lowers; the graphs of the run of scaling order `≤ D`
that are outputs are normal regular and carry the invariant of a run. The run kinds pass along
every step (`TerminationK_step`).

The output graphs of order `> D` are not covered by the first item: the substituted graphs of
`Err` may carry a `P` label.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private TerminationC2_Hyp TerminationC2_LF TerminationC2_ri_lf TerminationC2_ri_of
  TerminationC2_qGraph_labels TerminationC2_out_high TerminationC2_piece TerminationC2_Host
  TerminationC2_Good TerminationC2_M TerminationC2_R TerminationC2_rk TerminationC2_rk_lt_a
  TerminationC2_rk_lt_mu TerminationC2_rk_lt_b TerminationC2_rk_lt_c TerminationC2_rk_le_c
  TerminationC2_self_mem_oDotT TerminationC2_noLabDot_of_wf TerminationC2_labels_chain
  TerminationC2_loc TerminationC2_dropDot TerminationC2_lf_reorder TerminationC2_lf_dup
  TerminationC2_lf_drop TerminationC2_lf_coeff TerminationC2_not_lf_of_form
  TerminationC2_not_lf_of_q TerminationC2_reorder_lf_rev TerminationC2_host_lf
  TerminationC2_NuStep TerminationC2_NuStep.coeff TerminationC2_NuStep.dup
  TerminationC2_NuStep.drop TerminationC2_NuStep.labelFree TerminationC2_oDotT_chain
  TerminationC2_PStep TerminationC2_PStep.lf_chain TerminationC2_reorder_normal_rev
  TerminationC2_host_normal TerminationC2_normal_of TerminationC2_mem_eraseIdx
  TerminationC2_tSubst_runKinds TerminationC2_h2_invRun TerminationC2_runKinds_mono
  TerminationC2_runKinds_of_tKinds from RBM8D.GlobalExp.TerminationC2
open private GlobalGoodB_dotExcess_zero GlobalGoodB_oDot_label from RBM8D.GlobalExp.GlobalGoodB
open private Termination_inv1 Termination_not_qGraph from RBM8D.GlobalExp.Termination
open private h2Rec_struct from RBM8D.TExp.Second
open private RunCompare_def63_leaf RunCompare_def63_Q RunCompare_q0_out
  from RBM8D.GlobalExp.RunCompare

/-! ## Every step of the run gives outputs of order `> D` or graphs of the run -/

section Key

/-- An output of the run of scaling order `> D` (the class `Err` of [II, Def 6.3]). -/
private def RunExports_Hi (n D : ℕ) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  TerminationC_Out n D g ∧ (D : ℤ) < g.2.ord

/-- **The `O_dot` forms of a substituted graph in the run** ([II, Lemma 6.5], [II, Lemma 6.8]):
each is an output of the run of scaling order `> D`, or a graph of the run of a rank below that of
the host at tier `1`. -/
private theorem RunExports_piece_out {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g.2.swapSolid).RunKinds (n - 1))
    {t : Tracked 3 (m + g.1)} (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    RunExports_Hi n D ⟨t.nOut, t.g⟩ ∨ ∃ r', r' < TerminationC2_rk 1
      (runMu n (H.glue x y₁ y₂ (tVar true))) 1 0 ∧ TerminationC2_Good n D 𝒯 ⟨t.nOut, t.g⟩ r' := by
  obtain ⟨hN, hdf, hI, hK, hdc, hv, hT, hn0, hNL, hlab, hmu, hlb⟩ :=
    TerminationC2_piece hH hF hG hg hIt hKt ht
  have h0 : t.g.dotExcess = 0 := GlobalGoodB_dotExcess_zero hdf
  by_cases hL : t.g.LabelFree
  · exact Or.inr ⟨_, TerminationC2_rk_lt_mu (hmu hL), Or.inl ⟨⟨hN,
      TerminationC2_ri_lf hL hI hv hdc hT (fun h => absurd h0 h) hK, hL, hK⟩, rfl⟩⟩
  rcases hlb hL with ⟨hQs, hP, hQ⟩ | hD
  · by_cases hq : t.g.IsQGraph
    · exact Or.inr ⟨_, TerminationC2_rk_lt_a (by norm_num), Or.inr (Or.inl ⟨hN,
        TerminationC2_ri_of hI hv hdc hT hNL hlab hP hQ (fun h => absurd h0 h) hK, hq, hK, rfl⟩)⟩
    by_cases hD : (D : ℤ) < t.g.ord
    · exact Or.inl ⟨TerminationC2_out_high hN h0 hD hdc hI hn0 hNL hlab, hD⟩
    exact Or.inr ⟨_, TerminationC2_rk_lt_b (by norm_num), Or.inr (Or.inr (Or.inr
      ⟨m, H, x, y₁, y₂, g, t, hG, hQs, ht, rfl, hdc, hlab, hK, hI, hdf, hN,
        TerminationC2_ri_of hI hv hdc hT hNL hlab hP (fun h => absurd h hq)
          (fun h => absurd h0 h) hK, hL, hq, rfl⟩))⟩
  · exact Or.inl ⟨TerminationC2_out_high hN h0 hD hdc hI hn0 hNL hlab, hD⟩

/-- **The substituted graphs of Steps 2–3** ([II, (4.15)]): each is an output of the run of scaling
order `> D`, or a graph of the run of a rank below that of the host. -/
private theorem RunExports_subst_out {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g.2.swapSolid).RunKinds (n - 1)) :
    RunExports_Hi n D ⟨m + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ ∨ ∃ r', r' < TerminationC2_rk 1
      (runMu n (H.glue x y₁ y₂ (tVar true))) 2 0 ∧
      TerminationC2_Good n D 𝒯 ⟨m + g.1, H.glue x y₁ y₂ g.2.swapSolid⟩ r' := by
  by_cases hNn : ∃ C, (H.glue x y₁ y₂ g.2.swapSolid).Normal C
  · obtain ⟨C, hC⟩ := hNn
    rcases RunExports_piece_out hH hF hG hg hIt hKt (TerminationC2_self_mem_oDotT hC) with
      h | ⟨r', hr', hgood⟩
    · exact Or.inl h
    · exact Or.inr ⟨r', hr'.trans (TerminationC2_rk_lt_b (by norm_num)), hgood⟩
  · exact Or.inr ⟨_, TerminationC2_rk_lt_b (b := 1) (by norm_num), Or.inr (Or.inr (Or.inl
      ⟨m, H, x, y₁, y₂, g, hG, hg, hIt, hKt, Relation.ReflTransGen.refl, Or.inr rfl, hNn, hIt,
        hKt, rfl⟩))⟩

/-- **The outputs of a `Q`-expansion of Step 3** ([II, Lemma 6.5 (4)], [II, Lemma 4.15],
[II, Lemma 6.8]) at the label atom of an `O_dot` form `t` of a substituted graph of `Q` that is not
a `Q`-graph: every output graph is an output of the run of scaling order `> D`, or a graph without
labels with the invariant of a run and a smaller `runMu` than the host, or a normal regular
`Q`-graph with the invariant of a run and the run kinds. -/
private theorem RunExports_qexp {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g : Σ n₀ : ℕ, Graph 3 n₀} (hg : g ∈ 𝒯.Q) {t : Tracked 3 (m + g.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) (hdc : t.g.DoublyConnected)
    (hlab : t.g.labels.length ≤ 1) (hK : t.g.RunKinds (n - 1)) (hIt : t.g.InvRun D)
    {x' : Fin t.nOut} (hA : TerminationC_Adm n D 𝔈 ⟨t.nOut, t.g⟩ (.qexp x')) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 ⟨t.nOut, t.g⟩ (.qexp x'),
      RunExports_Hi n D s ∨
      (TerminationC2_LF n D s ∧ runMu n s.2 < runMu n (H.glue x y₁ y₂ (tVar true))) ∨
      ((∃ C, s.2.Normal C) ∧ TerminationC_RI n D s ∧ s.2.IsQGraph ∧ s.2.RunKinds (n - 1)) := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hK s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 _ _ (TerminationC_Adm.step hA) hIt s hs
  obtain ⟨hn, hT⟩ := hH
  obtain ⟨hD, ho2, ⟨ho1, ⟨C, hN⟩, hd, hL, hgs, hnr, hTD, hM, hst⟩, hI, hP⟩ := hG
  have hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63 :=
    ⟨hT.1, hT.2.2.2.1, hT.2.2.2.2⟩
  have hg' : g ∈ 𝒯.tSubst (n - 1) := by simp [TRec.tSubst, TRec.rhs, hg]
  obtain ⟨-, -, -, hform, hnQ, -, hcl⟩ := hA
  obtain ⟨C', hC'⟩ := hcl.1
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
  obtain ⟨⟨hbase, hcls, -, -⟩, -⟩ := hC' u hu
  have hn0 : u.nOut ≠ 0 := by
    intro h0
    have hfx := hbase.2.2.2.2.1
    rcases hf : u.f (.inr x') with a | j
    · rw [hf] at hfx; cases hfx
    · exact (Fin.cast h0 j).elim0
  have hTu : u.g.TensorDiffusive := by
    rcases hI' with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨-, -, -, h, -⟩
    · exact h
    · exact absurd h0 hn0
    · exact h
  have hv := TerminationB_inv_qexp 𝔈 hF hn hcore hL hN hd ho1 ho2 hI hTD hgs hnr hM hst hP g hg t
    ht x' hform hnQ u hu
  have hrow := ((globalGoodB' 𝔈 hF n D Sig 𝒯 m C H x y₁ y₂ hn hT hL hN hd ho1 ho2 hI hTD hgs hnr
    hM hst hP).2.2.1 g hg).2 t ht |>.2.2.2 x' hform hnQ u hu
  have hWF : ∀ c ∈ u.g.comps, c.WF := by
    rcases hcls with ⟨hPl, -⟩ | ⟨-, hCl⟩
    · exact fun c hc => (hPl c hc).2.2.2.2
    · exact fun c hc => (hCl c hc).2.2.2
  have hNL := TerminationC2_noLabDot_of_wf hWF
  have hlab' : u.g.labels.length ≤ 1 :=
    TerminationC2_labels_chain (a := ⟨t.nOut, t.g⟩) (b := ⟨u.nOut, u.g⟩)
      hbase.2.2.2.2.2.2 hlab
  have hdcu := hbase.2.2.2.2.2.1 hdc
  have hNu : ∃ C, u.g.Normal C := ⟨C', hbase.1⟩
  rcases hrow with ⟨h0, ⟨hLu, -, -⟩ | ⟨hQu, hspd, hql⟩ | ⟨hDu, -⟩⟩
  · refine Or.inr (Or.inl ⟨⟨hNu, TerminationC2_ri_lf hLu hI' hv hdcu hTu
      (fun h => absurd h0 h) hK', hLu, hK'⟩, ?_⟩)
    exact (substMu n D Sig 𝒯 m C H x y₁ y₂ hn hT hL hN hd ho1 ho2 hI hTD hgs hnr hM hst).2 g hg t
      ht x' _ hform hnQ hcl u hu hLu
  · obtain ⟨hl1, hP1, -⟩ := TerminationC2_qGraph_labels hQu
    exact Or.inr (Or.inr ⟨hNu, TerminationC2_ri_of hI' hv hdcu hTu hNL hl1 hP1
      (fun _ => ⟨hspd, hql⟩) (fun h => absurd h0 h) hK', hQu, hK'⟩)
  · exact Or.inl ⟨TerminationC2_out_high hNu h0 hDu hdcu hI' hn0 hNL hlab', hDu⟩

/-- **The steps at a graph without labels with the invariant of a run** ([II, Lemma 6.8]): every
graph of the step is an output of the run of scaling order `> D` or a graph of the run of smaller
rank. -/
private theorem RunExports_key_lf {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hg : TerminationC2_LF n D g) {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, RunExports_Hi n D s ∨ ∃ r', r' <
      TerminationC2_rk 1 (runMu n g.2) 2 (TerminationC_nu g) ∧ TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hg.2.2.2 s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 g _ (TerminationC_Adm.step hA) hg.2.1.1 s hs
  obtain ⟨n₀, Γ⟩ := g
  cases l with
  | loc o x =>
    rcases TerminationC2_loc hH hF h𝒯 hA hg s hs with ⟨hs', hmu⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inr ⟨_, TerminationC2_rk_lt_mu hmu, Or.inl ⟨hs', rfl⟩⟩
    · exact Or.inr ⟨_, TerminationC2_rk_lt_a (by norm_num), Or.inr (Or.inl ⟨h1, h2, h3, h4, rfl⟩)⟩
  | dot => exact absurd hg.1 hA
  | dropDot Γ' =>
    obtain ⟨hN', hR', hK'', hlf, -, hmu⟩ := TerminationC2_dropDot hH hF h𝒯 hA hg.2.1 hg.2.2.2
    rw [List.mem_singleton.1 hs]
    exact Or.inr ⟨_, TerminationC2_rk_lt_mu hmu, Or.inl ⟨⟨hN', hR', hlf hg.2.2.1, hK''⟩, rfl⟩⟩
  | reorder Γ' =>
    have hnu := TerminationC_nu_reorder (𝒯 := 𝒯) hA s hs
    rw [List.mem_singleton.1 hs] at hnu ⊢
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_reorder hH hA.1 hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | xdotDup i =>
    have hnu := TerminationC_nu_xdotDup (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, ⟨hk, hx, hy, -⟩, -, -⟩ := hA
    have e : s = ⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩ := by
      rw [List.mem_singleton.1 hs]
      simp only [List.getElem?_eq_getElem hi, Option.toList_some]
    subst e
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_dup hH ⟨i, hi⟩ hk hx hy hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only [Fin.getElem_fin] at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | xdotDrop i j =>
    have hnu := TerminationC_nu_xdotDrop (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, hj, ⟨hij, hc, hk, hx, hy, -⟩, -, -⟩ := hA
    rw [List.mem_singleton.1 hs] at hnu ⊢
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_drop hH ⟨i, hi⟩ ⟨j, hj⟩ hij hc hk hx hy hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    have hnu := TerminationC_nu_coeffNorm (𝒯 := 𝒯) hA s hs
    rw [List.mem_singleton.1 hs] at hnu ⊢
    obtain ⟨hs', hmu⟩ := TerminationC2_lf_coeff hH hg
    refine Or.inr ⟨_, ?_, Or.inl ⟨hs', rfl⟩⟩
    simp only at hmu ⊢
    rw [hmu]
    exact TerminationC2_rk_lt_c hnu
  | subst m H x y₁ y₂ =>
    obtain ⟨he, hD, hn', hP⟩ := hA
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    obtain ⟨-, ⟨hI, hv, -⟩, hL, -⟩ := hg
    obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
    have h0 := GlobalGoodB_dotExcess_zero hP.2.2.1
    have hPl : (H.glue x y₁ y₂ (tVar true)).Plain := by
      rcases hv.1 with h | h
      · exact h
      · rw [Graph.paperOrd_of_dotExcess h0] at h
        exact absurd h hD
    have hG : TerminationC2_Host n D H x y₁ y₂ := ⟨hD, hn', hP, hB, hPl⟩
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hs
    obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 hg'
    rcases RunExports_subst_out hH hF hG hg'' hI' hK' with h | ⟨r', hr', hgood⟩
    · exact Or.inl h
    · exact Or.inr ⟨r', hr'.trans_le (by
        rcases Nat.eq_zero_or_pos (TerminationC_nu ⟨m + 1, H.glue x y₁ y₂ (tVar true)⟩) with
          h | h
        · rw [h]
        · exact (TerminationC2_rk_lt_c h).le), hgood⟩
  | qexp x => exact absurd hg.2.2.1 (TerminationC2_not_lf_of_form hA.2.2.2.1)

/-- **The steps at a `Q`-graph** with the invariant of a run: every graph of the step is a graph of
the run of smaller rank. -/
private theorem RunExports_key_qb {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hN : ∃ C, g.2.Normal C) (hR : TerminationC_RI n D g) (hQ : g.2.IsQGraph)
    (hK : g.2.RunKinds (n - 1)) {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, RunExports_Hi n D s ∨ ∃ r', r' <
      TerminationC2_rk 0 (runMu n g.2) 0 0 ∧ TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  have hnl := TerminationC2_not_lf_of_q hQ
  cases l with
  | loc o x => exact absurd hA.2.2.2.1 hnl
  | dot => exact absurd hN hA
  | dropDot Γ' =>
    obtain ⟨hN', hR', hK', -, hq, hmu⟩ := TerminationC2_dropDot hH hF h𝒯 hA hR hK
    rw [List.mem_singleton.1 hs]
    exact Or.inr ⟨_, TerminationC2_rk_lt_mu hmu, Or.inr (Or.inl ⟨hN', hR', hq hQ, hK', rfl⟩)⟩
  | reorder Γ' =>
    exact absurd (TerminationC2_reorder_lf_rev hA.1 (TerminationC2_host_lf hA.2.2)) hnl
  | xdotDup i => exact absurd hA.2.2.1.1 hnl
  | xdotDrop i j => exact absurd hA.2.2.2.1.1 hnl
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm => exact absurd hA.1.1 hnl
  | subst m H x y₁ y₂ =>
    exact absurd (TerminationC2_host_lf ⟨m, H, x, y₁, y₂, hA.1, hA.2.2.2⟩) hnl
  | qexp x => exact absurd hQ hA.2.2.2.2.1

/-- **The steps at a substituted graph of Steps 2–3 that is not normal regular**: every graph of the
step is an output of the run of scaling order `> D` or a graph of the run of smaller rank. -/
private theorem RunExports_key_raw {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g' : Σ n₀ : ℕ, Graph 3 n₀} (hg' : g' ∈ 𝒯.tSubst (n - 1))
    (hIt : (H.glue x y₁ y₂ g'.2.swapSolid).InvRun D)
    (hKt : (H.glue x y₁ y₂ g'.2.swapSolid).RunKinds (n - 1)) {X : Σ n₀ : ℕ, Graph 3 n₀}
    (hch : Relation.ReflTransGen TerminationC2_NuStep ⟨m + g'.1, H.glue x y₁ y₂ g'.2.swapSolid⟩ X)
    (hlf : X.2.LabelFree ∨ X = ⟨m + g'.1, H.glue x y₁ y₂ g'.2.swapSolid⟩)
    (hNn : ¬ ∃ C, X.2.Normal C) (hI : X.2.InvRun D) (hK : X.2.RunKinds (n - 1))
    {l : TerminationC_Loc X.1} (hA : TerminationC_Adm n D 𝔈 X l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 X l, RunExports_Hi n D s ∨ ∃ r', r' <
      TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 1 (TerminationC_nu X) ∧
      TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  have hK' := TerminationK_step hF h𝒯 hA hK s hs
  have hI' := invRun_step n D Sig 𝒯 hH.1 hH.2 X _ (TerminationC_Adm.step hA) hI s hs
  have hraw : ∀ Γ' : Graph 3 X.1, TerminationC2_NuStep X ⟨X.1, Γ'⟩ → Γ'.LabelFree →
      (¬ ∃ C, Γ'.Normal C) → s = ⟨X.1, Γ'⟩ →
      TerminationC_nu ⟨X.1, Γ'⟩ < TerminationC_nu X →
      RunExports_Hi n D s ∨ ∃ r', r' <
        TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 1 (TerminationC_nu X) ∧
        TerminationC2_Good n D 𝒯 s r' := by
    intro Γ' hst hL' hN' hs' hnu
    subst hs'
    exact Or.inr ⟨_, TerminationC2_rk_lt_c hnu, Or.inr (Or.inr (Or.inl ⟨m, H, x, y₁, y₂, g', hG,
      hg', hIt, hKt, hch.tail hst, Or.inl hL', hN', hI', hK', rfl⟩))⟩
  obtain ⟨n₀, Γ⟩ := X
  cases l with
  | loc o x => exact absurd hA.2.2.1 hNn
  | dot =>
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hs
    rcases hlf with hL | he
    · obtain ⟨t, ht, hrel⟩ := TerminationC2_oDotT_chain hch t' ht'
      have hLG := TerminationC2_NuStep.labelFree hch hL
      have hLt : t.g.LabelFree := by
        intro c hc
        by_contra hne
        obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hne
        obtain ⟨c₀, hc₀, w, hw, -⟩ := GlobalGoodB_oDot_label ht hc hl
        rw [hLG c₀ hc₀] at hw
        cases hw
      obtain ⟨hN, hdf, hIt', hKt', hdc, hv, hT, -, -, -, hmu, -⟩ :=
        TerminationC2_piece hH hF hG hg' hIt hKt ht
      have h0 : t.g.dotExcess = 0 := GlobalGoodB_dotExcess_zero hdf
      obtain ⟨hLF', hmu'⟩ := TerminationC2_PStep.lf_chain hH hrel
        ⟨hN, TerminationC2_ri_lf hLt hIt' hv hdc hT (fun h => absurd h0 h) hKt', hLt, hKt'⟩
      refine Or.inr ⟨_, TerminationC2_rk_lt_mu ?_, Or.inl ⟨hLF', rfl⟩⟩
      simp only at hmu'
      rw [hmu']
      exact hmu hLt
    · simp only [Sigma.mk.inj_iff] at he
      obtain ⟨rfl, he⟩ := he
      cases eq_of_heq he
      rcases RunExports_piece_out hH hF hG hg' hIt hKt ht' with h | ⟨r', hr', hgood⟩
      · exact Or.inl h
      · exact Or.inr ⟨r', hr'.trans_le TerminationC2_rk_le_c, hgood⟩
  | dropDot Γ' => exact absurd hA.2.1 hNn
  | reorder Γ' =>
    exact absurd (TerminationC2_reorder_normal_rev hA.1 (TerminationC2_host_normal hA.2.2)) hNn
  | xdotDup i =>
    have hnu := TerminationC_nu_xdotDup (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, ⟨hk, hx, hy, -⟩, hcell, -⟩ := hA
    have hL := hcell.1
    have e : s = ⟨n₀, ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩⟩ := by
      rw [List.mem_singleton.1 hs]
      simp only [List.getElem?_eq_getElem hi, Option.toList_some]
    have hst := TerminationC2_NuStep.dup Γ ⟨i, hi⟩ hk (hL _ (List.getElem_mem hi)) hx hy
    simp only [Fin.getElem_fin] at hst
    refine hraw _ hst (fun c hc => ?_) (fun ⟨C, hC⟩ => hNn ⟨_, TerminationC2_normal_of
      (fun c hc => ⟨c, List.mem_append_left _ hc, Or.inl rfl⟩) (fun c hc => ?_) hC⟩) e
      (by rw [← e]; exact hnu)
    · rcases List.mem_append.1 hc with hc | hc
      · exact hL c hc
      · rw [List.mem_singleton.1 hc]; exact hL _ (List.getElem_mem hi)
    · rcases List.mem_append.1 hc with hc | hc
      · exact ⟨c, hc, Or.inl rfl⟩
      · rw [List.mem_singleton.1 hc]; exact ⟨_, List.getElem_mem hi, Or.inl rfl⟩
  | xdotDrop i j =>
    have hnu := TerminationC_nu_xdotDrop (𝒯 := 𝒯) hA s hs
    obtain ⟨hi, hj, ⟨hij, hc, hk, hx, hy, -⟩, hcell, -⟩ := hA
    have hL := hcell.1
    have e : s = ⟨n₀, ⟨Γ.comps.eraseIdx j, Γ.coeff⟩⟩ := List.mem_singleton.1 hs
    have hst := TerminationC2_NuStep.drop Γ ⟨i, hi⟩ ⟨j, hj⟩ hij hc hk
      (hL _ (List.getElem_mem hi)) hx hy
    have hij' : i ≠ j := fun h => hij (Fin.ext h)
    refine hraw _ hst (fun c hc => hL c (List.mem_of_mem_eraseIdx hc))
      (fun ⟨C, hC⟩ => hNn ⟨_, TerminationC2_normal_of (fun c hcm => ?_)
        (fun c hc => ⟨c, List.mem_of_mem_eraseIdx hc, Or.inl rfl⟩) hC⟩) e
      (by rw [← e]; exact hnu)
    rcases TerminationC2_mem_eraseIdx hcm hj with h | rfl
    · exact ⟨c, h, Or.inl rfl⟩
    · refine ⟨Γ.comps[i], List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, hij', rfl⟩, ?_⟩
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hk, h⟩
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    have hnu := TerminationC_nu_coeffNorm (𝒯 := 𝒯) hA s hs
    have hL : Γ.LabelFree := hA.1.1
    set Γ' : Graph 3 n₀ :=
      ⟨Γ.comps, Γ.coeff * cm * MvPolynomial.X .mInv * cmb * MvPolynomial.X .mBarInv⟩ with hΓ'
    have e : s = ⟨n₀, Γ'⟩ := List.mem_singleton.1 hs
    have hL' : Γ'.LabelFree := fun c hc => hL c hc
    have hN' : ¬ ∃ C, Γ'.Normal C := by
      rintro ⟨C, hC⟩
      exact hNn ⟨_, TerminationC2_normal_of (Γ := Γ') (Γ' := Γ)
        (fun c hc => ⟨c, hc, Or.inl rfl⟩) (fun c hc => ⟨c, hc, Or.inl rfl⟩) hC⟩
    exact hraw Γ' (TerminationC2_NuStep.coeff Γ) hL' hN' e (by rw [← e]; exact hnu)
  | subst m' H' x' y₁' y₂' =>
    exact absurd (TerminationC2_host_normal ⟨m', H', x', y₁', y₂', hA.1, hA.2.2.2⟩) hNn
  | qexp x' => exact absurd hA.1 hNn

/-- **The steps at an `O_dot` form with labels of a substituted graph of `Q`**: every graph of the
step is an output of the run of scaling order `> D` or a graph of the run of smaller rank. -/
private theorem RunExports_key_lp {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) {m : ℕ} {H : Graph 3 m}
    {x y₁ y₂ : Atom 3 m} (hG : TerminationC2_Host n D H x y₁ y₂)
    {g' : Σ n₀ : ℕ, Graph 3 n₀} (hg' : g' ∈ 𝒯.Q) {t : Tracked 3 (m + g'.1)}
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g'.2.swapSolid)) (hdc : t.g.DoublyConnected)
    (hlab : t.g.labels.length ≤ 1) (hK : t.g.RunKinds (n - 1)) (hI : t.g.InvRun D)
    (hdf : t.g.DotFree) (hN : ∃ C, t.g.Normal C) (hL : ¬ t.g.LabelFree)
    {l : TerminationC_Loc t.nOut} (hA : TerminationC_Adm n D 𝔈 ⟨t.nOut, t.g⟩ l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 ⟨t.nOut, t.g⟩ l, RunExports_Hi n D s ∨ ∃ r', r' <
      TerminationC2_rk 1 (runMu n (H.glue x y₁ y₂ (tVar true))) 0 0 ∧
      TerminationC2_Good n D 𝒯 s r' := by
  intro s hs
  cases l with
  | loc o x => exact absurd hA.2.2.2.1 hL
  | dot => exact absurd hN hA
  | dropDot Γ' =>
    obtain ⟨⟨i, c, hc, hk, -, -⟩, -, -⟩ := hA
    exact absurd hk (hdf c (List.mem_of_getElem? hc))
  | reorder Γ' =>
    exact absurd (TerminationC2_reorder_lf_rev hA.1 (TerminationC2_host_lf hA.2.2)) hL
  | xdotDup i => exact absurd hA.2.2.1.1 hL
  | xdotDrop i j => exact absurd hA.2.2.2.1.1 hL
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm => exact absurd hA.1.1 hL
  | subst m' H' x' y₁' y₂' =>
    exact absurd (TerminationC2_host_lf ⟨m', H', x', y₁', y₂', hA.1, hA.2.2.2⟩) hL
  | qexp x' =>
    rcases RunExports_qexp hH hF h𝒯 hG hg' ht hdc hlab hK hI hA s hs with h | ⟨h1, h2⟩ | h
    · exact Or.inl h
    · exact Or.inr ⟨_, TerminationC2_rk_lt_mu h2, Or.inl ⟨h1, rfl⟩⟩
    · exact Or.inr ⟨_, TerminationC2_rk_lt_a (by norm_num), Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2.1,
        h.2.2.2, rfl⟩)⟩

/-- **Every step of a run driven by an admissible selector** ([II, Lemma 6.8]): at every graph of
the run that is not an output, the graph lies in `TerminationC_Dom`, and every graph of the step is
an output of scaling order `> D` or a graph of the run of smaller rank. -/
private theorem RunExports_key {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀}
    {ℓ : (g : Σ n₀ : ℕ, Graph 3 n₀) → TerminationC_Loc g.1}
    (hH : TerminationC2_Hyp n D Sig 𝒯) (hF : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds (n - 1)) (hℓ : AdmSelector n D 𝒯 𝔈 ℓ) :
    ∀ g r, TerminationC2_Good n D 𝒯 g r → ¬ TerminationC_Out n D g →
      TerminationC_Dom n D g ∧ ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g (ℓ g),
        RunExports_Hi n D s ∨ ∃ r', r' < r ∧ TerminationC2_Good n D 𝒯 s r' := by
  intro g r hg hO
  rcases hg with ⟨hLF, rfl⟩ | ⟨hN, hR, hQ, hK, rfl⟩ |
    ⟨m, H, x, y₁, y₂, g', hG, hg', hIt, hKt, hch, hlf, hNn, hI, hK, rfl⟩ |
    ⟨m, H, x, y₁, y₂, g', t, hG, hQs, ht, rfl, hdc, hlab, hK, hI, hdf, hN, hR, hL, hq, rfl⟩
  · have hD : TerminationC_Dom n D g := Or.inr hLF.2.1
    exact ⟨hD, RunExports_key_lf hH hF h𝒯 hLF (hℓ g hD hO).1⟩
  · have hD : TerminationC_Dom n D g := Or.inr hR
    exact ⟨hD, RunExports_key_qb hH hF h𝒯 hN hR hQ hK (hℓ g hD hO).1⟩
  · have hD : TerminationC_Dom n D g := Or.inl hNn
    exact ⟨hD, RunExports_key_raw hH hF h𝒯 hG hg' hIt hKt hch hlf hNn hI hK (hℓ g hD hO).1⟩
  · have hD : TerminationC_Dom n D ⟨t.nOut, t.g⟩ := Or.inr hR
    exact ⟨hD, RunExports_key_lp hH hF h𝒯 hG hQs ht hdc hlab hK hI hdf hN hL
      (hℓ _ hD hO).1⟩

end Key

/-! ## The graphs of the run -/

section Run

/-- The graphs of the run of `TerminationC_sel` ([II, Lemma 6.8]): outputs of scaling order `> D`
or graphs of the run with a rank, with the run kinds for the order `n - 1`. -/
private def RunExports_J (n D : ℕ) (𝒯 : TRec) (g : Σ n₀ : ℕ, Graph 3 n₀) : Prop :=
  (RunExports_Hi n D g ∨ ∃ r, TerminationC2_Good n D 𝒯 g r) ∧ g.2.RunKinds (n - 1)

/-- A graph of the run with a rank has the run kinds for the order `n - 1`. -/
private theorem RunExports_good_runKinds {n D : ℕ} {𝒯 : TRec} {g : Σ n₀ : ℕ, Graph 3 n₀}
    {r : TerminationC2_R} (h : TerminationC2_Good n D 𝒯 g r) : g.2.RunKinds (n - 1) := by
  rcases h with ⟨hLF, -⟩ | ⟨-, -, -, hK, -⟩ | ⟨m, H, x, y₁, y₂, g', -, -, -, -, -, -, -, -, hK, -⟩ |
    ⟨m, H, x, y₁, y₂, g', t, -, -, -, rfl, -, -, hK, -⟩
  · exact hLF.2.2.2
  · exact hK
  · exact hK
  · exact hK

/-- A normal regular graph of the run with a rank has the invariant of a run. -/
private theorem RunExports_good_ri {n D : ℕ} {𝒯 : TRec} {g : Σ n₀ : ℕ, Graph 3 n₀}
    {r : TerminationC2_R} (h : TerminationC2_Good n D 𝒯 g r) (hN : ∃ C, g.2.Normal C) :
    TerminationC_RI n D g := by
  rcases h with ⟨hLF, -⟩ | ⟨-, hR, -⟩ | ⟨m, H, x, y₁, y₂, g', -, -, -, -, -, -, hNn, -⟩ |
    ⟨m, H, x, y₁, y₂, g', t, -, -, -, rfl, -, -, -, -, -, -, hR, -⟩
  · exact hLF.2.1
  · exact hR
  · exact absurd hN hNn
  · exact hR

/-- **The inputs of the run are graphs of the run with a rank**: the graphs of `A` of the second
order `T`-expansion are normal regular without labels with the invariant of a run, those of `Q`
are normal regular `Q`-graphs with the invariant of a run. -/
private theorem RunExports_inputs {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hH : TerminationC2_Hyp n D Sig 𝒯) :
    ∀ g ∈ h2Rec.A ++ h2Rec.Q, ∃ r, TerminationC2_Good n D 𝒯 g r := by
  have hD : 2 < D := by have := hH.2.1; have := hH.1; omega
  have h2 := h2Rec_struct Sig D hD
  have hSh := h2.2.2.2.1
  have hDef := h2.2.2.2.2
  intro g hg
  have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q := by
    rcases List.mem_append.1 hg with h | h <;> simp [h]
  have h4 : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err := List.mem_append_left _ hRAQ
  obtain ⟨hN, hTK, -, hdc⟩ := hSh.1.1 g hRAQ
  obtain ⟨hT, h0, hNL, hlab⟩ := RunCompare_def63_leaf hDef g h4
  have hI := TerminationC2_h2_invRun D g hg
  have hv := TerminationB_inv_h2 n D hD g hg
  have hK : g.2.RunKinds (n - 1) :=
    TerminationC2_runKinds_mono (by have := hH.1; omega) (TerminationC2_runKinds_of_tKinds hTK)
  rcases List.mem_append.1 hg with hA | hQ
  · have hL := (hSh.2.2.1 g hA).1
    exact ⟨_, Or.inl ⟨⟨hN, TerminationC2_ri_lf hL hI hv hdc hT (fun h => absurd h0 h) hK, hL,
      hK⟩, rfl⟩⟩
  · have hq := (hSh.2.2.2.1 g hQ).1
    obtain ⟨-, hP1, -⟩ := TerminationC2_qGraph_labels hq
    obtain ⟨hspd, hql, -⟩ := RunCompare_def63_Q hDef g hQ
    exact ⟨_, Or.inr (Or.inl ⟨hN, TerminationC2_ri_of hI hv hdc hT hNL hlab hP1
      (fun _ => ⟨hspd, hql⟩) (fun h => absurd h0 h) hK, hq, hK, rfl⟩)⟩

/-- **Along the run of `TerminationC_sel`**: from graphs of the run, every output graph is an
output and a graph of the run. -/
private theorem RunExports_run {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {E F : Expansion 3}
    (hr : SelRunB n D 𝒯 𝔈 TerminationC_sel E F) :
    (∀ g ∈ E, RunExports_J n D 𝒯 g) →
      ∀ g ∈ F, TerminationC_Out n D g ∧ RunExports_J n D 𝒯 g := by
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  have hℓ := TerminationC_sel_adm 𝔈 hF n D 𝒯
  have h𝒯 := TerminationC2_tSubst_runKinds hH
  have hkey := RunExports_key hH hF h𝒯 hℓ
  induction hr with
  | nil =>
    intro _ g hg
    simp at hg
  | out hO _ ih =>
    intro hE g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨hO, hE _ List.mem_cons_self⟩
    · exact ih (fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')) g hg
  | @step g E F hO _ _ ih =>
    intro hE
    obtain ⟨hc, hK⟩ := hE g List.mem_cons_self
    obtain ⟨r, hr⟩ := hc.resolve_left fun h => hO h.1
    obtain ⟨hD, hs⟩ := hkey g r hr hO
    have hA := (hℓ g hD hO).1
    refine ih fun s hs' => ?_
    rcases List.mem_append.1 hs' with hs' | hs'
    · refine ⟨?_, TerminationK_step hF h𝒯 hA hK s hs'⟩
      rcases hs s hs' with h | ⟨r', -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨r', h⟩
    · exact hE s (List.mem_cons_of_mem _ hs')

/-- **The invariant of a run on the output graphs** ([II, Lemma 6.8]): every output graph of the
run of `TerminationC_sel` is an output with the run kinds for the order `n - 1`, and with the
invariant of a run if its scaling order is `≤ D`; its scaling order in the count of [II, (2.5)]
is its scaling order. -/
private theorem RunExports_main {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {F : Expansion 3}
    (hr : SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F) :
    ∀ g ∈ F, TerminationC_Out n D g ∧ (¬ (D : ℤ) < g.2.ord → TerminationC_RI n D g) ∧
      g.2.RunKinds (n - 1) ∧ g.2.paperOrd = g.2.ord := by
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  intro g hg
  obtain ⟨hO, hc, hK⟩ := RunExports_run hF hn hT hr (fun g' hg' => by
    obtain ⟨r, h⟩ := RunExports_inputs hH g' hg'
    exact ⟨Or.inr ⟨r, h⟩, RunExports_good_runKinds h⟩) g hg
  refine ⟨hO, fun hD => ?_, hK, Graph.paperOrd_of_dotExcess hO.2.2.2.1.2.1⟩
  obtain ⟨r, h⟩ := hc.resolve_left fun h => hD h.2
  exact RunExports_good_ri h hO.2.2.1

end Run

/-! ## The output graphs of the run -/

/-- **An output graph without labels has scaling order `≥ 3`** ([II, Lemma 6.8], [II, Def 6.3]):
for a family `𝔈` of `Q`-expansions of [II, Lemma 4.15], a cutoff order `n ≥ 3` and an
`(n - 1)`-th order `T`-expansion `𝒯` with error order `D`, every output graph without labels of the
run driven by `TerminationC_sel` from the graphs of `A` and `Q` of the second order `T`-expansion
has scaling order `≥ 3`. -/
theorem RunExports.selRun_labelFree_ord :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ F : Expansion 3, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F →
    ∀ g ∈ F, g.2.LabelFree → 3 ≤ g.2.ord := by
  intro 𝔈 hF n D Sig 𝒯 hn hT F hr g hg hL
  obtain ⟨-, hR, -, hpo⟩ := RunExports_main hF hn hT hr g hg
  by_cases hD : (D : ℤ) < g.2.ord
  · have h1 : n - 1 < D := hT.1
    have h2 : (3 : ℤ) ≤ D := by exact_mod_cast (show 3 ≤ D by omega)
    omega
  · have := (hR hD).2.1.2.1 hL
    rw [hpo] at this
    exact this

/-- **An output graph without labels of scaling order `≤ D` with `⊕`, `⊖` in one dotted block has
scaling order `≥ 5`** ([II, Def 6.3 (1)], [II, Lemma 6.8]), on the output graphs of the run driven
by `TerminationC_sel` as in `RunExports.selRun_labelFree_ord`. -/
theorem RunExports.selRun_pmBlock_ord :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ F : Expansion 3, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F →
    ∀ g ∈ F, g.2.PMBlock ∧ g.2.LabelFree ∧ ¬ (D : ℤ) < g.2.ord → 5 ≤ g.2.ord := by
  intro 𝔈 hF n D Sig 𝒯 hn hT F hr g hg ⟨hpm, hL, hD⟩
  obtain ⟨-, hR, -, hpo⟩ := RunExports_main hF hn hT hr g hg
  have := ((hR hD).2.1.2.2.2.2.1 hpm).2 hL
  rw [hpo] at this
  exact this

/-- **The invariant of a run, the run kinds and the class `R` on the output graphs of the selector**
([II, Lemma 6.8], [II, Def 3.2 (2)], [II, Def 6.3 (1)]): for a family `𝔈` of `Q`-expansions of
[II, Lemma 4.15] (`QExpFamilyStmt`), a cutoff order `n ≥ 3` and an `(n - 1)`-th order
`T`-expansion `𝒯` with error order `D`, every output graph `g` of the run driven by
`TerminationC_sel` from the graphs of `A` and `Q` of the second order `T`-expansion
1. has the invariant of a run `TerminationC_RI n D` if its scaling order is `≤ D`;
2. has the run kinds `Graph.RunKinds (n - 1)`: no `Θ^{(n)}_err`, ghost or auxiliary edge, and `Θ`
   labels with entries even in `[4, n - 1]`;
3. is of the class `Graph.LeafR` if it is of the class `Graph.LeafDet`, a `⊕/⊖`-recollision graph
   and of scaling order `≤ D`. -/
theorem RunExports.selRun_exports :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ F : Expansion 3, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F →
    ∀ g ∈ F,
      (¬ (D : ℤ) < g.2.ord → TerminationC_RI n D g) ∧ g.2.RunKinds (n - 1) ∧
      (g.2.LeafDet → g.2.IsRecollision {1, 2} → ¬ (D : ℤ) < g.2.ord → g.2.LeafR) := by
  intro 𝔈 hF n D Sig 𝒯 hn hT F hr g hg
  obtain ⟨-, hR, hK, -⟩ := RunExports_main hF hn hT hr g hg
  refine ⟨hR, hK, fun ⟨hL, hgs, _, hE, hC⟩ hrc hD => ⟨hrc, hL, hgs, hE, hC, fun hpm => ?_⟩⟩
  exact RunExports.selRun_pmBlock_ord 𝔈 hF n D Sig 𝒯 hn hT F hr g hg ⟨hpm, hL, hD⟩

section Instances

end Instances

end RBM8D.Graphs
