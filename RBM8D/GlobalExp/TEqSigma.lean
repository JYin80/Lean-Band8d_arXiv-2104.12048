import RBM8D.GlobalExp.RunCompare
import Batteries.Tactic.OpenPrivate

/-!
# The `n`-th order `T`-equation read off the run of [II, Strategy 6.6]: the construction and `Σ_n`

The construction of [II, (6.8)] from the output graphs of the run `RunCompare.run` of
[II, Strategy 6.6] ([II, Lemma 6.8]), for every map `sigma` from an output graph
`Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of [II, Lemma 6.7] to its graph `𝒮` and every map `corr` to the graphs of
the `t → T` rewriting of [II, (6.7)]:

* the family of `Q`-expansions of [II, Lemma 4.15] fixed once (`TEqSigma.qFam`);
* the `T`-equation read off the output graphs (`TEqSigma.ofLeaves`) and the construction
  (`TEqSigma.strat`);
* `Σ_n` does not depend on the error order `D` (`TEqSigma.sigN_indep`, [II, (6.9)]);
* for `4 ≤ l < n` the graphs `𝒮` of the output graphs of [II, Lemma 6.7] of order `l` of the run at
  the cutoff order `n` are those of `Σ_l` (`TEqSigma.sig_perm`, [II, (6.7)], [II, (6.9)]).

Both statements hold for every `sigma` and `corr`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The construction -/

/-- The family of `Q`-expansions of [II, Lemma 4.15] used in Step 3 of [II, Strategy 6.6]: one
family with the clauses `QExpFamilyStmt`, fixed once for every order. -/
def TEqSigma.qFam : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀ :=
  exists_qExpFamilyStmt.choose

/-- `TEqSigma.qFam` satisfies `QExpFamilyStmt`. -/
theorem TEqSigma.qFam_spec : QExpFamilyStmt TEqSigma.qFam :=
  exists_qExpFamilyStmt.choose_spec

open Classical in
/-- The `n`-th order `T`-equation with error order `D` read off the output graphs `F` of a run of
[II, Strategy 6.6] at the cutoff order `n` ([II, §6.4], [II, (6.7)–(6.8)]), given the map `sigma`
from an output graph `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of [II, Lemma 6.7] to its graph `𝒮` and the map
`corr` to the graphs `Θ_{⊗x} 𝒮_{xy} (t - T)_{y,⊕⊖}`; the output graphs of [II, Lemma 6.7] are those
of the class `Graph.LeafDet` that are not `⊕/⊖`-recollision graphs, of order `≤ n`. `Σ_n` is the
formal sum of the graphs `𝒮` of those of order `n`, listed in one order fixed by their multiset;
`R` the output graphs of order `≤ min(n, D)` of the class `Graph.LeafR` and the graphs of `corr` of
order `≤ n`; `A` the other output graphs of order `≤ D` of the class `Graph.LeafA n` and the graphs
of `corr` of order `> n`; `Q` the output graphs of order `≤ D` of the class `Graph.LeafQ`; `Err`
the output graphs of order `> D`. -/
def TEqSigma.ofLeaves (n D : ℕ) (sigma : (Σ m, Graph 3 m) → Expansion 2)
    (corr : (Σ m, Graph 3 m) → Expansion 3) (F : Expansion 3) : TEqRec where
  SigN := (((F.filter fun g =>
      decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (n : ℤ))).flatMap sigma :
    List (Σ m, Graph 2 m)) : Multiset (Σ m, Graph 2 m)).toList
  R := F.filter (fun g => decide (¬ (D : ℤ) < g.2.ord ∧ g.2.LeafR ∧ g.2.ord ≤ (n : ℤ))) ++
    ((F.filter fun g =>
      decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (n : ℤ))).flatMap corr).filter
      fun g => decide (g.2.ord ≤ (n : ℤ))
  A := F.filter (fun g => decide (¬ (D : ℤ) < g.2.ord ∧ ¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧
      g.2.LeafA n)) ++
    ((F.filter fun g =>
      decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (n : ℤ))).flatMap corr).filter
      fun g => decide ((n : ℤ) < g.2.ord)
  Q := F.filter fun g => decide (¬ (D : ℤ) < g.2.ord ∧ g.2.LeafQ)
  Err := F.filter fun g => decide ((D : ℤ) < g.2.ord)

open Classical in
/-- **The construction of [II, (6.8)]** from the run of [II, Strategy 6.6]: for `n ≥ 3` and a
record `𝒯` that is the structural part of an `(n - 1)`-th order `T`-expansion with error order `D`
over some `Sig`, the `T`-equation `TEqSigma.ofLeaves` read off the output graphs of the run
`RunCompare.run` with the family `TEqSigma.qFam`; the empty record otherwise. -/
def TEqSigma.strat (sigma : (Σ m, Graph 3 m) → Expansion 2)
    (corr : (Σ m, Graph 3 m) → Expansion 3) (n D : ℕ) (𝒯 : TRec) : TEqRec :=
  if 3 ≤ n ∧ ∃ Sig, 𝒯.IsTExpStruct Sig (n - 1) D then
    TEqSigma.ofLeaves n D sigma corr (RunCompare.run TEqSigma.qFam n D 𝒯)
  else ⟨[], [], [], [], []⟩

/-- Under its condition, `TEqSigma.strat` is `TEqSigma.ofLeaves` of the run. -/
theorem TEqSigma.strat_eq {sigma : (Σ m, Graph 3 m) → Expansion 2}
    {corr : (Σ m, Graph 3 m) → Expansion 3} {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) :
    TEqSigma.strat sigma corr n D 𝒯 =
      TEqSigma.ofLeaves n D sigma corr (RunCompare.run TEqSigma.qFam n D 𝒯) := by
  classical
  unfold TEqSigma.strat
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hn, Sig, hT⟩)

/-! ## `Σ_n` of the construction -/

open Classical in
/-- Two output lists whose graphs `𝒮` of order `n` (the images under `sigma` of the output graphs of
[II, Lemma 6.7] of order `n`) agree up to order give the same `Σ_n`, as lists. -/
theorem TEqSigma.ofLeaves_sigN_eq {n D D' : ℕ} {sigma : (Σ m, Graph 3 m) → Expansion 2}
    {corr corr' : (Σ m, Graph 3 m) → Expansion 3} {F F' : Expansion 3}
    (h : ((F.filter fun g =>
        decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (n : ℤ))).flatMap sigma).Perm
      ((F'.filter fun g =>
        decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (n : ℤ))).flatMap sigma)) :
    (TEqSigma.ofLeaves n D sigma corr F).SigN = (TEqSigma.ofLeaves n D' sigma corr' F').SigN := by
  unfold TEqSigma.ofLeaves
  simp only
  rw [Multiset.coe_eq_coe.2 h]

open Classical in
/-- The output graphs of [II, Lemma 6.7] of order `l` of `F` are those of the output graphs of
order `l`. -/
private theorem TEqSigma_filter_det (F : Expansion 3) (l : ℕ) :
    F.filter (fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (l : ℤ))) =
      (F.filter fun g => decide (g.2.ord = (l : ℤ))).filter
        fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2}) := by
  rw [List.filter_filter]
  refine List.filter_congr fun g _ => ?_
  by_cases h1 : g.2.LeafDet <;> by_cases h2 : g.2.IsRecollision {1, 2} <;>
    by_cases h3 : g.2.ord = (l : ℤ) <;> simp [h1, h2, h3]

open Classical in
/-- Two output lists whose graphs of order `l` agree up to order have the same images under `sigma`
of their output graphs of [II, Lemma 6.7] of order `l`, up to order. -/
private theorem TEqSigma_det_perm {F F' : Expansion 3} {l : ℕ}
    (sigma : (Σ m, Graph 3 m) → Expansion 2)
    (h : (F.filter fun g => decide (g.2.ord = (l : ℤ))).Perm
      (F'.filter fun g => decide (g.2.ord = (l : ℤ)))) :
    ((F.filter fun g =>
        decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (l : ℤ))).flatMap sigma).Perm
      ((F'.filter fun g =>
        decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (l : ℤ))).flatMap sigma) := by
  rw [TEqSigma_filter_det F l, TEqSigma_filter_det F' l]
  exact (h.filter _).flatMap_right sigma

/-- **`Σ_n` does not depend on the error order** ([II, (6.9)], [II, Def 3.3 (1)]): for every map
`sigma` and `corr`, `n ≥ 3` and families of `H(n - 1)` that record `TEqSigma.strat sigma corr`, one
`Σ_n = E` serves the `T`-equations `TEqSigma.strat sigma corr n D (𝒯 (n - 1) D)` of every error
order `D > n`. -/
theorem TEqSigma.sigN_indep (sigma : (Σ m, Graph 3 m) → Expansion 2)
    (corr : (Σ m, Graph 3 m) → Expansion 3) :
    ∀ n : ℕ, 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec),
      HFam (TEqSigma.strat sigma corr) Sig (n - 1) 𝒬 𝒯 →
      ∃ E : Expansion 2, ∀ D, n < D → (TEqSigma.strat sigma corr n D (𝒯 (n - 1) D)).SigN = E := by
  intro n hn Sig 𝒬 𝒯 hH
  obtain ⟨h1, -, -, h4, -, -⟩ := hH
  refine ⟨(TEqSigma.strat sigma corr n (n + 1) (𝒯 (n - 1) (n + 1))).SigN, fun D hD => ?_⟩
  have hT₀ : (𝒯 (n - 1) (n + 1)).IsTExpStruct Sig (n - 1) (n + 1) :=
    (h1 (n - 1) (n + 1) (by omega) le_rfl (by omega)).2.1
  have hT : (𝒯 (n - 1) D).IsTExpStruct Sig (n - 1) D :=
    (h1 (n - 1) D (by omega) le_rfl (by omega)).2.1
  have hAg : (𝒯 (n - 1) (n + 1)).AgreeTo (n + 1) (𝒯 (n - 1) D) :=
    (h4 (n - 1) (n + 1) D (by omega) le_rfl (by omega) (by omega)).2
  have hP := (RunCompare.runCompare TEqSigma.qFam TEqSigma.qFam_spec).2 Sig n (n + 1) D
    (𝒯 (n - 1) (n + 1)) (𝒯 (n - 1) D) hn (by omega) (by omega) hT₀ hT hAg n (by omega)
  rw [TEqSigma.strat_eq hn hT, TEqSigma.strat_eq hn hT₀]
  exact (TEqSigma.ofLeaves_sigN_eq (TEqSigma_det_perm sigma hP)).symm

open Classical in
/-- **`Σ_l` from the run at the cutoff order `n`** ([II, (6.7)], [II, (6.9)]): for every map
`sigma` and `corr`, `n ≥ 3`, families of `H(n - 1)` that record `TEqSigma.strat sigma corr`, every
error order `D > n` and every `4 ≤ l < n`, the images under `sigma` of the output graphs of
[II, Lemma 6.7] of order `l` of the run at the cutoff order `n` from `𝒯 (n - 1) D` are the graphs of
`Σ_l = Sig l`, up to order. -/
theorem TEqSigma.sig_perm (sigma : (Σ m, Graph 3 m) → Expansion 2)
    (corr : (Σ m, Graph 3 m) → Expansion 3) :
    ∀ n : ℕ, 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec),
      HFam (TEqSigma.strat sigma corr) Sig (n - 1) 𝒬 𝒯 → ∀ D, n < D → ∀ l, 4 ≤ l → l < n →
      (((RunCompare.run TEqSigma.qFam n D (𝒯 (n - 1) D)).filter fun g =>
          decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (l : ℤ))).flatMap
          sigma).Perm (Sig l) := by
  classical
  intro n hn Sig 𝒬 𝒯 hH D hD l hl hln
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hH
  have hTn : (𝒯 (n - 1) D).IsTExpStruct Sig (n - 1) D :=
    (h1 (n - 1) D (by omega) le_rfl (by omega)).2.1
  have hTl : (𝒯 (l - 1) D).IsTExpStruct Sig (l - 1) D :=
    (h1 (l - 1) D (by omega) (by omega) (by omega)).2.1
  obtain ⟨-, hC, hPM⟩ := h3 (l - 1) (n - 1) D (by omega) (by omega) le_rfl (by omega)
  have hl1 : l - 1 + 1 = l := by omega
  rw [hl1] at hPM
  have hA : ∀ g ∈ (𝒯 (l - 1) D).A ++ (𝒯 (n - 1) D).A, (l : ℤ) ≤ g.2.ord := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · have := ((hTl.2.2.2.1).2.2.1 g hg).2
      have e : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
      rw [e] at this
      omega
    · have := ((hTn.2.2.2.1).2.2.1 g hg).2
      have e : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [e] at this
      omega
  have hP := ((RunCompare.runCompare TEqSigma.qFam TEqSigma.qFam_spec).1 Sig l l n D
    (𝒯 (l - 1) D) (𝒯 (n - 1) D) (by omega) le_rfl (by omega) (by omega) hTl hTn hC hPM hA).1 l
    le_rfl
  have hS : (𝒬 l D).SigN = Sig l := h2 l D (by omega) (by omega) (by omega)
  rw [h6 l D (by omega) (by omega) (by omega), TEqSigma.strat_eq (by omega) hTl] at hS
  rw [← hS]
  unfold TEqSigma.ofLeaves
  simp only
  refine (TEqSigma_det_perm sigma hP).symm.trans ?_
  exact Multiset.coe_eq_coe.1 (Multiset.coe_toList _).symm

section Instances

open private h2Rec_struct from RBM8D.TExp.Second
open private RunCompare_q0_out from RBM8D.GlobalExp.RunCompare

end Instances

end RBM8D.Graphs
