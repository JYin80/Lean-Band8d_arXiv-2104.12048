module

public import RBM8D.GlobalExp.Strategy
public import RBM8D.Bound.GraphAbs
public import RBM8D.Graph.QExp.MolMono

@[expose] public section

/-!
# The family of `Q`-expansions as a hypothesis

The family of `Q`-expansions of [II, Lemma 4.15], one for each error order `D`, graph `Γ` and
label atom `x`, with the clauses used in [II, Theorem 3.7] (`QExpFamilyStmt`). The last clause
carries, for every output graph of a graph that is not a `Q`-graph and has `Graph.InvB'`, the map
of the atoms along which the output graph is reached: it is `Graph.MolMono` (the observation in
the proof of [II, Lemma 6.5 (4)] that the expansions create no new molecule and keep or subdivide
the edges between molecules), and the proper isolated subsets of an output graph without labels
are read through their pullback `Graph.molPull` along that map.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- A family of `Q`-expansions `𝔈 D n₀ x Γ` of [II, Lemma 4.15], one for each error order `D`,
graph `Γ` and label atom `x`, with the clauses:
* (F1) on every normal regular plain graph `Γ₀ Q_x(Γ̃₀)`: the value of `Γ`, and the clause
  `qexpClauseB` of Step 3;
* (F2) for all `C`, `j` and `D` there are `K`, `C'` such that on every such graph with bound `C`
  and `D + 1 ≤ ord Γ + j` there are at most `K` output graphs, each with `qExpansionOut'` and
  bound `C'`;
* (F3) for `D ≤ D'` the output graphs of scaling order `≤ D` in the count of [II, (2.5)] are the
  same, up to order, for every selection of such graphs;
* (F4) on a graph with the invariant `Graph.InvB'` in which `⊕`, `⊖` do not lie in one dotted
  block, an output graph in which they do has a strictly larger scaling order in the count of
  [II, (2.5)];
* (F5) an output graph that is not plain is normal regular, without `×`-dotted edge inside a
  block, clean, and of scaling order `> D` in the count of [II, (2.5)];
* (F6) on a graph `Γ` that is not a `Q`-graph and has the invariant `Graph.InvB'`, every output
  graph `s` is reached by the map `s.f` of the atoms, which is `Graph.MolMono` ([II, Lemma 6.5 (4)]:
  the label atom of a `Q`-graph output lies in the MIS, from [II, Lemma 4.15]); and if `Γ` has no
  unlabelled weight or solid edge at the block of `x`, `s` has no labels and scaling order `≤ D`,
  every proper isolated subset `P'` of its molecular graph whose pullback `Graph.molPull` along
  `s.f` contains the molecule of `x` and no molecule of an atom of an unlabelled weight or solid
  edge of `Γ` is weakly isolated ([II, Def 6.1]; [II, Lemma 4.15 (iv)]). -/
def QExpFamilyStmt (𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀) : Prop :=
  (∀ (D n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), (∃ C, Γ.Normal C) → Γ.IsQFormAt (.inr x) →
    Γ.Plain → (𝔈 D n₀ x Γ).ValueEq Γ modelAdm ∧ qexpClauseB D x Γ (𝔈 D n₀ x Γ)) ∧
  (∀ C j D : ℕ, ∃ K C' : ℕ, ∀ (n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀),
    Γ.Normal C → Γ.IsQFormAt (.inr x) → Γ.Plain → (D : ℤ) + 1 ≤ Γ.ord + j →
      (𝔈 D n₀ x Γ).length ≤ K ∧ ∀ t ∈ 𝔈 D n₀ x Γ, qExpansionOut' D C' (.inr x) Γ t) ∧
  (∀ (D D' n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), D ≤ D' → (∃ C, Γ.Normal C) →
    Γ.IsQFormAt (.inr x) → Γ.Plain →
    ∀ P : (Σ n, Graph 3 n) → Bool, (∀ g, P g = true → g.2.paperOrd ≤ D) →
      ((𝔈 D' n₀ x Γ).forget.filter P).Perm ((𝔈 D n₀ x Γ).forget.filter P)) ∧
  (∀ (D n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), (∃ C, Γ.Normal C) → Γ.IsQFormAt (.inr x) →
    Γ.Plain → Γ.InvB' → ¬ Γ.PMBlock →
    ∀ t ∈ 𝔈 D n₀ x Γ, t.g.PMBlock → Γ.paperOrd + 1 ≤ t.g.paperOrd) ∧
  (∀ (D n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), (∃ C, Γ.Normal C) → Γ.IsQFormAt (.inr x) →
    Γ.Plain → ∀ t ∈ 𝔈 D n₀ x Γ, ¬ t.g.Plain →
      (∃ C, t.g.Normal C) ∧ t.g.XdotApart ∧ t.g.Clean ∧ (D : ℤ) < t.g.paperOrd) ∧
  (∀ (D n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), (∃ C, Γ.Normal C) → Γ.IsQFormAt (.inr x) →
    Γ.Plain → ¬ Γ.IsQGraph → Γ.InvB' →
    ∀ s ∈ 𝔈 D n₀ x Γ, Γ.MolMono s.g s.f ∧
      (Γ.UnlabelledFreeAtBlock (.inr x) → s.g.LabelFree → s.g.ord ≤ D →
        ∀ P' : Finset (Atom 3 s.nOut), s.g.toMG'.IsProperIso s.g.toMG'.int P' →
          Γ.molRep (.inr x) ∈ Γ.molPull s.g s.f P' →
          (∀ c ∈ Γ.comps, c.label = none → c.kind.isRandom = true → ∀ u ∈ [c.x, c.y],
            Γ.molRep (Γ.flatAtom u) ∉ Γ.molPull s.g s.f P') →
          s.g.toMG'.IsWeaklyIso P'))

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

instance QFamily_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

instance QFamily_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (QFamily_decAdjDot Γ) u v

instance QFamily_decIsQFormAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.IsQFormAt u) := by
  unfold Graph.IsQFormAt; infer_instance

instance QFamily_decUnlabelledFreeAtBlock {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.UnlabelledFreeAtBlock u) := by
  unfold Graph.UnlabelledFreeAtBlock; infer_instance

end Instances

end RBM8D.Graphs
