import RBM8D.Graph.QExp.SelStep1
import RBM8D.Graph.DotBlocks

/-!
# Coherence in the Taylor degree, order, blocks and history of the run `selStep1`

Three properties of the run `selStep1 d x Γ` of [II, Lemma 4.11] ([II, §4.4, Step 1, (4.17)–(4.21)])
on a normal regular graph `Γ = Γ₀ Q_x(Γ̃₀)` with `x` internal, with `p` the scaling order of `Γ`
counted as in the paper (`Graph.paperOrd`):

* `selStep1Coh_coherent`: for Taylor degrees `d ≤ d'` the two runs have a common part `A`; the
  other terms (`B` at degree `d`, `B'` at degree `d'`) have scaling order at least `p + d + 1`.
  These are the remainders `W_d`, `W_{d'}` of [II, (4.21)] and the terms `j > d` of its sum.
* `selStep1Coh_order`: every output graph has scaling order at least `p`, and at least `p + 2` if
  it has `⊕` and `⊖` in one dotted block while `Γ` has not.
* `selStep1Coh_history`: every output graph is reached from `Γ` by a chain of steps of the run
  (`SelStep1CohStep`), then `O_merge` and removals of redundant dotted edges (`SelStep1CohDrop`).
  If `Γ₀` has no weight or edge attached to the block of `x` and the output is a `Q`-form that is
  not a `Q`-graph, the chain contains the second term of [II, (4.17)] at a weight or edge of `Γ₀`,
  or a split term `1_{u = x}` at an atom `u` of one (`SelStep1CohWit`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The steps of the run -/

section CohSteps

variable {k n : ℕ}

/-- One step of the run `selStep1` at the internal atom `X`, from `T` to `g`, with the identity
atom map: `g` is a term of a split `1 = 1_{u = X} + 1_{u ≠ X}` (`oSplitT`), of [II, (4.17)]
(`oSchurT`, `oSchurWT`), of [II, (4.20)] (`oSchurRevT`, `oSchurWRevT`), of [II, (4.21)]
(`oTaylorT`), of `1_{u ≠ v} = 1 - 1_{u = v}` (`oXdotT`), or `g` is `T` with the factors with minor
`{X}` moved into the label group `Q_X` (`Graph.absorb`). -/
inductive SelStep1CohStep (X : Atom k n) : Graph k n → Graph k n → Prop
  | split (u : Atom k n) (T g : Graph k n) (h : Tracked.self g ∈ oSplitT u X T) :
      SelStep1CohStep X T g
  | schur (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurT X i T) : SelStep1CohStep X T g
  | schurW (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurWT X i T) :
      SelStep1CohStep X T g
  | absorb (T : Graph k n) (hℓ : ∃ c ∈ T.comps, c.label = some (.Q, X))
      (hl : ∀ c ∈ T.comps, c.label = none ∨ c.label = some (.Q, X)) :
      SelStep1CohStep X T (T.absorb (.Q, X))
  | schurRev (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurRevT X i T) :
      SelStep1CohStep X T g
  | schurWRev (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurWRevT X i T) :
      SelStep1CohStep X T g
  | taylor (D i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oTaylorT D i T) :
      SelStep1CohStep X T g
  | xdot (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oXdotT i T) : SelStep1CohStep X T g

/-- A step of the run at an internal atom is an elementary step `QElemStep`. -/
theorem SelStep1CohStep.qElemStep {X : Atom k n} (hX : X.isRight = true) {T g : Graph k n}
    (h : SelStep1CohStep X T g) : QElemStep ⟨n, T⟩ ⟨n, g⟩ := by
  cases h with
  | split u T g h => exact QElemStep.split u X T (Tracked.self g) hX h
  | schur i T g h => exact QElemStep.schur X i T (Tracked.self g) hX h
  | schurW i T g h => exact QElemStep.schurW X i T (Tracked.self g) hX h
  | absorb T hℓ hl => exact QElemStep.absorb (.Q, X) T hℓ hl
  | schurRev i T g h => exact QElemStep.schurRev X i T (Tracked.self g) hX h
  | schurWRev i T g h => exact QElemStep.schurWRev X i T (Tracked.self g) hX h
  | taylor D i T g h => exact QElemStep.taylor D i T (Tracked.self g) h
  | xdot i T g h => exact QElemStep.xdot i T (Tracked.self g) h

/-- The removal of a dotted edge of `g` whose ends are joined by the other dotted edges. -/
def SelStep1CohDrop {m : ℕ} (g g' : Graph k m) : Prop :=
  ∃ i c, g.comps[i]? = some c ∧ c.kind = .dot ∧
    (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k m).SameBlock c.x c.y ∧
    g' = ⟨g.comps.eraseIdx i, g.coeff⟩

/-- The witness of [II, Lemma 4.11] in a chain `l` of graphs from `Γ` at the internal atom `X`:
for some weight or edge `c` of `Γ₀` (a random component of `Γ` without label), two consecutive
graphs `T`, `g` of `l` such that `g` is the second term `G_{c.x X} G_{X c.y} (G_{XX})⁻¹` of
[II, (4.17)] at the component `c` of `T`, or `g` is the split term `1_{u = X}` of `T` at an atom
`u` of `c`. -/
def SelStep1CohWit (X : Atom k n) (Γ : Graph k n) (l : List (Graph k n)) : Prop :=
  ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧ ∃ (j : ℕ) (T g : Graph k n),
    l[j]? = some T ∧ l[j + 1]? = some g ∧
    ((∃ (i : ℕ) (ch : Charge), T.comps[i]? = some c ∧
      g = ⟨T.comps.eraseIdx i ++ [mkC (.G ch) c.x X, mkC (.G ch) X c.y, mkC (.inv ch) X X],
        T.coeff⟩) ∨
      ∃ u ∈ [c.x, c.y], g = ⟨T.comps ++ [mkC .dot u X], T.coeff⟩)

end CohSteps

/-! ## Auxiliary facts -/

section CohBasic

variable {k n : ℕ}

private theorem coh_self_inj {a b : Graph k n} (h : Tracked.self a = Tracked.self b) : a = b := by
  simp only [Tracked.self, Tracked.mk.injEq, heq_eq_eq, true_and, and_true] at h
  exact h

private theorem coh_mem_self {Gs : List (Graph k n)} {g : Graph k n}
    (h : Tracked.self g ∈ Gs.map Tracked.self) : g ∈ Gs := by
  obtain ⟨g', hg', he⟩ := List.mem_map.1 h
  exact coh_self_inj he ▸ hg'

private theorem coh_bind_self (Gs : List (Graph k n))
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n') :
    TExpansion.bind (Gs.map Tracked.self) O = Gs.flatMap fun g => O id g := by
  unfold TExpansion.bind
  rw [List.flatMap_map]
  congr 1
  funext g
  simp only [Tracked.self, Function.comp_id]
  exact List.map_id' _

private theorem coh_findIdx_some {α : Type*} {L : List α} {p : α → Bool} {i : ℕ}
    (h : L.findIdx? p = some i) : ∃ c, L[i]? = some c ∧ p c = true := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨L[i], List.getElem?_eq_getElem hi, hp⟩

private theorem coh_ord_replace {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n))) (co : Coeff) :
    (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord =
      T.ord - c.kind.ord + (new.map fun d => d.kind.ord).sum := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hp := ((List.getElem_cons_eraseIdx_perm hi).map fun d => d.kind.ord).sum_eq
  simp only [Graph.ord, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hp ⊢
  linarith

private theorem coh_ord_append (T : Graph k n) (new : List (Comp (Atom k n))) (co : Coeff) :
    (⟨T.comps ++ new, co⟩ : Graph k n).ord = T.ord + (new.map fun d => d.kind.ord).sum := by
  simp only [Graph.ord, List.map_append, List.sum_append]
  ring

/-- The ends of a dotted edge lie in one block. -/
private theorem coh_dot_sameBlock {T : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ T.comps)
    (hk : c.kind = .dot) : T.SameBlock c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
    exact SimpleGraph.Reachable.refl _
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩).reachable

/-- Fewer dotted edges give smaller blocks. -/
private theorem coh_sameBlock_mono {g T : Graph k n}
    (h : ∀ c ∈ g.comps, c.kind = .dot → ∃ d ∈ T.comps, d.kind = .dot ∧ d.x = c.x ∧ d.y = c.y)
    {a b : Atom k n} (hab : g.SameBlock a b) : T.SameBlock a b := by
  refine SimpleGraph.Reachable.mono (G := g.dotGraph) ?_ hab
  intro u v huv
  rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at huv ⊢
  obtain ⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := huv
  · obtain ⟨d, hd, hdk, hx, hy⟩ := h c hc hk
    exact ⟨hne, Or.inl ⟨d, hd, hdk, hx, hy⟩⟩
  · obtain ⟨d, hd, hdk, hx, hy⟩ := h c hc hk
    exact ⟨hne, Or.inr ⟨d, hd, hdk, hx, hy⟩⟩

/-- An atom lies in the block of its representative. -/
private theorem coh_sameBlock_mrep (T : Graph k n) (u : Atom k n) : T.SameBlock u (T.mrep u) := by
  have key : ∀ P : List (List (Atom k n)),
      blockRep P u = u ∨ ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
    intro P
    unfold blockRep
    split
    · next r rest hf =>
      right
      refine ⟨r :: rest, List.mem_of_find?_eq_some hf, ?_, List.mem_cons_self ..⟩
      simpa [List.contains_iff_mem] using List.find?_some hf
    · exact Or.inl rfl
  rcases key (dotBlocks (allAtoms k n) T.comps) with h | ⟨B, hB, hu, hr⟩
  · change T.SameBlock u (blockRep _ u)
    rw [h]
    exact SimpleGraph.Reachable.refl _
  · exact (T.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, hu, hr⟩

private theorem coh_sameBlock_of_mrep {T : Graph k n} {u v : Atom k n} (h : T.mrep u = T.mrep v) :
    T.SameBlock u v :=
  (coh_sameBlock_mrep T u).trans (h ▸ (coh_sameBlock_mrep T v).symm)

end CohBasic

/-! ## The facts carried by one step -/

section CohRs

variable {k n : ℕ}

/-- A step of the run that does not lower the scaling order, that keeps the blocks or raises the
scaling order by at least `2`, and that keeps the class `ClsQ`. -/
private def CohRs (X : Atom k n) (T g : Graph k n) : Prop :=
  SelStep1CohStep X T g ∧ T.ord ≤ g.ord ∧
    ((∀ a b, g.SameBlock a b → T.SameBlock a b) ∨ T.ord + 2 ≤ g.ord) ∧ (ClsQ X T → ClsQ X g)

private theorem coh_rs_self {X : Atom k n} {T : Graph k n} (h : SelStep1CohStep X T T) :
    CohRs X T T :=
  ⟨h, le_rfl, Or.inl fun _ _ => id, id⟩

private theorem coh_rs_replace {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n))) (co : Coeff)
    (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++ new, co⟩)
    (hord : c.kind.ord ≤ (new.map fun d => d.kind.ord).sum)
    (hblk : (∀ d ∈ new, d.kind ≠ .dot) ∨ c.kind.ord + 2 ≤ (new.map fun d => d.kind.ord).sum)
    (hcl : ∀ d ∈ new, d.kind.isRandom = true → c.kind.isRandom = true ∧ d.label = c.label) :
    CohRs X T ⟨T.comps.eraseIdx i ++ new, co⟩ := by
  have ho := coh_ord_replace hc new co
  refine ⟨hst, by linarith, ?_, fun hQ d hd hdr => ?_⟩
  · rcases hblk with hnd | h2
    · refine Or.inl fun a b h => coh_sameBlock_mono (fun d hd hdk => ⟨d, ?_, hdk, rfl, rfl⟩) h
      rcases List.mem_append.1 hd with h | h
      · exact List.mem_of_mem_eraseIdx h
      · exact absurd hdk (hnd d h)
    · exact Or.inr (by linarith)
  · rcases List.mem_append.1 hd with h | h
    · exact hQ d (List.mem_of_mem_eraseIdx h) hdr
    · obtain ⟨hr, hl⟩ := hcl d h hdr
      rw [hl]
      exact hQ c (List.mem_of_getElem? hc) hr

private theorem coh_rs_append {X : Atom k n} {T : Graph k n} (κ : Kind) (hκ : κ = .dot ∨ κ = .xdot)
    (u v : Atom k n) (hst : SelStep1CohStep X T ⟨T.comps ++ [mkC κ u v], T.coeff⟩) :
    CohRs X T ⟨T.comps ++ [mkC κ u v], T.coeff⟩ := by
  have ho : (⟨T.comps ++ [mkC κ u v], T.coeff⟩ : Graph k n).ord = T.ord + κ.ord := by
    rw [coh_ord_append]
    simp [mkC]
  have hnr : (mkC κ u v).kind.isRandom = false := by rcases hκ with rfl | rfl <;> rfl
  refine ⟨hst, ?_, ?_, fun hQ d hd hdr => ?_⟩
  · rcases hκ with rfl | rfl <;> simp only [Kind.ord] at ho <;> linarith
  · rcases hκ with rfl | rfl
    · exact Or.inr (by simp only [Kind.ord] at ho; linarith)
    · refine Or.inl fun a b h => coh_sameBlock_mono (fun d hd hdk => ⟨d, ?_, hdk, rfl, rfl⟩) h
      rcases List.mem_append.1 hd with h | h
      · exact h
      · rw [List.mem_singleton.1 h] at hdk
        cases hdk
  · rcases List.mem_append.1 hd with h | h
    · exact hQ d h hdr
    · rw [List.mem_singleton.1 h, hnr] at hdr
      cases hdr

private theorem coh_rs_absorb {X : Atom k n} {T : Graph k n}
    (hℓ : ∃ c ∈ T.comps, c.label = some (.Q, X))
    (hl : ∀ c ∈ T.comps, c.label = none ∨ c.label = some (.Q, X)) :
    CohRs X T (T.absorb (.Q, X)) := by
  set φ : Comp (Atom k n) → Comp (Atom k n) := fun c =>
    if c.label = none ∧ c.kind.isRandom = true ∧ X ∈ c.minor then { c with label := some (.Q, X) }
    else c with hφ
  have hcomps : (T.absorb (.Q, X)).comps = T.comps.map φ := rfl
  have hk : ∀ c, (φ c).kind = c.kind ∧ (φ c).x = c.x ∧ (φ c).y = c.y := by
    intro c
    simp only [hφ]
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  refine ⟨.absorb T hℓ hl, le_of_eq ?_, Or.inl fun a b h => coh_sameBlock_mono ?_ h, ?_⟩
  · simp only [Graph.ord, hcomps, List.map_map]
    congr 2
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, (hk c).1]
  · intro d hd hdk
    rw [hcomps] at hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    obtain ⟨h1, h2, h3⟩ := hk c
    exact ⟨c, hc, h1 ▸ hdk, h2.symm, h3.symm⟩
  · intro hQ d hd hdr
    rw [hcomps] at hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    rw [(hk c).1] at hdr
    have hcl := hQ c hc hdr
    have : φ c = c := by
      simp only [hφ]
      refine ite_eq_right fun h => ?_
      rw [hcl] at h
      cases h.1
    rw [this]
    exact hcl

/-- A step of [II, (4.17)] at a pending component `c`: the graph itself, the first term, or the
second term `G_{c.x X} G_{X c.y} (G_{XX})⁻¹`. -/
private theorem coh_rs_schur {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hp : pendB X c = true) (hwf : c.WF)
    (hg : Tracked.self g ∈ selStep1_schurAt X i T) :
    CohRs X T g ∧ (g = T ∨ g = ⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ ∨
      ∃ ch, g = ⟨T.comps.eraseIdx i ++ [mkC (.G ch) c.x X, mkC (.G ch) X c.y, mkC (.inv ch) X X],
        T.coeff⟩) := by
  simp only [pendB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff, bne_iff_ne,
    ne_eq] at hp
  obtain ⟨⟨⟨⟨hl, hr⟩, hm⟩, hx⟩, hy⟩ := hp
  obtain ⟨κ, cx, cy, cm, cl⟩ := c
  simp only at hl hm hx hy hr hwf ⊢
  subst hl hm
  have h1 : SelStep1CohStep X T
      ⟨T.comps.eraseIdx i ++ [⟨κ, cx, cy, [X], none⟩], T.coeff⟩ →
      CohRs X T ⟨T.comps.eraseIdx i ++ [⟨κ, cx, cy, [X], none⟩], T.coeff⟩ := fun hst =>
    coh_rs_replace hc _ _ hst (by simp) (Or.inl (by simp; intro h; rw [h] at hr; cases hr))
      (by simp [hr])
  have h2 : ∀ ch, κ.ord ≤ 1 →
      ∀ (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩),
      CohRs X T ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩ := by
    intro ch ho hst
    have hs : (([mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X] :
        List (Comp (Atom k n))).map fun d => d.kind.ord).sum = 2 := by
      simp [mkC, Kind.ord]
    exact coh_rs_replace hc _ _ hst (by rw [hs]; linarith) (Or.inl (by simp [mkC]))
      (by simp [mkC, hr])
  cases κ with
  | G ch =>
    have hS : selStep1_schurAt X i T = oSchurT X i T := by simp [selStep1_schurAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schur i T g hg
    have hE : oSchurT X i T = [(⟨T.comps.eraseIdx i ++ [⟨.G ch, cx, cy, [X], none⟩], T.coeff⟩ :
        Graph k n), ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cx X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩].map Tracked.self := by
      simp only [oSchurT, hc, List.isEmpty_nil, Option.all_none, Bool.and_self, ↓reduceIte,
        solidC, hx, Ne.symm hy]
      rfl
    rw [hE] at hg
    rcases List.mem_cons.1 (coh_mem_self hg) with rfl | hg
    · exact ⟨h1 hst, Or.inr (Or.inl rfl)⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      exact ⟨h2 ch le_rfl hst, Or.inr (Or.inr ⟨ch, rfl⟩)⟩
  | weight ch =>
    have hS : selStep1_schurAt X i T = oSchurWT X i T := by simp [selStep1_schurAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurW i T g hg
    have hyx : cy = cx := hwf.1 rfl
    subst hyx
    have hE : oSchurWT X i T = [(⟨T.comps.eraseIdx i ++ [⟨.weight ch, cy, cy, [X], none⟩],
        T.coeff⟩ : Graph k n), ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cy X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩].map Tracked.self := by
      simp only [oSchurWT, hc]
      split_ifs with hcond
      · rfl
      · simp [hx] at hcond
    rw [hE] at hg
    rcases List.mem_cons.1 (coh_mem_self hg) with rfl | hg
    · exact ⟨h1 hst, Or.inr (Or.inl rfl)⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      exact ⟨h2 ch (by simp [Kind.ord]) hst, Or.inr (Or.inr ⟨ch, rfl⟩)⟩
  | light ch =>
    have hS : selStep1_schurAt X i T = oSchurWT X i T := by simp [selStep1_schurAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurW i T g hg
    have hyx : cy = cx := hwf.1 rfl
    subst hyx
    have hE : oSchurWT X i T = [(⟨T.comps.eraseIdx i ++ [⟨.light ch, cy, cy, [X], none⟩],
        T.coeff⟩ : Graph k n), ⟨T.comps.eraseIdx i ++
        [mkC (.G ch) cy X, mkC (.G ch) X cy, mkC (.inv ch) X X], T.coeff⟩].map Tracked.self := by
      simp only [oSchurWT, hc]
      split_ifs with hcond
      · rfl
      · simp [hx] at hcond
    rw [hE] at hg
    rcases List.mem_cons.1 (coh_mem_self hg) with rfl | hg
    · exact ⟨h1 hst, Or.inr (Or.inl rfl)⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      exact ⟨h2 ch le_rfl hst, Or.inr (Or.inr ⟨ch, rfl⟩)⟩
  | _ =>
    all_goals
      have hS : selStep1_schurAt X i T = oSchurT X i T := by simp [selStep1_schurAt, hc]
      rw [hS] at hg
      have hst := SelStep1CohStep.schur i T g hg
      have hE : oSchurT X i T = [Tracked.self T] := by simp [oSchurT, hc]
      rw [hE] at hg
      have := coh_self_inj (List.mem_singleton.1 hg)
      subst this
      exact ⟨coh_rs_self hst, Or.inl rfl⟩

private theorem coh_rs_minor {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hr : c.kind.isRandom = true) (m : List (Atom k n)) (co : Coeff)
    (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++ [{ c with minor := m }], co⟩) :
    CohRs X T ⟨T.comps.eraseIdx i ++ [{ c with minor := m }], co⟩ :=
  coh_rs_replace hc _ _ hst (by simp) (Or.inl (by simp; intro h; rw [h] at hr; cases hr))
    (by simp [hr])

private theorem coh_rs_three {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hr : c.kind.isRandom = true) (a b e : Comp (Atom k n))
    (co : Coeff) (hst : SelStep1CohStep X T ⟨T.comps.eraseIdx i ++ [a, b, e], co⟩)
    (hl : a.label = c.label ∧ b.label = c.label ∧ e.label = c.label)
    (hnd : a.kind ≠ .dot ∧ b.kind ≠ .dot ∧ e.kind ≠ .dot)
    (hord : c.kind.ord ≤ a.kind.ord + b.kind.ord + e.kind.ord) :
    CohRs X T ⟨T.comps.eraseIdx i ++ [a, b, e], co⟩ := by
  refine coh_rs_replace hc _ _ hst (by simp; linarith) (Or.inl ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl)
    exacts [hnd.1, hnd.2.1, hnd.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl) _
    exacts [⟨hr, hl.1⟩, ⟨hr, hl.2.1⟩, ⟨hr, hl.2.2⟩]

/-- A step of [II, (4.20)] at a component `c` with both ends different from `X`. -/
private theorem coh_rs_rev {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hx : c.x ≠ X) (hy : c.y ≠ X)
    (hg : Tracked.self g ∈ selStep1_revAt X i T) : CohRs X T g := by
  obtain ⟨κ, cx, cy, cm, cl⟩ := c
  simp only at hx hy
  cases κ with
  | G ch =>
    have hS : selStep1_revAt X i T = oSchurRevT X i T := by simp [selStep1_revAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurRev i T g hg
    simp only [oSchurRevT, hc] at hg
    split_ifs at hg
    · rcases List.mem_cons.1 hg with he | hg
      · rw [coh_self_inj he] at hst ⊢
        exact coh_rs_minor hc rfl _ _ hst
      · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
        refine coh_rs_three hc rfl _ _ _ _ hst ⟨rfl, rfl, rfl⟩ ?_ ?_ <;>
          simp [solidC, hx, Ne.symm hy, mkC, Kind.ord]
    · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact coh_rs_self hst
  | weight ch =>
    have hS : selStep1_revAt X i T = oSchurWRevT X i T := by simp [selStep1_revAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurWRev i T g hg
    simp only [oSchurWRevT, hc] at hg
    split_ifs at hg
    · rcases List.mem_cons.1 hg with he | hg
      · rw [coh_self_inj he] at hst ⊢
        exact coh_rs_minor hc rfl _ _ hst
      · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
        refine coh_rs_three hc rfl _ _ _ _ hst ⟨rfl, rfl, rfl⟩ ?_ ?_ <;> simp [mkC, Kind.ord]
    · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact coh_rs_self hst
  | light ch =>
    have hS : selStep1_revAt X i T = oSchurWRevT X i T := by simp [selStep1_revAt, hc]
    rw [hS] at hg
    have hst := SelStep1CohStep.schurWRev i T g hg
    simp only [oSchurWRevT, hc] at hg
    split_ifs at hg
    · rcases List.mem_cons.1 hg with he | hg
      · rw [coh_self_inj he] at hst ⊢
        exact coh_rs_minor hc rfl _ _ hst
      · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
        refine coh_rs_three hc rfl _ _ _ _ hst ⟨rfl, rfl, rfl⟩ ?_ ?_ <;> simp [mkC, Kind.ord]
    · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact coh_rs_self hst
  | _ =>
    all_goals
      have hS : selStep1_revAt X i T = oSchurRevT X i T := by simp [selStep1_revAt, hc]
      rw [hS] at hg
      have hst := SelStep1CohStep.schurRev i T g hg
      have hE : oSchurRevT X i T = [Tracked.self T] := by simp [oSchurRevT, hc]
      rw [hE] at hg
      rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
      exact coh_rs_self hst

/-- The terms `j ≤ D` of the sum of [II, (4.21)] at the weight `c = (G_{xx})⁻¹` with index `i`. -/
private def cohTTerm (T : Graph k n) (i : ℕ) (c : Comp (Atom k n)) (ch : Charge) (j : ℕ) :
    Graph k n :=
  ⟨T.comps.eraseIdx i ++ List.replicate j { c with kind := .light ch, y := c.x },
    (-1 : Coeff) ^ j * mInvOf ch ^ (j + 1) * T.coeff⟩

/-- The remainder `W_D` of [II, (4.21)] at the weight `c = (G_{xx})⁻¹` with index `i`. -/
private def cohTW (T : Graph k n) (i : ℕ) (c : Comp (Atom k n)) (ch : Charge) (D : ℕ) :
    Graph k n :=
  ⟨T.comps.eraseIdx i ++ [{ c with kind := .wD ch D, y := c.x }], T.coeff⟩

private theorem coh_taylor_eq {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (D : ℕ) :
    oTaylorT D i T = [Tracked.self T] ∨
      oTaylorT D i T = ((List.range (D + 1)).map (cohTTerm T i c ch) ++
        [cohTW T i c ch D]).map Tracked.self := by
  simp only [oTaylorT, hc, hk]
  split_ifs
  · right
    simp [cohTTerm, cohTW, Tracked.self]
  · left
    rfl

private theorem coh_ord_tterm {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (j : ℕ) :
    (cohTTerm T i c ch j).ord = T.ord + j := by
  rw [cohTTerm, coh_ord_replace hc, hk]
  simp [Kind.ord, List.sum_replicate]

private theorem coh_ord_tW {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (D : ℕ) :
    (cohTW T i c ch D).ord = T.ord + D + 1 := by
  rw [cohTW, coh_ord_replace hc, hk]
  simp [Kind.ord]
  ring

/-- A step of [II, (4.21)] at the weight `(G_{xx})⁻¹` with index `i`. -/
private theorem coh_rs_taylor {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    {ch : Charge} (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (D : ℕ)
    (hg : Tracked.self g ∈ oTaylorT D i T) : CohRs X T g := by
  have hst := SelStep1CohStep.taylor (X := X) D i T g hg
  have hr : c.kind.isRandom = true := by rw [hk]; rfl
  rcases coh_taylor_eq hc hk D with hE | hE <;> rw [hE] at hg
  · rw [coh_self_inj (List.mem_singleton.1 hg)] at hst ⊢
    exact coh_rs_self hst
  · rcases List.mem_append.1 (coh_mem_self hg) with hg | hg
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
      refine coh_rs_replace hc _ _ hst ?_ (Or.inl ?_) ?_
      · rw [hk]; simp [Kind.ord, List.sum_replicate]
      · intro d hd; rw [List.eq_of_mem_replicate hd]; simp
      · intro d hd _; rw [List.eq_of_mem_replicate hd]; exact ⟨hr, rfl⟩
    · rw [List.mem_singleton.1 hg] at hst ⊢
      refine coh_rs_replace hc _ _ hst ?_ (Or.inl ?_) ?_
      · rw [hk]; simp [Kind.ord]; omega
      · simp
      · simp [hr]

/-- A step of `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge `c` with index `i`. -/
private theorem coh_rs_clean {X : Atom k n} {T g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hk : c.kind = .xdot)
    (hE : oXdotT i T = [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self)
    (hg : g ∈ [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩]) : CohRs X T g := by
  have hst : SelStep1CohStep X T g := .xdot i T g (by rw [hE]; exact List.mem_map_of_mem hg)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · have h := coh_rs_replace (X := X) hc [] T.coeff (by simpa using hst) (by simp [hk, Kind.ord])
      (Or.inl (by simp)) (by simp)
    simpa using h
  · exact coh_rs_replace hc _ _ hst (by simp [hk, mkC, Kind.ord])
      (Or.inr (by simp [hk, mkC, Kind.ord])) (by simp [mkC, Kind.isRandom])

end CohRs

/-! ## The last step: `O_merge` and the removal of redundant dotted edges -/

section CohFinal

variable {k n : ℕ}

private theorem coh_firstRed_some {m : ℕ} {L : List (Comp (Atom k m))} {i : ℕ}
    (h : selStep1_firstRed L = some i) :
    ∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step1_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep1_firstRed at h
  simpa using List.find?_some h

/-- The removals of redundant dotted edges keep the scaling order counted as in the paper, the
blocks and the components other than dotted edges. -/
private theorem coh_drop {m : ℕ} : ∀ (r : ℕ) (g : Graph k m),
    Relation.ReflTransGen SelStep1CohDrop g (selStep1_drop r g) ∧
      (selStep1_drop r g).paperOrd = g.paperOrd ∧
      (∀ a b, (selStep1_drop r g).SameBlock a b ↔ g.SameBlock a b) ∧
      (∀ c ∈ (selStep1_drop r g).comps, c ∈ g.comps) ∧
      (∀ c ∈ g.comps, c.kind ≠ .dot → c ∈ (selStep1_drop r g).comps)
  | 0, g => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [selStep1_drop, Relation.ReflTransGen.refl]
    exact fun _ h _ => h
  | r + 1, g => by
    rcases hf : selStep1_firstRed g.comps with _ | i
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [selStep1_drop, hf, Relation.ReflTransGen.refl]
      exact fun _ h _ => h
    · obtain ⟨c, hc, hk, hr⟩ := coh_firstRed_some hf
      obtain ⟨-, he, hord, hmem, hb, -⟩ := step1_drop_one g hc hk hr
      obtain ⟨h1, h2, h3, h4, h5⟩ := coh_drop r ⟨g.comps.eraseIdx i, g.coeff⟩
      simp only [selStep1_drop, hf]
      refine ⟨Relation.ReflTransGen.head ⟨i, c, hc, hk, hr, rfl⟩ h1, ?_,
        fun a b => (h3 a b).trans (hb a b), fun d hd => List.mem_of_mem_eraseIdx (h4 d hd),
        fun d hd hdk => h5 d (hmem d hd hdk) hdk⟩
      rw [h2]
      change _ - 2 * step1_eL _ = _ - 2 * step1_eL _
      linarith

private theorem coh_mergeComp_some {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind ≠ .dot) : ∃ c', mergeComp rep f c = some c' := by
  unfold mergeComp
  split_ifs with h1
  · simp [hk] at h1
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem coh_mergeComp_label {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) ∧ c'.kind.isRandom = c.kind.isRandom := by
  refine ⟨?_, ?_⟩
  · unfold mergeComp at h
    split_ifs at h
    · obtain rfl := Option.some.inj h
      rfl
    · obtain rfl := Option.some.inj h
      rfl
  · rcases mergeComp_kind h with h' | ⟨ch, h1, h2⟩
    · rw [h']
    · rw [h1, h2]
      rfl

/-- The output of the last step at a graph `T` with the clauses `Step1Base`: `O_merge`, then
removals of redundant dotted edges; the scaling order counted as in the paper is that of `T`,
the blocks are images of blocks of `T`, the external atoms are fixed, and a graph `T` of class
`ClsQ` gives a `Q`-graph. -/
private theorem coh_final {d S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Step1Base d S X Γ T)
    {t : Tracked k n} (ht : t ∈ selStep1_final T) :
    ∃ s : Tracked k n, T.mergeT = some s ∧ ∃ g' : Graph k s.nOut,
      Relation.ReflTransGen SelStep1CohDrop s.g g' ∧ t = ⟨s.nOut, g', s.f⟩ ∧
      g'.paperOrd = T.paperOrd ∧ (∀ a b, g'.SameBlock (s.f a) (s.f b) → T.SameBlock a b) ∧
      (∀ a, s.f (.inl a) = .inl a) ∧ (ClsQ X T → g'.IsQGraphAt (s.f X)) := by
  unfold selStep1_final at ht
  rcases hm : T.mergeT with _ | s
  · rw [hm] at ht
    cases ht
  rw [hm, List.mem_singleton] at ht
  have hs := mergeT_spec hm
  set g' := selStep1_drop (step1_eL s.g.comps - step1_eL T.comps).toNat s.g with hg'
  obtain ⟨hch, hpo, hsb, hsub, hkeep⟩ :=
    coh_drop (step1_eL s.g.comps - step1_eL T.comps).toNat s.g
  -- no solid edge inside a block
  have hconv : convN T = 0 := by
    unfold convN
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro hsol heq
    obtain ⟨-, e, he, hek, hexy⟩ := hB.solid c hc hsol
    have hsb' : T.SameBlock c.x c.y := coh_sameBlock_of_mrep heq
    apply hB.xapart e he hek
    rcases hexy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hsb'
    · rw [h1, h2]; exact hsb'.symm
  -- blocks of the graph given by `O_merge`
  have hbase : ∀ a b, s.f a = s.f b → T.SameBlock a b := fun a b h => by
    have : T.mrep a = T.mrep b := by
      by_contra h'
      exact hs.f_ne a b h' h
    exact coh_sameBlock_of_mrep this
  have hlift : ∀ w w', s.g.dotGraph.Reachable w w' →
      ∀ a b, s.f a = w → s.f b = w' → T.SameBlock a b := by
    intro w w' h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact fun a b ha hb => hbase a b (ha.trans hb.symm)
    | tail _ hadj ih =>
      intro a b ha hb
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      have key : ∀ c' ∈ s.g.comps, c'.kind = .dot → ∃ c ∈ T.comps, c.kind = .dot ∧
          c' = c.map s.f := by
        intro c' hc' hk'
        obtain ⟨c, hc, hmc⟩ := hs.mem_comps.1 hc'
        have hck : c.kind = .dot := by
          rcases mergeComp_kind hmc with h | ⟨ch, -, h⟩
          · rw [← h]; exact hk'
          · rw [h] at hk'; cases hk'
        rw [mergeComp_dot hck] at hmc
        split_ifs at hmc
        exact ⟨c, hc, hck, (Option.some.inj hmc).symm⟩
      obtain ⟨-, ⟨c', hc', hk', h1, h2⟩ | ⟨c', hc', hk', h1, h2⟩⟩ := hadj
      · obtain ⟨c, hc, hck, rfl⟩ := key c' hc' hk'
        exact ((ih a c.x ha h1).trans (coh_dot_sameBlock hc hck)).trans
          (hbase c.y b (h2.trans hb.symm))
      · obtain ⟨c, hc, hck, rfl⟩ := key c' hc' hk'
        exact ((ih a c.y ha h2).trans (coh_dot_sameBlock hc hck).symm).trans
          (hbase c.x b (h1.trans hb.symm))
  refine ⟨s, rfl, g', hch, ht, ?_, fun a b h => hlift _ _ ((hsb _ _).1 h) a b rfl rfl,
    hs.f_inl, fun hQ => ?_⟩
  · rw [hpo, Graph.paperOrd_eq_obl, hs.obl_eq, hconv, Graph.paperOrd_eq_obl]
    simp
  · -- the `Q`-graph
    have hfrom : ∀ c' ∈ g'.comps, ∃ c ∈ T.comps, c'.label = c.label.map (Prod.map id s.f) ∧
        c'.kind.isRandom = c.kind.isRandom := by
      intro c' hc'
      obtain ⟨c, hc, hmc⟩ := hs.mem_comps.1 (hsub c' hc')
      exact ⟨c, hc, coh_mergeComp_label hmc⟩
    obtain ⟨c, hc, hcl, -, -⟩ := hB.labex
    have hcr : c.kind.isRandom = true := (hB.wf c hc).2 (by rw [hcl]; rfl)
    have hcd : c.kind ≠ .dot := by intro h; rw [h] at hcr; cases hcr
    obtain ⟨c', hc'⟩ := coh_mergeComp_some (rep := T.mrep) (f := s.f) hcd
    have hc'k : c'.kind ≠ .dot := by
      rcases mergeComp_kind hc' with h | ⟨ch, -, h⟩ <;> rw [h]
      · exact hcd
      · simp
    refine ⟨⟨c', hkeep c' (hs.mem_comps.2 ⟨c, hc, hc'⟩) hc'k, ?_⟩, fun e he hre => ?_⟩
    · rw [(coh_mergeComp_label hc').1, hcl]
      rfl
    · obtain ⟨c₀, hc₀, hl₀, hr₀⟩ := hfrom e he
      rw [hl₀]
      rcases hre with hre | hre
      · rw [hr₀] at hre
        rw [hQ c₀ hc₀ hre]
        rfl
      · rw [hl₀] at hre
        rcases hB.lab c₀ hc₀ with h | h
        · rw [h] at hre; cases hre
        · rw [h]; rfl

end CohFinal

/-! ## Chains of steps and the outputs of the phases -/

section CohChain

variable {k n : ℕ}

private theorem coh_chain_fold {X : Atom k n} : ∀ (l : List (Graph k n)) (T T_f : Graph k n),
    List.IsChain (CohRs X) (T :: l) → (T :: l).getLast? = some T_f →
    T.ord ≤ T_f.ord ∧ (∀ a b, T_f.SameBlock a b → T.SameBlock a b ∨ T.ord + 2 ≤ T_f.ord) ∧
      (ClsQ X T → ClsQ X T_f)
  | [], T, T_f, _, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact ⟨le_rfl, fun _ _ h => Or.inl h, id⟩
  | g :: l, T, T_f, hc, h => by
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast?_cons_cons] at h
    obtain ⟨o1, b1, q1⟩ := coh_chain_fold l g T_f hc.2 h
    obtain ⟨-, o0, b0, q0⟩ := hc.1
    refine ⟨o0.trans o1, fun a b hab => ?_, fun h => q1 (q0 h)⟩
    rcases b1 a b hab with h | h
    · rcases b0 with b0 | b0
      · exact Or.inl (b0 a b h)
      · exact Or.inr (by linarith)
    · exact Or.inr (by linarith)

private theorem coh_chain_clsQ {X : Atom k n} : ∀ (l : List (Graph k n)) (T_f : Graph k n),
    List.IsChain (CohRs X) l → l.getLast? = some T_f → ∀ T' ∈ l, ClsQ X T' → ClsQ X T_f
  | [], _, _, _, _, hT', _ => by cases hT'
  | T :: l, T_f, hc, h, T', hT', hQ => by
    rcases List.mem_cons.1 hT' with rfl | hT'
    · exact (coh_chain_fold l T' T_f hc h).2.2 hQ
    · cases l with
      | nil => cases hT'
      | cons g l =>
        rw [List.isChain_cons_cons] at hc
        rw [List.getLast?_cons_cons] at h
        exact coh_chain_clsQ (g :: l) T_f hc.2 h T' hT' hQ

private theorem coh_wit_cons {X : Atom k n} {Γ : Graph k n} {l : List (Graph k n)} (T : Graph k n)
    (h : SelStep1CohWit X Γ l) : SelStep1CohWit X Γ (T :: l) := by
  obtain ⟨c, hc, hl, hr, j, T', g, h1, h2, h3⟩ := h
  exact ⟨c, hc, hl, hr, j + 1, T', g, by simpa using h1, by simpa using h2, h3⟩

/-- An output `t` of a phase started at `T`: a chain of steps from `T` to a graph `T_f` with the
clauses `Step1Base`, `t` an output of the last step at `T_f`, and the property `Pc` of the
chain. -/
private def CohOut (X : Atom k n) (Γ : Graph k n) (Pc : List (Graph k n) → Prop) (T : Graph k n)
    (t : Tracked k n) : Prop :=
  ∃ (l : List (Graph k n)) (T_f : Graph k n), List.IsChain (CohRs X) (T :: l) ∧
    (T :: l).getLast? = some T_f ∧ (∃ d S, Step1Base d S X Γ T_f) ∧ t ∈ selStep1_final T_f ∧
    Pc (T :: l)

private theorem CohOut.cons {X : Atom k n} {Γ : Graph k n} {Pc Pc' : List (Graph k n) → Prop}
    {T g : Graph k n} {t : Tracked k n} (h : CohOut X Γ Pc' g t) (hR : CohRs X T g)
    (hP : ∀ l, Pc' (g :: l) → Pc (T :: g :: l)) : CohOut X Γ Pc T t := by
  obtain ⟨l, T_f, hc, hl, hB, ht, hp⟩ := h
  exact ⟨g :: l, T_f, hc.cons_cons hR, by rw [List.getLast?_cons_cons]; exact hl, hB, ht,
    hP l hp⟩

private theorem CohOut.final {d S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    {Pc : List (Graph k n) → Prop} (hB : Step1Base d S X Γ T) {t : Tracked k n}
    (ht : t ∈ selStep1_final T) (hP : Pc [T]) : CohOut X Γ Pc T t :=
  ⟨[], T, List.isChain_singleton T, rfl, ⟨d, S, hB⟩, ht, hP⟩

private theorem CohOut.mono {X : Atom k n} {Γ T : Graph k n} {Pc Pc' : List (Graph k n) → Prop}
    {t : Tracked k n} (h : CohOut X Γ Pc T t) (hP : ∀ l, Pc l → Pc' l) : CohOut X Γ Pc' T t := by
  obtain ⟨l, T_f, hc, hl, hB, ht, hp⟩ := h
  exact ⟨l, T_f, hc, hl, hB, ht, hP _ hp⟩

end CohChain

section CohPhases

variable {k n : ℕ}

private theorem coh_clean_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      (ClsQ X T ∨ ClsW d X Γ T) → ∀ t ∈ selStep1_clean m T, CohOut X Γ (fun _ => True) T t := by
  intro m
  induction m with
  | zero =>
    intro T hB _ _ _ _ t ht
    simp only [selStep1_clean] at ht
    exact CohOut.final hB ht trivial
  | succ m ih =>
    intro T hB hK hmin hinv hcls t ht
    rcases hf : T.comps.findIdx? (badB T.comps) with _ | i
    · simp only [selStep1_clean, hf] at ht
      exact CohOut.final hB ht trivial
    · obtain ⟨c, hc, hcb⟩ := coh_findIdx_some hf
      obtain ⟨hE, -, -, hG⟩ := selStep1_clean_step hB hK hmin hinv hcls hc hcb
      have hk : c.kind = .xdot := by
        simp only [badB, Bool.and_eq_true, decide_eq_true_eq] at hcb
        exact hcb.1
      simp only [selStep1_clean, hf] at ht
      rw [hE, coh_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      by_cases hxa : g.XdotApart
      · rw [ite_eq_left hxa] at ht
        obtain ⟨hB', hK', hmin', hinv', hcls', -⟩ := (hG g hg).2 hxa
        exact (ih g hB' hK' hmin' hinv' hcls' t ht).cons (coh_rs_clean hc hk hE hg)
          fun _ _ => trivial
      · rw [ite_eq_right hxa] at ht
        cases ht

private theorem coh_taylor_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), nInv T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (ClsQ X T ∨ ClsW d X Γ T) →
      ∀ t ∈ selStep1_taylor d m T, CohOut X Γ (fun _ => True) T t := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hcls t ht
    have hinv : ∀ c ∈ T.comps, c.kind.step1_isInvB = false := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => c.kind.step1_isInvB :=
        List.mem_filter.2 ⟨hc, by simpa using h⟩
      have := List.length_pos_of_mem this
      unfold nInv at hm
      omega
    simp only [selStep1_taylor] at ht
    exact coh_clean_out _ T hB hK hmin hinv hcls t ht
  | succ m ih =>
    intro T hm hB hK hmin hcls t ht
    rcases hf : T.comps.findIdx? (fun c => c.kind.step1_isInvB) with _ | i
    · simp only [selStep1_taylor, hf] at ht
      exact coh_clean_out _ T hB hK hmin (List.findIdx?_eq_none_iff.1 hf) hcls t ht
    · obtain ⟨c, hc, hci⟩ := coh_findIdx_some hf
      obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
        revert hci
        cases c.kind <;> simp [Kind.step1_isInvB]
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_taylor_step hB hK hmin hcls hc hci
      simp only [selStep1_taylor, hf] at ht
      have hE' := hE
      rw [hE, coh_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      obtain ⟨hB', hK', hmin', hcls', hcnt⟩ := hGs g hg
      exact (ih g (by omega) hB' hK' hmin' hcls' t ht).cons
        (coh_rs_taylor hc hk d (by rw [hE']; exact List.mem_map_of_mem hg)) fun _ _ => trivial

private theorem coh_rev_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), nMin T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      (ClsQ X T ∨ ClsW d X Γ T) → ∀ t ∈ selStep1_rev d m X T, CohOut X Γ (fun _ => True) T t := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hcls t ht
    have hmin : ∀ c ∈ T.comps, c.minor = [] := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => !c.minor.isEmpty :=
        List.mem_filter.2 ⟨hc, by simpa [List.isEmpty_iff] using h⟩
      have := List.length_pos_of_mem this
      unfold nMin at hm
      omega
    simp only [selStep1_rev] at ht
    exact coh_taylor_out _ T le_rfl hB hK hmin hcls t ht
  | succ m ih =>
    intro T hm hB hK hcls t ht
    rcases hf : T.comps.findIdx? (fun c => !c.minor.isEmpty) with _ | i
    · have hmin : ∀ c ∈ T.comps, c.minor = [] := by
        intro c hc
        have := List.findIdx?_eq_none_iff.1 hf c hc
        simpa [List.isEmpty_iff] using this
      simp only [selStep1_rev, hf] at ht
      exact coh_taylor_out _ T le_rfl hB hK hmin hcls t ht
    · obtain ⟨c, hc, hcm⟩ := coh_findIdx_some hf
      have hcT : c ∈ T.comps := List.mem_of_getElem? hc
      obtain ⟨hmX, -, hx, hy, -⟩ : c.minor = [X] ∧ _ := by
        rcases hB.minor c hcT with h | h
        · rw [h] at hcm; simp at hcm
        · exact h
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_rev_step hB hK hcls hc hmX
      simp only [selStep1_rev, hf] at ht
      have hE' := hE
      rw [hE, coh_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      obtain ⟨⟨hB', hcls', hmin', -⟩, hK'⟩ := hGs g hg
      exact (ih g (by omega) hB' hK' hcls' t ht).cons
        (coh_rs_rev hc hx hy (by rw [hE']; exact List.mem_map_of_mem hg)) fun _ _ => trivial

private theorem coh_absorb_out {d S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base d S X Γ T) (hK : Step1OK1 Γ T) (hnp : nPend X T.comps = 0)
    (hcls : ClsW d X Γ T ∨ AllPend X T) :
    ∀ t ∈ selStep1_absorb d X T,
      CohOut X Γ (fun l => AllPend X T → ∃ T' ∈ l, ClsQ X T') T t := by
  intro t ht
  unfold selStep1_absorb at ht
  by_cases hA : AllPend X T
  · rw [ite_eq_left hA] at ht
    obtain ⟨hB', hQ, -⟩ := absorb_step hB hnp hA
    obtain ⟨c, hc, hcl, -⟩ := hB.labex
    exact (coh_rev_out _ _ le_rfl hB' (hK.absorb X) (Or.inl hQ) t ht).cons
      (coh_rs_absorb ⟨c, hc, hcl⟩ hB.lab)
      fun l _ _ => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hQ⟩
  · rw [ite_eq_right hA] at ht
    exact (coh_rev_out _ T le_rfl hB hK (Or.inr (hcls.resolve_right hA)) t ht).mono
      fun _ _ h => absurd h hA

private theorem coh_allPend_first {X : Atom k n} {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hA : AllPend X T) : AllPend X ⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ := by
  intro d hd hl hr
  rcases List.mem_append.1 hd with h | h
  · exact hA d (List.mem_of_mem_eraseIdx h) hl hr
  · rw [List.mem_singleton.1 h]
    exact Or.inr rfl

private theorem coh_schur_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} (hΓ : Γ.Plain) :
    ∀ (m : ℕ) (T : Graph k n), nPend X T.comps ≤ m → Step1Base d S X Γ T → Step1OK1 Γ T →
      PendInv X Γ T → (ClsW d X Γ T ∨ AllPend X T) →
      ∀ t ∈ selStep1_schur d m X T, CohOut X Γ
        (fun l => AllPend X T → SelStep1CohWit X Γ l ∨ ∃ T' ∈ l, ClsQ X T') T t := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK _ hcls t ht
    simp only [selStep1_schur] at ht
    exact (coh_absorb_out hB hK (by omega) hcls t ht).mono fun _ h hA => Or.inr (h hA)
  | succ m ih =>
    intro T hm hB hK hP hcls t ht
    rcases hf : T.comps.findIdx? (pendB X) with _ | i
    · have hnp : nPend X T.comps = 0 := by
        unfold nPend
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc
        simp [List.findIdx?_eq_none_iff.1 hf c hc]
      simp only [selStep1_schur, hf] at ht
      exact (coh_absorb_out hB hK hnp hcls t ht).mono fun _ h hA => Or.inr (h hA)
    · obtain ⟨c, hc, hcp⟩ := coh_findIdx_some hf
      have hcT : c ∈ T.comps := List.mem_of_getElem? hc
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_schur_step hΓ hB hK hP hcls hc hcp
      simp only [selStep1_schur, hf] at ht
      have hE' := hE
      rw [hE, coh_bind_self, List.mem_flatMap] at ht
      obtain ⟨g, hg, ht⟩ := ht
      obtain ⟨⟨hB', hP', hcls', hp'⟩, hK'⟩ := hGs g hg
      obtain ⟨hR, hform⟩ := coh_rs_schur hc hcp (hB.wf c hcT)
        (by rw [hE']; exact List.mem_map_of_mem hg)
      refine (ih g (by omega) hB' hK' hP' hcls' t ht).cons hR fun l hl hA => ?_
      have hshift : (SelStep1CohWit X Γ (g :: l) ∨ ∃ T' ∈ g :: l, ClsQ X T') →
          SelStep1CohWit X Γ (T :: g :: l) ∨ ∃ T' ∈ T :: g :: l, ClsQ X T' := by
        rintro (h | ⟨T', hT', hQ⟩)
        · exact Or.inl (coh_wit_cons T h)
        · exact Or.inr ⟨T', List.mem_cons_of_mem _ hT', hQ⟩
      rcases hform with rfl | rfl | ⟨ch, rfl⟩
      · exact hshift (hl hA)
      · exact hshift (hl (coh_allPend_first hA))
      · have hpp := hcp
        simp only [pendB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hpp
        refine Or.inl ⟨c, (hP c hcT hcp).1, hpp.1.1.1.1, hpp.1.1.1.2, 0, T, _, rfl, rfl,
          Or.inl ⟨i, ch, hc, rfl⟩⟩

private theorem coh_hasX_mono {L L' : List (Comp (Atom k n))} (h : ∀ d ∈ L, d ∈ L')
    {u v : Atom k n} (hx : Step1HasX L u v) : Step1HasX L' u v := by
  obtain ⟨d, hd, rest⟩ := hx
  exact ⟨d, h d hd, rest⟩

private theorem coh_sizeΦ_append {D' : ℕ} {X : Atom k n} (L : List (Comp (Atom k n)))
    {κ : Kind} (hκ : κ = .dot ∨ κ = .xdot) (u v : Atom k n) :
    step1_sizeΦ D' X (L ++ [mkC κ u v]) = step1_sizeΦ D' X L + 1 := by
  unfold step1_sizeΦ nPend nMin nInv
  rw [List.filter_append, List.filter_append, List.filter_append]
  rcases hκ with rfl | rfl <;> simp [mkC, pendB, Kind.isRandom, Kind.step1_isInvB] <;> ring

open Classical in
private theorem coh_split_out {d S : ℕ} {X : Atom k n} {Γ : Graph k n} (hΓ : Γ.Plain)
    (hfree : Γ.UnlabelledFreeAtBlock X) :
    ∀ (us : List (Atom k n)) (T : Graph k n),
      Step1Base d S X Γ T → Step1OK1 Γ T → step1_sizeΦ d X T.comps + us.length ≤ S →
      step1_dg T.comps = step1_dg Γ.comps →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      AllPend X T →
      (∀ c ∈ T.comps, pendB X c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], Step1HasX T.comps u X ∨ u ∈ us) →
      (∀ u ∈ us, ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧ u ∈ [c.x, c.y]) →
      ∀ t ∈ selStep1_split d X us T, CohOut X Γ
        (fun l => SelStep1CohWit X Γ l ∨ ∃ T' ∈ l, ClsQ X T') T t
  | [], T, hB, hK, _, _, _, _, hA, hP, _ => by
    have hP' : PendInv X Γ T := by
      intro c hc hp
      obtain ⟨h1, h2⟩ := hP c hc hp
      refine ⟨h1, ?_, ?_⟩
      · rcases h2 c.x (by simp) with h | h
        · exact h
        · simp at h
      · rcases h2 c.y (by simp) with h | h
        · exact h
        · simp at h
    intro t ht
    simp only [selStep1_split] at ht
    exact (coh_schur_out hΓ _ T le_rfl hB hK hP' (Or.inr hA) t ht).mono fun _ h => h hA
  | u :: us, T, hB, hK, hsz, hdg, hmin, hinv, hA, hP, hus => by
    intro t ht
    obtain ⟨c₀, hc₀, hl₀, hr₀, hu₀⟩ := hus u (List.mem_cons_self ..)
    have hBsz : step1_sizeΦ d X T.comps + 1 ≤ S := by
      simp only [List.length_cons] at hsz
      omega
    obtain ⟨hE, -, -, hgood₁, hB₂, hK₂, hdg₂⟩ :=
      selStep1_split_step hfree hB hK hBsz hdg hc₀ hl₀ hr₀ hu₀
    simp only [selStep1_split, List.mem_append] at ht
    rcases ht with ht | ht
    · -- the term with `u` identified with `X`
      by_cases hxa : (⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart
      · rw [ite_eq_left hxa] at ht
        obtain ⟨hB₁, hK₁, hcls⟩ := hgood₁ hxa
        refine (coh_clean_out _ _ hB₁ hK₁ ?_ ?_ (Or.inr hcls) t ht).cons
          (coh_rs_append .dot (Or.inl rfl) u X (.split u T _ (by rw [hE]; simp)))
          fun l _ => Or.inl ⟨c₀, hc₀, hl₀, hr₀, 0, T, _, rfl, rfl, Or.inr ⟨u, hu₀, rfl⟩⟩
        · intro d hd
          rcases List.mem_append.1 hd with h | h
          · exact hmin d h
          · rw [List.mem_singleton.1 h]; rfl
        · intro d hd
          rcases List.mem_append.1 hd with h | h
          · exact hinv d h
          · rw [List.mem_singleton.1 h]; rfl
      · rw [ite_eq_right hxa] at ht
        cases ht
    · -- the term with `u ≠ X`
      refine (coh_split_out hΓ hfree us _ hB₂ hK₂ ?_ hdg₂ ?_ ?_ ?_ ?_
        (fun v hv => hus v (List.mem_cons_of_mem _ hv)) t ht).cons
        (coh_rs_append .xdot (Or.inr rfl) u X (.split u T _ (by rw [hE]; simp))) ?_
      · rw [coh_sizeΦ_append _ (Or.inr rfl)]
        simp only [List.length_cons] at hsz
        omega
      · intro d hd
        rcases List.mem_append.1 hd with h | h
        · exact hmin d h
        · rw [List.mem_singleton.1 h]; rfl
      · intro d hd
        rcases List.mem_append.1 hd with h | h
        · exact hinv d h
        · rw [List.mem_singleton.1 h]; rfl
      · intro d hd hdl hdr
        rcases List.mem_append.1 hd with h | h
        · exact hA d h hdl hdr
        · rw [List.mem_singleton.1 h] at hdr; simp [mkC, Kind.isRandom] at hdr
      · intro d hd hdp
        rcases List.mem_append.1 hd with h | h
        · obtain ⟨h1, h2⟩ := hP d h hdp
          refine ⟨h1, fun v hv => ?_⟩
          rcases h2 v hv with h3 | h3
          · exact Or.inl (coh_hasX_mono (fun d hd => List.mem_append_left _ hd) h3)
          · rcases List.mem_cons.1 h3 with rfl | h4
            · exact Or.inl ⟨mkC .xdot v X, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
            · exact Or.inr h4
        · rw [List.mem_singleton.1 h] at hdp; simp [pendB, mkC, Kind.isRandom] at hdp
      · rintro l (h | ⟨T', hT', hQ⟩)
        · exact Or.inl (coh_wit_cons T h)
        · exact Or.inr ⟨T', List.mem_cons_of_mem _ hT', hQ⟩

end CohPhases

/-! ## The input of the run -/

section CohRoot

variable {k : ℕ}

/-- The clauses of the phases at the input `Γ`, for the Taylor degree `d` and the size bound
`(d + 6) C + 1`. -/
private theorem coh_root {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} (d : ℕ) (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart)
    (hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)) :
    Step1Base d ((d + 6) * C + 1) (.inr x₀) Γ Γ ∧
      step1_sizeΦ d (.inr x₀) Γ.comps + (selStep1_us Γ).length ≤ (d + 6) * C + 1 ∧
      (∀ c ∈ Γ.comps, c.minor = []) ∧ (∀ c ∈ Γ.comps, c.kind.step1_isInvB = false) ∧
      AllPend (.inr x₀) Γ ∧
      (∀ c ∈ Γ.comps, pendB (.inr x₀) c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], Step1HasX Γ.comps u (.inr x₀) ∨ u ∈ selStep1_us Γ) ∧
      (∀ u ∈ selStep1_us Γ, ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧
        u ∈ [c.x, c.y]) := by
  set X : Atom k n₀ := .inr x₀ with hXdef
  have hsize := hN.1.size
  have hlenΓ : Γ.comps.length ≤ C := by omega
  have hminΓ : nMin Γ.comps = 0 := by
    unfold nMin
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [(hP c hc).1]
  have hinv : ∀ c ∈ Γ.comps, c.kind.step1_isInvB = false := fun c hc => by
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.step1_isInvB]
  have hinvΓ : nInv Γ.comps = 0 := by
    unfold nInv
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [hinv c hc]
  have hΦ : step1_sizeΦ d X Γ.comps ≤ (d + 4) * C := by
    have hpendΓ : nPend X Γ.comps ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    unfold step1_sizeΦ
    rw [hminΓ, hinvΓ]
    have h1 : (d + 3) * (nPend X Γ.comps + 0) ≤ (d + 3) * C :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  set R := Γ.comps.filter fun c => c.label.isNone && c.kind.isRandom with hR
  have hus : selStep1_us Γ = R.flatMap fun c => [c.x, c.y] := rfl
  have hlenus : (selStep1_us Γ).length ≤ 2 * C := by
    have h1 : (selStep1_us Γ).length = 2 * R.length := by
      rw [hus, List.length_flatMap]
      simp only [List.length_cons, List.length_nil]
      induction R with
      | nil => simp
      | cons a l ih => simp; ring
    have h2 : R.length ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    omega
  have hS : (d + 4) * C + 2 * C ≤ (d + 6) * C + 1 := by nlinarith
  refine ⟨base_init hN hQ hP hxa rfl (by omega), by omega, fun c hc => (hP c hc).1, hinv, ?_, ?_,
    ?_⟩
  · intro c hc hl hr
    left
    have hcx := (hfree c hc hl hr).1
    have hcy := (hfree c hc hl hr).2
    have hx : c.x ≠ X := fun h => hcx (by rw [h]; exact SimpleGraph.Reachable.refl _)
    have hy : c.y ≠ X := fun h => hcy (by rw [h]; exact SimpleGraph.Reachable.refl _)
    simp [pendB, hl, hr, (hP c hc).1, hx, hy]
  · intro c hc hp
    refine ⟨hc, fun u hu => Or.inr ?_⟩
    rw [hus, List.mem_flatMap]
    refine ⟨c, ?_, hu⟩
    rw [hR, List.mem_filter]
    simp only [pendB, Bool.and_eq_true] at hp
    exact ⟨hc, by simp only [Bool.and_eq_true]; exact ⟨hp.1.1.1.1, hp.1.1.1.2⟩⟩
  · intro u hu
    rw [hus, List.mem_flatMap] at hu
    obtain ⟨c, hcR, hu⟩ := hu
    rw [hR, List.mem_filter] at hcR
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hcR
    exact ⟨c, hcR.1, hcR.2.1, hcR.2.2, hu⟩

/-- Every output of the run in the main case comes from a chain of steps from `Γ`. -/
private theorem coh_run_out {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} (d : ℕ) (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart)
    (hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)) {t : Tracked k n₀}
    (ht : t ∈ selStep1 d (.inr x₀) Γ) :
    CohOut (.inr x₀) Γ (fun l => SelStep1CohWit (.inr x₀) Γ l ∨ ∃ T' ∈ l, ClsQ (.inr x₀) T') Γ
      t := by
  rw [selStep1, ite_eq_left hxa, ite_eq_left hfree] at ht
  obtain ⟨hB, hsz, hmin, hinv, hA, hPd, hus⟩ := coh_root d hN hQ hP hxa hfree
  exact coh_split_out hP hfree _ Γ hB (Step1OK1.refl Γ) hsz rfl hmin hinv hA hPd hus t ht

end CohRoot

/-! ## Order and blocks of the outputs -/

section CohOrder

/-- **Order and blocks of the outputs of the run** ([II, Lemma 4.11]): for a normal regular graph
`Γ = Γ₀ Q_x(Γ̃₀)` with bound `C` (`x` internal) and three external atoms `⊗, ⊕, ⊖`, every output
graph of the run with Taylor degree `d` has scaling order at least the scaling order `p` of `Γ`,
both counted as in the paper; if `⊕` and `⊖` lie in one dotted block of the output graph but not
of `Γ`, its scaling order is at least `p + 2`. -/
theorem selStep1Coh_order {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph 3 n₀} (d : ℕ) (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain) :
    ∀ t ∈ selStep1 d (.inr x₀) Γ, Γ.paperOrd ≤ t.g.paperOrd ∧
      (¬ Γ.PMBlock → t.g.PMBlock → Γ.paperOrd + 2 ≤ t.g.paperOrd) := by
  intro t ht
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep1, ite_eq_right hxa] at ht
    cases ht
  by_cases hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)
  swap
  · rw [selStep1, ite_eq_left hxa, ite_eq_right hfree, List.mem_singleton] at ht
    subst ht
    exact ⟨le_rfl, fun h h' => absurd h' h⟩
  obtain ⟨l, T_f, hc, hl, ⟨d', S', hBf⟩, htf, -⟩ := coh_run_out d hN hQ hP hxa hfree ht
  obtain ⟨-, hblk, -⟩ := coh_chain_fold l Γ T_f hc hl
  have ho : Γ.ord ≤ T_f.ord := by
    have := hBf.ord
    have : (0 : ℤ) ≤ ((d' + 1 : ℕ) : ℤ) * (step1_nWD T_f.comps : ℤ) := by positivity
    push_cast at *
    linarith
  obtain ⟨s, -, g', -, rfl, hpo, hsb, hinl, -⟩ := coh_final hBf htf
  have hex : T_f.dotExcess = Γ.dotExcess := hBf.excess
  have hT : T_f.paperOrd = T_f.ord - 2 * Γ.dotExcess := by
    unfold Graph.paperOrd
    rw [hex]
  have hΓ : Γ.paperOrd = Γ.ord - 2 * Γ.dotExcess := rfl
  refine ⟨?_, fun hn hpm => ?_⟩
  · change Γ.paperOrd ≤ g'.paperOrd
    rw [hpo, hT, hΓ]
    linarith
  · rw [Graph.pmBlock_iff_sameBlock] at hn
    have hpm' : g'.SameBlock (s.f (.inl 1)) (s.f (.inl 2)) := by
      rw [hinl 1, hinl 2]
      exact (Graph.pmBlock_iff_sameBlock g').1 hpm
    rcases hblk _ _ (hsb _ _ hpm') with h | h
    · exact absurd h hn
    · change Γ.paperOrd + 2 ≤ g'.paperOrd
      rw [hpo, hT, hΓ]
      linarith

end CohOrder

/-! ## The history of the outputs -/

section CohHistory

/-- **The history of the outputs of the run** (the proof of [II, Lemma 4.11]): for a normal
regular graph `Γ = Γ₀ Q_x(Γ̃₀)` with bound `C` (`x` internal), every output `t` of the run with
Taylor degree `d` is `Γ` itself when `Γ₀` has a weight or edge attached to the block of `x`;
otherwise there is a chain `Γ = g₀, g₁, …, g_m = T` of steps of the run (`SelStep1CohStep`, each
with the identity atom map), then `O_merge` at `T` and removals of redundant dotted edges
(`SelStep1CohDrop`), giving `t` with the atom map of `O_merge`. If `Γ₀` has no weight or edge
attached to the block of `x` and `t` is a graph `Γ_ω Q_x(Γ̃_ω)` that is not a `Q`-graph, the chain
contains the second term of [II, (4.17)] at a weight or edge `c` of `Γ₀`, or a split term
`1_{u = x}` at an atom `u` of such a `c` (`SelStep1CohWit`). -/
theorem selStep1Coh_history {k C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} (d : ℕ)
    (hN : Γ.Normal C) (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain) :
    ∀ t ∈ selStep1 d (.inr x₀) Γ,
      (¬ Γ.UnlabelledFreeAtBlock (.inr x₀) ∧ t = Tracked.self Γ) ∨
      ∃ (gs : List (Graph k n₀)) (T : Graph k n₀) (s : Tracked k n₀) (g' : Graph k s.nOut),
        List.IsChain (SelStep1CohStep (.inr x₀)) (Γ :: gs) ∧ (Γ :: gs).getLast? = some T ∧
        T.mergeT = some s ∧ Relation.ReflTransGen SelStep1CohDrop s.g g' ∧
        t = ⟨s.nOut, g', s.f⟩ ∧
        (Γ.UnlabelledFreeAtBlock (.inr x₀) → t.g.Plain → t.g.IsQFormAt (t.f (.inr x₀)) →
          ¬ t.g.IsQGraphAt (t.f (.inr x₀)) → SelStep1CohWit (.inr x₀) Γ (Γ :: gs)) := by
  intro t ht
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep1, ite_eq_right hxa] at ht
    cases ht
  by_cases hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)
  swap
  · rw [selStep1, ite_eq_left hxa, ite_eq_right hfree, List.mem_singleton] at ht
    exact Or.inl ⟨hfree, ht⟩
  obtain ⟨l, T_f, hc, hl, ⟨d', S', hBf⟩, htf, hw⟩ := coh_run_out d hN hQ hP hxa hfree ht
  obtain ⟨s, hm, g', hdr, rfl, -, -, -, hQg⟩ := coh_final hBf htf
  refine Or.inr ⟨l, T_f, s, g', hc.imp fun _ _ h => h.1, hl, hm, hdr, rfl,
    fun _ _ _ hnQ => ?_⟩
  rcases hw with h | ⟨T', hT', hQ'⟩
  · exact h
  · exact absurd (hQg (coh_chain_clsQ _ T_f hc hl T' hT' hQ')) hnQ

end CohHistory

/-! ## Coherence in the Taylor degree -/

section CohRel

variable {k n : ℕ}

/-- `F` and `F'` have a common part `A`; the other terms have scaling order at least `lo`, counted
as in the paper. -/
private def CohRel (lo : ℤ) (F F' : TExpansion k n) : Prop :=
  ∃ A B B' : TExpansion k n, F.Perm (A ++ B) ∧ F'.Perm (A ++ B') ∧
    ∀ t ∈ B ++ B', lo ≤ t.g.paperOrd

private theorem CohRel.refl (lo : ℤ) (F : TExpansion k n) : CohRel lo F F :=
  ⟨F, [], [], by simp, by simp, by simp⟩

private theorem CohRel.append {lo : ℤ} {F G F' G' : TExpansion k n} (h₁ : CohRel lo F F')
    (h₂ : CohRel lo G G') : CohRel lo (F ++ G) (F' ++ G') := by
  obtain ⟨A₁, B₁, B₁', p₁, p₁', b₁⟩ := h₁
  obtain ⟨A₂, B₂, B₂', p₂, p₂', b₂⟩ := h₂
  have key : ∀ B C : TExpansion k n, ((A₁ ++ B) ++ (A₂ ++ C)).Perm ((A₁ ++ A₂) ++ (B ++ C)) := by
    intro B C
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := B) (l₂ := A₂)).append_right C).append_left A₁
  refine ⟨A₁ ++ A₂, B₁ ++ B₂, B₁' ++ B₂', (p₁.append p₂).trans (key _ _),
    (p₁'.append p₂').trans (key _ _), fun t ht => ?_⟩
  simp only [List.mem_append] at ht
  rcases ht with (h | h) | (h | h)
  · exact b₁ t (List.mem_append_left _ h)
  · exact b₂ t (List.mem_append_left _ h)
  · exact b₁ t (List.mem_append_right _ h)
  · exact b₂ t (List.mem_append_right _ h)

private theorem CohRel.bound {lo : ℤ} {F F' : TExpansion k n} (h : ∀ t ∈ F, lo ≤ t.g.paperOrd)
    (h' : ∀ t ∈ F', lo ≤ t.g.paperOrd) : CohRel lo F F' :=
  ⟨[], F, F', by simp, by simp, fun t ht => (List.mem_append.1 ht).elim (h t) (h' t)⟩

private theorem CohRel.flatMap {α : Type*} {lo : ℤ} (f f' : α → TExpansion k n) :
    ∀ L : List α, (∀ a ∈ L, CohRel lo (f a) (f' a)) → CohRel lo (L.flatMap f) (L.flatMap f')
  | [], _ => CohRel.refl lo []
  | a :: L, h => by
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append
      (CohRel.flatMap f f' L fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem coh_map_self_inj {Gs Gs' : List (Graph k n)}
    (h : Gs.map Tracked.self = Gs'.map Tracked.self) : Gs = Gs' :=
  List.map_injective_iff.2 (fun _ _ h => coh_self_inj h) h

/-- An output of a phase started at `g` has scaling order at least that of `g` minus twice the
dot excess of `Γ`. -/
private theorem coh_out_bound {X : Atom k n} {Γ : Graph k n} {Pc : List (Graph k n) → Prop}
    {g : Graph k n} {t : Tracked k n} (h : CohOut X Γ Pc g t) :
    g.ord - 2 * Γ.dotExcess ≤ t.g.paperOrd := by
  obtain ⟨l, T_f, hc, hl, ⟨d', S', hBf⟩, htf, -⟩ := h
  obtain ⟨o, -, -⟩ := coh_chain_fold l g T_f hc hl
  obtain ⟨s, -, g', -, rfl, hpo, -⟩ := coh_final hBf htf
  have hex : T_f.dotExcess = Γ.dotExcess := hBf.excess
  change _ ≤ g'.paperOrd
  rw [hpo]
  unfold Graph.paperOrd
  rw [hex]
  linarith

private theorem coh_base_ord {d S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base d S X Γ T) : Γ.ord ≤ T.ord := by
  have := hB.ord
  have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (step1_nWD T.comps : ℤ) := by positivity
  push_cast at *
  linarith

private theorem coh_taylor_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), nInv T.comps ≤ m →
      Step1Base d S X Γ T → (ClsQ X T ∨ ClsW d X Γ T) →
      Step1Base d' S' X Γ T → (ClsQ X T ∨ ClsW d' X Γ T) →
      Step1OK1 Γ T → (∀ c ∈ T.comps, c.minor = []) →
      CohRel (Γ.paperOrd + d + 1) (selStep1_taylor d m T) (selStep1_taylor d' m T) := by
  intro m
  induction m with
  | zero =>
    intro T _ _ _ _ _ _ _
    simp only [selStep1_taylor]
    exact CohRel.refl _ _
  | succ m ih =>
    intro T hm hB hcls hB' hcls' hK hmin
    rcases hf : T.comps.findIdx? (fun c => c.kind.step1_isInvB) with _ | i
    · simp only [selStep1_taylor, hf]
      exact CohRel.refl _ _
    obtain ⟨c, hc, hci⟩ := coh_findIdx_some hf
    obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
      revert hci
      cases c.kind <;> simp [Kind.step1_isInvB]
    obtain ⟨Gs, hE, hlen, -, hGs⟩ := selStep1_taylor_step hB hK hmin hcls hc hci
    obtain ⟨Gs', hE', hlen', -, hGs'⟩ := selStep1_taylor_step hB' hK hmin hcls' hc hci
    have hL : ∀ (D : ℕ) (Hs : List (Graph k n)), oTaylorT D i T = Hs.map Tracked.self →
        Hs.length = D + 2 → oTaylorT D i T =
          ((List.range (D + 1)).map (cohTTerm T i c ch) ++ [cohTW T i c ch D]).map
            Tracked.self := by
      intro D Hs hH hlH
      rcases coh_taylor_eq hc hk D with h | h
      · rw [h] at hH
        have := congrArg List.length hH
        simp only [List.length_singleton, List.length_map] at this
        omega
      · exact h
    have hLd := hL d Gs hE hlen
    have hLd' := hL d' Gs' hE' hlen'
    have hmem : ∀ g, g ∈ (List.range (d + 1)).map (cohTTerm T i c ch) ++ [cohTW T i c ch d] →
        g ∈ Gs := fun g hg =>
      coh_mem_self (hE ▸ hLd ▸ List.mem_map_of_mem hg)
    have hmem' : ∀ g, g ∈ (List.range (d' + 1)).map (cohTTerm T i c ch) ++ [cohTW T i c ch d'] →
        g ∈ Gs' := fun g hg =>
      coh_mem_self (hE' ▸ hLd' ▸ List.mem_map_of_mem hg)
    have hTo := coh_base_ord hB
    have hpo : Γ.paperOrd = Γ.ord - 2 * Γ.dotExcess := rfl
    simp only [selStep1_taylor, hf]
    rw [hLd, hLd', coh_bind_self, coh_bind_self]
    have hsplit : List.range (d' + 1) =
        List.range (d + 1) ++ (List.range (d' - d)).map (fun j => d + 1 + j) := by
      rw [← List.range_add]
      congr 1
      omega
    rw [hsplit, List.map_append, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      List.append_assoc]
    refine CohRel.append (CohRel.flatMap _ _ _ fun g hg => ?_) (CohRel.bound ?_ ?_)
    · -- the terms `j ≤ d`, common to both runs
      obtain ⟨hB1, hK1, hmin1, hcls1, hcnt1⟩ := hGs g (hmem g (List.mem_append_left _ hg))
      obtain ⟨hB2, -, -, hcls2, -⟩ := hGs' g (hmem' g (by
        rw [hsplit, List.map_append]
        exact List.mem_append_left _ (List.mem_append_left _ hg)))
      exact ih g (by omega) hB1 hcls1 hB2 hcls2 hK1 hmin1
    · -- the remainder `W_d`
      intro t ht
      rw [List.flatMap_singleton] at ht
      obtain ⟨hB1, hK1, hmin1, hcls1, hcnt1⟩ :=
        hGs _ (hmem _ (List.mem_append_right _ (List.mem_singleton_self _)))
      have := coh_out_bound (coh_taylor_out m _ (by omega) hB1 hK1 hmin1 hcls1 t ht)
      rw [coh_ord_tW hc hk] at this
      linarith
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · -- the terms `d < j ≤ d'`
        obtain ⟨g, hg, ht⟩ := List.mem_flatMap.1 ht
        have hg' : g ∈ (List.range (d' + 1)).map (cohTTerm T i c ch) ++ [cohTW T i c ch d'] := by
          rw [hsplit, List.map_append]
          exact List.mem_append_left _ (List.mem_append_right _ hg)
        obtain ⟨hB1, hK1, hmin1, hcls1, hcnt1⟩ := hGs' g (hmem' g hg')
        have := coh_out_bound (coh_taylor_out m _ (by omega) hB1 hK1 hmin1 hcls1 t ht)
        simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hg
        obtain ⟨j, -, rfl⟩ := hg
        rw [coh_ord_tterm hc hk] at this
        push_cast at this
        linarith
      · -- the remainder `W_{d'}`
        rw [List.flatMap_singleton] at ht
        obtain ⟨hB1, hK1, hmin1, hcls1, hcnt1⟩ :=
          hGs' _ (hmem' _ (List.mem_append_right _ (List.mem_singleton_self _)))
        have := coh_out_bound (coh_taylor_out m _ (by omega) hB1 hK1 hmin1 hcls1 t ht)
        rw [coh_ord_tW hc hk] at this
        have : (d : ℤ) ≤ d' := by exact_mod_cast hdd
        linarith

private theorem coh_rev_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n} :
    ∀ (m : ℕ) (T : Graph k n), nMin T.comps ≤ m →
      Step1Base d S X Γ T → (ClsQ X T ∨ ClsW d X Γ T) →
      Step1Base d' S' X Γ T → (ClsQ X T ∨ ClsW d' X Γ T) → Step1OK1 Γ T →
      CohRel (Γ.paperOrd + d + 1) (selStep1_rev d m X T) (selStep1_rev d' m X T) := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hcls hB' hcls' hK
    have hmin : ∀ c ∈ T.comps, c.minor = [] := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => !c.minor.isEmpty :=
        List.mem_filter.2 ⟨hc, by simpa [List.isEmpty_iff] using h⟩
      have := List.length_pos_of_mem this
      unfold nMin at hm
      omega
    simp only [selStep1_rev]
    exact coh_taylor_rel hdd _ T le_rfl hB hcls hB' hcls' hK hmin
  | succ m ih =>
    intro T hm hB hcls hB' hcls' hK
    rcases hf : T.comps.findIdx? (fun c => !c.minor.isEmpty) with _ | i
    · have hmin : ∀ c ∈ T.comps, c.minor = [] := by
        intro c hc
        have := List.findIdx?_eq_none_iff.1 hf c hc
        simpa [List.isEmpty_iff] using this
      simp only [selStep1_rev, hf]
      exact coh_taylor_rel hdd _ T le_rfl hB hcls hB' hcls' hK hmin
    obtain ⟨c, hc, hcm⟩ := coh_findIdx_some hf
    have hcT : c ∈ T.comps := List.mem_of_getElem? hc
    have hmX : c.minor = [X] := by
      rcases hB.minor c hcT with h | ⟨h, -⟩
      · rw [h] at hcm; simp at hcm
      · exact h
    obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_rev_step hB hK hcls hc hmX
    obtain ⟨Gs', hE', -, -, hGs'⟩ := selStep1_rev_step hB' hK hcls' hc hmX
    have hGG := coh_map_self_inj (hE.symm.trans hE')
    subst hGG
    simp only [selStep1_rev, hf]
    rw [hE, coh_bind_self, coh_bind_self]
    refine CohRel.flatMap _ _ _ fun g hg => ?_
    obtain ⟨⟨hB1, hcls1, hmin1, -⟩, hK1⟩ := hGs g hg
    obtain ⟨⟨hB2, hcls2, -, -⟩, -⟩ := hGs' g hg
    exact ih g (by omega) hB1 hcls1 hB2 hcls2 hK1

private theorem coh_absorb_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ T : Graph k n}
    (hB : Step1Base d S X Γ T) (hcls : ClsW d X Γ T ∨ AllPend X T)
    (hB' : Step1Base d' S' X Γ T) (hcls' : ClsW d' X Γ T ∨ AllPend X T) (hK : Step1OK1 Γ T)
    (hnp : nPend X T.comps = 0) :
    CohRel (Γ.paperOrd + d + 1) (selStep1_absorb d X T) (selStep1_absorb d' X T) := by
  unfold selStep1_absorb
  by_cases hA : AllPend X T
  · rw [ite_eq_left hA, ite_eq_left hA]
    obtain ⟨hB1, hQ, -⟩ := absorb_step hB hnp hA
    obtain ⟨hB2, -, -⟩ := absorb_step hB' hnp hA
    exact coh_rev_rel hdd _ _ le_rfl hB1 (Or.inl hQ) hB2 (Or.inl hQ) (hK.absorb X)
  · rw [ite_eq_right hA, ite_eq_right hA]
    exact coh_rev_rel hdd _ _ le_rfl hB (Or.inr (hcls.resolve_right hA)) hB'
      (Or.inr (hcls'.resolve_right hA)) hK

private theorem coh_schur_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n}
    (hΓ : Γ.Plain) :
    ∀ (m : ℕ) (T : Graph k n), nPend X T.comps ≤ m →
      Step1Base d S X Γ T → (ClsW d X Γ T ∨ AllPend X T) →
      Step1Base d' S' X Γ T → (ClsW d' X Γ T ∨ AllPend X T) → Step1OK1 Γ T → PendInv X Γ T →
      CohRel (Γ.paperOrd + d + 1) (selStep1_schur d m X T) (selStep1_schur d' m X T) := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hcls hB' hcls' hK _
    simp only [selStep1_schur]
    exact coh_absorb_rel hdd hB hcls hB' hcls' hK (by omega)
  | succ m ih =>
    intro T hm hB hcls hB' hcls' hK hP
    rcases hf : T.comps.findIdx? (pendB X) with _ | i
    · have hnp : nPend X T.comps = 0 := by
        unfold nPend
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc
        simp [List.findIdx?_eq_none_iff.1 hf c hc]
      simp only [selStep1_schur, hf]
      exact coh_absorb_rel hdd hB hcls hB' hcls' hK hnp
    obtain ⟨c, hc, hcp⟩ := coh_findIdx_some hf
    obtain ⟨Gs, hE, -, -, hGs⟩ := selStep1_schur_step hΓ hB hK hP hcls hc hcp
    obtain ⟨Gs', hE', -, -, hGs'⟩ := selStep1_schur_step hΓ hB' hK hP hcls' hc hcp
    have hGG := coh_map_self_inj (hE.symm.trans hE')
    subst hGG
    simp only [selStep1_schur, hf]
    rw [hE, coh_bind_self, coh_bind_self]
    refine CohRel.flatMap _ _ _ fun g hg => ?_
    obtain ⟨⟨hB1, hP1, hcls1, hp1⟩, hK1⟩ := hGs g hg
    obtain ⟨⟨hB2, -, hcls2, -⟩, -⟩ := hGs' g hg
    exact ih g (by omega) hB1 hcls1 hB2 hcls2 hK1 hP1

open Classical in
private theorem coh_split_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n}
    (hΓ : Γ.Plain) (hfree : Γ.UnlabelledFreeAtBlock X) :
    ∀ (us : List (Atom k n)) (T : Graph k n),
      Step1Base d S X Γ T → Step1Base d' S' X Γ T → Step1OK1 Γ T →
      step1_sizeΦ d X T.comps + us.length ≤ S → step1_sizeΦ d' X T.comps + us.length ≤ S' →
      step1_dg T.comps = step1_dg Γ.comps →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.step1_isInvB = false) →
      AllPend X T →
      (∀ c ∈ T.comps, pendB X c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], Step1HasX T.comps u X ∨ u ∈ us) →
      (∀ u ∈ us, ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧ u ∈ [c.x, c.y]) →
      CohRel (Γ.paperOrd + d + 1) (selStep1_split d X us T) (selStep1_split d' X us T)
  | [], T, hB, hB', hK, _, _, _, _, _, hA, hP, _ => by
    have hP' : PendInv X Γ T := by
      intro c hc hp
      obtain ⟨h1, h2⟩ := hP c hc hp
      refine ⟨h1, ?_, ?_⟩
      · rcases h2 c.x (by simp) with h | h
        · exact h
        · simp at h
      · rcases h2 c.y (by simp) with h | h
        · exact h
        · simp at h
    simp only [selStep1_split]
    exact coh_schur_rel hdd hΓ _ T le_rfl hB (Or.inr hA) hB' (Or.inr hA) hK hP'
  | u :: us, T, hB, hB', hK, hsz, hsz', hdg, hmin, hinv, hA, hP, hus => by
    obtain ⟨c₀, hc₀, hl₀, hr₀, hu₀⟩ := hus u (List.mem_cons_self ..)
    simp only [List.length_cons] at hsz hsz'
    obtain ⟨-, -, -, -, hB₂, hK₂, hdg₂⟩ :=
      selStep1_split_step hfree hB hK (by omega) hdg hc₀ hl₀ hr₀ hu₀
    obtain ⟨-, -, -, -, hB₂', -, -⟩ :=
      selStep1_split_step hfree hB' hK (by omega) hdg hc₀ hl₀ hr₀ hu₀
    simp only [selStep1_split]
    refine (CohRel.refl _ _).append (coh_split_rel hdd hΓ hfree us _ hB₂ hB₂' hK₂ ?_ ?_ hdg₂ ?_ ?_
      ?_ ?_ (fun v hv => hus v (List.mem_cons_of_mem _ hv)))
    · rw [coh_sizeΦ_append _ (Or.inr rfl)]
      omega
    · rw [coh_sizeΦ_append _ (Or.inr rfl)]
      omega
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hmin d h
      · rw [List.mem_singleton.1 h]; rfl
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hinv d h
      · rw [List.mem_singleton.1 h]; rfl
    · intro d hd hdl hdr
      rcases List.mem_append.1 hd with h | h
      · exact hA d h hdl hdr
      · rw [List.mem_singleton.1 h] at hdr; simp [mkC, Kind.isRandom] at hdr
    · intro d hd hdp
      rcases List.mem_append.1 hd with h | h
      · obtain ⟨h1, h2⟩ := hP d h hdp
        refine ⟨h1, fun v hv => ?_⟩
        rcases h2 v hv with h3 | h3
        · exact Or.inl (coh_hasX_mono (fun d hd => List.mem_append_left _ hd) h3)
        · rcases List.mem_cons.1 h3 with rfl | h4
          · exact Or.inl ⟨mkC .xdot v X, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
          · exact Or.inr h4
      · rw [List.mem_singleton.1 h] at hdp; simp [pendB, mkC, Kind.isRandom] at hdp

end CohRel

/-- **Coherence of the run in the Taylor degree** ([II, Lemma 4.11] with the expansion
[II, (4.21)] at two degrees): for a normal regular graph `Γ = Γ₀ Q_x(Γ̃₀)` with bound `C` (`x`
internal) and Taylor degrees `d ≤ d'`, the runs at `d` and at `d'` are, up to order, `A ++ B` and
`A ++ B'` with a common part `A`, and every term of `B` and of `B'` has scaling order at least
`p + d + 1`, with `p` the scaling order of `Γ`, both counted as in the paper. -/
theorem selStep1Coh_coherent {k C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} {d d' : ℕ}
    (hdd : d ≤ d') (hN : Γ.Normal C) (hQ : Γ.IsQFormAt (.inr x₀)) (hP : Γ.Plain) :
    ∃ A B B' : TExpansion k n₀, (selStep1 d (.inr x₀) Γ).Perm (A ++ B) ∧
      (selStep1 d' (.inr x₀) Γ).Perm (A ++ B') ∧
      ∀ t ∈ B ++ B', Γ.paperOrd + d + 1 ≤ t.g.paperOrd := by
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep1, selStep1, ite_eq_right hxa, ite_eq_right hxa]
    exact CohRel.refl _ _
  by_cases hfree : Γ.UnlabelledFreeAtBlock (.inr x₀)
  swap
  · rw [selStep1, selStep1, ite_eq_left hxa, ite_eq_right hfree, ite_eq_left hxa,
      ite_eq_right hfree]
    exact CohRel.refl _ _
  rw [selStep1, selStep1, ite_eq_left hxa, ite_eq_left hfree, ite_eq_left hxa, ite_eq_left hfree]
  obtain ⟨hB, hsz, hmin, hinv, hA, hPd, hus⟩ := coh_root d hN hQ hP hxa hfree
  obtain ⟨hB', hsz', -⟩ := coh_root d' hN hQ hP hxa hfree
  exact coh_split_rel hdd hP hfree _ Γ hB hB' (Step1OK1.refl Γ) hsz hsz' rfl hmin hinv hA hPd hus

section CohInstances

end CohInstances

end RBM8D.Graphs
