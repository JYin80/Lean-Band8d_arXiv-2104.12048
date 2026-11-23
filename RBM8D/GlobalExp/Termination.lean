module

public import RBM8D.GlobalExp.GlobalGood
public import RBM8D.GlobalExp.GlobalGoodRows
public import RBM8D.Graph.DotBlocks
public import Batteries.Tactic.OpenPrivate
public import RBM8D.Graph.Local.StrategyPart1
public import RBM8D.Graph.Local.SolidMono
public import RBM8D.Graph.QExp.Clauses
public import RBM8D.Graph.Local.DotNorm
public import RBM8D.Graph.Local.Weight
public import RBM8D.GlobalExp.SubstSPD
public import RBM8D.GlobalExp.GlueNormal
public import RBM8D.GlobalExp.SubstDC
public import RBM8D.TExp.Second
import all RBM8D.Graph.Local.StrategyPart1
import all RBM8D.Graph.Local.SolidMono
import all RBM8D.Graph.QExp.Clauses
import all RBM8D.Graph.Local.DotNorm
import all RBM8D.Graph.Local.Weight
import all RBM8D.GlobalExp.GlobalGoodRows
import all RBM8D.GlobalExp.SubstSPD
import all RBM8D.GlobalExp.GlueNormal
import all RBM8D.GlobalExp.SubstDC
import all RBM8D.TExp.Second

@[expose] public section

/-!
# [II, Lemma 6.8] in the block reading: the invariant of a run and the measure

The facts on single steps of [II, Strategy 6.6] used for [II, Lemma 6.8] in the block reading:

* `O_dot` keeps the clause on the external atoms and the charge pattern of the block normal form
  (`oDot_extClause`);
* the inputs of Step 1 have no dotted edge (`locInput_dotFree`);
* the elementary steps of the `Q`-expansions of [II, §4.4] keep at most one label
  (`qElemStep_labels`);
* the measure `runMu` of a run decreases along Step 1 (`locMu`) and along the removal of a
  redundant dotted edge (`dotNormStep_mu`);
* every step keeps the invariant of a run (`invRun_step`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

-- (the names formerly opened from RBM8D.Graph.Local.StrategyPart1 are public)
open private SolidMono.dotExcess_zero from RBM8D.Graph.Local.SolidMono

/-! ## The removal of a redundant dotted edge -/

section DotNorm

variable {k n : ℕ}

/-- A list with the entry `c` at index `i`, and the list without it. -/
private theorem Termination_split {α : Type*} {L : List α} {i : ℕ} {c : α}
    (hc : L[i]? = some c) : ∃ A B : List α, L = A ++ c :: B ∧ L.eraseIdx i = A ++ B := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  refine ⟨L.take i, L.drop (i + 1), ?_, List.eraseIdx_eq_take_drop_succ L i⟩
  conv_lhs => rw [← List.take_append_drop i L]
  rw [List.drop_eq_getElem_cons hi]

/-- Two disjoint filters of a list together have at most its length. -/
private theorem Termination_filter_add_le {α : Type*} (p q : α → Bool) :
    ∀ L : List α, (∀ d ∈ L, ¬ (p d = true ∧ q d = true)) →
      (L.filter p).length + (L.filter q).length ≤ L.length
  | [], _ => by simp
  | d :: L, h => by
    have ih := Termination_filter_add_le p q L (fun e he => h e (List.mem_cons_of_mem _ he))
    have hd := h d List.mem_cons_self
    by_cases hp : p d = true <;> by_cases hq : q d = true <;>
      simp_all <;> omega

/-- A filter does not see an entry that fails its test. -/
private theorem Termination_filter_skip {α : Type*} (p : α → Bool) (A B : List α) (c : α)
    (h : p c = false) : (A ++ c :: B).filter p = (A ++ B).filter p := by
  simp [List.filter_append, h]

/-- A standard neutral atom stays standard neutral when a dotted edge is removed. -/
private theorem Termination_std {A B : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hk : c.kind = .dot) (co co' : Coeff) (u : Atom k n)
    (h : (⟨A ++ c :: B, co⟩ : Graph k n).stdNeutralAt u = true) :
    (⟨A ++ B, co'⟩ : Graph k n).stdNeutralAt u = true := by
  have hends : (⟨A ++ B, co'⟩ : Graph k n).ends u = (⟨A ++ c :: B, co⟩ : Graph k n).ends u := by
    simp [Graph.ends, List.filterMap_append, hk]
  unfold Graph.stdNeutralAt at h ⊢
  rw [hends]
  by_cases hu : (c.x == u || c.y == u) = true
  · exfalso
    set p : Comp (Atom k n) → Bool := fun d => d.kind != .xdot && (d.x == u || d.y == u)
      with hp
    have hpc : p c = true := by simp [hp, hk, hu]
    have hcs : (A ++ c :: B).filter p = A.filter p ++ c :: B.filter p := by
      simp [List.filter_append, hpc]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
    rw [hcs] at h1 h2 h3
    set L := A.filter p ++ B.filter p with hL
    have e1 : L.length = 2 := by simp [hL] at h1 ⊢; omega
    have e2 : (L.filter fun d => d.kind.isSolid).length = 2 := by
      have := Termination_filter_skip (fun d : Comp (Atom k n) => d.kind.isSolid) (A.filter p)
        (B.filter p) c (by simp [hk, Kind.isSolid])
      rw [this] at h2; exact h2
    have e3 : (L.filter fun d => d.kind == .waved .s).length = 1 := by
      have := Termination_filter_skip (fun d : Comp (Atom k n) => d.kind == .waved .s)
        (A.filter p) (B.filter p) c (by simp [hk])
      rw [this] at h3; exact h3
    have := Termination_filter_add_le (fun d : Comp (Atom k n) => d.kind.isSolid)
      (fun d => d.kind == .waved .s) L (by
        intro d _ ⟨hs, hw⟩
        simp only [beq_iff_eq] at hw
        rw [hw] at hs
        cases hs)
    omega
  · have hcs : ((A ++ c :: B).filter fun d => d.kind != .xdot && (d.x == u || d.y == u)) =
        (A ++ B).filter fun d => d.kind != .xdot && (d.x == u || d.y == u) :=
      Termination_filter_skip _ A B c (by simp only [Bool.not_eq_true] at hu; simp [hu])
    rw [hcs] at h
    exact h

/-- **The removal of a redundant dotted edge lowers the measure of a run**: the statement
`dotNormStep_muStmt`. The order in the count of [II, (2.5)], the light weights, the solid edges,
the blocks and the components other than dotted edges are kept, the number of internal atoms of
degree `2` that are not standard neutral does not grow, and the dot excess drops by `1`. -/
theorem dotNormStep_mu : dotNormStep_muStmt := by
  intro N k n₀ C g g' hst _ _
  obtain ⟨i, c, hc, hk, hr, rfl⟩ := hst
  obtain ⟨-, he, hord, -, hb, -, -, -⟩ := drop_one g hc hk hr
  obtain ⟨A, B, hA, hAB⟩ := Termination_split hc
  set g₁ : Graph k n₀ := ⟨g.comps.eraseIdx i, g.coeff⟩ with hg₁
  have hex : g₁.dotExcess + 1 = g.dotExcess := he
  have hpo : g₁.paperOrd = g.paperOrd := by
    simp only [Graph.paperOrd]; linarith
  have hnn : 0 ≤ g₁.dotExcess := eL_nonneg _
  have hf : ∀ p : Comp (Atom k n₀) → Bool, p c = false →
      (g₁.comps.filter p).length = (g.comps.filter p).length := by
    intro p hp
    change ((g.comps.eraseIdx i).filter p).length = _
    rw [hAB, hA, Termination_filter_skip p A B c hp]
  have hlw : g₁.lwN = g.lwN := hf _ (by simp [hk, Kind.isLt])
  have hsol : g₁.solidN = g.solidN := hf _ (by simp [hk, Kind.isSolid])
  have hrw : g₁.rwN = g.rwN := hf _ (by simp [hk, Kind.isRg])
  have hext : g₁.eextN = g.eextN := hf _ (by simp [hk, Kind.isSolid])
  have hdeg : ∀ u, g₁.deg u = g.deg u := fun u => hf _ (by simp [hk, Kind.isSolid])
  have hdegX : g₁.degX = g.degX := by
    unfold Graph.degX; simp only [hdeg]
  have hstd : ∀ u, g.stdNeutralAt u = true → g₁.stdNeutralAt u = true := by
    intro u hu
    have hg : g = ⟨A ++ c :: B, g.coeff⟩ := by rw [← hA]
    have hg1 : g₁ = ⟨A ++ B, g.coeff⟩ := by rw [hg₁]; congr 1
    rw [hg] at hu
    rw [hg1]
    exact Termination_std hk g.coeff g.coeff u hu
  have hbad : g₁.badN ≤ g.badN := by
    unfold Graph.badN
    refine Finset.card_le_card fun j hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨by rw [← hdeg]; exact hj.1, ?_⟩
    by_contra hs
    simp only [Bool.not_eq_false] at hs
    rw [hstd _ hs] at hj
    exact Bool.noConfusion hj.2
  have hsep : g₁.SepInt ↔ g.SepInt :=
    ⟨fun h a b hab => h a b ((hb _ _).2 hab), fun h a b hab => h a b ((hb _ _).1 hab)⟩
  have hmfl : g₁.mfl = g.mfl := by
    by_cases h : g.SepInt
    · simp only [Graph.mfl, h, hsep.2 h, ↓reduceIte]
    · have h' : ¬ g₁.SepInt := fun h' => h (hsep.1 h')
      simp only [Graph.mfl, h, h', ↓reduceIte]
  have hphi : g₁.phi ≤ g.phi := by
    unfold Graph.phi; rw [hlw, hdegX, hrw]; omega
  unfold runMu
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨by rw [hpo], ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hlw, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hsol, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hmfl, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hext, ?_⟩
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hphi with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    omega

end DotNorm

/-! ## The inputs of Step 1 and the descent of Step 1 -/

section Step1

variable {n₀ : ℕ}

/-- The order in the count of [II, (2.5)] is at most the scaling order. -/
private theorem Termination_paperOrd_le {k n : ℕ} (Γ : Graph k n) : Γ.paperOrd ≤ Γ.ord := by
  have : 0 ≤ Γ.dotExcess := eL_nonneg Γ.comps
  unfold Graph.paperOrd
  omega

/-- A graph with the invariant of a run that is not a `Q`-graph without internal atom and has
scaling order `≤ D` has the invariant `Graph.InvB'` and only diffusive edges at `⊗`. -/
private theorem Termination_inv1 {D : ℕ} {Γ : Graph 3 n₀} (hI : Γ.InvRun D)
    (h2 : ¬ (n₀ = 0 ∧ Γ.IsQGraph)) (h3 : ¬ (D : ℤ) < Γ.ord) : Γ.InvB' ∧ Γ.TensorDiffusive := by
  rcases hI with h | h | h
  · exact h
  · exact absurd h h2
  · exact absurd (lt_of_lt_of_le h.1 (Termination_paperOrd_le Γ)) h3

/-- A graph without labels is not a `Q`-graph. -/
private theorem Termination_not_qGraph {k n : ℕ} {Γ : Graph k n} (hL : Γ.LabelFree) :
    ¬ Γ.IsQGraph := by
  rintro ⟨u, ⟨c, hc, hl⟩, -⟩
  rw [hL c hc] at hl
  cases hl

/-- In a graph with only diffusive edges at `⊗`, a component with an end at `⊗` is diffusive. -/
private theorem Termination_td_at {Γ : Graph 3 n₀} (hT : Γ.TensorDiffusive)
    {c : Comp (Atom 3 n₀)} (hc : c ∈ Γ.comps) (h : c.x = .inl 0 ∨ c.y = .inl 0) :
    c.kind.isDiffusive = true := by
  have := List.all_eq_true.1 hT c hc
  rcases h with h | h <;> simpa [h] using this

/-- A path of dotted edges from an external to an internal atom has a dotted edge between an
external and an internal atom. -/
private theorem Termination_walk_ext_int {k n : ℕ} {Γ : Graph k n} :
    ∀ {u v : Atom k n} (_ : Γ.dotGraph.Walk u v), u.isLeft = true → v.isRight = true →
      ∃ d ∈ Γ.comps, d.kind = .dot ∧ (d.x.isLeft = true ∧ d.y.isRight = true ∨
        d.y.isLeft = true ∧ d.x.isRight = true) := by
  intro u v w
  induction w with
  | nil => intro hu hv; rename_i u; cases u <;> simp at hu hv
  | @cons a b _ hadj _ ih =>
    intro ha hc
    by_cases hb : b.isRight = true
    · rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨-, ⟨d, hd, hk, h1, h2⟩ | ⟨d, hd, hk, h1, h2⟩⟩ := hadj
      · exact ⟨d, hd, hk, Or.inl ⟨h1 ▸ ha, h2 ▸ hb⟩⟩
      · exact ⟨d, hd, hk, Or.inr ⟨h2 ▸ ha, h1 ▸ hb⟩⟩
    · exact ih (by cases b <;> simp_all) hc

/-- **The inputs of Step 1 have no dotted edge** ([II, Strategy 6.6]): the statement
`locInput_dotFreeStmt`. A dotted edge at `⊗` is excluded by the diffusive edges at `⊗`, one from
`⊕` or `⊖` to an internal atom makes a `⊕/⊖`-recollision graph, one between internal atoms is
excluded by regularity, a loop by `Graph.Plain`, and one between `⊕` and `⊖` puts an internal atom
into their block (the clause on the external atoms), so that a dotted edge of that block joins an
external to an internal atom. -/
theorem locInput_dotFree : locInput_dotFreeStmt := by
  intro n D n₀ C Γ hI hD hL hN hP hS c hc hk
  obtain ⟨hB, hT⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have hR : ¬ Γ.IsRecollision {1, 2} := fun h => hS ⟨⟨C, hN⟩, Or.inl h⟩
  have key : ∀ d ∈ Γ.comps, d.kind = .dot → ¬ (d.x.isLeft = true ∧ d.y.isRight = true ∨
      d.y.isLeft = true ∧ d.x.isRight = true) := by
    intro d hd hdk h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 h1
      fin_cases a
      · have := Termination_td_at hT hd (Or.inl ha)
        rw [hdk] at this
        cases this
      · exact hR ⟨d, hd, hdk, Or.inl ⟨⟨1, by simp, ha⟩, h2⟩⟩
      · exact hR ⟨d, hd, hdk, Or.inl ⟨⟨2, by simp, ha⟩, h2⟩⟩
    · obtain ⟨a, ha⟩ := Sum.isLeft_iff.1 h1
      fin_cases a
      · have := Termination_td_at hT hd (Or.inr ha)
        rw [hdk] at this
        cases this
      · exact hR ⟨d, hd, hdk, Or.inr ⟨⟨1, by simp, ha⟩, h2⟩⟩
      · exact hR ⟨d, hd, hdk, Or.inr ⟨⟨2, by simp, ha⟩, h2⟩⟩
  have hleft : ∀ u : Atom 3 n₀, u.isRight = false → u.isLeft = true := by
    intro u hu; cases u <;> simp_all
  by_cases hx : c.x.isRight = true <;> by_cases hy : c.y.isRight = true
  · rcases hN.1.noIntDot c hc hk with h | h
    · cases hcx : c.x <;> simp_all
    · cases hcy : c.y <;> simp_all
  · exact key c hc hk (Or.inr ⟨hleft _ (by simpa using hy), hx⟩)
  · exact key c hc hk (Or.inl ⟨hleft _ (by simpa using hx), hy⟩)
  · have hne : c.x ≠ c.y := (hP c hc).2.2.2.1 hk
    have hsb : Γ.SameBlock c.x c.y :=
      ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩).reachable
    obtain ⟨b, ⟨w⟩⟩ := hB.2.2.1.1 c.x c.y hne hsb
    obtain ⟨d, hd, hdk, hdd⟩ := Termination_walk_ext_int w (hleft _ (by simpa using hx)) rfl
    exact key d hd hdk hdd

/-- In a graph without dotted edges, every block is a single atom. -/
private theorem Termination_sameBlock_of_dotFree {k n : ℕ} {Γ : Graph k n}
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) {u v : Atom k n} (h : Γ.SameBlock u v) : u = v := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ =>
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨d, hd, hk, -⟩ | ⟨d, hd, hk, -⟩⟩ := hadj <;> exact absurd hk (hD d hd)

/-- A graph without dotted edges with the charge pattern of the block normal form has internal
first atoms on its random components. -/
private theorem Termination_randomFirstInt {Γ : Graph 3 n₀} (hC : Γ.ColourInvB)
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) : Γ.RandomFirstInt := by
  intro c hc hr
  have h := (hC (Γ.flatComp c) (List.mem_map_of_mem hc)).1
  have hfc : Γ.flatComp c = { c with x := Γ.flatAtom c.x, y := Γ.flatAtom c.y } := by
    simp [Graph.flatComp, hD c hc]
  rw [hfc] at h
  have h1 := (h hr).1
  rcases hx : c.x with a | b
  · rw [hx] at h1
    have han : Γ.anchor (.inl a) = none := by
      unfold Graph.anchor
      rw [List.find?_eq_none]
      intro b _ hb
      have hb' : Γ.SameBlock (.inl a) (.inr b) := by simpa using hb
      exact absurd (Termination_sameBlock_of_dotFree hD hb') (by simp)
    simp [Graph.flatAtom, han] at h1
  · rfl

/-- The descent of `runMu` from the clauses `StepOut` of a step and the light weights and solid
edges at equal order. -/
private theorem Termination_mu_of {N : ℕ} {Γ : Graph 3 n₀} {t : Tracked 3 n₀}
    (hs : StepOut Γ t)
    (hlw : t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.lwN < Γ.lwN ∨ (t.g.lwN ≤ Γ.lwN ∧ t.g.solidN ≤ Γ.solidN))
    (hL : t.g.LabelFree) (hord : Γ.paperOrd ≤ N) : runMu N t.g < runMu N Γ := by
  obtain ⟨-, hobl, hlex, -⟩ := hs
  rw [← Graph.paperOrd_eq_obl, ← Graph.paperOrd_eq_obl] at hobl
  unfold runMu
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hobl with h | h
  · left
    omega
  · right
    refine ⟨by rw [h], ?_⟩
    have hl := hlex hL (by rw [← Graph.paperOrd_eq_obl, ← Graph.paperOrd_eq_obl]; exact h.symm)
    rw [Prod.Lex.toLex_lt_toLex]
    rcases hlw hL h.symm with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    rcases lt_or_eq_of_le h1 with h1 | h1
    · exact Or.inl h1
    refine Or.inr ⟨h1, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    rcases lt_or_eq_of_le h2 with h2 | h2
    · exact Or.inl h2
    refine Or.inr ⟨h2, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex]
    unfold LexLt at hl
    rcases hl with h3 | ⟨h3, h4 | ⟨h4, h5⟩⟩
    · exact Or.inl h3
    · rcases lt_or_eq_of_le h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨h3, by rw [Prod.Lex.toLex_lt_toLex]; exact Or.inl h4⟩
    · rcases lt_or_eq_of_le h3 with h3 | h3
      · exact Or.inl h3
      refine Or.inr ⟨h3, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      rcases lt_or_eq_of_le h4 with h4 | h4
      · exact Or.inl h4
      refine Or.inr ⟨h4, ?_⟩
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl h5

/-- **The descent of Step 1** ([II, Lemma 6.8], [I, Strategy 3.21]): the statement `locMuStmt`.
The input has no dotted edge (`locInput_dotFree`), so its order in the count of [II, (2.5)] is its
scaling order, at most `n`; outputs of higher order lower the first coordinate of `runMu n`, and
outputs of equal order lower the light weights, the solid edges or `(mfl, eextN, phi)`. -/
theorem locMu : locMuStmt := by
  intro N D n₀ C Γ o x hI hS hD hN hL hP hX hA t ht htL
  have hdf := locInput_dotFree N D n₀ C Γ hI hD hL hN hP hS
  obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have hK := Termination_randomFirstInt hB.2.1 hdf
  have hord : Γ.paperOrd ≤ N := by
    have h1 : ¬ ((N : ℤ) + 1 ≤ Γ.ord) := fun h => hS ⟨⟨C, hN⟩, Or.inr (Or.inl h)⟩
    have := Termination_paperOrd_le Γ
    omega
  have hx : (Sum.inr x : Atom 3 n₀).isRight = true := rfl
  have key : StepOut Γ t ∧ (t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.lwN < Γ.lwN ∨ (t.g.lwN ≤ Γ.lwN ∧ t.g.solidN ≤ Γ.solidN)) := by
    rcases hA with ⟨rfl, hw⟩ | ⟨rfl, hw, hdeg, hM⟩ | ⟨ho, hw, y, y', hin⟩ |
        ⟨rfl, hw, hM, y, y', hin⟩
    · refine ⟨oWeightT_step hN hP hL hK hX hx hw t ht, fun h1 h2 => ?_⟩
      rcases (oWeightT_lwSolid hN hP hL hK hX hx hw hdf t ht h1 h2).2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1.le, h.2.le⟩
    · have H : MEHyp C (.inr x) Γ := ⟨hN, hP, hL, hK, hx, hw, hM⟩
      exact ⟨oMultiET_step H hX hdeg t ht,
        fun h1 h2 => Or.inr (oMultiET_lwSolid H hX hdeg hdf t ht h1 h2).2⟩
    · rcases ho with rfl | rfl
      · exact ⟨oGGT_step hN hP hL hK hX hx hw hin t ht,
          fun h1 h2 => Or.inr (oGGT_lwSolid hN hP hL hK hX hx hw hin hdf t ht h1 h2).2⟩
      · exact ⟨oGGTT_step hN hP hL hK hX hx hw hin t ht,
          fun h1 h2 => Or.inr (oGGTT_lwSolid hN hP hL hK hX hx hw hin hdf t ht h1 h2).2⟩
    · have H : MEHyp C (.inr x) Γ := ⟨hN, hP, hL, hK, hx, hw, hM⟩
      exact ⟨oGGbarT_step H hX hin t ht,
        fun h1 h2 => Or.inr (oGGbarT_lwSolid H hX hin hdf t ht h1 h2).2⟩
  exact Termination_mu_of key.1 key.2 htL hord

end Step1

/-! ## At most one label along the elementary steps of the `Q`-expansions -/

section Labels

/-- Every label of the list is `ℓ` (no label at all when `ℓ = none`). -/
private def Termination_OneLab {V : Type*} (L : List (Comp V)) : Prop :=
  ∃ ℓ : Option (PQ × V), ∀ c ∈ L, c.label = none ∨ c.label = ℓ

/-- Every label of `L'` is a label of `L`. -/
private def Termination_LabSub {V : Type*} (L L' : List (Comp V)) : Prop :=
  ∀ c' ∈ L', c'.label = none ∨ ∃ c ∈ L, c'.label = c.label

/-- No component of the list other than a solid edge or a weight carries a label. -/
private def Termination_NRL {V : Type*} (L : List (Comp V)) : Prop :=
  ∀ c ∈ L, c.kind.isRandom = false → c.label = none

private theorem Termination_oneLab_iff {k n : ℕ} (Γ : Graph k n) :
    Γ.labels.length ≤ 1 ↔ Termination_OneLab Γ.comps := by
  have hmem : ∀ c ∈ Γ.comps, ∀ l, c.label = some l → l ∈ Γ.labels := fun c hc l hl =>
    List.mem_dedup.2 (List.mem_filterMap.2 ⟨c, hc, hl⟩)
  constructor
  · intro h
    rcases hL : Γ.labels with _ | ⟨ℓ, _ | ⟨ℓ', rest⟩⟩
    · refine ⟨none, fun c hc => Or.inl ?_⟩
      rcases hcl : c.label with _ | l
      · rfl
      · have := hmem c hc l hcl
        rw [hL] at this
        cases this
    · refine ⟨some ℓ, fun c hc => ?_⟩
      rcases hcl : c.label with _ | l
      · exact Or.inl rfl
      · have := hmem c hc l hcl
        rw [hL, List.mem_singleton] at this
        rw [this]
        exact Or.inr rfl
    · rw [hL] at h
      simp at h
  · rintro ⟨ℓ, h⟩
    rcases ℓ with _ | ℓ
    · have : Γ.labels = [] := by
        unfold Graph.labels
        rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
        intro c hc
        rcases h c hc with h | h <;> exact h
      rw [this]
      simp
    · exact labels_le_one Γ ℓ h

private theorem Termination_oneLab_img {V W : Type*} (f : V → W) {L : List (Comp V)}
    {L' : List (Comp W)} (h : Termination_OneLab L)
    (hs : ∀ c' ∈ L', c'.label = none ∨ ∃ c ∈ L, c'.label = c.label.map (Prod.map id f)) :
    Termination_OneLab L' := by
  obtain ⟨ℓ, hℓ⟩ := h
  refine ⟨ℓ.map (Prod.map id f), fun c' hc' => ?_⟩
  rcases hs c' hc' with h | ⟨c, hc, h⟩
  · exact Or.inl h
  · rcases hℓ c hc with h' | h'
    · left
      rw [h, h']
      rfl
    · right
      rw [h, h']

private theorem Termination_oneLab_sub {V : Type*} {L L' : List (Comp V)}
    (h : Termination_OneLab L) (hs : Termination_LabSub L L') : Termination_OneLab L' := by
  refine Termination_oneLab_img id h fun c' hc' => ?_
  rcases hs c' hc' with h | ⟨c, hc, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨c, hc, ?_⟩
    rw [h]
    cases c.label <;> rfl

private theorem Termination_map_id {V : Type*} (o : Option (PQ × V)) :
    o.map (Prod.map id id) = o := by
  cases o <;> rfl

/-- Every label of the output `t` is the image of a label of `L`. -/
private def Termination_LabImg {k n : ℕ} (L : List (Comp (Atom k n))) (t : Tracked k n) : Prop :=
  ∀ c' ∈ t.g.comps, c'.label = none ∨ ∃ c ∈ L, c'.label = c.label.map (Prod.map id t.f)

private theorem Termination_oneLab_of_img {k n : ℕ} {L : List (Comp (Atom k n))}
    {t : Tracked k n} (h : Termination_OneLab L) (hi : Termination_LabImg L t) :
    Termination_OneLab t.g.comps :=
  Termination_oneLab_img t.f h hi

private theorem Termination_labImg_self {k n : ℕ} {Γ : Graph k n} {t : Tracked k n}
    (ht : t ∈ [Tracked.self Γ]) : Termination_LabImg Γ.comps t := by
  rw [List.mem_singleton] at ht
  subst ht
  intro c hc
  exact Or.inr ⟨c, hc, (Termination_map_id _).symm⟩

/-- The labels of the outputs of `O_merge` are the images of those of the input. -/
private theorem Termination_oneLab_merge {k n : ℕ} {Δ : Graph k n} {t : Tracked k n}
    (h : Δ.mergeT = some t) (hΔ : Termination_OneLab Δ.comps) : Termination_OneLab t.g.comps := by
  have hs := psteps_mergeT_spec h
  refine Termination_oneLab_img t.f hΔ fun c' hc' => Or.inr ?_
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  exact ⟨c, hc, mergeComp_label hm⟩

/-- The labels of the outputs of `O_dot` are the images of those of the input. -/
private theorem Termination_oneLab_dot {k n : ℕ} {Γ : Graph k n} {t : Tracked k n}
    (ht : t ∈ oDotT Γ) (hΓ : Termination_OneLab Γ.comps) : Termination_OneLab t.g.comps := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact hΓ
  · refine Termination_oneLab_merge hm (Termination_oneLab_sub hΓ fun c' hc' => ?_)
    unfold Graph.dotChoice at hc'
    rcases List.mem_append.1 hc' with h | h
    · exact Or.inr ⟨c', (List.mem_filter.1 h).1, rfl⟩
    · obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 h
      split_ifs at hp
      · obtain rfl := Option.some.inj hp
        exact Or.inl rfl
      · obtain rfl := Option.some.inj hp
        exact Or.inl rfl

/-- The resolvent identities [II, (4.17), (4.20)] and the expansion [II, (4.21)] at a component:
the new factors carry the label of the expanded component. -/
private theorem Termination_labImg_new {k n : ℕ} {Γ : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : Γ.comps[i]? = some c) (L : List (Comp (Atom k n))) (co : Coeff)
    (hL : ∀ d ∈ L, d.label = c.label) :
    Termination_LabImg Γ.comps ⟨n, ⟨Γ.comps.eraseIdx i ++ L, co⟩, id⟩ := by
  intro c' hc'
  rcases List.mem_append.1 hc' with h | h
  · exact Or.inr ⟨c', List.mem_of_mem_eraseIdx h, (Termination_map_id _).symm⟩
  · exact Or.inr ⟨c, List.mem_of_getElem? hc, by rw [hL c' h]; exact (Termination_map_id _).symm⟩

private theorem Termination_labImg_schur {k n : ℕ} {x : Atom k n} {i : ℕ} {Γ : Graph k n}
    {t : Tracked k n} (ht : t ∈ oSchurT x i Γ ∨ t ∈ oSchurRevT x i Γ) :
    Termination_LabImg Γ.comps t := by
  rcases ht with ht | ht
  all_goals
    first | unfold oSchurT at ht | unfold oSchurRevT at ht
    split at ht
    · rename_i c hc
      split at ht
      · dsimp only at ht
        split_ifs at ht
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact Termination_labImg_new hc _ _ (by simp)
          · exact Termination_labImg_new hc _ _ (by simp)
        · exact Termination_labImg_self ht
      · exact Termination_labImg_self ht
    · exact Termination_labImg_self ht

private theorem Termination_labImg_schurW {k n : ℕ} {x : Atom k n} {i : ℕ} {Γ : Graph k n}
    {t : Tracked k n} (ht : t ∈ oSchurWT x i Γ ∨ t ∈ oSchurWRevT x i Γ) :
    Termination_LabImg Γ.comps t := by
  rcases ht with ht | ht
  all_goals
    first | unfold oSchurWT at ht | unfold oSchurWRevT at ht
    split at ht
    · rename_i c hc
      split at ht
      all_goals first
        | exact Termination_labImg_self ht
        | (dsimp only at ht
           split_ifs at ht
           · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
             rcases ht with rfl | rfl
             · exact Termination_labImg_new hc _ _ (by simp)
             · exact Termination_labImg_new hc _ _ (by simp)
           · exact Termination_labImg_self ht)
    · exact Termination_labImg_self ht

private theorem Termination_labImg_taylor {k n : ℕ} {D i : ℕ} {Γ : Graph k n} {t : Tracked k n}
    (ht : t ∈ oTaylorT D i Γ) : Termination_LabImg Γ.comps t := by
  unfold oTaylorT at ht
  split at ht
  · rename_i c hc
    split at ht
    · dsimp only at ht
      split_ifs at ht
      · rcases List.mem_append.1 ht with h | h
        · obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
          refine Termination_labImg_new hc _ _ fun d hd => ?_
          rw [(List.mem_replicate.1 hd).2]
        · rw [List.mem_singleton] at h
          subst h
          exact Termination_labImg_new hc _ _ (by simp)
      · exact Termination_labImg_self ht
    · exact Termination_labImg_self ht
  · exact Termination_labImg_self ht

/-- The lists of `splitRegular` carry the labels of the input list. -/
private theorem Termination_labSub_splitRegular {V : Type*} [DecidableEq V] (x : V) :
    ∀ (cs : List (Comp V)), ∀ p ∈ splitRegular x cs, Termination_LabSub cs p.1
  | [], p, hp => by
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    intro c hc
    cases hc
  | c :: cs, p, hp => by
    have ih := Termination_labSub_splitRegular x cs
    have hcons : ∀ q ∈ splitRegular x cs, ∀ d : Comp V, d.label = c.label →
        Termination_LabSub (c :: cs) (d :: q.1) := by
      intro q hq d hd c' hc'
      rcases List.mem_cons.1 hc' with rfl | h
      · exact Or.inr ⟨c, List.mem_cons_self, hd⟩
      · rcases ih q hq c' h with h' | ⟨e, he, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, h'⟩
    have hdrop : ∀ q ∈ splitRegular x cs, Termination_LabSub (c :: cs) q.1 := by
      intro q hq c' hc'
      rcases ih q hq c' hc' with h' | ⟨e, he, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, h'⟩
    simp only [splitRegular] at hp
    split at hp
    · split_ifs at hp
      · rcases List.mem_append.1 hp with h | h
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
          exact hdrop q hq
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
          exact hcons q hq _ rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hcons q hq _ rfl
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hcons q hq _ rfl

private theorem Termination_labImg_weight1 {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {t : Tracked k n} (ht : t ∈ oWeight1T x Γ) : Termination_LabImg Γ.comps t := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  intro c' hc'
  rcases Termination_labSub_splitRegular x Γ.comps p hp c' hc' with h | ⟨c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, by rw [h]; exact (Termination_map_id _).symm⟩

private theorem Termination_nrl_of_unl {V : Type*} {L : List (Comp V)} (h : Unl L) :
    Termination_NRL L :=
  fun c hc _ => h c hc

private theorem Termination_nrl_labelQs {V : Type*} (u : V) {L : List (Comp V)}
    (h : Termination_NRL L) : Termination_NRL (labelQs u L) := by
  intro c hc hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  unfold Comp.labelQ at hr ⊢
  split_ifs at hr ⊢ with hd'
  · simp [hd'] at hr
  · exact h d hd hr

/-- The outputs of `P_x` applied to a formal sum whose components other than solid edges and
weights carry no label have the single label `P` at the image of `x`. -/
private theorem Termination_oneLab_pLift {k n : ℕ} {u : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : ∀ s ∈ E, Termination_NRL s.g.comps) {t : Tracked k n}
    (ht : t ∈ pLiftT u Γ E) : Termination_OneLab t.g.comps := by
  obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
  refine ⟨some (.P, s.f u), fun c hc => ?_⟩
  rcases List.mem_append.1 hc with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    unfold rl
    split_ifs with hr
    · exact Or.inr rfl
    · exact Or.inl (hE s hs d hd (by simpa using hr))
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    left
    simp [Comp.map, pEnv_unl Γ d hd]

private theorem Termination_unl_lift {k n : ℕ} {L : List (Comp (Atom k n))} (hL : Unl L)
    {M : List (Comp (Atom k n))} (hM : ∀ c ∈ M, c ∈ L) : Unl (liftCs 1 M) :=
  Unl_liftCs 1 (Unl_sub hL hM)

private theorem Termination_nrl_conj {k n : ℕ} {E : TExpansion k n}
    (h : ∀ s ∈ E, Termination_NRL s.g.comps) : ∀ s ∈ E.conj, Termination_NRL s.g.comps := by
  intro s hs
  obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.1 hs
  intro c hc hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  refine h s₀ hs₀ d hd ?_
  rw [← Kind.conj_isRandom']
  exact hr

/-- The terms of `multiEOut` on a graph without labels: no component other than a solid edge or
a weight carries a label. -/
private theorem Termination_nrl_multiEOut {k n : ℕ} {x : Atom k n} {h : Graph k n}
    (hU : Unl h.comps) {E : TExpansion k n} (hE : multiEOut x h = some E) :
    ∀ s ∈ E, Termination_NRL s.g.comps := by
  obtain ⟨i₁, is₂, e₁, -, -, -, rfl⟩ := multiEOut_some _ _ hE
  have hmk : ∀ (κ : Kind) (u v : Atom k (n + 1)), Unl [mkC κ u v] := fun κ u v => by
    simp [Unl, mkC]
  have hBM : ∀ j, Unl (oBaseM x h i₁ e₁ j) := fun j =>
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => mem_eraseIdxs hc,
      (by simp [Unl, mkC, oSx, oGy])⟩
  have hBP : ∀ j, Unl (oBaseP x h i₁ e₁ j) := fun j =>
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => mem_eraseIdxs hc,
      (by simp [Unl, mkC, oSx, oGy])⟩
  have hE1 : Unl (oE1 x h i₁ e₁) :=
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => List.mem_of_mem_eraseIdx hc,
      (by simp [Unl, mkC, oSx, oGy])⟩
  have hE2 : Unl (oE2 x h i₁ e₁) :=
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => List.mem_of_mem_eraseIdx hc,
      (by simp [Unl, mkC, oSx, oGy])⟩
  have hL3 : Unl (oL3 x h) :=
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => hc, (by simp [Unl, mkC, oSx])⟩
  have hDs : ∀ d ∈ oDs x h i₁ e₁, Unl d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    refine Unl_append.2 ⟨Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => mem_pickIdxs hc,
      dTerms_unl (Termination_unl_lift hU fun _ hc => mem_eraseIdxs hc) d' hd'⟩,
      (by simp [Unl, mkC, oSx, oGy])⟩
  have hP : ∀ cs : List (Comp (Atom k (n + 1))), ∀ d, Termination_NRL (t1 cs d).g.comps ↔
      Termination_NRL cs := fun _ _ => Iff.rfl
  simp only [psteps_oOut, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton,
    hP]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals first
    | exact fun j _ => Termination_nrl_of_unl (hBM j)
    | exact fun j _ => Termination_nrl_of_unl (hBP j)
    | exact fun j _ => Termination_nrl_of_unl (Unl_append.2 ⟨hBM j, hmk _ _ _⟩)
    | exact fun j _ => Termination_nrl_of_unl (Unl_append.2 ⟨hBP j, hmk _ _ _⟩)
    | exact Termination_nrl_of_unl hL3
    | exact fun d hd => Termination_nrl_of_unl (hDs d hd)
    | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hU)
    | exact fun j _ => Termination_nrl_labelQs _
        (Termination_nrl_of_unl (Unl_append.2 ⟨hBM j, hmk _ _ _⟩))
    | exact fun j _ => Termination_nrl_labelQs _
        (Termination_nrl_of_unl (Unl_append.2 ⟨hBP j, hmk _ _ _⟩))
    | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hL3)
    | exact fun d hd => Termination_nrl_labelQs _ (Termination_nrl_of_unl (hDs d hd))
    | (intro s hs
       split_ifs at hs
       · simp at hs
       · rw [List.mem_singleton] at hs
         subst hs
         first
          | exact Termination_nrl_of_unl hE1
          | exact Termination_nrl_of_unl hE2
          | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hE1)
          | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hE2))

/-- The terms of `multiEIn` on a graph without labels: no component other than a solid edge or
a weight carries a label. -/
private theorem Termination_nrl_multiEIn {k n : ℕ} {x : Atom k n} {h : Graph k n}
    (hU : Unl h.comps) {E : TExpansion k n} (hE : multiEIn x h = some E) :
    ∀ s ∈ E, Termination_NRL s.g.comps := by
  obtain ⟨i₁, is₂, e₁, -, -, -, rfl⟩ := multiEIn_some _ _ hE
  have hmk : ∀ (κ : Kind) (u v : Atom k (n + 1)), Unl [mkC κ u v] := fun κ u v => by
    simp [Unl, mkC]
  have hBM : ∀ j, Unl (iBaseM x h i₁ e₁ j) := fun j =>
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => mem_eraseIdxs hc,
      (by simp [Unl, mkC, oSx, iGw])⟩
  have hE1 : Unl (iE1 x h i₁ e₁) :=
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => List.mem_of_mem_eraseIdx hc,
      (by simp [Unl, mkC, oSx, iGw])⟩
  have hL3 : Unl (oL3 x h) :=
    Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => hc, (by simp [Unl, mkC, oSx])⟩
  have hDs : ∀ d ∈ iDs x h i₁ e₁, Unl d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    refine Unl_append.2 ⟨Unl_append.2 ⟨Termination_unl_lift hU fun _ hc => mem_pickIdxs hc,
      dTerms_unl (Termination_unl_lift hU fun _ hc => mem_eraseIdxs hc) d' hd'⟩,
      (by simp [Unl, mkC, oSx, iGw])⟩
  have hP : ∀ cs : List (Comp (Atom k (n + 1))), ∀ d, Termination_NRL (t1 cs d).g.comps ↔
      Termination_NRL cs := fun _ _ => Iff.rfl
  simp only [psteps_iOut, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton,
    hP]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  all_goals first
    | exact fun j _ => Termination_nrl_of_unl (hBM j)
    | exact fun j _ => Termination_nrl_of_unl (Unl_append.2 ⟨hBM j, hmk _ _ _⟩)
    | exact Termination_nrl_of_unl hL3
    | exact fun d hd => Termination_nrl_of_unl (hDs d hd)
    | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hU)
    | exact fun j _ => Termination_nrl_labelQs _
        (Termination_nrl_of_unl (Unl_append.2 ⟨hBM j, hmk _ _ _⟩))
    | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hL3)
    | exact fun d hd => Termination_nrl_labelQs _ (Termination_nrl_of_unl (hDs d hd))
    | (intro s hs
       split_ifs at hs
       · simp at hs
       · rw [List.mem_singleton] at hs
         subst hs
         first
          | exact Termination_nrl_of_unl hE1
          | exact Termination_nrl_labelQs _ (Termination_nrl_of_unl hE1))


/-- The terms of `Ô^{(x)}_multi-e` on a graph without labels: no component other than a solid edge
or a weight carries a label. -/
private theorem Termination_nrl_multiEHat {k n : ℕ} {x : Atom k n} {h : Graph k n}
    (hU : Unl h.comps) {E : TExpansion k n} (hE : multiEHat x h = some E) :
    ∀ s ∈ E, Termination_NRL s.g.comps := by
  have hU' : Unl h.conj.comps := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact hU d hd
  unfold multiEHat at hE
  split_ifs at hE
  · exact Termination_nrl_multiEOut hU hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    exact Termination_nrl_conj (Termination_nrl_multiEOut hU' hE')
  · exact Termination_nrl_multiEIn hU hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    exact Termination_nrl_conj (Termination_nrl_multiEIn hU' hE')

/-- **Every elementary step of the `Q`-expansions keeps at most one label** ([II, §4.4]): the
statement `qElemStep_labelsStmt`. The resolvent identities, the expansion of [II, (4.21)],
`O^{(x),1}_weight`, the partitions by dotted and `×`-dotted edges, the removal of a dotted edge
and the moves of an end keep the labels or put the label of the expanded component on the new
factors; `O_dot` and `O_merge` map the labels to their images; `Q_u = 1 - P_u`, the absorption into
a label group and the removal of a label `P_u` give the labels `P_u`, `ℓ` or none; the identities
inside `P_x` give the single label `P` at the image of `x`. -/
theorem qElemStep_labels : qElemStep_labelsStmt := by
  intro g g' hs hg
  rw [Termination_oneLab_iff] at hg ⊢
  cases hs with
  | schur x i Γ t hx ht =>
    exact Termination_oneLab_of_img hg (Termination_labImg_schur (Or.inl ht))
  | schurRev x i Γ t hx ht =>
    exact Termination_oneLab_of_img hg (Termination_labImg_schur (Or.inr ht))
  | schurW x i Γ t hx ht =>
    exact Termination_oneLab_of_img hg (Termination_labImg_schurW (Or.inl ht))
  | schurWRev x i Γ t hx ht =>
    exact Termination_oneLab_of_img hg (Termination_labImg_schurW (Or.inr ht))
  | taylor D i Γ t ht => exact Termination_oneLab_of_img hg (Termination_labImg_taylor ht)
  | weight1 x Γ t ht => exact Termination_oneLab_of_img hg (Termination_labImg_weight1 ht)
  | dot Γ t ht => exact Termination_oneLab_dot ht hg
  | merge Γ t ht => exact Termination_oneLab_merge ht hg
  | split u v Γ t hv ht =>
    refine Termination_oneLab_of_img hg ?_
    unfold oSplitT at ht
    split_ifs at ht
    · exact Termination_labImg_self ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;>
      · intro c' hc'
        rcases List.mem_append.1 hc' with h | h
        · exact Or.inr ⟨c', h, (Termination_map_id _).symm⟩
        · exact Or.inl (by rw [List.mem_singleton.1 h]; rfl)
  | xdot i Γ t ht =>
    refine Termination_oneLab_of_img hg ?_
    unfold oXdotT at ht
    split at ht
    · split_ifs at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · intro c' hc'
          exact Or.inr ⟨c', List.mem_of_mem_eraseIdx hc', (Termination_map_id _).symm⟩
        · intro c' hc'
          rcases List.mem_append.1 hc' with h | h
          · exact Or.inr ⟨c', List.mem_of_mem_eraseIdx h, (Termination_map_id _).symm⟩
          · exact Or.inl (by rw [List.mem_singleton.1 h]; rfl)
      · exact Termination_labImg_self ht
    · exact Termination_labImg_self ht
  | dropDot i Γ c hc hk hb =>
    exact Termination_oneLab_sub hg fun c' hc' =>
      Or.inr ⟨c', List.mem_of_mem_eraseIdx hc', rfl⟩
  | rebase i Γ c u v hc hk hb =>
    refine Termination_oneLab_sub hg fun c' hc' => ?_
    rcases List.mem_or_eq_of_mem_set hc' with h | rfl
    · exact Or.inr ⟨c', h, rfl⟩
    · exact Or.inr ⟨c, List.mem_of_getElem? hc, rfl⟩
  | qToP u Γ t hQ ht =>
    simp only [oQPT, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨none, fun c hc => by
        obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
        exact Or.inl rfl⟩
    · refine ⟨some (.P, u), fun c hc => ?_⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      dsimp only [Tracked.self]
      split_ifs with h
      · exact Or.inr rfl
      · rcases hQ.2 d hd with h' | h'
        · exact Or.inl h'
        · exact absurd h' h
  | absorb ℓ Γ hℓ hl =>
    refine ⟨some ℓ, fun c hc => ?_⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    split_ifs
    · exact Or.inr rfl
    · exact hl d hd
  | dropP u Γ hP hm =>
    exact ⟨none, fun c hc => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
      exact Or.inl rfl⟩
  | pWeight1 x Γ t hP hp ht =>
    refine Termination_oneLab_pLift (fun s hs c hc _ => ?_) ht
    rcases Termination_labImg_weight1 hs c hc with h | ⟨d, hd, h⟩
    · exact h
    · rw [h, pCore_unl Γ d hd]
      rfl
  | pWeight2 x Γ t hP hp ht =>
    unfold oWeightP2T at ht
    split at ht
    · rename_i E hE
      exact Termination_oneLab_pLift (fun s hs c hc _ =>
        (oWeightP2Pos_ub (fun c hc => ⟨pCore_unl Γ c hc, pCore_basB hp c hc⟩) hE s hs c hc).1) ht
    · split at ht
      · rename_i E hE
        have hb : ∀ c ∈ Γ.pCore.conj.comps, c.label = none ∧ basB c = true := by
          rw [← pCore_conj]
          exact fun c hc => ⟨pCore_unl _ c hc, pCore_basB hp.conj c hc⟩
        exact Termination_oneLab_pLift (Termination_nrl_conj fun s hs c hc _ =>
          (oWeightP2Pos_ub hb hE s hs c hc).1) ht
      · exact Termination_oneLab_of_img hg (Termination_labImg_self ht)
  | pMultiE x Γ E t hP hp hE ht =>
    exact Termination_oneLab_pLift (Termination_nrl_multiEHat (pCore_unl Γ) hE) ht

end Labels

/-! ## `O_dot` and the clause on the external atoms -/

section ODot

open private Rep clauses_rep rep_dot from RBM8D.Graph.QExp.Clauses

/-- The component without its label, a ghost edge read as a non-diffusive auxiliary edge: the
clause on the external atoms, the charge pattern of the block normal form and `O_dot` do not
distinguish the two. -/
private def Termination_neut {V : Type*} (c : Comp V) : Comp V :=
  ⟨if c.kind = .ghost then .aux 0 0 false else c.kind, c.x, c.y, c.minor, none⟩

/-- The graph with every component replaced by `Termination_neut`. -/
private def Termination_neutG {k n : ℕ} (Δ : Graph k n) : Graph k n :=
  ⟨Δ.comps.map Termination_neut, Δ.coeff⟩

@[simp] private theorem Termination_neut_x {V : Type*} (c : Comp V) :
    (Termination_neut c).x = c.x := rfl

@[simp] private theorem Termination_neut_y {V : Type*} (c : Comp V) :
    (Termination_neut c).y = c.y := rfl

@[simp] private theorem Termination_neut_label {V : Type*} (c : Comp V) :
    (Termination_neut c).label = none := rfl

private theorem Termination_neut_kind_eq {V : Type*} (c : Comp V) {κ : Kind} (h1 : κ ≠ .ghost)
    (h2 : κ ≠ .aux 0 0 false) : (Termination_neut c).kind = κ ↔ c.kind = κ := by
  unfold Termination_neut
  split_ifs with h
  · exact ⟨fun e => absurd e.symm h2, fun e => absurd (e.symm.trans h) h1⟩
  · exact Iff.rfl

@[simp] private theorem Termination_neut_dot {V : Type*} (c : Comp V) :
    (Termination_neut c).kind = .dot ↔ c.kind = .dot :=
  Termination_neut_kind_eq c (by decide) (by decide)

@[simp] private theorem Termination_neut_xdot {V : Type*} (c : Comp V) :
    (Termination_neut c).kind = .xdot ↔ c.kind = .xdot :=
  Termination_neut_kind_eq c (by decide) (by decide)

@[simp] private theorem Termination_neut_G {V : Type*} (c : Comp V) (ch : Charge) :
    (Termination_neut c).kind = .G ch ↔ c.kind = .G ch :=
  Termination_neut_kind_eq c (by cases ch <;> decide) (by cases ch <;> decide)

@[simp] private theorem Termination_neut_s {V : Type*} (c : Comp V) :
    (Termination_neut c).kind = .waved .s ↔ c.kind = .waved .s :=
  Termination_neut_kind_eq c (by decide) (by decide)

@[simp] private theorem Termination_neut_diff {V : Type*} (c : Comp V) :
    (Termination_neut c).kind.isDiffusive = c.kind.isDiffusive := by
  unfold Termination_neut
  split_ifs with h <;> simp [h, Kind.isDiffusive]

@[simp] private theorem Termination_neut_random {V : Type*} (c : Comp V) :
    (Termination_neut c).kind.isRandom = c.kind.isRandom := by
  unfold Termination_neut
  split_ifs with h <;> simp [h, Kind.isRandom]

@[simp] private theorem Termination_neut_solid {V : Type*} (c : Comp V) :
    (Termination_neut c).kind.isSolid = c.kind.isSolid := by
  unfold Termination_neut
  split_ifs with h <;> simp [h, Kind.isSolid]

@[simp] private theorem Termination_neut_dotB {V : Type*} (c : Comp V) :
    ((Termination_neut c).kind == .dot) = (c.kind == .dot) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Termination_neut_dot]

@[simp] private theorem Termination_neut_xdotB {V : Type*} (c : Comp V) :
    ((Termination_neut c).kind == .xdot) = (c.kind == .xdot) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Termination_neut_xdot]

private theorem Termination_neut_mkC {V : Type*} {κ : Kind} (h : κ ≠ .ghost) (u v : V) :
    Termination_neut (mkC κ u v) = mkC κ u v := by
  simp [Termination_neut, mkC, h]

private theorem Termination_neutG_comps {k n : ℕ} (Δ : Graph k n) :
    (Termination_neutG Δ).comps = Δ.comps.map Termination_neut := rfl

private theorem Termination_dotGraph_neut {k n : ℕ} (Δ : Graph k n) :
    (Termination_neutG Δ).dotGraph = Δ.dotGraph := by
  ext u v
  simp [Graph.dotGraph, SimpleGraph.fromRel_adj, Termination_neutG]

private theorem Termination_sameBlock_neut {k n : ℕ} (Δ : Graph k n) (u v : Atom k n) :
    (Termination_neutG Δ).SameBlock u v ↔ Δ.SameBlock u v := by
  unfold Graph.SameBlock
  rw [Termination_dotGraph_neut]

private theorem Termination_unpinned_neut {k n : ℕ} (Δ : Graph k n) (u : Atom k n) :
    (Termination_neutG Δ).Unpinned u ↔ Δ.Unpinned u := by
  simp [Graph.Unpinned, Termination_sameBlock_neut]

private theorem Termination_anchor_neut {k n : ℕ} (Δ : Graph k n) (u : Atom k n) :
    (Termination_neutG Δ).anchor u = Δ.anchor u := by
  unfold Graph.anchor
  congr 1
  funext b
  exact decide_eq_decide.2 (Termination_sameBlock_neut Δ _ _)

private theorem Termination_flatAtom_neut {k n : ℕ} (Δ : Graph k n) (u : Atom k n) :
    (Termination_neutG Δ).flatAtom u = Δ.flatAtom u := by
  unfold Graph.flatAtom
  rw [Termination_anchor_neut]

private theorem Termination_flatComp_neut {k n : ℕ} (Δ : Graph k n) (c : Comp (Atom k n)) :
    (Termination_neutG Δ).flatComp (Termination_neut c) = Termination_neut (Δ.flatComp c) := by
  unfold Graph.flatComp
  by_cases h : c.kind = .dot
  · simp [h]
  · simp only [Termination_neut_dot, h, ↓reduceIte, Termination_flatAtom_neut]
    rfl

private theorem Termination_colourInvB_neut {n : ℕ} (Δ : Graph 3 n) :
    (Termination_neutG Δ).ColourInvB ↔ Δ.ColourInvB := by
  unfold Graph.ColourInvB Graph.ColourInv' Graph.blockNorm
  simp only [Termination_neutG_comps, List.forall_mem_map]
  refine forall₂_congr fun c _ => ?_
  rw [Termination_flatComp_neut]
  simp

private theorem Termination_extClause_neut {n : ℕ} (Δ : Graph 3 n) :
    (Termination_neutG Δ).ExtClause ↔ Δ.ExtClause := by
  have hsb := Termination_sameBlock_neut Δ
  have hun := Termination_unpinned_neut Δ
  have hdiff : ∀ u, (Termination_neutG Δ).DiffToPinned u ↔ Δ.DiffToPinned u := by
    intro u
    simp [Graph.DiffToPinned, Termination_neutG_comps, hun]
  have hhas : ∀ u, (Termination_neutG Δ).HasDiffToPinned u ↔ Δ.HasDiffToPinned u := by
    intro u
    simp [Graph.HasDiffToPinned, Termination_neutG_comps, hun]
  have hdeg : ∀ u, (Termination_neutG Δ).nonDotDeg u = Δ.nonDotDeg u := by
    intro u
    simp only [Graph.nonDotDeg, Termination_neutG_comps, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro c _
    by_cases h1 : c.kind = .dot <;> by_cases h2 : c.kind = .xdot <;>
      by_cases hx : c.x = u <;> by_cases hy : c.y = u <;> simp [h1, h2, hx, hy]
  unfold Graph.ExtClause
  simp only [hsb, hun, hdiff, hhas, hdeg]
  simp [Termination_neutG_comps]

/-- The atom map of `O_merge`, with the representative map of the blocks as a parameter. -/
private def Termination_Mf {k n : ℕ} (rep : Atom k n → Atom k n) :
    Atom k n → Atom k ((List.finRange n).map fun i => rep (Sum.inr i)).dedup.length
  | .inl a => .inl a
  | .inr i => .inr ⟨((List.finRange n).map fun i => rep (Sum.inr i)).dedup.idxOf (rep (.inr i)),
      List.idxOf_lt_length_of_mem (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩

/-- `O_merge`, with the representative map of the blocks as a parameter. -/
private def Termination_M {k n : ℕ} (rep : Atom k n → Atom k n) (cs : List (Comp (Atom k n)))
    (co : Coeff) : Option (Tracked k n) :=
  if cs.any (fun c => c.kind == .xdot && rep c.x == rep c.y) then none else
  some ⟨_, ⟨cs.filterMap (psteps_mergeComp rep (Termination_Mf rep)), co⟩, Termination_Mf rep⟩

private theorem Termination_mergeT_eq {k n : ℕ} (Γ : Graph k n) :
    Γ.mergeT = Termination_M Γ.psteps_mrep Γ.comps Γ.coeff := by
  rw [mergeT_eq]
  rfl

/-- The tracked graph with every component replaced by `Termination_neut`. -/
private def Termination_neutT {k n : ℕ} (t : Tracked k n) : Tracked k n :=
  ⟨t.nOut, Termination_neutG t.g, t.f⟩

private theorem Termination_dotBlocks_neut {V : Type*} [DecidableEq V] (as : List V)
    (cs : List (Comp V)) : dotBlocks as (cs.map Termination_neut) = dotBlocks as cs := by
  unfold dotBlocks
  rw [List.foldl_map]
  congr 1
  funext P c
  simp only [Termination_neut_dot, Termination_neut_x, Termination_neut_y]

private theorem Termination_mergeComp_neut {k n m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (c : Comp (Atom k n)) :
    psteps_mergeComp rep f (Termination_neut c) =
      (psteps_mergeComp rep f c).map Termination_neut := by
  unfold psteps_mergeComp
  simp only [Termination_neut_dotB, Termination_neut_x, Termination_neut_y,
    Termination_neut_solid]
  split_ifs with h1 h2
  · rfl
  · have hs : c.kind.isSolid = true := by simp only [Bool.and_eq_true] at h2; exact h2.1
    obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hs
    simp [Termination_neut, Comp.map, hch, Kind.toWeight]
  · simp [Termination_neut, Comp.map]

private theorem Termination_M_neut {k n : ℕ} (rep : Atom k n → Atom k n)
    (cs : List (Comp (Atom k n))) (co : Coeff) :
    Termination_M rep (cs.map Termination_neut) co =
      (Termination_M rep cs co).map Termination_neutT := by
  unfold Termination_M
  have hany : (cs.map Termination_neut).any (fun c => c.kind == .xdot && rep c.x == rep c.y) =
      cs.any (fun c => c.kind == .xdot && rep c.x == rep c.y) := by
    rw [List.any_map]
    congr 1
    funext c
    simp
  rw [hany]
  split_ifs
  · rfl
  · simp only [Option.map_some, Termination_neutT, Termination_neutG, List.filterMap_map,
      List.map_filterMap]
    congr 4
    funext c
    exact Termination_mergeComp_neut rep _ c

private theorem Termination_mergeT_neut {k n : ℕ} (Δ : Graph k n) :
    (Termination_neutG Δ).mergeT = Δ.mergeT.map Termination_neutT := by
  have hrep : (Termination_neutG Δ).psteps_mrep = Δ.psteps_mrep := by
    unfold Graph.psteps_mrep
    rw [Termination_neutG_comps, Termination_dotBlocks_neut]
  rw [Termination_mergeT_eq, Termination_mergeT_eq, hrep, Termination_neutG_comps,
    Termination_M_neut]
  rfl

private theorem Termination_splitPairs_neut {k n : ℕ} (Γ : Graph k n) :
    (Termination_neutG Γ).splitPairs = Γ.splitPairs := by
  unfold Graph.splitPairs
  simp [Termination_neutG_comps, List.filterMap_map, List.any_map, Function.comp_def]

private theorem Termination_dotChoice_neut {k n : ℕ} (Γ : Graph k n)
    (SP A : List (Atom k n × Atom k n × Bool)) :
    (Termination_neutG Γ).dotChoice SP A = Termination_neutG (Γ.dotChoice SP A) := by
  unfold Graph.dotChoice Termination_neutG
  simp only [List.map_append, Graph.mk.injEq, and_true]
  congr 1
  · rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro c _
    simp
  · symm
    refine (List.map_congr_left fun d hd => ?_).trans (List.map_id _)
    obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hd
    split_ifs at hp
    · obtain rfl := Option.some.inj hp
      exact Termination_neut_mkC (by decide) _ _
    · obtain rfl := Option.some.inj hp
      exact Termination_neut_mkC (by decide) _ _

/-- **`O_dot` keeps the clause on the external atoms and the charge pattern of the block normal
form**: the statement `oDot_extClauseStmt`. With the labels removed and the ghost edges read as
non-diffusive auxiliary edges, the graph has the four clauses of [II, Lemma 5.13] in the block
reading other than `spdPM'`, and its `O_dot` forms are those of the graph with the same
reading. -/
theorem oDot_extClause : oDot_extClauseStmt := by
  intro n Γ hE hC _ t ht
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht with h1 h2
  · rw [List.mem_singleton.1 ht]
    exact ⟨hE, hC⟩
  · rw [List.mem_singleton.1 ht]
    exact ⟨hE, hC⟩
  · obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht
    have hm' : ((Termination_neutG Γ).dotChoice (Termination_neutG Γ).splitPairs A).mergeT =
        some (Termination_neutT t) := by
      rw [Termination_splitPairs_neut, Termination_dotChoice_neut, Termination_mergeT_neut, hm]
      rfl
    have hlab : (Termination_neutG Γ).labels = [] := by
      unfold Graph.labels
      rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
      intro c hc
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
      rfl
    have ht' : Termination_neutT t ∈ oDotT (Termination_neutG Γ) := by
      unfold oDotT
      dsimp only
      rw [ite_eq_right, ite_eq_right]
      · exact List.mem_filterMap.2 ⟨A, by rwa [Termination_splitPairs_neut], hm'⟩
      · rw [Termination_splitPairs_neut, Termination_neutG_comps, List.any_map]
        simpa [Function.comp_def] using h2
      · rw [hlab, Termination_neutG_comps, List.any_map]
        simp [Function.comp_def]
    have hR : Rep (Termination_neutG Γ) := (clauses_rep _).1
      ⟨(Termination_colourInvB_neut Γ).2 hC, (Termination_extClause_neut Γ).2 hE,
        fun c hc => by
          obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
          unfold Termination_neut
          split_ifs with h
          · simp
          · exact h,
        fun c hc => by
          obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
          rfl⟩
    obtain ⟨h3, h4, -, -⟩ := (clauses_rep _).2 (rep_dot hR ht')
    exact ⟨(Termination_extClause_neut t.g).1 h4, (Termination_colourInvB_neut t.g).1 h3⟩

end ODot

/-! ## Graphs with the same components, and the clauses on the external atoms -/

section Members

variable {k n : ℕ}

private theorem Termination_dotGraph_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) : g'.dotGraph = g.dotGraph := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, h]

private theorem Termination_molGraph_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) : g'.molGraph = g.molGraph := by
  ext u v
  simp only [Graph.molGraph, SimpleGraph.fromRel_adj, h]

private theorem Termination_edgeGraph_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) : g'.edgeGraph = g.edgeGraph := by
  ext u v
  simp only [Graph.edgeGraph, SimpleGraph.fromRel_adj, h]

private theorem Termination_wavedThetaGraph_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) : g'.wavedThetaGraph = g.wavedThetaGraph := by
  ext u v
  simp only [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj, h]

private theorem Termination_sameBlock_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) (u v : Atom k n) :
    g'.SameBlock u v ↔ g.SameBlock u v := by
  unfold Graph.SameBlock
  rw [Termination_dotGraph_mem h]

private theorem Termination_sameMol_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) (u v : Atom k n) :
    g'.SameMol u v ↔ g.SameMol u v := by
  unfold Graph.SameMol
  rw [Termination_molGraph_mem h]

private theorem Termination_anchor_congr {g g' : Graph k n}
    (hb : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) (u : Atom k n) :
    g'.anchor u = g.anchor u := by
  unfold Graph.anchor
  congr 1
  funext b
  exact decide_eq_decide.2 (hb _ _)

private theorem Termination_flatComp_congr {g g' : Graph k n}
    (hb : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) (c : Comp (Atom k n)) :
    g'.flatComp c = g.flatComp c := by
  unfold Graph.flatComp Graph.flatAtom
  simp only [Termination_anchor_congr hb]

private theorem Termination_molRep_mem {g g' : Graph k n}
    (h : ∀ d, d ∈ g'.comps ↔ d ∈ g.comps) (u : Atom k n) : g'.molRep u = g.molRep u := by
  unfold Graph.molRep
  rcases u with a | a
  · rfl
  · change Sum.inr _ = Sum.inr _
    congr 3
    funext b
    exact decide_eq_decide.2 (Termination_sameMol_mem h _ _)

/-- The charge pattern of the block normal form passes to a graph with the same blocks whose
components are components of the first graph. -/
private theorem Termination_colourInvB_of {n₀ : ℕ} {g g' : Graph 3 n₀}
    (hb : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) (hs : ∀ c ∈ g'.comps, c ∈ g.comps)
    (h : g.ColourInvB) : g'.ColourInvB := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  rw [Termination_flatComp_congr hb]
  exact h _ (List.mem_map_of_mem (hs d hd))

/-- The clause on the external atoms passes to a graph with the same blocks, the same
components other than dotted edges and the same number of components other than dotted and
`×`-dotted edges at each atom. -/
private theorem Termination_extClause_of {n₀ : ℕ} {g g' : Graph 3 n₀}
    (hb : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) (hs : ∀ c ∈ g'.comps, c ∈ g.comps)
    (hnd : ∀ c ∈ g.comps, c.kind ≠ .dot → c ∈ g'.comps)
    (hdeg : ∀ u, g'.nonDotDeg u = g.nonDotDeg u) (h : g.ExtClause) : g'.ExtClause := by
  have hun : ∀ u, g'.Unpinned u ↔ g.Unpinned u := fun u => by
    simp only [Graph.Unpinned, hb]
  have hdiff : ∀ c : Comp (Atom 3 n₀), c.kind.isDiffusive = true → c.kind ≠ .dot :=
      fun c hc hk => by
    rw [hk] at hc
    cases hc
  have hDiff : ∀ u, g.DiffToPinned u → g'.DiffToPinned u := by
    intro u hu c hc hd
    simp only [hun]
    exact hu c (hs c hc) hd
  have hHas : ∀ u, g.HasDiffToPinned u → g'.HasDiffToPinned u := by
    rintro u ⟨c, hc, hd, h'⟩
    exact ⟨c, hnd c hc (hdiff c hd), hd, by simpa only [hun] using h'⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun u v huv hsb => ?_, fun c hc hk => ?_, fun hu => ?_, fun hu => ?_, fun hu => ?_⟩
  · obtain ⟨b, hb'⟩ := h1 u v huv ((hb u v).1 hsb)
    exact ⟨b, (hb _ _).2 hb'⟩
  · simp only [hun]
    exact h2 c (hs c hc) hk
  · obtain ⟨ha, hd⟩ := h3 ((hun _).1 hu)
    exact ⟨hHas _ ha, hDiff _ hd⟩
  · obtain ⟨ha, hd⟩ := h4 ((hun _).1 hu)
    exact ⟨fun c hc => ha c (hs c hc), by rw [hdeg]; exact hd⟩
  · obtain ⟨ha, hd, hc⟩ := h5 ((hun _).1 hu)
    refine ⟨?_, hDiff _ hd, by rw [hdeg]; exact hc⟩
    rcases ha with ⟨c, hc', hk, h'⟩ | ha
    · exact Or.inl ⟨c, hnd c hc' (by rw [hk]; decide), hk, h'⟩
    · exact Or.inr (hHas _ ha)

/-- Only diffusive edges at `⊗` passes to a graph whose components are components of the first
graph. -/
private theorem Termination_td_of {n₀ : ℕ} {g g' : Graph 3 n₀} (hs : ∀ c ∈ g'.comps, c ∈ g.comps)
    (h : g.TensorDiffusive) : g'.TensorDiffusive :=
  List.all_eq_true.2 fun c hc => List.all_eq_true.1 h c (hs c hc)

/-- A graph with one more copy of a `×`-dotted edge that it has: the same components, one more
component, the same scaling order and dot excess. -/
private theorem Termination_dup_facts {g g' : Graph k n} {d : Comp (Atom k n)}
    (hp : g'.comps.Perm (g.comps ++ [d])) (hd : d ∈ g.comps) (hk : d.kind = .xdot) :
    (∀ e, e ∈ g'.comps ↔ e ∈ g.comps) ∧ g'.comps.length = g.comps.length + 1 ∧
      g'.ord = g.ord ∧ g'.dotExcess = g.dotExcess ∧
      ∀ u, g'.nonDotDeg u = g.nonDotDeg u := by
  have hmem : ∀ e, e ∈ g'.comps ↔ e ∈ g.comps := by
    intro e
    rw [hp.mem_iff, List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact hd
    · exact Or.inl
  refine ⟨hmem, by rw [hp.length_eq]; simp, ?_, ?_, ?_⟩
  · unfold Graph.ord
    rw [(hp.map _).sum_eq]
    simp [hk, Kind.ord]
  · unfold Graph.dotExcess Graph.nDots
    rw [Termination_dotGraph_mem hmem, (hp.filter _).length_eq]
    simp [hk]
  · intro u
    unfold Graph.nonDotDeg
    rw [(hp.filter _).length_eq]
    simp [hk]

/-- A graph with one more copy of a `×`-dotted edge of a normal regular graph is normal
regular. -/
private theorem Termination_dup_normal {C : ℕ} {g g' : Graph k n}
    (hmem : ∀ e, e ∈ g'.comps ↔ e ∈ g.comps) (hlen : g'.comps.length = g.comps.length + 1)
    (hN : g.Normal C) : g'.Normal (C + 1) := by
  obtain ⟨⟨hsz, hcon, hint, hnoint⟩, hsol, hxs⟩ := hN
  refine ⟨⟨by omega, ?_, ?_, fun c hc => hnoint c ((hmem c).1 hc)⟩,
    fun c hc => hsol c ((hmem c).1 hc), ?_⟩
  · rw [Termination_edgeGraph_mem hmem]
    exact hcon
  · rw [Termination_wavedThetaGraph_mem hmem]
    exact hint
  · intro u v huv
    simp only [hmem]
    exact hxs u v huv

/-- The molecular graph `Graph.toMG'` of a graph with one more copy of a `×`-dotted edge is that
of the graph with one more absent edge. -/
private theorem Termination_toMG'_app {Γ : Graph k n} {d : Comp (Atom k n)} (hd : d ∈ Γ.comps)
    (hk : d.kind = .xdot) :
    Γ.toMG'.Transported (⟨Γ.comps ++ [d], Γ.coeff⟩ : Graph k n).toMG' := by
  set Γ' : Graph k n := ⟨Γ.comps ++ [d], Γ.coeff⟩ with hΓ'
  have hmem : ∀ e, e ∈ Γ'.comps ↔ e ∈ Γ.comps :=
    (Termination_dup_facts (g := Γ) (g' := Γ') (List.Perm.refl _) hd hk).1
  have hrep := Termination_molRep_mem hmem
  have hsb := Termination_sameBlock_mem hmem
  have hfc := Termination_flatComp_congr hsb
  have han := Termination_anchor_congr hsb
  have hlt : ∀ j : Fin Γ.comps.length, (j : ℕ) < Γ'.comps.length := fun j => by
    simp only [hΓ', List.length_append, List.length_singleton]
    omega
  have hget : ∀ j : Fin Γ.comps.length, Γ'.comps[(j : ℕ)]'(hlt j) = Γ.comps[j] := fun j =>
    List.getElem_append_left _
  let ι : Fin Γ.comps.length → Fin Γ'.comps.length := fun j => ⟨j, hlt j⟩
  have hcls : ∀ j, Γ'.toMG'.cls (.inl (ι j)) = Γ.toMG'.cls (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hget, hfc, hrep]
  have hends : ∀ j, Γ'.toMG'.ends (.inl (ι j)) = Γ.toMG'.ends (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hget, hfc, hrep]
  have hclsr : ∀ a, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) := by
    intro a
    simp only [Graph.toMG', han]
  have hendsr : ∀ a, Γ'.toMG'.ends (.inr a) = Γ.toMG'.ends (.inr a) := by
    intro a
    simp only [Graph.toMG', han, hrep]
  refine ⟨id, Sum.map ι id, ?_, Set.injOn_id _, ?_, ?_,
    fun e _ => MolInsert_toMG'_ends_vtx k n Γ e, ?_, ?_, ?_⟩
  · rintro (a | a) (b | b) - - h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      exact congrArg Sum.inl (Fin.ext (by simpa [ι] using congrArg Fin.val h))
    · simp at h
    · simp at h
    · simpa using h
  · simp only [Graph.toMG', Finset.image_id, hrep]
  · simp only [Graph.toMG', Finset.image_id]
  · rintro (j | a) _
    · exact hcls j
    · exact hclsr a
  · rintro (j | a) _
    · left
      rw [Sum.map_inl, hends j]
      rfl
    · left
      simp only [Sum.map_inr, id, hendsr a]
  · rintro (j | a) hj
    · by_cases hjl : (j : ℕ) < Γ.comps.length
      · by_contra hne
        refine hj (.inl ⟨j, hjl⟩) ?_ rfl
        rw [← hcls]
        exact hne
      · have hj' : (j : ℕ) = Γ.comps.length := by
          have := j.2
          simp [hΓ'] at this
          omega
        have hdj : Γ'.comps[j] = d := by
          simp only [Fin.getElem_fin, hΓ', hj']
          exact List.getElem_concat_length rfl _
        simp only [Graph.toMG', hdj]
        split_ifs
        · rfl
        · simp [Graph.flatComp, hk, Kind.mclass]
    · by_contra hne
      refine hj (.inr a) ?_ rfl
      rw [← hclsr]
      exact hne

/-- The molecular graph `Graph.toMG'` of a graph with the same components and another coefficient
is that of the graph. -/
theorem Termination_toMG'_coeff (Γ : Graph k n) (co : Coeff) :
    Γ.toMG'.Transported (⟨Γ.comps, co⟩ : Graph k n).toMG' := by
  set Γ' : Graph k n := ⟨Γ.comps, co⟩ with hΓ'
  have hmem : ∀ e, e ∈ Γ'.comps ↔ e ∈ Γ.comps := fun e => Iff.rfl
  have hrep := Termination_molRep_mem hmem
  have hsb := Termination_sameBlock_mem hmem
  have hfc := Termination_flatComp_congr hsb
  have han := Termination_anchor_congr hsb
  let ι : Fin Γ.comps.length → Fin Γ'.comps.length := fun j => ⟨j, j.2⟩
  have hcls : ∀ j, Γ'.toMG'.cls (.inl (ι j)) = Γ.toMG'.cls (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hfc, hrep]
    rfl
  have hends : ∀ j, Γ'.toMG'.ends (.inl (ι j)) = Γ.toMG'.ends (.inl j) := by
    intro j
    simp only [Graph.toMG', Fin.getElem_fin, ι, hfc, hrep]
    rfl
  have hclsr : ∀ a, Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) := by
    intro a
    simp only [Graph.toMG', han]
  have hendsr : ∀ a, Γ'.toMG'.ends (.inr a) = Γ.toMG'.ends (.inr a) := by
    intro a
    simp only [Graph.toMG', han, hrep]
  refine ⟨id, Sum.map ι id, ?_, Set.injOn_id _, ?_, ?_,
    fun e _ => MolInsert_toMG'_ends_vtx k n Γ e, ?_, ?_, ?_⟩
  · rintro (a | a) (b | b) - - h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      exact congrArg Sum.inl (Fin.ext (by simpa [ι] using congrArg Fin.val h))
    · simp at h
    · simp at h
    · simpa using h
  · simp only [Graph.toMG', Finset.image_id, hrep]
  · simp only [Graph.toMG', Finset.image_id]
  · rintro (j | a) _
    · exact hcls j
    · exact hclsr a
  · rintro (j | a) _
    · left
      rw [Sum.map_inl, hends j]
      rfl
    · left
      simp only [Sum.map_inr, id, hendsr a]
  · rintro (j | a) hj
    · by_contra hne
      refine hj (.inl ⟨j, j.2⟩) ?_ rfl
      rw [← hcls]
      exact hne
    · by_contra hne
      refine hj (.inr a) ?_ rfl
      rw [← hclsr]
      exact hne

/-- A test on the components of a graph with one more copy of a component that it has. -/
private theorem Termination_any_app {L : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hc : c ∈ L) (q : Comp (Atom k n) → Bool) : (L ++ [c]).any q = L.any q := by
  rw [List.any_append]
  by_cases h : q c = true
  · have : L.any q = true := List.any_eq_true.2 ⟨c, hc, h⟩
    simp [this]
  · simp [h]

/-- The number of labels of a graph with one more copy of a component that it has. -/
private theorem Termination_labels_app {L : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hc : c ∈ L) (co co' : Coeff) :
    (⟨L ++ [c], co⟩ : Graph k n).labels.length = (⟨L, co'⟩ : Graph k n).labels.length := by
  unfold Graph.labels
  refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup (List.nodup_dedup _)
    (List.nodup_dedup _)).2 fun a => ?_)
  simp only [List.mem_dedup, List.mem_filterMap, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨e, he | rfl, hl⟩
    · exact ⟨e, he, hl⟩
    · exact ⟨e, hc, hl⟩
  · rintro ⟨e, he, hl⟩
    exact ⟨e, Or.inl he, hl⟩

/-- In the removal of repeated unordered pairs, every pair met is kept up to order. -/
private theorem Termination_foldl_cover {α : Type*} [BEq α] [LawfulBEq α] (sw : α → α) :
    ∀ (l acc : List α), ∀ p ∈ l, (l.foldl (fun acc p =>
      if acc.any (fun q => q == p || q == sw p) then acc else acc ++ [p]) acc).any
        (fun q => q == p || q == sw p) = true := by
  have hmono : ∀ (l acc : List α) (r : α), r ∈ acc → r ∈ l.foldl (fun acc p =>
      if acc.any (fun q => q == p || q == sw p) then acc else acc ++ [p]) acc := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons p l ih =>
      intro acc r hr
      refine ih _ r ?_
      dsimp only
      split_ifs
      · exact hr
      · exact List.mem_append_left _ hr
  intro l
  induction l with
  | nil => intro _ p hp; cases hp
  | cons p₀ l ih =>
    intro acc p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only [List.foldl_cons]
      split_ifs with h
      · obtain ⟨q, hq, hqp⟩ := List.any_eq_true.1 h
        exact List.any_eq_true.2 ⟨q, hmono l _ q hq, hqp⟩
      · refine List.any_eq_true.2 ⟨p, hmono l _ p (List.mem_append_right _
          (List.mem_singleton_self _)), by simp⟩
    · exact ih _ p hp

/-- The pairs of [I, Def 3.2] of a graph with one more copy of a component that it has. -/
private theorem Termination_splitPairs_app {L : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hc : c ∈ L) (co co' : Coeff) :
    (⟨L ++ [c], co⟩ : Graph k n).splitPairs = (⟨L, co'⟩ : Graph k n).splitPairs := by
  unfold Graph.splitPairs
  simp only [Termination_any_app hc]
  rw [List.filterMap_append, List.foldl_append]
  congr 1
  simp only [List.filterMap_cons, List.filterMap_nil]
  split
  · rfl
  · rename_i p hp
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ite_eq_left (Termination_foldl_cover Prod.swap _ [] p (List.mem_filterMap.2 ⟨c, hc, hp⟩))]

/-- A test on the components of a list with one more copy of a component that it has. -/
private theorem Termination_any_ins {K Ad : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hc : c ∈ K) (q : Comp (Atom k n) → Bool) : (K ++ c :: Ad).any q = (K ++ Ad).any q := by
  simp only [List.any_append, List.any_cons]
  by_cases h : q c = true
  · have : K.any q = true := List.any_eq_true.2 ⟨c, hc, h⟩
    simp [this]
  · simp [h]

/-- One term of `O_dot` before `O_merge` of a graph with one more copy of a component that it
has: the same term, or the same term with one more copy of that component. -/
private theorem Termination_dotChoice_app {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (SP A : List (Atom k n × Atom k n × Bool)) :
    (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph k n).dotChoice SP A = Γ.dotChoice SP A ∨
      ∃ K Ad co, c ∈ K ∧
        (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph k n).dotChoice SP A = ⟨K ++ c :: Ad, co⟩ ∧
        Γ.dotChoice SP A = ⟨K ++ Ad, co⟩ := by
  unfold Graph.dotChoice
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  split_ifs with h
  · right
    refine ⟨_, _, _, List.mem_filter.2 ⟨hc, h⟩, ?_, rfl⟩
    simp [List.append_assoc]
  · left
    simp

private theorem Termination_dotBlocks_ins {V : Type*} [DecidableEq V] (as : List V)
    (K Ad : List (Comp V)) {c : Comp V} (hk : c.kind ≠ .dot) :
    dotBlocks as (K ++ c :: Ad) = dotBlocks as (K ++ Ad) := by
  unfold dotBlocks
  rw [List.foldl_append, List.foldl_cons, List.foldl_append, ite_eq_right hk]

/-- `O_merge` of a graph with one more copy of a `×`-dotted edge that it has: the output has one
more copy of the image of that edge; it is normal regular when the other output is, and has the
same order in the count of [II, (2.5)]. -/
private theorem Termination_mergeT_ins {K Ad : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hc : c ∈ K) (hk : c.kind = .xdot) (co : Coeff) {t'' : Tracked k n}
    (h : (⟨K ++ c :: Ad, co⟩ : Graph k n).mergeT = some t'') :
    ∃ t, (⟨K ++ Ad, co⟩ : Graph k n).mergeT = some t ∧
      (∀ C, t.g.Normal C → t''.g.Normal (C + 1)) ∧ t''.g.paperOrd = t.g.paperOrd := by
  have hkd : c.kind ≠ .dot := by rw [hk]; decide
  have hrep : (⟨K ++ c :: Ad, co⟩ : Graph k n).psteps_mrep =
      (⟨K ++ Ad, co⟩ : Graph k n).psteps_mrep := by
    unfold Graph.psteps_mrep
    exact congrArg blockRep (Termination_dotBlocks_ins _ K Ad hkd)
  rw [Termination_mergeT_eq, hrep] at h
  rw [Termination_mergeT_eq]
  set rep := (⟨K ++ Ad, co⟩ : Graph k n).psteps_mrep with hrepd
  unfold Termination_M at h ⊢
  simp only [Termination_any_ins hc] at h
  split_ifs at h ⊢ with h1
  obtain rfl := Option.some.inj h
  refine ⟨_, rfl, ?_⟩
  have hF : psteps_mergeComp rep (Termination_Mf rep) c = some (c.map (Termination_Mf rep)) :=
    mergeComp_other hkd (by rw [hk]; rfl)
  obtain ⟨hmem, hlen, hord, hex, -⟩ := Termination_dup_facts
    (g := ⟨(K ++ Ad).filterMap (psteps_mergeComp rep (Termination_Mf rep)), co⟩)
    (g' := ⟨(K ++ c :: Ad).filterMap (psteps_mergeComp rep (Termination_Mf rep)), co⟩)
    (d := c.map (Termination_Mf rep))
    (by
      simp only [List.filterMap_append, List.filterMap_cons, hF]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm)
    (List.mem_filterMap.2 ⟨c, List.mem_append_left _ hc, hF⟩) (by simp [Comp.map, hk])
  exact ⟨fun C hN => Termination_dup_normal hmem hlen hN, by
    unfold Graph.paperOrd
    rw [hord, hex]⟩

/-- The `O_dot` forms of a graph with one more copy of a `×`-dotted edge that it has are normal
regular of scaling order `> D` in the count of [II, (2.5)] when those of the graph are. -/
private theorem Termination_oDotT_app {D : ℕ} {Γ : Graph k n} {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .xdot)
    (hall : ∀ t ∈ oDotT Γ, (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C) :
    ∀ t ∈ oDotT (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph k n),
      (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C := by
  set Γ'' : Graph k n := ⟨Γ.comps ++ [c], Γ.coeff⟩ with hΓ''
  obtain ⟨hmem, hlen, hord, hex, -⟩ :=
    Termination_dup_facts (g := Γ) (g' := Γ'') (List.Perm.refl _) hc hk
  have hpo : Γ''.paperOrd = Γ.paperOrd := by
    unfold Graph.paperOrd
    rw [hord, hex]
  have hSP : Γ''.splitPairs = Γ.splitPairs := Termination_splitPairs_app hc _ _
  have hlab : Γ''.labels.length = Γ.labels.length := Termination_labels_app hc _ _
  have hany : ∀ q, Γ''.comps.any q = Γ.comps.any q := Termination_any_app hc
  have hself : oDotT Γ = [Tracked.self Γ] → ∀ t ∈ [Tracked.self Γ''],
      (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C := by
    intro hO t ht
    rw [List.mem_singleton.1 ht]
    obtain ⟨h1, C, h2⟩ := hall (Tracked.self Γ) (by rw [hO]; exact List.mem_singleton_self _)
    refine ⟨?_, C + 1, ?_⟩
    · change (D : ℤ) < Γ''.paperOrd
      rw [hpo]
      exact h1
    · exact Termination_dup_normal hmem hlen h2
  intro t ht
  unfold oDotT at ht
  dsimp only at ht
  simp only [hSP, hlab, hany] at ht
  split_ifs at ht with h1 h2
  · exact hself (by unfold oDotT; dsimp only; rw [ite_eq_left h1]) t ht
  · exact hself (by unfold oDotT; dsimp only; rw [ite_eq_right h1, ite_eq_left h2]) t ht
  · obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht
    have hO : oDotT Γ = Γ.splitPairs.sublists.filterMap fun A =>
        (Γ.dotChoice Γ.splitPairs A).mergeT := by
      unfold oDotT
      dsimp only
      rw [ite_eq_right h1, ite_eq_right h2]
    rcases Termination_dotChoice_app hc Γ.splitPairs A with he | ⟨K, Ad, co, hcK, he1, he2⟩
    · rw [he] at hm
      exact hall t (by rw [hO]; exact List.mem_filterMap.2 ⟨A, hA, hm⟩)
    · rw [he1] at hm
      obtain ⟨t₀, ht₀, hN, hp⟩ := Termination_mergeT_ins hcK hk co hm
      obtain ⟨hD, C, hC⟩ := hall t₀ (by
        rw [hO]
        exact List.mem_filterMap.2 ⟨A, hA, by rw [he2]; exact ht₀⟩)
      exact ⟨by rw [hp]; exact hD, C + 1, hN C hC⟩

/-- A graph with one copy of a `×`-dotted edge fewer than a normal regular graph is normal
regular. -/
private theorem Termination_dup_normal' {C : ℕ} {g g' : Graph k n}
    (hmem : ∀ e, e ∈ g'.comps ↔ e ∈ g.comps) (hlen : g'.comps.length = g.comps.length + 1)
    (hN : g'.Normal C) : g.Normal C := by
  obtain ⟨⟨hsz, hcon, hint, hnoint⟩, hsol, hxs⟩ := hN
  refine ⟨⟨by omega, ?_, ?_, fun c hc => hnoint c ((hmem c).2 hc)⟩,
    fun c hc => hsol c ((hmem c).2 hc), ?_⟩
  · rw [← Termination_edgeGraph_mem hmem]
    exact hcon
  · rw [← Termination_wavedThetaGraph_mem hmem]
    exact hint
  · intro u v huv
    simp only [← hmem]
    exact hxs u v huv

/-- `O_merge` of a graph with one copy of a `×`-dotted edge fewer: the graph with one more copy has
an output with one more copy of the image of that edge, which has the same order in the count of
[II, (2.5)], and whose normal regularity gives that of the first output. -/
private theorem Termination_mergeT_del {K Ad : List (Comp (Atom k n))} {c : Comp (Atom k n)}
    (hc : c ∈ K) (hk : c.kind = .xdot) (co : Coeff) {t : Tracked k n}
    (h : (⟨K ++ Ad, co⟩ : Graph k n).mergeT = some t) :
    ∃ t'', (⟨K ++ c :: Ad, co⟩ : Graph k n).mergeT = some t'' ∧
      (∀ C, t''.g.Normal C → t.g.Normal C) ∧ t''.g.paperOrd = t.g.paperOrd := by
  have hkd : c.kind ≠ .dot := by rw [hk]; decide
  have hrep : (⟨K ++ c :: Ad, co⟩ : Graph k n).psteps_mrep =
      (⟨K ++ Ad, co⟩ : Graph k n).psteps_mrep := by
    unfold Graph.psteps_mrep
    exact congrArg blockRep (Termination_dotBlocks_ins _ K Ad hkd)
  rw [Termination_mergeT_eq] at h
  rw [Termination_mergeT_eq, hrep]
  set rep := (⟨K ++ Ad, co⟩ : Graph k n).psteps_mrep with hrepd
  unfold Termination_M at h ⊢
  simp only [Termination_any_ins hc]
  split_ifs at h ⊢ with h1
  obtain rfl := Option.some.inj h
  refine ⟨_, rfl, ?_⟩
  have hF : psteps_mergeComp rep (Termination_Mf rep) c = some (c.map (Termination_Mf rep)) :=
    mergeComp_other hkd (by rw [hk]; rfl)
  obtain ⟨hmem, hlen, hord, hex, -⟩ := Termination_dup_facts
    (g := ⟨(K ++ Ad).filterMap (psteps_mergeComp rep (Termination_Mf rep)), co⟩)
    (g' := ⟨(K ++ c :: Ad).filterMap (psteps_mergeComp rep (Termination_Mf rep)), co⟩)
    (d := c.map (Termination_Mf rep))
    (by
      simp only [List.filterMap_append, List.filterMap_cons, hF]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm)
    (List.mem_filterMap.2 ⟨c, List.mem_append_left _ hc, hF⟩) (by simp [Comp.map, hk])
  exact ⟨fun C hN => Termination_dup_normal' hmem hlen hN, by
    unfold Graph.paperOrd
    rw [hord, hex]⟩

/-- The `O_dot` forms of a graph with one copy of a `×`-dotted edge fewer than a graph whose
`O_dot` forms are normal regular of scaling order `> D` in the count of [II, (2.5)] are normal
regular of scaling order `> D`. -/
private theorem Termination_oDotT_del {D : ℕ} {Γ : Graph k n} {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .xdot)
    (hall : ∀ t ∈ oDotT (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph k n),
      (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C) :
    ∀ t ∈ oDotT Γ, (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C := by
  set Γ'' : Graph k n := ⟨Γ.comps ++ [c], Γ.coeff⟩ with hΓ''
  obtain ⟨hmem, hlen, hord, hex, -⟩ :=
    Termination_dup_facts (g := Γ) (g' := Γ'') (List.Perm.refl _) hc hk
  have hpo : Γ''.paperOrd = Γ.paperOrd := by
    unfold Graph.paperOrd
    rw [hord, hex]
  have hSP : Γ''.splitPairs = Γ.splitPairs := Termination_splitPairs_app hc _ _
  have hlab : Γ''.labels.length = Γ.labels.length := Termination_labels_app hc _ _
  have hany : ∀ q, Γ''.comps.any q = Γ.comps.any q := Termination_any_app hc
  have hself : oDotT Γ'' = [Tracked.self Γ''] → ∀ t ∈ [Tracked.self Γ],
      (D : ℤ) < t.g.paperOrd ∧ ∃ C, t.g.Normal C := by
    intro hO t ht
    rw [List.mem_singleton.1 ht]
    obtain ⟨h1, C, h2⟩ := hall (Tracked.self Γ'') (by rw [hO]; exact List.mem_singleton_self _)
    refine ⟨?_, C, ?_⟩
    · change (D : ℤ) < Γ.paperOrd
      rw [← hpo]
      exact h1
    · exact Termination_dup_normal' hmem hlen h2
  intro t ht
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht with h1 h2
  · refine hself ?_ t ht
    unfold oDotT
    dsimp only
    simp only [hSP, hlab, hany]
    rw [ite_eq_left h1]
  · refine hself ?_ t ht
    unfold oDotT
    dsimp only
    simp only [hSP, hlab, hany]
    rw [ite_eq_right h1, ite_eq_left h2]
  · obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht
    have hO : oDotT Γ'' = Γ''.splitPairs.sublists.filterMap fun A =>
        (Γ''.dotChoice Γ''.splitPairs A).mergeT := by
      unfold oDotT
      dsimp only
      simp only [hSP, hlab, hany]
      rw [ite_eq_right h1, ite_eq_right h2]
    have hA' : A ∈ Γ''.splitPairs.sublists := by rw [hSP]; exact hA
    rcases Termination_dotChoice_app hc Γ.splitPairs A with he | ⟨K, Ad, co, hcK, he1, he2⟩
    · rw [← he] at hm
      rw [hSP] at hO
      exact hall t (by rw [hO]; exact List.mem_filterMap.2 ⟨A, hA, hm⟩)
    · rw [he2] at hm
      obtain ⟨t₀, ht₀, hN, hp⟩ := Termination_mergeT_del hcK hk co hm
      rw [hSP] at hO
      obtain ⟨hD, C, hC⟩ := hall t₀ (by
        rw [hO]
        exact List.mem_filterMap.2 ⟨A, hA, by rw [he1]; exact ht₀⟩)
      exact ⟨by rw [← hp]; exact hD, C, hN C hC⟩

/-- `O_merge` of a graph with the same components and another coefficient: an output with the same
components and the same atoms, and another coefficient. -/
private theorem Termination_mergeT_coeff {k n : ℕ} {Γ Γ' : Graph k n}
    (hc : Γ'.comps = Γ.comps) {t : Tracked k n} (h : Γ.mergeT = some t) :
    ∃ t₁, Γ'.mergeT = some t₁ ∧ ∃ c, t = ⟨t₁.nOut, ⟨t₁.g.comps, c⟩, t₁.f⟩ := by
  have hrep : Γ'.psteps_mrep = Γ.psteps_mrep := by
    unfold Graph.psteps_mrep
    rw [hc]
  rw [Termination_mergeT_eq] at h
  rw [Termination_mergeT_eq, hrep, hc]
  unfold Termination_M at h ⊢
  split_ifs at h ⊢ with h1
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, Γ.coeff, rfl⟩

/-- The `O_dot` forms of a graph with the same components and another coefficient have the same
components and the same atoms, and another coefficient. -/
private theorem Termination_oDotT_coeff {k n : ℕ} (L : List (Comp (Atom k n))) (c₁ c₂ : Coeff) :
    ∀ t ∈ oDotT (⟨L, c₂⟩ : Graph k n), ∃ t₁ ∈ oDotT (⟨L, c₁⟩ : Graph k n),
      ∃ c, t = ⟨t₁.nOut, ⟨t₁.g.comps, c⟩, t₁.f⟩ := by
  have hSP : (⟨L, c₂⟩ : Graph k n).splitPairs = (⟨L, c₁⟩ : Graph k n).splitPairs := rfl
  have hlab : (⟨L, c₂⟩ : Graph k n).labels = (⟨L, c₁⟩ : Graph k n).labels := rfl
  have hself : ∀ t ∈ [Tracked.self (⟨L, c₂⟩ : Graph k n)],
      ∃ t₁ ∈ [Tracked.self (⟨L, c₁⟩ : Graph k n)], ∃ c, t = ⟨t₁.nOut, ⟨t₁.g.comps, c⟩, t₁.f⟩ := by
    intro t ht
    rw [List.mem_singleton.1 ht]
    exact ⟨_, List.mem_singleton_self _, c₂, rfl⟩
  intro t ht
  unfold oDotT at ht ⊢
  dsimp only at ht ⊢
  simp only [hSP, hlab] at ht
  split_ifs at ht ⊢ with h1 h2
  · exact hself t ht
  · exact hself t ht
  · obtain ⟨A, hA, hm⟩ := List.mem_filterMap.1 ht
    obtain ⟨t₁, ht₁, c, hc⟩ := Termination_mergeT_coeff
      (Γ := (⟨L, c₂⟩ : Graph k n).dotChoice (⟨L, c₁⟩ : Graph k n).splitPairs A)
      (Γ' := (⟨L, c₁⟩ : Graph k n).dotChoice (⟨L, c₁⟩ : Graph k n).splitPairs A) rfl hm
    exact ⟨t₁, List.mem_filterMap.2 ⟨A, hA, ht₁⟩, c, hc⟩

end Members

/-! ## The invariant of a run along each step -/

section Steps

open private DotNorm.step DotNorm.Keep DotNorm.Keep.normal DotNorm.Keep.block DotNorm.Keep.nondot
  DotNorm.Keep.sub DotNorm.Keep.q from RBM8D.Graph.Local.DotNorm
open private oDotT_normal_self from RBM8D.Graph.Local.Weight

variable {n₀ : ℕ}

/-- Only diffusive edges at `⊗`, as a statement on the components. -/
private theorem Termination_td_iff {Γ : Graph 3 n₀} :
    Γ.TensorDiffusive ↔
      ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true := by
  unfold Graph.TensorDiffusive
  rw [List.all_eq_true]
  refine forall₂_congr fun c _ => ?_
  by_cases h : c.x = .inl 0 ∨ c.y = .inl 0
  · rcases h with h | h <;> simp [h]
  · push Not at h
    simp [h.1, h.2]

/-- Step 1 (`loc`). -/
private theorem Termination_inv_loc {D C : ℕ} {Γ : Graph 3 n₀} {N : ℕ} {o : Fin 5} {x : Fin n₀}
    (hS : ¬ Γ.StopsB N) (hD : ¬ (D : ℤ) < Γ.ord) (hN : Γ.Normal C) (hL : Γ.LabelFree)
    (hP : Γ.Plain) (hside : Γ.LocSide o (.inr x)) (hI : Γ.InvRun D) :
    ∀ h ∈ (localOp' o (.inr x) Γ).forget, h.2.InvRun D := by
  obtain ⟨hB, hT⟩ := Termination_inv1 hI (fun h => Termination_not_qGraph hL h.2) hD
  have hR : ¬ Γ.IsRecollision {1, 2} := fun h => hS ⟨⟨C, hN⟩, Or.inl h⟩
  intro h hh
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hh
  have h1 := (localSPDB n₀ C x Γ hB.1 hB.2.2.1 hB.2.2.2.1 hB.2.1).2 hN hL hP o hside t ht
  have h2 := localOp_clausesB n₀ C x Γ hN hL hP hB hT hR o hside t ht
  exact Or.inl ⟨⟨h1.1, h2.1, h1.2, h2.2.1, h2.2.2.1⟩, h2.2.2.2⟩

/-- `O_dot` (`dot`). -/
private theorem Termination_inv_dot {D : ℕ} {Γ : Graph 3 n₀} (hI : Γ.InvRun D) :
    ∀ h ∈ oDot Γ, h.2.InvRun D := by
  intro h hh
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hh
  rcases hI with ⟨hB, hT⟩ | ⟨h0, hQ⟩ | ⟨hD, hE, hC, hT, hall⟩
  · exact Or.inl ⟨qElemStep_invB _ _ (QElemStep.dot Γ t ht) hB, oDot_otimes.1 n₀ Γ hT t ht⟩
  · subst h0
    exact Or.inr (Or.inl (oDot_otimes.2 Γ hQ t ht))
  · obtain ⟨hD', C', hN'⟩ := hall t ht
    obtain ⟨hE', hC'⟩ := oDot_extClause n₀ Γ hE hC hT t ht
    refine Or.inr (Or.inr ⟨hD', hE', hC', oDot_otimes.1 n₀ Γ hT t ht, ?_⟩)
    rw [oDotT_normal_self hN']
    intro t' ht'
    rw [List.mem_singleton.1 ht']
    exact ⟨hD', C', hN'⟩

/-- The removal of a redundant dotted edge (`dropDot`). -/
private theorem Termination_inv_dropDot {D C : ℕ} {Γ Γ' : Graph 3 n₀} (hst : DotNormStep Γ Γ')
    (hN : Γ.Normal C) (hP : Γ.Plain) (hI : Γ.InvRun D) : Γ'.InvRun D := by
  obtain ⟨i, c, hc, hk, hr, rfl⟩ := hst
  obtain ⟨he, hord, hK⟩ := DotNorm.step hN hP hc hk hr
  have hsub : ∀ d ∈ (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).comps, d ∈ Γ.comps :=
    fun d hd => (DotNorm.Keep.sub hK).subset hd
  have hnd := DotNorm.Keep.nondot hK
  have hb := DotNorm.Keep.block hK
  have hmem : ∀ d ∈ Γ.comps, d.kind ≠ .dot →
      d ∈ (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).comps := by
    intro d hd hdk
    have : d ∈ Γ.comps.filter (fun d => decide (d.kind ≠ .dot)) :=
      List.mem_filter.2 ⟨hd, by simpa using hdk⟩
    rw [← hnd] at this
    exact (List.mem_filter.1 this).1
  have hdeg : ∀ u, (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).nonDotDeg u = Γ.nonDotDeg u := by
    have key : ∀ (u : Atom 3 n₀) (L : List (Comp (Atom 3 n₀))),
        (L.filter fun c => decide ((c.x = u ∨ c.y = u) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)) =
          (L.filter fun d => decide (d.kind ≠ .dot)).filter
            fun c => decide ((c.x = u ∨ c.y = u) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot) := by
      intro u L
      rw [List.filter_filter]
      apply List.filter_congr
      intro d _
      by_cases h : d.kind = .dot <;> simp [h]
    intro u
    unfold Graph.nonDotDeg
    rw [key, hnd, ← key]
  rcases hI with ⟨hB, hT⟩ | ⟨h0, hQ⟩ | ⟨hD, hE, hC, hT, -⟩
  · exact Or.inl ⟨qElemStep_invB _ _ (QElemStep.dropDot i Γ c hc hk hr) hB,
      Termination_td_of hsub hT⟩
  · exact Or.inr (Or.inl ⟨h0, DotNorm.Keep.q hK hQ⟩)
  · have hpo : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).paperOrd = Γ.paperOrd := by
      unfold Graph.paperOrd
      linarith
    have hN' := DotNorm.Keep.normal hK
    refine Or.inr (Or.inr ⟨by rw [hpo]; exact hD, Termination_extClause_of hb hsub hmem hdeg hE,
      Termination_colourInvB_of hb hsub hC, Termination_td_of hsub hT, ?_⟩)
    rw [oDotT_normal_self hN']
    intro t ht
    rw [List.mem_singleton.1 ht]
    refine ⟨?_, C, hN'⟩
    change (D : ℤ) < (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n₀).paperOrd
    rw [hpo]
    exact hD

/-- The duplication of a `×`-dotted edge between internal atoms (`xdotDup`). -/
private theorem Termination_inv_xdotDup {D : ℕ} {Γ : Graph 3 n₀} (i : Fin Γ.comps.length)
    (hk : Γ.comps[i].kind = .xdot) (hx : Γ.comps[i].x.isRight = true) (hI : Γ.InvRun D) :
    (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph 3 n₀).InvRun D := by
  have hd : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
  obtain ⟨hmem, -, hord, hex, hdeg⟩ := Termination_dup_facts (g := Γ)
    (g' := ⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩) (List.Perm.refl _) hd hk
  have hsb := Termination_sameBlock_mem hmem
  have hs : ∀ c ∈ (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph 3 n₀).comps, c ∈ Γ.comps :=
    fun c hc => (hmem c).1 hc
  have hnd : ∀ c ∈ Γ.comps, c.kind ≠ .dot →
      c ∈ (⟨Γ.comps ++ [Γ.comps[i]], Γ.coeff⟩ : Graph 3 n₀).comps :=
    fun c hc _ => (hmem c).2 hc
  rcases hI with ⟨hB, hT⟩ | ⟨h0, -⟩ | ⟨hD, hE, hC, hT, hall⟩
  · exact Or.inl ⟨⟨(MGraph.spd_transport _ _ _ _ _ _ (Termination_toMG'_app hd hk)).2 hB.1,
      Termination_colourInvB_of hsb hs hB.2.1, Termination_extClause_of hsb hs hnd hdeg hB.2.2.1,
      fun c hc => hB.2.2.2.1 c (hs c hc), fun c hc => hB.2.2.2.2 c (hs c hc)⟩,
      Termination_td_of hs hT⟩
  · exfalso
    subst h0
    rcases h : Γ.comps[i].x with a | j
    · rw [h] at hx
      cases hx
    · exact j.elim0
  · refine Or.inr (Or.inr ⟨?_, Termination_extClause_of hsb hs hnd hdeg hE,
      Termination_colourInvB_of hsb hs hC, Termination_td_of hs hT,
      Termination_oDotT_app hd hk hall⟩)
    unfold Graph.paperOrd
    rw [hord, hex]
    exact hD

/-- The removal of one of two parallel `×`-dotted edges between internal atoms (`xdotDrop`). -/
private theorem Termination_inv_xdotDrop {D : ℕ} {Γ : Graph 3 n₀} (i j : Fin Γ.comps.length)
    (hij : i ≠ j)
    (hc : Γ.comps[j] = Γ.comps[i] ∨
      Γ.comps[j] = { Γ.comps[i] with x := Γ.comps[i].y, y := Γ.comps[i].x })
    (hk : Γ.comps[i].kind = .xdot) (hx : Γ.comps[i].x.isRight = true) (hI : Γ.InvRun D) :
    (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n₀).InvRun D := by
  set Γ' : Graph 3 n₀ := ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ with hΓ'
  have hd : Γ.comps[i] ∈ Γ'.comps :=
    List.mem_eraseIdx_iff_getElem.2 ⟨i, i.2, fun h => hij (Fin.ext h), rfl⟩
  have hI' := reorder_invRun _ D Γ _ (Strategy_reorder_xdotDrop Γ i j hc hk) hI
  obtain ⟨hmem, -, hord, hex, hdeg⟩ := Termination_dup_facts (g := Γ')
    (g' := ⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩) (List.Perm.refl _) hd hk
  have hsb : ∀ u v, Γ'.SameBlock u v ↔
      (⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩ : Graph 3 n₀).SameBlock u v :=
    fun u v => (Termination_sameBlock_mem hmem u v).symm
  have hs : ∀ c ∈ Γ'.comps, c ∈ (⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩ : Graph 3 n₀).comps :=
    fun c hc => (hmem c).2 hc
  have hnd : ∀ c ∈ (⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩ : Graph 3 n₀).comps,
      c.kind ≠ .dot → c ∈ Γ'.comps := fun c hc _ => (hmem c).1 hc
  rcases hI' with ⟨hB, hT⟩ | ⟨h0, -⟩ | ⟨hD, hE, hC, hT, hall⟩
  · exact Or.inl ⟨⟨(MGraph.spd_transport _ _ _ _ _ _ (Termination_toMG'_app hd hk)).1 hB.1,
      Termination_colourInvB_of hsb hs hB.2.1,
      Termination_extClause_of hsb hs hnd (fun u => (hdeg u).symm) hB.2.2.1,
      fun c hc => hB.2.2.2.1 c (hs c hc), fun c hc => hB.2.2.2.2 c (hs c hc)⟩,
      Termination_td_of hs hT⟩
  · exfalso
    subst h0
    rcases h : Γ.comps[i].x with a | j
    · rw [h] at hx
      cases hx
    · exact j.elim0
  · refine Or.inr (Or.inr ⟨?_, Termination_extClause_of hsb hs hnd (fun u => (hdeg u).symm) hE,
      Termination_colourInvB_of hsb hs hC, Termination_td_of hs hT,
      Termination_oDotT_del hd hk hall⟩)
    have hpo : (⟨Γ'.comps ++ [Γ.comps[i]], Γ'.coeff⟩ : Graph 3 n₀).paperOrd = Γ'.paperOrd := by
      unfold Graph.paperOrd
      rw [hord, hex]
    rw [← hpo]
    exact hD

/-- A change of the coefficient (`coeffNorm`): the invariant of a run does not read the
coefficient. -/
private theorem Termination_inv_coeffNorm {D : ℕ} {Γ : Graph 3 n₀} (co : Coeff)
    (hI : Γ.InvRun D) : (⟨Γ.comps, co⟩ : Graph 3 n₀).InvRun D := by
  rcases hI with ⟨hB, hT⟩ | ⟨h0, hQ⟩ | ⟨hD, hE, hC, hT, hall⟩
  · exact Or.inl ⟨⟨(MGraph.spd_transport _ _ _ _ _ _ (Termination_toMG'_coeff Γ co)).2 hB.1,
      hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2⟩, hT⟩
  · exact Or.inr (Or.inl ⟨h0, hQ⟩)
  · refine Or.inr (Or.inr ⟨hD, hE, hC, hT, ?_⟩)
    intro t ht
    obtain ⟨t₁, h1, c, rfl⟩ := Termination_oDotT_coeff Γ.comps Γ.coeff co t ht
    obtain ⟨hD', C, ⟨h2, h3, h4, h5⟩, h6, h7⟩ := hall t₁ h1
    exact ⟨hD', C, ⟨h2, h3, h4, h5⟩, h6, h7⟩

/-- Step 3 (`qexp`). -/
private theorem Termination_inv_qexp {D : ℕ} {Γ : Graph 3 n₀} {x : Fin n₀} {E : TExpansion 3 n₀}
    (hD : ¬ (D : ℤ) < Γ.ord) (hnQ : ¬ Γ.IsQGraph) (hcl : qexpClauseB D x Γ E)
    (hI : Γ.InvRun D) : ∀ h ∈ E.forget, h.2.InvRun D := by
  obtain ⟨hB, hT⟩ := Termination_inv1 hI (fun h => hnQ h.2) hD
  obtain ⟨⟨C', hout⟩, hinv⟩ := hcl
  intro h hh
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hh
  refine Or.inl ⟨hinv hB t ht, Termination_td_iff.2 fun c hc hat => ?_⟩
  have hperm := (hout t ht).2 (Termination_td_iff.1 hT)
  have hc' : c ∈ t.g.comps.filter fun c => decide (c.x = .inl 0 ∨ c.y = .inl 0) :=
    List.mem_filter.2 ⟨hc, by simpa using hat⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hc')
  have hd' := List.mem_filter.1 hd
  exact Termination_td_iff.1 hT d hd'.1 (by simpa using hd'.2)

section Subst

open private GlobalGoodRows_root GlobalGoodRows_noExt0 GlobalGoodRows_dA0_spd
  from RBM8D.GlobalExp.GlobalGoodRows
open private SubstSPD_noGhost_of_tKinds SubstSPD_swap_noGhost SubstSPD_tVarCorr_cases
  SubstSPD_tc_gs123 SubstSPD_comps_of_code SubstSPD_gs_comps SubstSPD_tc1 SubstSPD_tc2
  SubstSPD_tc3 from RBM8D.GlobalExp.SubstSPD
open private gn_glue_dotExcess from RBM8D.GlobalExp.GlueNormal
open private SubstDC_swap_otimesNoDot SubstDC_swap_dotExcess SubstDC_tVar_ord
  from RBM8D.GlobalExp.SubstDC

/-- The graphs of [II, Def 3.2] of `Err`, with their weights `W_d`, have no ghost edge. -/
private theorem Termination_noGhost_of_tKindsErr {k n N : ℕ} {Γ : Graph k n}
    (h : Γ.TKindsErr N) : Γ.NoGhost := by
  intro c hc hk
  have := List.all_eq_true.1 h c hc
  simp [Comp.isTKind, hk] at this

/-- The graph `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` with its solid edge reversed has no ghost edge, and its first
component is the diffusive edge `Θ^{[o]}_{⊗⊕}`. -/
private theorem Termination_theta_facts (o : List ℕ) :
    (thetaLabelGraph o).swapSolid.NoGhost ∧
      ∃ i₀ : Fin (thetaLabelGraph o).swapSolid.comps.length,
        (thetaLabelGraph o).swapSolid.comps[i₀].kind.isDiffusive = true ∧
        (((thetaLabelGraph o).swapSolid.comps[i₀].x = .inl 0 ∧
            (thetaLabelGraph o).swapSolid.comps[i₀].y = .inl 1) ∨
          ((thetaLabelGraph o).swapSolid.comps[i₀].x = .inl 1 ∧
            (thetaLabelGraph o).swapSolid.comps[i₀].y = .inl 0)) := by
  refine ⟨?_, ⟨0, by simp [thetaLabelGraph, Graph.swapSolid]⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
  · intro c hc
    simp only [thetaLabelGraph, Graph.swapSolid, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [Comp.swapSolid, mkC, Kind.isSolid]
  all_goals simp [thetaLabelGraph, Graph.swapSolid, Comp.swapSolid, mkC, Kind.isSolid,
    Kind.isDiffusive]

/-- The substitution of a graph of `R`, `A` or `Q` with the clauses of [II, Def 6.3]: the result is
sequentially pre-deterministic in the block reading. -/
private theorem Termination_spd_glue {m : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    (hDF : (H.glue x y₁ y₂ (tVar true)).DotFree) (hB : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    {g : Σ n, Graph 3 n} (hspd : spdPM' g.2)
    (hroot : (g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB) (hG : g.2.NoGhost)
    (hAE : g.2.AtExternals) (hTd : g.2.TensorDiffusive) (hX : g.2.dotExcess = 0) :
    spdPM' (H.glue x y₁ y₂ g.2.swapSolid) := by
  obtain ⟨n₁, g₁⟩ := g
  rcases hroot with ⟨h0, hR⟩ | ⟨hE', hC'⟩
  · simp only at h0
    subst h0
    obtain ⟨⟨i₀, hd₀, he₀⟩, -⟩ := GlobalGoodRows_root g₁ hR hTd hAE
    exact GlobalGoodRows_dA0_spd H x y₁ y₂ g₁.swapSolid hDF hB hst (SubstSPD_swap_noGhost _ hG)
      i₀ hd₀ he₀
  · exact (substSPDB m n₁ H x y₁ y₂ g₁ hDF hB hst hspd hE' hC' hTd hAE hG hX).1

/-- Steps 2–3 (`subst`): every substituted graph has the invariant of a run, in its first
disjunct for the graphs of the leading term, of `Σ_T`, of `R`, `A`, `Q` and of the recollision
terms, in its third disjunct for the graphs of `Err`. -/
private theorem Termination_inv_subst {n D m C : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    (hn : 3 ≤ n) (h𝒯 : 𝒯.IsTExpStruct Sig (n - 1) D) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (hD : ¬ (D : ℤ) < (H.glue x y₁ y₂ (tVar true)).ord)
    (h4 : 4 ≤ (H.glue x y₁ y₂ (tVar true)).ord) (hon : (H.glue x y₁ y₂ (tVar true)).ord ≤ n)
    (hN : (H.glue x y₁ y₂ (tVar true)).Normal C) (hDF : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hL : H.LabelFree) (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hR : ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2})
    (hT : (H.glue x y₁ y₂ (tVar true)).TensorDiffusive)
    (hmis : (H.glue x y₁ y₂ (tVar true)).MISLocStdB)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvRun D) :
    ∀ h ∈ H.globalSubst x y₁ y₂ (𝒯.tSubst (n - 1)).swapSolid, h.2.InvRun D := by
  obtain ⟨hDn, -, -, hSh, hDef⟩ := h𝒯
  have hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63 := ⟨hDn, hSh, hDef⟩
  obtain ⟨hB, -⟩ := Termination_inv1 hI (fun h => absurd h.1 (Nat.succ_ne_zero m)) hD
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hNG0 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.swapSolid.NoGhost := by
    intro g hg
    simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg
    rcases hg with (((((hl | hs) | hr) | ha) | hq) | he) | htc
    · simp only [leadExp, List.mem_singleton] at hl
      subst hl
      exact (Termination_theta_facts []).1
    · obtain ⟨o, -, rfl⟩ := List.mem_map.1 hs
      exact (Termination_theta_facts o).1
    · exact SubstSPD_swap_noGhost _ (SubstSPD_noGhost_of_tKinds (hSh.1.1 g (by simp [hr])).2.1)
    · exact SubstSPD_swap_noGhost _ (SubstSPD_noGhost_of_tKinds (hSh.1.1 g (by simp [ha])).2.1)
    · exact SubstSPD_swap_noGhost _ (SubstSPD_noGhost_of_tKinds (hSh.1.1 g (by simp [hq])).2.1)
    · exact SubstSPD_swap_noGhost _ (Termination_noGhost_of_tKindsErr (hSh.1.2 g he).2.1)
    · obtain ⟨h1, hcode⟩ := SubstSPD_tVarCorr_cases g htc
      obtain ⟨n₁, g₂⟩ := g
      simp only at h1 hcode
      subst h1
      intro c hc
      rcases hcode with hc' | hc' | hc' <;> rw [SubstSPD_comps_of_code hc'] at hc <;>
        simp only [SubstSPD_tc1, SubstSPD_tc2, SubstSPD_tc3, List.mem_cons, List.not_mem_nil,
          or_false] at hc <;>
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [mkC]
  have hNGF : ∀ g ∈ (𝒯.tSubst (n - 1)).swapSolid, g.2.NoGhost := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
    exact hNG0 g₀ hg₀
  intro h hh
  have hE := globalSubst_extClause m H x y₁ y₂ _ hx hy₁ hy₂ hB.2.2.1 h hh
  obtain ⟨hC, hNG, hLI, hT'⟩ := globalSubst_clauses m H x y₁ y₂ _ hx hy₁ hy₂ hB.2.2.1 hB.2.1
    hB.2.2.2.1 hB.2.2.2.2 hT hR hNGF h hh
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hh
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
  have hfirst : spdPM' (H.glue x y₁ y₂ g₀.2.swapSolid) →
      (⟨m + g₀.1, H.glue x y₁ y₂ g₀.2.swapSolid⟩ : Σ n, Graph 3 n).2.InvRun D :=
    fun hs => Or.inl ⟨⟨hs, hC, hE, hNG, hLI⟩, hT'⟩
  have hmemT : ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q, g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err :=
    fun g hg => List.mem_append_left _ hg
  simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg₀
  rcases hg₀ with (((((hl | hs) | hr) | ha) | hq) | he) | htc
  · simp only [leadExp, List.mem_singleton] at hl
    subst hl
    obtain ⟨hG, i₀, hd₀, he₀⟩ := Termination_theta_facts []
    exact hfirst (GlobalGoodRows_dA0_spd H x y₁ y₂ _ hDF hB hst hG i₀ hd₀ he₀)
  · obtain ⟨o, -, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hG, i₀, hd₀, he₀⟩ := Termination_theta_facts o
    exact hfirst (GlobalGoodRows_dA0_spd H x y₁ y₂ _ hDF hB hst hG i₀ hd₀ he₀)
  · have hg3 : g₀ ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hr]
    obtain ⟨-, hTK, hAE, -⟩ := hSh.1.1 g₀ hg3
    obtain ⟨hTd, hX, -, -⟩ := hDef.2.1 g₀ (hmemT g₀ hg3)
    obtain ⟨hgs₀, hE₀, hC₀⟩ := hDef.1.1 g₀ hr
    exact hfirst (Termination_spd_glue hDF hB hst hgs₀.1 (Or.inr ⟨hE₀, hC₀⟩)
      (SubstSPD_noGhost_of_tKinds hTK) hAE hTd hX)
  · have hg3 : g₀ ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [ha]
    obtain ⟨-, hTK, hAE, -⟩ := hSh.1.1 g₀ hg3
    obtain ⟨hTd, hX, -, -⟩ := hDef.2.1 g₀ (hmemT g₀ hg3)
    obtain ⟨hspd, hroot⟩ := hDef.1.2.1 g₀ ha
    exact hfirst (Termination_spd_glue hDF hB hst hspd hroot
      (SubstSPD_noGhost_of_tKinds hTK) hAE hTd hX)
  · have hg3 : g₀ ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by simp [hq]
    obtain ⟨-, hTK, hAE, -⟩ := hSh.1.1 g₀ hg3
    obtain ⟨hTd, hX, -, -⟩ := hDef.2.1 g₀ (hmemT g₀ hg3)
    obtain ⟨hspd, -, hroot⟩ := hDef.1.2.2 g₀ hq
    exact hfirst (Termination_spd_glue hDF hB hst hspd hroot
      (SubstSPD_noGhost_of_tKinds hTK) hAE hTd hX)
  · -- a graph of `Err`: the third disjunct
    obtain ⟨hTd, hX, -, -⟩ := hDef.2.1 g₀ (by simp [he])
    have hord : (D : ℤ) < g₀.2.ord := hSh.2.2.2.2 g₀ he
    have hε := gn_glue_dotExcess (H := H) (x := x) (y₁ := y₁) (y₂ := y₂) hDF
      (SubstDC_swap_otimesNoDot hTd) (by rw [SubstDC_swap_dotExcess]; exact hX)
    have e1 := glue_ord 3 m g₀.1 H x y₁ y₂ g₀.2.swapSolid
    have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
    have e3 : g₀.2.swapSolid.ord = g₀.2.ord := (swapSolid_basic 3 g₀.1 g₀.2).2.1
    rw [SubstDC_tVar_ord] at e2
    refine Or.inr (Or.inr ⟨?_, hE, hC, hT', fun t ht => ?_⟩)
    · change (D : ℤ) < (H.glue x y₁ y₂ g₀.2.swapSolid).paperOrd
      unfold Graph.paperOrd
      rw [hε]
      split_ifs <;> omega
    · obtain ⟨⟨C', hNt⟩, hDFt, -, hot⟩ := globalGood_row5 glue_oDotT_normal n D 𝒯 m C H x y₁ y₂
        hn hcore hL hN hDF h4 hon hB hT hgs hR hmis hst g₀ he t ht
      refine ⟨?_, C', hNt⟩
      rw [Graph.paperOrd_of_dotExcess (SolidMono.dotExcess_zero hDFt)]
      omega
  · -- a recollision term of [II, (4.15)]
    obtain ⟨h1, hcode⟩ := SubstSPD_tVarCorr_cases g₀ htc
    obtain ⟨g1, g2, g3⟩ := SubstSPD_tc_gs123 H x y₁ y₂ hDF hB hgs hst
    obtain ⟨n₁, g₂⟩ := g₀
    simp only at h1 hcode
    subst h1
    refine hfirst ?_
    have key : ∀ tc : Graph 3 1, g₂.swapSolid.code = tc.code → gsPM' (H.glue x y₁ y₂ tc) →
        spdPM' (H.glue x y₁ y₂ g₂.swapSolid) := by
      intro tc hc hgtc
      have hcomps := SubstSPD_comps_of_code hc
      refine ((SubstSPD_gs_comps (Γ₁ := H.glue x y₁ y₂ g₂.swapSolid)
        (Γ₂ := H.glue x y₁ y₂ tc) ?_).2 hgtc).1
      simp only [Graph.glue, hcomps]
    rcases hcode with hc | hc | hc
    · exact key _ hc g1
    · exact key _ hc g2
    · exact key _ hc g3

end Subst

end Steps

/-! ## The invariant of a run -/

/-- **Every step of [II, Strategy 6.6] keeps the invariant of a run** ([II, Lemma 6.8], the
invariant): the statement `invRun_stepStmt`. Step 1 keeps `Graph.InvB'` and the diffusive edges
at `⊗` ([II, Lemmas 5.10, 6.4]); `O_dot` and the removal of a redundant dotted edge keep each of
the three disjuncts; a reordering and the duplication of a `×`-dotted edge keep the components;
a graph with a `×`-dotted loop has no output (`xdotLoop`);
Steps 2–3 give the first disjunct for the substituted graphs of the leading term, of `Σ_T`, of
`R`, `A`, `Q` and of the recollision terms of [II, (4.15)] ([II, Lemma 6.5 (2)–(4)]), and the
third disjunct for those of `Err` ([II, Lemma 6.5 (5)]); a `Q`-expansion of Step 3 keeps
`Graph.InvB'` by `qexpClauseB` and the diffusive edges at `⊗` by `Tracked.QOtimes`. -/
theorem invRun_step : invRun_stepStmt := by
  intro n D Sig 𝒯 hn h𝒯 g E₁ hs hI
  cases hs with
  | loc Γ o x C hS hD hN hL hP _ _ hside => exact Termination_inv_loc hS hD hN hL hP hside hI
  | dot Γ => exact Termination_inv_dot hI
  | dropDot Γ Γ' C hst hN hP =>
    intro h hh
    rw [List.mem_singleton.1 hh]
    exact Termination_inv_dropDot hst hN hP hI
  | reorder Γ Γ' hr =>
    intro h hh
    rw [List.mem_singleton.1 hh]
    exact reorder_invRun _ D Γ Γ' hr hI
  | xdotDup Γ i hk hx _ =>
    intro h hh
    rw [List.mem_singleton.1 hh]
    exact Termination_inv_xdotDup i hk hx hI
  | xdotDrop Γ i j hij hc hk hx _ =>
    intro h hh
    rw [List.mem_singleton.1 hh]
    exact Termination_inv_xdotDrop i j hij hc hk hx hI
  | xdotLoop _ _ _ _ =>
    intro h hh
    exact absurd hh List.not_mem_nil
  | coeffNorm Γ =>
    intro h hh
    rw [List.mem_singleton.1 hh]
    exact Termination_inv_coeffNorm _ hI
  | subst H x y₁ y₂ C hD h4 hon hN hDF hL hgs hR hT hmis hst =>
    exact Termination_inv_subst hn h𝒯 H x y₁ y₂ hD h4 hon hN hDF hL hgs hR hT hmis hst hI
  | qexp Γ x E hD _ hnQ _ hcl => exact Termination_inv_qexp hD hnQ hcl hI

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

open private h2Rec_struct from RBM8D.TExp.Second

end Instances

end RBM8D.Graphs
