module

public import RBM8D.Graph.QExp.Main
public import RBM8D.Graph.QExp.SelStep3
public import RBM8D.Graph.DotBlocks

@[expose] public section

/-!
# The second step of the `Q`-expansions with deterministic choices

[II, Lemma 4.13] ([II, §4.4, Step 2], with [II, (4.23), (4.24)]) for functions of the graph: every
choice is made at the first index, and every step is a term of an operator of `QElemStep` with its
own atom map (`SelStep2Step`).

* `selInit X g`: `O_merge`, the removal of the redundant dotted edges, and the moves of the
  labelled components of the block of `X` to `X` (`selRebase`).
* `selRound X g`: the identity inside `P_X` (`selOp`: `O^{(x),1}_weight`, [II, (4.23)] or
  [II, (4.24)]), the normalization (`selNorm`: at the first `×`-dotted edge without solid edge,
  else at the first solid edge without `×`-dotted edge; a term with an identification is followed
  by `O_merge` and the removal of the redundant dotted edges), and `selRebase`.

The main statements are `selStep2_init` and `selStep2_round` (the clauses of the states of the
construction and `SR`, the scaling orders, the components at the external atoms, the history
`SelStep2Hist` of every output graph), and `selStep2_round_pmBlock` (for `k = 3`, a round that
puts `⊕` and `⊖` in one dotted block raises the paper scaling order by at least `1`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The elementary steps of the run and the history of an output graph -/

section SelStep2Hist

variable {k : ℕ}

/-- One elementary step of the run of [II, §4.4, Step 2] from `Γ`, with its own atom map `t.f`:
`t` is a term of `1 = 1_{u = v} + 1_{u ≠ v}` with `v` internal (`oSplitT`), of
`1_{u ≠ v} = 1 - 1_{u = v}` (`oXdotT`), the output of `O_merge`, `Γ` without a dotted edge whose
ends are joined by the other dotted edges, `Γ` with an end of a component moved to an atom of its
block, or a term of `O^{(x),1}_weight`, [II, (4.23)] or [II, (4.24)] inside `P_x`. Each is a
constructor of `QElemStep` with the same output (`SelStep2Step.qElemStep`). -/
inductive SelStep2Step : {n : ℕ} → Graph k n → Tracked k n → Prop
  | split {n : ℕ} (u v : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hv : v.isRight = true)
      (ht : t ∈ oSplitT u v Γ) : SelStep2Step Γ t
  | xdot {n : ℕ} (i : ℕ) (Γ : Graph k n) (t : Tracked k n) (ht : t ∈ oXdotT i Γ) :
      SelStep2Step Γ t
  | merge {n : ℕ} (Γ : Graph k n) (t : Tracked k n) (ht : Γ.mergeT = some t) : SelStep2Step Γ t
  | dropDot {n : ℕ} (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n)) (hc : Γ.comps[i]? = some c)
      (hk : c.kind = .dot)
      (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameBlock c.x c.y) :
      SelStep2Step Γ (Tracked.self ⟨Γ.comps.eraseIdx i, Γ.coeff⟩)
  | rebase {n : ℕ} (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n)) (u v : Atom k n)
      (hc : Γ.comps[i]? = some c) (hk : c.kind ≠ .dot) (hb : Γ.SameBlock u v) :
      SelStep2Step Γ (Tracked.self ⟨Γ.comps.set i
        { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }, Γ.coeff⟩)
  | pWeight1 {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hP : Γ.IsPFormAt x)
      (hp : Γ.Plain) (ht : t ∈ pLiftT x Γ (oWeight1T x Γ.pCore)) : SelStep2Step Γ t
  | pWeight2 {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hP : Γ.IsPFormAt x)
      (hp : Γ.Plain) (ht : t ∈ oWeightP2T x Γ) : SelStep2Step Γ t
  | pMultiE {n : ℕ} (x : Atom k n) (Γ : Graph k n) (E : TExpansion k n) (t : Tracked k n)
      (hP : Γ.IsPFormAt x) (hp : Γ.Plain) (hE : multiEHat x Γ.pCore = some E)
      (ht : t ∈ pLiftT x Γ E) : SelStep2Step Γ t

/-- A step of the run is an elementary step `QElemStep`. -/
theorem SelStep2Step.qElemStep {n : ℕ} {Γ : Graph k n} {t : Tracked k n}
    (h : SelStep2Step Γ t) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩ := by
  cases h with
  | split u v Γ t hv ht => exact .split u v Γ t hv ht
  | xdot i Γ t ht => exact .xdot i Γ t ht
  | merge Γ t ht => exact .merge Γ t ht
  | dropDot i Γ c hc hk hb => exact .dropDot i Γ c hc hk hb
  | rebase i Γ c u v hc hk hb => exact .rebase i Γ c u v hc hk hb
  | pWeight1 x Γ t hP hp ht => exact .pWeight1 x Γ t hP hp ht
  | pWeight2 x Γ t hP hp ht => exact .pWeight2 x Γ t hP hp ht
  | pMultiE x Γ E t hP hp hE ht => exact .pMultiE x Γ E t hP hp hE ht

/-- The history of an output `s` of the run from `Γ`: a chain of steps `SelStep2Step`, each with
its own atom map; `s.f` is the composite of these maps. -/
inductive SelStep2Hist : {n : ℕ} → Graph k n → Tracked k n → Prop
  | refl {n : ℕ} (Γ : Graph k n) : SelStep2Hist Γ (Tracked.self Γ)
  | step {n : ℕ} {Γ : Graph k n} {t : Tracked k n} {s : Tracked k t.nOut}
      (h : SelStep2Step Γ t) (hs : SelStep2Hist t.g s) : SelStep2Hist Γ (t.comp s)

theorem SelStep2Hist.single {n : ℕ} {Γ : Graph k n} {t : Tracked k n} (h : SelStep2Step Γ t) :
    SelStep2Hist Γ t := by
  have := SelStep2Hist.step h (SelStep2Hist.refl t.g)
  rwa [Tracked.psteps_comp_self] at this

theorem SelStep2Hist.trans {n : ℕ} {Γ : Graph k n} {t : Tracked k n}
    (h1 : SelStep2Hist Γ t) {s : Tracked k t.nOut} (h2 : SelStep2Hist t.g s) :
    SelStep2Hist Γ (t.comp s) := by
  induction h1 with
  | refl Γ => exact h2
  | @step n Γ t s' h _ ih => exact SelStep2Hist.step (s := s'.comp s) h (ih h2)

/-- Removals of redundant dotted edges are steps of the run with the identity map. -/
theorem SelStep2Hist.of_drops {n : ℕ} {g g' : Graph k n}
    (h : Relation.ReflTransGen SelStep3Drop g g') : SelStep2Hist g (Tracked.self g') := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head hst _ ih =>
    obtain ⟨i, c, hc, hk, hb, rfl⟩ := hst
    exact SelStep2Hist.step (SelStep2Step.dropDot i _ c hc hk hb) ih

theorem SelStep2Hist.self_comp {n : ℕ} {Γ g : Graph k n} {s : Tracked k n}
    (h1 : SelStep2Hist Γ (Tracked.self g)) (h2 : SelStep2Hist g s) : SelStep2Hist Γ s :=
  h1.trans h2

end SelStep2Hist

/-! ## The removal of the redundant dotted edges after `O_merge` -/

section SelStep2Clean

variable {k : ℕ}

theorem selStep2_excL_eq {n : ℕ} (L : List (Comp (Atom k n))) : excL L = step3_eL L := by
  unfold excL nBlk nDotL step3_eL step3_nD
  congr 2
  unfold SimpleGraph.ConnectedComponent
  have : (step3_dg L).Reachable = Relation.EqvGen (dotRel L) := by
    funext u v
    exact propext (Graph.sameBlock_iff_eqvGen (⟨L, 1⟩ : Graph k n) u v)
  rw [this]

theorem selStep2_dotExcess_eq {n : ℕ} (g : Graph k n) : g.dotExcess = excL g.comps := by
  rw [selStep2_excL_eq]; rfl

theorem selStep2_firstRed_some {n : ℕ} {L : List (Comp (Atom k n))} {i : ℕ}
    (h : selStep3_firstRed L = some i) :
    ∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step3_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep3_firstRed at h
  simpa using List.find?_some h

theorem selStep2_firstRed_none {n : ℕ} {L : List (Comp (Atom k n))}
    (h : selStep3_firstRed L = none) {i : ℕ} {c : Comp (Atom k n)} (hc : L[i]? = some c)
    (hk : c.kind = .dot) : ¬ (step3_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep3_firstRed at h
  rw [List.find?_eq_none] at h
  intro hr
  have hi : i < L.length := (List.getElem?_eq_some_iff.1 hc).1
  exact h i (List.mem_range.2 hi) (by simpa using ⟨c, hc, hk, hr⟩)

/-- `r` removals of the first redundant dotted edge, when the dot excess is `T + r`: the dot
excess becomes `T`, the components other than dotted edges, the blocks and the value are kept,
and the scaling order drops by `2 r`. -/
theorem selStep2_drop_spec (m : ℕ) : ∀ {n : ℕ} (g : Graph k n) (T : ℤ), 0 ≤ T →
    excL g.comps = T + m → (∀ c ∈ g.comps, c.kind = .dot → c.label = none) →
    Relation.ReflTransGen SelStep3Drop g (selStep3_drop m g) ∧
      excL (selStep3_drop m g).comps = T ∧
      (selStep3_drop m g).coeff = g.coeff ∧ (selStep3_drop m g).comps.Sublist g.comps ∧
      ((selStep3_drop m g).comps.filter fun c => decide (c.kind ≠ .dot)).Perm
        (g.comps.filter fun c => decide (c.kind ≠ .dot)) ∧
      (∀ u v, (selStep3_drop m g).SameBlock u v ↔ g.SameBlock u v) ∧
      (selStep3_drop m g).ord = g.ord - 2 * m ∧
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), (selStep3_drop m g).valR PF D e = g.valR PF D e) := by
  induction m with
  | zero =>
    intro n g T _ hT _
    exact ⟨Relation.ReflTransGen.refl, by simpa [selStep3_drop] using hT, rfl, List.Sublist.refl _,
      List.Perm.refl _, fun _ _ => Iff.rfl, by simp [selStep3_drop], fun _ _ _ _ _ _ _ => rfl⟩
  | succ m ih =>
    intro n g T hT0 hT hlab
    have hpos : 0 < step3_eL g.comps := by
      rw [← selStep2_excL_eq, hT]; push_cast; linarith
    obtain ⟨i₀, c₀, hc₀, hk₀, hr₀⟩ := step3_exists_red_of_pos hpos
    obtain ⟨i, hi⟩ : ∃ i, selStep3_firstRed g.comps = some i := by
      rcases h' : selStep3_firstRed g.comps with _ | i
      · exact absurd hr₀ (selStep2_firstRed_none h' hc₀ hk₀)
      · exact ⟨i, rfl⟩
    obtain ⟨c, hc, hk, hr⟩ := selStep2_firstRed_some hi
    have hdrop : selStep3_drop (m + 1) g = selStep3_drop m ⟨g.comps.eraseIdx i, g.coeff⟩ := by
      simp only [selStep3_drop, hi]
    rw [hdrop]
    set g₁ : Graph k n := ⟨g.comps.eraseIdx i, g.coeff⟩ with hg₁
    obtain ⟨-, he, hord₁, -, hfp, hbl₁, -⟩ := step3_drop_one g hc hk hr
    have hex : excL g₁.comps = T + m := by
      rw [selStep2_excL_eq] at hT ⊢
      have : step3_eL g₁.comps + 1 = step3_eL g.comps := he
      push_cast at hT; linarith
    have hlab₁ : ∀ d ∈ g₁.comps, d.kind = .dot → d.label = none :=
      fun d hd hdk => hlab d (List.mem_of_mem_eraseIdx hd) hdk
    obtain ⟨hch, hex', hco, hsub, hfil, hbl, hord, hval⟩ := ih g₁ T hT0 hex hlab₁
    refine ⟨Relation.ReflTransGen.head ⟨i, c, hc, hk, hr, rfl⟩ hch, hex', hco,
      hsub.trans (List.eraseIdx_sublist _ _), hfil.trans ?_, fun u v => (hbl u v).trans (hbl₁ u v),
      ?_, ?_⟩
    · have : (fun c : Comp (Atom k n) => decide (c.kind ≠ .dot)) =
          fun d => !decide (d.kind = .dot) := by funext d; simp
      rw [this]; exact hfp
    · rw [hord]; push_cast; linarith
    · intro Ω ι _ _ PF D e
      rw [hval]
      exact step1_dropDot_value g hc hk hr hlab Ω ι PF D e

/-- `O_merge` followed by the removal of the first redundant dotted edge until the dot excess is
that of the input; `none` when `O_merge` gives `0`. -/
def selStep2_clean {n : ℕ} (h : Graph k n) : Option (Tracked k n) :=
  match h.mergeT with
  | some t => some ⟨t.nOut, selStep3_drop (excL t.g.comps - excL h.comps).toNat t.g, t.f⟩
  | none => none

theorem selStep2_clean_none {n : ℕ} {h : Graph k n} (hm : h.mergeT = none) :
    selStep2_clean h = none := by
  simp [selStep2_clean, hm]

/-- `O_merge` followed by the removal of the redundant dotted edges (the first redundant dotted edge
is removed at each step): the clauses for the output of `selStep2_clean`, and its history. -/
theorem selStep2_clean_spec {n : ℕ} (h : Graph k n) (t : Tracked k n) (hm : h.mergeT = some t)
    (hlab : ∀ c ∈ h.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
    (hl1 : h.labels.length ≤ 1)
    (hRr : ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ) ≤
      (n : ℤ) - t.nOut) :
    ∃ g' : Graph k t.nOut, selStep2_clean h = some ⟨t.nOut, g', t.f⟩ ∧
      Relation.ReflTransGen SelStep3Drop t.g g' ∧
      Relation.ReflTransGen QElemStep ⟨n, h⟩ ⟨t.nOut, g'⟩ ∧
      excL g'.comps = excL h.comps ∧ g'.coeff = h.coeff ∧ g'.comps.Sublist t.g.comps ∧
      (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
        (t.g.comps.filter fun c => decide (c.kind ≠ .dot)) ∧
      (∀ u v, g'.SameBlock u v ↔ t.g.SameBlock u v) ∧
      g'.ord = h.ord - ((h.comps.filter fun c => c.kind.isSolid &&
        h.psteps_mrep c.x == h.psteps_mrep c.y).length : ℤ) ∧
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), g'.valR PF D e = h.valR PF D e) := by
  have hs := psteps_mergeT_spec hm
  have hle := hs.nOut_le
  set R : ℤ := ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ)
  set m : ℕ := (n - t.nOut) - (h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length
  have hex := hs.excL_eq
  have hT0 := (excL_spec h.comps).1
  have hmT : excL t.g.comps = excL h.comps + m := by
    rw [hex]
    have : (m : ℤ) = ((n : ℤ) - t.nOut) - R := by
      simp only [m, R]
      push_cast [Nat.cast_sub hle]
      have : ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ) ≤
          (n : ℤ) - t.nOut := hRr
      omega
    rw [this]; ring
  have hlabt : ∀ c ∈ t.g.comps, c.kind = .dot → c.label = none :=
    fun c hc hk => hs.hlab hlab c hc (Or.inl hk)
  have hr : (excL t.g.comps - excL h.comps).toNat = m := by
    rw [hmT]; simp
  obtain ⟨hdr, hex', hco, hsub, hfil, hbl, hord, hval⟩ :=
    selStep2_drop_spec m t.g (excL h.comps) hT0 hmT hlabt
  have hstep : QElemStep ⟨n, h⟩ ⟨t.nOut, t.g⟩ := QElemStep.merge h t hm
  refine ⟨selStep3_drop m t.g, by simp [selStep2_clean, hm, hr], hdr,
    Relation.ReflTransGen.head hstep (SelStep3Drop.chain hdr), hex', hco.trans hs.coeff_eq, hsub,
    hfil, hbl, ?_, ?_⟩
  · rw [hord, hs.ord_eq]
    simp only [m]
    push_cast [Nat.cast_sub hle]
    have : ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ) ≤
        (n : ℤ) - t.nOut := hRr
    rw [Nat.cast_sub (by omega)]
    push_cast [Nat.cast_sub hle]
    ring
  · intro Ω ι _ _ PF D e
    rw [hval]
    have := oMerge_value k n h hl1 hlab Ω ι PF D e
    rw [hm] at this
    exact this

end SelStep2Clean

/-! ## The identification of two blocks -/

section SelStep2Ident

variable {k n : ℕ}

/-- The identification of the blocks of `u` and `v`: a dotted edge `u – v` added to `g` (with
coefficient `co`), then `O_merge` and the removal of the first redundant dotted edges. -/
def selStep2_ident (g : Graph k n) (u v : Atom k n) (co : Coeff) : Option (Tracked k n) :=
  selStep2_clean ⟨g.comps ++ [mkC .dot u v], co⟩

/-- The identification of the blocks of `u` and `v` (the output of `selStep2_ident`): the term vanishes, or its output has the clauses `IdOut`, keeps the components
at the external atoms other than `u`, `v`, and has a history. -/
theorem selStep2_ident_spec {C : ℕ} {x : Atom k n} {g : Graph k n} (hN : NN C x g)
    {u v : Atom k n} (huv : ¬ g.SameBlock u v) (co : Coeff) :
    (selStep2_ident g u v co = none ∧
      ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), (⟨g.comps ++ [mkC .dot u v], co⟩ : Graph k n).valR PF D e = 0) ∨
    ∃ t : Tracked k n, selStep2_ident g u v co = some t ∧ IdOut C x g u v co t ∧
      (∀ o, ODiff o g → u ≠ .inl o → v ≠ .inl o → OOut o g t) ∧
      SelStep2Hist (⟨g.comps ++ [mkC .dot u v], co⟩ : Graph k n) t ∧
      (∀ o, t.f (.inl o) = .inl o) := by
  set h' : Graph k n := ⟨g.comps ++ [mkC .dot u v], co⟩ with hh'
  have hSB : ∀ a b, h'.SameBlock a b ↔ g.SameBlock a b ∨
      (g.SameBlock a u ∧ g.SameBlock v b) ∨ (g.SameBlock a v ∧ g.SameBlock u b) :=
    sameBlock_append_dot g u v co
  have hSBg : ∀ a b, g.SameBlock a b → h'.SameBlock a b := fun a b h => (hSB a b).2 (Or.inl h)
  have hmem : ∀ c, c ∈ h'.comps ↔ c ∈ g.comps ∨ c = mkC .dot u v := by
    intro c; simp [hh']
  have hlabd : ∀ c ∈ h'.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
    intro c hc hk
    rcases (hmem c).1 hc with hc | rfl
    · by_contra hne
      have := (hN.plain c hc).2.2.2.2.2 (Option.isSome_iff_ne_none.2 hne)
      rcases hk with hk | hk <;> rw [hk] at this <;> simp [Kind.isRandom] at this
    · rfl
  have hlab : ∀ c ∈ h'.comps, c.label = none ∨ c.label = some (.P, x) := by
    intro c hc
    rcases (hmem c).1 hc with hc | rfl
    · exact hN.lab c hc
    · exact Or.inl rfl
  have hl1 : h'.labels.length ≤ 1 := labels_le_one h' (.P, x) hlab
  rcases hm : h'.mergeT with _ | t₀
  · left
    refine ⟨selStep2_clean_none hm, ?_⟩
    intro Ω ι _ _ PF D e
    have := oMerge_value k n h' hl1 hlabd Ω ι PF D e
    rw [hm] at this
    exact this
  right
  have hs := psteps_mergeT_spec hm
  -- at most the new dotted edge has identified ends
  have hold : ∀ c ∈ g.comps, c.kind = .dot → t₀.f c.x ≠ t₀.f c.y := by
    intro c hc hk
    have hne : c.x ≠ c.y := (hN.plain c hc).2.2.2.1 hk
    have hext := hN.reg.noIntDot c hc hk
    intro hf
    rcases hx : c.x with a | i <;> rcases hy : c.y with b | j
    · rw [hx, hy, hs.f_inl, hs.f_inl] at hf
      exact hne (by rw [hx, hy, Sum.inl.inj hf])
    · obtain ⟨j', hj'⟩ := hs.f_inr' j
      rw [hx, hy, hs.f_inl, hj'] at hf; cases hf
    · obtain ⟨i', hi'⟩ := hs.f_inr' i
      rw [hx, hy, hs.f_inl, hi'] at hf; cases hf
    · rw [hx, hy] at hext; simp at hext
  have hRr : ((h'.comps.filter fun c => c.kind == .dot && t₀.f c.x == t₀.f c.y).length : ℤ) ≤
      (n : ℤ) - t₀.nOut := by
    have hle := hs.nOut_le
    have hfil : h'.comps.filter (fun c => c.kind == .dot && t₀.f c.x == t₀.f c.y) =
        if t₀.f u = t₀.f v then [mkC .dot u v] else [] := by
      simp only [hh']
      rw [List.filter_append, List.filter_eq_nil_iff.2 (fun c hc => by
        by_cases hk : c.kind = .dot
        · simp [hk, hold c hc hk]
        · simp [hk])]
      by_cases hf : t₀.f u = t₀.f v
      · simp [hf, mkC]
      · simp [hf, mkC]
    rw [hfil]
    split_ifs with hf
    · simp only [List.length_singleton, Nat.cast_one]
      rcases hu : u with a | i
      · exfalso
        rw [hu, hs.f_inl] at hf
        rcases hv : v with b | j
        · rw [hv, hs.f_inl] at hf
          exact huv (by rw [hu, hv, Sum.inl.inj hf]; exact Graph.sameBlock_refl _ _)
        · obtain ⟨j', hj'⟩ := hs.f_inr' j
          rw [hv, hj'] at hf; cases hf
      · rcases hv : v with b | j
        · exfalso
          obtain ⟨i', hi'⟩ := hs.f_inr' i
          rw [hu, hi', hv, hs.f_inl] at hf; cases hf
        · have hij : i ≠ j := by
            rintro rfl; exact huv (by rw [hu, hv]; exact Graph.sameBlock_refl _ _)
          have hr : h'.psteps_mrep (.inr i) = h'.psteps_mrep (.inr j) := by
            rw [← hu, ← hv]
            exact h'.mrep_dot (c := mkC .dot u v) (by simp [hh']) rfl
          have := hs.r_one hij hr
          omega
    · simp only [List.length_nil, Nat.cast_zero]
      omega
  obtain ⟨g', hsel, hdr, hch, hex, hco, hsub, hnd, hbl, hord, hval⟩ :=
    selStep2_clean_spec h' t₀ hm hlabd hl1 hRr
  have hag : Agree g' t₀.g := Agree.of_cleanup hsub hnd hbl
  -- the identified solid edges
  have hconv : (h'.comps.filter fun c => c.kind.isSolid && h'.psteps_mrep c.x == h'.psteps_mrep c.y).length =
      g.nBetween u v := by
    classical
    unfold Graph.nBetween Graph.unpart
    simp only [hh']
    rw [List.filter_append, List.filter_cons_of_neg (by simp [mkC, Kind.isSolid]), List.filter_nil,
      List.append_nil, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro c hc
    have key : (c.kind.isSolid = true ∧ h'.psteps_mrep c.x = h'.psteps_mrep c.y) ↔
        (((g.SameBlock c.x u ∧ g.SameBlock c.y v) ∨ (g.SameBlock c.x v ∧ g.SameBlock c.y u)) ∧
          c.kind.isSolid = true ∧ g.partB c = false) := by
      constructor
      · rintro ⟨hsol, hr⟩
        have hsb : h'.SameBlock c.x c.y := (Graph.sameBlock_iff_mrep _ _ _).2 hr
        refine ⟨?_, hsol, ?_⟩
        · rcases (hSB c.x c.y).1 hsb with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h0 (hN.inBlk c hc hsol)
          · exact Or.inl ⟨h1, Graph.sameBlock_symm h2⟩
          · exact Or.inr ⟨h1, Graph.sameBlock_symm h2⟩
        · by_contra hp
          have hp' : g.partB c = true := by simpa using hp
          obtain ⟨d, hd, hdk, hdp⟩ := (g.partB_iff c).1 hp'
          have hdm : d ∈ h'.comps := by simp [hh', hd]
          apply hs.xdot_ne d hdm hdk
          rw [← Graph.sameBlock_iff_mrep]
          rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hsb
          · rw [h1, h2]; exact Graph.sameBlock_symm hsb
      · rintro ⟨hb, hsol, -⟩
        refine ⟨hsol, (Graph.sameBlock_iff_mrep _ _ _).1 ?_⟩
        rw [hSB]
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, Graph.sameBlock_symm h2⟩)
        · exact Or.inr (Or.inr ⟨h1, Graph.sameBlock_symm h2⟩)
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true']
    exact key
  -- basic facts about `h'`
  have hne : u ≠ v := fun he => huv (by rw [he]; exact Graph.sameBlock_refl _ _)
  have hpl' : h'.Plain := by
    intro c hc
    rcases (hmem c).1 hc with hc | rfl
    · exact hN.plain c hc
    · refine ⟨rfl, by simp [mkC], by simp [mkC], fun _ => hne, by simp [mkC, Kind.isWeight], ?_⟩
      simp [mkC]
  have hpartB' : ∀ c, h'.partB c = g.partB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.partB_iff, Graph.partB_iff]
    constructor
    · rintro ⟨d, hd, hk, hp⟩
      rcases (hmem d).1 hd with hd | rfl
      · exact ⟨d, hd, hk, hp⟩
      · simp [mkC] at hk
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hmem d).2 (Or.inl hd), hk, hp⟩
  have hsolidB' : ∀ c, h'.solidB c = g.solidB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.solidB_iff, Graph.solidB_iff]
    constructor
    · rintro ⟨d, hd, hk, hp⟩
      rcases (hmem d).1 hd with hd | rfl
      · exact ⟨d, hd, hk, hp⟩
      · simp [mkC, Kind.isSolid] at hk
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hmem d).2 (Or.inl hd), hk, hp⟩
  have hunp' : h'.unpart = g.unpart := by
    unfold Graph.unpart
    simp only [hh']
    rw [List.filter_append, List.filter_cons_of_neg (by simp [mkC, Kind.isSolid]), List.filter_nil,
      List.append_nil]
    apply List.filter_congr
    intro c _
    rw [hpartB']
  have horph' : h'.orph = g.orph := by
    unfold Graph.orph
    simp only [hh']
    rw [List.filter_append, List.filter_cons_of_neg (by simp [mkC]), List.filter_nil,
      List.append_nil]
    apply List.filter_congr
    intro c _
    rw [hsolidB']
  -- unlabelled solid edges are not inside a block of `h'`
  have hsolU : ∀ c ∈ h'.comps, c.label = none → c.kind.isSolid = true →
      ¬ h'.SameBlock c.x c.y := by
    intro c hc hl hsol hsb
    rcases (hmem c).1 hc with hc | rfl
    · have hp : g.partB c = true := by
        by_contra hp
        have := hN.unpLab c (Graph.mem_unpart.2 ⟨hc, hsol, by simpa using hp⟩)
        rw [hl] at this; cases this
      obtain ⟨d, hd, hdk, hdp⟩ := (g.partB_iff c).1 hp
      apply hs.xdot_ne d ((hmem d).2 (Or.inl hd)) hdk
      rw [← Graph.sameBlock_iff_mrep]
      rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hsb
      · rw [h1, h2]; exact Graph.sameBlock_symm hsb
    · simp [mkC, Kind.isSolid] at hsol
  -- the components of `t₀` without `×`-dotted partner come from such components of `h'`
  have hU : t₀.g.unpart.length + g.nBetween u v ≤ g.unpart.length := by
    rw [← hconv, ← hunp']
    unfold Graph.unpart
    rw [hs.comps_eq]
    apply count_filterMap
    · intro c hc c' hm hP
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hP
      obtain ⟨hsol', hpart'⟩ := hP
      rcases mergeComp_y hm with ⟨hy, hk⟩ | ⟨hsol, hr, -, hk⟩
      · rw [hk] at hsol'
        have hrne : h'.psteps_mrep c.x ≠ h'.psteps_mrep c.y := by
          intro hr
          rw [psteps_mergeComp_solid hsol', if_pos hr] at hm
          obtain rfl := Option.some.inj hm
          obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hsol'
          simp [hch, Kind.toWeight] at hk
        have hc' : c' = c.map t₀.f := by
          rw [psteps_mergeComp_solid hsol', if_neg hrne] at hm; exact (Option.some.inj hm).symm
        refine ⟨?_, by simp [hrne]⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨hsol', ?_⟩
        by_contra hp
        obtain ⟨d, hd, hdk, hdp⟩ := (h'.partB_iff c).1 (by simpa using hp)
        have : t₀.g.partB c' = true := by
          refine (t₀.g.partB_iff c').2 ⟨d.map t₀.f, hs.mem_of_other hd (by rw [hdk]; simp)
            (by rw [hdk]; rfl), hdk, ?_⟩
          rw [hc']
          rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
          · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
        rw [this] at hpart'; cases hpart'
      · obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hsol
        rw [hk, hch] at hsol'; simp [Kind.toWeight, Kind.isSolid] at hsol'
    · intro c hc hR
      simp only [Bool.and_eq_true, beq_iff_eq] at hR
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨hR.1, ?_⟩
      by_contra hp
      obtain ⟨d, hd, hdk, hdp⟩ := (h'.partB_iff c).1 (by simpa using hp)
      apply hs.xdot_ne d hd hdk
      rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hR.2
      · rw [h1, h2]; exact hR.2.symm
  have hO : t₀.g.orph.length ≤ g.orph.length := by
    rw [← horph']
    have := count_filterMap h'.comps (psteps_mergeComp h'.psteps_mrep t₀.f)
      (fun c => c.kind == .xdot && !t₀.g.solidB c) (fun c => c.kind == .xdot && !h'.solidB c)
      (fun _ => false) (by
        intro c hc c' hm hP
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hP
        obtain ⟨hk', hsb'⟩ := hP
        have hk : c.kind = .xdot := by
          rcases psteps_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
          · rw [← h]; exact hk'
          · rw [hch'] at hk'; cases hk'
        have hc' : c' = c.map t₀.f := by
          rw [mergeComp_other (by rw [hk]; simp) (by rw [hk]; rfl)] at hm
          exact (Option.some.inj hm).symm
        refine ⟨?_, rfl⟩
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
        refine ⟨hk, ?_⟩
        by_contra hsb
        obtain ⟨d, hd, hdk, hdp⟩ := (h'.solidB_iff c).1 (by simpa using hsb)
        have hrne : h'.psteps_mrep d.x ≠ h'.psteps_mrep d.y := by
          intro hr
          apply hs.xdot_ne c hc hk
          rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]; exact hr
          · rw [← h1, ← h2]; exact hr.symm
        have : t₀.g.solidB c' = true := by
          refine (t₀.g.solidB_iff c').2 ⟨d.map t₀.f, hs.mem_of_solid hd hdk hrne, hdk, ?_⟩
          rw [hc']
          rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
          · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
        rw [this] at hsb'; cases hsb')
      (by intro c _ h; cases h)
    rw [← hs.comps_eq] at this
    unfold Graph.orph
    simpa using this
  -- the facts about `t₀`
  have hlen₀ : t₀.g.comps.length ≤ g.comps.length + 1 := by
    rw [hs.comps_eq]
    refine (List.length_filterMap_le _ _).trans ?_
    simp [hh']
  have hcx' : h'.ConnNoX := by
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
    intro p q hpq
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne', ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inl ⟨c, (hmem c).2 (Or.inl hc), hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inr ⟨c, (hmem c).2 (Or.inl hc), hk, h1, h2⟩⟩
  have hint' : ∀ a b : Fin n, h'.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.reg.internal a b)
    intro p q hpq
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne', ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inl ⟨c, (hmem c).2 (Or.inl hc), hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inr ⟨c, (hmem c).2 (Or.inl hc), hk, h1, h2⟩⟩
  have hcx₀ : t₀.g.ConnNoX := hs.connNoX hcx'
  have hreg₀ : t₀.g.Regular (C + 1) := by
    refine ⟨?_, ConnNoX.connected hcx₀, hs.internal hint', hs.noIntDot⟩
    have := hN.reg.size
    have := hs.nOut_le
    omega
  have hunpimg : ∀ c' ∈ t₀.g.unpart, ∃ c ∈ g.unpart, c' = c.map t₀.f := by
    intro c' hc'
    obtain ⟨hc'm, hsol', hp'⟩ := Graph.mem_unpart.1 hc'
    obtain ⟨c, hc, hsol, hrne, rfl⟩ := hs.of_mem_solid hc'm hsol'
    refine ⟨c, ?_, rfl⟩
    rw [← hunp']
    refine Graph.mem_unpart.2 ⟨hc, hsol, ?_⟩
    by_contra hp
    obtain ⟨d, hd, hdk, hdp⟩ := (h'.partB_iff c).1 (by simpa using hp)
    have : t₀.g.partB (c.map t₀.f) = true := by
      refine (t₀.g.partB_iff _).2 ⟨d.map t₀.f, hs.mem_of_other hd (by rw [hdk]; simp)
        (by rw [hdk]; rfl), hdk, ?_⟩
      rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
      · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
    rw [this] at hp'; cases hp'
  have hNN : NN (C + 1) (t₀.f x) g' := by
    refine hag.nn (hsub.length_le) (by rw [hs.isRight_f]; exact hN.hx) hreg₀ hcx₀ hs.solid_ne
      (hs.plain hpl') (hs.labels hlab) hs.xdotApart hs.ib hs.inBlk ?_ ?_
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := hunpimg c' hc'
      have := hN.unpLab c hc
      simpa [Comp.map] using this
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := hunpimg c' hc'
      rcases hN.unpInt c hc with h | h
      · left; simp only [Comp.map]; rw [hs.isRight_f]; exact h
      · right; simp only [Comp.map]; rw [hs.isRight_f]; exact h
  -- the environment is carried
  have henvh : (h'.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
      c.kind ≠ .xdot)) = g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
      c.kind ≠ .xdot) := by
    simp only [hh']
    rw [List.filter_append, List.filter_cons_of_neg (by simp [mkC]), List.filter_nil,
      List.append_nil]
  have hcarS : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
      c.kind ≠ .xdot)).map (Comp.map t₀.f)).Subperm g'.comps := by
    have h1 := hs.carries_sub hsolU
    rw [henvh] at h1
    have h2 : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
        c.kind ≠ .xdot)).map (Comp.map t₀.f)).Subperm
          (t₀.g.comps.filter fun c => decide (c.kind ≠ .dot)) := by
      refine subperm_filter_of_forall h1.subperm _ ?_
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have := (List.mem_filter.1 hd).2
      simp only [decide_eq_true_eq] at this
      simp only [Comp.map]
      exact decide_eq_true this.2.1
    exact (h2.trans hnd.symm.subperm).trans List.filter_sublist.subperm
  have hblk : ∀ a b, g'.SameBlock (t₀.f a) (t₀.f b) ↔ h'.SameBlock a b := by
    intro a b; rw [hbl, hs.sameBlock_iff]
  refine ⟨⟨t₀.nOut, g', t₀.f⟩, hsel, ?_, fun o hO hu hv => merge_oout hs hO
    (OKeep.append (List.Perm.refl _) _ (fun d hd => by
      rw [List.mem_singleton.1 hd]; simp [atO, mkC, hu, hv]) co) hsub hnd,
    (SelStep2Hist.single (SelStep2Step.merge h' t₀ hm)).trans (SelStep2Hist.of_drops hdr),
    hs.f_inl⟩
  refine ⟨hch, hNN, ?_, ?_, ?_, ?_, hco, ⟨hcarS, fun a b hab =>
    (hblk a b).2 (hSBg a b hab)⟩, ?_, hs.f_surj, hval, ?_, hblk, hsub.length_le.trans hlen₀⟩
  · simp only
    rw [hag.unpart.length_eq]; exact hU
  · simp only
    rw [hag.orph.length_eq]; exact hO
  · simp only
    rw [hord, ← hconv]
    have : h'.ord = g.ord + 2 := by
      simp [Graph.ord, hh', mkC, Kind.ord]; ring
    rw [this]; ring
  · simp only
    rw [hex, hh']
    exact excL_append_dot_out g.comps u v (by rwa [← Graph.sameBlock_iff_eqvGen])
  · intro hdc
    refine dc_transfer t₀.f hN.plain.labRand hs.f_inr' ?_ ?_ hcarS ?_ hdc
    · have key : ∀ p q, Relation.EqvGen (fun u v => ∃ c ∈ g.comps, c.kind.joinsMol = true ∧
          c.x = u ∧ c.y = v) p q → Relation.EqvGen (fun u v => ∃ c ∈ g'.comps,
            c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) (t₀.f p) (t₀.f q) := by
        intro p q hr
        induction hr with
        | rel p q hpq =>
          obtain ⟨c, hc, hj, rfl, rfl⟩ := hpq
          by_cases hd : c.kind = .dot
          · have hb' := (hblk c.x c.y).2 (hSBg _ _ (Graph.sameBlock_of_dot hc hd))
            rw [Graph.sameBlock_iff_eqvGen] at hb'
            refine Relation.EqvGen.mono ?_ _ _ hb'
            rintro p q ⟨d, hd', hdk, rfl, rfl⟩
            exact ⟨d, hd', by rw [hdk]; rfl, rfl, rfl⟩
          · have hl : c.label = none := by
              by_contra hne'
              have := hN.plain.labRand c hc (Option.isSome_iff_ne_none.2 hne')
              rw [Kind.not_joinsMol_of_isRandom this] at hj; cases hj
            have hnx : c.kind ≠ .xdot := by intro h; rw [h] at hj; simp [Kind.joinsMol] at hj
            have hmemc : c.map t₀.f ∈ g'.comps :=
              hcarS.subset (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl, hd, hnx]⟩, rfl⟩)
            exact Relation.EqvGen.rel _ _ ⟨c.map t₀.f, hmemc, hj, rfl, rfl⟩
        | refl p => exact Relation.EqvGen.refl _
        | symm p q _ ih => exact ih.symm
        | trans p q r _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
      intro a b ha hb hab
      rcases hab with rfl | ⟨-, -, hr⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨by rw [hs.isRight_f]; exact ha, by rw [hs.isRight_f]; exact hb, ?_⟩
        unfold Graph.molGraph at hr ⊢
        rw [reachable_fromRel_iff] at hr ⊢
        exact key _ _ hr
    · intro j
      obtain ⟨i, hi⟩ := hs.surj_inr j
      exact ⟨i, Or.inl hi.symm⟩
    · intro c hc hk a b a' b' hx' hy' ha hb
      by_cases hsb : h'.SameBlock c.x c.y
      · have := (hblk c.x c.y).2 hsb
        rw [hx', hy', ha, hb] at this
        have hab := hNN.ib a' b' this
        subst hab
        exact Relation.EqvGen.refl _
      · have hsol : c.kind.isSolid = true := by rw [hk]; rfl
        have hm : psteps_mergeComp h'.psteps_mrep t₀.f c = some (c.map t₀.f) :=
          mergeComp_of_solid hsol (fun hr => hsb ((Graph.sameBlock_iff_mrep _ _ _).2 hr))
        have hm₀ : c.map t₀.f ∈ t₀.g.comps := hs.mem_comps.2 ⟨c, (hmem c).2 (Or.inl hc), hm⟩
        have hkd : (c.map t₀.f).kind ≠ .dot := by simp [Comp.map, hk]
        have hm' : c.map t₀.f ∈ g'.comps := (hag.mem_nd hkd).2 hm₀
        refine Relation.EqvGen.rel _ _ (Or.inr ⟨c.map t₀.f, hm', hk, ?_, ?_⟩)
        · simp [Comp.map, hx', ha]
        · simp [Comp.map, hy', hb]
  · intro hH
    simp only
    rw [hag.pw]
    have hident : ∀ c : Comp (Atom k n), ((g.SameBlock c.x u ∧ g.SameBlock c.y v) ∨
        (g.SameBlock c.x v ∧ g.SameBlock c.y u)) → h'.SameBlock c.x c.y := by
      intro c hc
      rw [hSB]
      rcases hc with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inr (Or.inl ⟨h3, Graph.sameBlock_symm h4⟩)
      · exact Or.inr (Or.inr ⟨h3, Graph.sameBlock_symm h4⟩)
    -- the block of `x` in `h'` at the ends of the labelled components that are not identified
    have hBx : ∀ c ∈ g.comps, c.label.isSome = true →
        (c.kind.isSolid = true → ¬ h'.SameBlock c.x c.y) →
        ∀ a, (a = c.x ∨ a = c.y) → (h'.SameBlock a x ↔ g.SameBlock a x) := by
      intro c hc hl hnc a ha
      have htouch : ∀ b, g.SameBlock a b → (g.SameBlock c.x b ∨ g.SameBlock c.y b) := by
        intro b hab
        rcases ha with rfl | rfl
        · exact Or.inl hab
        · exact Or.inr hab
      rw [hSB]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h
        · exfalso
          rcases hH with ⟨-, hvx⟩ | ⟨hux, -⟩ | ⟨-, hL⟩
          · exact hvx h2
          · exact huv (hux.trans (Graph.sameBlock_symm h2))
          · obtain ⟨hcs, hcb⟩ := hL c hc hl (htouch u h1)
            exact hnc hcs (hident c hcb)
        · exfalso
          rcases hH with ⟨hux, -⟩ | ⟨-, hL⟩ | ⟨hvx, -⟩
          · exact hux h2
          · obtain ⟨hcs, hcb⟩ := hL c hc hl (htouch v h1)
            exact hnc hcs (hident c hcb.symm)
          · exact huv (h2.trans (Graph.sameBlock_symm hvx))
      · exact fun h => Or.inl h
    unfold Graph.pw
    rw [hs.comps_eq]
    have key := sum_filterMap h'.comps (psteps_mergeComp h'.psteps_mrep t₀.f)
      (wBP fun a => g.SameBlock a x) (wBP fun a' => t₀.g.SameBlock a' (t₀.f x)) (fun _ => 0) (by
        intro c hc
        simp only [add_zero]
        rcases hφ : psteps_mergeComp h'.psteps_mrep t₀.f c with _ | c'
        · obtain ⟨hk, -⟩ := mergeComp_none hφ
          simp [wBP, hk]
        · simp only [Option.elim_some]
          have hl := mergeComp_label hφ
          obtain ⟨hx', -⟩ := mergeComp_x hφ
          by_cases hcl : c.label.isSome = true
          · have hcg : c ∈ g.comps := by
              rcases (hmem c).1 hc with h | rfl
              · exact h
              · simp [mkC] at hcl
            rcases mergeComp_y hφ with ⟨hy', hk'⟩ | ⟨hsol, hr, hy', hk'⟩
            · -- not identified
              have hnc : c.kind.isSolid = true → ¬ h'.SameBlock c.x c.y := by
                intro hsol hb
                rw [psteps_mergeComp_solid hsol, if_pos ((Graph.sameBlock_iff_mrep _ _ _).1 hb)] at hφ
                obtain rfl := Option.some.inj hφ
                obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hsol
                simp [hch, Kind.toWeight] at hk'
              have e1 : ∀ a, (a = c.x ∨ a = c.y) →
                  (t₀.g.SameBlock (t₀.f a) (t₀.f x) ↔ g.SameBlock a x) := fun a ha =>
                (hs.sameBlock_iff a x).trans (hBx c hcg hcl hnc a ha)
              exact wBP_congr (c := c) (c' := c') (by rw [hl]; simp) hk'
                (by rw [hx']; exact e1 c.x (Or.inl rfl)) (by rw [hy']; exact e1 c.y (Or.inr rfl))
            · -- identified: an edge between the two blocks
              obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hsol
              have hsb : h'.SameBlock c.x c.y := (Graph.sameBlock_iff_mrep _ _ _).2 hr
              have hnb := hN.inBlk c hcg hsol
              have hbtw : (g.SameBlock c.x u ∧ g.SameBlock c.y v) ∨
                  (g.SameBlock c.x v ∧ g.SameBlock c.y u) := by
                rcases (hSB c.x c.y).1 hsb with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact absurd h0 hnb
                · exact Or.inl ⟨h1, Graph.sameBlock_symm h2⟩
                · exact Or.inr ⟨h1, Graph.sameBlock_symm h2⟩
              have hA : t₀.g.SameBlock c'.x (t₀.f x) ↔ (g.SameBlock c.x x ∨ g.SameBlock c.y x) := by
                rw [hx', hs.sameBlock_iff, hSB]
                rcases hH with ⟨hux, hvx⟩ | ⟨hux, -⟩ | ⟨hvx, -⟩
                · constructor
                  · rintro (h | ⟨-, h2⟩ | ⟨-, h2⟩)
                    · exact Or.inl h
                    · exact absurd h2 hvx
                    · exact absurd h2 hux
                  · rintro (h | h)
                    · exact Or.inl h
                    · exfalso
                      rcases hbtw with ⟨-, h2⟩ | ⟨-, h2⟩
                      · exact hvx ((Graph.sameBlock_symm h2).trans h)
                      · exact hux ((Graph.sameBlock_symm h2).trans h)
                · constructor
                  · intro _
                    rcases hbtw with ⟨h1, -⟩ | ⟨-, h2⟩
                    · exact Or.inl (h1.trans hux)
                    · exact Or.inr (h2.trans hux)
                  · intro _
                    rcases hbtw with ⟨h1, -⟩ | ⟨h1, -⟩
                    · exact Or.inl (h1.trans hux)
                    · exact Or.inr (Or.inr ⟨h1, hux⟩)
                · constructor
                  · intro _
                    rcases hbtw with ⟨-, h2⟩ | ⟨h1, -⟩
                    · exact Or.inr (h2.trans hvx)
                    · exact Or.inl (h1.trans hvx)
                  · intro _
                    rcases hbtw with ⟨h1, -⟩ | ⟨h1, -⟩
                    · exact Or.inr (Or.inl ⟨h1, hvx⟩)
                    · exact Or.inl (h1.trans hvx)
              have hnot2 : ¬ (g.SameBlock c.x x ∧ g.SameBlock c.y x) := fun ⟨h1, h2⟩ =>
                hnb (h1.trans (Graph.sameBlock_symm h2))
              unfold wBP
              rw [hl, hk', hch]
              simp only [Option.isSome_map, hcl, ite_true, Kind.toWeight]
              by_cases h1 : g.SameBlock c.x x <;> by_cases h2 : g.SameBlock c.y x
              · exact absurd ⟨h1, h2⟩ hnot2
              · rw [if_pos (hA.2 (Or.inl h1)), if_pos h1, if_neg h2]
              · rw [if_pos (hA.2 (Or.inr h2)), if_neg h1, if_pos h2]
              · rw [if_neg (fun h => (hA.1 h).elim h1 h2), if_neg h1, if_neg h2]
          · have hl' : c'.label = none := by
              rw [hl]; simpa using hcl
            simp [wBP, hl', show c.label = none by simpa using hcl])
    simp only [List.map_const', List.sum_replicate, smul_zero, add_zero] at key
    rw [key]
    simp only [hh', List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    simp [wBP, mkC]

end SelStep2Ident

/-! ## Solid edges without `×`-dotted edge between two blocks -/

section SelStep2Between

variable {k n : ℕ}

open Classical in
/-- `Graph.nBetween` depends only on the blocks of its two atoms. -/
theorem selStep2_nBetween_congr (g : Graph k n) {a a' b b' : Atom k n} (ha : g.SameBlock a a')
    (hb : g.SameBlock b b') : g.nBetween a b = g.nBetween a' b' := by
  unfold Graph.nBetween
  congr 1
  apply List.filter_congr
  intro c _
  simp only [decide_eq_decide]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.trans ha, h2.trans hb⟩
    · exact Or.inr ⟨h1.trans hb, h2.trans ha⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.trans (Graph.sameBlock_symm ha), h2.trans (Graph.sameBlock_symm hb)⟩
    · exact Or.inr ⟨h1.trans (Graph.sameBlock_symm hb), h2.trans (Graph.sameBlock_symm ha)⟩

open Classical in
/-- Fewer solid edges without `×`-dotted edge and the same blocks: `Graph.nBetween` does not
grow. -/
theorem selStep2_nBetween_le {g g' : Graph k n} (hbl : ∀ a b, g'.SameBlock a b ↔ g.SameBlock a b)
    (hsub : g'.unpart.Sublist g.unpart) (a b : Atom k n) : g'.nBetween a b ≤ g.nBetween a b := by
  unfold Graph.nBetween
  refine le_trans (le_of_eq ?_) (List.Sublist.length_le (List.Sublist.filter _ hsub))
  congr 1
  apply List.filter_congr
  intro c _
  rw [decide_eq_decide]
  simp only [hbl]

/-- The two ends of a solid edge without `×`-dotted edge joined by one dotted edge: the identified
pair gives `Graph.nBetween` of any two atoms whose blocks are joined. -/
theorem selStep2_nBetween_join {g : Graph k n} {u v a b : Atom k n} (co : Coeff)
    (hab : ¬ g.SameBlock a b)
    (h : (⟨g.comps ++ [mkC .dot u v], co⟩ : Graph k n).SameBlock a b) :
    g.nBetween u v = g.nBetween a b := by
  rcases (sameBlock_append_dot g u v co a b).1 h with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h0 hab
  · exact selStep2_nBetween_congr g (Graph.sameBlock_symm h1) h2
  · rw [Graph.nBetween_comm]
    exact selStep2_nBetween_congr g (Graph.sameBlock_symm h1) h2

/-- Removing a `×`-dotted edge without solid edge keeps the solid edges without `×`-dotted
edge. -/
theorem selStep2_unpart_erase {g : Graph k n} {i : ℕ} {d : Comp (Atom k n)}
    (hd : g.comps[i]? = some d) (hdo : d ∈ g.orph) :
    (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).unpart.Sublist g.unpart := by
  obtain ⟨-, hdk, hds⟩ := Graph.mem_orph.1 hdo
  have hp : g.comps.Perm (d :: g.comps.eraseIdx i) := perm_cons_eraseIdx hd
  have hpart : ∀ c ∈ g.comps.eraseIdx i, c.kind.isSolid = true →
      (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).partB c = g.partB c := by
    intro c hc hcs
    rw [Bool.eq_iff_iff, Graph.partB_iff, Graph.partB_iff]
    constructor
    · rintro ⟨e, he, hek, hep⟩
      exact ⟨e, List.mem_of_mem_eraseIdx he, hek, hep⟩
    · rintro ⟨e, he, hek, hep⟩
      rcases List.mem_cons.1 (hp.mem_iff.1 he) with rfl | he'
      · exfalso
        have : g.solidB e = true := (g.solidB_iff e).2 ⟨c, List.mem_of_mem_eraseIdx hc, hcs, by
          rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h2.symm, h1.symm⟩⟩
        rw [this] at hds; cases hds
      · exact ⟨e, he', hek, hep⟩
  unfold Graph.unpart
  simp only
  rw [List.filter_congr (p := fun c => c.kind.isSolid &&
      !(⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n).partB c)
    (q := fun c => c.kind.isSolid && !g.partB c) (fun c hc => by
      by_cases hcs : c.kind.isSolid = true
      · rw [hpart c hc hcs]
      · simp [hcs])]
  exact (List.eraseIdx_sublist _ _).filter _

/-- Adding a `×`-dotted edge keeps no new solid edge without `×`-dotted edge. -/
theorem selStep2_unpart_xdot (g : Graph k n) (u v : Atom k n) :
    (⟨g.comps ++ [mkC .xdot u v], g.coeff⟩ : Graph k n).unpart.Sublist g.unpart := by
  unfold Graph.unpart
  simp only
  rw [List.filter_append, List.filter_cons_of_neg (by simp [mkC, Kind.isSolid]), List.filter_nil,
    List.append_nil]
  refine filter_sublist_filter_of_mem _ _ _ fun c hc => ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  rintro ⟨hs, hp⟩
  refine ⟨hs, ?_⟩
  rw [Bool.eq_false_iff] at hp ⊢
  intro h'
  apply hp
  obtain ⟨e, he, hek, hep⟩ := (g.partB_iff c).1 h'
  exact (Graph.partB_iff _ c).2 ⟨e, List.mem_append_left _ he, hek, hep⟩

end SelStep2Between

/-! ## The normalization with the first defect at each step -/

section SelStep2Norm

variable {k : ℕ}

/-- `c` is a `×`-dotted edge of `g` whose two atoms are joined by no solid edge. -/
def selStep2_orphB {n : ℕ} (g : Graph k n) (c : Comp (Atom k n)) : Bool :=
  c.kind == .xdot && !g.solidB c

/-- The first atom of the pair of a solid edge, oriented so that the second is internal when the
`y`-end is. -/
def selStep2_su {n : ℕ} (c : Comp (Atom k n)) : Atom k n := if c.y.isRight then c.x else c.y

/-- The second atom of the pair of a solid edge: its `y`-end if internal, else its `x`-end. -/
def selStep2_sv {n : ℕ} (c : Comp (Atom k n)) : Atom k n := if c.y.isRight then c.y else c.x

/-- The normalization of [II, Def 4.1] used in [II, §4.4, Step 2] with fuel `m`: at the first
`×`-dotted edge without solid edge, `1_{u ≠ v} = 1 - 1_{u = v}` (the second term followed by
`O_merge` and the removal of redundant dotted edges); else at the first solid edge without
`×`-dotted edge `u – v` (`v` internal), `1 = 1_{u = v} + 1_{u ≠ v}` (the first term followed by
`O_merge` and the removal of redundant dotted edges). Terms whose `O_merge` vanishes are
dropped. -/
def selStep2_normF : ℕ → {n : ℕ} → Graph k n → TExpansion k n
  | 0, _, g => [Tracked.self g]
  | m + 1, n, g =>
    match g.comps.findIdx? (selStep2_orphB g) with
    | some i =>
      match g.comps[i]? with
      | some d =>
        selStep2_normF m (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n) ++
          match selStep2_ident ⟨g.comps.eraseIdx i, g.coeff⟩ d.x d.y (-g.coeff) with
          | some t => (selStep2_normF m t.g).map t.comp
          | none => []
      | none => [Tracked.self g]
    | none =>
      match g.unpart with
      | [] => [Tracked.self g]
      | c :: _ =>
        (match selStep2_ident g (selStep2_su c) (selStep2_sv c) g.coeff with
          | some t => (selStep2_normF m t.g).map t.comp
          | none => []) ++
        selStep2_normF m
          (⟨g.comps ++ [mkC .xdot (selStep2_su c) (selStep2_sv c)], g.coeff⟩ : Graph k n)

/-- The normalization at fuel `#unpart + #orph`. -/
def selNorm {n : ℕ} (g : Graph k n) : TExpansion k n :=
  selStep2_normF (g.unpart.length + g.orph.length) g

theorem selStep2_normF_orph {m n : ℕ} {g : Graph k n} {i : ℕ} {d : Comp (Atom k n)}
    (hi : g.comps.findIdx? (selStep2_orphB g) = some i) (hd : g.comps[i]? = some d) :
    selStep2_normF (m + 1) g = selStep2_normF m (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k n) ++
      match selStep2_ident ⟨g.comps.eraseIdx i, g.coeff⟩ d.x d.y (-g.coeff) with
      | some t => (selStep2_normF m t.g).map t.comp
      | none => [] := by
  rw [selStep2_normF, hi]
  simp only [hd]

theorem selStep2_normF_unp {m n : ℕ} {g : Graph k n} {c : Comp (Atom k n)}
    {l : List (Comp (Atom k n))}
    (hi : g.comps.findIdx? (selStep2_orphB g) = none) (hU : g.unpart = c :: l) :
    selStep2_normF (m + 1) g =
      (match selStep2_ident g (selStep2_su c) (selStep2_sv c) g.coeff with
        | some t => (selStep2_normF m t.g).map t.comp
        | none => []) ++
      selStep2_normF m
        (⟨g.comps ++ [mkC .xdot (selStep2_su c) (selStep2_sv c)], g.coeff⟩ : Graph k n) := by
  rw [selStep2_normF, hi]
  simp only [hU]

theorem selStep2_normF_done {m n : ℕ} {g : Graph k n}
    (hi : g.comps.findIdx? (selStep2_orphB g) = none) (hU : g.unpart = []) :
    selStep2_normF (m + 1) g = [Tracked.self g] := by
  rw [selStep2_normF, hi]
  simp only [hU]

theorem selStep2_orphB_none {n : ℕ} {g : Graph k n}
    (h : g.comps.findIdx? (selStep2_orphB g) = none) : g.orph = [] := by
  rw [List.findIdx?_eq_none_iff] at h
  rw [List.eq_nil_iff_forall_not_mem]
  intro d hd
  obtain ⟨hdm, hdk, hds⟩ := Graph.mem_orph.1 hd
  have := h d hdm
  simp [selStep2_orphB, hdk, hds] at this

theorem selStep2_orphB_some {n : ℕ} {g : Graph k n} {i : ℕ}
    (h : g.comps.findIdx? (selStep2_orphB g) = some i) :
    ∃ d, g.comps[i]? = some d ∧ d ∈ g.orph := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  refine ⟨g.comps[i], List.getElem?_eq_getElem hi, Graph.mem_orph.2 ⟨List.getElem_mem hi, ?_⟩⟩
  simpa [selStep2_orphB] using hp

/-- The clauses on an output `t` of the normalization of `g` at `x` (with the count of
the solid edges removed at an identification of two given blocks, the components at the external
atoms, the history): `I` identifications of blocks have been made, which removed `E` solid edges
inside the new blocks; if the blocks of `a` and `b` are joined, then `I ≥ 1`, and for `I = 1` the
`E` removed edges join the blocks of `a` and `b` in `g`. -/
structure SelStep2NormOut {n : ℕ} (C : ℕ) (x : Atom k n) (g : Graph k n) (t : Tracked k n) :
    Prop where
  nn : NN C (t.f x) t.g
  unp : t.g.unpart = []
  orp : t.g.orph = []
  sr : SR g x t
  count : ∃ I E : ℕ, t.g.ord + E = g.ord + 2 * I ∧ E ≤ g.unpart.length ∧
    (I = 0 → E = 0 ∧ t.g.pw (t.f x) = g.pw x) ∧ (∀ b, g.Beta b → I = 1 → E ≤ b) ∧
    (I = 1 → E = 2 → g.HAvoid x → t.g.pw (t.f x) = g.pw x) ∧
    (∀ a b, ¬ g.SameBlock a b → t.g.SameBlock (t.f a) (t.f b) →
      1 ≤ I ∧ (I = 1 → E ≤ g.nBetween a b))
  oo : OO1 g t
  hist : SelStep2Hist g t
  inl : ∀ o, t.f (.inl o) = .inl o

/-- The tracked graph `g` itself is an output of its normalization when it has no defect. -/
theorem selStep2_normOut_self {n C : ℕ} {x : Atom k n} {g : Graph k n} (hN : NN C x g)
    (hu : g.unpart = []) (ho : g.orph = []) : SelStep2NormOut C x g (Tracked.self g) :=
  ⟨hN, hu, ho, SR.refl g x hN.hx, ⟨0, 0, by simp [Tracked.self], by simp,
    fun _ => ⟨rfl, rfl⟩, fun _ _ h => absurd h (by simp), fun h => absurd h (by simp),
    fun a b hab h => absurd h hab⟩, OO1.self g, .refl g, fun _ => rfl⟩

/-- The normalization (the explicit list `selStep2_normF m g`): at most `2 ^ m`
terms with the value of `g`, each with the clauses `SelStep2NormOut`. -/
theorem selStep2_normF_spec (m : ℕ) : ∀ {n C : ℕ} {x : Atom k n} (g : Graph k n), NN C x g →
    g.unpart.length + g.orph.length ≤ m →
    (selStep2_normF m g).length ≤ 2 ^ m ∧ (selStep2_normF m g).ValueEq g modelAdm ∧
      ∀ t ∈ selStep2_normF m g, SelStep2NormOut (C + m) x g t ∧
        t.g.comps.length ≤ g.comps.length + m := by
  induction m with
  | zero =>
    intro n C x g hN hm
    have hu : g.unpart = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ho : g.orph = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨by simp [selStep2_normF], ?_, ?_⟩
    · intro Ω ι _ _ PF D _ e
      funext ω
      simp [selStep2_normF, TExpansion.forget, Expansion.valR, Tracked.self]
    · intro t ht
      simp only [selStep2_normF, List.mem_singleton] at ht
      subst ht
      exact ⟨selStep2_normOut_self hN hu ho, by simp [Tracked.self]⟩
  | succ m ih =>
    intro n C x g hN hm
    rcases hfi : g.comps.findIdx? (selStep2_orphB g) with _ | i
    · have hO : g.orph = [] := selStep2_orphB_none hfi
      rcases hU : g.unpart with _ | ⟨c₀, l⟩
      · rw [selStep2_normF_done hfi hU]
        refine ⟨by simp; exact Nat.one_le_two_pow, ?_, ?_⟩
        · intro Ω ι _ _ PF D _ e
          funext ω
          simp [TExpansion.forget, Expansion.valR, Tracked.self]
        · intro t ht
          rw [List.mem_singleton] at ht
          subst ht
          exact ⟨selStep2_normOut_self (hN.mono (by omega)) hU hO, by simp [Tracked.self]⟩
      · -- a solid edge without `×`-dotted edge: `1 = 1_{u = v} + 1_{u ≠ v}`
        rw [selStep2_normF_unp hfi hU]
        have hc₀ : c₀ ∈ g.unpart := by rw [hU]; exact List.mem_cons_self ..
        obtain ⟨hc₀m, hc₀s, hc₀p⟩ := Graph.mem_unpart.1 hc₀
        set u := selStep2_su c₀ with hu_def
        set v := selStep2_sv c₀ with hv_def
        have huv : (u = c₀.x ∧ v = c₀.y) ∨ (u = c₀.y ∧ v = c₀.x) := by
          by_cases hy : c₀.y.isRight = true
          · left; simp [hu_def, hv_def, selStep2_su, selStep2_sv, hy]
          · right; simp [hu_def, hv_def, selStep2_su, selStep2_sv, hy]
        have hv : v.isRight = true := by
          by_cases hy : c₀.y.isRight = true
          · simp [hv_def, selStep2_sv, hy]
          · simp only [hv_def, selStep2_sv, hy]
            rcases hN.unpInt c₀ hc₀ with h | h
            · simpa using h
            · exact absurd h hy
        have hnb : ¬ g.SameBlock u v := by
          have := hN.inBlk c₀ hc₀m hc₀s
          rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact this
          · rw [h1, h2]; exact fun h => this (Graph.sameBlock_symm h)
        have hne : u ≠ v := fun he => hnb (by rw [he]; exact Graph.sameBlock_refl _ _)
        have hS := oSplitT_eq (g := g) hne
        obtain ⟨hN₂, hU₂, hO₂, hB₂, hH₂, hpw₂, hord₂, hex₂, -, hbl₂⟩ := xdotBranch hN hc₀ huv
        set g₂ : Graph k n := ⟨g.comps ++ [mkC .xdot u v], g.coeff⟩ with hg₂
        have hmem₂ : Tracked.self g₂ ∈ oSplitT u v g := by
          rw [hS]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))
        have hst₂ : QElemStep ⟨n, g⟩ ⟨n, g₂⟩ := QElemStep.split u v g (Tracked.self g₂) hv hmem₂
        have hSR₂ : SR g x (Tracked.self g₂) := by
          refine SR.of_id hN.hx hN.plain.labRand ?_ ?_ ?_ (le_of_eq hex₂) (.single hst₂)
          · exact (List.filter_sublist.trans (List.sublist_append_left _ _)).subperm
          · intro c hc _; exact List.mem_append_left _ hc
          · intro c hc _ _ _; exact List.mem_append_left _ hc
        obtain ⟨hF₂l, hF₂v, hF₂⟩ := ih g₂ hN₂ (by omega)
        have huvo : ∀ o, ODiff o g → u ≠ .inl o ∧ v ≠ .inl o := by
          intro o hO
          obtain ⟨h1, h2⟩ := ends_off hO hc₀m (Kind.not_isDiffusive_of_isRandom
            (Kind.isRandom_of_isSolid hc₀s))
          rcases huv with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [h3, h4]; exact ⟨h1, h2⟩
          · rw [h3, h4]; exact ⟨h2, h1⟩
        have hK1g₂ : PStepsOK1 g g₂ := by
          refine PStepsOK1.append (PStepsOK1.refl g) _ (fun o hO d hd => ?_) g.coeff
          rw [List.mem_singleton.1 hd]
          simp [atO, mkC, (huvo o hO).1, (huvo o hO).2]
        have hnbet₂ := selStep2_nBetween_le hbl₂ (selStep2_unpart_xdot g u v)
        have hout₂ : ∀ t ∈ selStep2_normF m g₂, SelStep2NormOut (C + (m + 1)) x g t ∧
            t.g.comps.length ≤ g.comps.length + (m + 1) := by
          intro t ht
          obtain ⟨⟨hnn, hu, ho, hsr, ⟨I, E, he, hE, h0, hb, h1, hpm⟩, hoo, hhist, hinl⟩, hl⟩ := hF₂ t ht
          refine ⟨⟨by rw [show C + (m + 1) = C + 1 + m by ring]; exact hnn, hu, ho,
            SR.self_comp hSR₂ hN₂.plain.labRand hsr, ⟨I, E, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            OO1.of_ok hK1g₂ hoo, SelStep2Hist.self_comp
              (SelStep2Hist.single (SelStep2Step.split u v g _ hv hmem₂)) hhist, hinl⟩, ?_⟩
          · rw [he, hord₂]
          · exact hE.trans hU₂.le
          · intro hI; obtain ⟨hE0, hp⟩ := h0 hI; exact ⟨hE0, by rw [← hpw₂]; exact hp⟩
          · intro b hB hI; exact hb b (hB₂ b hB) hI
          · intro hI hE2 hH; rw [← hpw₂]; exact h1 hI hE2 (hH₂ hH)
          · intro a b hab hj
            obtain ⟨h1', h2'⟩ := hpm a b (fun h => hab ((hbl₂ a b).1 h)) hj
            exact ⟨h1', fun hI => (h2' hI).trans (hnbet₂ a b)⟩
          · simp [g₂] at hl; omega
        have hnb1 : 1 ≤ g.nBetween u v := by
          classical
          unfold Graph.nBetween
          apply List.length_pos_of_mem (a := c₀)
          refine List.mem_filter.2 ⟨hc₀, ?_⟩
          rcases huv with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · rw [h3, h4]; simp [Graph.sameBlock_refl]
          · rw [h3, h4]; simp [Graph.sameBlock_refl]
        rcases selStep2_ident_spec hN hnb g.coeff with ⟨hnone, hz⟩ | ⟨t₁, hsome, hI, hIo, hIh, hIi⟩
        · rw [hnone]
          simp only [List.nil_append]
          have hpow : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          refine ⟨by omega, ?_, hout₂⟩
          intro Ω ι _ _ PF D hA e
          rw [hF₂v Ω ι PF D hA e]
          funext ω
          have := valR_split PF D g.comps g.coeff u v e ω
          rw [hz Ω ι PF D e] at this
          simpa using this
        · rw [hsome]
          simp only
          have hU₁ : t₁.g.unpart.length + t₁.g.orph.length ≤ m := by
            have h1 := hI.unp; have h2 := hI.orp
            have hlen : g.unpart.length = l.length + 1 := by rw [hU]; rfl
            omega
          obtain ⟨hF₁l, hF₁v, hF₁⟩ := ih t₁.g hI.nn hU₁
          have hmem₁ : Tracked.self (⟨g.comps ++ [mkC .dot u v], g.coeff⟩ : Graph k n) ∈
              oSplitT u v g := by
            rw [hS]; exact List.mem_cons_self ..
          have hst₁ : QElemStep ⟨n, g⟩ ⟨n, ⟨g.comps ++ [mkC .dot u v], g.coeff⟩⟩ :=
            QElemStep.split u v g _ hv hmem₁
          have hSR₁ : SR g x t₁ := by
            refine ⟨hI.carries, hI.dc, ?_, hI.nn.hx,
              (Relation.ReflTransGen.single hst₁).trans hI.chain, ?_⟩
            · rw [hI.exc]
            · intro w hw; obtain ⟨a, ha⟩ := hI.surj w; exact absurd ha (hw a)
          have hH₁ : SelStep2Hist g t₁ :=
            SelStep2Hist.self_comp (SelStep2Hist.single (SelStep2Step.split u v g _ hv hmem₁)) hIh
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_map, pow_succ]; omega
          · intro Ω ι _ _ PF D hA e
            rw [TExpansion.valR_append, TExpansion.valR_map_comp,
              hF₁v Ω ι PF D hA e, hF₂v Ω ι PF D hA e, hI.val Ω ι PF D e]
            funext ω
            exact valR_split PF D g.comps g.coeff u v e ω
          · intro t ht
            rcases List.mem_append.1 ht with ht | ht
            · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
              obtain ⟨⟨hnn, hu, ho, hsr, ⟨I, E, he, hE, h0, hb, h1, hpm⟩, hoo, hhist, hinl⟩, hl⟩ :=
                hF₁ t' ht'
              have hord₁ := hI.ord
              have hunp₁ := hI.unp
              refine ⟨⟨by rw [show C + (m + 1) = C + 1 + m by ring]; exact hnn, hu, ho,
                hSR₁.trans hI.nn.plain.labRand hsr, ⟨I + 1, E + g.nBetween u v, ?_, by omega,
                fun h => absurd h (by simp), ?_, ?_, ?_⟩,
                fun o hO => (hIo o hO (huvo o hO).1 (huvo o hO).2).comp
                  (hoo o (ODiff.of_oout (hIo o hO (huvo o hO).1 (huvo o hO).2) hO)),
                hH₁.trans hhist, fun o => by simp [Tracked.comp, hIi o, hinl o]⟩, ?_⟩
              · simp only [Tracked.comp]
                push_cast at hord₁ ⊢
                linarith
              · intro b hB hI1
                have hI0 : I = 0 := by omega
                rw [(h0 hI0).1]
                simpa using hB u v hnb
              · intro hI1 hE2 hH
                have hI0 : I = 0 := by omega
                obtain ⟨hE0, hp⟩ := h0 hI0
                rw [hE0] at hE2
                have hn2 : 2 ≤ g.nBetween u v := by omega
                simp only [Tracked.comp, Function.comp_apply]
                rw [hp, hI.pwHAv (hH u v hnb hn2)]
              · intro a b hab hj
                refine ⟨by omega, fun hI1 => ?_⟩
                have hI0 : I = 0 := by omega
                rw [(h0 hI0).1, zero_add]
                have hj₁ : t₁.g.SameBlock (t₁.f a) (t₁.f b) := by
                  by_contra hn
                  have := (hpm _ _ hn hj).1
                  omega
                exact le_of_eq (selStep2_nBetween_join g.coeff hab ((hI.blk a b).1 hj₁))
              · simp only [Tracked.comp]
                have := hI.size; omega
            · exact hout₂ t ht
    · -- a `×`-dotted edge without solid edge: `1_{u ≠ v} = 1 - 1_{u = v}`
      obtain ⟨d, hdi, hd⟩ := selStep2_orphB_some hfi
      rw [selStep2_normF_orph hfi hdi]
      obtain ⟨hdm, hdk, hds⟩ := Graph.mem_orph.1 hd
      have hdl : d.label = none := by
        by_contra hne
        have := hN.plain.labRand d hdm (Option.isSome_iff_ne_none.2 hne)
        rw [hdk] at this; simp [Kind.isRandom] at this
      have hX := oXdotT_eq hdi hdk hdl hds
      obtain ⟨hN₁, hU₁, hO₁, hB₁, hH₁, hpw₁, hord₁, hex₁, -, hbl₁, hsub₁⟩ := xdotRemove hN hdi hd
      set g₁ : Graph k n := ⟨g.comps.eraseIdx i, g.coeff⟩ with hg₁
      have hmem₁ : Tracked.self g₁ ∈ oXdotT i g := by rw [hX]; simp
      have hst₁ : QElemStep ⟨n, g⟩ ⟨n, g₁⟩ := QElemStep.xdot i g (Tracked.self g₁) hmem₁
      have hSR₁ : SR g x (Tracked.self g₁) := by
        refine SR.of_id hN.hx hN.plain.labRand ?_ ?_ ?_ (le_of_eq hex₁) (.single hst₁)
        · have hp := (perm_cons_eraseIdx hdi).filter
            (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
          rw [List.filter_cons_of_neg (by simp [hdk])] at hp
          exact hp.subperm.trans List.filter_sublist.subperm
        · intro c hc hk
          exact (List.mem_cons.1 ((perm_cons_eraseIdx hdi).mem_iff.1 hc)).resolve_left (by
            rintro rfl; rw [hdk] at hk; cases hk)
        · intro c hc hk _ _
          exact (List.mem_cons.1 ((perm_cons_eraseIdx hdi).mem_iff.1 hc)).resolve_left (by
            rintro rfl; rw [hdk] at hk; cases hk)
      obtain ⟨hF₁l, hF₁v, hF₁⟩ := ih g₁ hN₁ (by omega)
      have hK1g₁ : PStepsOK1 g g₁ :=
        PStepsOK1.erase (PStepsOK1.refl g) hdi (by rw [hdk]; rfl) g.coeff
      have hnb : ¬ g₁.SameBlock d.x d.y := by rw [hbl₁]; exact hN.xa d hdm hdk
      have hnbet₁ := selStep2_nBetween_le hbl₁ (selStep2_unpart_erase hdi hd)
      -- outputs of the first term
      have hout₁ : ∀ t ∈ selStep2_normF m g₁, SelStep2NormOut (C + (m + 1)) x g t ∧
          t.g.comps.length ≤ g.comps.length + (m + 1) := by
        intro t ht
        obtain ⟨⟨hnn, hu, ho, hsr, ⟨I, E, he, hE, h0, hb, h1, hpm⟩, hoo, hhist, hinl⟩, hl⟩ := hF₁ t ht
        refine ⟨⟨hnn.mono (by omega), hu, ho, SR.self_comp hSR₁ hN₁.plain.labRand hsr,
          ⟨I, E, ?_, ?_, ?_, ?_, ?_, ?_⟩, OO1.of_ok hK1g₁ hoo,
          SelStep2Hist.self_comp (SelStep2Hist.single (SelStep2Step.xdot i g _ hmem₁)) hhist,
          hinl⟩, ?_⟩
        · rw [he, hord₁]
        · exact hE.trans hU₁
        · intro hI; obtain ⟨hE0, hp⟩ := h0 hI; exact ⟨hE0, by rw [← hpw₁]; exact hp⟩
        · intro b hB hI; exact hb b (hB₁ b hB) hI
        · intro hI hE2 hH; rw [← hpw₁]; exact h1 hI hE2 (hH₁ hH)
        · intro a b hab hj
          obtain ⟨h1', h2'⟩ := hpm a b (fun h => hab ((hbl₁ a b).1 h)) hj
          exact ⟨h1', fun hI => (h2' hI).trans (hnbet₁ a b)⟩
        · have := (perm_cons_eraseIdx hdi).length_eq
          simp only [List.length_cons] at this
          simp only [g₁] at hl
          omega
      rcases selStep2_ident_spec hN₁ hnb (-g.coeff) with ⟨hnone, hz⟩ | ⟨t₂, hsome, hI, hIo, hIh, hIi⟩
      · rw [hnone]
        simp only [List.append_nil]
        have hpow : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        refine ⟨by omega, ?_, hout₁⟩
        intro Ω ι _ _ PF D hA e
        rw [hF₁v Ω ι PF D hA e]
        funext ω
        have := valR_xdot PF D g.comps g.coeff hdi hdk hdl e ω
        rw [hz Ω ι PF D e] at this
        simpa using this
      · rw [hsome]
        simp only
        have hU₂ : t₂.g.unpart.length + t₂.g.orph.length ≤ m := by
          have := hI.unp; have := hI.orp; omega
        obtain ⟨hF₂l, hF₂v, hF₂⟩ := ih t₂.g hI.nn hU₂
        have hmem₂ : Tracked.self (⟨g₁.comps ++ [mkC .dot d.x d.y], -g.coeff⟩ : Graph k n) ∈
            oXdotT i g := by
          rw [hX]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))
        have hst₂ : QElemStep ⟨n, g⟩ ⟨n, ⟨g₁.comps ++ [mkC .dot d.x d.y], -g.coeff⟩⟩ :=
          QElemStep.xdot i g _ hmem₂
        have hSR₂ : SR g x t₂ := by
          refine ⟨Tracked.Carries.self_trans hSR₁.carries hI.carries, fun h => hI.dc (hSR₁.dc h),
            ?_, hI.nn.hx, (Relation.ReflTransGen.single hst₂).trans hI.chain, ?_⟩
          · rw [hI.exc, hex₁]
          · intro u hu; obtain ⟨a, ha⟩ := hI.surj u; exact absurd ha (hu a)
        have hH₂ : SelStep2Hist g t₂ :=
          SelStep2Hist.self_comp (SelStep2Hist.single (SelStep2Step.xdot i g _ hmem₂)) hIh
        have hoo₂ : ∀ t' ∈ selStep2_normF m t₂.g, OO1 g (t₂.comp t') := by
          intro t' ht' o hO
          have hk := hK1g₁ o hO
          have hO₁ := ODiff.of_keep hk hO
          obtain ⟨hdx, hdy⟩ := ends_off hO hdm (by rw [hdk]; rfl)
          have h2 := hIo o hO₁ hdx hdy
          exact (h2.comp ((hF₂ t' ht').1.oo o (ODiff.of_oout h2 hO₁))).of_keep hk
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_map, pow_succ]; omega
        · intro Ω ι _ _ PF D hA e
          rw [TExpansion.valR_append, TExpansion.valR_map_comp,
            hF₁v Ω ι PF D hA e, hF₂v Ω ι PF D hA e, hI.val Ω ι PF D e]
          funext ω
          exact valR_xdot PF D g.comps g.coeff hdi hdk hdl e ω
        · intro t ht
          rcases List.mem_append.1 ht with ht | ht
          · exact hout₁ t ht
          obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
          obtain ⟨⟨hnn, hu, ho, hsr, ⟨I, E, he, hE, h0, hb, h1, hpm⟩, -, hhist, hinl⟩, hl⟩ := hF₂ t' ht'
          have hord₂ := hI.ord
          have hunp₂ := hI.unp
          refine ⟨⟨by rw [show C + (m + 1) = C + 1 + m by ring]; exact hnn, hu, ho,
            hSR₂.trans hI.nn.plain.labRand hsr, ⟨I + 1, E + g₁.nBetween d.x d.y, ?_, by omega,
            fun h => absurd h (by simp), ?_, ?_, ?_⟩, hoo₂ t' ht', hH₂.trans hhist,
            fun o => by simp [Tracked.comp, hIi o, hinl o]⟩, ?_⟩
          · simp only [Tracked.comp]
            push_cast at hord₂ ⊢
            rw [hord₁] at hord₂
            linarith
          · intro b hB hI1
            have hI0 : I = 0 := by omega
            rw [(h0 hI0).1]
            simpa using hB₁ b hB d.x d.y hnb
          · intro hI1 hE2 hH
            have hI0 : I = 0 := by omega
            obtain ⟨hE0, hp⟩ := h0 hI0
            rw [hE0] at hE2
            have hn2 : 2 ≤ g₁.nBetween d.x d.y := by omega
            simp only [Tracked.comp, Function.comp_apply]
            rw [hp, hI.pwHAv (hH₁ hH d.x d.y hnb hn2), hpw₁]
          · intro a b hab hj
            refine ⟨by omega, fun hI1 => ?_⟩
            have hI0 : I = 0 := by omega
            rw [(h0 hI0).1, zero_add]
            have hj₂ : t₂.g.SameBlock (t₂.f a) (t₂.f b) := by
              by_contra hn
              have := (hpm _ _ hn hj).1
              omega
            have hab₁ : ¬ g₁.SameBlock a b := fun h => hab ((hbl₁ a b).1 h)
            rw [selStep2_nBetween_join (-g.coeff) hab₁ ((hI.blk a b).1 hj₂)]
            exact hnbet₁ a b
          · simp only [Tracked.comp]
            have := hI.size
            have := (perm_cons_eraseIdx hdi).length_eq
            simp only [List.length_cons] at this
            simp only [g₁] at *
            omega

end SelStep2Norm

/-! ## Moving the labelled components of the block of `x` to `x` -/

section SelStep2Reb

variable {k n : ℕ}

/-- `m` times: the first `×`-dotted edge without solid edge is removed. -/
def selStep2_remOrphF : ℕ → Graph k n → Graph k n
  | 0, g => g
  | m + 1, g =>
    match g.comps.findIdx? (selStep2_orphB g) with
    | some i => selStep2_remOrphF m ⟨g.comps.eraseIdx i, g.coeff⟩
    | none => g

/-- The removal of the `×`-dotted edges without solid edge, the first one at each step. -/
def selStep2_remOrph (g : Graph k n) : Graph k n := selStep2_remOrphF g.orph.length g

theorem selStep2_remOrphF_none {m : ℕ} {g : Graph k n}
    (h : g.comps.findIdx? (selStep2_orphB g) = none) : selStep2_remOrphF (m + 1) g = g := by
  rw [selStep2_remOrphF, h]

theorem selStep2_remOrphF_some {m : ℕ} {g : Graph k n} {i : ℕ}
    (h : g.comps.findIdx? (selStep2_orphB g) = some i) :
    selStep2_remOrphF (m + 1) g = selStep2_remOrphF m ⟨g.comps.eraseIdx i, g.coeff⟩ := by
  rw [selStep2_remOrphF, h]

theorem selStep2_orphB_none_of {g : Graph k n} (h : g.orph = []) :
    g.comps.findIdx? (selStep2_orphB g) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro d hd
  rw [Bool.eq_false_iff]
  intro hb
  have : d ∈ g.orph := Graph.mem_orph.2 ⟨hd, by simpa [selStep2_orphB] using hb⟩
  rw [h] at this; cases this

theorem selStep2_orphB_exists {g : Graph k n} (h : g.orph ≠ []) :
    ∃ i, g.comps.findIdx? (selStep2_orphB g) = some i := by
  rcases h' : g.comps.findIdx? (selStep2_orphB g) with _ | i
  · exact absurd (selStep2_orphB_none h') h
  · exact ⟨i, rfl⟩

open Classical in
/-- `c` is a labelled component with an end other than `x` in the block of `x`. -/
def selStep2_vB (x : Atom k n) (g : Graph k n) (c : Comp (Atom k n)) : Bool :=
  decide (0 < vP x (fun u => g.SameBlock u x) c)

open Classical in
/-- The end of `c` to move to `x`: its `x`-end if it is not `x` and lies in the block of `x`, else
its `y`-end. -/
def selStep2_rebEnd (x : Atom k n) (g : Graph k n) (c : Comp (Atom k n)) : Atom k n :=
  if c.x ≠ x ∧ g.SameBlock c.x x then c.x else c.y

/-- `c` with its end `w` moved to `x`. -/
def selStep2_rebComp (x w : Atom k n) (c : Comp (Atom k n)) : Comp (Atom k n) :=
  { c with x := if c.x = w then x else c.x, y := if c.y = w then x else c.y }

/-- The other end of a solid edge at `x`. -/
def selStep2_rebSplit (x : Atom k n) (c : Comp (Atom k n)) : Atom k n :=
  if c.x = x then c.y else c.x

/-- One move of a labelled component of the block of `x` to `x` (the first component with an end
other than `x` in the block of `x`, its first such end): the rebase step; for a solid edge without
`×`-dotted edge after the move, the term `1_{u ≠ x}` of `1 = 1_{u = x} + 1_{u ≠ x}` (the other
term has value `0`); then the removal of the `×`-dotted edges without solid edge (the other terms
of `1_{u ≠ v} = 1 - 1_{u = v}` have value `0`). -/
def selStep2_rebOne (x : Atom k n) (g : Graph k n) : Graph k n :=
  match g.comps.findIdx? (selStep2_vB x g) with
  | none => g
  | some i =>
    match g.comps[i]? with
    | none => g
    | some c =>
      if c.kind.isSolid = true ∧
          (⟨g.comps.set i (selStep2_rebComp x (selStep2_rebEnd x g c) c), g.coeff⟩ :
            Graph k n).partB (selStep2_rebComp x (selStep2_rebEnd x g c) c) = false then
        selStep2_remOrph ⟨(g.comps.set i (selStep2_rebComp x (selStep2_rebEnd x g c) c)) ++
          [mkC .xdot (selStep2_rebSplit x (selStep2_rebComp x (selStep2_rebEnd x g c) c)) x],
          g.coeff⟩
      else
        selStep2_remOrph ⟨g.comps.set i (selStep2_rebComp x (selStep2_rebEnd x g c) c), g.coeff⟩

theorem selStep2_rebOne_eq {x : Atom k n} {g : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hfi : g.comps.findIdx? (selStep2_vB x g) = some i) (hci : g.comps[i]? = some c) :
    selStep2_rebOne x g =
      if c.kind.isSolid = true ∧
          (⟨g.comps.set i (selStep2_rebComp x (selStep2_rebEnd x g c) c), g.coeff⟩ :
            Graph k n).partB (selStep2_rebComp x (selStep2_rebEnd x g c) c) = false then
        selStep2_remOrph ⟨(g.comps.set i (selStep2_rebComp x (selStep2_rebEnd x g c) c)) ++
          [mkC .xdot (selStep2_rebSplit x (selStep2_rebComp x (selStep2_rebEnd x g c) c)) x],
          g.coeff⟩
      else
        selStep2_remOrph ⟨g.comps.set i (selStep2_rebComp x (selStep2_rebEnd x g c) c),
          g.coeff⟩ := by
  rw [selStep2_rebOne, hfi]
  simp only [hci]

theorem selStep2_vB_some {x : Atom k n} {g : Graph k n} {i : ℕ}
    (h : g.comps.findIdx? (selStep2_vB x g) = some i) :
    ∃ c, g.comps[i]? = some c ∧ 0 < vP x (fun u => g.SameBlock u x) c := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨g.comps[i], List.getElem?_eq_getElem hi, by simpa [selStep2_vB] using hp⟩

theorem selStep2_vB_none {x : Atom k n} {g : Graph k n}
    (h : g.comps.findIdx? (selStep2_vB x g) = none) : g.viol x = 0 := by
  rw [List.findIdx?_eq_none_iff] at h
  unfold Graph.viol
  rw [List.sum_eq_zero_iff]
  intro a ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
  have := h c hc
  rcases Nat.eq_zero_or_pos (vP x (fun u => g.SameBlock u x) c) with h0 | hpos
  · exact h0
  · exfalso
    simp [selStep2_vB, hpos] at this

theorem selStep2_vB_exists {x : Atom k n} {g : Graph k n} (h : 0 < g.viol x) :
    ∃ i, g.comps.findIdx? (selStep2_vB x g) = some i := by
  rcases h' : g.comps.findIdx? (selStep2_vB x g) with _ | i
  · rw [selStep2_vB_none h'] at h; cases h
  · exact ⟨i, rfl⟩

theorem selStep2_rebEnd_spec {x : Atom k n} {g : Graph k n} {c : Comp (Atom k n)}
    (hcv : 0 < vP x (fun u => g.SameBlock u x) c) :
    (selStep2_rebEnd x g c = c.x ∨ selStep2_rebEnd x g c = c.y) ∧ selStep2_rebEnd x g c ≠ x ∧
      g.SameBlock (selStep2_rebEnd x g c) x := by
  classical
  have hcl : c.label.isSome = true := by
    by_contra h; simp [vP, h] at hcv
  unfold vP at hcv
  rw [if_pos hcl] at hcv
  unfold selStep2_rebEnd
  by_cases h1 : c.x ≠ x ∧ g.SameBlock c.x x
  · rw [if_pos h1]; exact ⟨Or.inl rfl, h1.1, h1.2⟩
  · rw [if_neg h1]
    by_cases h2 : c.y ≠ x ∧ g.SameBlock c.y x
    · exact ⟨Or.inr rfl, h2.1, h2.2⟩
    · rw [if_neg h1, if_neg h2] at hcv; omega

/-- The removal of the `×`-dotted edges without solid edge (the explicit graph
`selStep2_remOrphF m h`). -/
theorem selStep2_remOrphF_spec (m : ℕ) : ∀ {C : ℕ} {x : Atom k n} (h : Graph k n), NN C x h →
    h.unpart = [] → h.orph.length ≤ m →
    (∃ e ∈ h.comps, e.kind = .xdot ∧ h.solidB e = true ∧ ∀ d ∈ h.orph,
      (h.SameBlock e.x d.x ∧ h.SameBlock e.y d.y) ∨ (h.SameBlock e.x d.y ∧ h.SameBlock e.y d.x)) ∨
      h.orph = [] →
    KeepOut C x h (selStep2_remOrphF m h) ∧ PStepsOK1 h (selStep2_remOrphF m h) ∧
      SelStep2Hist h (Tracked.self (selStep2_remOrphF m h)) := by
  induction m with
  | zero =>
    intro C x h hN hU hO _
    have hO' : h.orph = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨⟨Relation.ReflTransGen.refl, hN, hU, hO', rfl, rfl, rfl, rfl, fun _ _ => Iff.rfl,
      fun _ _ _ _ _ _ _ => rfl, SR.refl h x hN.hx, fun c hc _ => hc, fun c hc _ => hc, le_rfl⟩,
      PStepsOK1.refl h, .refl h⟩
  | succ m ih =>
    intro C x h hN hU hO hZ
    by_cases hO0 : h.orph = []
    · rw [selStep2_remOrphF_none (selStep2_orphB_none_of hO0)]
      exact ⟨⟨Relation.ReflTransGen.refl, hN, hU, hO0, rfl, rfl, rfl, rfl, fun _ _ => Iff.rfl,
        fun _ _ _ _ _ _ _ => rfl, SR.refl h x hN.hx, fun c hc _ => hc, fun c hc _ => hc, le_rfl⟩,
        PStepsOK1.refl h, .refl h⟩
    obtain ⟨e, he, hek, hes, hed⟩ := hZ.resolve_right hO0
    obtain ⟨i, hfi⟩ := selStep2_orphB_exists hO0
    obtain ⟨d, hdi, hd⟩ := selStep2_orphB_some hfi
    obtain ⟨hdm, hdk, hds⟩ := Graph.mem_orph.1 hd
    rw [selStep2_remOrphF_some hfi]
    have hdl : d.label = none := by
      by_contra hne
      have := hN.plain.labRand d hdm (Option.isSome_iff_ne_none.2 hne)
      rw [hdk] at this; simp [Kind.isRandom] at this
    have hX := oXdotT_eq hdi hdk hdl hds
    obtain ⟨hN₁, hU₁, hO₁, -, -, hpw₁, hord₁, hex₁, -, hbl₁, hsub₁⟩ := xdotRemove hN hdi hd
    set h₁ : Graph k n := ⟨h.comps.eraseIdx i, h.coeff⟩ with hh₁
    have hp := perm_cons_eraseIdx hdi
    have hne : e ≠ d := by
      rintro rfl; rw [hes] at hds; cases hds
    have he₁ : e ∈ h₁.comps := by
      rcases List.mem_cons.1 (hp.mem_iff.1 he) with h' | h'
      · exact absurd h' hne
      · exact h'
    have hmem₁ : Tracked.self h₁ ∈ oXdotT i h := by rw [hX]; simp
    have hst₁ : QElemStep ⟨n, h⟩ ⟨n, h₁⟩ := QElemStep.xdot i h (Tracked.self h₁) hmem₁
    -- the second term vanishes
    have hz : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e' : Fin k → ι), (⟨h₁.comps ++ [mkC .dot d.x d.y], -h.coeff⟩ : Graph k n).valR PF D e' = 0 := by
      intro Ω ι _ _ PF D e'
      apply valR_eq_zero_of_not_xdotApart
      · intro c hc hk
        rcases List.mem_append.1 hc with hc | hc
        · by_contra hne'
          have := hN.plain.labRand c (List.mem_of_mem_eraseIdx hc) (Option.isSome_iff_ne_none.2 hne')
          rcases hk with hk | hk <;> rw [hk] at this <;> simp [Kind.isRandom] at this
        · simp at hc; subst hc; rfl
      · intro hxa
        apply hxa e (List.mem_append_left _ he₁) hek
        have hdot : (⟨h₁.comps ++ [mkC .dot d.x d.y], -h.coeff⟩ : Graph k n).SameBlock d.x d.y :=
          Graph.sameBlock_of_dot (c := mkC .dot d.x d.y) (List.mem_append_right _ (by simp)) rfl
        have hmono : ∀ a b, h.SameBlock a b →
            (⟨h₁.comps ++ [mkC .dot d.x d.y], -h.coeff⟩ : Graph k n).SameBlock a b := by
          intro a b hab
          rw [← hbl₁] at hab
          exact Graph.sameBlock_mono (fun c hc _ => List.mem_append_left _ hc) hab
        rcases hed d hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ((hmono _ _ h1).trans hdot).trans (Graph.sameBlock_symm (hmono _ _ h2))
        · exact ((hmono _ _ h1).trans (Graph.sameBlock_symm hdot)).trans
            (Graph.sameBlock_symm (hmono _ _ h2))
    have hU₁' : h₁.unpart = [] := List.eq_nil_of_length_eq_zero (by rw [hU] at hU₁; simpa using hU₁)
    have hZ₁ : (∃ e ∈ h₁.comps, e.kind = .xdot ∧ h₁.solidB e = true ∧ ∀ d ∈ h₁.orph,
        (h₁.SameBlock e.x d.x ∧ h₁.SameBlock e.y d.y) ∨ (h₁.SameBlock e.x d.y ∧ h₁.SameBlock e.y d.x))
        ∨ h₁.orph = [] := by
      left
      refine ⟨e, he₁, hek, ?_, ?_⟩
      · obtain ⟨c, hc, hck, hcp⟩ := (h.solidB_iff e).1 hes
        refine (h₁.solidB_iff e).2 ⟨c, ?_, hck, hcp⟩
        rcases List.mem_cons.1 (hp.mem_iff.1 hc) with h' | h'
        · subst h'; rw [hdk] at hck; simp [Kind.isSolid] at hck
        · exact h'
      · intro d' hd'
        have hd'' : d' ∈ h.orph := by
          obtain ⟨h1, h2, h3⟩ := Graph.mem_orph.1 hd'
          refine Graph.mem_orph.2 ⟨List.mem_of_mem_eraseIdx h1, h2, ?_⟩
          rw [Bool.eq_false_iff] at h3 ⊢
          intro hs; apply h3
          obtain ⟨c, hc, hck, hcp⟩ := (h.solidB_iff d').1 hs
          refine (h₁.solidB_iff d').2 ⟨c, ?_, hck, hcp⟩
          rcases List.mem_cons.1 (hp.mem_iff.1 hc) with h' | h'
          · subst h'; rw [hdk] at hck; simp [Kind.isSolid] at hck
          · exact h'
        simp only [hbl₁]
        exact hed d' hd''
    obtain ⟨hK, hK1, hKh⟩ := ih h₁ hN₁ hU₁' (by omega) hZ₁
    refine ⟨?_, (PStepsOK1.erase (PStepsOK1.refl h) hdi (by rw [hdk]; rfl) h.coeff).trans hK1,
      SelStep2Hist.self_comp (SelStep2Hist.single (SelStep2Step.xdot i h _ hmem₁)) hKh⟩
    have hSR₁ : SR h x (Tracked.self h₁) := by
      refine SR.of_id hN.hx hN.plain.labRand ?_ ?_ ?_ (le_of_eq hex₁) (.single hst₁)
      · have hp' := hp.filter (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
        rw [List.filter_cons_of_neg (by simp [hdk])] at hp'
        exact hp'.subperm.trans List.filter_sublist.subperm
      · intro c hc hk
        exact (List.mem_cons.1 (hp.mem_iff.1 hc)).resolve_left (by rintro rfl; rw [hdk] at hk; cases hk)
      · intro c hc hk _ _
        exact (List.mem_cons.1 (hp.mem_iff.1 hc)).resolve_left (by rintro rfl; rw [hdk] at hk; cases hk)
    have hvio₁ : h₁.viol x = h.viol x := by
      unfold Graph.viol
      rw [blockPred_congr x hbl₁, (hp.map _).sum_eq]
      simp [vP, hdl]
      rfl
    refine ⟨(Relation.ReflTransGen.single hst₁).trans hK.chain, hK.nn, hK.unp, hK.orp,
      hK.ord.trans hord₁, hK.pw.trans hpw₁, hK.vio.trans hvio₁, hK.exc.trans hex₁,
      fun a b => (hK.blk a b).trans (hbl₁ a b), ?_, SR.self_comp hSR₁ hN₁.plain.labRand hK.sr, ?_, ?_,
      hK.size.trans hsub₁.length_le⟩
    · intro Ω ι _ _ PF D e'
      rw [hK.val]
      funext ω
      have := valR_xdot PF D h.comps h.coeff hdi hdk hdl e' ω
      rw [hz Ω ι PF D e'] at this
      simpa using this
    · intro c hc hl
      exact List.mem_of_mem_eraseIdx (hK.labc c hc hl)
    · intro c hc hl
      refine hK.labc' c ?_ hl
      rcases List.mem_cons.1 (hp.mem_iff.1 hc) with h' | h'
      · subst h'; rw [hdl] at hl; cases hl
      · exact h'

theorem selStep2_remOrph_spec {C : ℕ} {x : Atom k n} (h : Graph k n) (hN : NN C x h)
    (hU : h.unpart = [])
    (hZ : (∃ e ∈ h.comps, e.kind = .xdot ∧ h.solidB e = true ∧ ∀ d ∈ h.orph,
      (h.SameBlock e.x d.x ∧ h.SameBlock e.y d.y) ∨ (h.SameBlock e.x d.y ∧ h.SameBlock e.y d.x)) ∨
      h.orph = []) :
    KeepOut C x h (selStep2_remOrph h) ∧ PStepsOK1 h (selStep2_remOrph h) ∧
      SelStep2Hist h (Tracked.self (selStep2_remOrph h)) :=
  selStep2_remOrphF_spec h.orph.length h hN hU le_rfl hZ

/-- One move of a labelled component of the block of `x` to `x` (the explicit
graph `selStep2_rebOne x g`), with its history and the blocks kept. -/
theorem selStep2_rebOne_spec {C : ℕ} {x : Atom k n} {g : Graph k n} (hN : NN C x g)
    (hU : g.unpart = []) (hO : g.orph = []) (hV : 0 < g.viol x) :
    RebOut (C + 1) x g (selStep2_rebOne x g) ∧ PStepsOK1 g (selStep2_rebOne x g) ∧
      SelStep2Hist g (Tracked.self (selStep2_rebOne x g)) ∧
      (∀ a b, (selStep2_rebOne x g).SameBlock a b ↔ g.SameBlock a b) := by
  obtain ⟨i, hfi⟩ := selStep2_vB_exists hV
  obtain ⟨c, hci, hcv⟩ := selStep2_vB_some hfi
  have hcm : c ∈ g.comps := List.mem_of_getElem? hci
  have hi : i < g.comps.length := (List.getElem?_eq_some_iff.1 hci).1
  rw [selStep2_rebOne_eq hfi hci]
  classical
  have hcl : c.label.isSome = true := by
    by_contra h; simp [vP, h] at hcv
  have hcr : c.kind.isRandom = true := hN.plain.labRand c hcm hcl
  -- the end to move
  obtain ⟨w, hw_def⟩ : ∃ w, w = selStep2_rebEnd x g c := ⟨_, rfl⟩
  rw [← hw_def]
  obtain ⟨hw, hwx, hwb⟩ : (w = c.x ∨ w = c.y) ∧ w ≠ x ∧ g.SameBlock w x := by
    rw [hw_def]; exact selStep2_rebEnd_spec hcv
  have hck : c.kind ≠ .dot := Kind.ne_dot_of_isRandom hcr
  have hckx : c.kind ≠ .xdot := Kind.ne_xdot_of_isRandom hcr
  set c' : Comp (Atom k n) := selStep2_rebComp x w c with hc'
  set g₁ : Graph k n := ⟨g.comps.set i c', g.coeff⟩ with hg₁
  have hst : QElemStep ⟨n, g⟩ ⟨n, g₁⟩ := QElemStep.rebase i g c w x hci hck hwb
  have hstH : SelStep2Hist g (Tracked.self g₁) :=
    SelStep2Hist.single (SelStep2Step.rebase i g c w x hci hck hwb)
  have hxo : ∀ o : Fin k, x ≠ .inl o := by
    intro o h
    have := hN.hx
    rw [h] at this
    cases this
  have hK1₁ : PStepsOK1 g g₁ := by
    refine PStepsOK1.set (PStepsOK1.refl g) hci (Kind.not_isDiffusive_of_isRandom hcr) c' (fun o ho => ?_)
      g.coeff
    rw [psteps_atO_iff] at ho ⊢
    rcases ho with h | h
    · left
      have h' : (if c.x = w then x else c.x) = .inl o := h
      split_ifs at h' with hw'
      · exact absurd h' (hxo o)
      · exact h'
    · right
      have h' : (if c.y = w then x else c.y) = .inl o := h
      split_ifs at h' with hw'
      · exact absurd h' (hxo o)
      · exact h'
  have hp : g.comps.Perm (c :: g.comps.eraseIdx i) := perm_cons_eraseIdx hci
  have hp₁ : g₁.comps.Perm (c' :: g.comps.eraseIdx i) := by
    have h1 : (g.comps.set i c')[i]? = some c' := by simp [hi]
    have := perm_cons_eraseIdx h1
    rwa [List.eraseIdx_set_eq] at this
  have hmem₁ : ∀ d, d ∈ g₁.comps ↔ d = c' ∨ d ∈ g.comps.eraseIdx i := by
    intro d; rw [hp₁.mem_iff, List.mem_cons]
  have hmem : ∀ d, d ∈ g.comps ↔ d = c ∨ d ∈ g.comps.eraseIdx i := by
    intro d; rw [hp.mem_iff, List.mem_cons]
  have hsub : ∀ d ∈ g.comps.eraseIdx i, d ∈ g.comps := fun d hd => List.mem_of_mem_eraseIdx hd
  have hck' : c'.kind = c.kind := rfl
  -- dotted and `×`-dotted edges are unchanged
  have hdx : ∀ d, (d.kind = .dot ∨ d.kind = .xdot) → (d ∈ g₁.comps ↔ d ∈ g.comps) := by
    intro d hd
    rw [hmem₁, hmem]
    constructor
    · rintro (rfl | h)
      · rcases hd with hd | hd
        · exact absurd hd hck
        · exact absurd hd hckx
      · exact Or.inr h
    · rintro (rfl | h)
      · rcases hd with hd | hd
        · exact absurd hd hck
        · exact absurd hd hckx
      · exact Or.inr h
  have hbl : ∀ a b, g₁.SameBlock a b ↔ g.SameBlock a b :=
    fun a b => (Graph.sameBlock_iff_of_dots (fun d hd => (hdx d (Or.inl hd)).symm) a b).symm
  have hwx' : g₁.SameBlock w x := (hbl w x).2 hwb
  -- the ends of `c'`
  have hcx' : g.SameBlock c'.x c.x := by
    simp only [hc', selStep2_rebComp]
    split_ifs with h
    · rw [h]; exact Graph.sameBlock_symm hwb
    · exact Graph.sameBlock_refl _ _
  have hcy' : g.SameBlock c'.y c.y := by
    simp only [hc', selStep2_rebComp]
    split_ifs with h
    · rw [h]; exact Graph.sameBlock_symm hwb
    · exact Graph.sameBlock_refl _ _
  have hlab' : c'.label = c.label := rfl
  -- the scaling order, the weights, the dot excess and the value
  have hord : g₁.ord = g.ord := by
    rw [Graph.ord_perm (g := g₁) (g' := ⟨c' :: g.comps.eraseIdx i, g.coeff⟩) hp₁,
      Graph.ord_perm (g := g) (g' := ⟨c :: g.comps.eraseIdx i, g.coeff⟩) hp]
    simp [Graph.ord, hck']
  have hpw : g₁.pw x = g.pw x := by
    unfold Graph.pw
    rw [blockPred_congr x hbl, (hp₁.map _).sum_eq, (hp.map _).sum_eq]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    refine wBP_congr rfl hck' ?_ ?_
    · exact ⟨fun h => hcx'.symm.trans h, fun h => hcx'.trans h⟩
    · exact ⟨fun h => hcy'.symm.trans h, fun h => hcy'.trans h⟩
  have hvio : g₁.viol x < g.viol x := by
    unfold Graph.viol
    rw [blockPred_congr x hbl, (hp₁.map _).sum_eq, (hp.map _).sum_eq]
    simp only [List.map_cons, List.sum_cons]
    have : vP x (fun u => g.SameBlock u x) c' < vP x (fun u => g.SameBlock u x) c := by
      have hP : ∀ a : Atom k n, ((if a = w then x else a) ≠ x ∧
          g.SameBlock (if a = w then x else a) x) → (a ≠ x ∧ g.SameBlock a x) := by
        intro a ha
        split_ifs at ha with h
        · exact absurd rfl ha.1
        · exact ha
      have hPw : ∀ a : Atom k n, a = w → ¬ ((if a = w then x else a) ≠ x ∧
          g.SameBlock (if a = w then x else a) x) := by
        intro a ha h; rw [if_pos ha] at h; exact h.1 rfl
      have hlt : ∀ (p q p' q' : Prop) {_ : Decidable p} {_ : Decidable q} {_ : Decidable p'}
          {_ : Decidable q'},
          (p' → p) → (q' → q) → ((p ∧ ¬ p') ∨ (q ∧ ¬ q')) →
          (if p' then 1 else 0) + (if q' then 1 else 0) < (if p then 1 else 0) + (if q then 1 else 0) := by
        intro p q p' q' _ _ _ _ h1 h2 h3
        by_cases hp' : p'
        · have hp := h1 hp'; rw [if_pos hp', if_pos hp]
          rcases h3 with ⟨_, h⟩ | ⟨hq, hq'⟩
          · exact absurd hp' h
          · rw [if_neg hq', if_pos hq]; first | omega | (split_ifs <;> omega)
        · rw [if_neg hp']
          by_cases hq' : q'
          · have hq := h2 hq'; rw [if_pos hq', if_pos hq]
            rcases h3 with ⟨hp, _⟩ | ⟨_, h⟩
            · rw [if_pos hp]; omega
            · exact absurd hq' h
          · rw [if_neg hq']
            rcases h3 with ⟨hp, _⟩ | ⟨hq, _⟩
            · rw [if_pos hp]; first | omega | (split_ifs <;> omega)
            · rw [if_pos hq]; first | omega | (split_ifs <;> omega)
      unfold vP
      rw [hlab', if_pos hcl, if_pos hcl]
      refine hlt _ _ _ _ (hP c.x) (hP c.y) ?_
      rcases hw with rfl | rfl
      · exact Or.inl ⟨⟨hwx, hwb⟩, hPw c.x rfl⟩
      · exact Or.inr ⟨⟨hwx, hwb⟩, hPw c.y rfl⟩
    omega
  have hexc : excL g₁.comps = excL g.comps := by
    rw [excL_perm hp₁, excL_perm hp, excL_cons_ne hck, excL_cons_ne (by rw [hck']; exact hck)]
  have hval : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι), g₁.valR PF D e = g.valR PF D e := by
    intro Ω ι _ _ PF D e
    exact valR_rebase PF D g hci hck hwb (fun d hd hk => by
      by_contra hne
      have := hN.plain.labRand d hd (Option.isSome_iff_ne_none.2 hne)
      rw [hk] at this; simp [Kind.isRandom] at this) e
  -- `w` is external
  have hwe : w.isRight = false := by
    by_contra hwr
    have hwr' : w.isRight = true := by simpa using hwr
    obtain ⟨a, rfl⟩ : ∃ a, w = .inr a := by
      rcases w with a | a
      · simp at hwr'
      · exact ⟨a, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, x = .inr b := by
      rcases hx : x with b | b
      · have := hN.hx; rw [hx] at this; simp at this
      · exact ⟨b, rfl⟩
    rw [hb] at hwb hwx
    exact hwx (by rw [hN.ib a b hwb])
  have hSR : SR g x (Tracked.self g₁) := by
    refine SR.of_id hN.hx hN.plain.labRand ?_ (fun d hd hk => (hdx d (Or.inl hk)).2 hd) ?_
      (le_of_eq hexc) (.single hst)
    · have h1 := hp.filter (fun d => decide (d.label = none ∧ d.kind ≠ .dot ∧ d.kind ≠ .xdot))
      have h2 := hp₁.filter (fun d => decide (d.label = none ∧ d.kind ≠ .dot ∧ d.kind ≠ .xdot))
      have hcn : ¬ (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot) := by
        rintro ⟨h, -⟩; rw [h] at hcl; cases hcl
      rw [List.filter_cons_of_neg (by simpa using hcn)] at h1
      rw [List.filter_cons_of_neg (by simpa [hlab', hck'] using hcn)] at h2
      exact (h1.trans h2.symm).subperm.trans List.filter_sublist.subperm
    · intro d hd hk hdx' hdy'
      rcases (hmem d).1 hd with rfl | h
      · exfalso
        rcases hw with rfl | rfl
        · rw [hwe] at hdx'; cases hdx'
        · rw [hwe] at hdy'; cases hdy'
      · exact (hmem₁ d).2 (Or.inr h)
  -- the clauses `NN` for `g₁`
  have hcxy : (c.kind.isSolid = true → c'.x ≠ c'.y) ∧ (c.kind.isWeight = true → c'.y = c'.x) := by
    constructor
    · intro hsol hxy
      have : g.SameBlock c.x c.y :=
        (Graph.sameBlock_symm hcx').trans ((by rw [hxy]; exact Graph.sameBlock_refl _ _ :
          g.SameBlock c'.x c'.y).trans hcy')
      exact hN.inBlk c hcm hsol this
    · intro hwt
      have := (hN.plain c hcm).2.2.2.2.1 hwt
      simp [hc', selStep2_rebComp, this]
  have hwend : c'.x = x ∨ c'.y = x := by
    rcases hw with rfl | rfl
    · left; simp [hc', selStep2_rebComp]
    · right; simp [hc', selStep2_rebComp]
  have hsize₁ : k + n + g₁.comps.length ≤ C := by
    rw [show g₁.comps.length = g.comps.length from List.length_set ..]
    exact hN.reg.size
  have hcnx₁ : g₁.ConnNoX := by
    intro a b
    have hab := hN.cnx a b
    unfold Graph.edgeGraphNoX at hab ⊢
    rw [reachable_fromRel_iff] at hab ⊢
    induction hab with
    | rel p q hr =>
      obtain ⟨d, hd, hk, rfl, rfl⟩ := hr
      rcases (hmem d).1 hd with rfl | h
      · have h1 := (hbl d.x c'.x).2 (Graph.sameBlock_symm hcx')
        have h2 := (hbl c'.y d.y).2 hcy'
        rw [Graph.sameBlock_iff_eqvGen] at h1 h2
        exact ((dotRel_le_noX _ _ _ h1).trans _ _ _ (Relation.EqvGen.rel _ _
          ⟨c', (hmem₁ c').2 (Or.inl rfl), hk, rfl, rfl⟩)).trans _ _ _ (dotRel_le_noX _ _ _ h2)
      · exact Relation.EqvGen.rel _ _ ⟨d, (hmem₁ d).2 (Or.inr h), hk, rfl, rfl⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  have hNN₁ : NN C x g₁ := by
    refine ⟨hN.hx, ⟨hsize₁, ConnNoX.connected hcnx₁, ?_, ?_⟩, hcnx₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b
      refine SimpleGraph.Reachable.mono ?_ (hN.reg.internal a b)
      intro p q hpq
      rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
      have hnot : ∀ d : Comp (Atom k n), d.kind.isRandom = true →
          ¬ ((d.kind.joinsMol = true ∧ d.kind ≠ .dot) ∨ d.kind.isDiffusive = true) := by
        intro d hd h
        rcases h with ⟨h, -⟩ | h
        · rw [Kind.not_joinsMol_of_isRandom hd] at h; cases h
        · rw [Kind.not_isDiffusive_of_isRandom hd] at h; cases h
      rcases hpq with ⟨hne, ⟨d, hd, hk, h1, h2⟩ | ⟨d, hd, hk, h1, h2⟩⟩
      · rcases (hmem d).1 hd with rfl | h
        · exact absurd hk (hnot _ hcr)
        · exact ⟨hne, Or.inl ⟨d, (hmem₁ d).2 (Or.inr h), hk, h1, h2⟩⟩
      · rcases (hmem d).1 hd with rfl | h
        · exact absurd hk (hnot _ hcr)
        · exact ⟨hne, Or.inr ⟨d, (hmem₁ d).2 (Or.inr h), hk, h1, h2⟩⟩
    · intro d hd hk
      exact hN.reg.noIntDot d ((hdx d (Or.inl hk)).1 hd) hk
    · intro d hd hk
      rcases (hmem₁ d).1 hd with rfl | h
      · exact hcxy.1 hk
      · exact hN.noLoop d (hsub d h) hk
    · intro d hd
      rcases (hmem₁ d).1 hd with rfl | h
      · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN.plain c hcm
        exact ⟨h1, h2, h3, fun h => absurd h hck, fun h => hcxy.2 h, h6⟩
      · exact hN.plain d (hsub d h)
    · intro d hd
      rcases (hmem₁ d).1 hd with rfl | h
      · exact hN.lab c hcm
      · exact hN.lab d (hsub d h)
    · intro d hd hk
      rw [hbl]
      exact hN.xa d ((hdx d (Or.inr hk)).1 hd) hk
    · intro a b hab; exact hN.ib a b ((hbl _ _).1 hab)
    · intro d hd hk
      rw [hbl]
      rcases (hmem₁ d).1 hd with rfl | h
      · intro hb
        exact hN.inBlk c hcm hk ((Graph.sameBlock_symm hcx').trans (hb.trans hcy'))
      · exact hN.inBlk d (hsub d h) hk
    · intro d hd
      obtain ⟨hdm, hds, hdp⟩ := Graph.mem_unpart.1 hd
      rcases (hmem₁ d).1 hdm with rfl | h
      · exact hcl
      · exfalso
        have : g.partB d = true := by
          by_contra hp'
          have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hsub d h, hds, by simpa using hp'⟩
          rw [hU] at this; simp at this
        obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 this
        have : g₁.partB d = true := (g₁.partB_iff d).2 ⟨e, (hdx e (Or.inr hek)).2 he, hek, hep⟩
        rw [this] at hdp; cases hdp
    · intro d hd
      obtain ⟨hdm, hds, hdp⟩ := Graph.mem_unpart.1 hd
      rcases (hmem₁ d).1 hdm with rfl | h
      · rcases hwend with h | h
        · left; rw [h]; exact hN.hx
        · right; rw [h]; exact hN.hx
      · exfalso
        have : g.partB d = true := by
          by_contra hp'
          have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hsub d h, hds, by simpa using hp'⟩
          rw [hU] at this; simp at this
        obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 this
        have : g₁.partB d = true := (g₁.partB_iff d).2 ⟨e, (hdx e (Or.inr hek)).2 he, hek, hep⟩
        rw [this] at hdp; cases hdp
  have hsub₁ : ∀ d ∈ g.comps.eraseIdx i, d ∈ g₁.comps := fun d hd => (hmem₁ d).2 (Or.inr hd)
  -- a solid edge of `g` other than `c` keeps its `×`-dotted partner
  have hpart₁ : ∀ d ∈ g.comps.eraseIdx i, d.kind.isSolid = true → g₁.partB d = true := by
    intro d hd hds
    have : g.partB d = true := by
      by_contra hp'
      have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hsub d hd, hds, by simpa using hp'⟩
      rw [hU] at this; simp at this
    obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 this
    exact (g₁.partB_iff d).2 ⟨e, (hdx e (Or.inr hek)).2 he, hek, hep⟩
  by_cases hsol : c.kind.isSolid = true
  · -- a solid edge: its `×`-dotted partner in `g`
    have hpc : g.partB c = true := by
      by_contra hp'
      have : c ∈ g.unpart := Graph.mem_unpart.2 ⟨hcm, hsol, by simpa using hp'⟩
      rw [hU] at this; simp at this
    obtain ⟨e₀, he₀, he₀k, he₀p⟩ := (g.partB_iff c).1 hpc
    have he₀₁ : e₀ ∈ g₁.comps := (hdx e₀ (Or.inr he₀k)).2 he₀
    -- the `×`-dotted edges without solid edge of an extension of `g₁` lie on the pair of `c`
    have horph_of : ∀ (h : Graph k n), (∀ d ∈ h.comps, d.kind = .xdot → d ∈ g₁.comps ∨
        h.solidB d = true) → (∀ d ∈ g₁.comps, d ∈ h.comps) →
        ∀ d ∈ h.orph, (d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x) := by
      intro h hx₁ hsub' d hd
      obtain ⟨hdm, hdk, hds⟩ := Graph.mem_orph.1 hd
      rcases hx₁ d hdm hdk with hd₁ | hds'
      · have hdg := (hdx d (Or.inr hdk)).1 hd₁
        have : g.solidB d = true := by
          by_contra hs'
          have : d ∈ g.orph := Graph.mem_orph.2 ⟨hdg, hdk, by simpa using hs'⟩
          rw [hO] at this; simp at this
        obtain ⟨s', hs', hs'k, hs'p⟩ := (g.solidB_iff d).1 this
        rcases (hmem s').1 hs' with rfl | h'
        · rcases hs'p with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h2.symm, h1.symm⟩
        · have : h.solidB d = true :=
            (h.solidB_iff d).2 ⟨s', hsub' s' (hsub₁ s' h'), hs'k, hs'p⟩
          rw [this] at hds; cases hds
      · rw [hds'] at hds; cases hds
    -- the `×`-dotted edge on the pair of `c'`, if any, and the `×`-dotted edges on the pair of `c`
    have hZ : ∀ (h : Graph k n) (e : Comp (Atom k n)), e ∈ h.comps → e.kind = .xdot →
        ((e.x = c'.x ∧ e.y = c'.y) ∨ (e.x = c'.y ∧ e.y = c'.x)) → (∀ a b, h.SameBlock a b ↔
          g.SameBlock a b) → (∀ d ∈ h.orph, (d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x)) →
        h.solidB e = true → (∃ e ∈ h.comps, e.kind = .xdot ∧ h.solidB e = true ∧ ∀ d ∈ h.orph,
          (h.SameBlock e.x d.x ∧ h.SameBlock e.y d.y) ∨ (h.SameBlock e.x d.y ∧ h.SameBlock e.y d.x))
          ∨ h.orph = [] := by
      intro h e he hek hep hbl' hor hes
      left
      refine ⟨e, he, hek, hes, fun d hd => ?_⟩
      simp only [hbl']
      rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hor d hd with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        rw [h1, h2, h3, h4]
      · exact Or.inl ⟨hcx', hcy'⟩
      · exact Or.inr ⟨hcx', hcy'⟩
      · exact Or.inr ⟨hcy', hcx'⟩
      · exact Or.inl ⟨hcy', hcx'⟩
    by_cases hpc' : g₁.partB c' = true
    · -- `c'` already has a `×`-dotted partner
      have hU₁ : g₁.unpart = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro d hd
        obtain ⟨hdm, hds, hdp⟩ := Graph.mem_unpart.1 hd
        rcases (hmem₁ d).1 hdm with rfl | h
        · rw [hpc'] at hdp; cases hdp
        · rw [hpart₁ d h hds] at hdp; cases hdp
      obtain ⟨e, he, hek, hep⟩ := (g₁.partB_iff c').1 hpc'
      have hes : g₁.solidB e = true := (g₁.solidB_iff e).2 ⟨c', (hmem₁ c').2 (Or.inl rfl), hsol, by
        rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩⟩
      have hor := horph_of g₁ (fun d hd _ => Or.inl hd) (fun d hd => hd)
      rw [if_neg (fun h => by rw [h.2] at hpc'; cases hpc')]
      obtain ⟨hK, hK1, hKh⟩ := selStep2_remOrph_spec g₁ hNN₁ hU₁
        (hZ g₁ e he hek hep hbl hor hes)
      refine ⟨?_, hK1₁.trans hK1, hstH.self_comp hKh, fun a b => (hK.blk a b).trans (hbl a b)⟩
      exact ⟨(Relation.ReflTransGen.single hst).trans hK.chain, hK.nn.mono (by omega), hK.unp,
        hK.orp, hK.ord.trans hord, hK.pw.trans hpw, by rw [hK.vio]; exact hvio,
        hK.exc.trans hexc, fun Ω ι _ _ PF D e => (hK.val Ω ι PF D e).trans (hval Ω ι PF D e),
        SR.self_comp hSR hNN₁.plain.labRand hK.sr, by
          have := hK.size
          rw [show g₁.comps.length = g.comps.length from List.length_set ..] at this; omega⟩
    · -- `c'` gets a `×`-dotted partner: `1 = 1_{u = x} + 1_{u ≠ x}`, the first term vanishes
      have hc'u : c' ∈ g₁.unpart :=
        Graph.mem_unpart.2 ⟨(hmem₁ c').2 (Or.inl rfl), hsol, by simpa using hpc'⟩
      have hU₁ : g₁.unpart.length ≤ 1 := by
        unfold Graph.unpart
        rw [(hp₁.filter _).length_eq, List.filter_cons, List.filter_eq_nil_iff.2 (fun d hd => by
          have := hpart₁ d hd
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          intro ⟨h1, h2⟩; rw [this h1] at h2; cases h2)]
        split_ifs <;> simp
      rw [if_pos ⟨hsol, by simpa using hpc'⟩]
      obtain ⟨u, hu_def⟩ : ∃ u, u = selStep2_rebSplit x c' := ⟨_, rfl⟩
      rw [← hu_def]
      have huv : (u = c'.x ∧ x = c'.y) ∨ (u = c'.y ∧ x = c'.x) := by
        by_cases h : c'.x = x
        · exact Or.inr ⟨by simp [hu_def, selStep2_rebSplit, h], h.symm⟩
        · rcases hwend with h' | h'
          · exact absurd h' h
          · exact Or.inl ⟨by simp [hu_def, selStep2_rebSplit, h], h'.symm⟩
      obtain ⟨hN₂, hU₂, -, -, -, hpw₂, hord₂, hex₂, -, hbl₂⟩ := xdotBranch hNN₁ hc'u huv
      set g₂ : Graph k n := ⟨g₁.comps ++ [mkC .xdot u x], g₁.coeff⟩ with hg₂
      have hux : u ≠ x := by
        intro h
        rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hcxy.1 hsol (by rw [← h1, h, h2])
        · exact hcxy.1 hsol (by rw [← h2, ← h, h1])
      have hS := oSplitT_eq (g := g₁) hux
      have hmem₂ : Tracked.self g₂ ∈ oSplitT u x g₁ := by
        rw [hS]; exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))
      have hst₂ : QElemStep ⟨n, g₁⟩ ⟨n, g₂⟩ :=
        QElemStep.split u x g₁ (Tracked.self g₂) hN.hx hmem₂
      have hz : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
          (e : Fin k → ι), (⟨g₁.comps ++ [mkC .dot u x], g₁.coeff⟩ : Graph k n).valR PF D e = 0 := by
        intro Ω ι _ _ PF D e
        apply valR_eq_zero_of_not_xdotApart
        · intro d hd hk
          rcases List.mem_append.1 hd with hd | hd
          · by_contra hne
            have := hNN₁.plain.labRand d hd (Option.isSome_iff_ne_none.2 hne)
            rcases hk with hk | hk <;> rw [hk] at this <;> simp [Kind.isRandom] at this
          · simp at hd; subst hd; rfl
        · intro hxa
          apply hxa e₀ (List.mem_append_left _ he₀₁) he₀k
          set h' : Graph k n := ⟨g₁.comps ++ [mkC .dot u x], g₁.coeff⟩
          have hmono : ∀ a b, g.SameBlock a b → h'.SameBlock a b := by
            intro a b hab
            rw [← hbl] at hab
            exact Graph.sameBlock_mono (fun d hd _ => List.mem_append_left _ hd) hab
          have hux' : h'.SameBlock u x :=
            Graph.sameBlock_of_dot (c := mkC .dot u x) (List.mem_append_right _ (by simp)) rfl
          -- the ends of `c'` are joined in `h'`
          have hc'b : h'.SameBlock c'.x c'.y := by
            rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [← h1, ← h2]; exact hux'
            · rw [← h1, ← h2]; exact Graph.sameBlock_symm hux'
          have hcb : h'.SameBlock c.x c.y :=
            ((hmono _ _ (Graph.sameBlock_symm hcx')).trans hc'b).trans (hmono _ _ hcy')
          rcases he₀p with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hcb
          · rw [h1, h2]; exact Graph.sameBlock_symm hcb
      have hval₂ : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
          (e : Fin k → ι), g₂.valR PF D e = g₁.valR PF D e := by
        intro Ω ι _ _ PF D e
        funext ω
        have := valR_split PF D g₁.comps g₁.coeff u x e ω
        rw [hz Ω ι PF D e] at this
        simpa using this
      have hSR₂ : SR g₁ x (Tracked.self g₂) := by
        refine SR.of_id hN.hx hNN₁.plain.labRand ?_ ?_ ?_ (le_of_eq hex₂) (.single hst₂)
        · exact (List.filter_sublist.trans (List.sublist_append_left _ _)).subperm
        · intro d hd _; exact List.mem_append_left _ hd
        · intro d hd _ _ _; exact List.mem_append_left _ hd
      have hU₂' : g₂.unpart = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hes : g₂.solidB (mkC .xdot u x) = true := by
        refine (g₂.solidB_iff _).2 ⟨c', List.mem_append_left _ ((hmem₁ c').2 (Or.inl rfl)), hsol, ?_⟩
        simp only [mkC]
        rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
      have hor := horph_of g₂ (fun d hd hdk => by
          rcases List.mem_append.1 hd with hd | hd
          · exact Or.inl hd
          · simp at hd; subst hd; exact Or.inr hes)
        (fun d hd => List.mem_append_left _ hd)
      have hbl₂' : ∀ a b, g₂.SameBlock a b ↔ g.SameBlock a b := fun a b => (hbl₂ a b).trans (hbl a b)
      have hK1₂ : PStepsOK1 g₁ g₂ := by
        refine PStepsOK1.append (PStepsOK1.refl g₁) _ (fun o hO d hd => ?_) g₁.coeff
        rw [List.mem_singleton.1 hd]
        have hc'o : atO o c' = false := hO.random ((hmem₁ c').2 (Or.inl rfl)) hcr
        have huo : u ≠ .inl o := by
          rcases huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · intro h; simp [atO, h] at hc'o
          · intro h; simp [atO, h] at hc'o
        simp [atO, mkC, huo, hxo o]
      obtain ⟨hK, hK1, hKh⟩ := selStep2_remOrph_spec g₂ hN₂ hU₂'
        (hZ g₂ (mkC .xdot u x) (List.mem_append_right _ (by simp)) rfl (by
          simp only [mkC]
          rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, h2⟩) hbl₂' hor hes)
      have hvio₂ : g₂.viol x = g₁.viol x := by
        unfold Graph.viol
        rw [blockPred_congr x hbl₂]
        simp [g₂, vP, mkC]
      refine ⟨?_, (hK1₁.trans hK1₂).trans hK1, hstH.self_comp
        ((SelStep2Hist.single (SelStep2Step.split u x g₁ _ hN.hx hmem₂)).self_comp hKh),
        fun a b => (hK.blk a b).trans (hbl₂' a b)⟩
      refine ⟨((Relation.ReflTransGen.single hst).trans (.single hst₂)).trans hK.chain, hK.nn,
        hK.unp, hK.orp, hK.ord.trans (hord₂.trans hord), hK.pw.trans (hpw₂.trans hpw),
        by rw [hK.vio, hvio₂]; exact hvio, hK.exc.trans (hex₂.trans hexc),
        fun Ω ι _ _ PF D e => (hK.val Ω ι PF D e).trans ((hval₂ Ω ι PF D e).trans
          (hval Ω ι PF D e)),
        SR.self_comp hSR hNN₁.plain.labRand (SR.self_comp hSR₂ hN₂.plain.labRand hK.sr), ?_⟩
      have := hK.size
      simp only [g₂, List.length_append, List.length_singleton] at this
      rw [show g₁.comps.length = g.comps.length from List.length_set ..] at this
      omega
  · -- a weight or a light weight
    have hU₁ : g₁.unpart = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro d hd
      obtain ⟨hdm, hds, hdp⟩ := Graph.mem_unpart.1 hd
      rcases (hmem₁ d).1 hdm with rfl | h
      · exact hsol hds
      · rw [hpart₁ d h hds] at hdp; cases hdp
    have hO₁ : g₁.orph = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro d hd
      obtain ⟨hdm, hdk, hds⟩ := Graph.mem_orph.1 hd
      have hdg := (hdx d (Or.inr hdk)).1 hdm
      have : g.solidB d = true := by
        by_contra hs'
        have : d ∈ g.orph := Graph.mem_orph.2 ⟨hdg, hdk, by simpa using hs'⟩
        rw [hO] at this; simp at this
      obtain ⟨e, he, hek, hep⟩ := (g.solidB_iff d).1 this
      rcases (hmem e).1 he with rfl | h
      · exact hsol hek
      · have : g₁.solidB d = true := (g₁.solidB_iff d).2 ⟨e, hsub₁ e h, hek, hep⟩
        rw [this] at hds; cases hds
    rw [if_neg (fun h => hsol h.1)]
    have hro : selStep2_remOrph g₁ = g₁ := by
      simp only [selStep2_remOrph, hO₁, List.length_nil]; rfl
    rw [hro]
    refine ⟨?_, hK1₁, hstH, hbl⟩
    exact ⟨.single hst, hNN₁.mono (by omega), hU₁, hO₁, hord, hpw, hvio, hexc, hval, hSR,
      by rw [show g₁.comps.length = g.comps.length from List.length_set ..]; omega⟩

end SelStep2Reb

/-! ## Moving all labelled components of the block of `x` to `x` -/

section SelStep2RebAll

variable {k n : ℕ}

theorem selStep2_s6_of_viol {x : Atom k n} {g : Graph k n} (h : g.viol x = 0) : g.S6 x := by
  classical
  intro c hc hl
  have hc0 : vP x (fun u => g.SameBlock u x) c = 0 := by
    unfold Graph.viol at h
    rw [List.sum_eq_zero_iff] at h
    exact h _ (List.mem_map.2 ⟨c, hc, rfl⟩)
  unfold vP at hc0
  rw [if_pos hl] at hc0
  constructor
  · intro hb
    by_contra hne
    rw [if_pos (⟨hne, hb⟩ : c.x ≠ x ∧ g.SameBlock c.x x)] at hc0; omega
  · intro hb
    by_contra hne
    rw [if_pos (⟨hne, hb⟩ : c.y ≠ x ∧ g.SameBlock c.y x)] at hc0; omega

/-- `m` moves of a labelled component of the block of `x` to `x`, until none is left. -/
def selStep2_rebF (x : Atom k n) : ℕ → Graph k n → Graph k n
  | 0, g => g
  | m + 1, g => if g.viol x = 0 then g else selStep2_rebF x m (selStep2_rebOne x g)

/-- The labelled components of the block of `x` moved to `x` one by one ([II, §4.4, Step 2]), at
fuel `viol`. -/
def selRebase (x : Atom k n) (g : Graph k n) : Graph k n := selStep2_rebF x (g.viol x) g

/-- Moving all labelled components of the block of `x` to `x` (the explicit graph
`selStep2_rebF x m g`), with its history and the blocks kept. -/
theorem selStep2_rebF_spec (m : ℕ) : ∀ {C : ℕ} {x : Atom k n} (g : Graph k n), NN C x g →
    g.unpart = [] → g.orph = [] → g.viol x ≤ m →
    Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n, selStep2_rebF x m g⟩ ∧
      St (C + m) x (selStep2_rebF x m g) ∧ (selStep2_rebF x m g).ord = g.ord ∧
      (selStep2_rebF x m g).pw x = g.pw x ∧ excL (selStep2_rebF x m g).comps = excL g.comps ∧
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), (selStep2_rebF x m g).valR PF D e = g.valR PF D e) ∧
      SR g x (Tracked.self (selStep2_rebF x m g)) ∧
      (selStep2_rebF x m g).comps.length ≤ g.comps.length + m ∧
      PStepsOK1 g (selStep2_rebF x m g) ∧ SelStep2Hist g (Tracked.self (selStep2_rebF x m g)) ∧
      (∀ a b, (selStep2_rebF x m g).SameBlock a b ↔ g.SameBlock a b) := by
  induction m with
  | zero =>
    intro C x g hN hU hO hV
    rw [selStep2_rebF]
    exact ⟨.refl, ⟨hN, hU, hO, selStep2_s6_of_viol (by omega)⟩, rfl, rfl, rfl,
      fun _ _ _ _ _ _ _ => rfl, SR.refl g x hN.hx, le_rfl, PStepsOK1.refl g, .refl g,
      fun _ _ => Iff.rfl⟩
  | succ m ih =>
    intro C x g hN hU hO hV
    by_cases h0 : g.viol x = 0
    · rw [selStep2_rebF, if_pos h0]
      exact ⟨.refl, ⟨hN.mono (by omega), hU, hO, selStep2_s6_of_viol h0⟩, rfl, rfl, rfl,
        fun _ _ _ _ _ _ _ => rfl, SR.refl g x hN.hx, by omega, PStepsOK1.refl g, .refl g,
        fun _ _ => Iff.rfl⟩
    rw [selStep2_rebF, if_neg h0]
    obtain ⟨hR, hR1, hRh, hRb⟩ := selStep2_rebOne_spec hN hU hO (by omega)
    obtain ⟨hch, hst, hord, hpw, hexc, hval, hsr, hsz, hK1, hKh, hKb⟩ :=
      ih (selStep2_rebOne x g) hR.nn hR.unp hR.orp (by have := hR.vio; omega)
    refine ⟨hR.chain.trans hch, by rw [show C + (m + 1) = C + 1 + m by ring]; exact hst,
      hord.trans hR.ord, hpw.trans hR.pw, hexc.trans hR.exc,
      fun Ω ι _ _ PF D e => (hval Ω ι PF D e).trans (hR.val Ω ι PF D e),
      SR.self_comp hR.sr hR.nn.plain.labRand hsr, by have := hR.size; omega, hR1.trans hK1,
      hRh.self_comp hKh, fun a b => (hKb a b).trans (hRb a b)⟩

end SelStep2RebAll

/-! ## The first step of a round: `O_merge`, the redundant dotted edges, the moves to `x` -/

section SelStep2Init

variable {k n : ℕ}

theorem selStep2_unpart_nil {C : ℕ} {g : Graph k n} (h : g.Normal C)
    (hx : g.XdotApart) : g.unpart = [] ∧ g.orph = [] := by
  constructor
  · rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hcm, hk, hp⟩ := Graph.mem_unpart.1 hc
    have hne := h.2.1 c hcm hk
    obtain ⟨d, hd, hdk, hdp⟩ := (h.2.2 c.x c.y hne).2 ⟨c, hcm, hk, Or.inl ⟨rfl, rfl⟩⟩
    have : g.partB c = true := (g.partB_iff c).2 ⟨d, hd, hdk, hdp⟩
    rw [hp] at this; cases this
  · rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hcm, hk, hp⟩ := Graph.mem_orph.1 hc
    have hne : c.x ≠ c.y := by
      intro he
      have := hx c hcm hk
      rw [he] at this
      exact this (Graph.sameBlock_refl _ _)
    obtain ⟨d, hd, hdk, hdp⟩ := (h.2.2 c.x c.y hne).1 ⟨c, hcm, hk, Or.inl ⟨rfl, rfl⟩⟩
    have : g.solidB c = true := (g.solidB_iff c).2 ⟨d, hd, hdk, hdp⟩
    rw [hp] at this; cases this

theorem selStep2_connNoX {C : ℕ} {g : Graph k n} (h : g.Normal C) : g.ConnNoX := by
  intro u v
  have hc := h.1.connected u v
  unfold Graph.edgeGraph at hc
  unfold Graph.edgeGraphNoX
  rw [reachable_fromRel_iff] at hc ⊢
  induction hc with
  | rel a b hr =>
    obtain ⟨c, hcm, rfl, rfl⟩ := hr
    by_cases hk : c.kind = .xdot
    · by_cases hab : c.x = c.y
      · rw [hab]; exact Relation.EqvGen.refl _
      · obtain ⟨d, hd, hdk, hdp⟩ := (h.2.2 c.x c.y hab).1 ⟨c, hcm, hk, Or.inl ⟨rfl, rfl⟩⟩
        have hdx : d.kind ≠ .xdot := by
          intro he; rw [he] at hdk; simp [Kind.isSolid] at hdk
        rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Relation.EqvGen.rel _ _ ⟨d, hd, hdx, h1, h2⟩
        · exact (Relation.EqvGen.rel _ _ ⟨d, hd, hdx, h1, h2⟩).symm
    · exact Relation.EqvGen.rel _ _ ⟨c, hcm, hk, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

theorem selStep2_mergeT_none {Γ : Graph k n} (h : Γ.mergeT = none) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ Γ.psteps_mrep c.x = Γ.psteps_mrep c.y := by
  rw [mergeT_eq] at h
  split_ifs at h with hc
  rw [List.any_eq_true] at hc
  obtain ⟨c, hc, hb⟩ := hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨c, hc, hb.1, hb.2⟩

/-- `O_merge` and the removal of the redundant dotted edges (the explicit output
of `selStep2_clean`), with its history, the blocks, the dot excess and the external atoms kept. -/
theorem selStep2_cleanInit_spec {C : ℕ} {x : Atom k n} {g : Graph k n} (hx : x.isRight = true)
    (hNo : g.Normal C) (hpl : g.Plain)
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hxa : g.XdotApart) :
    ∃ t : Tracked k n, selStep2_clean g = some t ∧ (SR g x t ∧ NN C (t.f x) t.g ∧
      t.g.unpart = [] ∧ t.g.orph = [] ∧
      t.g.ord = g.ord ∧ (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
        (D : Ω → Data ι) (e : Fin k → ι), t.g.valR PF D e = g.valR PF D e)) ∧ OO1 g t ∧
      SelStep2Hist g t ∧ (∀ a b, t.g.SameBlock (t.f a) (t.f b) ↔ g.SameBlock a b) ∧
      excL t.g.comps = excL g.comps ∧ (∀ o, t.f (.inl o) = .inl o) := by
  have hreg := hNo.1
  have hcx := selStep2_connNoX hNo
  have hnl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y := hNo.2.1
  obtain ⟨hU0, hO0⟩ := selStep2_unpart_nil hNo hxa
  have hinB : ∀ c ∈ g.comps, c.kind.isSolid = true → ¬ g.SameBlock c.x c.y := by
    intro c hc hs hsb
    obtain ⟨d, hd, hdk, hdp⟩ := (hNo.2.2 c.x c.y (hnl c hc hs)).2 ⟨c, hc, hs, Or.inl ⟨rfl, rfl⟩⟩
    apply hxa d hd hdk
    rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hsb
    · rw [h1, h2]; exact Graph.sameBlock_symm hsb
  have hlabd : ∀ c ∈ g.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
    intro c hc hk
    by_contra hne
    have := hpl.labRand c hc (Option.isSome_iff_ne_none.2 hne)
    rcases hk with hk | hk <;> rw [hk] at this <;> simp [Kind.isRandom] at this
  have hl1 : g.labels.length ≤ 1 := labels_le_one g (.P, x) hlab
  rcases hm : g.mergeT with _ | t₀
  · exfalso
    obtain ⟨c, hc, hk, hr⟩ := selStep2_mergeT_none hm
    exact hxa c hc hk ((Graph.sameBlock_iff_mrep _ _ _).2 hr)
  have hs := psteps_mergeT_spec hm
  have hold : ∀ c ∈ g.comps, c.kind = .dot → t₀.f c.x ≠ t₀.f c.y := by
    intro c hc hk
    have hne : c.x ≠ c.y := (hpl c hc).2.2.2.1 hk
    have hext := hreg.noIntDot c hc hk
    intro hf
    rcases hx' : c.x with a | i <;> rcases hy : c.y with b | j
    · rw [hx', hy, hs.f_inl, hs.f_inl] at hf
      exact hne (by rw [hx', hy, Sum.inl.inj hf])
    · obtain ⟨j', hj'⟩ := hs.f_inr' j
      rw [hx', hy, hs.f_inl, hj'] at hf; cases hf
    · obtain ⟨i', hi'⟩ := hs.f_inr' i
      rw [hx', hy, hs.f_inl, hi'] at hf; cases hf
    · rw [hx', hy] at hext; simp at hext
  have hRr : ((g.comps.filter fun c => c.kind == .dot && t₀.f c.x == t₀.f c.y).length : ℤ) ≤
      (n : ℤ) - t₀.nOut := by
    have hle := hs.nOut_le
    rw [List.filter_eq_nil_iff.2 (fun c hc => by
      by_cases hk : c.kind = .dot
      · simp [hk, hold c hc hk]
      · simp [hk])]
    simp only [List.length_nil, Nat.cast_zero]
    omega
  obtain ⟨g', hsel, hdr, hch, hex, hco, hsub, hnd, hbl, hord, hval⟩ :=
    selStep2_clean_spec g t₀ hm hlabd hl1 hRr
  have hag : Agree g' t₀.g := Agree.of_cleanup hsub hnd hbl
  have hconv : (g.comps.filter fun c => c.kind.isSolid && g.psteps_mrep c.x == g.psteps_mrep c.y).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro hsol hr
    exact hinB c hc hsol ((Graph.sameBlock_iff_mrep _ _ _).2 hr)
  -- unlabelled solid edges are not inside a block
  have hsolU : ∀ c ∈ g.comps, c.label = none → c.kind.isSolid = true →
      ¬ g.SameBlock c.x c.y := fun c hc _ hsol => hinB c hc hsol
  -- the solid edges of `t₀` have `×`-dotted partners
  have hunp₀ : t₀.g.unpart = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c' hc'
    obtain ⟨hc'm, hsol', hp'⟩ := Graph.mem_unpart.1 hc'
    obtain ⟨c, hc, hsol, hrne, rfl⟩ := hs.of_mem_solid hc'm hsol'
    have hcp : g.partB c = true := by
      by_contra hp
      have : c ∈ g.unpart := Graph.mem_unpart.2 ⟨hc, hsol, by simpa using hp⟩
      rw [hU0] at this; simp at this
    obtain ⟨d, hd, hdk, hdp⟩ := (g.partB_iff c).1 hcp
    have : t₀.g.partB (c.map t₀.f) = true := by
      refine (t₀.g.partB_iff _).2 ⟨d.map t₀.f, hs.mem_of_other hd (by rw [hdk]; simp)
        (by rw [hdk]; rfl), hdk, ?_⟩
      rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
      · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
    rw [this] at hp'; cases hp'
  have horph₀ : t₀.g.orph = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c' hc'
    obtain ⟨hc'm, hk', hsb'⟩ := Graph.mem_orph.1 hc'
    obtain ⟨c, hc, hk, rfl⟩ := hs.of_mem_xdot hc'm hk'
    have hcs : g.solidB c = true := by
      by_contra hsb
      have : c ∈ g.orph := Graph.mem_orph.2 ⟨hc, hk, by simpa using hsb⟩
      rw [hO0] at this; simp at this
    obtain ⟨d, hd, hdk, hdp⟩ := (g.solidB_iff c).1 hcs
    have hrne : g.psteps_mrep d.x ≠ g.psteps_mrep d.y := by
      intro hr
      apply hs.xdot_ne c hc hk
      rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hr
      · rw [← h1, ← h2]; exact hr.symm
    have : t₀.g.solidB (c.map t₀.f) = true := by
      refine (t₀.g.solidB_iff _).2 ⟨d.map t₀.f, hs.mem_of_solid hd hdk hrne, hdk, ?_⟩
      rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
      · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
    rw [this] at hsb'; cases hsb'
  have hlen₀ : t₀.g.comps.length ≤ g.comps.length := by
    rw [hs.comps_eq]; exact List.length_filterMap_le _ _
  have hcx₀ : t₀.g.ConnNoX := hs.connNoX hcx
  have hreg₀ : t₀.g.Regular C := by
    refine ⟨?_, ConnNoX.connected hcx₀, hs.internal hreg.internal, hs.noIntDot⟩
    have := hreg.size
    have := hs.nOut_le
    omega
  have hNN : NN C (t₀.f x) g' :=
    hag.nn (hsub.length_le) (by rw [hs.isRight_f]; exact hx) hreg₀ hcx₀ hs.solid_ne
      (hs.plain hpl) (hs.labels hlab) hs.xdotApart hs.ib hs.inBlk
      (by rw [hunp₀]; simp) (by rw [hunp₀]; simp)
  -- the environment is carried
  have hcarS : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
      c.kind ≠ .xdot)).map (Comp.map t₀.f)).Subperm g'.comps := by
    have h1 := hs.carries_sub hsolU
    have h2 : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
        c.kind ≠ .xdot)).map (Comp.map t₀.f)).Subperm
          (t₀.g.comps.filter fun c => decide (c.kind ≠ .dot)) := by
      refine subperm_filter_of_forall h1.subperm _ ?_
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have := (List.mem_filter.1 hd).2
      simp only [decide_eq_true_eq] at this
      simp only [Comp.map]
      exact decide_eq_true this.2.1
    exact (h2.trans hnd.symm.subperm).trans List.filter_sublist.subperm
  have hblk : ∀ a b, g'.SameBlock (t₀.f a) (t₀.f b) ↔ g.SameBlock a b := by
    intro a b; rw [hbl, hs.sameBlock_iff]
  have hdc : g.DoublyConnected → g'.DoublyConnected := by
    intro hdc
    refine dc_transfer t₀.f hpl.labRand hs.f_inr' ?_ ?_ hcarS ?_ hdc
    · have key : ∀ p q, Relation.EqvGen (fun u v => ∃ c ∈ g.comps, c.kind.joinsMol = true ∧
          c.x = u ∧ c.y = v) p q → Relation.EqvGen (fun u v => ∃ c ∈ g'.comps,
            c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) (t₀.f p) (t₀.f q) := by
        intro p q hr
        induction hr with
        | rel p q hpq =>
          obtain ⟨c, hc, hj, rfl, rfl⟩ := hpq
          by_cases hd : c.kind = .dot
          · have hb' := (hblk c.x c.y).2 (Graph.sameBlock_of_dot hc hd)
            rw [Graph.sameBlock_iff_eqvGen] at hb'
            refine Relation.EqvGen.mono ?_ _ _ hb'
            rintro p q ⟨d, hd', hdk, rfl, rfl⟩
            exact ⟨d, hd', by rw [hdk]; rfl, rfl, rfl⟩
          · have hl : c.label = none := by
              by_contra hne'
              have := hpl.labRand c hc (Option.isSome_iff_ne_none.2 hne')
              rw [Kind.not_joinsMol_of_isRandom this] at hj; cases hj
            have hnx : c.kind ≠ .xdot := by intro h; rw [h] at hj; simp [Kind.joinsMol] at hj
            have hmemc : c.map t₀.f ∈ g'.comps :=
              hcarS.subset (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl, hd, hnx]⟩, rfl⟩)
            exact Relation.EqvGen.rel _ _ ⟨c.map t₀.f, hmemc, hj, rfl, rfl⟩
        | refl p => exact Relation.EqvGen.refl _
        | symm p q _ ih => exact ih.symm
        | trans p q r _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
      intro a b ha hb hab
      rcases hab with rfl | ⟨-, -, hr⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨by rw [hs.isRight_f]; exact ha, by rw [hs.isRight_f]; exact hb, ?_⟩
        unfold Graph.molGraph at hr ⊢
        rw [reachable_fromRel_iff] at hr ⊢
        exact key _ _ hr
    · intro j
      obtain ⟨i, hi⟩ := hs.surj_inr j
      exact ⟨i, Or.inl hi.symm⟩
    · intro c hc hk a b a' b' hx' hy' ha hb
      by_cases hsb : g.SameBlock c.x c.y
      · have := (hblk c.x c.y).2 hsb
        rw [hx', hy', ha, hb] at this
        have hab := hNN.ib a' b' this
        subst hab
        exact Relation.EqvGen.refl _
      · have hsol : c.kind.isSolid = true := by rw [hk]; rfl
        have hm : psteps_mergeComp g.psteps_mrep t₀.f c = some (c.map t₀.f) :=
          mergeComp_of_solid hsol (fun hr => hsb ((Graph.sameBlock_iff_mrep _ _ _).2 hr))
        have hm₀ : c.map t₀.f ∈ t₀.g.comps := hs.mem_comps.2 ⟨c, hc, hm⟩
        have hkd : (c.map t₀.f).kind ≠ .dot := by simp [Comp.map, hk]
        have hm' : c.map t₀.f ∈ g'.comps := (hag.mem_nd hkd).2 hm₀
        refine Relation.EqvGen.rel _ _ (Or.inr ⟨c.map t₀.f, hm', hk, ?_, ?_⟩)
        · simp [Comp.map, hx', ha]
        · simp [Comp.map, hy', hb]
  refine ⟨⟨t₀.nOut, g', t₀.f⟩, hsel, ?_, fun o hO => merge_oout hs hO (List.Perm.refl _) hsub hnd,
    (SelStep2Hist.single (SelStep2Step.merge g t₀ hm)).trans (SelStep2Hist.of_drops hdr), hblk,
    hex, hs.f_inl⟩
  refine ⟨⟨⟨hcarS, fun a b hab => (hblk a b).2 hab⟩, hdc, le_of_eq hex,
    by rw [hs.isRight_f]; exact hx, hch, ?_⟩, hNN, ?_, ?_, ?_, hval⟩
  · intro u hu
    obtain ⟨a, ha⟩ := hs.f_surj u
    exact absurd ha (hu a)
  · rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    have := hag.unpart.length_eq
    rw [hunp₀] at this
    have h0 : g'.unpart = [] := List.eq_nil_of_length_eq_zero (by simpa using this)
    rw [h0] at hc; simp at hc
  · rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    have := hag.orph.length_eq
    rw [horph₀] at this
    have h0 : g'.orph = [] := List.eq_nil_of_length_eq_zero (by simpa using this)
    rw [h0] at hc; simp at hc
  · show g'.ord = g.ord
    rw [hord, hconv]; simp

end SelStep2Init

section SelStep2InitMain

variable {k n : ℕ}

/-- The first step of the rounds of [II, §4.4, Step 2] at the atom `X`: `O_merge`, then `r` times
the removal of the first redundant dotted edge (`r` the dot excess created by `O_merge`), then the
labelled components of the block of the image of `X` moved to it (`selRebase`). The empty sum
when `O_merge` gives `0`. -/
def selInit (X : Atom k n) (g : Graph k n) : TExpansion k n :=
  match selStep2_clean g with
  | some t => [⟨t.nOut, selRebase (t.f X) t.g, t.f⟩]
  | none => []

/-- `OO1` and `MainOO1` have the same statement. -/
theorem selStep2_mainOO1 {Γ : Graph k n} {t : Tracked k n} (h : OO1 Γ t) : MainOO1 Γ t := h

theorem selStep2_paperOrd_eq {m : ℕ} (g' : Graph k m) :
    g'.paperOrd = g'.ord - 2 * excL g'.comps := by
  unfold Graph.paperOrd; rw [selStep2_dotExcess_eq]

/-- **The first step of the rounds** ([II, §4.4, Step 2]): for a normal regular graph
`Γ_ω P_x(𝒢)` (`x` internal, labels `P_x` only, no `×`-dotted edge inside a block), `selInit x g`
is one tracked graph `t`, a state of the construction (`St (3 C)`), with the clauses `SR`, the
scaling order (and the paper scaling order) and the value of `g`, the components at the external
atoms kept (`MainOO1`), the blocks and the external atoms kept, and its history of elementary
steps with their atom maps. -/
theorem selStep2_init {C : ℕ} {x : Atom k n} {g : Graph k n} (hx : x.isRight = true)
    (hNo : g.Normal C) (hpl : g.Plain)
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hxa : g.XdotApart) :
    ∃ t : Tracked k n, selInit x g = [t] ∧ St (3 * C) (t.f x) t.g ∧ SR g x t ∧
      t.g.ord = g.ord ∧ t.g.paperOrd = g.paperOrd ∧
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), t.g.valR PF D e = g.valR PF D e) ∧
      MainOO1 g t ∧ SelStep2Hist g t ∧
      (∀ a b, t.g.SameBlock (t.f a) (t.f b) ↔ g.SameBlock a b) ∧
      (∀ o, t.f (.inl o) = .inl o) := by
  obtain ⟨t₀, hsel, ⟨hsr₀, hNN₀, hU₀, hO₀, hord₀, hval₀⟩, hoo₀, hh₀, hblk₀, hex₀, hinl₀⟩ :=
    selStep2_cleanInit_spec hx hNo hpl hlab hxa
  have hsz := hNN₀.reg.size
  obtain ⟨-, hS₁, hord₁, -, hexc₁, hval₁, hsr₁, -, hK1, hh₁, hbl₁⟩ :=
    selStep2_rebF_spec (t₀.g.viol (t₀.f x)) t₀.g hNN₀ hU₀ hO₀ le_rfl
  have hv := Graph.viol_le t₀.g (t₀.f x)
  refine ⟨⟨t₀.nOut, selRebase (t₀.f x) t₀.g, t₀.f⟩, by simp [selInit, hsel],
    hS₁.mono (by omega), SR.trans hsr₀ hNN₀.plain.labRand hsr₁, hord₁.trans hord₀, ?_,
    fun Ω ι _ _ PF D e => (hval₁ Ω ι PF D e).trans (hval₀ Ω ι PF D e),
    selStep2_mainOO1 (OO1.comp hoo₀ (OO1.of_keep hK1)), hh₀.trans hh₁,
    fun a b => ((hbl₁ _ _).trans (hblk₀ a b)), hinl₀⟩
  rw [selStep2_paperOrd_eq, selStep2_paperOrd_eq]
  change (selRebase (t₀.f x) t₀.g).ord - 2 * excL (selRebase (t₀.f x) t₀.g).comps = _
  rw [show (selRebase (t₀.f x) t₀.g) = selStep2_rebF (t₀.f x) (t₀.g.viol (t₀.f x)) t₀.g from rfl,
    hord₁, hexc₁, hord₀, hex₀]

end SelStep2InitMain

/-! ## The blocks and the solid edges without `×`-dotted edge of the terms inside `P_x` -/

section SelStep2Loc

variable {k n : ℕ}

/-- The blocks of the input atoms are those of `g`, at most one solid edge without `×`-dotted
edge joins two blocks of input atoms that are distinct in `g`, and the external atoms are fixed. -/
def SelStep2OpLoc (g : Graph k n) (t : Tracked k n) : Prop :=
  (∀ a b, t.g.SameBlock (t.f a) (t.f b) ↔ g.SameBlock a b) ∧
    (∀ a b, ¬ g.SameBlock a b → t.g.nBetween (t.f a) (t.f b) ≤ 1) ∧
    (∀ o, t.f (.inl o) = .inl o)

/-- A graph with one new atom obtained from a state `g` by removing labelled components and
adding components `A` without dotted edge, at most one of them a solid edge not at the new atom:
the blocks of the lifted atoms are those of `g`, and at most one solid edge without `×`-dotted
edge joins two of them that are distinct in `g`. -/
theorem selStep2_loc_lift {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    (hRl : ∀ c ∈ R, c.label.isSome = true)
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A)) (hAd : ∀ a ∈ A, a.kind ≠ .dot)
    (hN1 : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1) :
    (∀ a b, g₁.SameBlock (liftA 1 a) (liftA 1 b) ↔ g.SameBlock a b) ∧
    (∀ a b, ¬ g.SameBlock a b → g₁.nBetween (liftA 1 a) (liftA 1 b) ≤ 1) := by
  have hdots : ∀ c, c.kind = .dot → (c ∈ rest ↔ c ∈ g.comps) := by
    intro c hk
    constructor
    · intro hc; exact hR.symm.subset (List.mem_append_right _ hc)
    · intro hc
      rcases List.mem_append.1 (hR.subset hc) with h | h
      · exfalso
        have := hS.nn.plain.labRand c hc (hRl c h)
        rw [hk] at this; simp [Kind.isRandom] at this
      · exact h
  have hblk := sameBlock_lift hdots hL hAd
  refine ⟨hblk, fun a b _ => ?_⟩
  have hpart : ∀ d ∈ rest, d.kind.isSolid = true → g₁.partB (d.map (liftA 1)) = true := by
    intro d hd hs
    have hdg : d ∈ g.comps := hR.symm.subset (List.mem_append_right _ hd)
    have hp : g.partB d = true := by
      by_contra hp
      have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hdg, hs, by simpa using hp⟩
      rw [hS.unp] at this; simp at this
    obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 hp
    have hel : e ∈ rest := by
      rcases List.mem_append.1 (hR.subset he) with h | h
      · exfalso
        have := hS.nn.plain.labRand e he (hRl e h)
        rw [hek] at this; simp [Kind.isRandom] at this
      · exact h
    refine (g₁.partB_iff _).2 ⟨e.map (liftA 1),
      hL.symm.subset (List.mem_append_left _ (List.mem_map_of_mem hel)), by simp [Comp.map, hek], ?_⟩
    rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
    · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
  have hunp : g₁.unpart.Subperm (A.filter fun c => c.kind.isSolid && !g₁.partB c) := by
    unfold Graph.unpart
    have := hL.filter (fun c => c.kind.isSolid && !g₁.partB c)
    have hnil : (rest.map (Comp.map (liftA 1))).filter (fun c => c.kind.isSolid && !g₁.partB c) =
        [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have hs : (d.map (liftA 1)).kind = d.kind := rfl
      by_cases hds : d.kind.isSolid = true
      · simp [hpart d hd hds]
      · simp [hs, hds]
    rw [List.filter_append, hnil, List.nil_append] at this
    exact this.subperm
  have hαa : ∀ u : Atom k n, ¬ g₁.SameBlock (newA 0) (liftA 1 u) := fun u h =>
    liftA_ne_newA 1 u 0 ((sameBlock_new hL hAd _).1 h)
  unfold Graph.nBetween
  refine le_trans (hunp.filter _).length_le ?_
  rw [List.filter_filter]
  refine le_trans (filter_length_le_of A _ (fun a => a.kind.isSolid && !touchN a) ?_) hN1
  intro c _ hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  obtain ⟨hb, hs, -⟩ := hc
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨hs, ?_⟩
  unfold touchN
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨fun hx => ?_, fun hy => ?_⟩
  · rcases hb with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hx] at h1
    · exact hαa a h1
    · exact hαa b h1
  · rcases hb with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [hy] at h2
    · exact hαa b h2
    · exact hαa a h2

theorem selStep2_cnt_rl (y : Atom k (n + 1)) (L : List (Comp (Atom k (n + 1)))) :
    ((L.map (rl y)).filter fun a => a.kind.isSolid && !touchN a).length =
      (L.filter fun a => a.kind.isSolid && !touchN a).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro a _
  simp only [Function.comp_apply, rl]
  split <;> rfl

theorem selStep2_cnt_two {a b : Comp (Atom k (n + 1))} (h : touchN a = true ∨ touchN b = true) :
    ([a, b].filter fun a => a.kind.isSolid && !touchN a).length ≤ 1 := by
  rcases h with h | h
  · simp [List.filter_cons, h]; split_ifs <;> simp
  · simp [List.filter_cons, h]; split_ifs <;> simp

theorem selStep2_touchN_solidC_left (ch : Charge) (v : Atom k (n + 1)) :
    touchN (solidC ch (newA 0) v) = true := by
  unfold solidC; split_ifs <;> simp [touchN, mkC]

theorem selStep2_touchN_solidC_right (ch : Charge) (u : Atom k (n + 1)) :
    touchN (solidC ch u (newA 0)) = true := by
  unfold solidC; split_ifs with h
  · simp [touchN, mkC, h]
  · simp [touchN, mkC]

/-- The pieces of `-∂_{h_{pq}}` of a component are two solid edges or weights. -/
theorem selStep2_dPieces_form {c : Comp (Atom k (n + 1))} {p q : Atom k (n + 1)}
    {ps : List (Comp (Atom k (n + 1)))} (h : c.dPieces p q = some ps) :
    ∃ cc, True ∧ ∃ a b a' b', ps = [solidC cc a b, solidC cc a' b'] := by
  rcases c with ⟨κ, a, b, mi, l⟩
  unfold Comp.dPieces at h
  cases κ with
  | G ch =>
    cases ch <;> simp only [Option.some.injEq] at h <;> exact ⟨_, trivial, _, _, _, _, h.symm⟩
  | weight ch =>
    cases ch <;> simp only [Option.some.injEq] at h <;> exact ⟨_, trivial, _, _, _, _, h.symm⟩
  | light ch =>
    cases ch <;> simp only [Option.some.injEq] at h <;> exact ⟨_, trivial, _, _, _, _, h.symm⟩
  | _ => simp at h

theorem selStep2_dPieces_nodot {c : Comp (Atom k (n + 1))} {p q : Atom k (n + 1)}
    {ps : List (Comp (Atom k (n + 1)))} (h : c.dPieces p q = some ps) :
    ∀ d ∈ ps, d.kind ≠ .dot := by
  obtain ⟨cc, -, u₁, v₁, u₂, v₂, hps⟩ := selStep2_dPieces_form h
  intro d hd
  rw [hps] at hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
  rcases hd with rfl | rfl <;> (unfold solidC; split_ifs <;> simp [mkC])

theorem selStep2_conjC_mkC {V : Type*} (κ : Kind) (u v : V) : conjC (mkC κ u v) = mkC κ.conj u v :=
  rfl

theorem selStep2_conj_coeff {m : ℕ} (g : Graph k m) : g.conj.coeff = Coeff.conj g.coeff :=
  rfl

/-- The two pieces of `-∂_{h_{pq}}` of a component, with `p` or `q` the new atom: at most one is
a solid edge not at the new atom. -/
theorem selStep2_cnt_dPieces {c : Comp (Atom k (n + 1))} {p q : Atom k (n + 1)}
    (hpq : p = newA 0 ∨ q = newA 0) {ps : List (Comp (Atom k (n + 1)))}
    (h : c.dPieces p q = some ps) :
    (ps.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1 := by
  have key : ∀ (cc : Charge) (a' b' : Atom k (n + 1)), ps = [solidC cc a' p, solidC cc q b'] →
      (ps.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1 := by
    intro cc a' b' hp
    subst hp
    refine selStep2_cnt_two ?_
    rcases hpq with rfl | rfl
    · exact Or.inl (selStep2_touchN_solidC_right _ _)
    · exact Or.inr (selStep2_touchN_solidC_left _ _)
  have key' : ∀ (cc : Charge) (a' b' : Atom k (n + 1)), ps = [solidC cc a' q, solidC cc p b'] →
      (ps.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1 := by
    intro cc a' b' hp
    subst hp
    refine selStep2_cnt_two ?_
    rcases hpq with rfl | rfl
    · exact Or.inr (selStep2_touchN_solidC_left _ _)
    · exact Or.inl (selStep2_touchN_solidC_right _ _)
  rcases c with ⟨κ, a, b, mi, l⟩
  unfold Comp.dPieces at h
  cases κ with
  | G ch =>
    cases ch <;> simp only [Option.some.injEq] at h <;>
      first | exact key _ _ _ h.symm | exact key' _ _ _ h.symm
  | weight ch =>
    cases ch <;> simp only [Option.some.injEq] at h <;>
      first | exact key _ _ _ h.symm | exact key' _ _ _ h.symm
  | light ch =>
    cases ch <;> simp only [Option.some.injEq] at h <;>
      first | exact key _ _ _ h.symm | exact key' _ _ _ h.symm
  | _ => simp at h

theorem selStep2_newH_touch {u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewH u κ a) : touchN a = true := by
  rcases h with rfl | rfl <;> simp [touchN, mkC]

/-- A term `⟨(liftCs 1 B ++ new) read inside P_x, Γ_ω⟩` of an identity inside `P_x` at a state
`g`, with `B` the core of `g` without the components `R₀`: the clauses `SelStep2OpLoc`. -/
theorem selStep2_loc_core {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R₀ B : List (Comp (Atom k n))} (hB : g.pCore.comps.Perm (R₀ ++ B))
    (hR₀ : ∀ c ∈ R₀, c.kind.isRandom = true)
    (new : List (Comp (Atom k (n + 1)))) (hnd : ∀ a ∈ new, a.kind ≠ .dot)
    (hcnt : (new.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1) (co : Coeff) :
    SelStep2OpLoc g ⟨n + 1, ⟨(liftCs 1 B ++ new).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), co⟩, liftA 1⟩ := by
  obtain ⟨hR, hL⟩ := liftOut hS.nn.lab hS.nn.plain.labRand hB new
  obtain ⟨h1, h2⟩ := selStep2_loc_lift (g₁ := ⟨(liftCs 1 B ++ new).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), co⟩) hS hR (by
        intro c hc; obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc; simp [rl, hR₀ r hr]) hL (by
        intro a ha; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
        unfold rl; split_ifs <;> exact hnd b hb) (by rw [selStep2_cnt_rl]; exact hcnt)
  exact ⟨h1, h2, fun _ => rfl⟩

/-- The terms of the shapes `ShapeE` read inside `P_x` have the clauses `SelStep2OpLoc`. -/
theorem selStep2_loc_shape {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {cs : List (Comp (Atom k (n + 1)))} (hcs : ShapeE x g.pCore.comps cs) (co : Coeff) :
    SelStep2OpLoc g ⟨n + 1, ⟨cs.map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), co⟩, liftA 1⟩ := by
  rcases hcs with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · refine selStep2_loc_core hS hB ?_ _ ?_ ?_ co
    · intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · exact Kind.isRandom_of_isSolid hr₁.1
      · exact Kind.isRandom_of_isSolid hr₂.1
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ((rfl | rfl | rfl) | ha)
      · simp [mkC]
      · obtain ⟨ch', hch'⟩ := Kind.isSolid_iff.1 hr₁.1
        rcases ha₁ with rfl | rfl <;> simp [mkC, hch']
      · obtain ⟨ch', hch'⟩ := Kind.isSolid_iff.1 hr₂.1
        rcases ha₂ with rfl | rfl <;> simp [mkC, hch']
      · obtain ⟨ch, rfl⟩ := hX a ha; simp [mkC]
    · rw [List.filter_eq_nil_iff.2]
      · simp
      intro a ha
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ((rfl | rfl | rfl) | ha)
      · simp [mkC, Kind.isSolid]
      · simp [selStep2_newH_touch ha₁]
      · simp [selStep2_newH_touch ha₂]
      · obtain ⟨ch, rfl⟩ := hX a ha; simp [mkC, Kind.isSolid]
  · have hR₀ : ∀ c ∈ [r₁], c.kind.isRandom = true := by
      intro c hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rw [hc]; exact Kind.isRandom_of_isSolid hr₁.1
    have hnew : ∀ new : List (Comp (Atom k (n + 1))), (new = [mkC (.waved .s) (liftA 1 x) (newA 0),
        a₁, b] ∨ new = [mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁]) →
        (∀ a ∈ new, a.kind ≠ .dot) ∧ (new.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1 := by
      intro new hn
      have h1 : ∀ a ∈ new, a = mkC (.waved .s) (liftA 1 x) (newA 0) ∨ a = a₁ ∨ a = b := by
        intro a ha
        rcases hn with rfl | rfl <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha <;>
          tauto
      refine ⟨fun a ha => ?_, ?_⟩
      · rcases h1 a ha with rfl | rfl | rfl
        · simp [mkC]
        · obtain ⟨ch', hch'⟩ := Kind.isSolid_iff.1 hr₁.1
          rcases ha₁ with rfl | rfl <;> simp [mkC, hch']
        · rcases hb with rfl | rfl <;> simp [mkC]
      · rw [List.filter_eq_nil_iff.2]
        · simp
        intro a ha
        rcases h1 a ha with rfl | rfl | rfl
        · simp [mkC, Kind.isSolid]
        · simp [selStep2_newH_touch ha₁]
        · simp [selStep2_newH_touch hb]
    rcases hcs with rfl | rfl
    · obtain ⟨h1, h2⟩ := hnew _ (Or.inl rfl)
      exact selStep2_loc_core hS hB hR₀ _ h1 h2 co
    · obtain ⟨h1, h2⟩ := hnew _ (Or.inr rfl)
      exact selStep2_loc_core hS hB hR₀ _ h1 h2 co
  · have hB : g.pCore.comps.Perm ([] ++ g.pCore.comps) := by simp
    refine selStep2_loc_core hS hB (by simp) _ ?_ ?_ co
    · intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> simp [mkC]
    · rw [List.filter_eq_nil_iff.2]
      · simp
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> simp [mkC, Kind.isSolid]
  · refine selStep2_loc_core hS hB ?_ _ ?_ ?_ co
    · intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · exact Kind.isRandom_of_isSolid hr.1
      · exact hc
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact selStep2_dPieces_nodot hps a ha
      · simp [mkC]
      · obtain ⟨ch', hch'⟩ := Kind.isSolid_iff.1 hr.1
        rcases he with rfl | rfl <;> simp [mkC, hch']
    · rw [List.filter_append]
      have h2 : ([mkC (.waved .s) (liftA 1 x) (newA 0), e₀].filter fun a =>
          a.kind.isSolid && !touchN a) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl
        · simp [mkC, Kind.isSolid]
        · simp [selStep2_newH_touch he]
      rw [h2, List.append_nil]
      refine selStep2_cnt_dPieces ?_ hps
      rcases hpq with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- The terms of [II, (4.24)] inside `P_x` have the clauses `SelStep2OpLoc`. -/
theorem selStep2_loc_E {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {E : TExpansion k n} (hE : multiEHat x g.pCore = some E) :
    ∀ t ∈ pLiftT x g E, SelStep2OpLoc g t := by
  intro t ht
  obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
  rcases shapes_multiEHat (noLoop_core hS) hE s hs with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, hsh⟩
  · exfalso
    have := List.any_eq_false.1 hq c hc
    simp [hl] at this
  · exact selStep2_loc_shape hS hsh co

/-- The terms of [II, (4.23)] inside `P_x` at a light weight with label `P_x` on `x` have the
clauses `SelStep2OpLoc`. -/
theorem selStep2_loc_L {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hLx : ∃ c ∈ g.comps, (∃ ch, c.kind = .light ch) ∧ c.x = x ∧ c.label = some (.P, x)) :
    ∀ t ∈ oWeightP2T x g, SelStep2OpLoc g t := by
  have hN := hS.nn
  have hlab := hN.lab
  have hlr := hN.plain.labRand
  have hsxrl : rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) =
      mkC (.waved .s) (liftA 1 x) (newA 0) := by simp [rl, mkC, Kind.isRandom]
  have keyA' : ∀ (ℓ₀ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (ch : Charge),
      g.pCore.comps.Perm ([ℓ₀] ++ B) → ℓ₀.kind = .light ch → ℓ₀.x = x →
      ∀ co (g₁ : Graph k (n + 1)), g₁ = ⟨(liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.light ch) (newA 0) (newA 0)]).map (rl (liftA 1 x)) ++
          g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      SelStep2OpLoc g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ℓ₀ B ch hB hk _ co g₁ hg₁
    subst hg₁
    refine selStep2_loc_core hS hB (fun c hc => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc; rw [hc, hk]; rfl) _ ?_ ?_ co
    · intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> simp [mkC]
    · rw [List.filter_eq_nil_iff.2]
      · simp
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> simp [mkC, Kind.isSolid]
  have keyB' : ∀ (ch : Charge) co (g₁ : Graph k (n + 1)),
      g₁ = ⟨(liftCs 1 g.pCore.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.light ch) (newA 0) (newA 0)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      SelStep2OpLoc g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ch co g₁ hg₁
    subst hg₁
    have hB : g.pCore.comps.Perm ([] ++ g.pCore.comps) := by simp
    refine selStep2_loc_core hS hB (by simp) _ ?_ ?_ co
    · intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> simp [mkC]
    · rw [List.filter_eq_nil_iff.2]
      · simp
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> simp [mkC, Kind.isSolid]
  have keyC' : ∀ (ℓ₀ c₀ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (ch : Charge),
      g.pCore.comps.Perm ([ℓ₀, c₀] ++ B) → ℓ₀.kind = .light ch → ℓ₀.x = x →
      ∀ p q : Atom k (n + 1), ((p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0)) →
      ∀ ps, (c₀.map (liftA 1)).dPieces p q = some ps →
      ∀ co (g₁ : Graph k (n + 1)), g₁ = ⟨(liftCs 1 B ++ (ps ++
        [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G ch) (newA 0) (liftA 1 x)])).map (rl (liftA 1 x)) ++
          g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      SelStep2OpLoc g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ℓ₀ c₀ B ch hB hk _ p q hpq ps hps co g₁ hg₁
    subst hg₁
    refine selStep2_loc_core hS hB ?_ _ ?_ ?_ co
    · intro d hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl
      · rw [hk]; rfl
      · have := dPieces_random hps; simpa [Comp.map] using this
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact selStep2_dPieces_nodot hps a ha
      · simp [mkC]
      · simp [mkC]
    · rw [List.filter_append]
      have h2 : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G ch) (newA 0) (liftA 1 x)].filter
          fun a => a.kind.isSolid && !touchN a) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl
        · simp [mkC, Kind.isSolid]
        · simp [mkC, touchN]
      rw [h2, List.append_nil]
      refine selStep2_cnt_dPieces ?_ hps
      rcases hpq with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  intro t ht
  unfold oWeightP2T at ht
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · rw [hE] at ht
    dsimp only at ht
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E
    · exfalso
      have hn1 : g.pCore.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
        unfold oWeightP2Pos at hE
        split at hE
        · assumption
        · cases hE
      have hn2 : g.pCore.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) =
          none := by
        unfold oWeightP2Pos at hE'
        split at hE'
        · assumption
        · cases hE'
      obtain ⟨c, hc, ⟨ch, hk⟩, hx, hl⟩ := hLx
      have hc₀ : { c with label := none } ∈ g.pCore.comps := by
        rw [pCore_comps]
        exact List.mem_map_of_mem (List.mem_filter.2 ⟨hc, by simp [coreP, hl]⟩)
      cases ch
      · have := List.findIdx?_eq_none_iff.1 hn1 _ hc₀
        simp [hk, hx] at this
      · have := List.findIdx?_eq_none_iff.1 hn2 (conjC { c with label := none })
          (by rw [Graph.conj_comps']; exact List.mem_map_of_mem hc₀)
        simp [conjC, hk, hx, Kind.conj, Charge.flip] at this
    · rw [hE'] at ht
      dsimp only at ht
      obtain ⟨s', hs', -, rfl⟩ := mem_pLiftT.1 ht
      obtain ⟨s, hs, rfl⟩ := mem_TExpansion_conj.1 hs'
      obtain ⟨i, hi, hk, hx, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE' hs
      have hcore : g.pCore.conj.comps.map conjC = g.pCore.comps := by
        rw [Graph.conj_comps', map_conjC_conjC]
      have hk' : (conjC g.pCore.conj.comps[i]).kind = .light .minus := by
        simp only [conjC, hk]; rfl
      have hx' : (conjC g.pCore.conj.comps[i]).x = x := hx
      have hpermi : g.pCore.comps.Perm ([conjC g.pCore.conj.comps[i]] ++
          (g.pCore.conj.comps.eraseIdx i).map conjC) := by
        have := (List.getElem_cons_eraseIdx_perm hi).symm.map conjC
        rw [hcore] at this
        simpa only [List.map_cons, List.singleton_append] using this
      rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
      · refine keyA' _ ((g.pCore.conj.comps.eraseIdx i).map conjC) .minus hpermi hk' hx' co.conj _
          ?_
        simp only [Graph.conj_comps', selStep2_conj_coeff, List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          selStep2_conjC_mkC, Kind.conj, Charge.flip]
      · refine keyB' .minus co.conj _ ?_
        simp only [Graph.conj_comps', selStep2_conj_coeff, List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          selStep2_conjC_mkC, Kind.conj, Charge.flip, map_conjC_conjC]
      · have hB : g.pCore.comps.Perm ([conjC g.pCore.conj.comps[i],
            conjC (g.pCore.conj.comps.eraseIdx i)[j]] ++
            ((g.pCore.conj.comps.eraseIdx i).eraseIdx j).map conjC) := by
          have := ((List.getElem_cons_eraseIdx_perm hi).symm.trans
            (List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hj).symm)).map conjC
          rw [hcore] at this
          simpa only [List.map_cons, List.cons_append, List.nil_append] using this
        have hps' : ((conjC (g.pCore.conj.comps.eraseIdx i)[j]).map (liftA 1)).dPieces
            (liftA 1 x) (newA 0) = some (ps.map conjC) := by
          rw [← dPieces_conj, conjC_map, conjC_conjC, hps]
          rfl
        refine keyC' _ _ _ .minus hB hk' hx' _ _ (Or.inr ⟨rfl, rfl⟩) _ hps' co.conj _ ?_
        simp only [Graph.conj_comps', selStep2_conj_coeff, List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          selStep2_conjC_mkC, Kind.conj, Charge.flip, List.append_assoc]
  · rw [hE] at ht
    dsimp only at ht
    obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
    obtain ⟨i, hi, hk, hx, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
    rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
    · exact keyA' _ _ .plus (List.getElem_cons_eraseIdx_perm hi).symm hk hx co _ rfl
    · exact keyB' .plus co _ rfl
    · have hB : g.pCore.comps.Perm ([g.pCore.comps[i], (g.pCore.comps.eraseIdx i)[j]] ++
          (g.pCore.comps.eraseIdx i).eraseIdx j) :=
        (List.getElem_cons_eraseIdx_perm hi).symm.trans
          (List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hj).symm)
      exact keyC' _ _ _ .plus hB hk hx _ _ (Or.inl ⟨rfl, rfl⟩) ps hps co _
        (by simp only [List.append_assoc])

end SelStep2Loc

/-! ## The identity inside `P_x` and the round -/

section SelStep2Round

variable {k n : ℕ}

/-- The terms of `O^{(x),1}_weight` inside `P_x` have the clauses `SelStep2OpLoc`. -/
theorem selStep2_loc_W {S : ℕ} {x : Atom k n} {g : Graph k n} (hS : St S x g)
    (hW : ∃ c ∈ g.pCore.comps, isRegAt x c = true) :
    ∀ t ∈ pLiftT x g (oWeight1T x g.pCore), SelStep2OpLoc g t := by
  have hN := hS.nn
  intro t ht
  rw [pLiftT_oWeight1T] at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := splitRegular_dec x _ p hp
  set R := (W₁ ++ W₂).map (rl x)
  set A := (W₁.map toLight).map (rl x)
  set L := rest.map (rl x) ++ g.pEnv
  have hgR : g.comps.Perm (R ++ L) := by
    have hp0 : g.comps.Perm (g.pCore.comps.map (rl x) ++ g.pEnv) := by
      rw [relab_pCore hN.lab hN.plain.labRand]; exact comps_perm_core g
    refine hp0.trans ?_
    have := (h1.map (rl x)).append_right g.pEnv
    simpa [R, L, List.append_assoc] using this
  have hgA : (p.1.map (rl x) ++ g.pEnv).Perm (A ++ L) := by
    have := (h2.map (rl x)).append_right g.pEnv
    simpa [A, L, List.append_assoc] using this
  -- the weights of `W₁ ++ W₂` are labelled weights on `x`
  have hW' : ∀ w ∈ W₁ ++ W₂, (∃ ch, w.kind = .weight ch) ∧ w.x = x ∧ w.y = x ∧ w.minor = [] := by
    intro w hw
    obtain ⟨⟨ch, hk⟩, hx, -⟩ := (isRegAt_iff x w).1 (h3 w hw)
    obtain ⟨d, hd, -, rfl⟩ := pCore_mem (h1.symm.subset (List.mem_append_left _ hw))
    obtain ⟨hmi, -, -, -, hwf, -⟩ := hN.plain d hd
    have hy : d.y = d.x := hwf (by simp only at hk; rw [hk]; rfl)
    exact ⟨⟨ch, hk⟩, hx, by simp only at hx ⊢; rw [hy]; exact hx, hmi⟩
  have hRw : ∀ c ∈ R, WtAt x c := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨ch, hk⟩, hx, hy, hmi⟩ := hW' w hw
    refine ⟨Or.inl ⟨ch, by simp [rl, hk, Kind.isRandom]⟩, by simp [rl, hk, Kind.isRandom, hx],
      by simp [rl, hk, Kind.isRandom, hy], by simp [rl, hk, Kind.isRandom, hmi],
      by simp [rl, hk, Kind.isRandom]⟩
  have hAw : ∀ c ∈ A, WtAt x c := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨⟨ch, hk⟩, hx, hy, hmi⟩ := hW' w (List.mem_append_left _ hw)
    refine ⟨Or.inr ⟨ch, by simp [rl, toLight, hk, Kind.isRandom]⟩,
      by simp [rl, toLight, hk, Kind.isRandom, hx], by simp [rl, toLight, hk, Kind.isRandom, hy],
      by simp [rl, toLight, hk, Kind.isRandom, hmi], by simp [rl, toLight, hk, Kind.isRandom]⟩
  have hP : g.IsPFormAt x := by
    obtain ⟨c, hc, hcr⟩ := hW
    obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hcr
    obtain ⟨d, hd, hdl, rfl⟩ := pCore_random hc (by rw [hk]; rfl)
    refine ⟨⟨d, hd, ?_⟩, hN.lab⟩
    rcases hN.lab d hd with h | h
    · rw [h] at hdl; cases hdl
    · exact h
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩
      ⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩⟩ := by
    refine .single (QElemStep.pWeight1 x g ⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩, id⟩ hP
      hN.plain ?_)
    rw [pLiftT_oWeight1T]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  have hlen : A.length ≤ R.length := by simp [A, R]
  obtain ⟨hS₁, -⟩ := weightSwap hS hgR hgA hRw hAw hlen hch
  have hdots : ∀ c : Comp (Atom k n), c.kind = .dot → (c ∈ g.comps ↔
      c ∈ (⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩ : Graph k n).comps) := by
    intro c hk
    have hnw : ¬ WtAt x c := by
      rintro ⟨⟨ch, h⟩ | ⟨ch, h⟩, -⟩ <;> rw [hk] at h <;> cases h
    change c ∈ g.comps ↔ c ∈ p.1.map (rl x) ++ g.pEnv
    rw [hgR.mem_iff, hgA.mem_iff]
    constructor
    · intro h
      rcases List.mem_append.1 h with h | h
      · exact absurd (hRw c h) hnw
      · exact List.mem_append_right _ h
    · intro h
      rcases List.mem_append.1 h with h | h
      · exact absurd (hAw c h) hnw
      · exact List.mem_append_right _ h
  refine ⟨fun a b => (Graph.sameBlock_iff_of_dots hdots a b).symm, fun a b _ => ?_, fun o => rfl⟩
  change Graph.nBetween (⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩ : Graph k n) a b ≤ 1
  unfold Graph.nBetween
  rw [hS₁.unp]
  simp

theorem selStep2_pform {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hpw : 0 < g.pw x) : g.IsPFormAt x := by
  unfold Graph.pw at hpw
  obtain ⟨c, hc, hcw⟩ := exists_pos_of_sum_pos _ _ hpw
  have hcl : c.label.isSome = true := by
    by_contra h
    rw [wBP_none (by simpa using h)] at hcw; omega
  have hlab : c.label = some (.P, x) :=
    (hS.nn.lab c hc).resolve_left (by intro h; rw [h] at hcl; cases hcl)
  exact ⟨⟨c, hc, hlab⟩, hS.nn.lab⟩

open Classical in
/-- The identity inside `P_x` at `X` ([II, §4.4, Step 2]): `O^{(x),1}_weight` if a regular weight
with label `P_X` is on `X`, else [II, (4.23)] if a light weight with label `P_X` is on `X`, else
[II, (4.24)] (`Ô^{(x)}_multi-e`). -/
def selOp (X : Atom k n) (g : Graph k n) : TExpansion k n :=
  if ∃ c ∈ g.pCore.comps, isRegAt X c = true then pLiftT X g (oWeight1T X g.pCore)
  else if ∃ c ∈ g.comps, (∃ ch, c.kind = .light ch) ∧ c.x = X ∧ c.label = some (.P, X) then
    oWeightP2T X g
  else
    match multiEHat X g.pCore with
    | some E => pLiftT X g E
    | none => []

/-- The identity inside `P_x` (the explicit list `selOp x g`): its terms have the
clauses `PStepsTermOK`, keep the components at the external atoms, are elementary steps with their
atom maps, and have the clauses `SelStep2OpLoc`. -/
theorem selStep2_op_spec {n C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hpw : 0 < g.pw x) :
    (selOp x g).length ≤ 2 ^ C + 8 * C + 8 ∧ (selOp x g).ValueEq g modelAdm ∧
      ∀ t ∈ selOp x g, PStepsTermOK (C + 5) x g t ∧ OO1 g t ∧ SelStep2Step g t ∧
        SelStep2OpLoc g t := by
  have hP₀ := selStep2_pform hS hpw
  have hN := hS.nn
  have hsz := hN.reg.size
  have hcore := pCore_length_le g
  by_cases hW : ∃ c ∈ g.pCore.comps, isRegAt x c = true
  · rw [selOp, if_pos hW]
    refine ⟨?_, valueW hN.lab hN.plain,
      fun t ht => ⟨(termsW hS hW t ht).1.mono (by omega), (opTerms_oo1 hS).1 t ht,
        SelStep2Step.pWeight1 x g t hP₀ hN.plain ht, selStep2_loc_W hS hW t ht⟩⟩
    refine (length_pLiftT_le _ _ _).trans ?_
    unfold oWeight1T
    rw [List.length_map]
    refine (splitRegular_length_le _ _).trans ?_
    have : 2 ^ g.pCore.comps.length ≤ 2 ^ C := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hL : ∃ c ∈ g.comps, (∃ ch, c.kind = .light ch) ∧ c.x = x ∧ c.label = some (.P, x)
  · rw [selOp, if_neg hW, if_pos hL]
    refine ⟨?_, valueL hN.lab hN.plain,
      fun t ht => ⟨termsL hS hL t ht, (opTerms_oo1 hS).2.1 t ht,
        SelStep2Step.pWeight2 x g t hP₀ hN.plain ht, selStep2_loc_L hS hL t ht⟩⟩
    have := oWeightP2T_length x g
    have : 0 < 2 ^ C := Nat.pow_pos (by norm_num)
    omega
  -- a labelled solid edge at `x`
  unfold Graph.pw at hpw
  obtain ⟨c, hc, hcw⟩ := exists_pos_of_sum_pos _ _ hpw
  have hcl : c.label.isSome = true := by
    by_contra h
    rw [wBP_none (by simpa using h)] at hcw; omega
  have hlab : c.label = some (.P, x) := by
    rcases hN.lab c hc with h | h
    · rw [h] at hcl; cases hcl
    · exact h
  have hS6 := hS.s6 c hc hcl
  have hc₀ : { c with label := none } ∈ g.pCore.comps := by
    rw [pCore_comps]
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨hc, by simp [coreP, hcl]⟩)
  obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .G ch := by
    rcases hck : c.kind with ch | ch | ch | ch | ⟨ch, d⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _
    · exact ⟨ch, rfl⟩
    · exfalso
      rw [wBP_W hck hcl] at hcw
      split_ifs at hcw with hb
      · have hx := hS6.1 hb
        exact hW ⟨_, hc₀, (isRegAt_iff x _).2 ⟨⟨ch, hck⟩, hx, rfl⟩⟩
      · omega
    · exfalso
      rw [wBP_L hck hcl] at hcw
      split_ifs at hcw with hb
      · exact hL ⟨c, hc, ⟨ch, hck⟩, hS6.1 hb, hlab⟩
      · omega
    all_goals first
      | exact absurd hck ((hN.plain c hc).2.1 _)
      | exact absurd hck ((hN.plain c hc).2.2.1 _ _)
      | (exfalso; rw [wBP_det (by rw [hck]; rfl)] at hcw; omega)
  have hne := hN.noLoop c hc (by rw [hk]; rfl)
  have hend : c.x = x ∨ c.y = x := by
    rw [wBP_G hk hcl] at hcw
    by_cases hb : g.SameBlock c.x x
    · exact Or.inl (hS6.1 hb)
    · by_cases hb' : g.SameBlock c.y x
      · exact Or.inr (hS6.2 hb')
      · simp [hb, hb'] at hcw
  have hedge : ∃ ch' out, g.pCore.edgeIdx x ch' out ≠ [] := by
    obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hc₀
    have hz : ({ c with label := none }, j) ∈ g.pCore.comps.zipIdx := by
      rw [← hjc]; exact mem_zip_of_get (List.getElem?_eq_getElem hj)
    rcases hend with hx | hy
    · refine ⟨ch, true, List.ne_nil_of_mem (a := j) ?_⟩
      rw [edgeIdx_eq]
      refine List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hz, ?_⟩, rfl⟩
      simp [ep, hk, hx, (hx ▸ hne : x ≠ c.y).symm]
    · refine ⟨ch, false, List.ne_nil_of_mem (a := j) ?_⟩
      rw [edgeIdx_eq]
      refine List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hz, ?_⟩, rfl⟩
      have : c.x ≠ x := fun h => hne (h.trans hy.symm)
      simp [ep, hk, hy, this]
  obtain ⟨E, hE⟩ := multiEHat_isSome (XP_core hS) hedge
  have hP : g.IsPFormAt x := ⟨⟨c, hc, hlab⟩, hN.lab⟩
  rw [selOp, if_neg hW, if_neg hL, hE]
  refine ⟨?_, valueE hN.lab hN.plain hN.noLoop hE,
    fun t ht => ⟨termsE hS hP hE t ht, (opTerms_oo1 hS).2.2 E hE t ht,
      SelStep2Step.pMultiE x g E t hP hN.plain hE ht, selStep2_loc_E hS hE t ht⟩⟩
  have := multiEHat_length hE
  refine (length_pLiftT_le _ _ _).trans ?_
  have : 0 < 2 ^ C := Nat.pow_pos (by norm_num)
  omega

/-- The normalization of a term followed by the moves of the labelled components to the image of
`x`. -/
def selStep2_normReb (X : Atom k n) (g : Graph k n) : TExpansion k n :=
  (selNorm g).map fun u => u.comp (Tracked.self (selRebase (u.f X) u.g))

/-- One round of [II, §4.4, Step 2] at `X`: the identity inside `P_X` (`selOp`), the
normalization (`selNorm`) and the moves of the labelled components of the block of the image of
`X` to it (`selRebase`), with the atom maps composed. -/
def selRound (X : Atom k n) (g : Graph k n) : TExpansion k n :=
  (selOp X g).flatMap fun t => (selStep2_normReb (t.f X) t.g).map t.comp

theorem selStep2_valR_map {m : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) (e : Fin k → ι) (F : TExpansion k m) (φ : Tracked k m → Tracked k m)
    (h : ∀ u ∈ F, (φ u).g.valR PF D e = u.g.valR PF D e) :
    (TExpansion.forget (F.map φ)).valR PF D e = (TExpansion.forget F).valR PF D e := by
  induction F with
  | nil => rfl
  | cons u F ih =>
    rw [List.map_cons, TExpansion.valR_cons, TExpansion.valR_cons, h u (List.mem_cons_self ..),
      ih fun v hv => h v (List.mem_cons_of_mem _ hv)]

/-- The normalization and the moves to `x` applied to a term with the clauses `PStepsTermOK`
(the explicit list): the outputs are states of the construction; the scaling
order does not drop, and if it is unchanged the weighted number of labelled weights and edge ends
at `x` drops; the components at the external atoms and the external atoms are kept; the history;
when the blocks of two atoms are joined, `I ≥ 1` identifications were made, and for `I = 1` the
removed solid edges join the blocks of the two atoms. -/
theorem selStep2_roundTerm {C₁ : ℕ} {x : Atom k n} {g : Graph k n} {t : Tracked k n}
    (h : PStepsTermOK C₁ x g t) :
    (selStep2_normReb (t.f x) t.g).length ≤ 2 ^ C₁ ∧
      (selStep2_normReb (t.f x) t.g).ValueEq t.g modelAdm ∧
      ∀ s ∈ selStep2_normReb (t.f x) t.g, St (6 * C₁) (s.f (t.f x)) s.g ∧
        SR t.g (t.f x) s ∧ g.ord ≤ s.g.ord ∧
        (s.g.ord = g.ord → s.g.pw (s.f (t.f x)) < g.pw x) ∧ OO1 t.g s ∧ SelStep2Hist t.g s ∧
        (∀ o, s.f (.inl o) = .inl o) ∧
        (∀ a b, ¬ t.g.SameBlock a b → s.g.SameBlock (s.f a) (s.f b) →
          ∃ I E : ℕ, 1 ≤ I ∧ s.g.ord + E = t.g.ord + 2 * I ∧ E ≤ t.g.unpart.length ∧
            (I = 1 → E ≤ t.g.nBetween a b)) := by
  have hmC : t.g.unpart.length + t.g.orph.length ≤ C₁ := h.bnd
  obtain ⟨hlen, hval, hF⟩ := selStep2_normF_spec (t.g.unpart.length + t.g.orph.length) t.g h.nn
    le_rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [selStep2_normReb, List.length_map]
    exact hlen.trans (Nat.pow_le_pow_right (by norm_num) hmC)
  · intro Ω ι _ _ PF D hA e
    rw [← hval Ω ι PF D hA e]
    refine selStep2_valR_map PF D e _ _ fun u hu => ?_
    obtain ⟨hN, -⟩ := hF u hu
    obtain ⟨-, -, -, -, -, hv, -⟩ := selStep2_rebF_spec (u.g.viol (u.f (t.f x))) u.g hN.nn hN.unp
      hN.orp le_rfl
    exact hv Ω ι PF D e
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hN, -⟩ := hF u hu
    have hsz := hN.nn.reg.size
    obtain ⟨-, hS', hordw, hpww, -, -, hsrw, -, hK1, hh, hbl⟩ :=
      selStep2_rebF_spec (u.g.viol (u.f (t.f x))) u.g hN.nn hN.unp hN.orp le_rfl
    have hv := Graph.viol_le u.g (u.f (t.f x))
    obtain ⟨I, Eu, hcount, hEU, hI0, hIb, hI1, hpm⟩ := hN.count
    refine ⟨hS'.mono (by omega), SR.trans hN.sr hN.nn.plain.labRand hsrw, ?_, ?_,
      OO1.comp hN.oo (OO1.of_keep hK1), hN.hist.trans hh, fun o => hN.inl o, ?_⟩
    · show g.ord ≤ (selRebase (u.f (t.f x)) u.g).ord
      rw [show selRebase (u.f (t.f x)) u.g =
        selStep2_rebF (u.f (t.f x)) (u.g.viol (u.f (t.f x))) u.g from rfl, hordw]
      have hU := h.unp
      have hord := h.ord
      rcases Nat.lt_or_ge I 2 with hI | hI
      · interval_cases I
        · obtain ⟨hE0, -⟩ := hI0 rfl
          rw [hE0] at hcount; push_cast at hcount; linarith
        · have := hIb 2 h.beta rfl
          push_cast at hcount
          have : (Eu : ℤ) ≤ 2 := by exact_mod_cast this
          linarith
      · have : (Eu : ℤ) ≤ 3 := by exact_mod_cast hEU.trans hU
        have : (I : ℤ) ≥ 2 := by exact_mod_cast hI
        push_cast at hcount; linarith
    · intro heq
      change (selRebase (u.f (t.f x)) u.g).ord = g.ord at heq
      show (selRebase (u.f (t.f x)) u.g).pw (u.f (t.f x)) < g.pw x
      rw [show selRebase (u.f (t.f x)) u.g =
        selStep2_rebF (u.f (t.f x)) (u.g.viol (u.f (t.f x))) u.g from rfl] at heq ⊢
      rw [hordw] at heq
      rw [hpww]
      have hU := h.unp
      have hord := h.ord
      rcases Nat.lt_or_ge I 2 with hI | hI
      · interval_cases I
        · obtain ⟨hE0, hpw0⟩ := hI0 rfl
          rw [hE0] at hcount; push_cast at hcount
          rw [hpw0]
          exact (h.eq (by linarith)).1
        · have hE2 := hIb 2 h.beta rfl
          push_cast at hcount
          have hE2' : (Eu : ℤ) ≤ 2 := by exact_mod_cast hE2
          have hteq : t.g.ord = g.ord := by linarith
          have hEu2 : Eu = 2 := by
            have : (Eu : ℤ) = 2 := by linarith
            exact_mod_cast this
          obtain ⟨hlt, hb⟩ := h.eq hteq
          rcases hb with hb | hb
          · have := hIb 1 hb rfl; omega
          · rw [hI1 rfl hEu2 hb]; exact hlt
      · exfalso
        have : (Eu : ℤ) ≤ 3 := by exact_mod_cast hEU.trans hU
        have : (I : ℤ) ≥ 2 := by exact_mod_cast hI
        push_cast at hcount
        linarith
    · intro a b hab hj
      have hj' : u.g.SameBlock (u.f a) (u.f b) := (hbl _ _).1 hj
      obtain ⟨h1, h2⟩ := hpm a b hab hj'
      refine ⟨I, Eu, h1, ?_, hEU, h2⟩
      show (selRebase (u.f (t.f x)) u.g).ord + Eu = t.g.ord + 2 * I
      rw [show selRebase (u.f (t.f x)) u.g =
        selStep2_rebF (u.f (t.f x)) (u.g.viol (u.f (t.f x))) u.g from rfl, hordw]
      exact hcount

end SelStep2Round

section SelStep2RoundMain

variable {k n : ℕ}

theorem selStep2_mem_round {x : Atom k n} {g : Graph k n} {s : Tracked k n}
    (hs : s ∈ selRound x g) : ∃ t ∈ selOp x g, ∃ u ∈ selStep2_normReb (t.f x) t.g, s = t.comp u := by
  obtain ⟨t, ht, hs'⟩ := List.mem_flatMap.1 hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs'
  exact ⟨t, ht, u, hu, rfl⟩

/-- **One round of the Step 2 of the `Q`-expansions** ([II, Lemma 4.13], one application of
[II, (4.23), (4.24)] or `O^{(x),1}_weight` inside `P_x` followed by the normalization and the
moves of the labelled components to `x`): at a state `g` with a labelled weight or edge end at the
block of `x`, `selRound x g` has at most `(2 ^ C + 8 C + 8) 2 ^ (C + 5)` terms with the value of
`g`; every output `s` is a state (`St (6 (C + 5))`), with the clauses `SR`; its scaling order is at
least that of `g`, and if equal, the weighted number of labelled weights and edge ends at the
image of `x` drops; its paper scaling order is at least that of `g`, and strictly larger unless
that number drops; the components at the external atoms are kept (`MainOO1`), the external atoms
are fixed, and the history is a chain of elementary steps with their atom maps. -/
theorem selStep2_round {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hpw : 0 < g.pw x) :
    (selRound x g).length ≤ (2 ^ C + 8 * C + 8) * 2 ^ (C + 5) ∧
      (selRound x g).ValueEq g modelAdm ∧
      ∀ s ∈ selRound x g, St (6 * (C + 5)) (s.f x) s.g ∧ SR g x s ∧ g.ord ≤ s.g.ord ∧
        (s.g.ord = g.ord → s.g.pw (s.f x) < g.pw x) ∧ g.paperOrd ≤ s.g.paperOrd ∧
        (g.paperOrd < s.g.paperOrd ∨ (g.paperOrd = s.g.paperOrd ∧ s.g.pw (s.f x) < g.pw x)) ∧
        MainOO1 g s ∧ SelStep2Hist g s ∧ (∀ o, s.f (.inl o) = .inl o) := by
  obtain ⟨hlen, hval, hF₀⟩ := selStep2_op_spec hS hpw
  set Fs : List (Σ t : Tracked k n, TExpansion k t.nOut) :=
    (selOp x g).map fun t => ⟨t, selStep2_normReb (t.f x) t.g⟩ with hFs
  have hR : selRound x g = Fs.flatMap fun p => p.2.map p.1.comp := by
    simp only [selRound, hFs, List.flatMap_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]
    refine (TExpansion.length_bind Fs (2 ^ (C + 5)) fun p hp => ?_).trans ?_
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
      exact (selStep2_roundTerm (hF₀ t ht).1).1
    · rw [hFs, List.length_map]
      exact Nat.mul_le_mul_right _ hlen
  · rw [hR]
    refine TExpansion.valueEq_bind g (selOp x g) hval Fs (by
      rw [hFs, List.map_map]; exact List.map_id' _) fun p hp => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
    exact (selStep2_roundTerm (hF₀ t ht).1).2.1
  · intro s hs
    obtain ⟨t, ht, u, hu, rfl⟩ := selStep2_mem_round hs
    obtain ⟨hT, hoo, hstep, hloc⟩ := hF₀ t ht
    obtain ⟨hSu, hsru, hord, hpw', hoou, hhu, hinlu, -⟩ := (selStep2_roundTerm hT).2.2 u hu
    have hsr : SR g x (t.comp u) := SR.trans hT.sr hT.nn.plain.labRand hsru
    have hexc := hsr.exc
    have hp : g.paperOrd + (2 * (excL g.comps - excL u.g.comps)) + (u.g.ord - g.ord) =
        (t.comp u).g.paperOrd := by
      rw [selStep2_paperOrd_eq, selStep2_paperOrd_eq]
      change _ = u.g.ord - 2 * excL u.g.comps
      ring
    have hexc' : excL u.g.comps ≤ excL g.comps := hexc
    have hord' : g.ord ≤ u.g.ord := hord
    refine ⟨hSu, hsr, hord, hpw', by linarith, ?_, selStep2_mainOO1 (OO1.comp hoo hoou),
      (SelStep2Hist.single hstep).trans hhu, fun o => ?_⟩
    · by_cases hlt : g.paperOrd < (t.comp u).g.paperOrd
      · exact Or.inl hlt
      · right
        have he : u.g.ord = g.ord := by linarith
        exact ⟨by linarith, hpw' he⟩
    · show u.f (t.f (.inl o)) = .inl o
      rw [hloc.2.2 o, hinlu o]

/-- **The `⊕`–`⊖` block in a round** ([II, §4.4, Step 2]): for `k = 3`, an output graph
of `selRound x g` with `⊕` and `⊖` in one dotted block, while they are in distinct blocks of `g`,
has paper scaling order at least that of `g` plus `1`. -/
theorem selStep2_round_pmBlock {C : ℕ} {x : Atom 3 n} {g : Graph 3 n} (hS : St C x g)
    (hpw : 0 < g.pw x) :
    ∀ s ∈ selRound x g, ¬ g.PMBlock → s.g.PMBlock → g.paperOrd + 1 ≤ s.g.paperOrd := by
  intro s hs hn hpm
  obtain ⟨-, -, hF₀⟩ := selStep2_op_spec hS hpw
  obtain ⟨t, ht, u, hu, rfl⟩ := selStep2_mem_round hs
  obtain ⟨hT, -, -, hloc⟩ := hF₀ t ht
  obtain ⟨-, hsru, -, -, -, -, hinlu, hjoin⟩ := (selStep2_roundTerm hT).2.2 u hu
  rw [Graph.pmBlock_iff_sameBlock] at hn hpm
  have hn' : ¬ t.g.SameBlock (t.f (.inl 1)) (t.f (.inl 2)) := fun h => hn ((hloc.1 _ _).1 h)
  have hj : u.g.SameBlock (u.f (t.f (.inl 1))) (u.f (t.f (.inl 2))) := by
    rw [hloc.2.2 1, hloc.2.2 2, hinlu 1, hinlu 2]; exact hpm
  obtain ⟨I, E, hI, hcount, hEU, hI1⟩ := hjoin _ _ hn' hj
  have hsr : SR g x (t.comp u) := SR.trans hT.sr hT.nn.plain.labRand hsru
  have hexc : excL u.g.comps ≤ excL g.comps := hsr.exc
  have hU := hT.unp
  have hord := hT.ord
  have hnb := hloc.2.1 _ _ hn
  rw [selStep2_paperOrd_eq, selStep2_paperOrd_eq]
  change g.ord - 2 * excL g.comps + 1 ≤ u.g.ord - 2 * excL u.g.comps
  have hE : (E : ℤ) + 2 ≤ 2 * I + 1 := by
    rcases Nat.lt_or_ge I 2 with hI2 | hI2
    · have hI1' : I = 1 := by omega
      have := (hI1 hI1').trans hnb
      subst hI1'
      push_cast; omega
    · have : E ≤ 3 := hEU.trans hU
      push_cast; omega
  push_cast at hcount
  linarith

end SelStep2RoundMain

section SelStep2Inst

end SelStep2Inst

end RBM8D.Graphs
