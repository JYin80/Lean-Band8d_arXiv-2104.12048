module

public import RBM8D.Graph.QExp.SelStep2
public import RBM8D.Graph.QExp.SelStep1

@[expose] public section

/-!
# The rounds of [II, Lemma 4.15] with deterministic choices

[II, Lemmas 4.13, 4.14] iterated as in the proof of [II, Lemma 4.15], for a function of the graph.
On a graph `Γ = Γ_ω P_x(𝒢)` (`X = x` internal), `selRounds D d X Γ` is the empty sum if `Γ` has a
`×`-dotted edge inside a block; otherwise it is `selInit` (`O_merge`, the removal of the redundant
dotted edges, the moves of the labelled components to `x`) followed by `selRoundsSt` at the state
reached. At a state `s` of the construction, `selRoundsSt D d X s` is
* `s` itself, if its paper scaling order is `> D` or it has no labels;
* otherwise, if a labelled weight or edge end is at the block of `x`, one round `selRound` of
  [II, §4.4, Step 2], then `selRoundsSt` again at every term whose paper scaling order is higher,
  or equal with a smaller weighted number of labelled weights and edge ends at the image of `x`;
* otherwise the run `selStep3 d` of [II, Lemma 4.14]; a term of `P`-form at the image of `x` with
  a labelled weight or edge attached to its block and a higher paper scaling order goes through
  `selInit` and `selRoundsSt` again, every other term is kept.

Every choice reads only the graph. The error order `D` enters only through the first case, and
the Taylor degree `d` only through `selStep3 d`.

The main statements are `selRounds_clauses` (the length, the value, the clauses `Rel` and
`MainOO1`, and the three forms of the output graphs), and `selRounds_hist` (every output graph has the history
`SelRoundsHist`: a chain of the histories `SelStep2Hist` and `SelStep3Hist` of the pieces).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The rounds -/

section SelRoundsRun

variable {k : ℕ}

open Classical in
/-- The rounds of [II, §4.4, Steps 2, 3] at a state `s` of the construction at `X`, with error
order `D` and Taylor degree `d`: `s` itself if `D < paperOrd s` or `s` has no labels; otherwise,
if `0 < pw s X`, the round `selRound X s` and the rounds again at every term whose paper scaling
order is higher, or equal with a smaller `pw` at the image of `X` (every other term is kept);
otherwise `selStep3 d X s`, and at every term that is plain, of `P`-form at the image of `X` with
a labelled weight or edge attached to its block, and of higher paper scaling order, `selInit` and
the rounds again at the terms of higher paper scaling order (every other term is kept; a term
with a `×`-dotted edge inside a block is dropped). -/
def selRoundsSt (D d : ℕ) {n : ℕ} (X : Atom k n) (s : Graph k n) : TExpansion k n :=
  if hs : (D : ℤ) < s.paperOrd ∨ s.LabelFree then [Tracked.self s]
  else if 0 < s.pw X then
    (selRound X s).flatMap fun t =>
      (if _h : s.paperOrd < t.g.paperOrd ∨
          (s.paperOrd = t.g.paperOrd ∧ t.g.pw (t.f X) < s.pw X) then
        selRoundsSt D d (t.f X) t.g
      else [Tracked.self t.g]).map t.comp
  else
    (selStep3 d X s).flatMap fun c =>
      (if c.g.Plain ∧ c.g.IsPFormAt (c.f X) ∧ ¬ c.g.LabelledFreeAtBlock (c.f X) ∧
          s.paperOrd < c.g.paperOrd then
        (if c.g.XdotApart then
          (selInit (c.f X) c.g).flatMap fun u =>
            (if _h : s.paperOrd < u.g.paperOrd then selRoundsSt D d (u.f (c.f X)) u.g
            else [Tracked.self u.g]).map u.comp
        else [])
      else [Tracked.self c.g]).map c.comp
termination_by (((D : ℤ) + 1 - s.paperOrd).toNat, s.pw X)
decreasing_by
  all_goals
    simp only [not_or, not_lt] at hs
    rw [Prod.lex_def]
  · rcases _h with h | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨by rw [h1], h2⟩
  · left; omega

open Classical in
/-- The rounds of [II, §4.4, Steps 2, 3] on a graph `Γ = Γ_ω P_X(𝒢)` with error order `D` and
Taylor degree `d`: the empty sum if `Γ` has a `×`-dotted edge inside a block; otherwise
`selInit X Γ`, then `selRoundsSt D d` at the state reached. -/
def selRounds (D d : ℕ) {n : ℕ} (X : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if Γ.XdotApart then (selInit X Γ).flatMap fun u => (selRoundsSt D d (u.f X) u.g).map u.comp
  else []

/-- The history of an output graph `t` of the rounds from `Γ` at `X` with Taylor degree `d`: a
chain of pieces, each a history `SelStep2Hist` of `selInit` or `selRound`, or a history
`SelStep3Hist d` of `selStep3 d` at the image of `X`; the atom map of `t` is the composite of the
atom maps of the pieces. -/
inductive SelRoundsHist (d : ℕ) : {n : ℕ} → Atom k n → Graph k n → Tracked k n → Prop
  | refl {n : ℕ} (X : Atom k n) (Γ : Graph k n) : SelRoundsHist d X Γ (Tracked.self Γ)
  | step2 {n : ℕ} {X : Atom k n} {Γ : Graph k n} {t : Tracked k n} {s : Tracked k t.nOut}
      (h : SelStep2Hist Γ t) (hs : SelRoundsHist d (t.f X) t.g s) :
      SelRoundsHist d X Γ (t.comp s)
  | step3 {n : ℕ} {X : Atom k n} {Γ : Graph k n} {t : Tracked k n} {s : Tracked k t.nOut}
      (h : SelStep3Hist d X Γ t) (hs : SelRoundsHist d (t.f X) t.g s) :
      SelRoundsHist d X Γ (t.comp s)

end SelRoundsRun

/-! ## Composition of the clauses -/

section SelRoundsComp

variable {k : ℕ}

/-- Expanding every term of `R` by a formal sum with the value of the term. -/
private theorem selRounds_bind {n A B K : ℕ} {g : Graph k n} (R : TExpansion k n)
    (F : (t : Tracked k n) → TExpansion k t.nOut) (P : Tracked k n → Prop)
    (hR : R.ValueEq g modelAdm) (hRl : R.length ≤ A) (hK : A * B ≤ K)
    (h : ∀ t ∈ R, (F t).length ≤ B ∧ (F t).ValueEq t.g modelAdm ∧ ∀ u ∈ F t, P (t.comp u)) :
    (R.flatMap fun t => (F t).map t.comp).length ≤ K ∧
      TExpansion.ValueEq (R.flatMap fun t => (F t).map t.comp) g modelAdm ∧
      ∀ s ∈ R.flatMap (fun t => (F t).map t.comp), P s := by
  let Fs : List (Σ t : Tracked k n, TExpansion k t.nOut) := R.map fun t => ⟨t, F t⟩
  have hE : (R.flatMap fun t => (F t).map t.comp) = Fs.flatMap fun p => p.2.map p.1.comp := by
    simp only [Fs, List.flatMap_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]
    refine (TExpansion.length_bind Fs B fun p hp => ?_).trans ?_
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
      exact (h t ht).1
    · simp only [Fs, List.length_map]
      exact (Nat.mul_le_mul_right _ hRl).trans hK
  · rw [hE]
    refine TExpansion.valueEq_bind g R hR Fs ?_ fun p hp => ?_
    · simp only [Fs, List.map_map]
      exact List.map_id' _
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
      exact (h t ht).2.1
  · intro s hs
    obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    exact (h t ht).2.2 u hu

/-- A single tracked graph with the value of `g`. -/
private theorem selRounds_valueEq_single {n : ℕ} {g : Graph k n} {u : Tracked k n}
    (h : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι), u.g.valR PF D e = g.valR PF D e) :
    TExpansion.ValueEq [u] g modelAdm := by
  intro Ω ι _ _ PF D _ e
  rw [← h Ω ι PF D e]
  funext ω
  simp [TExpansion.forget, Expansion.valR]

/-- The paper scaling order does not drop along `Rel`. -/
theorem selRounds_paperOrd_le {C n : ℕ} {X : Atom k n} {g : Graph k n} {t : Tracked k n}
    (h : Rel C X g t) : g.paperOrd ≤ t.g.paperOrd := by
  have h1 := h.1.2.1
  have h2 := h.1.2.2.2.1
  unfold Graph.paperOrd
  linarith

/-- An output of a round or of `selInit` that is a state of the construction, with the clauses
`SR` and a scaling order at least that of `g`, has the clauses `Rel`. -/
private theorem selRounds_rel_of_sr {C n : ℕ} {X : Atom k n} {g : Graph k n} {t : Tracked k n}
    (hS : St C (t.f X) t.g) (hsr : SR g X t) (hord : g.ord ≤ t.g.ord) : Rel C X g t :=
  ⟨⟨hS.normal, hord, hS.nn.xa, by rw [selStep2_dotExcess_eq, selStep2_dotExcess_eq]; exact hsr.exc,
    hsr.fx, hsr.dc, hsr.chain⟩, hsr.carries, hsr.newWaved⟩

/-- The clauses of an output graph `t` of the rounds at `s`: `Rel`, `MainOO1`, one of the three
forms, and the history. -/
private def SelRoundsOut (C' D d : ℕ) {n : ℕ} (X : Atom k n) (s : Graph k n) (t : Tracked k n) :
    Prop :=
  Rel C' X s t ∧ MainOO1 s t ∧
    ((t.g.Plain ∧ t.g.LabelFree) ∨ (t.g.Plain ∧ (D : ℤ) < t.g.paperOrd) ∨
      (t.g.Clean ∧ s.paperOrd + d + 1 ≤ t.g.paperOrd)) ∧ SelRoundsHist d X s t

private theorem SelRoundsOut.mono {C₁ C₂ D d n : ℕ} {X : Atom k n} {s : Graph k n}
    {t : Tracked k n} (h : SelRoundsOut C₁ D d X s t) (hC : C₁ ≤ C₂) :
    SelRoundsOut C₂ D d X s t :=
  ⟨h.1.mono hC, h.2⟩

/-- The clauses of an output of the rounds at `t.g`, composed with a piece `t` of `g`. -/
private theorem selRounds_out_comp {C₁ C' D d n : ℕ} {X : Atom k n} {g : Graph k n}
    {t : Tracked k n} {u : Tracked k t.nOut} (hR : Rel C₁ X g t) (hp : t.g.Plain)
    (hoo : MainOO1 g t)
    (hH : ∀ w : Tracked k t.nOut, SelRoundsHist d (t.f X) t.g w → SelRoundsHist d X g (t.comp w))
    (hu : SelRoundsOut C' D d (t.f X) t.g u) : SelRoundsOut C' D d X g (t.comp u) := by
  obtain ⟨hRu, hoou, hform, hhu⟩ := hu
  have hpo := selRounds_paperOrd_le hR
  refine ⟨hR.trans hp hRu, hoo.comp hoou, ?_, hH u hhu⟩
  rcases hform with h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h1, by
      change t.g.paperOrd + d + 1 ≤ u.g.paperOrd at h2
      change g.paperOrd + d + 1 ≤ u.g.paperOrd
      linarith⟩)

end SelRoundsComp

/-! ## The clauses at a state of the construction -/

section SelRoundsMain

variable {k : ℕ}

/-- The clauses of `selRoundsSt` at the states with bound `C`, at most `L` levels of paper
scaling order below `D + 1`, and `pw < P`. -/
private def SelRoundsGood (k D e L P C : ℕ) : Prop :=
  ∃ K C' : ℕ, ∀ (n : ℕ) (X : Atom k n) (s : Graph k n) (d : ℕ), d ≤ e → St C X s →
    ((D : ℤ) + 1 - s.paperOrd).toNat ≤ L → s.pw X < P →
    (selRoundsSt D d X s).length ≤ K ∧ (selRoundsSt D d X s).ValueEq s modelAdm ∧
      ∀ t ∈ selRoundsSt D d X s, SelRoundsOut C' D d X s t

private theorem selRoundsSt_stop {D d n : ℕ} {X : Atom k n} {s : Graph k n}
    (h : (D : ℤ) < s.paperOrd ∨ s.LabelFree) : selRoundsSt D d X s = [Tracked.self s] := by
  rw [selRoundsSt, dite_eq_left h]

/-- The output `s` itself. -/
private theorem selRounds_self {C C' D d n : ℕ} {X : Atom k n} {s : Graph k n} (hS : St C X s)
    (hC : C ≤ C') (h : (D : ℤ) < s.paperOrd ∨ s.LabelFree) :
    (selRoundsSt D d X s).length ≤ 1 ∧ (selRoundsSt D d X s).ValueEq s modelAdm ∧
      ∀ t ∈ selRoundsSt D d X s, SelRoundsOut C' D d X s t := by
  rw [selRoundsSt_stop h]
  refine ⟨by simp, valueEq_self s, fun t ht => ?_⟩
  rw [List.mem_singleton] at ht
  subst ht
  refine ⟨(Rel.self hS.normal hS.nn.hx hS.nn.xa).mono hC, MainOO1.self s, ?_, .refl X s⟩
  rcases h with h | h
  · exact Or.inr (Or.inl ⟨hS.nn.plain, h⟩)
  · exact Or.inl ⟨hS.nn.plain, h⟩

/-- The pass from `L` levels to `L + 1` levels, and from `pw < P` to `pw < P + 1`. -/
private theorem selRounds_node {D e L P : ℕ} (ihL : ∀ P₁ C₁, SelRoundsGood k D e L P₁ C₁)
    (ihP : ∀ C₁, SelRoundsGood k D e (L + 1) P C₁) (C : ℕ) :
    SelRoundsGood k D e (L + 1) (P + 1) C := by
  obtain ⟨Ka, Ca, ha⟩ := ihL (4 * (6 * (C + 5)) + 1) (6 * (C + 5))
  obtain ⟨Kb, Cb, hb⟩ := ihP (6 * (C + 5))
  obtain ⟨K₃, C₃, h3⟩ := selStep3_clauses' k C e
  obtain ⟨Kc, Cc, hc⟩ := ihL (4 * (3 * C₃) + 1) (3 * C₃)
  refine ⟨(2 ^ C + 8 * C + 8) * 2 ^ (C + 5) * (Ka + Kb + 1) + K₃ * (Kc + 1) + 1,
    C + 6 * (C + 5) + Ca + Cb + 3 * C₃ + Cc, ?_⟩
  intro n X s d hde hS hL hP
  by_cases hstop : (D : ℤ) < s.paperOrd ∨ s.LabelFree
  · obtain ⟨h1, h2, h3⟩ := selRounds_self (D := D) (d := d) hS (C' := C + 6 * (C + 5) + Ca + Cb +
      3 * C₃ + Cc) (by omega) hstop
    exact ⟨h1.trans (by omega), h2, h3⟩
  have hD : s.paperOrd ≤ D := by
    by_contra h
    exact hstop (Or.inl (by omega))
  have hx := hS.nn.hx
  by_cases hpw : 0 < s.pw X
  · -- one round of Step 2
    rw [selRoundsSt, dite_eq_right hstop, ite_eq_left hpw]
    obtain ⟨hlen, hval, hround⟩ := selStep2_round hS hpw
    refine selRounds_bind (A := (2 ^ C + 8 * C + 8) * 2 ^ (C + 5)) (B := Ka + Kb + 1) _ _ _ hval hlen (by
      have := Nat.zero_le (K₃ * (Kc + 1)); omega) fun t ht => ?_
    obtain ⟨hSt, hsr, hord, -, -, hguard, hoo, hh, -⟩ := hround t ht
    rw [dite_eq_left hguard]
    have hRt : Rel (6 * (C + 5)) X s t := selRounds_rel_of_sr hSt hsr hord
    have hpwt := t.g.pw_le (t.f X)
    have hsz := hSt.nn.reg.size
    by_cases hlt : s.paperOrd < t.g.paperOrd
    · obtain ⟨hl, hv, ho⟩ := ha t.nOut (t.f X) t.g d hde hSt (by omega) (by omega)
      refine ⟨by omega, hv, fun u hu => selRounds_out_comp hRt hSt.nn.plain hoo
        (fun w hw => .step2 hh hw) ((ho u hu).mono (by omega))⟩
    · obtain ⟨heq, hpwlt⟩ := hguard.resolve_left hlt
      obtain ⟨hl, hv, ho⟩ := hb t.nOut (t.f X) t.g d hde hSt (by omega) (by omega)
      refine ⟨by omega, hv, fun u hu => selRounds_out_comp hRt hSt.nn.plain hoo
        (fun w hw => .step2 hh hw) ((ho u hu).mono (by omega))⟩
  · -- Step 3
    rw [selRoundsSt, dite_eq_right hstop, ite_eq_right hpw]
    have hpw0 : s.pw X = 0 := by omega
    obtain ⟨x₀, rfl⟩ := exists_inr_of_isRight hx
    have hPF : s.IsPFormAt (.inr x₀) := by
      refine ⟨?_, hS.nn.lab⟩
      have hnl : ¬ s.LabelFree := fun h => hstop (Or.inr h)
      unfold Graph.LabelFree at hnl
      push Not at hnl
      obtain ⟨c, hc, hne⟩ := hnl
      exact ⟨c, hc, (hS.nn.lab c hc).resolve_left hne⟩
    obtain ⟨hlen, hval, hout⟩ := h3 n x₀ s d hde hS.normal hPF hS.nn.plain
      (labelledFree_of_pw hS.nn.plain hpw0)
    refine selRounds_bind (A := K₃) (B := Kc + 1) _ _ _ hval hlen (by omega) fun c hc' => ?_
    obtain ⟨⟨hB, hCa, hW⟩, hoo3, hform, hh3⟩ := hout c hc'
    have hRc : Rel C₃ (.inr x₀) s c := ⟨hB, hCa, hW⟩
    have hoo : MainOO1 s c := hoo3
    by_cases hcls : c.g.Plain ∧ c.g.IsPFormAt (c.f (.inr x₀)) ∧
        ¬ c.g.LabelledFreeAtBlock (c.f (.inr x₀)) ∧ s.paperOrd < c.g.paperOrd
    · -- a term of `P`-form: `selInit` and the rounds again
      rw [ite_eq_left hcls, ite_eq_left hB.2.2.1]
      obtain ⟨u, hsel, hSu, hsru, hordu, hpou, hvalu, hoou, hhu, -, -⟩ :=
        selStep2_init hB.2.2.2.2.1 hB.1 hcls.1 hcls.2.1.2 hB.2.2.1
      rw [hsel]
      have hRu : Rel (3 * C₃) (c.f (.inr x₀)) c.g u := selRounds_rel_of_sr hSu hsru hordu.ge
      have hpwu := u.g.pw_le (u.f (c.f (.inr x₀)))
      have hszu := hSu.nn.reg.size
      have hlt : s.paperOrd < u.g.paperOrd := by rw [hpou]; exact hcls.2.2.2
      obtain ⟨hl, hv, ho⟩ := selRounds_bind (A := 1) (B := Kc) (K := Kc) [u]
        (fun u' => if _h : s.paperOrd < u'.g.paperOrd then
          selRoundsSt D d (u'.f (c.f (.inr x₀))) u'.g else [Tracked.self u'.g])
        (SelRoundsOut (C + 6 * (C + 5) + Ca + Cb + 3 * C₃ + Cc) D d (c.f (.inr x₀)) c.g)
        (selRounds_valueEq_single hvalu) (by simp) (by omega) fun u' hu' => by
          rw [List.mem_singleton] at hu'
          subst hu'
          rw [dite_eq_left hlt]
          obtain ⟨hl, hv, ho⟩ := hc _ (u'.f (c.f (.inr x₀))) u'.g d hde hSu (by omega)
            (by omega)
          exact ⟨hl, hv, fun w hw => selRounds_out_comp hRu hSu.nn.plain hoou
            (fun w hw => .step2 hhu hw) ((ho w hw).mono (by omega))⟩
      exact ⟨hl.trans (by omega), hv, fun w hw =>
        selRounds_out_comp hRc hcls.1 hoo (fun w hw => .step3 hh3 hw) (ho w hw)⟩
    · -- every other term is kept
      rw [ite_eq_right hcls]
      refine ⟨by simp, valueEq_self c.g, fun w hw => ?_⟩
      rw [List.mem_singleton] at hw
      subst hw
      rw [Tracked.psteps_comp_self]
      have hH : SelRoundsHist d (.inr x₀) s c := by
        have := SelRoundsHist.step3 hh3 (SelRoundsHist.refl (c.f (.inr x₀)) c.g)
        rwa [Tracked.psteps_comp_self] at this
      refine ⟨hRc.mono (by omega), hoo, ?_, hH⟩
      rcases hform with ⟨T, rfl, -, hTp, hTl⟩ | ⟨hp, hpo1, ⟨hlf, -⟩ | ⟨hpf, hnl⟩⟩ | ⟨hcl, hge⟩
      · exact Or.inl ⟨hTp, hTl⟩
      · exact Or.inl ⟨hp, hlf⟩
      · exact absurd ⟨hp, hpf, hnl, by linarith⟩ hcls
      · exact Or.inr (Or.inr ⟨hcl, hge⟩)

/-- The clauses of `selRoundsSt` at every number of levels, every bound on `pw` and every bound
`C`. -/
private theorem selRounds_main (k D e : ℕ) : ∀ L P C : ℕ, SelRoundsGood k D e L P C := by
  intro L
  induction L with
  | zero =>
    intro P C
    refine ⟨1, C, fun n X s d _ hS hL _ => ?_⟩
    exact selRounds_self hS le_rfl (Or.inl (by omega))
  | succ L ihL =>
    intro P
    induction P with
    | zero => exact fun C => ⟨0, 0, fun n X s d _ _ _ hP => absurd hP (Nat.not_lt_zero _)⟩
    | succ P ihP => exact selRounds_node ihL ihP

/-- The clauses of `selRounds` with the history. -/
private theorem selRounds_root (k D C j e : ℕ) :
    ∃ K C' : ℕ, ∀ (n₀ : ℕ) (x₀ : Fin n₀) (Γ : Graph k n₀) (d : ℕ), d ≤ e →
      Γ.Normal C → Γ.IsPFormAt (.inr x₀) → Γ.Plain → Γ.XdotApart → (D : ℤ) + 1 ≤ Γ.ord + j →
      (selRounds D d (.inr x₀) Γ).length ≤ K ∧ (selRounds D d (.inr x₀) Γ).ValueEq Γ modelAdm ∧
      ∀ t ∈ selRounds D d (.inr x₀) Γ, SelRoundsOut C' D d (.inr x₀) Γ t := by
  obtain ⟨K, C', h⟩ := selRounds_main k D e (j + 2 * C) (4 * (3 * C) + 1) (3 * C)
  refine ⟨K, C', fun n₀ x₀ Γ d hde hN hPF hP hxa hD => ?_⟩
  rw [selRounds, ite_eq_left hxa]
  obtain ⟨u, hsel, hSu, hsru, hordu, hpou, hvalu, hoou, hhu, -, -⟩ :=
    selStep2_init rfl hN hP hPF.2 hxa
  rw [hsel]
  have hRu : Rel (3 * C) (.inr x₀) Γ u := selRounds_rel_of_sr hSu hsru hordu.ge
  have hpwu := u.g.pw_le (u.f (.inr x₀))
  have hszu := hSu.nn.reg.size
  have hsz := hN.1.size
  have hex := selStep1_dotExcess_le Γ
  have hpΓ : Γ.paperOrd = Γ.ord - 2 * Γ.dotExcess := rfl
  refine selRounds_bind (A := 1) (B := K) _ _ _ (selRounds_valueEq_single hvalu) (by simp)
    (by omega) fun u' hu' => ?_
  rw [List.mem_singleton] at hu'
  subst hu'
  obtain ⟨hl, hv, ho⟩ := h _ (u'.f (.inr x₀)) u'.g d hde hSu (by omega) (by omega)
  exact ⟨hl, hv, fun w hw => selRounds_out_comp hRu hSu.nn.plain hoou
    (fun w hw => .step2 hhu hw) (ho w hw)⟩

/-- **The rounds of [II, Lemma 4.15]** ([II, Lemmas 4.13, 4.14] iterated as in the proof of
[II, Lemma 4.15]): for all `k`, `D`, `C`, `j`, `e` there are `K`, `C'` such that for every normal
regular graph `Γ = Γ_ω P_x(𝒢)` with bound `C` (`x` internal, labels `P_x` only, plain, no
`×`-dotted edge inside a block) of scaling order at least `D + 1 - j`, and every Taylor degree
`d ≤ e`, the rounds `selRounds D d x Γ` have at most `K` terms and the value of `Γ`, and every
output graph `t` has the clauses `Rel C'` (in particular it is normal regular with bound `C'`),
keeps the components at the external atoms at which all components of `Γ` are diffusive, and is
plain without labels, or plain of paper scaling order `> D`, or without `G^{(T)}`, `(G_{xx})⁻¹`
or dotted loop of paper scaling order at least that of `Γ` plus `d + 1`. -/
theorem selRounds_clauses (k D C j e : ℕ) :
    ∃ K C' : ℕ, ∀ (n₀ : ℕ) (x₀ : Fin n₀) (Γ : Graph k n₀) (d : ℕ), d ≤ e →
      Γ.Normal C → Γ.IsPFormAt (.inr x₀) → Γ.Plain → Γ.XdotApart → (D : ℤ) + 1 ≤ Γ.ord + j →
      (selRounds D d (.inr x₀) Γ).length ≤ K ∧ (selRounds D d (.inr x₀) Γ).ValueEq Γ modelAdm ∧
      ∀ t ∈ selRounds D d (.inr x₀) Γ, Rel C' (.inr x₀) Γ t ∧ MainOO1 Γ t ∧
        ((t.g.Plain ∧ t.g.LabelFree) ∨ (t.g.Plain ∧ (D : ℤ) < t.g.paperOrd) ∨
          (t.g.Clean ∧ Γ.paperOrd + d + 1 ≤ t.g.paperOrd)) := by
  obtain ⟨K, C', h⟩ := selRounds_root k D C j e
  refine ⟨K, C', fun n₀ x₀ Γ d hde hN hPF hP hxa hD => ?_⟩
  obtain ⟨hl, hv, ho⟩ := h n₀ x₀ Γ d hde hN hPF hP hxa hD
  exact ⟨hl, hv, fun t ht => (ho t ht).imp_right fun h => ⟨h.1, h.2.1⟩⟩

/-- **The history of the rounds**: for every normal regular graph `Γ = Γ_ω P_x(𝒢)` (`x`
internal, labels `P_x` only, plain, no `×`-dotted edge inside a block), every error order `D` and
every Taylor degree `d`, every output graph of `selRounds D d x Γ` is reached from `Γ` by a chain
of the histories of `selInit`, `selRound` (`SelStep2Hist`) and `selStep3 d` (`SelStep3Hist d`),
with the composite of their atom maps (`SelRoundsHist d`). -/
theorem selRounds_hist {k C : ℕ} (D d : ℕ) {n₀ : ℕ} (x₀ : Fin n₀) (Γ : Graph k n₀)
    (hN : Γ.Normal C) (hPF : Γ.IsPFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart) :
    ∀ t ∈ selRounds D d (.inr x₀) Γ, SelRoundsHist d (.inr x₀) Γ t := by
  obtain ⟨K, C', h⟩ := selRounds_root k D C ((D : ℤ) + 1 - Γ.ord).toNat d
  intro t ht
  exact ((h n₀ x₀ Γ d le_rfl hN hPF hP hxa (by omega)).2.2 t ht).2.2.2

end SelRoundsMain

section SelRoundsInstances

end SelRoundsInstances

end RBM8D.Graphs
