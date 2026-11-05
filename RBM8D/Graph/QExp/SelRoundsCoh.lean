import RBM8D.Graph.QExp.SelRounds
import RBM8D.Graph.QExp.MolMonoSteps
import RBM8D.Graph.QExp.MainB

/-!
# Coherence, order and molecular monotonicity of the rounds of [II, Lemma 4.15]

For the rounds `selRounds D d x Γ` of [II, Lemmas 4.13, 4.14] iterated as in the proof of
[II, Lemma 4.15], on a normal regular graph `Γ = Γ_ω P_x(𝒢)` (`x` internal, labels `P_x` only,
plain, no `×`-dotted edge inside a block):
* `selRounds_coherent`: for error orders `D ≤ D'` and Taylor degrees `d ≤ d'` with
  `D ≤ paperOrd Γ + d`, the rounds at `(D, d)` and at `(D', d')` are, up to order, `A ++ B` and
  `A ++ B'` with a common part `A`, and every graph of `B` and of `B'` has paper scaling order
  `> D`;
* `selRounds_order` (`k = 3`): every output graph has paper scaling order at least that of `Γ`,
  and at least that of `Γ` plus `1` if `⊕` and `⊖` lie in one dotted block of the output graph but
  not of `Γ`;
* `selRounds_molMono` (`k = 3`): for `Γ` with the invariant `Graph.InvB'`, every output graph
  `t` is `Graph.MolMono` from `Γ` with the atom map of `t` (the observation in the proof of
  [II, Lemma 6.5 (4)]).

The proof of the coherence uses the coherence of the run `selStep3` of [II, Lemma 4.14] in the
Taylor degree of [II, (4.21)]: the terms of [II, (4.21)] of degree at most `d` are common to the
two degrees, and every other output graph has paper scaling order at least that of the input plus
`d + 1`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Lists of tracked graphs -/

section RCohBasic

variable {k n : ℕ}

private theorem rcoh_self_inj {a b : Graph k n} (h : Tracked.self a = Tracked.self b) : a = b := by
  simp only [Tracked.self, Tracked.mk.injEq, heq_eq_eq, true_and, and_true] at h
  exact h

private theorem rcoh_mem_self {Gs : List (Graph k n)} {g : Graph k n}
    (h : Tracked.self g ∈ Gs.map Tracked.self) : g ∈ Gs := by
  obtain ⟨g', hg', he⟩ := List.mem_map.1 h
  exact rcoh_self_inj he ▸ hg'

private theorem rcoh_map_self_inj {Gs Gs' : List (Graph k n)}
    (h : Gs.map Tracked.self = Gs'.map Tracked.self) : Gs = Gs' :=
  List.map_injective_iff.2 (fun _ _ h => rcoh_self_inj h) h

private theorem rcoh_bind_self (Gs : List (Graph k n))
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n') :
    TExpansion.bind (Gs.map Tracked.self) O = Gs.flatMap fun g => O id g := by
  unfold TExpansion.bind
  rw [List.flatMap_map]
  congr 1
  funext g
  simp only [Tracked.self, Function.comp_id]
  exact List.map_id' _

private theorem rcoh_findIdx_some {α : Type*} {L : List α} {p : α → Bool} {i : ℕ}
    (h : L.findIdx? p = some i) : ∃ c, L[i]? = some c ∧ p c = true := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨L[i], List.getElem?_eq_getElem hi, hp⟩

private theorem rcoh_ord_replace {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (new : List (Comp (Atom k n))) (co : Coeff) :
    (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord =
      T.ord - c.kind.ord + (new.map fun d => d.kind.ord).sum := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  have hp := ((List.getElem_cons_eraseIdx_perm hi).map fun d => d.kind.ord).sum_eq
  simp only [Graph.ord, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hp ⊢
  linarith

/-- The paper scaling order through the dot excess of the list of components. -/
private theorem rcoh_p_eq {m : ℕ} (g : Graph k m) :
    g.paperOrd = g.ord - 2 * step3_eL g.comps := by
  rw [show g.paperOrd = g.ord - 2 * g.dotExcess from rfl, selStep2_dotExcess_eq,
    selStep2_excL_eq]

/-- The terms `j ≤ D` of the sum of [II, (4.21)] at the weight `c = (G_{xx})⁻¹` with index `i`. -/
private def rcohTTerm (T : Graph k n) (i : ℕ) (c : Comp (Atom k n)) (ch : Charge) (j : ℕ) :
    Graph k n :=
  ⟨T.comps.eraseIdx i ++ List.replicate j { c with kind := .light ch, y := c.x },
    (-1 : Coeff) ^ j * mInvOf ch ^ (j + 1) * T.coeff⟩

/-- The remainder `W_D` of [II, (4.21)] at the weight `c = (G_{xx})⁻¹` with index `i`. -/
private def rcohTW (T : Graph k n) (i : ℕ) (c : Comp (Atom k n)) (ch : Charge) (D : ℕ) :
    Graph k n :=
  ⟨T.comps.eraseIdx i ++ [{ c with kind := .wD ch D, y := c.x }], T.coeff⟩

private theorem rcoh_taylor_eq {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (D : ℕ) :
    oTaylorT D i T = [Tracked.self T] ∨
      oTaylorT D i T = ((List.range (D + 1)).map (rcohTTerm T i c ch) ++
        [rcohTW T i c ch D]).map Tracked.self := by
  simp only [oTaylorT, hc, hk]
  split_ifs
  · right
    simp [rcohTTerm, rcohTW, Tracked.self]
  · left
    rfl

private theorem rcoh_ord_tterm {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (j : ℕ) :
    (rcohTTerm T i c ch j).ord = T.ord + j := by
  rw [rcohTTerm, rcoh_ord_replace hc, hk]
  simp [Kind.ord, List.sum_replicate]

private theorem rcoh_ord_tW {T : Graph k n} {i : ℕ} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (D : ℕ) :
    (rcohTW T i c ch D).ord = T.ord + D + 1 := by
  rw [rcohTW, rcoh_ord_replace hc, hk]
  simp [Kind.ord]
  ring

/-- Every graph of [II, (4.21)] at a weight `(G_{xx})⁻¹` has scaling order at least that of `T`. -/
private theorem rcoh_taylor_ord {D i : ℕ} {T g : Graph k n} {c : Comp (Atom k n)} {ch : Charge}
    (hc : T.comps[i]? = some c) (hk : c.kind = .inv ch) (h : Tracked.self g ∈ oTaylorT D i T) :
    T.ord ≤ g.ord := by
  rcases rcoh_taylor_eq hc hk D with hE | hE <;> rw [hE] at h
  · rw [rcoh_self_inj (List.mem_singleton.1 h)]
  · rcases List.mem_append.1 (rcoh_mem_self h) with h | h
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
      rw [rcoh_ord_tterm hc hk]
      have : (0 : ℤ) ≤ j := by positivity
      linarith
    · rw [List.mem_singleton.1 h, rcoh_ord_tW hc hk]
      have : (0 : ℤ) ≤ D := by positivity
      linarith

end RCohBasic

/-! ## Common part and remainders -/

section RCohRel

variable {k : ℕ}

/-- `F` and `F'` have a common part `A`; the other terms have paper scaling order at least
`lo`. -/
private def RCoh {n : ℕ} (lo : ℤ) (F F' : TExpansion k n) : Prop :=
  ∃ A B B' : TExpansion k n, F.Perm (A ++ B) ∧ F'.Perm (A ++ B') ∧
    ∀ t ∈ B ++ B', lo ≤ t.g.paperOrd

private theorem RCoh.refl {n : ℕ} (lo : ℤ) (F : TExpansion k n) : RCoh lo F F :=
  ⟨F, [], [], by simp, by simp, by simp⟩

private theorem RCoh.append {n : ℕ} {lo : ℤ} {F G F' G' : TExpansion k n} (h₁ : RCoh lo F F')
    (h₂ : RCoh lo G G') : RCoh lo (F ++ G) (F' ++ G') := by
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

private theorem RCoh.bound {n : ℕ} {lo : ℤ} {F F' : TExpansion k n}
    (h : ∀ t ∈ F, lo ≤ t.g.paperOrd) (h' : ∀ t ∈ F', lo ≤ t.g.paperOrd) : RCoh lo F F' :=
  ⟨[], F, F', by simp, by simp, fun t ht => (List.mem_append.1 ht).elim (h t) (h' t)⟩

private theorem RCoh.flatMap {n : ℕ} {α : Type*} {lo : ℤ} (f f' : α → TExpansion k n) :
    ∀ L : List α, (∀ a ∈ L, RCoh lo (f a) (f' a)) → RCoh lo (L.flatMap f) (L.flatMap f')
  | [], _ => RCoh.refl lo []
  | a :: L, h => by
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append
      (RCoh.flatMap f f' L fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem RCoh.perm {n : ℕ} {lo : ℤ} {F G F' G' : TExpansion k n} (h : RCoh lo G G')
    (hF : F.Perm G) (hF' : F'.Perm G') : RCoh lo F F' := by
  obtain ⟨A, B, B', p, p', b⟩ := h
  exact ⟨A, B, B', hF.trans p, hF'.trans p', b⟩

/-- The common part and the remainders, composed with a tracked graph `t`. -/
private theorem RCoh.comp {n : ℕ} {lo : ℤ} (t : Tracked k n) {F F' : TExpansion k t.nOut}
    (h : RCoh lo F F') : RCoh lo (F.map t.comp) (F'.map t.comp) := by
  obtain ⟨A, B, B', p, p', b⟩ := h
  refine ⟨A.map t.comp, B.map t.comp, B'.map t.comp, ?_, ?_, fun s hs => ?_⟩
  · rw [← List.map_append]; exact p.map _
  · rw [← List.map_append]; exact p'.map _
  · rw [← List.map_append] at hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    exact b u hu

end RCohRel

/-! ## The paper scaling order of the outputs of the last phases of `selStep3` -/

section RCohBound

variable {k n : ℕ}

private theorem rcoh_firstRed_some {m : ℕ} {L : List (Comp (Atom k m))} {i : ℕ}
    (h : selStep3_firstRed L = some i) :
    ∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step3_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep3_firstRed at h
  simpa using List.find?_some h

/-- The removal of redundant dotted edges keeps the scaling order minus twice the dot excess. -/
private theorem rcoh_drop_p {m : ℕ} : ∀ (r : ℕ) (g : Graph k m),
    (selStep3_drop r g).ord - 2 * step3_eL (selStep3_drop r g).comps =
      g.ord - 2 * step3_eL g.comps
  | 0, g => rfl
  | r + 1, g => by
    rcases h : selStep3_firstRed g.comps with _ | i
    · simp only [selStep3_drop, h]
    · obtain ⟨c, hc, hk, hr⟩ := rcoh_firstRed_some h
      obtain ⟨-, he, ho, -⟩ := step3_drop_one g hc hk hr
      have ih := rcoh_drop_p r ⟨g.comps.eraseIdx i, g.coeff⟩
      simp only [selStep3_drop, h]
      rw [ih]
      simp only at he ho ⊢
      linarith

/-- The last step: every output has paper scaling order at least the scaling order of `T` minus
twice the dot excess of `Γ`. -/
private theorem rcoh_final_bound {d S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Base d S X Γ T) :
    ∀ t ∈ selStep3_final Γ.ord T, T.ord - 2 * step3_eL Γ.comps ≤ t.g.paperOrd := by
  intro t ht
  unfold selStep3_final at ht
  split_ifs at ht with hle
  · rw [List.mem_singleton.1 ht]
    change T.ord - 2 * step3_eL Γ.comps ≤ T.paperOrd
    rw [rcoh_p_eq, hB.excess]
  · have hsol : ∀ c ∈ T.comps, c.kind.isSolid = true → ¬ T.SameBlock c.x c.y := by
      intro c hc hk hb
      obtain ⟨-, d, hd, hdk, hdxy⟩ := hB.solid c hc hk
      apply hB.xapart d hd hdk
      rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hb
      · rw [h1, h2]; exact hb.symm
    rcases hm : T.mergeT with _ | t₀
    · rw [hm] at ht; simp at ht
    · rw [hm] at ht
      rw [List.mem_singleton.1 ht]
      obtain ⟨hord, heL⟩ := (step3_mergeT_spec hm).ord_eL hsol
      change _ ≤ (selStep3_drop _ t₀.g).paperOrd
      rw [rcoh_p_eq, rcoh_drop_p, hord, heL, hB.excess]
      linarith

/-- The phase of the `×`-dotted edges without solid edge, then the last step. -/
private theorem rcoh_clean_bound {d S : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ) :
    ∀ (m : ℕ) (T : Graph k n), Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.isInvB = false) → Cls d X Γ T →
      ∀ t ∈ selStep3_clean Γ.ord m T, T.ord - 2 * step3_eL Γ.comps ≤ t.g.paperOrd := by
  intro m
  induction m with
  | zero =>
    intro T hB _ _ _ _
    simp only [selStep3_clean]
    exact rcoh_final_bound hB
  | succ m ih =>
    intro T hB hK hmin hinv hcls t ht
    rcases hf : T.comps.findIdx? (step3_badB T.comps) with _ | i
    · simp only [selStep3_clean, hf] at ht
      exact rcoh_final_bound hB t ht
    · obtain ⟨c, hc, hcb⟩ := rcoh_findIdx_some hf
      obtain ⟨hE, -, -, hGs⟩ := selStep3_clean_step hG hB hK hmin hinv hcls hc hcb
      simp only [selStep3_clean, hf] at ht
      rw [hE, rcoh_bind_self] at ht
      obtain ⟨g, hg, ht⟩ := List.mem_flatMap.1 ht
      by_cases hxa : g.XdotApart
      · rw [ite_eq_left hxa] at ht
        obtain ⟨hB', hK', hmin', hinv', hcls', -⟩ := (hGs g hg).2 hxa
        have h1 := ih g hB' hK' hmin' hinv' hcls' t ht
        have hck : c.kind = .xdot := by
          simp only [step3_badB, Bool.and_eq_true, decide_eq_true_eq] at hcb
          exact hcb.1
        have hgo : T.ord ≤ g.ord := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl
          · have h2 := rcoh_ord_replace hc [] T.coeff
            simp only [List.append_nil, List.map_nil, List.sum_nil, hck, Kind.ord] at h2
            linarith
          · rw [rcoh_ord_replace hc]
            simp [hck, mkC, Kind.ord]
        linarith
      · rw [ite_eq_right hxa] at ht
        simp at ht

/-- The phase of [II, (4.21)], then the phase of the `×`-dotted edges without solid edge. -/
private theorem rcoh_taylor_bound {d S : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ) :
    ∀ (m : ℕ) (T : Graph k n), step3_nInv T.comps ≤ m → Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → Cls d X Γ T →
      ∀ t ∈ selStep3_taylor Γ.ord d m T, T.ord - 2 * step3_eL Γ.comps ≤ t.g.paperOrd := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hcls
    have hinv : ∀ c ∈ T.comps, c.kind.isInvB = false := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => c.kind.isInvB :=
        List.mem_filter.2 ⟨hc, by simpa using h⟩
      have := List.length_pos_of_mem this
      unfold step3_nInv at hm
      omega
    simp only [selStep3_taylor]
    exact rcoh_clean_bound hG _ T hB hK hmin hinv hcls
  | succ m ih =>
    intro T hm hB hK hmin hcls t ht
    rcases hf : T.comps.findIdx? (fun c => c.kind.isInvB) with _ | i
    · simp only [selStep3_taylor, hf] at ht
      exact rcoh_clean_bound hG _ T hB hK hmin (List.findIdx?_eq_none_iff.1 hf) hcls t ht
    · obtain ⟨c, hc, hci⟩ := rcoh_findIdx_some hf
      obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
        revert hci
        cases c.kind <;> simp [Kind.isInvB]
      obtain ⟨Gs, hE, -, -, hGs⟩ := selStep3_taylor_step hG hB hK hmin hcls hc hci
      simp only [selStep3_taylor, hf] at ht
      rw [hE, rcoh_bind_self] at ht
      obtain ⟨g, hg, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨hB', hK', hmin', hcls', hcnt⟩ := hGs g hg
      have h1 := ih g (by omega) hB' hK' hmin' hcls' t ht
      have h2 := rcoh_taylor_ord (D := d) hc hk (hE ▸ List.mem_map_of_mem hg)
      linarith

end RCohBound

/-! ## Coherence of `selStep3` in the Taylor degree -/

section RCohStep3

variable {k n : ℕ}

private theorem rcoh_base_ord {d S : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Base d S X Γ T) : Γ.ord ≤ T.ord := by
  have := hB.ord
  have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (nWD T.comps : ℤ) := by positivity
  push_cast at *
  linarith

private theorem rcoh_taylor_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n}
    (hG : GIn Γ) :
    ∀ (m : ℕ) (T : Graph k n), step3_nInv T.comps ≤ m →
      Base d S X Γ T → Cls d X Γ T → Base d' S' X Γ T → Cls d' X Γ T →
      OK1 Γ T → (∀ c ∈ T.comps, c.minor = []) →
      RCoh (Γ.paperOrd + d + 1) (selStep3_taylor Γ.ord d m T)
        (selStep3_taylor Γ.ord d' m T) := by
  intro m
  induction m with
  | zero =>
    intro T _ _ _ _ _ _ _
    simp only [selStep3_taylor]
    exact RCoh.refl _ _
  | succ m ih =>
    intro T hm hB hcls hB' hcls' hK hmin
    rcases hf : T.comps.findIdx? (fun c => c.kind.isInvB) with _ | i
    · simp only [selStep3_taylor, hf]
      exact RCoh.refl _ _
    obtain ⟨c, hc, hci⟩ := rcoh_findIdx_some hf
    obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
      revert hci
      cases c.kind <;> simp [Kind.isInvB]
    obtain ⟨Gs, hE, hlen, -, hGs⟩ := selStep3_taylor_step hG hB hK hmin hcls hc hci
    obtain ⟨Gs', hE', hlen', -, hGs'⟩ := selStep3_taylor_step hG hB' hK hmin hcls' hc hci
    have hL : ∀ (D : ℕ) (Hs : List (Graph k n)), oTaylorT D i T = Hs.map Tracked.self →
        Hs.length = D + 2 → oTaylorT D i T =
          ((List.range (D + 1)).map (rcohTTerm T i c ch) ++ [rcohTW T i c ch D]).map
            Tracked.self := by
      intro D Hs hH hlH
      rcases rcoh_taylor_eq hc hk D with h | h
      · rw [h] at hH
        have := congrArg List.length hH
        simp only [List.length_singleton, List.length_map] at this
        omega
      · exact h
    have hLd := hL d Gs hE hlen
    have hLd' := hL d' Gs' hE' hlen'
    have hmem : ∀ g, g ∈ (List.range (d + 1)).map (rcohTTerm T i c ch) ++ [rcohTW T i c ch d] →
        g ∈ Gs := fun g hg =>
      rcoh_mem_self (hE ▸ hLd ▸ List.mem_map_of_mem hg)
    have hmem' : ∀ g, g ∈ (List.range (d' + 1)).map (rcohTTerm T i c ch) ++
        [rcohTW T i c ch d'] → g ∈ Gs' := fun g hg =>
      rcoh_mem_self (hE' ▸ hLd' ▸ List.mem_map_of_mem hg)
    have hTo := rcoh_base_ord hB
    have hpo := rcoh_p_eq Γ
    simp only [selStep3_taylor, hf]
    rw [hLd, hLd', rcoh_bind_self, rcoh_bind_self]
    have hsplit : List.range (d' + 1) =
        List.range (d + 1) ++ (List.range (d' - d)).map (fun j => d + 1 + j) := by
      rw [← List.range_add]
      congr 1
      omega
    rw [hsplit, List.map_append, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      List.append_assoc]
    refine RCoh.append (RCoh.flatMap _ _ _ fun g hg => ?_) (RCoh.bound ?_ ?_)
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
      have := rcoh_taylor_bound hG m _ (by omega) hB1 hK1 hmin1 hcls1 t ht
      rw [rcoh_ord_tW hc hk] at this
      linarith
    · intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · -- the terms `d < j ≤ d'`
        obtain ⟨g, hg, ht⟩ := List.mem_flatMap.1 ht
        have hg' : g ∈ (List.range (d' + 1)).map (rcohTTerm T i c ch) ++
            [rcohTW T i c ch d'] := by
          rw [hsplit, List.map_append]
          exact List.mem_append_left _ (List.mem_append_right _ hg)
        obtain ⟨hB1, hK1, hmin1, hcls1, hcnt1⟩ := hGs' g (hmem' g hg')
        have := rcoh_taylor_bound hG m _ (by omega) hB1 hK1 hmin1 hcls1 t ht
        simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hg
        obtain ⟨j, -, rfl⟩ := hg
        rw [rcoh_ord_tterm hc hk] at this
        push_cast at this
        linarith
      · -- the remainder `W_{d'}`
        rw [List.flatMap_singleton] at ht
        obtain ⟨hB1, hK1, hmin1, hcls1, hcnt1⟩ :=
          hGs' _ (hmem' _ (List.mem_append_right _ (List.mem_singleton_self _)))
        have := rcoh_taylor_bound hG m _ (by omega) hB1 hK1 hmin1 hcls1 t ht
        rw [rcoh_ord_tW hc hk] at this
        have : (d : ℤ) ≤ d' := by exact_mod_cast hdd
        linarith

private theorem rcoh_rev_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n}
    (hG : GIn Γ) :
    ∀ (m : ℕ) (T : Graph k n), step3_nMin T.comps ≤ m →
      Base d S X Γ T → Cls d X Γ T → Base d' S' X Γ T → Cls d' X Γ T → OK1 Γ T →
      RCoh (Γ.paperOrd + d + 1) (selStep3_rev Γ.ord d m X T)
        (selStep3_rev Γ.ord d' m X T) := by
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
      unfold step3_nMin at hm
      omega
    simp only [selStep3_rev]
    exact rcoh_taylor_rel hdd hG _ T le_rfl hB hcls hB' hcls' hK hmin
  | succ m ih =>
    intro T hm hB hcls hB' hcls' hK
    rcases hf : T.comps.findIdx? (fun c => !c.minor.isEmpty) with _ | i
    · have hmin : ∀ c ∈ T.comps, c.minor = [] := by
        intro c hc
        have := List.findIdx?_eq_none_iff.1 hf c hc
        simpa [List.isEmpty_iff] using this
      simp only [selStep3_rev, hf]
      exact rcoh_taylor_rel hdd hG _ T le_rfl hB hcls hB' hcls' hK hmin
    obtain ⟨c, hc, hcm⟩ := rcoh_findIdx_some hf
    have hcT : c ∈ T.comps := List.mem_of_getElem? hc
    have hmX : c.minor = [X] := by
      rcases hB.minor c hcT with h | ⟨h, -⟩
      · rw [h] at hcm; simp at hcm
      · exact h
    obtain ⟨Gs, hE, -, -, hGs⟩ := selStep3_rev_step hG hB hK hcls hc hmX
    obtain ⟨Gs', hE', -, -, hGs'⟩ := selStep3_rev_step hG hB' hK hcls' hc hmX
    have hGG := rcoh_map_self_inj (hE.symm.trans hE')
    subst hGG
    simp only [selStep3_rev, hf]
    rw [hE, rcoh_bind_self, rcoh_bind_self]
    refine RCoh.flatMap _ _ _ fun g hg => ?_
    obtain ⟨⟨hB1, hcls1, hmin1, -⟩, hK1⟩ := hGs g hg
    obtain ⟨⟨hB2, hcls2, -, -⟩, -⟩ := hGs' g hg
    exact ih g (by omega) hB1 hcls1 hB2 hcls2 hK1

private theorem rcoh_dropP_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ T : Graph k n}
    (hG : GIn Γ) (hB : Base d S X Γ T) (hcls : ClsP d X Γ T ∨ AllPendL X Γ T)
    (hB' : Base d' S' X Γ T) (hcls' : ClsP d' X Γ T ∨ AllPendL X Γ T) (hK : OK1 Γ T)
    (hnp : step3_nPend X T.comps = 0) :
    RCoh (Γ.paperOrd + d + 1) (selStep3_dropP Γ.ord d X T) (selStep3_dropP Γ.ord d' X T) := by
  unfold selStep3_dropP
  by_cases hA : selStep3_AllMinor X T
  · rw [ite_eq_left hA, ite_eq_left hA]
    obtain ⟨-, hB1, hK1, hL, -⟩ := (selStep3_dropP_step hB hK hnp hcls).1 hA
    obtain ⟨-, hB2, -, -, -⟩ := (selStep3_dropP_step hB' hK hnp hcls').1 hA
    exact rcoh_rev_rel hdd hG _ _ le_rfl hB1 (Or.inr (Or.inr hL)) hB2 (Or.inr (Or.inr hL)) hK1
  · rw [ite_eq_right hA, ite_eq_right hA]
    exact rcoh_rev_rel hdd hG _ _ le_rfl hB (Or.inl ((selStep3_dropP_step hB hK hnp hcls).2 hA))
      hB' (Or.inl ((selStep3_dropP_step hB' hK hnp hcls').2 hA)) hK

private theorem rcoh_schur_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n}
    (hG : GIn Γ) :
    ∀ (m : ℕ) (T : Graph k n), step3_nPend X T.comps ≤ m →
      Base d S X Γ T → (ClsP d X Γ T ∨ AllPendL X Γ T) →
      Base d' S' X Γ T → (ClsP d' X Γ T ∨ AllPendL X Γ T) → OK1 Γ T → Step3PendInv X Γ T →
      RCoh (Γ.paperOrd + d + 1) (selStep3_schur Γ.ord d m X T)
        (selStep3_schur Γ.ord d' m X T) := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hcls hB' hcls' hK _
    simp only [selStep3_schur]
    exact rcoh_dropP_rel hdd hG hB hcls hB' hcls' hK (by omega)
  | succ m ih =>
    intro T hm hB hcls hB' hcls' hK hP
    rcases hf : T.comps.findIdx? (step3_pendB X) with _ | i
    · have hnp : step3_nPend X T.comps = 0 := by
        unfold step3_nPend
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc
        simp [List.findIdx?_eq_none_iff.1 hf c hc]
      simp only [selStep3_schur, hf]
      exact rcoh_dropP_rel hdd hG hB hcls hB' hcls' hK hnp
    obtain ⟨c, hc, hcp⟩ := rcoh_findIdx_some hf
    obtain ⟨Gs, hE, -, -, hGs⟩ := selStep3_schur_step hG.plain hB hK hP hcls hc hcp
    obtain ⟨Gs', hE', -, -, hGs'⟩ := selStep3_schur_step hG.plain hB' hK hP hcls' hc hcp
    have hGG := rcoh_map_self_inj (hE.symm.trans hE')
    subst hGG
    simp only [selStep3_schur, hf]
    rw [hE, rcoh_bind_self, rcoh_bind_self]
    refine RCoh.flatMap _ _ _ fun g hg => ?_
    obtain ⟨⟨hB1, hP1, hcls1, hp1⟩, hK1⟩ := hGs g hg
    obtain ⟨⟨hB2, -, hcls2, -⟩, -⟩ := hGs' g hg
    exact ih g (by omega) hB1 hcls1 hB2 hcls2 hK1 hP1

open Classical in
private theorem rcoh_split_rel {d d' S S' : ℕ} (hdd : d ≤ d') {X : Atom k n} {Γ : Graph k n}
    (hG : GIn Γ) (hfree : Γ.LabelledFreeAtBlock X) :
    ∀ (us : List (Atom k n)) (T : Graph k n),
      Base d S X Γ T → Base d' S' X Γ T → OK1 Γ T →
      sizeΦ d X T.comps + us.length ≤ S → sizeΦ d' X T.comps + us.length ≤ S' →
      step3_dg T.comps = step3_dg Γ.comps → (∀ g ∈ Γ.comps, g ∈ T.comps) →
      AllPendL X Γ T →
      (∀ c ∈ T.comps, step3_pendB X c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], HasX T.comps u X ∨ u ∈ us) →
      (∀ u ∈ us, ∃ c ∈ Γ.comps, c.label.isSome = true ∧ c.kind.isRandom = true ∧
        u ∈ [c.x, c.y]) →
      RCoh (Γ.paperOrd + d + 1) (selStep3_split Γ.ord d X us T)
        (selStep3_split Γ.ord d' X us T)
  | [], T, hB, hB', hK, _, _, _, _, hA, hP, _ => by
    have hP' : Step3PendInv X Γ T := by
      intro c hc hp
      obtain ⟨h1, h2⟩ := hP c hc hp
      refine ⟨h1, ?_, ?_⟩
      · rcases h2 c.x (by simp) with h | h
        · exact h
        · simp at h
      · rcases h2 c.y (by simp) with h | h
        · exact h
        · simp at h
    simp only [selStep3_split]
    exact rcoh_schur_rel hdd hG _ T le_rfl hB (Or.inr hA) hB' (Or.inr hA) hK hP'
  | u :: us, T, hB, hB', hK, hsz, hsz', hdg, hsub, hA, hP, hus => by
    obtain ⟨c₀, hc₀, hl₀, hr₀, hu₀⟩ := hus u (List.mem_cons_self ..)
    simp only [List.length_cons] at hsz hsz'
    by_cases hux : HasX T.comps u X
    · -- `u` is already `×`-dotted to `X`
      simp only [selStep3_split, ite_eq_left hux]
      refine rcoh_split_rel hdd hG hfree us T hB hB' hK (by omega) (by omega) hdg hsub hA ?_
        (fun v hv => hus v (List.mem_cons_of_mem _ hv))
      intro c hc hp
      obtain ⟨h1, h2⟩ := hP c hc hp
      refine ⟨h1, fun v hv => ?_⟩
      rcases h2 v hv with h | h
      · exact Or.inl h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inl hux
        · exact Or.inr h
    obtain ⟨-, -, -, -, hB₂, hK₂, hdg₂⟩ :=
      selStep3_split_step hG hfree hB hK (by omega) hdg hsub hc₀ hl₀ hr₀ hu₀
    obtain ⟨-, -, -, -, hB₂', -, -⟩ :=
      selStep3_split_step hG hfree hB' hK (by omega) hdg hsub hc₀ hl₀ hr₀ hu₀
    have hX : ∀ v w, HasX T.comps v w → HasX (T.comps ++ [mkC .xdot u X]) v w :=
      fun v w h => hasX_mono (fun d hd => List.mem_append_left _ hd) h
    -- `u` is joined to `X` by no solid edge of `Γ`
    have hnS : ¬ HasS Γ.comps u X := by
      rintro ⟨g, hg, hgk, hgxy⟩
      obtain ⟨d, hd, hdk, hdxy⟩ := hG.sx g hg hgk
      apply hux
      refine ⟨d, hsub d hd, hdk, ?_⟩
      rcases hgxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
      · exact Or.inr ⟨h3.trans h2, h4.trans h1⟩
      · exact Or.inr ⟨h3.trans h1, h4.trans h2⟩
      · exact Or.inl ⟨h3.trans h2, h4.trans h1⟩
    simp only [selStep3_split, ite_eq_right hux]
    refine (RCoh.refl _ _).append (rcoh_split_rel hdd hG hfree us _ hB₂ hB₂' hK₂ ?_ ?_ hdg₂ ?_ ?_
      ?_ (fun v hv => hus v (List.mem_cons_of_mem _ hv)))
    · rw [sizeΦ_append_xdot _ (Or.inr rfl)]
      omega
    · rw [sizeΦ_append_xdot _ (Or.inr rfl)]
      omega
    · exact fun g hg => List.mem_append_left _ (hsub g hg)
    · obtain ⟨hA1, ⟨w, hw, hwl⟩, us', hus', hp⟩ := hA
      refine ⟨?_, ⟨w, List.mem_append_left _ hw, hwl⟩, us' ++ [u], ?_, ?_⟩
      · intro d hd hdl hdr
        rcases List.mem_append.1 hd with h | h
        · exact hA1 d h hdl hdr
        · rw [List.mem_singleton.1 h] at hdr; simp [mkC, Kind.isRandom] at hdr
      · intro v hv
        rcases List.mem_append.1 hv with h | h
        · exact hus' v h
        · rw [List.mem_singleton.1 h]
          exact ⟨hnS, c₀, hc₀, hr₀, hu₀⟩
      · rw [List.map_append, List.map_append, List.map_singleton, List.map_singleton,
          ← List.append_assoc]
        exact hp.append_right _
    · intro d hd hdp
      rcases List.mem_append.1 hd with h | h
      · obtain ⟨h1, h2⟩ := hP d h hdp
        refine ⟨h1, fun v hv => ?_⟩
        rcases h2 v hv with h3 | h3
        · exact Or.inl (hX _ _ h3)
        · rcases List.mem_cons.1 h3 with rfl | h4
          · exact Or.inl ⟨mkC .xdot v X, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
          · exact Or.inr h4
      · rw [List.mem_singleton.1 h] at hdp; simp [step3_pendB, mkC] at hdp

/-- The run `selStep3` of [II, Lemma 4.14] at two Taylor degrees `d ≤ d'`: a common part, and
remainders of paper scaling order at least that of `Γ` plus `d + 1`. -/
private theorem rcoh_step3 {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} {d d' : ℕ} (hdd : d ≤ d')
    (hN : Γ.Normal C) (hPF : Γ.IsPFormAt (.inr x₀)) (hP : Γ.Plain)
    (hfree : Γ.LabelledFreeAtBlock (.inr x₀)) :
    RCoh (Γ.paperOrd + d + 1) (selStep3 d (.inr x₀) Γ) (selStep3 d' (.inr x₀) Γ) := by
  set X : Atom k n₀ := .inr x₀ with hXdef
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep3, selStep3, ite_eq_right hxa, ite_eq_right hxa]
    exact RCoh.refl _ _
  have hG : GIn Γ := by
    refine ⟨hP, ?_, ?_, hN.1.noIntDot⟩
    · intro g hg hk
      have hne : g.x ≠ g.y := fun h => hxa g hg hk (by rw [h]; exact SimpleGraph.Reachable.refl _)
      exact (hN.2.2 _ _ hne).1 ⟨g, hg, hk, Or.inl ⟨rfl, rfl⟩⟩
    · intro g hg hk
      have hne := hN.2.1 g hg hk
      exact (hN.2.2 _ _ hne).2 ⟨g, hg, hk, Or.inl ⟨rfl, rfl⟩⟩
  have hsize := hN.1.size
  have hlenΓ : Γ.comps.length ≤ C := by omega
  have hpendΓ : step3_nPend X Γ.comps ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
  have hminΓ : step3_nMin Γ.comps = 0 := by
    unfold step3_nMin
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [(hP c hc).1]
  have hinvΓ : step3_nInv Γ.comps = 0 := by
    unfold step3_nInv
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.isInvB]
  have hΦ : ∀ e : ℕ, sizeΦ e X Γ.comps ≤ (e + 4) * C := by
    intro e
    unfold sizeΦ
    rw [hminΓ, hinvΓ]
    have h1 : (e + 3) * (step3_nPend X Γ.comps + 0) ≤ (e + 3) * C :=
      Nat.mul_le_mul le_rfl (by omega)
    nlinarith
  rw [selStep3, selStep3, ite_eq_left hxa, ite_eq_left hxa]
  set R := Γ.comps.filter fun c => c.label.isSome && c.kind.isRandom with hR
  have hus : selStep3_us Γ = R.flatMap fun c => [c.x, c.y] := rfl
  have hlenus : (selStep3_us Γ).length ≤ 2 * C := by
    have h1 : (selStep3_us Γ).length = 2 * R.length := by
      rw [hus, List.length_flatMap]
      simp only [List.length_cons, List.length_nil]
      induction R with
      | nil => simp
      | cons a l ih => simp; ring
    have h2 : R.length ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    omega
  have hS : ∀ e : ℕ, sizeΦ e X Γ.comps + (selStep3_us Γ).length ≤ (e + 6) * C + 1 := by
    intro e
    have := hΦ e
    nlinarith
  have hB := step3_base_init (D' := d) (S := (d + 6) * C + 1) hN hPF hP hxa rfl
    (by have := hS d; omega)
  have hB' := step3_base_init (D' := d') (S := (d' + 6) * C + 1) hN hPF hP hxa rfl
    (by have := hS d'; omega)
  refine rcoh_split_rel hdd hG hfree (selStep3_us Γ) Γ hB hB' (OK1.refl Γ) (hS d) (hS d') rfl
    (fun g hg => hg) ?_ ?_ ?_
  · refine ⟨?_, hPF.1, [], by simp, by simp⟩
    intro c hc hl hr
    left
    have hcx := (hfree c hc hl hr).1
    have hcy := (hfree c hc hl hr).2
    have hx : c.x ≠ X := fun h => hcx (by rw [h]; exact SimpleGraph.Reachable.refl _)
    have hy : c.y ≠ X := fun h => hcy (by rw [h]; exact SimpleGraph.Reachable.refl _)
    simp [step3_pendB, hl, hr, (hP c hc).1, hx, hy]
  · intro c hc hp
    refine ⟨hc, fun u hu => Or.inr ?_⟩
    rw [hus, List.mem_flatMap]
    refine ⟨c, ?_, hu⟩
    rw [hR, List.mem_filter]
    simp only [step3_pendB, Bool.and_eq_true] at hp
    exact ⟨hc, by simp only [Bool.and_eq_true]; exact ⟨hp.1.1.1.1, hp.1.1.1.2⟩⟩
  · intro u hu
    rw [hus, List.mem_flatMap] at hu
    obtain ⟨c, hcR, hu⟩ := hu
    rw [hR, List.mem_filter] at hcR
    simp only [Bool.and_eq_true] at hcR
    exact ⟨c, hcR.1, hcR.2.1, hcR.2.2, hu⟩

end RCohStep3

/-! ## The rounds: induction on the state -/

section RCohRounds

variable {k : ℕ}

/-- Induction on the states of the rounds with error order `D`, along the order of the recursion
of `selRoundsSt`: first `D + 1` minus the paper scaling order, then the weighted number of
labelled weights and edge ends at the image of `X`. -/
private theorem rcoh_wf (D : ℕ) (M : ∀ {n : ℕ}, Atom k n → Graph k n → Prop)
    (h : ∀ {n : ℕ} (X : Atom k n) (s : Graph k n),
      (∀ {n' : ℕ} (X' : Atom k n') (s' : Graph k n'),
        ((D : ℤ) + 1 - s'.paperOrd).toNat < ((D : ℤ) + 1 - s.paperOrd).toNat ∨
          (((D : ℤ) + 1 - s'.paperOrd).toNat = ((D : ℤ) + 1 - s.paperOrd).toNat ∧
            s'.pw X' < s.pw X) → M X' s') → M X s) :
    ∀ {n : ℕ} (X : Atom k n) (s : Graph k n), M X s
  | _, X, s => h X s fun X' s' _hlt => rcoh_wf D M h X' s'
termination_by n X s => (((D : ℤ) + 1 - s.paperOrd).toNat, s.pw X)
decreasing_by
  rw [Prod.lex_def]
  exact _hlt

private theorem rcoh_lex {D : ℕ} {a b : ℤ} {p q : ℕ} (hD : a ≤ D)
    (h : a < b ∨ (a = b ∧ q < p)) :
    ((D : ℤ) + 1 - b).toNat < ((D : ℤ) + 1 - a).toNat ∨
      (((D : ℤ) + 1 - b).toNat = ((D : ℤ) + 1 - a).toNat ∧ q < p) := by
  rcases h with h | ⟨rfl, h⟩
  · left; omega
  · right; exact ⟨rfl, h⟩

open Classical in
/-- The continuation of the rounds at an output graph `c` of `selStep3` at the state `s`. -/
private def rcohK (D d : ℕ) {n : ℕ} (X : Atom k n) (s : Graph k n) (c : Tracked k n) :
    TExpansion k n :=
  (if c.g.Plain ∧ c.g.IsPFormAt (c.f X) ∧ ¬ c.g.LabelledFreeAtBlock (c.f X) ∧
      s.paperOrd < c.g.paperOrd then
    (if c.g.XdotApart then
      (selInit (c.f X) c.g).flatMap fun u =>
        (if _h : s.paperOrd < u.g.paperOrd then selRoundsSt D d (u.f (c.f X)) u.g
        else [Tracked.self u.g]).map u.comp
    else [])
  else [Tracked.self c.g]).map c.comp

/-- The continuation of the rounds at an output graph `t` of a round at the state `s`. -/
private def rcohR (D d : ℕ) {n : ℕ} (X : Atom k n) (s : Graph k n) (t : Tracked k n) :
    TExpansion k n :=
  (if _h : s.paperOrd < t.g.paperOrd ∨
      (s.paperOrd = t.g.paperOrd ∧ t.g.pw (t.f X) < s.pw X) then
    selRoundsSt D d (t.f X) t.g
  else [Tracked.self t.g]).map t.comp

private theorem rcoh_stop {D d n : ℕ} {X : Atom k n} {s : Graph k n}
    (h : (D : ℤ) < s.paperOrd ∨ s.LabelFree) : selRoundsSt D d X s = [Tracked.self s] := by
  rw [selRoundsSt, dite_eq_left h]

private theorem rcoh_unfold_round {D d n : ℕ} {X : Atom k n} {s : Graph k n}
    (h1 : ¬ ((D : ℤ) < s.paperOrd ∨ s.LabelFree)) (h2 : 0 < s.pw X) :
    selRoundsSt D d X s = (selRound X s).flatMap (rcohR D d X s) := by
  rw [selRoundsSt, dite_eq_right h1, ite_eq_left h2]
  rfl

private theorem rcoh_unfold_step3 {D d n : ℕ} {X : Atom k n} {s : Graph k n}
    (h1 : ¬ ((D : ℤ) < s.paperOrd ∨ s.LabelFree)) (h2 : ¬ 0 < s.pw X) :
    selRoundsSt D d X s = (selStep3 d X s).flatMap (rcohK D d X s) := by
  rw [selRoundsSt, dite_eq_right h1, ite_eq_right h2]
  congr 1
  funext c
  unfold rcohK
  congr 1
  split_ifs <;> rfl

/-- At a state where `selStep3` runs: the atom is internal, the state is a `P`-form at it, and no
labelled weight or edge is attached to its block. -/
private theorem rcoh_st3 {C D n : ℕ} {X : Atom k n} {s : Graph k n} (hS : St C X s)
    (hstop : ¬ ((D : ℤ) < s.paperOrd ∨ s.LabelFree)) (hpw : ¬ 0 < s.pw X) :
    ∃ x₀, X = .inr x₀ ∧ s.IsPFormAt X ∧ s.LabelledFreeAtBlock X := by
  obtain ⟨x₀, rfl⟩ := exists_inr_of_isRight hS.nn.hx
  refine ⟨x₀, rfl, ⟨?_, hS.nn.lab⟩, labelledFree_of_pw hS.nn.plain (by omega)⟩
  have hnl : ¬ s.LabelFree := fun h => hstop (Or.inr h)
  unfold Graph.LabelFree at hnl
  push Not at hnl
  obtain ⟨c, hc, hne⟩ := hnl
  exact ⟨c, hc, (hS.nn.lab c hc).resolve_left hne⟩

/-- The paper scaling order does not drop along `Tracked.QBase`. -/
private theorem rcoh_p_le_of_qbase {C' n : ℕ} {X : Atom k n} {s : Graph k n} {c : Tracked k n}
    (h : c.QBase C' X s) : s.paperOrd ≤ c.g.paperOrd := by
  have h1 := h.2.1
  have h2 := h.2.2.2.1
  unfold Graph.paperOrd
  linarith

/-- The paper scaling order does not drop along the rounds at a state. -/
private theorem rcoh_mono (D d : ℕ) : ∀ {n : ℕ} (X : Atom k n) (s : Graph k n), ∀ C, St C X s →
    ∀ t ∈ selRoundsSt D d X s, s.paperOrd ≤ t.g.paperOrd := by
  refine rcoh_wf D (fun X s => ∀ C, St C X s →
    ∀ t ∈ selRoundsSt D d X s, s.paperOrd ≤ t.g.paperOrd) ?_
  intro n X s ih C hS t ht
  by_cases hstop : (D : ℤ) < s.paperOrd ∨ s.LabelFree
  · rw [rcoh_stop hstop, List.mem_singleton] at ht
    rw [ht]
    exact le_rfl
  have hD : s.paperOrd ≤ D := by
    by_contra h
    exact hstop (Or.inl (by omega))
  by_cases hpw : 0 < s.pw X
  · rw [rcoh_unfold_round hstop hpw] at ht
    obtain ⟨t₁, ht₁, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨hSt, -, -, -, hpo, hguard, -⟩ := (selStep2_round hS hpw).2.2 t₁ ht₁
    unfold rcohR at ht
    rw [dite_eq_left hguard] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    exact hpo.trans (ih (t₁.f X) t₁.g (rcoh_lex hD hguard) _ hSt w hw)
  · rw [rcoh_unfold_step3 hstop hpw] at ht
    obtain ⟨x₀, rfl, hPF, hfree⟩ := rcoh_st3 hS hstop hpw
    obtain ⟨K₃, C₃, h3⟩ := selStep3_clauses' k C d
    obtain ⟨-, -, hout⟩ := h3 n x₀ s d le_rfl hS.normal hPF hS.nn.plain hfree
    obtain ⟨c, hc, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨⟨hB, -, -⟩, -, -, -⟩ := hout c hc
    have hpc := rcoh_p_le_of_qbase hB
    unfold rcohK at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    split_ifs at hw with hcls hxa
    · obtain ⟨u, hsel, hSu, -, -, hpou, -⟩ :=
        selStep2_init hB.2.2.2.2.1 hB.1 hcls.1 hcls.2.1.2 hxa
      rw [hsel, List.flatMap_singleton] at hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      split_ifs at hv with hlt
      · have := ih _ u.g (rcoh_lex hD (Or.inl hlt)) _ hSu v hv
        change s.paperOrd ≤ v.g.paperOrd
        linarith
      · rw [List.mem_singleton.1 hv]
        change s.paperOrd ≤ u.g.paperOrd
        linarith
    · simp at hw
    · rw [List.mem_singleton.1 hw]
      exact hpc

/-- The continuation at an output graph of `selStep3` does not lower the paper scaling order. -/
private theorem rcoh_K_mono {C₁ D d n : ℕ} {X : Atom k n} {s : Graph k n} {c : Tracked k n}
    (hB : c.QBase C₁ X s) : ∀ w ∈ rcohK D d X s c, c.g.paperOrd ≤ w.g.paperOrd := by
  intro w₀ hw₀
  unfold rcohK at hw₀
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw₀
  split_ifs at hw with hcls hxa
  · obtain ⟨u, hsel, hSu, -, -, hpou, -⟩ :=
      selStep2_init hB.2.2.2.2.1 hB.1 hcls.1 hcls.2.1.2 hxa
    rw [hsel, List.flatMap_singleton] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    split_ifs at hv with hlt
    · have := rcoh_mono D d _ u.g _ hSu v hv
      change c.g.paperOrd ≤ v.g.paperOrd
      linarith
    · rw [List.mem_singleton.1 hv]
      change c.g.paperOrd ≤ u.g.paperOrd
      linarith
  · simp at hw
  · rw [List.mem_singleton.1 hw]
    exact le_rfl

end RCohRounds

/-! ## Coherence of the rounds in the error order and the Taylor degree -/

section RCohCoherent

variable {k : ℕ}

/-- The rounds at a state `s` with `(D, d)` and with `(D', d')`: a common part, and remainders of
paper scaling order `> D`. -/
private theorem rcoh_rounds (D D' d d' : ℕ) (hD : D ≤ D') (hd : d ≤ d') :
    ∀ {n : ℕ} (X : Atom k n) (s : Graph k n), ∀ C, St C X s → (D : ℤ) ≤ s.paperOrd + d →
      RCoh ((D : ℤ) + 1) (selRoundsSt D d X s) (selRoundsSt D' d' X s) := by
  refine rcoh_wf D (fun X s => ∀ C, St C X s → (D : ℤ) ≤ s.paperOrd + d →
    RCoh ((D : ℤ) + 1) (selRoundsSt D d X s) (selRoundsSt D' d' X s)) ?_
  intro n X s ih C hS hDs
  have hDD : (D : ℤ) ≤ D' := by exact_mod_cast hD
  by_cases hlt : (D : ℤ) < s.paperOrd
  · -- the `D`-run stops at `s`
    rw [rcoh_stop (Or.inl hlt)]
    refine RCoh.bound (fun t ht => ?_) (fun t ht => ?_)
    · rw [List.mem_singleton.1 ht]
      change (D : ℤ) + 1 ≤ s.paperOrd
      omega
    · have := rcoh_mono D' d' X s C hS t ht
      omega
  by_cases hlf : s.LabelFree
  · rw [rcoh_stop (Or.inr hlf), rcoh_stop (Or.inr hlf)]
    exact RCoh.refl _ _
  have hstop : ¬ ((D : ℤ) < s.paperOrd ∨ s.LabelFree) := by tauto
  have hstop' : ¬ ((D' : ℤ) < s.paperOrd ∨ s.LabelFree) := by
    rintro (h | h)
    · exact hlt (by omega)
    · exact hlf h
  have hDle : s.paperOrd ≤ D := by omega
  by_cases hpw : 0 < s.pw X
  · -- a round of Step 2, the same in both runs
    rw [rcoh_unfold_round hstop hpw, rcoh_unfold_round hstop' hpw]
    refine RCoh.flatMap _ _ _ fun t₁ ht₁ => ?_
    obtain ⟨hSt, -, -, -, hpo, hguard, -⟩ := (selStep2_round hS hpw).2.2 t₁ ht₁
    unfold rcohR
    rw [dite_eq_left hguard, dite_eq_left hguard]
    exact RCoh.comp t₁ (ih _ _ (rcoh_lex hDle hguard) _ hSt (by linarith))
  · -- Step 3 at the two Taylor degrees
    rw [rcoh_unfold_step3 hstop hpw, rcoh_unfold_step3 hstop' hpw]
    obtain ⟨x₀, rfl, hPF, hfree⟩ := rcoh_st3 hS hstop hpw
    obtain ⟨K₃, C₃, h3⟩ := selStep3_clauses' k C d
    obtain ⟨K₃', C₃', h3'⟩ := selStep3_clauses' k C d'
    obtain ⟨-, -, hout⟩ := h3 n x₀ s d le_rfl hS.normal hPF hS.nn.plain hfree
    obtain ⟨-, -, hout'⟩ := h3' n x₀ s d' le_rfl hS.normal hPF hS.nn.plain hfree
    obtain ⟨A, B, B', hp, hp', hb⟩ := rcoh_step3 hd hS.normal hPF hS.nn.plain hfree
    have hq1 : ((selStep3 d (.inr x₀) s).flatMap (rcohK D d (.inr x₀) s)).Perm
        (A.flatMap (rcohK D d (.inr x₀) s) ++ B.flatMap (rcohK D d (.inr x₀) s)) := by
      rw [← List.flatMap_append]
      exact hp.flatMap_right _
    have hq2 : ((selStep3 d' (.inr x₀) s).flatMap (rcohK D' d' (.inr x₀) s)).Perm
        (A.flatMap (rcohK D' d' (.inr x₀) s) ++ B'.flatMap (rcohK D' d' (.inr x₀) s)) := by
      rw [← List.flatMap_append]
      exact hp'.flatMap_right _
    refine RCoh.perm (RCoh.append (RCoh.flatMap _ _ _ fun c hcA => ?_)
      (RCoh.bound (fun t ht => ?_) (fun t ht => ?_))) hq1 hq2
    · -- a common output graph of `selStep3`
      have hc : c ∈ selStep3 d (.inr x₀) s := hp.symm.subset (List.mem_append_left _ hcA)
      obtain ⟨⟨hB, -, -⟩, -, -, -⟩ := hout c hc
      have hpc := rcoh_p_le_of_qbase hB
      unfold rcohK
      by_cases hcls : c.g.Plain ∧ c.g.IsPFormAt (c.f (.inr x₀)) ∧
          ¬ c.g.LabelledFreeAtBlock (c.f (.inr x₀)) ∧ s.paperOrd < c.g.paperOrd
      · rw [ite_eq_left hcls, ite_eq_left hcls, ite_eq_left hB.2.2.1, ite_eq_left hB.2.2.1]
        obtain ⟨u, hsel, hSu, -, -, hpou, -⟩ :=
          selStep2_init hB.2.2.2.2.1 hB.1 hcls.1 hcls.2.1.2 hB.2.2.1
        rw [hsel, List.flatMap_singleton, List.flatMap_singleton]
        refine RCoh.comp c (RCoh.comp u ?_)
        by_cases hlt' : s.paperOrd < u.g.paperOrd
        · rw [dite_eq_left hlt', dite_eq_left hlt']
          exact ih _ _ (rcoh_lex hDle (Or.inl hlt')) _ hSu (by linarith)
        · rw [dite_eq_right hlt', dite_eq_right hlt']
          exact RCoh.refl _ _
      · rw [ite_eq_right hcls, ite_eq_right hcls]
        exact RCoh.refl _ _
    · -- the remainder of the `(D, d)`-run
      obtain ⟨c, hcB, hw⟩ := List.mem_flatMap.1 ht
      have hc : c ∈ selStep3 d (.inr x₀) s := hp.symm.subset (List.mem_append_right _ hcB)
      obtain ⟨⟨hB, -, -⟩, -, -, -⟩ := hout c hc
      have h1 := rcoh_K_mono hB t hw
      have h2 := hb c (List.mem_append_left _ hcB)
      linarith
    · -- the remainder of the `(D', d')`-run
      obtain ⟨c, hcB, hw⟩ := List.mem_flatMap.1 ht
      have hc : c ∈ selStep3 d' (.inr x₀) s := hp'.symm.subset (List.mem_append_right _ hcB)
      obtain ⟨⟨hB, -, -⟩, -, -, -⟩ := hout' c hc
      have h1 := rcoh_K_mono hB t hw
      have h2 := hb c (List.mem_append_right _ hcB)
      linarith

end RCohCoherent

/-- **Coherence of the rounds of [II, Lemma 4.15] in the error order and the Taylor degree**:
for a normal regular graph `Γ = Γ_ω P_x(𝒢)` with bound `C` (`x` internal, labels `P_x` only,
plain, no `×`-dotted edge inside a block), error orders `D ≤ D'` and Taylor degrees `d ≤ d'` with
`D` at most the paper scaling order of `Γ` plus `d`, the rounds `selRounds D d x Γ` and
`selRounds D' d' x Γ` are, up to order, `A ++ B` and `A ++ B'` with a common part `A`, and every
graph of `B` and of `B'` has paper scaling order `> D`. -/
theorem selRounds_coherent {k C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph k n₀} {D D' d d' : ℕ}
    (hN : Γ.Normal C) (hPF : Γ.IsPFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart)
    (hD : D ≤ D') (hd : d ≤ d') (hDd : (D : ℤ) ≤ Γ.paperOrd + d) :
    ∃ A B B' : TExpansion k n₀, (selRounds D d (.inr x₀) Γ).Perm (A ++ B) ∧
      (selRounds D' d' (.inr x₀) Γ).Perm (A ++ B') ∧
      ∀ t ∈ B ++ B', (D : ℤ) < t.g.paperOrd := by
  rw [selRounds, selRounds, ite_eq_left hxa, ite_eq_left hxa]
  obtain ⟨u, hsel, hSu, -, -, hpou, -⟩ := selStep2_init rfl hN hP hPF.2 hxa
  rw [hsel, List.flatMap_singleton, List.flatMap_singleton]
  obtain ⟨A, B, B', h1, h2, h3⟩ :=
    RCoh.comp u (rcoh_rounds D D' d d' hD hd _ _ _ hSu (by rw [hpou]; exact hDd))
  exact ⟨A, B, B', h1, h2, fun t ht => by have := h3 t ht; omega⟩

/-! ## Order and the `⊕`–`⊖` block -/

section RCohOrder

/-- A graph whose components are those of `s` without labels, up to order, has the dotted blocks
of `s`. -/
private theorem rcoh_pm_lead {n : ℕ} {s T : Graph 3 n} (h : T.comps.Perm s.dropLabels.comps)
    (hT : T.PMBlock) : s.PMBlock := by
  rw [Graph.pmBlock_iff_sameBlock] at hT ⊢
  refine SimpleGraph.Reachable.mono ?_ hT
  intro u v huv
  rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at huv ⊢
  obtain ⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := huv
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (show c ∈ s.comps.map _ from h.subset hc)
    exact ⟨hne, Or.inl ⟨c', hc', hk, rfl, rfl⟩⟩
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (show c ∈ s.comps.map _ from h.subset hc)
    exact ⟨hne, Or.inr ⟨c', hc', hk, rfl, rfl⟩⟩

/-- The `⊕`–`⊖` block along the rounds: an output graph of the rounds at a state `s` with `⊕`
and `⊖` in one dotted block, while they are in distinct blocks of `s`, has paper scaling order at
least that of `s` plus `1`. -/
private theorem rcoh_pm (D d : ℕ) : ∀ {n : ℕ} (X : Atom 3 n) (s : Graph 3 n), ∀ C, St C X s →
    ∀ t ∈ selRoundsSt D d X s, ¬ s.PMBlock → t.g.PMBlock →
      s.paperOrd + 1 ≤ t.g.paperOrd := by
  refine rcoh_wf D (fun X s => ∀ C, St C X s → ∀ t ∈ selRoundsSt D d X s, ¬ s.PMBlock →
    t.g.PMBlock → s.paperOrd + 1 ≤ t.g.paperOrd) ?_
  intro n X s ih C hS t ht hn hpm
  by_cases hstop : (D : ℤ) < s.paperOrd ∨ s.LabelFree
  · rw [rcoh_stop hstop, List.mem_singleton] at ht
    rw [ht] at hpm
    exact absurd hpm hn
  have hD : s.paperOrd ≤ D := by
    by_contra h
    exact hstop (Or.inl (by omega))
  by_cases hpw : 0 < s.pw X
  · rw [rcoh_unfold_round hstop hpw] at ht
    obtain ⟨t₁, ht₁, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨hSt, -, -, -, hpo, hguard, -⟩ := (selStep2_round hS hpw).2.2 t₁ ht₁
    unfold rcohR at ht
    rw [dite_eq_left hguard] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    change s.paperOrd + 1 ≤ w.g.paperOrd
    by_cases hpm₁ : t₁.g.PMBlock
    · have h1 := selStep2_round_pmBlock hS hpw t₁ ht₁ hn hpm₁
      have h2 := rcoh_mono D d _ _ _ hSt w hw
      linarith
    · have := ih (t₁.f X) t₁.g (rcoh_lex hD hguard) _ hSt w hw hpm₁ hpm
      linarith
  · rw [rcoh_unfold_step3 hstop hpw] at ht
    obtain ⟨x₀, rfl, hPF, hfree⟩ := rcoh_st3 hS hstop hpw
    obtain ⟨K₃, C₃, h3⟩ := selStep3_clauses' 3 C d
    obtain ⟨-, -, hout⟩ := h3 n x₀ s d le_rfl hS.normal hPF hS.nn.plain hfree
    obtain ⟨c, hc, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨⟨hB, -, -⟩, -, hform, -⟩ := hout c hc
    have hK := rcoh_K_mono (D := D) (d := d) hB t ht
    unfold rcohK at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    by_cases hcls : c.g.Plain ∧ c.g.IsPFormAt (c.f (.inr x₀)) ∧
        ¬ c.g.LabelledFreeAtBlock (c.f (.inr x₀)) ∧ s.paperOrd < c.g.paperOrd
    · -- a term of `P`-form of higher paper scaling order and its continuation
      have := hcls.2.2.2
      linarith
    · rw [ite_eq_right hcls, List.mem_singleton] at hw
      subst hw
      change c.g.PMBlock at hpm
      change s.paperOrd + 1 ≤ c.g.paperOrd
      rcases hform with ⟨T, rfl, hperm, -, -⟩ | ⟨-, h, -⟩ | ⟨-, h⟩
      · exact absurd (rcoh_pm_lead hperm hpm) hn
      · exact h
      · have : (0 : ℤ) ≤ d := by positivity
        linarith

end RCohOrder

/-- **Order and the `⊕`–`⊖` block of the outputs of the rounds** ([II, §4.4, Steps 2, 3]): for
`k = 3` and a normal regular graph `Γ = Γ_ω P_x(𝒢)` with bound `C` (`x` internal, labels `P_x`
only, plain, no `×`-dotted edge inside a block), every output graph of `selRounds D d x Γ` has
paper scaling order at least that of `Γ`, and at least that of `Γ` plus `1` if `⊕` and `⊖` lie in
one dotted block of the output graph but not of `Γ`. -/
theorem selRounds_order {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph 3 n₀} (D d : ℕ) (hN : Γ.Normal C)
    (hPF : Γ.IsPFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart) :
    ∀ t ∈ selRounds D d (.inr x₀) Γ, Γ.paperOrd ≤ t.g.paperOrd ∧
      (¬ Γ.PMBlock → t.g.PMBlock → Γ.paperOrd + 1 ≤ t.g.paperOrd) := by
  intro t ht
  rw [selRounds, ite_eq_left hxa] at ht
  obtain ⟨u, hsel, hSu, -, -, hpou, -, -, -, hblk, hinl⟩ := selStep2_init rfl hN hP hPF.2 hxa
  rw [hsel, List.flatMap_singleton] at ht
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
  have h1 := rcoh_mono D d _ _ _ hSu w hw
  refine ⟨by rw [← hpou]; exact h1, fun hn hpm => ?_⟩
  have hnu : ¬ u.g.PMBlock := by
    rw [Graph.pmBlock_iff_sameBlock] at hn ⊢
    rw [← hinl 1, ← hinl 2]
    exact fun h => hn ((hblk _ _).1 h)
  have := rcoh_pm D d _ _ _ hSu w hw hnu hpm
  rw [← hpou]
  exact this

/-! ## Molecular monotonicity -/

section RCohMolMono

/-- The atom of a `P` label of a graph whose label atoms are internal is internal. -/
private theorem rcoh_isRight_of_P {n : ℕ} {Γ : Graph 3 n} {x : Atom 3 n}
    (hP : Γ.IsPFormAt x) (hL : Γ.LabelsInt) : x.isRight = true := by
  obtain ⟨c, hc, hl⟩ := hP.1
  have := hL c hc
  rw [hl] at this
  exact this

/-- A step of the run of Step 2, with its own atom map. -/
private theorem rcoh_step2_mm {n : ℕ} {Γ : Graph 3 n} {t : Tracked 3 n}
    (h : SelStep2Step Γ t) (hI : Γ.InvB') : Γ.MolMono t.g t.f := by
  cases h with
  | split u v Γ t hv ht => exact molMono_oSplitT u v Γ hI.2.1 hI.2.2.1 hI.2.2.2.1 t ht
  | xdot i Γ t ht => exact molMono_oXdotT i Γ hI.2.1 hI.2.2.1 hI.2.2.2.1 t ht
  | merge Γ t ht => exact molMono_mergeT Γ t ht
  | dropDot i Γ c hc hk hb => exact molMono_dropDot i Γ c hc hk hb
  | rebase i Γ c u v hc hk hb => exact molMono_rebase i Γ c u v hI.2.2.1 hc hk hb
  | pWeight1 x Γ t hP hp ht => exact molMono_pWeight1 x Γ t ht
  | pWeight2 x Γ t hP hp ht =>
    exact molMono_oWeightP2T x Γ (rcoh_isRight_of_P hP hI.2.2.2.2) t ht
  | pMultiE x Γ E t hP hp hE ht =>
    exact molMono_pMultiE x Γ (rcoh_isRight_of_P hP hI.2.2.2.2) E hE t ht

/-- The history of a piece of Step 2: the composite of the atom maps of its steps. -/
private theorem rcoh_hist2_mm {n : ℕ} {Γ : Graph 3 n} {s : Tracked 3 n} (h : SelStep2Hist Γ s) :
    Γ.InvB' → Γ.MolMono s.g s.f ∧ s.g.InvB' := by
  induction h with
  | refl Γ => exact fun hI => ⟨Graph.MolMono.refl Γ, hI⟩
  | step h _ ih =>
    intro hI
    obtain ⟨hm, hI'⟩ := ih (qElemStep_invB _ _ h.qElemStep hI)
    exact ⟨(rcoh_step2_mm h hI).comp hm, hI'⟩

/-- A step of the run `selStep3`, with the identity map. -/
private theorem rcoh_step3_mm {n d : ℕ} {X : Atom 3 n} (hX : X.isRight = true) {T g : Graph 3 n}
    (h : SelStep3Step d X T g) (hI : T.InvB') : T.MolMono g id := by
  cases h with
  | split u T g h => exact molMono_oSplitT u X T hI.2.1 hI.2.2.1 hI.2.2.2.1 _ h
  | schur i T g h => exact molMono_oSchurT X hX i T _ h
  | schurW i T g h => exact molMono_oSchurWT X i T _ h
  | dropP T hP hm => exact molMono_dropLabels T
  | schurRev i T g h => exact molMono_oSchurRevT X hX i T _ h
  | schurWRev i T g h => exact molMono_oSchurWRevT X i T _ h
  | taylor i T g h => exact molMono_oTaylorT d i T _ h
  | xdot i T g h => exact molMono_oXdotT i T hI.2.1 hI.2.2.1 hI.2.2.2.1 _ h

/-- A chain of steps of the run `selStep3`, with the identity map. -/
private theorem rcoh_chain3_mm {n d : ℕ} {X : Atom 3 n} (hX : X.isRight = true) {Γ T : Graph 3 n}
    (h : Relation.ReflTransGen (SelStep3Step d X) Γ T) (hI : Γ.InvB') :
    Γ.MolMono T id ∧ T.InvB' := by
  induction h with
  | refl => exact ⟨Graph.MolMono.refl Γ, hI⟩
  | tail _ hst ih =>
    exact ⟨ih.1.comp (rcoh_step3_mm hX hst ih.2),
      qElemStep_invB _ _ (hst.qElemStep hX) ih.2⟩

/-- A chain of removals of redundant dotted edges, with the identity map. -/
private theorem rcoh_drops_mm {m : ℕ} {g g' : Graph 3 m}
    (h : Relation.ReflTransGen SelStep3Drop g g') (hI : g.InvB') : g.MolMono g' id ∧ g'.InvB' := by
  induction h with
  | refl => exact ⟨Graph.MolMono.refl g, hI⟩
  | tail _ hst ih =>
    obtain ⟨i, c, hc, hk, hb, rfl⟩ := hst
    exact ⟨ih.1.comp (molMono_dropDot i _ c hc hk hb),
      qElemStep_invB _ _ (QElemStep.dropDot i _ c hc hk hb) ih.2⟩

/-- The history of a piece of Step 3: the identity map, then the map of `O_merge`. -/
private theorem rcoh_hist3_mm {n d : ℕ} {X : Atom 3 n} (hX : X.isRight = true) {Γ : Graph 3 n}
    {t : Tracked 3 n} (h : SelStep3Hist d X Γ t) (hI : Γ.InvB') :
    Γ.MolMono t.g t.f ∧ t.g.InvB' := by
  obtain ⟨T, hch, ht⟩ := h
  obtain ⟨hm, hIT⟩ := rcoh_chain3_mm hX hch hI
  rcases ht with rfl | ⟨t₀, hmt, g', hdr, rfl⟩
  · exact ⟨hm, hIT⟩
  · have hI₀ := qElemStep_invB _ _ (QElemStep.merge T t₀ hmt) hIT
    obtain ⟨hmd, hI'⟩ := rcoh_drops_mm hdr hI₀
    exact ⟨(hm.comp (molMono_mergeT T t₀ hmt)).comp hmd, hI'⟩

/-- The history of an output graph of the rounds: the composite of the atom maps of the pieces. -/
private theorem rcoh_roundsHist_mm {d n : ℕ} {X : Atom 3 n} {Γ : Graph 3 n} {t : Tracked 3 n}
    (h : SelRoundsHist d X Γ t) : X.isRight = true → Γ.InvB' → Γ.MolMono t.g t.f := by
  induction h with
  | refl X Γ => exact fun _ _ => Graph.MolMono.refl Γ
  | step2 h _ ih =>
    rename_i X _ _ _
    intro hX hI
    obtain ⟨hm, hI'⟩ := rcoh_hist2_mm h hI
    obtain ⟨a, rfl⟩ := exists_inr_of_isRight hX
    exact hm.comp (ih (hm.isRight a) hI')
  | step3 h _ ih =>
    rename_i X _ _ _
    intro hX hI
    obtain ⟨hm, hI'⟩ := rcoh_hist3_mm hX h hI
    obtain ⟨a, rfl⟩ := exists_inr_of_isRight hX
    exact hm.comp (ih (hm.isRight a) hI')

end RCohMolMono

/-- **Molecular monotonicity of the rounds** (the observation in the proof of
[II, Lemma 6.5 (4)]): for `k = 3` and a normal regular graph `Γ = Γ_ω P_x(𝒢)` with bound `C`
(`x` internal, labels `P_x` only, plain, no `×`-dotted edge inside a block) with the invariant
`Graph.InvB'`, every output graph `t` of `selRounds D d x Γ` is `Graph.MolMono` from `Γ` with the
atom map of `t`, the composite of the atom maps of the elementary steps of its history. -/
theorem selRounds_molMono {C n₀ : ℕ} {x₀ : Fin n₀} {Γ : Graph 3 n₀} (D d : ℕ) (hN : Γ.Normal C)
    (hPF : Γ.IsPFormAt (.inr x₀)) (hP : Γ.Plain) (hxa : Γ.XdotApart) (hI : Γ.InvB') :
    ∀ t ∈ selRounds D d (.inr x₀) Γ, Γ.MolMono t.g t.f := fun t ht =>
  rcoh_roundsHist_mm (selRounds_hist D d x₀ Γ hN hPF hP hxa t ht) rfl hI

section RCohInstances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end RCohInstances

end RBM8D.Graphs
