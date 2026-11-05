import RBM8D.Graph.QExp.SelRoundsCoh
import RBM8D.Graph.QExp.SelStep1Coh
import RBM8D.GlobalExp.QFamily

/-!
# The family of `Q`-expansions of [II, Lemma 4.15] with deterministic choices

The expansion of [II, Lemma 4.15] of a graph `Γ = Γ₀ Q_x(Γ̃₀)` at error order `D`, as a function
of `D`, `x` and `Γ` (`selRunFam`): the run `selStep1` of [II, Lemma 4.11] with the Taylor degree
`d = selDeg D Γ`, then, at every output graph `Γ_ω Q_x(Γ̃_ω)` that is plain and not a `Q`-graph,
the identity `Q_x = 1 - P_x` (`oQPT`): the graph without labels, and the rounds `selRounds D d` of
[II, Lemmas 4.13, 4.14] at the `P`-form; every other output graph is kept.

The clauses (F1)–(F5) of `QExpFamilyStmt` and the map clause of (F6) for this family:
* `selRunFam_clauses`: the length, the value and the clauses `qExpansionOut'` ((F1), (F2)), and
  the output graphs that are not plain ((F5));
* `selRunFam_coherent`: coherence in the error order ((F3));
* `selRunFam_pmBlock`: the order of the output graphs with `⊕`, `⊖` in one dotted block ((F4));
* `selRunFam_molMono`: the atom map of every output graph is `Graph.MolMono` (the map conjunct of
  (F6), the observation in the proof of [II, Lemma 6.5 (4)]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The family -/

section SelRunDef

variable {k : ℕ}

open Classical in
/-- The second part of the family at an output graph `g` of `selStep1` with label atom `X`: if `g`
is plain, of the form `Γ_ω Q_X(Γ̃_ω)` and not a `Q`-graph, the two terms of `Q_X = 1 - P_X`, the
graph without labels and the rounds `selRounds D d X` at the `P`-form; otherwise `g` itself. -/
def selRunTail (D d : ℕ) {n : ℕ} (X : Atom k n) (g : Graph k n) : TExpansion k n :=
  if g.Plain ∧ g.IsQFormAt X ∧ ¬ g.IsQGraphAt X then
    Tracked.self g.dropLabels :: selRounds D d X (g.qpGraph X)
  else [Tracked.self g]

/-- **The family of `Q`-expansions** of [II, Lemma 4.15] at error order `D`, label atom `x` and
graph `Γ`: the run `selStep1` with Taylor degree `selDeg D Γ`, then `selRunTail` at the image of
`x` in every output graph. -/
def selRunFam (D n₀ : ℕ) (x : Fin n₀) (Γ : Graph k n₀) : TExpansion k n₀ :=
  (selStep1 (selDeg D Γ) (.inr x) Γ).flatMap fun t =>
    (selRunTail D (selDeg D Γ) (t.f (.inr x)) t.g).map t.comp

/-- An output graph of the family is the composite of an output `t` of `selStep1` with a term of
`selRunTail` at `t`. -/
theorem SelRun_fam_mem {D n₀ : ℕ} {x : Fin n₀} {Γ : Graph k n₀} {s : Tracked k n₀}
    (hs : s ∈ selRunFam D n₀ x Γ) :
    ∃ t ∈ selStep1 (selDeg D Γ) (.inr x) Γ,
      ∃ u ∈ selRunTail D (selDeg D Γ) (t.f (.inr x)) t.g, s = t.comp u := by
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
  exact ⟨t, ht, u, hu, rfl⟩

/-- The terms of `selRunTail`. -/
theorem SelRun_tail_mem {D d n : ℕ} {X : Atom k n} {g : Graph k n} {u : Tracked k n}
    (hu : u ∈ selRunTail D d X g) :
    (¬ (g.Plain ∧ g.IsQFormAt X ∧ ¬ g.IsQGraphAt X) ∧ u = Tracked.self g) ∨
      ((g.Plain ∧ g.IsQFormAt X ∧ ¬ g.IsQGraphAt X) ∧
        (u = Tracked.self g.dropLabels ∨ u ∈ selRounds D d X (g.qpGraph X))) := by
  classical
  unfold selRunTail at hu
  split_ifs at hu with h
  · exact Or.inr ⟨h, List.mem_cons.1 hu⟩
  · exact Or.inl ⟨h, List.mem_singleton.1 hu⟩

/-- A tracked graph composed with its own graph and the identity map. -/
theorem SelRun_comp_self {n : ℕ} (t : Tracked k n) : t.comp (Tracked.self t.g) = t := by
  rcases t with ⟨m, g, f⟩
  rfl

/-- The dot excess is nonnegative. -/
theorem SelRun_dotExcess_nonneg {n : ℕ} (g : Graph k n) : 0 ≤ g.dotExcess := by
  rw [selStep2_dotExcess_eq, selStep2_excL_eq]
  exact step3_eL_nonneg _

/-- The scaling order counted as in the paper is at most the scaling order. -/
theorem SelRun_paperOrd_le {n : ℕ} (g : Graph k n) : g.paperOrd ≤ g.ord := by
  have := SelRun_dotExcess_nonneg g
  unfold Graph.paperOrd
  linarith

end SelRunDef

/-! ## Composition of the clauses -/

section SelRunBind

variable {k : ℕ}

/-- Expanding every term of `R` by a formal sum with the value of the term. -/
private theorem SelRun_bind {n A B K : ℕ} {g : Graph k n} (R : TExpansion k n)
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

end SelRunBind

/-! ## The clauses (F1), (F2), (F5) -/

section SelRunClauses

/-- **[II, Lemma 4.15] for the family** (the clauses (F1), (F2), (F5) of `QExpFamilyStmt`): for
all `C`, `j`, `D` there are `K`, `C'` such that for every normal regular graph
`Γ = Γ₀ Q_x(Γ̃₀)` with bound `C` (`x` internal, plain) of scaling order at least `D + 1 - j`, the
family has at most `K` terms and the value of `Γ`, every output graph has the clauses
`qExpansionOut' D C'`, and an output graph that is not plain has no `G^{(T)}`, `(G_{xx})⁻¹` or
dotted loop and paper scaling order `> D`. -/
theorem selRunFam_clauses (C j D : ℕ) :
    ∃ K C' : ℕ, ∀ (n₀ : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀),
      Γ.Normal C → Γ.IsQFormAt (.inr x) → Γ.Plain → (D : ℤ) + 1 ≤ Γ.ord + j →
      (selRunFam D n₀ x Γ).length ≤ K ∧ (selRunFam D n₀ x Γ).ValueEq Γ modelAdm ∧
      ∀ t ∈ selRunFam D n₀ x Γ, qExpansionOut' D C' (.inr x) Γ t ∧
        (¬ t.g.Plain → t.g.Clean ∧ (D : ℤ) < t.g.paperOrd) := by
  obtain ⟨K₁, C₁, h1⟩ := selStep1_clauses 3 C (D + j + 2 * C)
  obtain ⟨K₂, C₂, h2⟩ := selRounds_clauses 3 D C₁ j (D + j + 2 * C)
  refine ⟨K₁ * (K₂ + 1), max C₁ C₂, ?_⟩
  intro n₀ x Γ hN hQ hP hD
  set d := selDeg D Γ with hd
  have hde : d ≤ D + j + 2 * C := selDeg_le hN hD
  have hpd : (D : ℤ) + 1 ≤ Γ.paperOrd + d := selDeg_add D Γ
  have hΓe := SelRun_dotExcess_nonneg Γ
  obtain ⟨hl₁, hv₁, ho₁⟩ := h1 n₀ x Γ d hde hN hQ hP
  have hC₁ : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hC₂ : C₂ ≤ max C₁ C₂ := le_max_right _ _
  refine SelRun_bind _ _ _ hv₁ hl₁ le_rfl fun t₁ ht₁ => ?_
  obtain ⟨hcl₁, hoo₁, hcase₁'⟩ := ho₁ t₁ ht₁
  have hDd : (D : ℤ) ≤ Γ.ord + d := by unfold Graph.paperOrd at hpd; linarith
  obtain ⟨hB₁, hnew₁, hcase₁, hiv₁⟩ := hcl₁ D hDd
  obtain ⟨hN₁, hord₁, hX₁, he₁, hr₁, hd₁, hc₁⟩ := hB₁
  have hnoNew : ∀ u, ¬ t₁.IsNew u := hnew₁
  have hB₁' : t₁.QBase (max C₁ C₂) (.inr x) Γ :=
    ⟨normal_mono hN₁ hC₁, hord₁, hX₁, he₁, hr₁, hd₁, hc₁⟩
  have hpo₁ : Γ.paperOrd ≤ t₁.g.paperOrd := by unfold Graph.paperOrd; linarith
  set X₁ := t₁.f (.inr x) with hX₁def
  by_cases hcond : t₁.g.Plain ∧ t₁.g.IsQFormAt X₁ ∧ ¬ t₁.g.IsQGraphAt X₁
  swap
  · -- the output graph kept
    have hF : selRunTail D d X₁ t₁.g = [Tracked.self t₁.g] := by
      unfold selRunTail
      rw [ite_eq_right hcond]
    rw [hF]
    refine ⟨by simp, valueEq_self _, fun u hu => ?_⟩
    rw [List.mem_singleton.1 hu, SelRun_comp_self]
    by_cases hpq : t₁.g.Plain ∧ t₁.g.IsQFormAt X₁
    · have hg : t₁.g.IsQGraphAt X₁ := by
        by_contra h
        exact hcond ⟨hpq.1, hpq.2, h⟩
      refine ⟨⟨⟨hB₁', Or.inl ⟨hpq.1, Or.inr hg⟩, fun v hv => absurd hv (hnoNew v), ?_⟩,
        fun hO => hoo₁ 0 hO⟩, fun h => absurd hpq.1 h⟩
      intro _ hlf _
      obtain ⟨c, hc, hcl⟩ := hg.1
      rw [hlf c hc] at hcl
      cases hcl
    · obtain ⟨hcl, hge⟩ := hcase₁' hpq
      have hd' : (D : ℤ) + 1 ≤ t₁.g.ord := by
        have := SelRun_paperOrd_le t₁.g
        linarith
      refine ⟨⟨⟨hB₁', Or.inr ⟨hd', hcl⟩, fun v hv => absurd hv (hnoNew v), ?_⟩,
        fun hO => hoo₁ 0 hO⟩, fun _ => ⟨hcl, by linarith⟩⟩
      intro _ _ hle
      exact absurd (hd'.trans hle) (by omega)
  -- `Q_x = 1 - P_x`, then the rounds on the `P`-graph
  obtain ⟨hp₁, hq₁, hg⟩ := hcond
  have hF : selRunTail D d X₁ t₁.g =
      Tracked.self t₁.g.dropLabels :: selRounds D d X₁ (t₁.g.qpGraph X₁) := by
    unfold selRunTail
    rw [ite_eq_left ⟨hp₁, hq₁, hg⟩]
  rw [hF]
  obtain ⟨y₁, hy₁⟩ := exists_inr_of_isRight hr₁
  set gP : Graph 3 t₁.nOut := t₁.g.qpGraph X₁ with hgP
  have hsP := keepsShape_qp (k := 3) (n := t₁.nOut) X₁
  have hNP : gP.Normal C₁ := relab_normal hsP _ hN₁
  have hPP : gP.IsPFormAt (.inr y₁) := by rw [← hy₁]; exact qpGraph_pForm hq₁
  have hpP : gP.Plain := relab_plain hsP (fun c h => by rwa [qp_label_isSome] at h) _ hp₁
  have hXP : gP.XdotApart := relab_xdotApart hsP _ hX₁
  have hoP : gP.ord = t₁.g.ord := relab_ord hsP _ _
  have heP : gP.dotExcess = t₁.g.dotExcess := relab_dotExcess hsP _ _
  have hpoP : gP.paperOrd = t₁.g.paperOrd := by unfold Graph.paperOrd; rw [hoP, heP]
  obtain ⟨hl₂, hv₂, ho₂⟩ := h2 t₁.nOut y₁ gP d hde hNP hPP hpP hXP (by rw [hoP]; linarith)
  rw [show selRounds D d X₁ gP = selRounds D d (.inr y₁) gP by rw [hy₁]]
  have hstepP : QElemStep ⟨t₁.nOut, t₁.g⟩ ⟨t₁.nOut, gP⟩ :=
    QElemStep.qToP X₁ t₁.g (Tracked.self gP) hq₁ (by rw [oQPT_eq]; simp [gP])
  have hstepD : QElemStep ⟨t₁.nOut, t₁.g⟩ ⟨t₁.nOut, t₁.g.dropLabels⟩ :=
    QElemStep.qToP X₁ t₁.g (Tracked.self t₁.g.dropLabels) hq₁ (by rw [oQPT_eq]; simp)
  have hsD := keepsShape_drop (k := 3) (n := t₁.nOut)
  refine ⟨by simpa using hl₂, ?_, ?_⟩
  · intro Ω ι _ _ PF D₀ hA e
    rw [valR_cons', hv₂ Ω ι PF D₀ hA e]
    exact qp_value t₁.g X₁ hq₁ PF D₀ e
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · -- the term without labels
    have hpD : t₁.g.dropLabels.Plain := relab_plain hsD (fun c h => by simp at h) _ hp₁
    refine ⟨⟨?_, fun hO => MainOO1.comp (hoo₁ : MainOO1 Γ t₁)
      (MainOO1.of_keep (MainOK1.dropLabels hp₁)) 0 hO⟩, fun h => absurd hpD h⟩
    refine ⟨⟨normal_mono (relab_normal hsD _ hN₁) hC₁, ?_, relab_xdotApart hsD _ hX₁, ?_, hr₁,
      fun h => relab_dc hsD _ (hd₁ h), hc₁.tail hstepD⟩, Or.inl ⟨hpD, Or.inl ?_⟩, ?_, ?_⟩
    · change Γ.ord ≤ t₁.g.dropLabels.ord
      rw [show t₁.g.dropLabels.ord = t₁.g.ord from relab_ord hsD _ _]
      exact hord₁
    · change t₁.g.dropLabels.dotExcess ≤ Γ.dotExcess
      rw [show t₁.g.dropLabels.dotExcess = t₁.g.dotExcess from relab_dotExcess hsD _ _]
      exact he₁
    · intro c hc
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
      rfl
    · intro v hv
      exact absurd hv (hnoNew v)
    · intro hfree _ _
      obtain ⟨hord, c, hc, hcl, hcr, w, hw, hJ⟩ := hiv₁ hfree hp₁ hq₁ hg
      refine ⟨?_, c, hc, hcl, hcr, w, hw, relab_qJoined hsD (fun _ _ => rfl) _ hJ⟩
      change Γ.ord + 1 ≤ t₁.g.dropLabels.ord
      rw [show t₁.g.dropLabels.ord = t₁.g.ord from relab_ord hsD _ _]
      exact hord
  · -- the terms of the rounds
    obtain ⟨⟨⟨hNu, hou, hXu, heu, hru, hdu, hcu⟩, hCu, hWu⟩, hoou, hEu⟩ := ho₂ u hu
    have hue := SelRun_paperOrd_le u.g
    refine ⟨⟨?_, fun hO => MainOO1.comp (hoo₁ : MainOO1 Γ t₁)
      (MainOO1.of_ok (MainOK1.qpGraph hp₁ X₁) hoou) 0 hO⟩, ?_⟩
    · refine ⟨⟨normal_mono hNu hC₂, ?_, hXu, ?_, ?_, fun h => hdu (relab_dc hsP _ (hd₁ h)),
        (hc₁.tail hstepP).trans hcu⟩, ?_, ?_, ?_⟩
      · change Γ.ord ≤ u.g.ord
        linarith
      · change u.g.dotExcess ≤ Γ.dotExcess
        linarith
      · change (u.f X₁).isRight = true
        rw [hy₁]
        exact hru
      · rcases hEu with ⟨hpu, hlu⟩ | ⟨hpu, hlt⟩ | ⟨hclu, hgeu⟩
        · exact Or.inl ⟨hpu, Or.inl hlu⟩
        · exact Or.inr ⟨by change (D : ℤ) + 1 ≤ u.g.ord; linarith, plain_clean hpu⟩
        · exact Or.inr ⟨by change (D : ℤ) + 1 ≤ u.g.ord; linarith, hclu⟩
      · intro v hv
        have hvu : u.IsNew v := by
          intro w hw
          obtain ⟨w', hw'⟩ : ∃ w', t₁.f w' = w := by
            by_contra hne
            push Not at hne
            exact hnoNew w hne
          exact hv w' (show u.f (t₁.f w') = v by rw [hw', hw])
        have := hWu v hvu
        change (u.g.wavedGraph).Reachable (u.f X₁) v
        rw [hy₁]
        exact this
      · intro hfree _ _
        obtain ⟨hord, c, hc, hcl, hcr, w, hw, hJ⟩ := hiv₁ hfree hp₁ hq₁ hg
        refine ⟨?_, c, hc, hcl, hcr, w, hw, ?_⟩
        · change Γ.ord + 1 ≤ u.g.ord
          linarith
        · exact carries_qJoined hCu (relab_qJoined hsP (qp_label_none X₁) _ hJ)
    · intro hnp
      rcases hEu with ⟨hpu, -⟩ | ⟨hpu, -⟩ | ⟨hclu, hgeu⟩
      · exact absurd hpu hnp
      · exact absurd hpu hnp
      · refine ⟨hclu, ?_⟩
        change (D : ℤ) < u.g.paperOrd
        linarith

end SelRunClauses

/-! ## The order of the output graphs and coherence ((F3), (F4)) -/

section SelRunOrder

/-- The clauses `Tracked.QBase` of every output graph of `selStep1` with Taylor degree
`selDeg D Γ`, with some bound. -/
theorem SelRun_step1_base {C n₀ : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} (D : ℕ)
    (hN : Γ.Normal C) (hQ : Γ.IsQFormAt (.inr x)) (hP : Γ.Plain) :
    ∃ C₁ : ℕ, ∀ t ∈ selStep1 (selDeg D Γ) (.inr x) Γ, t.QBase C₁ (.inr x) Γ := by
  obtain ⟨K₁, C₁, h1⟩ := selStep1_clauses 3 C (selDeg D Γ)
  refine ⟨C₁, fun t ht => ?_⟩
  have hpd := selDeg_add D Γ
  have hle := SelRun_paperOrd_le Γ
  exact (((h1 n₀ x Γ _ le_rfl hN hQ hP).2.2 t ht).1 D (by linarith)).1

/-- The facts on the `P`-form `Γ'` of an output graph `t` of `selStep1` that is plain and of the
form `Γ_ω Q_X(Γ̃_ω)`: normal regular, of `P`-form at an internal atom `y` equal to the image of
`x`, plain, without `×`-dotted edge inside a block, with the scaling order counted as in the
paper and the dotted blocks of `t`. -/
theorem SelRun_qp_facts {C₁ n₀ : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} {t : Tracked 3 n₀}
    (hB : t.QBase C₁ (.inr x) Γ) (hp : t.g.Plain) (hq : t.g.IsQFormAt (t.f (.inr x))) :
    ∃ y, t.f (.inr x) = .inr y ∧ (t.g.qpGraph (t.f (.inr x))).Normal C₁ ∧
      (t.g.qpGraph (t.f (.inr x))).IsPFormAt (.inr y) ∧ (t.g.qpGraph (t.f (.inr x))).Plain ∧
      (t.g.qpGraph (t.f (.inr x))).XdotApart ∧
      (t.g.qpGraph (t.f (.inr x))).paperOrd = t.g.paperOrd ∧
      (∀ u v, (t.g.qpGraph (t.f (.inr x))).SameBlock u v ↔ t.g.SameBlock u v) := by
  obtain ⟨y, hy⟩ := exists_inr_of_isRight hB.2.2.2.2.1
  have hsP := keepsShape_qp (k := 3) (n := t.nOut) (t.f (.inr x))
  refine ⟨y, hy, relab_normal hsP _ hB.1, by rw [← hy]; exact qpGraph_pForm hq,
    relab_plain hsP (fun c h => by rwa [qp_label_isSome] at h) _ hp,
    relab_xdotApart hsP _ hB.2.2.1, ?_, fun u v => by
      unfold Graph.qpGraph; rw [relab_sameBlock hsP]⟩
  unfold Graph.paperOrd Graph.qpGraph
  rw [relab_ord hsP, relab_dotExcess hsP]

/-- **(F4) for the family** ([II, §4.4], the strict rise of the scaling order of an output graph
in which `⊕` and `⊖` become one dotted block): for `k = 3` and a normal regular graph
`Γ = Γ₀ Q_x(Γ̃₀)` (`x` internal, plain) in which `⊕` and `⊖` lie in distinct dotted blocks, every
output graph of the family with `⊕` and `⊖` in one dotted block has paper scaling order at least
that of `Γ` plus `1`. -/
theorem selRunFam_pmBlock {C D n₀ : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x)) (hP : Γ.Plain) (hn : ¬ Γ.PMBlock) :
    ∀ s ∈ selRunFam D n₀ x Γ, s.g.PMBlock → Γ.paperOrd + 1 ≤ s.g.paperOrd := by
  intro s hs hpm
  obtain ⟨C₁, hB⟩ := SelRun_step1_base D hN hQ hP
  obtain ⟨t, ht, u, hu, rfl⟩ := SelRun_fam_mem hs
  obtain ⟨ho1, ho2⟩ := selStep1Coh_order (selDeg D Γ) hN hQ hP t ht
  rcases SelRun_tail_mem hu with ⟨-, rfl⟩ | ⟨⟨hp, hq, -⟩, rfl | hu⟩
  · exact (ho2 hn hpm).trans' (by linarith)
  · have hsD := keepsShape_drop (k := 3) (n := t.nOut)
    have hpm' : t.g.PMBlock := by
      rw [Graph.pmBlock_iff_sameBlock] at hpm ⊢
      change t.g.dropLabels.SameBlock _ _ at hpm
      unfold Graph.dropLabels at hpm
      rwa [relab_sameBlock hsD] at hpm
    have hpo : t.g.dropLabels.paperOrd = t.g.paperOrd := by
      unfold Graph.paperOrd Graph.dropLabels
      rw [relab_ord hsD, relab_dotExcess hsD]
    change Γ.paperOrd + 1 ≤ t.g.dropLabels.paperOrd
    rw [hpo]
    exact (ho2 hn hpm').trans' (by linarith)
  · obtain ⟨y, hy, hNP, hPP, hpP, hXP, hpoP, hbP⟩ := SelRun_qp_facts (hB t ht) hp hq
    obtain ⟨hu1, hu2⟩ := selRounds_order D (selDeg D Γ) hNP hPP hpP hXP u
      (by rw [← hy]; exact hu)
    change Γ.paperOrd + 1 ≤ u.g.paperOrd
    by_cases ht' : t.g.PMBlock
    · have := ho2 hn ht'
      linarith
    · have hnP : ¬ (t.g.qpGraph (t.f (.inr x))).PMBlock := by
        rw [Graph.pmBlock_iff_sameBlock, hbP, ← Graph.pmBlock_iff_sameBlock]
        exact ht'
      have := hu2 hnP hpm
      linarith

/-- The formal sum of the graphs of `E` whose scaling order counted as in the paper is `≤ D`,
selected by `P`, up to order. -/
private def SelRun_PEq (P : (Σ n, Graph 3 n) → Bool) {n : ℕ} (E E' : TExpansion 3 n) : Prop :=
  (E.forget.filter P).Perm (E'.forget.filter P)

private theorem SelRun_PEq.of_perm {P : (Σ n, Graph 3 n) → Bool} {n : ℕ} {E E' : TExpansion 3 n}
    (h : E.Perm E') : SelRun_PEq P E E' :=
  (h.map _).filter P

private theorem SelRun_PEq.trans {P : (Σ n, Graph 3 n) → Bool} {n : ℕ}
    {E E' E'' : TExpansion 3 n} (h₁ : SelRun_PEq P E E') (h₂ : SelRun_PEq P E' E'') :
    SelRun_PEq P E E'' :=
  List.Perm.trans h₁ h₂

private theorem SelRun_PEq.append {P : (Σ n, Graph 3 n) → Bool} {n : ℕ}
    {E E' F F' : TExpansion 3 n} (h₁ : SelRun_PEq P E E') (h₂ : SelRun_PEq P F F') :
    SelRun_PEq P (E ++ F) (E' ++ F') := by
  unfold SelRun_PEq TExpansion.forget at *
  rw [List.map_append, List.map_append, List.filter_append, List.filter_append]
  exact h₁.append h₂

/-- A formal sum whose graphs all have scaling order counted as in the paper `> D` has no graph
selected by `P`. -/
private theorem SelRun_filter_nil {P : (Σ n, Graph 3 n) → Bool} {D : ℕ}
    (hPD : ∀ g, P g = true → g.2.paperOrd ≤ D) {n : ℕ} {E : TExpansion 3 n}
    (h : ∀ t ∈ E, (D : ℤ) < t.g.paperOrd) : E.forget.filter P = [] := by
  rw [List.filter_eq_nil_iff]
  intro g hg hP
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hg
  have := hPD _ hP
  have := h t ht
  simp only at *
  omega

private theorem SelRun_forget_map_comp {n : ℕ} (t : Tracked 3 n) (E : TExpansion 3 t.nOut) :
    TExpansion.forget (E.map t.comp) = TExpansion.forget E := by
  simp only [TExpansion.forget, List.map_map]
  rfl

private theorem SelRun_PEq.flatMap {P : (Σ n, Graph 3 n) → Bool} {n : ℕ}
    (G G' : (t : Tracked 3 n) → TExpansion 3 n) :
    ∀ A : TExpansion 3 n, (∀ t ∈ A, SelRun_PEq P (G t) (G' t)) →
      SelRun_PEq P (A.flatMap G) (A.flatMap G')
  | [], _ => List.Perm.refl _
  | t :: A, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h t (List.mem_cons_self ..)).append
      (SelRun_PEq.flatMap G G' A fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))

/-- **(F3) for the family** (coherence in the error order): for a normal
regular graph `Γ = Γ₀ Q_x(Γ̃₀)` (`x` internal, plain) and error orders `D ≤ D'`, the output graphs
of the families at `D` and at `D'` whose scaling order counted as in the paper is `≤ D` are the
same up to order, for every selection `P` of such graphs. -/
theorem selRunFam_coherent {C D D' n₀ : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} (hDD : D ≤ D')
    (hN : Γ.Normal C) (hQ : Γ.IsQFormAt (.inr x)) (hP : Γ.Plain)
    (P : (Σ n, Graph 3 n) → Bool) (hPD : ∀ g, P g = true → g.2.paperOrd ≤ D) :
    ((selRunFam D' n₀ x Γ).forget.filter P).Perm ((selRunFam D n₀ x Γ).forget.filter P) := by
  set d := selDeg D Γ with hd
  set d' := selDeg D' Γ with hd'
  have hdd : d ≤ d' := selDeg_mono Γ hDD
  have hpd : (D : ℤ) + 1 ≤ Γ.paperOrd + d := selDeg_add D Γ
  obtain ⟨A, B, B', h1, h2, hBB⟩ := selStep1Coh_coherent hdd hN hQ hP
  obtain ⟨C₁, hB₁⟩ := SelRun_step1_base D hN hQ hP
  obtain ⟨C₁', hB₁'⟩ := SelRun_step1_base D' hN hQ hP
  set G : (t : Tracked 3 n₀) → TExpansion 3 n₀ := fun t =>
    (selRunTail D d (t.f (.inr x)) t.g).map t.comp with hG
  set G' : (t : Tracked 3 n₀) → TExpansion 3 n₀ := fun t =>
    (selRunTail D' d' (t.f (.inr x)) t.g).map t.comp with hG'
  -- the outputs at a term of high order have high order
  have hhigh : ∀ (E : ℕ) (e : ℕ) (C₂ : ℕ) (t : Tracked 3 n₀), t.QBase C₂ (.inr x) Γ →
      (D : ℤ) + 2 ≤ t.g.paperOrd → ∀ s ∈ (selRunTail E e (t.f (.inr x)) t.g).map t.comp,
        (D : ℤ) < s.g.paperOrd := by
    intro E e C₂ t hBt hpt s hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    rcases SelRun_tail_mem hu with ⟨-, rfl⟩ | ⟨⟨hp, hq, -⟩, rfl | hu⟩
    · change (D : ℤ) < t.g.paperOrd; linarith
    · have hsD := keepsShape_drop (k := 3) (n := t.nOut)
      change (D : ℤ) < t.g.dropLabels.paperOrd
      unfold Graph.paperOrd Graph.dropLabels
      rw [relab_ord hsD, relab_dotExcess hsD]
      unfold Graph.paperOrd at hpt
      linarith
    · obtain ⟨y, hy, hNP, hPP, hpP, hXP, hpoP, -⟩ := SelRun_qp_facts hBt hp hq
      have := (selRounds_order E e hNP hPP hpP hXP u (by rw [← hy]; exact hu)).1
      change (D : ℤ) < u.g.paperOrd
      linarith
  have hB : SelRun_PEq P (B.flatMap G) [] := by
    unfold SelRun_PEq
    rw [SelRun_filter_nil hPD (E := B.flatMap G)]
    · rfl
    · intro s hs
      obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 hs
      have htm : t ∈ selStep1 d (.inr x) Γ := h1.symm.subset (List.mem_append_right _ ht)
      exact hhigh D d C₁ t (hB₁ t htm) (by have := hBB t (List.mem_append_left _ ht); linarith)
        s hs
  have hB' : SelRun_PEq P (B'.flatMap G') [] := by
    unfold SelRun_PEq
    rw [SelRun_filter_nil hPD (E := B'.flatMap G')]
    · rfl
    · intro s hs
      obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 hs
      have htm : t ∈ selStep1 d' (.inr x) Γ := h2.symm.subset (List.mem_append_right _ ht)
      exact hhigh D' d' C₁' t (hB₁' t htm)
        (by have := hBB t (List.mem_append_right _ ht); linarith) s hs
  have hA : SelRun_PEq P (A.flatMap G') (A.flatMap G) := by
    refine SelRun_PEq.flatMap G' G A fun t ht => ?_
    have htm : t ∈ selStep1 d (.inr x) Γ := h1.symm.subset (List.mem_append_left _ ht)
    simp only [hG, hG']
    unfold selRunTail
    split_ifs with hcond
    · obtain ⟨hp, hq, -⟩ := hcond
      obtain ⟨y, hy, hNP, hPP, hpP, hXP, hpoP, -⟩ := SelRun_qp_facts (hB₁ t htm) hp hq
      have hpo := (selStep1Coh_order d hN hQ hP t htm).1
      obtain ⟨A₂, B₂, B₂', h₁, h₂, h₃⟩ := selRounds_coherent hNP hPP hpP hXP hDD hdd
        (by rw [hpoP]; linarith)
      rw [← hy] at h₁ h₂
      have hrel : SelRun_PEq P ((selRounds D' d' (t.f (.inr x))
          (t.g.qpGraph (t.f (.inr x)))).map t.comp)
          ((selRounds D d (t.f (.inr x)) (t.g.qpGraph (t.f (.inr x)))).map t.comp) := by
        unfold SelRun_PEq
        rw [SelRun_forget_map_comp, SelRun_forget_map_comp]
        refine (SelRun_PEq.of_perm h₂).trans (SelRun_PEq.trans ?_ (SelRun_PEq.of_perm h₁.symm))
        have hz : ∀ L : TExpansion 3 t.nOut, (∀ u ∈ L, (D : ℤ) < u.g.paperOrd) →
            SelRun_PEq P L [] := by
          intro L hL
          unfold SelRun_PEq
          rw [SelRun_filter_nil hPD hL]
          rfl
        have := (SelRun_PEq.of_perm (P := P) (List.Perm.refl A₂)).append
          ((hz B₂' fun u hu => h₃ u (List.mem_append_right _ hu)).trans
            (hz B₂ fun u hu => h₃ u (List.mem_append_left _ hu)).symm)
        exact this
      rw [List.map_cons, List.map_cons]
      unfold SelRun_PEq at hrel ⊢
      simp only [TExpansion.forget, List.map_cons, List.filter_cons] at hrel ⊢
      split_ifs
      · exact hrel.cons _
      · exact hrel
    · exact List.Perm.refl _
  have e1 : SelRun_PEq P (selRunFam D' n₀ x Γ) (A.flatMap G' ++ B'.flatMap G') := by
    refine SelRun_PEq.of_perm ?_
    unfold selRunFam
    rw [← List.flatMap_append]
    exact h2.flatMap_right _
  have e2 : SelRun_PEq P (A.flatMap G ++ B.flatMap G) (selRunFam D n₀ x Γ) := by
    refine SelRun_PEq.of_perm ?_
    unfold selRunFam
    rw [← List.flatMap_append]
    exact (h1.flatMap_right _).symm
  have e3 := hA.append (hB'.trans hB.symm)
  exact e1.trans (e3.trans e2)

end SelRunOrder

/-! ## The atom maps of the output graphs (the map conjunct of (F6)) -/

section SelRunMolMono

variable {n : ℕ}

/-- A chain of a relation given as a list, from its head to its last element. -/
theorem SelRun_rtg_of_chain {α : Type*} {R : α → α → Prop} :
    ∀ (l : List α) (a b : α), List.IsChain R (a :: l) → (a :: l).getLast? = some b →
      Relation.ReflTransGen R a b
  | [], a, b, _, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    rw [h]
  | g :: l, a, b, hc, h => by
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast?_cons_cons] at h
    exact Relation.ReflTransGen.head hc.1 (SelRun_rtg_of_chain l g b hc.2 h)

/-- The invariant `Graph.InvB'` along a chain of elementary steps. -/
theorem SelRun_invB_of_chain {g g' : Σ m, Graph 3 m} (h : Relation.ReflTransGen QElemStep g g')
    (hI : g.2.InvB') : g'.2.InvB' := by
  induction h with
  | refl => exact hI
  | tail _ hst ih => exact qElemStep_invB _ _ hst ih

/-- A step of the run `selStep1` at an internal atom keeps the molecules from losing crossings,
with the identity map, under the invariant `Graph.InvB'`. -/
theorem SelRun_step_molMono {X : Atom 3 n} (hX : X.isRight = true) {T g : Graph 3 n}
    (h : SelStep1CohStep X T g) (hI : T.InvB') : T.MolMono g id := by
  cases h with
  | split u T g h => exact molMono_oSplitT u X T hI.2.1 hI.2.2.1 hI.2.2.2.1 _ h
  | schur i T g h => exact molMono_oSchurT X hX i T _ h
  | schurW i T g h => exact molMono_oSchurWT X i T _ h
  | absorb T hℓ hl => exact molMono_absorb (.Q, X) T
  | schurRev i T g h => exact molMono_oSchurRevT X hX i T _ h
  | schurWRev i T g h => exact molMono_oSchurWRevT X i T _ h
  | taylor D i T g h => exact molMono_oTaylorT D i T _ h
  | xdot i T g h => exact molMono_oXdotT i T hI.2.1 hI.2.2.1 hI.2.2.2.1 _ h

/-- A chain of steps of the run `selStep1` at an internal atom: the identity map is
`Graph.MolMono`, and the invariant `Graph.InvB'` is kept. -/
theorem SelRun_chain_molMono {X : Atom 3 n} (hX : X.isRight = true) {Γ T : Graph 3 n}
    (h : Relation.ReflTransGen (SelStep1CohStep X) Γ T) (hI : Γ.InvB') :
    Γ.MolMono T id ∧ T.InvB' := by
  induction h with
  | refl => exact ⟨Graph.MolMono.refl Γ, hI⟩
  | tail _ hst ih =>
    exact ⟨ih.1.comp (SelRun_step_molMono hX hst ih.2),
      qElemStep_invB _ _ (hst.qElemStep hX) ih.2⟩

/-- A chain of removals of redundant dotted edges: the identity map is `Graph.MolMono`, and the
invariant `Graph.InvB'` is kept. -/
theorem SelRun_drops_molMono {m : ℕ} {g g' : Graph 3 m}
    (h : Relation.ReflTransGen SelStep1CohDrop g g') (hI : g.InvB') :
    g.MolMono g' id ∧ g'.InvB' := by
  induction h with
  | refl => exact ⟨Graph.MolMono.refl g, hI⟩
  | tail _ hst ih =>
    obtain ⟨i, c, hc, hk, hb, rfl⟩ := hst
    exact ⟨ih.1.comp (molMono_dropDot i _ c hc hk hb),
      qElemStep_invB _ _ (QElemStep.dropDot i _ c hc hk hb) ih.2⟩

/-- A chain of steps of the run, then `O_merge` and removals of redundant dotted edges: the
atom map of `O_merge` is `Graph.MolMono`, and the invariant `Graph.InvB'` is kept. -/
theorem SelRun_final_molMono {X : Atom 3 n} (hX : X.isRight = true) {Γ T : Graph 3 n}
    {s : Tracked 3 n} {g' : Graph 3 s.nOut} (h : Relation.ReflTransGen (SelStep1CohStep X) Γ T)
    (hm : T.mergeT = some s) (hdr : Relation.ReflTransGen SelStep1CohDrop s.g g')
    (hI : Γ.InvB') : Γ.MolMono g' s.f ∧ g'.InvB' := by
  obtain ⟨h1, hIT⟩ := SelRun_chain_molMono hX h hI
  have hIs := qElemStep_invB _ _ (QElemStep.merge T s hm) hIT
  obtain ⟨h3, hI'⟩ := SelRun_drops_molMono hdr hIs
  exact ⟨(h1.comp (molMono_mergeT T s hm)).comp h3, hI'⟩

/-- **The map conjunct of (F6) for the family** (the observation in the proof of
[II, Lemma 6.5 (4)] that the expansions create no new molecule and keep or subdivide the edges
between molecules): for `k = 3` and a normal regular graph `Γ = Γ₀ Q_x(Γ̃₀)` (`x` internal, plain)
with the invariant `Graph.InvB'`, every output graph `s` of the family is `Graph.MolMono` from `Γ`
with its atom map `s.f`: the composite, in the order of `TExpansion.bind`, of the identity maps
of the steps of `selStep1`, the map of `O_merge`, the identity map of `Q_x = 1 - P_x`, and the
atom map of the rounds. -/
theorem selRunFam_molMono {C D n₀ : ℕ} {x : Fin n₀} {Γ : Graph 3 n₀} (hN : Γ.Normal C)
    (hQ : Γ.IsQFormAt (.inr x)) (hP : Γ.Plain) (hI : Γ.InvB') :
    ∀ s ∈ selRunFam D n₀ x Γ, Γ.MolMono s.g s.f := by
  intro s hs
  obtain ⟨C₁, hB⟩ := SelRun_step1_base D hN hQ hP
  obtain ⟨t, ht, u, hu, rfl⟩ := SelRun_fam_mem hs
  have ht₁ : Γ.MolMono t.g t.f := by
    rcases selStep1Coh_history (selDeg D Γ) hN hQ hP t ht with ⟨-, rfl⟩ |
      ⟨gs, T, s₀, g', hch, hlast, hm, hdr, rfl, -⟩
    · exact Graph.MolMono.refl Γ
    · exact (SelRun_final_molMono rfl (SelRun_rtg_of_chain gs Γ T hch hlast) hm hdr hI).1
  have hIt : t.g.InvB' := SelRun_invB_of_chain (hB t ht).2.2.2.2.2.2 hI
  rcases SelRun_tail_mem hu with ⟨-, rfl⟩ | ⟨⟨hp, hq, -⟩, rfl | hu⟩
  · rw [SelRun_comp_self]
    exact ht₁
  · exact ht₁.comp (molMono_dropLabels t.g)
  · obtain ⟨y, hy, hNP, hPP, hpP, hXP, -, -⟩ := SelRun_qp_facts (hB t ht) hp hq
    have hmem : Tracked.self (t.g.qpGraph (t.f (.inr x))) ∈ oQPT (t.f (.inr x)) t.g := by
      rw [oQPT_eq]; simp
    have hIP := qElemStep_invB _ _ (QElemStep.qToP _ t.g _ hq hmem) hIt
    have h₂ := molMono_oQPT _ t.g _ hmem
    exact (ht₁.comp h₂).comp
      (selRounds_molMono D (selDeg D Γ) hNP hPP hpP hXP hIP u (by rw [← hy]; exact hu))

end SelRunMolMono

/-! ## Decidability instances for concrete graphs -/

section SelRunInstances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance SelRun_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance SelRun_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (SelRun_decAdjDot Γ) u v

private instance SelRun_decIsQFormAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.IsQFormAt u) := by
  unfold Graph.IsQFormAt; infer_instance

end SelRunInstances

end RBM8D.Graphs
