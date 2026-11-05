import RBM8D.Graph.Local.DotNorm

/-!
# Light weights and solid edges at equal order under the local expansions

For a graph without dotted edges, consider the label-free outputs of the local expansions
`O^{(x)}_weight`, `O^{(x)}_multi-e`, `O^{(x)}_GG` (also in its transposed form) and `O^{(x)}_GḠ`
([I, Lemmas 3.9, 3.13, 3.16, 3.19]) whose order in the count of [II, (2.5)] (`Graph.paperOrd`)
equals that of the input. Such outputs have dot excess `0`. The edge expansions raise neither the
number of light weights nor the number of solid edges. The weight expansion lowers the number of
light weights, or keeps both numbers. The order bound of `O_dot` ([I, Def 3.2]) used here is
`dot_paperOrd_succ`: on an input without dotted edges, an output with positive dot excess has an
order at least `1` above the input, up to the order surplus of the input.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section SolidCount

variable {k n : ℕ}

/-- The number of solid edges `G_{uv}`, `Ḡ_{uv}` of a graph. -/
def Graph.solidN (g : Graph k n) : ℕ := (g.comps.filter fun c => c.kind.isSolid).length

end SolidCount

/-! ## The order bound of `O_dot` at positive dot excess -/

section Excess

variable {k n : ℕ}

/-- Without dotted components, reachability by dotted components is equality. -/
private theorem SolidMono.dg_reach_eq {L : List (Comp (Atom k n))}
    (hL : ∀ c ∈ L, c.kind ≠ .dot) {a b : Atom k n} (h : (dg L).Reachable a b) : a = b := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ =>
    obtain ⟨-, c, hc, hk, -⟩ := dg_adj.1 hadj
    exact absurd hk (hL c hc)

private theorem SolidMono.nD_zero {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.kind ≠ .dot) :
    nD L = 0 := by
  unfold nD
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc
  simpa using h c hc

/-- A list with at most one dotted component, not a loop, has dot excess `0`. -/
private theorem SolidMono.eL_zero {L : List (Comp (Atom k n))} (h1 : nD L ≤ 1)
    (h2 : ∀ c ∈ L, c.kind = .dot → c.x ≠ c.y) : eL L = 0 := by
  apply eL_eq_zero_of_nonRed
  intro c L' hp hk hr
  have hc : c ∈ L := hp.symm.subset (List.mem_cons_self ..)
  have hn := nD_perm hp
  rw [nD_cons, ite_eq_left hk] at hn
  have h0 : ∀ d ∈ L', d.kind ≠ .dot := by
    intro d hd hdk
    have : 0 < nD L' := List.length_pos_of_mem (List.mem_filter.2 ⟨hd, by simp [hdk]⟩)
    omega
  exact h2 c hc hk (SolidMono.dg_reach_eq h0 hr)

/-- A graph without dotted edges has dot excess `0`. -/
private theorem SolidMono.dotExcess_zero {g : Graph k n} (h : ∀ c ∈ g.comps, c.kind ≠ .dot) :
    g.dotExcess = 0 :=
  SolidMono.eL_zero (by rw [SolidMono.nD_zero h]; omega) fun c hc hk => absurd hk (h c hc)

/-- The dotted components added by a term of `dotChoice`: one for each pair of `A`. -/
private theorem SolidMono.added_dots (SP A : List (Atom k n × Atom k n × Bool)) :
    nD (addedComps SP A) = (SP.filter fun p => decide (p ∈ A)).length := by
  induction SP with
  | nil => rfl
  | cons p SP ih =>
    unfold addedComps at ih ⊢
    rw [List.filterMap_cons]
    by_cases hp : p ∈ A
    · rw [ite_eq_left hp]
      rw [nD_cons, ih, List.filter_cons_of_pos (by simpa using hp)]
      simp [mkC]
    · rw [ite_eq_right hp, List.filter_cons_of_neg (by simpa using hp)]
      by_cases h2 : p.2.2 = true
      · rw [ite_eq_left h2, nD_cons, ih]
        simp [mkC]
      · rw [ite_eq_right h2]
        exact ih

private theorem SolidMono.length_le_one {α : Type*} {l : List α} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a = b) : l.length ≤ 1 := by
  match l, hl, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: l, hl, h =>
    exfalso
    have hab := h a (by simp) b (by simp)
    subst hab
    simp at hl

open Classical in
/-- At most one pair of blocks joined: the term of `dotChoice` has at most one dotted component. -/
private theorem SolidMono.nD_dc_le {g : Graph k n} (hg : ∀ c ∈ g.comps, c.kind ≠ .dot)
    (A : List (Atom k n × Atom k n × Bool))
    (hΔ : ccN g.comps ≤ ccN (g.dotChoice g.splitPairs A).comps + 1) :
    nD (g.dotChoice g.splitPairs A).comps ≤ 1 := by
  set dc := g.dotChoice g.splitPairs A with hdc
  have hJ := ccN_dc_le g g.splitPairs A
  rw [← hdc] at hJ
  have hGH : ∀ a b, (dg g.comps).Reachable a b → (dg dc.comps).Reachable a b :=
    fun _ _ hr => dc_reach g _ A hr
  -- every pair of `A` joins two atoms joined in the term
  have hreach : ∀ p ∈ g.splitPairs.filter (fun p => decide (p ∈ A)),
      (dg dc.comps).Reachable p.1 p.2.1 := by
    intro p hp
    obtain ⟨hpS, hpA⟩ := List.mem_filter.1 hp
    have hmem : mkC .dot p.1 p.2.1 ∈ dc.comps := by
      rw [hdc, dc_comps]
      exact List.mem_append_right _ (mem_addedComps.2 ⟨p, hpS, Or.inl ⟨by simpa using hpA, rfl⟩⟩)
    exact dg_reach_of_mem hmem rfl
  have hcount : nD dc.comps = (g.splitPairs.filter fun p => decide (p ∈ A)).length := by
    rw [hdc, dc_comps, nD_append, nD_kept, SolidMono.nD_zero hg, zero_add, SolidMono.added_dots]
  rw [hcount]
  apply SolidMono.length_le_one ((splitPairs_nodup g).filter _)
  intro p hp p' hp'
  have hpS := (List.mem_filter.1 hp).1
  have hpS' := (List.mem_filter.1 hp').1
  rcases Nat.lt_or_ge (ccN dc.comps) (ccN g.comps) with h1 | h0
  · -- two blocks joined into one: both pairs join these two blocks
    have hc1 : Nat.card (dg g.comps).ConnectedComponent =
        Nat.card (dg dc.comps).ConnectedComponent + 1 := by
      change ccN g.comps = ccN dc.comps + 1
      omega
    obtain ⟨a, b, -, -, hab⟩ := reach_of_card_cc_succ hGH hc1
    have hends : ∀ q ∈ g.splitPairs.filter (fun p => decide (p ∈ A)),
        (q.1 = a ∧ q.2.1 = b) ∨ (q.1 = b ∧ q.2.1 = a) := by
      intro q hq
      have hqS := (List.mem_filter.1 hq).1
      rcases hab _ _ (hreach q hq) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (SolidMono.dg_reach_eq hg h) (sp_ne hqS)
      · exact Or.inl ⟨SolidMono.dg_reach_eq hg h1, SolidMono.dg_reach_eq hg h2⟩
      · exact Or.inr ⟨SolidMono.dg_reach_eq hg h1, SolidMono.dg_reach_eq hg h2⟩
    obtain ⟨hq, -, hs⟩ := mem_splitPairs.1 hpS
    obtain ⟨hq', -, hs'⟩ := mem_splitPairs.1 hpS'
    have hrel : (p'.1, p'.2.1) = (p.1, p.2.1) ∨ (p'.1, p'.2.1) = (p.1, p.2.1).swap := by
      rcases hends p hp with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hends p' hp' with ⟨e3, e4⟩ | ⟨e3, e4⟩
      · left; rw [e1, e2, e3, e4]
      · right; rw [e1, e2, e3, e4]; rfl
      · right; rw [e1, e2, e3, e4]; rfl
      · left; rw [e1, e2, e3, e4]
    have heq := spUniq_eq hq hq' hrel
    have e1 : p'.1 = p.1 := congrArg (fun q : Atom k n × Atom k n => q.1) heq
    have e2 : p'.2.1 = p.2.1 := congrArg (fun q : Atom k n × Atom k n => q.2) heq
    have e3 : p'.2.2 = p.2.2 := by rw [hs, hs', e1, e2]
    exact (Prod.ext e1 (Prod.ext e2 e3)).symm
  · -- no blocks joined: no pair at all
    exfalso
    have hc0 : Nat.card (dg g.comps).ConnectedComponent =
        Nat.card (dg dc.comps).ConnectedComponent := by
      change ccN g.comps = ccN dc.comps
      omega
    have h := reach_of_card_cc_eq hGH hc0 _ _ (hreach p hp)
    exact sp_ne hpS (SolidMono.dg_reach_eq hg h)

open Classical in
/-- `O_dot` ([I, Def 3.2]) at a graph `g` without dotted edges: an output with positive dot
excess has order (in the count of [II, (2.5)]) at least that of `g` plus `1`, up to the order
surplus `s` of `g`. -/
theorem dot_paperOrd_succ {g : Graph k n} (_hd : DotIn g) {s : ℕ} {nw : Atom k n → Bool}
    (hn : DotNew g s nw) (hg : ∀ c ∈ g.comps, c.kind ≠ .dot) {t : Tracked k n}
    (ht : t ∈ oDotT g) (hε : 0 < t.g.dotExcess) : g.paperOrd + 1 ≤ t.g.paperOrd + s := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exfalso
    have : (Tracked.self g).g.dotExcess = 0 := SolidMono.dotExcess_zero hg
    omega
  have hs := mergeT_spec hm
  have hobl := hs.obl_eq
  have hdco := dc_obl g g.splitPairs A
  have hJ := ccN_dc_le g g.splitPairs A
  rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl]
  by_cases h2 : ccN (g.dotChoice g.splitPairs A).comps + 2 ≤ ccN g.comps
  · have hle := convN_le hm
    have h4 : (g.comps.filter fun c => unpB g c &&
        decide ((dg (g.dotChoice g.splitPairs A).comps).Reachable c.x c.y)).length ≤
        (g.comps.filter (unpB g)).length :=
      length_filter_mono _ _ _ fun c _ hc => by
        simp only [Bool.and_eq_true] at hc; exact hc.1
    have hf := hn.four
    have hz := hn.zero
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · have := hz hs0
      subst hs0
      push_cast
      omega
    · omega
  · exfalso
    have hdots := SolidMono.nD_dc_le hg A (by omega)
    have hnt : nD t.g.comps ≤ 1 := by
      have := nD_filterMap_mergeComp (g.dotChoice g.splitPairs A).mrep t.f
        (g.dotChoice g.splitPairs A).comps
      rw [← hs.comps_eq] at this
      omega
    have hloop : ∀ c ∈ t.g.comps, c.kind = .dot → c.x ≠ c.y := by
      intro c' hc' hk'
      obtain ⟨c, hc, hmc⟩ := hs.mem_comps.1 hc'
      have hk : c.kind = .dot := by
        rcases mergeComp_kind hmc with h | ⟨ch, -, h⟩
        · rw [← h]; exact hk'
        · rw [h] at hk'; cases hk'
      rw [mergeComp_dot hk] at hmc
      split_ifs at hmc with hf
      obtain rfl := Option.some.inj hmc
      exact hf
    have := SolidMono.eL_zero hnt hloop
    change 0 < eL t.g.comps at hε
    omega

end Excess

/-! ## Facts on `O_dot` -/

section DotFacts

variable {k n : ℕ}

/-- `O_dot` keeps the number of light weights. -/
private theorem SolidMono.lwN_oDotT {g : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT g) :
    t.g.lwN = g.lwN := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · rfl
  · rw [(mergeT_spec hm).lwN_eq]
    have := dc_count g g.splitPairs A Kind.isLt rfl rfl (fun _ => true)
    simpa [Graph.lwN] using this

/-- `O_dot` creates no solid loop. -/
private theorem SolidMono.noLoop_oDotT {g : Graph k n}
    (h : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y) {t : Tracked k n} (ht : t ∈ oDotT g) :
    ∀ c ∈ t.g.comps, c.kind.isSolid = true → c.x ≠ c.y := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact h
  · have hs := mergeT_spec hm
    intro c' hc' hsol
    obtain ⟨c, hc, hmc⟩ := hs.mem_comps.1 hc'
    have hcs : c.kind.isSolid = true := by
      rcases mergeComp_kind hmc with h1 | ⟨ch, -, h2⟩
      · rwa [← h1]
      · rw [h2] at hsol; cases hsol
    rw [mergeComp_solid hcs] at hmc
    split_ifs at hmc with hr
    · obtain rfl := Option.some.inj hmc
      exfalso
      obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
        cases hk : c.kind <;> simp_all [Kind.isSolid]
      simp [hch, Kind.toWeight, Kind.isSolid] at hsol
    · obtain rfl := Option.some.inj hmc
      exact hs.f_ne _ _ hr

/-- A label-free output of `O_dot` comes from a label-free graph. -/
private theorem SolidMono.lf_back {g : Graph k n} (hP : g.Plain) {t : Tracked k n}
    (ht : t ∈ oDotT g) (hlf : t.g.LabelFree) : g.LabelFree :=
  oDotT_lf_back hP ht hlf

end DotFacts

/-! ## Terms of a local operation -/

section Terms

variable {k n : ℕ}

/-- The data of a term with `TermOK` at a graph without dotted edges: it has no dotted edge, is an
input of `O_dot`, and its order exceeds that of the graph by its order surplus. -/
private theorem SolidMono.termOK_data {C : ℕ} {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (hT : TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree) (hX : Γ.XdotApart)
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∃ s : ℕ, ∃ nw : Atom k T.nOut → Bool, DotIn T.g ∧ DotNew T.g s nw ∧
      (∀ c ∈ T.g.comps, c.kind ≠ .dot) ∧ T.g.obl = Γ.obl + s := by
  obtain ⟨j, R, N, lab, g, s, rfl, hS, hNo, -, hs, two, old, four, zero, -⟩ := hT
  have hNd : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
    fun c hc => ⟨(hNo c hc).1.ne_dot, (hNo c hc).1.ne_xdot'⟩
  have hgD : ∀ c ∈ g.comps, c.kind ≠ .dot := by
    intro c hc
    rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
    · rw [labF_kind]; exact hD c₀ hc₀
    · rw [labF_kind]; exact (hNd c₁ hc₁).1
  have hexc : g.dotExcess = Γ.dotExcess := hS.dotExcess (fun c hc => (hNd c hc).1)
  have hord : g.ord = Γ.ord + s := by
    have := hS.ord
    linarith
  refine ⟨s, isNewA n, hS.dotIn hN hP hL hX hNo, hS.dotNew hN hNd two old four zero, hgD, ?_⟩
  simp only [Graph.obl, hord, hexc]
  ring

/-- After a term with `TermOK` at a graph without dotted edges, an output of `O_dot` of order at
most that of the graph has dot excess `0`. -/
private theorem SolidMono.termOK_exc {C : ℕ} {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (hT : TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree) (hX : Γ.XdotApart)
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) {t : Tracked k T.nOut} (ht : t ∈ oDotT T.g)
    (heq : t.g.obl ≤ Γ.obl) : t.g.dotExcess = 0 := by
  obtain ⟨s, nw, hd, hn, hgD, hobl⟩ := SolidMono.termOK_data hT hN hP hL hX hD
  have h0 : 0 ≤ t.g.dotExcess := eL_nonneg _
  by_contra hne
  have := dot_paperOrd_succ hd hn hgD ht (by omega)
  rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl] at this
  omega

/-- The outputs of a bind of `O_dot` over terms with `TermOK`, at a graph without dotted edges:
at order at most that of the graph, dot excess `0`; no solid loop. -/
private theorem SolidMono.bind_exc {C : ℕ} {Γ : Graph k n} {x : Atom k n} {E : TExpansion k n}
    (hE : ∀ T ∈ E, TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree)
    (hX : Γ.XdotApart) (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), (t.g.obl ≤ Γ.obl → t.g.dotExcess = 0) ∧
      ∀ c ∈ t.g.comps, c.kind.isSolid = true → c.x ≠ c.y := by
  intro t ht
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  refine ⟨fun h => SolidMono.termOK_exc (hE T hT) hN hP hL hX hD hs h, ?_⟩
  obtain ⟨-, -, hd, -, -, -⟩ := SolidMono.termOK_data (hE T hT) hN hP hL hX hD
  exact SolidMono.noLoop_oDotT hd.noLoop hs

end Terms

/-! ## Degrees and solid edges -/

section Degrees

variable {k n : ℕ}

open Classical in
private theorem SolidMono.sum_deg_list (L : List (Comp (Atom k n)))
    (h : ∀ c ∈ L, c.kind.isSolid = true → c.x ≠ c.y) :
    ∑ a : Atom k n, (L.filter fun c => c.kind.isSolid && (c.x == a || c.y == a)).length =
      2 * (L.filter fun c => c.kind.isSolid).length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [← List.countP_eq_length_filter, List.countP_cons] at ih' ⊢
    rw [Finset.sum_add_distrib, ih']
    by_cases hs : c.kind.isSolid = true
    · have hxy := h c (List.mem_cons_self ..) hs
      have key : ∑ a : Atom k n, (if (c.kind.isSolid && (c.x == a || c.y == a)) = true then 1
          else 0) = 2 := by
        rw [Finset.sum_boole]
        have : (Finset.univ.filter fun a : Atom k n =>
            (c.kind.isSolid && (c.x == a || c.y == a)) = true) = {c.x, c.y} := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, hs, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
          constructor
          · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
          · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
        rw [this, Finset.card_pair hxy]
        rfl
      rw [key, ite_eq_left hs]
      ring
    · have key : ∑ a : Atom k n, (if (c.kind.isSolid && (c.x == a || c.y == a)) = true then 1
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        simp [hs]
      rw [key, ite_eq_right hs]
      ring

/-- Twice the number of solid edges is the sum of the degrees, when no solid edge is a loop. -/
private theorem SolidMono.sum_deg {g : Graph k n}
    (h : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y) : ∑ a, g.deg a = 2 * g.solidN :=
  SolidMono.sum_deg_list g.comps h

open Classical in
/-- The sum over the atoms of an output is at most the sum over the images of the atoms of the
input plus the sum over the new atoms. -/
private theorem SolidMono.sum_le_image {m : ℕ} (f : Atom k n → Atom k m) (d : Atom k m → ℕ) :
    ∑ a, d a ≤ ∑ v, d (f v) + ∑ a ∈ Finset.univ.filter (fun a => ∀ v, f v ≠ a), d a := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => ∃ v, f v = a)]
  have h1 : (Finset.univ.filter fun a => ∃ v, f v = a) = Finset.univ.image f := by
    ext a; simp
  have h2 : (Finset.univ.filter fun a => ¬ ∃ v, f v = a) =
      Finset.univ.filter (fun a => ∀ v, f v ≠ a) := by
    ext a; simp
  rw [h1, h2]
  gcongr
  exact Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _

open Classical in
/-- Degree data of an output give the bound on its solid edges: if the image of every atom `v`
has degree at most `deg v - b v`, and the new atoms have total degree at most `∑ b`, then the
output has at most as many solid edges. -/
private theorem SolidMono.solidN_le {Γ : Graph k n} {t : Tracked k n}
    (hΓ : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (ht : ∀ c ∈ t.g.comps, c.kind.isSolid = true → c.x ≠ c.y) (b : Atom k n → ℕ)
    (hpt : ∀ v, t.g.deg (t.f v) + b v ≤ Γ.deg v)
    (hnew : ∑ a ∈ Finset.univ.filter (fun a => ∀ v, t.f v ≠ a), t.g.deg a ≤ ∑ v, b v) :
    t.g.solidN ≤ Γ.solidN := by
  have h1 := SolidMono.sum_deg ht
  have h2 := SolidMono.sum_deg hΓ
  have h3 := SolidMono.sum_le_image t.f t.g.deg
  have h4 : ∑ v, (t.g.deg (t.f v) + b v) ≤ ∑ v, Γ.deg v := Finset.sum_le_sum fun v _ => hpt v
  rw [Finset.sum_add_distrib] at h4
  omega

open Classical in
/-- The degree pattern of case (a) of [I, Lemma 3.13] bounds the solid edges. -/
private theorem SolidMono.solidN_le_me {Γ : Graph k n} {t : Tracked k n} {x : Atom k n}
    (hΓ : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (ht : ∀ c ∈ t.g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hx : t.g.deg (t.f x) + 2 = Γ.deg x)
    (h : ((∃ u, t.IsNew u ∧ t.g.deg u = 2 ∧ ∀ v, t.IsNew v → v = u) ∧
            ∀ v, v ≠ x → t.g.deg (t.f v) = Γ.deg v) ∨
          ((∀ u, t.IsNew u → t.g.deg u = 0) ∧
            ∀ v, v ≠ x → t.g.deg (t.f v) = Γ.deg v ∨ t.g.deg (t.f v) + 2 = Γ.deg v)) :
    t.g.solidN ≤ Γ.solidN := by
  rcases h with ⟨⟨u, hu, hdu, huniq⟩, ho⟩ | ⟨hnew, ho⟩
  · refine SolidMono.solidN_le hΓ ht (fun v => if v = x then 2 else 0) (fun v => ?_) ?_
    · by_cases hv : v = x
      · subst hv; simp [hx]
      · simp [hv, ho v hv]
    · rw [Finset.sum_ite_eq' Finset.univ x (fun _ => 2)]
      simp only [Finset.mem_univ, ite_true]
      calc ∑ a ∈ Finset.univ.filter (fun a => ∀ v, t.f v ≠ a), t.g.deg a
          ≤ ∑ a ∈ ({u} : Finset _), t.g.deg a := by
            apply Finset.sum_le_sum_of_subset
            intro a ha
            have ha' : ∀ v, t.f v ≠ a := (Finset.mem_filter.1 ha).2
            simp [huniq a ha']
        _ = 2 := by simp [hdu]
  · refine SolidMono.solidN_le hΓ ht (fun _ => 0) (fun v => ?_) ?_
    · by_cases hv : v = x
      · subst hv; omega
      · rcases ho v hv with h | h <;> omega
    · have h0 : ∑ a ∈ Finset.univ.filter (fun a => ∀ v, t.f v ≠ a), t.g.deg a = 0 :=
        Finset.sum_eq_zero fun a ha => hnew a (Finset.mem_filter.1 ha).2
      rw [h0]
      exact Nat.zero_le _

open Classical in
/-- The degree pattern of case (b) of [I, Lemmas 3.16, 3.19] bounds the solid edges. -/
private theorem SolidMono.solidN_le_pair {Γ : Graph k n} {t : Tracked k n} {x y : Atom k n}
    (hΓ : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (ht : ∀ c ∈ t.g.comps, c.kind.isSolid = true → c.x ≠ c.y) (h : t.PairRemoved Γ x y) :
    t.g.solidN ≤ Γ.solidN := by
  obtain ⟨-, h1, h2, h3, h4⟩ := h
  refine SolidMono.solidN_le hΓ ht (fun _ => 0) (fun v => ?_) ?_
  · by_cases hv : v = x
    · subst hv; omega
    · by_cases hvy : v = y
      · subst hvy; omega
      · have := h3 v hv hvy; omega
  · have h0 : ∑ a ∈ Finset.univ.filter (fun a => ∀ v, t.f v ≠ a), t.g.deg a = 0 :=
      Finset.sum_eq_zero fun a ha => h4 a (Finset.mem_filter.1 ha).2
    rw [h0]
    exact Nat.zero_le _

end Degrees

/-! ## Light weights of the terms of the edge expansions -/

section EdgeTerms

variable {k n : ℕ}

private theorem SolidMono.eraseIdxs_sublist {α : Type*} (is : List ℕ) (l : List α) :
    (eraseIdxs is l).Sublist l := by
  have h := (List.filter_sublist (p := fun p : α × ℕ => !is.contains p.2) (l := l.zipIdx)).map
    Prod.fst
  rwa [List.zipIdx_map_fst] at h

private theorem SolidMono.lw_count {m : ℕ} (L : List (Comp (Atom k m)))
    (h : ∀ c ∈ L, c.kind.isLt = false) : (L.filter fun c => c.kind.isLt).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc
  simp [h c hc]

private theorem SolidMono.solidC_isLt {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).kind.isLt = false := by
  unfold solidC
  split_ifs <;> rfl

private theorem SolidMono.lwN_append {m : ℕ} (L N : List (Comp (Atom k m)))
    (hN : ∀ c ∈ N, c.kind.isLt = false) (d : Coeff) :
    (⟨L ++ N, d⟩ : Graph k m).lwN = (L.filter fun c => c.kind.isLt).length := by
  unfold Graph.lwN
  simp only [List.filter_append, List.length_append, SolidMono.lw_count N hN, add_zero]

/-- A graph made of components of `Γ` moved to more atoms and of new components without light
weight has at most the light weights of `Γ`. -/
private theorem SolidMono.lw_lift {j : ℕ} {Γ : Graph k n} {K : List (Comp (Atom k n))}
    (hK : K.Sublist Γ.comps) {N : List (Comp (Atom k (n + j)))}
    (hN : ∀ c ∈ N, c.kind.isLt = false) (d : Coeff) :
    (⟨liftCs j K ++ N, d⟩ : Graph k (n + j)).lwN ≤ Γ.lwN := by
  unfold Graph.lwN
  simp only [List.filter_append, List.length_append, SolidMono.lw_count N hN, add_zero]
  have h2 : ((liftCs j K).filter fun c => c.kind.isLt).length =
      (K.filter fun c => c.kind.isLt).length := by
    unfold liftCs
    rw [List.filter_map, List.length_map]
    rfl
  rw [h2]
  exact (hK.filter _).length_le

/-- A graph made of components of `Γ` and of new components without light weight has at most the
light weights of `Γ`. -/
private theorem SolidMono.lw_sub {Γ : Graph k n} {K : List (Comp (Atom k n))}
    (hK : K.Sublist Γ.comps) {N : List (Comp (Atom k n))} (hN : ∀ c ∈ N, c.kind.isLt = false)
    (d : Coeff) : (⟨K ++ N, d⟩ : Graph k n).lwN ≤ Γ.lwN := by
  unfold Graph.lwN
  simp only [List.filter_append, List.length_append, SolidMono.lw_count N hN, add_zero]
  exact (hK.filter _).length_le

/-- A term of an edge expansion before `O_dot`: the hypotheses of the order bound of `O_dot`, and
a label, an order gain, or no new light weight. -/
private def SolidMono.LwT (Γ : Graph k n) (x : Atom k n) (T : Tracked k n) : Prop :=
  ∃ C : ℕ, PreT C Γ.ord x T ∧
    (¬ T.g.LabelFree ∨ (Γ.wt x = 0 → Γ.ord + 1 ≤ T.g.ord) ∨ T.g.lwN ≤ Γ.lwN)

private theorem SolidMono.lwN_conj {m : ℕ} (g : Graph k m) : g.conj.lwN = g.lwN := by
  simp [Graph.lwN, Graph.conj_comps, List.filter_map, Function.comp_def, Kind.conj_isLt]

private theorem SolidMono.labelFree_conj {m : ℕ} (g : Graph k m) :
    g.conj.LabelFree ↔ g.LabelFree := by
  constructor
  · intro h c hc
    have := h c.conj (by rw [Graph.conj_comps]; exact List.mem_map_of_mem hc)
    simpa using this
  · exact Graph.conj_labelFree'

private theorem SolidMono.LwT.conj {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (h : SolidMono.LwT Γ.conj x T) : SolidMono.LwT Γ x ⟨T.nOut, T.g.conj, T.f⟩ := by
  obtain ⟨C, hP, hc⟩ := h
  refine ⟨C, ?_, ?_⟩
  · have := hP.conj
    rwa [Graph.conj_ord] at this
  · rcases hc with hc | hc | hc
    · exact Or.inl fun hl => hc ((SolidMono.labelFree_conj _).1 hl)
    · refine Or.inr (Or.inl fun hw => ?_)
      have := hc (by rw [Graph.conj_wt]; exact hw)
      rw [Graph.conj_ord] at this
      change Γ.ord + 1 ≤ T.g.conj.ord
      rw [Graph.conj_ord]
      exact this
    · refine Or.inr (Or.inr ?_)
      change T.g.conj.lwN ≤ Γ.lwN
      rw [SolidMono.lwN_conj, ← SolidMono.lwN_conj Γ]
      exact hc

/-- The outputs of `O_dot` after a term with `LwT`: label-free outputs of order at most that of
the graph have at most its light weights. -/
private theorem SolidMono.LwT.out {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (hT : SolidMono.LwT Γ x T) (hwt : Γ.wt x = 0) {t : Tracked k T.nOut} (ht : t ∈ oDotT T.g)
    (hlf : t.g.LabelFree) (hord : t.g.ord ≤ Γ.ord) : t.g.lwN ≤ Γ.lwN := by
  obtain ⟨C, hP, hc⟩ := hT
  have hge := dot_ord_ge hP.dotOK hP.sl hP.unp t ht
  rcases hc with h | h | h
  · exact absurd (oDotT_lf_back hP.plain ht hlf) h
  · have := h hwt
    omega
  · rw [SolidMono.lwN_oDotT ht]
    exact h

private theorem SolidMono.bind_lw {Γ : Graph k n} {x : Atom k n} {E : TExpansion k n}
    (hE : ∀ T ∈ E, SolidMono.LwT Γ x T) (hwt : Γ.wt x = 0) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), t.g.LabelFree → t.g.ord ≤ Γ.ord → t.g.lwN ≤ Γ.lwN := by
  intro t ht hlf hord
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  exact (hE T hT).out hwt hs hlf hord

/-- The terms of case (i) of the multi-edge expansion. -/
private theorem SolidMono.lw_oOut {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ}
    {is₂ : List ℕ} {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) :
    ∀ T ∈ oOut x Γ i₁ is₂ e₁, SolidMono.LwT Γ x T := by
  intro T hT
  obtain ⟨hPre, hc⟩ := oOut_spec Ctx T hT
  refine ⟨C, hPre, ?_⟩
  rcases hc with hc | hc | ⟨j, d, ⟨hj, rfl⟩ | ⟨hj, rfl⟩⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · refine Or.inr (Or.inr ?_)
    change (⟨liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ [_, _, _], d⟩ : Graph k (n + 1)).lwN ≤ Γ.lwN
    refine SolidMono.lw_lift (SolidMono.eraseIdxs_sublist _ _) ?_ d
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rfl
  · refine Or.inr (Or.inr ?_)
    change (⟨liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ [_, _, _], d⟩ : Graph k (n + 1)).lwN ≤ Γ.lwN
    refine SolidMono.lw_lift (SolidMono.eraseIdxs_sublist _ _) ?_ d
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rfl

/-- The terms of case (iii) of the multi-edge expansion. -/
private theorem SolidMono.lw_iOut {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ}
    {is₂ : List ℕ} {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) :
    ∀ T ∈ iOut x Γ i₁ is₂ e₁, SolidMono.LwT Γ x T := by
  intro T hT
  obtain ⟨hPre, hc⟩ := iOut_spec Ctx T hT
  refine ⟨C, hPre, ?_⟩
  rcases hc with hc | hc | ⟨j, d, hj, rfl⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · refine Or.inr (Or.inr ?_)
    change (⟨liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ [_, _, _], d⟩ : Graph k (n + 1)).lwN ≤ Γ.lwN
    refine SolidMono.lw_lift (SolidMono.eraseIdxs_sublist _ _) ?_ d
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> rfl

/-- The multi-edge expansion at `x` is `O_dot` applied to terms with `LwT`. -/
private theorem SolidMono.me_rep {C : ℕ} {x : Atom k n} {Γ : Graph k n} (H : MEHyp C x Γ)
    (hdeg : 1 ≤ Γ.deg x) :
    ∃ E : TExpansion k n, oMultiET x Γ = E.bind (fun _ g => oDotT g) ∧
      ∀ T ∈ E, SolidMono.LwT Γ x T := by
  have hsum := deg_eq_sum H.normal x
  have hXout : ∀ Γ' : Graph k n, Γ'.Normal C → Γ'.xdotsAt x (oXIdx x Γ') = true := by
    intro Γ' hN'
    refine xdotsAt_of_normal hN' x _ fun j hj => ?_
    obtain ⟨c, hc, ch, hk, hxy⟩ := mem_oXIdx.1 hj
    exact ⟨c, hc, by simp [hk, Kind.isSolid], by rcases hxy with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]⟩
  have hXin : ∀ Γ' : Graph k n, Γ'.Normal C → Γ'.xdotsAt x (iXIdx x Γ') = true := by
    intro Γ' hN'
    refine xdotsAt_of_normal hN' x _ fun j hj => ?_
    obtain ⟨c, hc, ch, hk, hxy, -⟩ := mem_iXIdx.1 hj
    exact ⟨c, hc, by simp [hk, Kind.isSolid], Or.inr hxy⟩
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB H.lf H.plain]
  have hbind : ∀ E : TExpansion k n, multiEHat x Γ = some E → (∀ T ∈ E, SolidMono.LwT Γ x T) →
      ∃ E : TExpansion k n, oMultiET x Γ = E.bind (fun _ g => oDotT g) ∧
        ∀ T ∈ E, SolidMono.LwT Γ x T := by
    intro E hE hT
    refine ⟨E, ?_, hT⟩
    unfold oMultiET
    rw [ite_eq_right (by simp [hpl]), hE]
  by_cases h1 : Γ.edgeIdx x .plus true = []
  · by_cases h2 : Γ.edgeIdx x .minus true = []
    · by_cases h3 : Γ.edgeIdx x .plus false = []
      · have h4 : Γ.edgeIdx x .minus false ≠ [] := by
          intro h4
          rw [h1, h2, h3, h4] at hsum
          simp at hsum
          omega
        obtain ⟨i₁, is₂, hIP⟩ := List.exists_cons_of_ne_nil h4
        obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .minus) (out := false)
          (by rw [hIP]; exact List.mem_cons_self ..)
        have Ctx₀ := InCtxS.conj_of (C := C) H.normal H.plain H.right H.lf hIP hL h1 h2
        have Ctx : InCtx C x Γ.conj i₁ is₂ e₁.conj := ⟨Ctx₀.normal, Ctx₀.plain, Ctx₀.right,
          Ctx₀.unl, Ctx₀.hIP, Ctx₀.hL, Ctx₀.hOP0, Ctx₀.hOM0⟩
        have hX' : Γ.conj.xdotsAt x (iXIdx x Γ.conj) = true := hXin _ (Graph.conj_Normal H.normal)
        have hIP' : Γ.conj.edgeIdx x .plus false = i₁ :: is₂ := by rw [edgeIdx_conj]; exact hIP
        have hL' : Γ.conj.comps[i₁]? = some e₁.conj := by simp [Graph.conj_comps, hL]
        refine hbind ((iOut x Γ.conj i₁ is₂ e₁.conj).map (fun t => ⟨t.nOut, t.g.conj, t.f⟩)) ?_ ?_
        · simp [multiEHat, h1, h2, h3, h4, multiEIn_eq hIP' hL' hX', TExpansion.conj]
        · intro T hT
          obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
          exact (SolidMono.lw_iOut Ctx T₀ hT₀).conj
      · obtain ⟨i₁, is₂, hIP⟩ := List.exists_cons_of_ne_nil h3
        obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .plus) (out := false)
          (by rw [hIP]; exact List.mem_cons_self ..)
        have Ctx : InCtx C x Γ i₁ is₂ e₁ := ⟨H.normal, H.plain, H.right, H.lf, hIP, hL, h1, h2⟩
        refine hbind (iOut x Γ i₁ is₂ e₁) ?_ (SolidMono.lw_iOut Ctx)
        simp [multiEHat, h1, h2, h3, multiEIn_eq hIP hL (hXin Γ H.normal)]
    · obtain ⟨i₁, is₂, hOP⟩ := List.exists_cons_of_ne_nil h2
      obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .minus) (out := true)
        (by rw [hOP]; exact List.mem_cons_self ..)
      have Ctx₀ := OutCtxS.conj_of (C := C) H.normal H.plain H.right H.lf hOP hL
      have Ctx : OutCtx C x Γ.conj i₁ is₂ e₁.conj :=
        ⟨Ctx₀.normal, Ctx₀.plain, Ctx₀.right, Ctx₀.unl, Ctx₀.hOP, Ctx₀.hL⟩
      have hX' : Γ.conj.xdotsAt x (oXIdx x Γ.conj) = true := hXout _ (Graph.conj_Normal H.normal)
      have hOP' : Γ.conj.edgeIdx x .plus true = i₁ :: is₂ := by rw [edgeIdx_conj]; exact hOP
      have hL' : Γ.conj.comps[i₁]? = some e₁.conj := by simp [Graph.conj_comps, hL]
      refine hbind ((oOut x Γ.conj i₁ is₂ e₁.conj).map (fun t => ⟨t.nOut, t.g.conj, t.f⟩)) ?_ ?_
      · simp [multiEHat, h1, h2, multiEOut_eq hOP' hL' hX', TExpansion.conj]
      · intro T hT
        obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
        exact (SolidMono.lw_oOut Ctx T₀ hT₀).conj
  · obtain ⟨i₁, is₂, hOP⟩ := List.exists_cons_of_ne_nil h1
    obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .plus) (out := true)
      (by rw [hOP]; exact List.mem_cons_self ..)
    have Ctx : OutCtx C x Γ i₁ is₂ e₁ := ⟨H.normal, H.plain, H.right, H.lf, hOP, hL⟩
    refine hbind (oOut x Γ i₁ is₂ e₁) ?_ (SolidMono.lw_oOut Ctx)
    simp [multiEHat, h1, multiEOut_eq hOP hL (hXout Γ H.normal)]

/-- The terms of the `GG` expansion. -/
private theorem SolidMono.lw_ggOut {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e') :
    ∀ T ∈ ggOut x Γ i j e e', SolidMono.LwT Γ x T := by
  intro T hT
  obtain ⟨hPre, hc⟩ := ggOut_spec Ctx T hT
  refine ⟨C, hPre, ?_⟩
  rcases hc with hc | hc | ⟨-, d, rfl⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · refine Or.inr (Or.inr ?_)
    change (⟨eraseIdxs [i, j] Γ.comps ++ [_] ++ [_], d⟩ : Graph k n).lwN ≤ Γ.lwN
    rw [List.append_assoc]
    refine SolidMono.lw_sub (SolidMono.eraseIdxs_sublist _ _) ?_ d
    intro c hc
    rcases List.mem_append.1 hc with hc | hc <;> rw [List.mem_singleton] at hc <;> subst hc
    · exact SolidMono.solidC_isLt _ _ _
    · rfl

/-- The `GG` expansion at `x` is `O_dot` applied to terms with `LwT`. -/
private theorem SolidMono.gg_rep {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain) (hL : Γ.LabelFree) (hx : x.isRight = true) {y y' : Atom k n}
    (hin : Γ.GGInputAt x y y') :
    ∃ E : TExpansion k n, oGGT x Γ = E.bind (fun _ g => oDotT g) ∧
      ∀ T ∈ E, SolidMono.LwT Γ x T := by
  obtain ⟨ch, i, j, e, e', hO, hI, hO', hI', hi, hj⟩ := gg_input hN hin
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB hL hP]
  have hdeg := hin.1
  cases ch
  · simp only [Charge.flip] at hO' hI'
    have Ctx : GGCtxS C x Γ i j e e' := ⟨hN, hP, hx, hL, hO, hI, hO', hI', hi, hj⟩
    have Ctx' : GGCtx C x Γ i j e e' := ⟨hN, hP, hx, hL, hO, hI, hO', hI', hi, hj⟩
    have hX' : Γ.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal hN x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e, hi, by simp [Ctx.espec.1, Kind.isSolid], Or.inl Ctx.espec.2.1⟩
      · exact ⟨e', hj, by simp [Ctx.e'spec.1, Kind.isSolid], Or.inr Ctx.e'spec.2.1⟩
    have hE : oGGT x Γ = (ggOut x Γ i j e e').bind (fun _ g => oDotT g) := by
      unfold oGGT
      rw [ite_eq_right (by simp [hpl]), ggPos_eq hdeg hO hI hi hj hX']
    exact ⟨_, hE, SolidMono.lw_ggOut Ctx'⟩
  · simp only [Charge.flip] at hO' hI'
    have hi' : Γ.conj.comps[i]? = some e.conj := by simp [Graph.conj_comps, hi]
    have hj' : Γ.conj.comps[j]? = some e'.conj := by simp [Graph.conj_comps, hj]
    have hO2 : Γ.conj.edgeIdx x .plus true = [i] := by rw [edgeIdx_conj]; exact hO
    have hI2 : Γ.conj.edgeIdx x .plus false = [j] := by rw [edgeIdx_conj]; exact hI
    have hM1 : Γ.conj.edgeIdx x .minus true = [] := by rw [edgeIdx_conj]; exact hO'
    have hM2 : Γ.conj.edgeIdx x .minus false = [] := by rw [edgeIdx_conj]; exact hI'
    have Ctx : GGCtxS C x Γ.conj i j e.conj e'.conj :=
      ⟨Graph.conj_Normal hN, Graph.conj_Plain hP, hx, Graph.conj_labelFree' hL, hO2, hI2, hM1, hM2,
        hi', hj'⟩
    have Ctx' : GGCtx C x Γ.conj i j e.conj e'.conj :=
      ⟨Graph.conj_Normal hN, Graph.conj_Plain hP, hx, Graph.conj_labelFree' hL, hO2, hI2, hM1, hM2,
        hi', hj'⟩
    have hX' : Γ.conj.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal (Graph.conj_Normal hN) x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e.conj, hi', by rw [Ctx.espec.1]; rfl, Or.inl Ctx.espec.2.1⟩
      · exact ⟨e'.conj, hj', by rw [Ctx.e'spec.1]; rfl, Or.inr Ctx.e'spec.2.1⟩
    have hdeg' : Γ.conj.deg x = 2 := by rw [Graph.conj_deg']; exact hdeg
    have hnone : ggPos x Γ = none := by
      unfold ggPos
      rw [ite_eq_right (by simp [hdeg])]
      have : Γ.edgeIdx x .plus true = [] := hO'
      rw [this]
    have hE : oGGT x Γ = (ggOut x Γ.conj i j e.conj e'.conj).conj.bind (fun _ g => oDotT g) := by
      unfold oGGT
      rw [ite_eq_right (by simp [hpl]), hnone]
      simp only
      rw [ggPos_eq hdeg' hO2 hI2 hi' hj' hX']
    refine ⟨_, hE, fun T hT => ?_⟩
    obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
    exact (SolidMono.lw_ggOut Ctx' T₀ hT₀).conj

end EdgeTerms

/-! ## Terms of the light weight expansion -/

section WeightTerms

variable {k n : ℕ}

/-- A term of `O^{(x),2}_weight` before `O_dot`: a label, one light weight fewer than `Γ`, or new
components without solid edge whose order exceeds that of the removed ones by at least `1`. -/
private def SolidMono.LwW (Γ : Graph k n) (T : Tracked k n) : Prop :=
  ¬ T.g.LabelFree ∨ T.g.lwN + 1 ≤ Γ.lwN ∨
    ∃ (j : ℕ) (R : List (Comp (Atom k n))) (N : List (Comp (Atom k (n + j))))
      (g : Graph k (n + j)), T = ⟨n + j, g, liftA j⟩ ∧ Sch Γ j R N none g ∧
      (∀ c ∈ N, c.kind.isSolid = false ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot) ∧
      ordL R + 2 * (j : ℤ) + 1 ≤ ordL N

private theorem SolidMono.ordL_conj {m : ℕ} (L : List (Comp (Atom k m))) :
    ordL (L.map Comp.conj) = ordL L := by
  unfold ordL
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp [Kind.conj_ord]

private theorem SolidMono.LwW.conj {Γ : Graph k n} {T : Tracked k n}
    (h : SolidMono.LwW Γ.conj T) : SolidMono.LwW Γ ⟨T.nOut, T.g.conj, T.f⟩ := by
  rcases h with h | h | ⟨j, R, N, g, rfl, hS, hN, ho⟩
  · exact Or.inl fun hl => h ((SolidMono.labelFree_conj _).1 hl)
  · refine Or.inr (Or.inl ?_)
    change T.g.conj.lwN + 1 ≤ Γ.lwN
    rw [SolidMono.lwN_conj, ← SolidMono.lwN_conj Γ]
    exact h
  · refine Or.inr (Or.inr ⟨j, R.map Comp.conj, N.map Comp.conj, g.conj, rfl, hS.conj, ?_, ?_⟩)
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      obtain ⟨h1, h2, h3⟩ := hN d hd
      refine ⟨by rw [Comp.conj_kind, Kind.conj_isSolid]; exact h1, ?_, ?_⟩
      · rw [Comp.conj_kind]
        intro h
        exact h2 ((Kind.conj_eq_dot _).1 h)
      · rw [Comp.conj_kind]
        intro h
        exact h3 ((Kind.conj_eq_xdot _).1 h)
    · rw [SolidMono.ordL_conj, SolidMono.ordL_conj]
      exact ho

/-- After a term whose new components have no solid edge and an order surplus of at least `1`,
every output of `O_dot` has order at least that of the graph plus `1`. -/
private theorem SolidMono.noSolid_obl {C : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) {j : ℕ}
    {R : List (Comp (Atom k n))} {N : List (Comp (Atom k (n + j)))} {g : Graph k (n + j)}
    (hS : Sch Γ j R N none g)
    (hNs : ∀ c ∈ N, c.kind.isSolid = false ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)
    (ho : ordL R + 2 * (j : ℤ) + 1 ≤ ordL N) (hd : DotIn g) {t : Tracked k (n + j)}
    (ht : t ∈ oDotT g) : Γ.obl + 1 ≤ t.g.obl := by
  have hz : ∀ q : Comp (Atom k (n + j)) → Bool, (∀ c ∈ N, q c = true → c.kind.isSolid = true) →
      (N.filter q).length = 0 := by
    intro q hq
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc hqc
    have := hq c hc hqc
    rw [(hNs c hc).1] at this
    cases this
  have hn : DotNew g 0 (isNewA n) := by
    refine hS.dotNew hN (fun c hc => ⟨(hNs c hc).2.1, (hNs c hc).2.2⟩) (fun i => ?_) ?_ ?_ ?_
    · rw [hz _ fun c _ h => by simp only [Bool.and_eq_true] at h; exact h.1]; omega
    · rw [hz _ fun c _ h => by simp only [Bool.and_eq_true] at h; exact h.1.1.1]
    · rw [hz _ fun c _ h => h]; omega
    · intro _; rw [hz _ fun c _ h => h]; omega
  obtain ⟨-, h2⟩ := dot_obl hd hn ht
  have hexc : g.dotExcess = Γ.dotExcess := hS.dotExcess fun c hc => (hNs c hc).2.1
  have hord := hS.ord
  simp only [Graph.obl, hexc] at h2 ⊢
  push_cast at h2
  linarith

/-- A derivative term has at most the light weights of the list it is taken of. -/
private theorem SolidMono.lw_dTerms {V : Type*} [DecidableEq V] {p q : V} {cs d : List (Comp V)}
    (hd : d ∈ dTerms p q cs) :
    (d.filter fun c => c.kind.isLt).length ≤ (cs.filter fun c => c.kind.isLt).length := by
  obtain ⟨j, hj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hps0 : (ps.filter fun c => c.kind.isLt).length = 0 := by
    unfold Comp.dPieces at hps
    split at hps <;> split at hps <;> (try cases hps) <;>
      simp [SolidMono.solidC_isLt]
  rw [List.filter_append, List.length_append, hps0, add_zero]
  exact ((List.eraseIdx_sublist cs j).filter _).length_le

/-- The light weights of `Γ` other than the one at the index `i`. -/
private theorem SolidMono.lw_erase {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    {ℓ : Comp (Atom k n)} (H : WCtx C x Γ i ℓ) (j : ℕ) :
    ((liftCs j (Γ.comps.eraseIdx i)).filter fun c => c.kind.isLt).length + 1 = Γ.lwN := by
  have h1 := (H.perm1.filter fun c => c.kind.isLt).length_eq
  rw [List.filter_append, List.length_append] at h1
  have h2 : ([ℓ].filter fun c => c.kind.isLt).length = 1 := by simp [H.hk, Kind.isLt]
  have h3 : ((liftCs j (Γ.comps.eraseIdx i)).filter fun c => c.kind.isLt).length =
      ((Γ.comps.eraseIdx i).filter fun c => c.kind.isLt).length := by
    unfold liftCs
    rw [List.filter_map, List.length_map]
    rfl
  unfold Graph.lwN
  omega

private theorem SolidMono.not_lf {m : ℕ} {g : Graph k m} {c : Comp (Atom k m)} (hc : c ∈ g.comps)
    (hl : c.label ≠ none) : ¬ g.LabelFree := fun h => hl (h c hc)

private theorem SolidMono.not_lf_lab {m : ℕ} {g : Graph k m} {u : Atom k m}
    {L M : List (Comp (Atom k m))} (hg : g.comps = labelQs u L ++ M) {c : Comp (Atom k m)}
    (hc : c ∈ L) (hr : c.kind.isRandom = true) : ¬ g.LabelFree := by
  intro h
  have := h (c.labelQ u) (by rw [hg]; exact List.mem_append_left _ (List.mem_map_of_mem hc))
  simp [Comp.labelQ, hr] at this

/-- The terms of [I, (3.5)] for the light weight of charge `plus` on `x` at the index `i`. -/
private theorem SolidMono.lw_w2Out {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    {ℓ : Comp (Atom k n)} (H : WCtx C x Γ i ℓ) : ∀ T ∈ w2Out x Γ i, SolidMono.LwW Γ T := by
  intro T hT
  have hℓ : ℓ.kind.isRandom = true := by rw [H.hk]; rfl
  unfold w2Out at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (((((rfl | rfl) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩) | (rfl | rfl | rfl | rfl)) |
    ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
  · refine Or.inr (Or.inr ⟨1, [], [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)], _, rfl, ⟨by simp, Γ.comps, by simp, ?_⟩, ?_, ?_⟩)
    · exact List.Perm.of_eq (by simp [labF])
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact ⟨rfl, by simp [mkC], by simp [mkC]⟩
    · simp [ordL, mkC, Kind.ord]
  · refine Or.inr (Or.inr ⟨2, [ℓ], [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.light .plus) (newA 1) (newA 1)], _, rfl,
      ⟨by simpa using hℓ, Γ.comps.eraseIdx i, H.perm1, ?_⟩, ?_, ?_⟩)
    · exact List.Perm.of_eq (by simp [labF])
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simp [mkC], by simp [mkC]⟩
    · simp [ordL, mkC, Kind.ord, H.hk]
  · refine Or.inr (Or.inl ?_)
    change (⟨d ++ [_, _], _⟩ : Graph k (n + 1)).lwN + 1 ≤ Γ.lwN
    rw [SolidMono.lwN_append _ _ (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl)]
    have h1 := SolidMono.lw_dTerms hd
    have h2 := SolidMono.lw_erase H 1
    omega
  · refine Or.inr (Or.inl ?_)
    change (⟨d ++ [_, _, _], _⟩ : Graph k (n + 2)).lwN + 1 ≤ Γ.lwN
    rw [SolidMono.lwN_append _ _ (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> rfl)]
    have h1 := SolidMono.lw_dTerms hd
    have h2 := SolidMono.lw_erase H 2
    omega
  · exact Or.inl (SolidMono.not_lf (List.mem_map_of_mem (f := Comp.labelQ x) H.mem)
      (by simp [Comp.labelQ, hℓ]))
  · exact Or.inl (SolidMono.not_lf_lab rfl (List.mem_append_right _ (List.mem_singleton_self _))
      (by simp [mkC, Kind.isRandom]))
  · exact Or.inl (SolidMono.not_lf_lab rfl (List.mem_append_right _ (List.mem_cons_self ..))
      (by simp [mkC, Kind.isRandom]))
  · exact Or.inl (SolidMono.not_lf_lab rfl (List.mem_append_right _ (List.mem_cons_self ..))
      (by simp [mkC, Kind.isRandom]))
  · exact Or.inl (SolidMono.not_lf_lab rfl (List.mem_append_right _ (List.mem_singleton_self _))
      (by simp [mkC, Kind.isRandom]))
  · exact Or.inl (SolidMono.not_lf_lab rfl (List.mem_append_right _ (List.mem_singleton_self _))
      (by simp [mkC, Kind.isRandom]))

/-- The terms of `O^{(x),2}_weight` at a graph with a light weight on `x`. -/
private theorem SolidMono.lw_w2 {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain) (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hx : x.isRight = true)
    (hl : HasLight Γ x) : ∀ T ∈ oWeight2T x Γ, SolidMono.LwW Γ T := by
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB hL hP]
  unfold oWeight2T
  rw [ite_eq_right (by simp [hpl])]
  cases h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
  | some i =>
    rw [oWeight2Pos_eq h]
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact SolidMono.lw_w2Out (C := C) ⟨hN, hP, hL, hK, hx, by simp [hi], hp.1, hp.2⟩
  | none =>
    rw [oWeight2Pos_none h]
    simp only
    cases h' : Γ.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
    | some i =>
      rw [oWeight2Pos_eq h']
      obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h'
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have H : WCtx C x Γ.conj i Γ.conj.comps[i] :=
        ⟨Graph.conj_Normal hN, Graph.conj_Plain hP, Graph.conj_labelFree' hL,
          Graph.conj_randomFirstInt hK, hx, by simp [hi], hp.1, hp.2⟩
      intro T hT
      obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
      exact (SolidMono.lw_w2Out H T₀ hT₀).conj
    | none =>
      exfalso
      obtain ⟨c, hc, hk, hcx⟩ := hl
      rw [List.findIdx?_eq_none_iff] at h h'
      rcases hk with hk | hk
      · have := h c hc
        simp [hk, hcx] at this
      · have := h' c.conj (List.mem_map_of_mem hc)
        simp [hk, hcx, Kind.conj, Charge.flip] at this

/-- `O^{(y),1}_weight` changes neither the solid edges nor the light weights, up to the light
weights `N` it creates. -/
private theorem SolidMono.o1_counts {y : Atom k n} {h h' : Graph k n}
    {R : List (Comp (Atom k n))} {N : List (Comp (Atom k (n + 0)))} (hS : Sch h 0 R N none h')
    (hNR : ∀ c ∈ N, ∃ c₀ ∈ R, c = c₀.toLight) (hR : ∀ c ∈ R, IsRegU y c) :
    h'.lwN = h.lwN + N.length ∧ h'.solidN = h.solidN := by
  have hRw : ∀ c ∈ R, ∃ ch, c.kind = .weight ch := fun c hc => (hR c hc).1
  have hNl : ∀ c ∈ N, ∃ ch, c.kind = .light ch := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := hNR c hc
    obtain ⟨ch, hk⟩ := hRw c₀ hc₀
    exact ⟨ch, by simp [Comp.toLight, hk]⟩
  refine ⟨?_, ?_⟩
  · have := hS.lwN
    have h1 : (R.filter fun c => c.kind.isLt).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨ch, hk⟩ := hRw c hc
      simp [hk, Kind.isLt]
    have h2 : (N.filter fun c => c.kind.isLt).length = N.length := by
      rw [List.filter_eq_self.2]
      intro c hc
      obtain ⟨ch, hk⟩ := hNl c hc
      simp [hk, Kind.isLt]
    omega
  · have := hS.count (fun c => c.kind.isSolid) (fun c => by rw [labF_kind])
    simp only [Comp.map] at this
    have h1 : (R.filter fun c => c.kind.isSolid).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨ch, hk⟩ := hRw c hc
      simp [hk, Kind.isSolid]
    have h2 : (N.filter fun c => c.kind.isSolid).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨ch, hk⟩ := hNl c hc
      simp [hk, Kind.isSolid]
    rw [h1, h2] at this
    exact Nat.add_right_cancel this

/-- A label-free output of `O^{(y),1}_weight` comes from a label-free graph. -/
private theorem SolidMono.o1_lf {y : Atom k n} {h h' : Graph k n}
    {R : List (Comp (Atom k n))} {N : List (Comp (Atom k (n + 0)))} (hS : Sch h 0 R N none h')
    (hR : ∀ c ∈ R, IsRegU y c) (hL : h'.LabelFree) : h.LabelFree := by
  intro c hc
  by_cases hcR : c ∈ R
  · exact (hR c hcR).2.2
  · have := hL _ (hS.mem_of_notR hc hcR)
    simpa [labF_none, Comp.map_liftA_zero] using this

private theorem SolidMono.mem_self {g : Graph k n} (h : oDotT g = [Tracked.self g])
    {t : Tracked k n} (ht : t ∈ oDotT g) : t = Tracked.self g := by
  rw [h] at ht
  exact List.mem_singleton.1 ht

/-- `O_dot` is the identity on a normal regular label-free graph without dotted edges. -/
private theorem SolidMono.oDotT_self {C : ℕ} {g : Graph k n} (hN : g.Normal C)
    (hL : g.LabelFree) (hD : ∀ c ∈ g.comps, c.kind ≠ .dot) : oDotT g = [Tracked.self g] := by
  have hlab : g.labels = [] := by
    unfold Graph.labels
    rw [List.filterMap_eq_nil_iff.2 fun c hc => hL c hc]
    rfl
  have hSP : g.splitPairs = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro p hp
    obtain ⟨-, hne, -⟩ := mem_splitPairs.1 hp
    have e := hN.2.2 p.1 p.2.1 (sp_ne hp)
    have hsj : spJoined g Kind.isSolid p.1 p.2.1 = spJoined g (· == .xdot) p.1 p.2.1 := by
      apply Bool.eq_iff_iff.2
      rw [spJoined_iff, spJoined_iff]
      constructor
      · rintro ⟨c, hc, hk, hxy⟩
        obtain ⟨c', hc', hk', hxy'⟩ := e.2 ⟨c, hc, hk, hxy⟩
        exact ⟨c', hc', by simp [hk'], hxy'⟩
      · rintro ⟨c, hc, hk, hxy⟩
        exact e.1 ⟨c, hc, by simpa using hk, hxy⟩
    rw [hsj] at hne
    simp at hne
  have hany : (g.comps.any fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) ||
      (c.kind.isSolid && c.x == c.y)) = false := by
    rw [List.any_eq_false]
    intro c hc
    have h1 : (c.kind == .dot) = false := by simpa using hD c hc
    have h2 : (c.kind.isSolid && c.x == c.y) = false := by
      cases hs : c.kind.isSolid
      · rfl
      · simpa using hN.2.1 c hc hs
    simp [h1, h2]
  apply oDotT_branch2
  · rintro (h | h)
    · rw [hlab] at h
      simp at h
    · rw [List.any_eq_true] at h
      obtain ⟨c, hc, hb⟩ := h
      simp [hL c hc] at hb
  · rw [hSP, hany]
    rfl

/-- The output of `O_dot` at a normal regular label-free graph without dotted edges is the graph. -/
private theorem SolidMono.self_facts {C : ℕ} {g : Graph k n} (hN : g.Normal C) (hP : g.Plain)
    (hK : g.RandomFirstInt) (hL : g.LabelFree) (hD : ∀ c ∈ g.comps, c.kind ≠ .dot)
    {t : Tracked k n} (ht : t ∈ oDotT g) :
    t.g.Plain ∧ t.g.RandomFirstInt ∧ t.g.obl = g.obl ∧ t.g.dotExcess = g.dotExcess ∧
      t.g.lwN = g.lwN ∧ t.g.solidN = g.solidN := by
  obtain rfl := SolidMono.mem_self (SolidMono.oDotT_self hN hL hD) ht
  exact ⟨hP, hK, rfl, rfl, rfl, rfl⟩

end WeightTerms

/-! ## Light weights and solid edges at equal order -/

section Main

variable {k n : ℕ}

/-- **The weight expansion of [I, Lemma 3.9] at equal order: light weights and solid edges.** At
an internal atom `x` of a graph without dotted edges, under the hypotheses of `oWeightT_step`,
every label-free output of the same order in the count of [II, (2.5)] has dot excess `0`, and has
fewer light weights, or as many light weights and as many solid edges. -/
theorem oWeightT_lwSolid {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain) (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart)
    (hx : x.isRight = true) (hw : 0 < Γ.wt x) (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∀ t ∈ oWeightT x Γ, t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.dotExcess = 0 ∧ (t.g.lwN < Γ.lwN ∨ (t.g.lwN = Γ.lwN ∧ t.g.solidN = Γ.solidN)) := by
  have hΓ0 : Γ.dotExcess = 0 := SolidMono.dotExcess_zero hD
  intro t ht htL heq
  rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl] at heq
  unfold oWeightT at ht
  split_ifs at ht with hany
  swap
  · exfalso
    apply hany
    unfold Graph.wt at hw
    obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos hw
    rw [List.mem_filter] at hc
    exact List.any_eq_true.2 ⟨c, hc.1, hc.2⟩
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨u₃, ⟨u₂, ⟨t₁, ht₁, t₂, ht₂, rfl⟩, t₃, ht₃, rfl⟩, t₄, ht₄, rfl⟩ := ht
  obtain ⟨R, N, g₁, rfl, hSch, hNl, hNR, hR, hall⟩ := oWeight1T_spec ht₁
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := o1_facts hP hK hSch hNl hNR hR
  have hN₁ := f11 C hN
  obtain ⟨hlw₁, hsol₁⟩ := SolidMono.o1_counts hSch hNR hR
  have hg₁D : ∀ c ∈ g₁.comps, c.kind ≠ .dot := by
    intro c hc
    rcases hSch.mem_cases hc with ⟨c₀, hc₀, he⟩ | ⟨c₁, hc₁, he⟩ <;> rw [he, labF_kind]
    · exact hD c₀ hc₀
    · obtain ⟨c₀, hc₀, he'⟩ := hNR c₁ hc₁
      obtain ⟨⟨ch, hk⟩, -⟩ := hR c₀ hc₀
      rw [he']
      simp [Comp.toLight, hk]
  simp only [Function.comp_id] at ht₂ ht₃ ht₄ htL heq ⊢
  obtain ⟨R₄, N₄, h₄, rfl, hSch₄, hNl₄, hNR₄, hR₄, -⟩ := oWeight1T_spec ht₄
  obtain ⟨hlw₄, hsol₄⟩ := SolidMono.o1_counts hSch₄ hNR₄ hR₄
  have hlf₃ : t₃.g.LabelFree := SolidMono.o1_lf hSch₄ hR₄ htL
  change h₄.obl = Γ.obl at heq
  change h₄.dotExcess = 0 ∧ (h₄.lwN < Γ.lwN ∨ (h₄.lwN = Γ.lwN ∧ h₄.solidN = Γ.solidN))
  by_cases hl : HasLight g₁ x
  · have hT := oWeight2T_terms hN₁ f6 (f9 hL) f7 hx hl t₂ ht₂
    have hW := SolidMono.lw_w2 hN₁ f6 (f9 hL) f7 hx hl t₂ ht₂
    obtain ⟨e1, e2, -, -, e5, e6, -⟩ := hT.step hN₁ f6 (f9 hL) f7 (f8 hX) ht₃
    obtain ⟨k1, k2, -⟩ := o1_facts (h := t₃.g) e6 e5 hSch₄ hNl₄ hNR₄ hR₄
    change g₁.obl ≤ t₃.g.obl at e2
    have hexc₃ : t₃.g.dotExcess = 0 :=
      SolidMono.termOK_exc hT hN₁ f6 (f9 hL) (f8 hX) hg₁D ht₃ (by omega)
    refine ⟨by rw [k1, hexc₃], Or.inl ?_⟩
    obtain ⟨-, -, hd₂, -, -, -⟩ := SolidMono.termOK_data hT hN₁ f6 (f9 hL) (f8 hX) hg₁D
    have hlf₂ : t₂.g.LabelFree := SolidMono.lf_back hd₂.plain ht₃ hlf₃
    have hlw₃ := SolidMono.lwN_oDotT ht₃
    rcases hW with hW | hW | ⟨j, R', N', g', rfl, hS', hNs', ho'⟩
    · exact absurd hlf₂ hW
    · omega
    · exfalso
      have := SolidMono.noSolid_obl hN₁ hS' hNs' ho' hd₂ ht₃
      omega
  · change t₂ ∈ oWeight2T x g₁ at ht₂
    rw [oWeight2T_self hl, List.mem_singleton] at ht₂
    subst ht₂
    have hN0 : N = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro c hc
      obtain ⟨c₀, hc₀, rfl⟩ := hNR c hc
      obtain ⟨⟨ch, hk⟩, hcx, -⟩ := hR c₀ hc₀
      apply hl
      refine ⟨labF none c₀.toLight, hSch.mem_N hc, ?_, ?_⟩
      · cases ch <;> simp [labF, Comp.toLight, hk]
      · simp [labF, Comp.toLight, hk, hcx]
    subst hN0
    change t₃ ∈ oDotT g₁ at ht₃
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := SolidMono.self_facts hN₁ f6 f7 (f9 hL) hg₁D ht₃
    obtain ⟨k1, k2, -⟩ := o1_facts (h := t₃.g) p1 p2 hSch₄ hNl₄ hNR₄ hR₄
    simp only [List.length_nil, CharP.cast_eq_zero, add_zero] at f2 hlw₁
    refine ⟨by rw [k1, p4, f1, hΓ0], Or.inr ⟨by omega, by rw [hsol₄, p6, hsol₁]⟩⟩

/-- **The multi-edge expansion of [I, Lemma 3.13] at equal order: light weights and solid
edges.** At an internal atom `x` of a graph without dotted edges, under the hypotheses of
`oMultiET_step`, every label-free output of the same order in the count of [II, (2.5)] has dot
excess `0` and at most the light weights and the solid edges of the input. -/
theorem oMultiET_lwSolid {C : ℕ} {x : Atom k n} {Γ : Graph k n} (H : MEHyp C x Γ)
    (hX : Γ.XdotApart) (hdeg : 1 ≤ Γ.deg x) (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∀ t ∈ oMultiET x Γ, t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.dotExcess = 0 ∧ t.g.lwN ≤ Γ.lwN ∧ t.g.solidN ≤ Γ.solidN := by
  intro t ht hlf heq
  have hΓ0 := SolidMono.dotExcess_zero hD
  obtain ⟨E, hE, hT, -⟩ := oMultiET_rep H hdeg
  have hb := SolidMono.bind_exc hT H.normal H.plain H.lf hX hD t (by rw [← hE]; exact ht)
  rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl] at heq
  have h0 := hb.1 heq.le
  have hord : t.g.ord = Γ.ord := by
    simp only [Graph.obl, h0, hΓ0] at heq
    linarith
  refine ⟨h0, ?_, ?_⟩
  · obtain ⟨E', hE', hT'⟩ := SolidMono.me_rep H hdeg
    exact SolidMono.bind_lw hT' H.wt0 t (by rw [← hE']; exact ht) hlf hord.le
  · rcases multiE_core H.normal H.plain H.right H.lf H.wt0 hdeg t ht hlf with h | ⟨-, -, hx, h⟩
    · omega
    · exact SolidMono.solidN_le_me H.normal.2.1 hb.2 hx h

/-- **The `GḠ` expansion of [I, Lemma 3.19] at equal order: light weights and solid edges.** At
an internal atom `x` of a graph without dotted edges, under the hypotheses of `oGGbarT_step`,
every label-free output of the same order in the count of [II, (2.5)] has dot excess `0` and at
most the light weights and the solid edges of the input. -/
theorem oGGbarT_lwSolid {C : ℕ} {x : Atom k n} {Γ : Graph k n} (H : MEHyp C x Γ)
    (hX : Γ.XdotApart) {y y' : Atom k n} (hin : Γ.GGbarInputAt x y y')
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∀ t ∈ oGGbarT x Γ, t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.dotExcess = 0 ∧ t.g.lwN ≤ Γ.lwN ∧ t.g.solidN ≤ Γ.solidN := by
  have hdeg := hin.1
  have hE : oGGbarT x Γ = oMultiET x Γ := by
    rcases ggbar_input H.normal hin with ⟨i₁, j, e₁, ej, hpt, hmt, hpf, hmf, -, -⟩ |
        ⟨i₁, j, e₁, ej, hpt, hmt, hpf, hmf, -, -⟩ <;>
      simp [oGGbarT, hdeg, hpt, hmt, hpf, hmf]
  rw [hE]
  exact oMultiET_lwSolid H hX (by omega) hD

/-- **The `GG` expansion of [I, Lemma 3.16] at equal order: light weights and solid edges.** At
an internal atom `x` of a graph without dotted edges, under the hypotheses of `oGGT_step`, every
label-free output of the same order in the count of [II, (2.5)] has dot excess `0` and at most the
light weights and the solid edges of the input. -/
theorem oGGT_lwSolid {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) (hx : x.isRight = true)
    (hwt : Γ.wt x = 0) {y y' : Atom k n} (hin : Γ.GGInputAt x y y')
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∀ t ∈ oGGT x Γ, t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.dotExcess = 0 ∧ t.g.lwN ≤ Γ.lwN ∧ t.g.solidN ≤ Γ.solidN := by
  intro t ht hlf heq
  have hΓ0 := SolidMono.dotExcess_zero hD
  obtain ⟨E, hE, hT, -⟩ := oGGT_rep hN hP hL hK hx hwt hin
  have hb := SolidMono.bind_exc hT hN hP hL hX hD t (by rw [← hE]; exact ht)
  rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl] at heq
  have h0 := hb.1 heq.le
  have hord : t.g.ord = Γ.ord := by
    simp only [Graph.obl, h0, hΓ0] at heq
    linarith
  refine ⟨h0, ?_, ?_⟩
  · obtain ⟨E', hE', hT'⟩ := SolidMono.gg_rep hN hP hL hx hin
    exact SolidMono.bind_lw hT' hwt t (by rw [← hE']; exact ht) hlf hord.le
  · rcases ggLemma k n C x y y' Γ hx hN hL hP hwt hin t ht hlf with h | ⟨z, -, hpr⟩
    · omega
    · exact SolidMono.solidN_le_pair hN.2.1 hb.2 hpr

private theorem SolidMono.rel_count {m : ℕ} {l' l : List (Comp (Atom k m))}
    (hR : List.Forall₂ ORel l' l) (P : Kind → Bool) :
    (l'.filter fun c => P c.kind).length = (l.filter fun c => P c.kind).length := by
  induction hR with
  | nil => rfl
  | cons h _ ih =>
    rw [List.filter_cons, List.filter_cons, h.1]
    split_ifs <;> simp [ih]

private theorem SolidMono.rel_lf {m : ℕ} {l' l : List (Comp (Atom k m))}
    (hR : List.Forall₂ ORel l' l) (h : ∀ c ∈ l', c.label = none) : ∀ c ∈ l, c.label = none := by
  induction hR with
  | nil => intro c hc; cases hc
  | cons hc _ ih =>
    intro c hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · rw [← hc.2.2.1]
      exact h _ (List.mem_cons_self ..)
    · exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) c hc'

private theorem SolidMono.rel_map_ord {m : ℕ} {l' l : List (Comp (Atom k m))}
    (hR : List.Forall₂ ORel l' l) : l'.map (fun c => c.kind.ord) = l.map (fun c => c.kind.ord) := by
  induction hR with
  | nil => rfl
  | cons h _ ih => simp [h.1, ih]

private theorem SolidMono.rel_ord {m : ℕ} {g' g : Graph k m}
    (hR : List.Forall₂ ORel g'.comps g.comps) : g'.ord = g.ord := by
  unfold Graph.ord
  rw [SolidMono.rel_map_ord hR]

/-- **The transposed `GG` expansion ([I, Lemma 3.16], [II, (4.10)]) at equal order: light weights
and solid edges.** At an internal atom `x` of a graph without dotted edges, under the hypotheses of
`oGGTT_step`, every label-free output of the same order in the count of [II, (2.5)] has dot excess
`0` and at most the light weights and the solid edges of the input. -/
theorem oGGTT_lwSolid {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) (hx : x.isRight = true)
    (hwt : Γ.wt x = 0) {y y' : Atom k n} (hin : Γ.GGInputAt x y y')
    (hD : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    ∀ t ∈ oGGTT x Γ, t.g.LabelFree → t.g.paperOrd = Γ.paperOrd →
      t.g.dotExcess = 0 ∧ t.g.lwN ≤ Γ.lwN ∧ t.g.solidN ≤ Γ.solidN := by
  intro t ht hlf heq
  have hΓ0 := SolidMono.dotExcess_zero hD
  obtain ⟨E, hE, hT, -⟩ := oGGTT_rep hN hP hL hK hx hwt hin
  have hb := SolidMono.bind_exc hT hN hP hL hX hD t (by rw [← hE]; exact ht)
  rw [Graph.paperOrd_eq_obl, Graph.paperOrd_eq_obl] at heq
  have h0 := hb.1 heq.le
  have hord : t.g.ord = Γ.ord := by
    simp only [Graph.obl, h0, hΓ0] at heq
    linarith
  refine ⟨h0, ?_, ?_⟩
  · have hB := swapSolid_basic k n Γ
    obtain ⟨t₀, ht₀, m, g', g, f, rfl, rfl, -, hR⟩ := oGGTT_rel x Γ t ht
    have hlf₀ : g.LabelFree := SolidMono.rel_lf hR hlf
    have hord' : g'.ord = Γ.ord := hord
    have hord₀ : g.ord ≤ Γ.swapSolid.ord := by
      rw [← SolidMono.rel_ord hR, hB.2.1, hord']
    obtain ⟨E', hE', hT'⟩ := SolidMono.gg_rep (Graph.swapSolid_Normal hN) (hB.2.2.2.1.2 hP)
      (hB.2.2.1.2 hL) hx (swap_ggInput hin)
    have h1 : g.lwN ≤ Γ.swapSolid.lwN := SolidMono.bind_lw hT'
      (by rw [hB.2.2.2.2.2.2.1]; exact hwt) _ (by rw [← hE']; exact ht₀) hlf₀ hord₀
    have h2 : Γ.swapSolid.lwN = Γ.lwN := by
      simp [Graph.lwN, Graph.swapSolid_comps', List.filter_map, Function.comp_def,
        Comp.swapSolid_kind']
    change g'.lwN ≤ Γ.lwN
    unfold Graph.lwN at h1 h2 ⊢
    rw [SolidMono.rel_count hR Kind.isLt]
    omega
  · rcases ggLemmaT k n C x y y' Γ hx hN hL hP hwt hin t ht hlf with h | ⟨z, -, hpr⟩
    · omega
    · exact SolidMono.solidN_le_pair hN.2.1 hb.2 hpr

end Main

section Instances

end Instances

end RBM8D.Graphs
