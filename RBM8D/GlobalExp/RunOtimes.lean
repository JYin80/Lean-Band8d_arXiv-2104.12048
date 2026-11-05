import RBM8D.GlobalExp.RunCompare
import Batteries.Tactic.OpenPrivate

/-!
# The component at `⊗`, the label atoms and the minors along the run of the selector

[II, Def 3.3 (4)] on the output graphs of the run of [II, Strategy 6.6] driven by the selector
`TerminationC_sel` ([II, Lemma 6.8]) from the graphs of `A` and `Q` of the second order
`T`-expansion, with a family `𝔈` of `Q`-expansions of [II, Lemma 4.15] (`QExpFamilyStmt`):

* `RunOtimes.selRun_otimes`: every output graph has exactly one component with an end at `⊗`, a
  plain `Θ` edge from `⊗` to an atom `v ≠ ⊗` without minor and without label (the field form of
  `Graph.ThetaRooted`); every label atom is internal, or the graph has no internal atom and the
  label atom is `⊕`; every component has an empty minor.

The three properties hold on the inputs and pass along every step of the run. On the local
expansions of Step 1 the components at `⊗` of every term, labels removed, are up to order the
images of those of the graph under the atom map of the term, which fixes `⊗`, `⊕`, `⊖` and sends
internal atoms to internal atoms (the terms of [II, Defs 4.3–4.6] keep, lift or replace the
components, and the replaced and new components are random or between internal atoms). `O_dot`
([II, Def 4.2]) keeps the component at `⊗` and maps it by its atom map. The substitution of
Steps 2–3 keeps it in the host graph `H`, since `x`, `y₁`, `y₂` are internal. A `Q`-expansion of
Step 3 maps it by the atom map of the output graph (clause on `⊗` of [II, Lemma 4.15]), which
sends the internal end `v` to an internal atom ((F6) of `QExpFamilyStmt`), so that `⊗` is fixed.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private Local_stripC Local_Dec Local_DecT Local_GM Local_MovR Local_PathOK Local_NewOK
  Local_f2_right Local_mem_liftCs Local_diff_notRandom Local_solidC_xy Local_kind_solidC
  Local_eraseIdxs2_perm Local_splitRegular_dec Local_liftA_zero Local_liftCs_zero
  Local_comp_proj_zero Local_rd Local_SameR Local_oW2_decT Local_decT_conj Local_conj_conj_comps
  Local_conj_labelFree Local_good_at Local_multiEHat_decT Local_ggPos_res Local_conj_out
  Local_GM_conj Local_sw_sw_comps Local_sw_labelFree Local_sw_out Local_decT_sw Local_GM_sw
  Local_mergeT_spec Local_MergeSpec Local_merge_mem Local_mergeComp Local_mergeComp_some
  Local_dotChoice_comps Local_kept Local_added Local_sp_mem Local_xonly Local_mrep
  Local_weight_random Local_f2_left from RBM8D.GlobalExp.Local
open private TerminationC_invB from RBM8D.GlobalExp.TerminationC
open private TerminationC2_Hyp TerminationC2_Good TerminationC2_key TerminationC2_inputs
  TerminationC2_tSubst_runKinds from RBM8D.GlobalExp.TerminationC2
open private h2Rec_root h2Rec_struct from RBM8D.TExp.Second
open private RunCompare_def63_leaf RunCompare_def63_Q RunCompare_def63_pmQ RunCompare_def63_rg
  RunCompare_q0_out from RBM8D.GlobalExp.RunCompare

/-! ## The components at `⊗` -/

section Toolkit

variable {n m : ℕ}

/-- The component has an end at `⊗`. -/
private abbrev RunOtimes_at (c : Comp (Atom 3 n)) : Bool := decide (c.x = .inl 0 ∨ c.y = .inl 0)

/-- Every component at `⊗` is diffusive (`Graph.TensorDiffusive`). -/
private def RunOtimes_TD (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true

/-- An atom map that fixes the external atoms and sends internal atoms to internal atoms. -/
private def RunOtimes_AtomOK (f : Atom 3 n → Atom 3 m) : Prop :=
  (∀ a : Fin 3, f (.inl a) = .inl a) ∧ ∀ i : Fin n, (f (.inr i)).isRight = true

private theorem RunOtimes_AtomOK.eq0 {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f)
    (u : Atom 3 n) : f u = .inl 0 ↔ u = .inl 0 := by
  cases u with
  | inl a => rw [hf.1 a]; simp
  | inr i =>
    have h := hf.2 i
    constructor
    · intro e
      rw [e] at h
      simp at h
    · intro e
      cases e

private theorem RunOtimes_AtomOK.isRight {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f)
    {u : Atom 3 n} (hu : u.isRight = true) : (f u).isRight = true := by
  cases u with
  | inl a => simp at hu
  | inr i => exact hf.2 i

private theorem RunOtimes_AtomOK.ne0 {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f)
    {u : Atom 3 n} (hu : u ≠ .inl 0) : f u ≠ .inl 0 := fun h => hu ((hf.eq0 u).1 h)

private theorem RunOtimes_AtomOK.plus {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f) :
    f (.inl 1) = .inl 1 := hf.1 1

private theorem RunOtimes_atomOK_id : RunOtimes_AtomOK (id : Atom 3 n → Atom 3 n) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

private theorem RunOtimes_atomOK_comp {l : ℕ} {f : Atom 3 n → Atom 3 m} {g : Atom 3 m → Atom 3 l}
    (hf : RunOtimes_AtomOK f) (hg : RunOtimes_AtomOK g) : RunOtimes_AtomOK (g ∘ f) :=
  ⟨fun a => by simp [hf.1 a, hg.1 a], fun i => hg.isRight (hf.2 i)⟩

private theorem RunOtimes_atomOK_liftA (j : ℕ) :
    RunOtimes_AtomOK (liftA j : Atom 3 n → Atom 3 (n + j)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

private theorem RunOtimes_at_map {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f)
    (c : Comp (Atom 3 n)) : RunOtimes_at (c.map f) = RunOtimes_at c := by
  simp only [RunOtimes_at, Comp.map, hf.eq0]

private theorem RunOtimes_filter_map {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f)
    (L : List (Comp (Atom 3 n))) :
    (L.map (Comp.map f)).filter RunOtimes_at = (L.filter RunOtimes_at).map (Comp.map f) := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun c _ => ?_
  simp only [Function.comp_apply, RunOtimes_at_map hf]

private theorem RunOtimes_comp_map_id (c : Comp (Atom 3 n)) : c.map id = c := by
  obtain ⟨κ, a, b, l, lab⟩ := c
  simp [Comp.map]

private theorem RunOtimes_map_map_id (L : List (Comp (Atom 3 n))) : L.map (Comp.map id) = L := by
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun c _ => RunOtimes_comp_map_id c

private theorem RunOtimes_comp_map_comp {l : ℕ} (f : Atom 3 n → Atom 3 m) (g : Atom 3 m → Atom 3 l)
    (c : Comp (Atom 3 n)) : (c.map f).map g = c.map (g ∘ f) := by
  obtain ⟨κ, a, b, mi, lab⟩ := c
  cases lab with
  | none => simp [Comp.map]
  | some p => obtain ⟨a, b⟩ := p; simp [Comp.map]

/-- The plain `Θ` edge from `⊗` to `v`. -/
private theorem RunOtimes_root_map (f : Atom 3 n → Atom 3 m) (v : Atom 3 n) :
    (mkC (.theta []) (.inl 0) v).map f = mkC (.theta []) (f (.inl 0)) (f v) := rfl

/-- A list whose filter is one entry: the entry is at some index and no other entry passes the
filter. -/
private theorem RunOtimes_filter_single {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.filter p = [a] →
      ∃ (j : ℕ) (hj : j < l.length), l[j] = a ∧ ∀ c ∈ l.eraseIdx j, p c = false
  | [], a, h => by simp at h
  | b :: l, a, h => by
    by_cases hb : p b = true
    · rw [List.filter_cons_of_pos hb, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      refine ⟨0, by simp, rfl, fun c hc => ?_⟩
      simp only [List.eraseIdx_cons_zero] at hc
      have : c ∉ l.filter p := by rw [h]; exact List.not_mem_nil
      simpa [List.mem_filter, hc] using this
    · rw [List.filter_cons_of_neg hb] at h
      obtain ⟨j, hj, e, hr⟩ := RunOtimes_filter_single p l a h
      refine ⟨j + 1, by simp; omega, by simpa using e, fun c hc => ?_⟩
      simp only [List.eraseIdx_cons_succ, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simpa using hb
      · exact hr c hc

/-- The converse of `RunOtimes_filter_single`. -/
private theorem RunOtimes_single_filter {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (j : ℕ) (hj : j < l.length), p l[j] = true →
      (∀ c ∈ l.eraseIdx j, p c = false) → l.filter p = [l[j]]
  | [], j, hj, _, _ => by simp at hj
  | b :: l, 0, _, hp, hr => by
    simp only [List.getElem_cons_zero] at hp ⊢
    rw [List.filter_cons_of_pos hp, List.filter_eq_nil_iff.2 fun c hc => by
      simpa using hr c (by simpa using hc)]
  | b :: l, j + 1, hj, hp, hr => by
    have hb : p b = false := hr b (by simp)
    rw [List.filter_cons_of_neg (by simp [hb])]
    exact RunOtimes_single_filter p l j (by simpa using hj) (by simpa using hp)
      fun c hc => hr c (by simp [hc])

/-- The field form of [II, Def 3.3 (4)] (`Graph.ThetaRooted`) at `⊗` from the filter of the
components at `⊗`. -/
private theorem RunOtimes_fields {Γ : Graph 3 n} {v : Atom 3 n} (hv : v ≠ .inl 0)
    (h : Γ.comps.filter RunOtimes_at = [mkC (.theta []) (.inl 0) v]) :
    ∃ (j : Fin Γ.comps.length) (v : Atom 3 n), v ≠ .inl 0 ∧
      Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧ Γ.comps[j].label = none ∧
      (Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v) ∧
      ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
  obtain ⟨j, hj, e, hr⟩ := RunOtimes_filter_single _ _ _ h
  refine ⟨⟨j, hj⟩, v, hv, ?_, ?_, ?_, ⟨?_, ?_⟩, fun c hc => ?_⟩
  all_goals try (simp only [Fin.getElem_fin, e]; rfl)
  have := hr c hc
  simp only [RunOtimes_at, decide_eq_false_iff_not, not_or] at this
  exact this

/-- The filter of the components at `⊗` from the field form. -/
private theorem RunOtimes_of_fields {Γ : Graph 3 n} (j : Fin Γ.comps.length) (v : Atom 3 n)
    (h1 : Γ.comps[j].kind = .theta []) (h2 : Γ.comps[j].minor = []) (h3 : Γ.comps[j].label = none)
    (h4 : Γ.comps[j].x = .inl 0) (h5 : Γ.comps[j].y = v)
    (h6 : ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0) :
    Γ.comps.filter RunOtimes_at = [mkC (.theta []) (.inl 0) v] := by
  have e : Γ.comps[(j : ℕ)] = mkC (.theta []) (.inl 0) v := by
    have h1' : Γ.comps[(j : ℕ)].kind = .theta [] := h1
    have h2' : Γ.comps[(j : ℕ)].minor = [] := h2
    have h3' : Γ.comps[(j : ℕ)].label = none := h3
    have h4' : Γ.comps[(j : ℕ)].x = .inl 0 := h4
    have h5' : Γ.comps[(j : ℕ)].y = v := h5
    generalize Γ.comps[(j : ℕ)] = c at h1' h2' h3' h4' h5'
    obtain ⟨κ, a, b, mi, lab⟩ := c
    simp only at h1' h2' h3' h4' h5'
    subst h1' h2' h3' h4' h5'
    rfl
  rw [← e]
  refine RunOtimes_single_filter _ _ _ j.2 (by simp [e, mkC]) fun c hc => ?_
  have := h6 c hc
  simp only [RunOtimes_at, decide_eq_false_iff_not, not_or]
  exact this

/-- The components at `⊗` with their labels removed. -/
private def RunOtimes_sf (L : List (Comp (Atom 3 n))) : List (Comp (Atom 3 n)) :=
  (L.map Local_stripC).filter RunOtimes_at

private theorem RunOtimes_sf_eq (L : List (Comp (Atom 3 n))) :
    RunOtimes_sf L = (L.filter RunOtimes_at).map Local_stripC := by
  unfold RunOtimes_sf
  rw [List.filter_map]
  rfl

private theorem RunOtimes_strip_map (f : Atom 3 n → Atom 3 m) (c : Comp (Atom 3 n)) :
    Local_stripC (c.map f) = (Local_stripC c).map f := by
  obtain ⟨κ, a, b, mi, lab⟩ := c
  rfl

end Toolkit

/-! ## `O_dot` and the component at `⊗` -/

section ODot

variable {n : ℕ}

private theorem RunOtimes_diff_kind {κ : Kind} (h : κ.isDiffusive = true) :
    κ ≠ .dot ∧ κ ≠ .xdot ∧ κ.isSolid = false := by
  cases κ <;> simp_all [Kind.isDiffusive, Kind.isSolid]

/-- The components of `Graph.mergeT` at `⊗` are the images of those of the graph when no
component at `⊗` is a dotted or a solid edge. -/
private theorem RunOtimes_filterMap_merge {m : ℕ} (rep : Atom 3 n → Atom 3 n)
    {f : Atom 3 n → Atom 3 m} (hf : RunOtimes_AtomOK f) : ∀ L : List (Comp (Atom 3 n)),
    (∀ c ∈ L, RunOtimes_at c = true → c.kind ≠ .dot ∧ c.kind.isSolid = false) →
    (L.filterMap (Local_mergeComp rep f)).filter RunOtimes_at =
      (L.filter RunOtimes_at).map (Comp.map f)
  | [], _ => rfl
  | c :: L, h => by
    have ih := RunOtimes_filterMap_merge rep hf L fun d hd => h d (List.mem_cons_of_mem _ hd)
    by_cases hc : RunOtimes_at c = true
    · obtain ⟨h1, h2⟩ := h c List.mem_cons_self hc
      have e : Local_mergeComp rep f c = some (c.map f) := by
        unfold Local_mergeComp
        simp [h1, h2]
      rw [List.filterMap_cons_some e,
        List.filter_cons_of_pos (by rw [RunOtimes_at_map hf]; exact hc),
        List.filter_cons_of_pos hc, List.map_cons, ih]
    · rw [List.filter_cons_of_neg hc]
      rcases e : Local_mergeComp rep f c with _ | c'
      · rw [List.filterMap_cons_none e]
        exact ih
      · rw [List.filterMap_cons_some e, List.filter_cons_of_neg ?_]
        · exact ih
        rcases Local_mergeComp_some e with ⟨-, -, rfl⟩ | ⟨rfl, -, -⟩
        · have hx : ¬ c.x = .inl 0 := fun h0 => hc (by simp [RunOtimes_at, h0])
          simp only [RunOtimes_at, Comp.map, or_self, decide_eq_true_eq]
          exact fun h0 => hx ((hf.eq0 _).1 h0)
        · rw [RunOtimes_at_map hf]
          exact hc

/-- Under `RunOtimes_TD`, the components of `Graph.dotChoice` at `⊗` are those of the graph: the
added dotted and `×`-dotted edges join the two atoms of a solid or a `×`-dotted edge, and only
`×`-dotted edges are removed. -/
private theorem RunOtimes_dotChoice_filter {Γ : Graph 3 n} (hT : RunOtimes_TD Γ)
    (A : List (Atom 3 n × Atom 3 n × Bool)) :
    (Γ.dotChoice Γ.splitPairs A).comps.filter RunOtimes_at = Γ.comps.filter RunOtimes_at := by
  rw [Local_dotChoice_comps, List.filter_append]
  have hadd : (Local_added Γ.splitPairs A).filter RunOtimes_at = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc h0
    have h0 : c.x = .inl 0 ∨ c.y = .inl 0 := of_decide_eq_true h0
    unfold Local_added at hc
    obtain ⟨p, hp, hpc⟩ := List.mem_filterMap.1 hc
    have hpe : c.x = p.1 ∧ c.y = p.2.1 := by
      split_ifs at hpc <;> obtain rfl := Option.some.inj hpc <;> exact ⟨rfl, rfl⟩
    obtain ⟨hs1, hs2⟩ := Local_sp_mem hp
    obtain ⟨d, hd, hk, hde⟩ : ∃ d ∈ Γ.comps, d.kind.isDiffusive = false ∧
        (d.x = p.1 ∧ d.y = p.2.1 ∨ d.x = p.2.1 ∧ d.y = p.1) := by
      cases hb : p.2.2
      · obtain ⟨d, hd, hk, he⟩ := hs2 hb
        exact ⟨d, hd, by rw [hk]; rfl, he⟩
      · obtain ⟨d, hd, hk, he⟩ := hs1 hb
        refine ⟨d, hd, ?_, he⟩
        cases h : d.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
    have : d.x = .inl 0 ∨ d.y = .inl 0 := by
      rw [hpe.1, hpe.2] at h0
      rcases hde with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> tauto
    rw [hT d hd this] at hk
    cases hk
  rw [hadd, List.append_nil]
  unfold Local_kept
  rw [List.filter_filter]
  refine List.filter_congr fun c hc => ?_
  by_cases h0 : RunOtimes_at c = true
  · have hk := hT c hc (of_decide_eq_true h0)
    have : c.kind ≠ .xdot := (RunOtimes_diff_kind hk).2.1
    simp [h0, this]
  · simp only [Bool.not_eq_true] at h0
    simp [h0]

/-- **`O_dot` and the component at `⊗`** ([II, Def 4.2]): the atom map of a term fixes the
external atoms and sends internal atoms to internal atoms (a graph without internal atom gives
graphs without internal atom); every component of the term is the image of a component of the
graph with the label and the minor mapped, or carries neither label nor minor; and when every
component at `⊗` is diffusive, the components at `⊗` of the term are the images of those of the
graph. -/
private theorem RunOtimes_oDotT {Γ : Graph 3 n} {t : Tracked 3 n} (ht : t ∈ oDotT Γ) :
    RunOtimes_AtomOK t.f ∧ (n = 0 → t.nOut = 0) ∧
    (∀ c' ∈ t.g.comps, (∃ c ∈ Γ.comps, c'.label = c.label.map (Prod.map id t.f) ∧
        c'.minor = c.minor.map t.f) ∨ (c'.label = none ∧ c'.minor = [])) ∧
    (RunOtimes_TD Γ →
      t.g.comps.filter RunOtimes_at = (Γ.comps.filter RunOtimes_at).map (Comp.map t.f)) := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · refine ⟨RunOtimes_atomOK_id, fun h => h, fun c hc => Or.inl ⟨c, hc, ?_, ?_⟩, fun _ => ?_⟩
    · change c.label = c.label.map (Prod.map id id)
      simp
    · change c.minor = c.minor.map id
      simp
    · exact (RunOtimes_map_map_id _).symm
  obtain ⟨hcomps, -, hle, hinl, -, ⟨g, hg, -⟩, -⟩ := Local_mergeT_spec hm
  have hf : RunOtimes_AtomOK t.f := ⟨hinl, fun i => by rw [hg i]; rfl⟩
  refine ⟨hf, fun h0 => by omega, fun c' hc' => ?_, fun hT => ?_⟩
  · obtain ⟨c, hc, hmc⟩ := Local_merge_mem hm hc'
    have hlm : c'.label = c.label.map (Prod.map id t.f) ∧ c'.minor = c.minor.map t.f := by
      rcases Local_mergeComp_some hmc with ⟨-, -, rfl⟩ | ⟨rfl, -, -⟩ <;> exact ⟨rfl, rfl⟩
    rw [Local_dotChoice_comps] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl ⟨c, (List.mem_filter.1 hc).1, hlm⟩
    · right
      unfold Local_added at hc
      obtain ⟨p, -, hpc⟩ := List.mem_filterMap.1 hc
      have hn : c.label = none ∧ c.minor = [] := by
        split_ifs at hpc <;> obtain rfl := Option.some.inj hpc <;> exact ⟨rfl, rfl⟩
      rw [hlm.1, hlm.2, hn.1, hn.2]
      exact ⟨rfl, rfl⟩
  · rw [hcomps, RunOtimes_filterMap_merge _ hf, RunOtimes_dotChoice_filter hT]
    intro c hc h0
    have hm' : c ∈ Γ.comps.filter RunOtimes_at := by
      rw [← RunOtimes_dotChoice_filter hT A]
      exact List.mem_filter.2 ⟨hc, h0⟩
    obtain ⟨hc', -⟩ := List.mem_filter.1 hm'
    have hk := RunOtimes_diff_kind (hT c hc' (of_decide_eq_true h0))
    exact ⟨hk.1, hk.2.2⟩

end ODot

/-! ## The local expansions and the component at `⊗` -/

section Track

variable {n : ℕ}

/-- A term `t` of an expansion of `Γ`: its atom map fixes the external atoms and sends internal
atoms to internal atoms, and when every component of `Γ` at `⊗` is diffusive, the components of `t`
at `⊗`, labels removed, are up to order the images of those of `Γ`. -/
private def RunOtimes_Track (Γ : Graph 3 n) (t : Tracked 3 n) : Prop :=
  RunOtimes_AtomOK t.f ∧
    (RunOtimes_TD Γ → (RunOtimes_sf t.g.comps).Perm ((RunOtimes_sf Γ.comps).map (Comp.map t.f)))

private theorem RunOtimes_track_self (Γ : Graph 3 n) : RunOtimes_Track Γ (Tracked.self Γ) :=
  ⟨RunOtimes_atomOK_id, fun _ => by
    change (RunOtimes_sf Γ.comps).Perm ((RunOtimes_sf Γ.comps).map (Comp.map id))
    rw [RunOtimes_map_map_id]⟩

/-- Every component at `⊗` of a term is diffusive. -/
private theorem RunOtimes_track_td {Γ : Graph 3 n} {t : Tracked 3 n} (h : RunOtimes_Track Γ t)
    (hT : RunOtimes_TD Γ) : RunOtimes_TD t.g := by
  intro c hc h0
  have hm : Local_stripC c ∈ RunOtimes_sf t.g.comps :=
    List.mem_filter.2 ⟨List.mem_map_of_mem hc, decide_eq_true h0⟩
  obtain ⟨d, hd, e⟩ := List.mem_map.1 ((h.2 hT).subset hm)
  obtain ⟨hd, hd0⟩ := List.mem_filter.1 hd
  obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
  have hk : c.kind = d₀.kind := (congrArg Comp.kind e).symm
  rw [hk]
  exact hT d₀ hd₀ (of_decide_eq_true hd0)

private theorem RunOtimes_track_bind {Γ : Graph 3 n} {E : TExpansion 3 n}
    {O : ∀ {n' : ℕ}, (Atom 3 n → Atom 3 n') → Graph 3 n' → TExpansion 3 n'}
    (hE : ∀ t ∈ E, RunOtimes_Track Γ t)
    (hO : ∀ t ∈ E, ∀ s ∈ O t.f t.g, RunOtimes_Track t.g s) :
    ∀ u ∈ E.bind O, RunOtimes_Track Γ u := by
  intro u hu
  unfold TExpansion.bind at hu
  obtain ⟨t, ht, hu⟩ := List.mem_flatMap.1 hu
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
  obtain ⟨a1, a2⟩ := hE t ht
  obtain ⟨b1, b2⟩ := hO t ht s hs
  refine ⟨show RunOtimes_AtomOK (s.f ∘ t.f) from RunOtimes_atomOK_comp a1 b1, fun hT => ?_⟩
  change (RunOtimes_sf s.g.comps).Perm ((RunOtimes_sf Γ.comps).map (Comp.map (s.f ∘ t.f)))
  refine (b2 (RunOtimes_track_td ⟨a1, a2⟩ hT)).trans (((a2 hT).map _).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq (List.map_congr_left fun c _ => RunOtimes_comp_map_comp _ _ c)

private theorem RunOtimes_track_oDot (Γ : Graph 3 n) : ∀ t ∈ oDotT Γ, RunOtimes_Track Γ t := by
  intro t ht
  obtain ⟨hf, -, -, hfil⟩ := RunOtimes_oDotT ht
  refine ⟨hf, fun hT => List.Perm.of_eq ?_⟩
  rw [RunOtimes_sf_eq, RunOtimes_sf_eq, hfil hT, List.map_map, List.map_map]
  exact List.map_congr_left fun c _ => RunOtimes_strip_map t.f c

private theorem RunOtimes_dot_after {Γ : Graph 3 n} {E : TExpansion 3 n}
    (hE : ∀ t ∈ E, RunOtimes_Track Γ t) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), RunOtimes_Track Γ t :=
  RunOtimes_track_bind hE fun t _ s hs => RunOtimes_track_oDot t.g s hs

/-- A random component of a graph with `RunOtimes_TD` has no end at `⊗`. -/
private theorem RunOtimes_random_at {Γ : Graph 3 n} (hT : RunOtimes_TD Γ) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps.map Local_stripC) (hr : c.kind.isRandom = true) : RunOtimes_at c = false := by
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  cases h0 : RunOtimes_at (Local_stripC c₀)
  · rfl
  · exfalso
    have h0' : c₀.x = .inl 0 ∨ c₀.y = .inl 0 := of_decide_eq_true h0
    have hr' : c₀.kind.isRandom = true := hr
    rw [Local_diff_notRandom (hT c₀ hc₀ h0')] at hr'
    cases hr'

/-- **The components at `⊗` of a term of `Local_Dec`** ([II, Defs 4.3–4.6]): the kept
components are lifted, the replaced components and the path are random, and the new components join
internal atoms. -/
private theorem RunOtimes_dec {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (hd : Local_Dec Γ x j Γ') (hT : RunOtimes_TD Γ) :
    (RunOtimes_sf Γ'.comps).Perm ((RunOtimes_sf Γ.comps).map (Comp.map (liftA j))) := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, -⟩ := hd
  have inl0 : ∀ u : Atom 3 n, (liftA j u : Atom 3 (n + j)) = .inl 0 ↔ u = .inl 0 :=
    (RunOtimes_atomOK_liftA j).eq0
  have int0 : ∀ u : Atom 3 (n + j), u.isRight = true → u ≠ .inl 0 := by
    rintro u hu rfl
    simp at hu
  have memΓ : ∀ c ∈ K ++ D ++ P ++ R, c ∈ Γ.comps.map Local_stripC :=
    fun c hc => h1.symm.subset hc
  have hnil : ∀ L : List (Comp (Atom 3 n)), (∀ c ∈ L, c ∈ K ++ D ++ P ++ R) →
      (∀ c ∈ L, c.kind.isRandom = true) → L.filter RunOtimes_at = [] := by
    intro L hL hr
    rw [List.filter_eq_nil_iff]
    intro c hc h0
    rw [RunOtimes_random_at hT (memΓ c (hL c hc)) (hr c hc)] at h0
    cases h0
  have hK : (K ++ D ++ P ++ R).filter RunOtimes_at = K.filter RunOtimes_at := by
    rw [List.filter_append, List.filter_append, List.filter_append,
      hnil D (fun c hc => by simp [hc]) (fun c hc => (Local_f2_left h3 hc).elim fun _ h => h.2.2.1),
      hnil P (fun c hc => by simp [hc]) ?_, hnil R (fun c hc => by simp [hc])
        (fun c hc => Local_weight_random (h5 c hc))]
    · simp
    · intro c hc
      rcases h4 with ⟨rfl, -⟩ | ⟨c', ch, u, v, rfl, hk, -⟩
      · simp at hc
      · rw [List.mem_singleton] at hc
        subst hc
        rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hD' : ∀ d ∈ D' ++ P' ++ N, RunOtimes_at d = false := by
    intro d hd
    cases h0' : RunOtimes_at d
    · rfl
    exfalso
    have h0 : d.x = .inl 0 ∨ d.y = .inl 0 := of_decide_eq_true h0'
    have hrand : ∀ c ∈ K ++ D ++ P ++ R, c.kind.isRandom = true → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
      intro c hc hr
      have := RunOtimes_random_at hT (memΓ c hc) hr
      simp only [RunOtimes_at, decide_eq_false_iff_not, not_or] at this
      exact this
    simp only [List.mem_append] at hd
    rcases hd with (h | h) | h
    · obtain ⟨d₀, hd₀, hk, hr, hx, hy, -⟩ := Local_f2_right h3 h
      obtain ⟨n1, n2⟩ := hrand d₀ (by simp [hd₀]) hr
      rcases h0 with h0 | h0
      · rcases hx with hx | ⟨-, hx⟩
        · rw [hx, inl0] at h0; exact n1 h0
        · exact int0 _ hx h0
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, inl0] at h0; exact n2 h0
        · exact int0 _ hy h0
    · rcases h4 with ⟨-, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, -, -, hp⟩
      · simp at h
      · have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
        obtain ⟨n1, n2⟩ := hrand c (by simp) hcr
        rw [hp.mem_iff] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · rw [(Local_solidC_xy _ _ _).1, (Local_solidC_xy _ _ _).2, inl0] at h0
          rcases h0 with h0 | h0
          · exact n1 h0
          · exact int0 _ hu h0
        · rw [(Local_solidC_xy _ _ _).1, (Local_solidC_xy _ _ _).2, inl0] at h0
          rcases h0 with h0 | h0
          · exact int0 _ hv h0
          · split_ifs at h0
            · exact n1 h0
            · exact n2 h0
    · obtain ⟨hx, hy, -⟩ := h6 d h
      rcases h0 with h0 | h0
      · exact int0 _ hx h0
      · exact int0 _ hy h0
  have hK' : (liftCs j K ++ D' ++ P' ++ N).filter RunOtimes_at =
      (K.filter RunOtimes_at).map (Comp.map (liftA j)) := by
    have hrest : (D' ++ (P' ++ N)).filter RunOtimes_at = [] :=
      List.filter_eq_nil_iff.2 fun d hd h0 => by
        rw [hD' d (by simpa [List.append_assoc] using hd)] at h0
        cases h0
    rw [List.append_assoc, List.append_assoc, List.filter_append, hrest, List.append_nil]
    exact RunOtimes_filter_map (RunOtimes_atomOK_liftA j) K
  unfold RunOtimes_sf
  refine (h2.filter _).symm.trans ?_
  rw [hK', ← hK]
  exact (h1.filter _).symm.map _

private theorem RunOtimes_track_dec {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {t : Tracked 3 n}
    (hn : t.nOut = n + j) (hf : ∀ u, t.f u = hn ▸ liftA j u) (hd : Local_Dec Γ x j (hn ▸ t.g)) :
    RunOtimes_Track Γ t := by
  obtain ⟨tn, tg, tf⟩ := t
  simp only at hn
  subst hn
  simp only at hf hd
  have e : tf = liftA j := funext hf
  subst e
  exact ⟨RunOtimes_atomOK_liftA j, RunOtimes_dec hd⟩

private theorem RunOtimes_track_decT {Δ : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Local_DecT Δ x t) : RunOtimes_Track Δ t := by
  obtain ⟨j, hn, hf, hd, -⟩ := h
  exact RunOtimes_track_dec hn hf hd

/-- **The main term of the `GG` expansion** keeps the components at `⊗`: the two solid edges
removed and the solid edge added have no end at `⊗`, and the waved edge joins internal atoms. -/
private theorem RunOtimes_track_GM {Δ : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Local_GM Δ x t) : RunOtimes_Track Δ t := by
  obtain ⟨Γ', rfl, i, j, hi, hj, ch, w, wv, hij, hki, hkj, hxi, hyj, hw, hperm, -⟩ := h
  refine ⟨RunOtimes_atomOK_id, fun hT => ?_⟩
  change (RunOtimes_sf Γ'.comps).Perm ((RunOtimes_sf Δ.comps).map (Comp.map id))
  rw [RunOtimes_map_map_id]
  have hΔ := Local_eraseIdxs2_perm Δ.comps i j hi hj hij
  have hnt : ∀ (k : ℕ) (hk : k < Δ.comps.length), Δ.comps[k].kind = .G ch →
      Δ.comps[k].x ≠ .inl 0 ∧ Δ.comps[k].y ≠ .inl 0 := by
    intro k hk hkk
    constructor
    · intro h0
      have := hT _ (List.getElem_mem hk) (Or.inl h0)
      rw [hkk] at this
      cases this
    · intro h0
      have := hT _ (List.getElem_mem hk) (Or.inr h0)
      rw [hkk] at this
      cases this
  obtain ⟨ni1, ni2⟩ := hnt i hi hki
  obtain ⟨nj1, nj2⟩ := hnt j hj hkj
  have h2 : [solidC ch Δ.comps[j].x Δ.comps[i].y, mkC (.waved wv) (.inr x) (.inr w)].filter
      RunOtimes_at = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc h0
    have h0 : c.x = .inl 0 ∨ c.y = .inl 0 := of_decide_eq_true h0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [(Local_solidC_xy _ _ _).1, (Local_solidC_xy _ _ _).2] at h0
      rcases h0 with h0 | h0
      · exact nj1 h0
      · exact ni2 h0
    · simp [mkC] at h0
  have h3 : ([Δ.comps[i], Δ.comps[j]].map Local_stripC).filter RunOtimes_at = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc h0
    have h0 : c.x = .inl 0 ∨ c.y = .inl 0 := of_decide_eq_true h0
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rcases h0 with h0 | h0
      · exact ni1 h0
      · exact ni2 h0
    · rcases h0 with h0 | h0
      · exact nj1 h0
      · exact nj2 h0
  unfold RunOtimes_sf
  refine (hperm.filter _).trans ?_
  rw [List.filter_append, h2, List.append_nil]
  refine List.Perm.trans ?_ ((hΔ.map _).filter _).symm
  rw [List.map_append, List.filter_append, h3, List.append_nil]

private theorem RunOtimes_lf_of_plain {Γ : Graph 3 n}
    (h : ¬ (!(Γ.comps.all Comp.isPlainB)) = true) : Γ.LabelFree := by
  intro c hc
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h
  have := h c hc
  unfold Comp.isPlainB at this
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1.2

private theorem RunOtimes_oWeight1 {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeight1T (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := Local_splitRegular_dec (.inr x) Γ.comps p hp
  refine RunOtimes_track_dec (j := 0) (x := x) rfl (fun u => (Local_liftA_zero u).symm) ?_
  refine ⟨K.map Local_stripC, D.map Local_stripC, [], R.map Local_stripC,
    D'.map Local_stripC, [], [], ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, by simp, fun i => i.elim0⟩
  · have := h1.map Local_stripC
    simpa [List.map_append] using this
  · rw [Local_liftCs_zero]
    have := (h2.map Local_stripC).symm
    simpa [List.map_append] using this
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h3.imp fun d d' ⟨ch, hk, hx, hl, hd'⟩ => ?_
    subst hd'
    refine ⟨Or.inr ⟨by simp [Local_stripC, hk, Kind.isWeight], by simp [Local_stripC,
      Kind.isWeight]⟩, by simp [Local_stripC, hk, Kind.isRandom],
      Or.inl (Local_liftA_zero _).symm, Or.inl (Local_liftA_zero _).symm, ?_⟩
    unfold Local_SameR
    rw [Local_comp_proj_zero]
    left
    refine ⟨?_, ?_⟩ <;> simp [Local_rd, Local_stripC, hk, Kind.mclass]
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨ch, hk⟩, -, -⟩ := h4 c₀ hc₀
    simp [Local_stripC, hk, Kind.isWeight]

private theorem RunOtimes_oWeight2 {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeight2T (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oWeight2T at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ
  have hlf := RunOtimes_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunOtimes_track_decT (Local_oW2_decT hlf x hE t ht)
  · split at ht
    · rename_i E _ hE
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      exact RunOtimes_track_decT (Local_decT_conj (Local_conj_conj_comps Γ)
        (Local_oW2_decT (Local_conj_labelFree hlf) x hE t₀ ht₀))
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunOtimes_track_self Γ

private theorem RunOtimes_oWeight {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeightT (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oWeightT at ht
  split_ifs at ht with hw
  · have h1 : ∀ t ∈ oWeight1T (.inr x) Γ, RunOtimes_Track Γ t := RunOtimes_oWeight1 x
    have h2 : ∀ t ∈ (oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g),
        RunOtimes_Track Γ t := by
      refine RunOtimes_track_bind h1 fun t ht s hs => ?_
      exact Local_good_at ((h1 t ht).1.2 x) (fun u => ∀ s ∈ oWeight2T u t.g, RunOtimes_Track t.g s)
        (fun x' => RunOtimes_oWeight2 x') s hs
    have h3 : ∀ t ∈ ((oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g)).bind
        (fun _ g => oDotT g), RunOtimes_Track Γ t := RunOtimes_dot_after h2
    refine RunOtimes_track_bind h3 (fun t ht s hs => ?_) t ht
    exact Local_good_at ((h3 t ht).1.2 x) (fun u => ∀ s ∈ oWeight1T u t.g, RunOtimes_Track t.g s)
      (fun x' => RunOtimes_oWeight1 x') s hs
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ

private theorem RunOtimes_oMultiE {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oMultiET (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oMultiET at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ
  have hlf := RunOtimes_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunOtimes_dot_after
      (fun t ht => RunOtimes_track_decT (Local_multiEHat_decT hlf x hE t ht)) t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ

private theorem RunOtimes_oGGbar {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oGGbarT (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oGGbarT at ht
  dsimp only at ht
  split_ifs at ht
  · exact RunOtimes_oMultiE x t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ

private theorem RunOtimes_res {Δ : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Local_DecT Δ x t ∨ Local_GM Δ x t) : RunOtimes_Track Δ t :=
  h.elim RunOtimes_track_decT RunOtimes_track_GM

private theorem RunOtimes_oGG {Γ : Graph 3 n} (x : Fin n)
    (hout : Γ.GGOutInt (.inr x)) : ∀ t ∈ oGGT (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oGGT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ
  have hlf := RunOtimes_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunOtimes_dot_after
      (fun t ht => RunOtimes_res (Local_ggPos_res hlf x hout hE t ht)) t ht
  · split at ht
    · rename_i E _ hE
      refine RunOtimes_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ
      rcases Local_ggPos_res (Local_conj_labelFree hlf) x (Local_conj_out hout) hE t₀ ht₀ with
        h | h
      · exact RunOtimes_track_decT (Local_decT_conj hc h)
      · exact RunOtimes_track_GM (Local_GM_conj hc h)
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunOtimes_track_self Γ

private theorem RunOtimes_oGGT {Γ : Graph 3 n} (x : Fin n)
    (hin : Γ.GGInInt (.inr x)) : ∀ t ∈ oGGTT (.inr x) Γ, RunOtimes_Track Γ t := by
  intro t ht
  unfold oGGTT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunOtimes_track_self Γ
  have hlf := RunOtimes_lf_of_plain hp
  have hs := Local_sw_sw_comps Γ
  have hlfs := Local_sw_labelFree hlf
  have houts := Local_sw_out hin
  split at ht
  · rename_i E hE
    refine RunOtimes_dot_after (fun t ht => ?_) t ht
    unfold TExpansion.swapSolid at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    rcases Local_ggPos_res hlfs x houts hE t₀ ht₀ with h | h
    · exact RunOtimes_track_decT (Local_decT_sw hs h)
    · exact RunOtimes_track_GM (Local_GM_sw hs h)
  · split at ht
    · rename_i E _ hE
      refine RunOtimes_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.swapSolid TExpansion.conj at ht
      rw [List.map_map] at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ.swapSolid
      rcases Local_ggPos_res (Local_conj_labelFree hlfs) x (Local_conj_out houts) hE t₀ ht₀ with
        h | h
      · exact RunOtimes_track_decT (Local_decT_sw hs (Local_decT_conj hc h))
      · exact RunOtimes_track_GM (Local_GM_sw hs (Local_GM_conj hc h))
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunOtimes_track_self Γ

/-- **The component at `⊗` along the local expansions** ([II, Defs 4.3–4.6], in the form of
`Graph.LocSide`): the atom map of every term fixes `⊗`, `⊕`, `⊖` and sends internal atoms to
internal atoms; if every component of `Γ` at `⊗` is diffusive, the components of the term at `⊗`,
labels removed, are up to order the images of those of `Γ`. -/
private theorem RunOtimes_localOp_otimes {Γ : Graph 3 n} (x : Fin n) (o : Fin 5)
    (hs : Γ.LocSide o (.inr x)) : ∀ t ∈ localOp' o (.inr x) Γ,
      (∀ a : Fin 3, t.f (.inl a) = .inl a) ∧ (∀ i : Fin n, (t.f (.inr i)).isRight = true) ∧
      ((∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true) →
        (((t.g.comps.map fun c => { c with label := none }).filter
            fun c => decide (c.x = .inl 0 ∨ c.y = .inl 0)).Perm
          (((Γ.comps.map fun c => { c with label := none }).filter
            fun c => decide (c.x = .inl 0 ∨ c.y = .inl 0)).map (Comp.map t.f)))) := by
  suffices h : ∀ t ∈ localOp' o (.inr x) Γ, RunOtimes_Track Γ t from
    fun t ht => ⟨(h t ht).1.1, (h t ht).1.2, (h t ht).2⟩
  obtain ⟨hs2, hs4⟩ := hs
  match o with
  | 0 => exact RunOtimes_oWeight x
  | 1 => exact RunOtimes_oMultiE x
  | 2 => exact RunOtimes_oGG x (hs2 rfl rfl)
  | 3 => exact RunOtimes_oGGbar x
  | 4 => exact RunOtimes_oGGT x (hs4 rfl rfl)

end Track

/-! ## The three properties along one step -/

section Steps

variable {n : ℕ}

/-- The three properties of an output graph on one graph: the only component at `⊗` is the plain
`Θ` edge from `⊗` to an atom `v ≠ ⊗`, internal unless the graph has no internal atom; every label
atom is internal, or the graph has no internal atom and the label atom is `⊕`; no minor. -/
private def RunOtimes_Inv (Γ : Graph 3 n) : Prop :=
  (∃ v : Atom 3 n, v ≠ .inl 0 ∧ (v.isRight = true ∨ n = 0) ∧
    Γ.comps.filter RunOtimes_at = [mkC (.theta []) (.inl 0) v]) ∧
  (∀ c ∈ Γ.comps, ∀ (pq : PQ) (u : Atom 3 n), c.label = some (pq, u) →
    u.isRight = true ∨ (n = 0 ∧ u = .inl 1)) ∧
  (∀ c ∈ Γ.comps, c.minor = [])

private theorem RunOtimes_inv_root {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (h0 : RunOtimes_at c = true) : c.kind = .theta [] := by
  obtain ⟨⟨v, -, -, hr⟩, -, -⟩ := h
  have : c ∈ Γ.comps.filter RunOtimes_at := List.mem_filter.2 ⟨hc, h0⟩
  rw [hr, List.mem_singleton] at this
  rw [this]
  rfl

private theorem RunOtimes_inv_td {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) : RunOtimes_TD Γ := by
  intro c hc h0
  rw [RunOtimes_inv_root h hc (decide_eq_true h0)]
  rfl

/-- A component other than a `Θ` edge has no end at `⊗`. -/
private theorem RunOtimes_inv_not_at {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .theta []) : RunOtimes_at c = false := by
  cases h0 : RunOtimes_at c
  · rfl
  · exact absurd (RunOtimes_inv_root h hc h0) hk

/-- The label and minor clauses of the components of a graph obtained by mapping the atoms. -/
private theorem RunOtimes_LM_of {m : ℕ} {Γ : Graph 3 n} {f : Atom 3 n → Atom 3 m}
    (hf : RunOtimes_AtomOK f) (h0 : n = 0 → m = 0)
    (hL : ∀ c ∈ Γ.comps, ∀ (pq : PQ) (u : Atom 3 n), c.label = some (pq, u) →
      u.isRight = true ∨ (n = 0 ∧ u = .inl 1))
    (hM : ∀ c ∈ Γ.comps, c.minor = []) {L : List (Comp (Atom 3 m))}
    (h : ∀ c' ∈ L, (∃ c ∈ Γ.comps, c'.label = c.label.map (Prod.map id f) ∧
      c'.minor = c.minor.map f) ∨ (c'.label = none ∧ c'.minor = [])) :
    (∀ c ∈ L, ∀ (pq : PQ) (u : Atom 3 m), c.label = some (pq, u) →
      u.isRight = true ∨ (m = 0 ∧ u = .inl 1)) ∧ (∀ c ∈ L, c.minor = []) := by
  refine ⟨fun c' hc' pq u hl => ?_, fun c' hc' => ?_⟩
  · rcases h c' hc' with ⟨c, hcm, hlab, -⟩ | ⟨hlab, -⟩
    · rw [hlab] at hl
      cases hcl : c.label with
      | none => rw [hcl] at hl; cases hl
      | some p =>
        obtain ⟨pq₀, u₀⟩ := p
        rw [hcl] at hl
        simp only [Option.map_some, Prod.map, id, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        rcases hL c hcm pq₀ u₀ hcl with hu | ⟨hn, rfl⟩
        · exact Or.inl (hf.isRight hu)
        · exact Or.inr ⟨h0 hn, hf.plus⟩
    · rw [hlab] at hl
      cases hl
  · rcases h c' hc' with ⟨c, hcm, -, hmin⟩ | ⟨-, hmin⟩
    · rw [hmin, hM c hcm]
      rfl
    · exact hmin

/-- **`O_dot`** keeps the three properties ([II, Def 4.2]). -/
private theorem RunOtimes_inv_oDot {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) :
    ∀ t ∈ oDotT Γ, RunOtimes_Inv t.g := by
  intro t ht
  have hT := RunOtimes_inv_td h
  obtain ⟨hf, h0, hc, hfil⟩ := RunOtimes_oDotT ht
  obtain ⟨⟨v, hv, hvr, hroot⟩, hL, hM⟩ := h
  refine ⟨⟨t.f v, hf.ne0 hv, ?_, ?_⟩, RunOtimes_LM_of hf h0 hL hM hc⟩
  · rcases hvr with hvr | hvr
    · exact Or.inl (hf.isRight hvr)
    · exact Or.inr (h0 hvr)
  · rw [hfil hT, hroot, List.map_singleton, RunOtimes_root_map, hf.1 0]

/-- A graph whose components are components of `Γ`, with the same components at `⊗`, keeps the
three properties. -/
private theorem RunOtimes_inv_sub {Γ Γ' : Graph 3 n} (h : RunOtimes_Inv Γ)
    (hs : ∀ c ∈ Γ'.comps, c ∈ Γ.comps)
    (hf : Γ'.comps.filter RunOtimes_at = Γ.comps.filter RunOtimes_at) : RunOtimes_Inv Γ' := by
  obtain ⟨⟨v, hv, hvr, hroot⟩, hL, hM⟩ := h
  exact ⟨⟨v, hv, hvr, hf.trans hroot⟩, fun c hc => hL c (hs c hc), fun c hc => hM c (hs c hc)⟩

/-- The removal of the component `j` without an end at `⊗` keeps the three properties. -/
private theorem RunOtimes_inv_erase {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) {j : ℕ}
    (hj : j < Γ.comps.length) (hk : Γ.comps[j].kind ≠ .theta []) :
    RunOtimes_Inv ⟨Γ.comps.eraseIdx j, Γ.coeff⟩ := by
  refine RunOtimes_inv_sub h (fun c hc => List.mem_of_mem_eraseIdx hc) ?_
  have hp : RunOtimes_at Γ.comps[j] = false := RunOtimes_inv_not_at h (List.getElem_mem hj) hk
  change (Γ.comps.eraseIdx j).filter RunOtimes_at = Γ.comps.filter RunOtimes_at
  rw [List.eraseIdx_eq_take_drop_succ]
  have h1 : Γ.comps.filter RunOtimes_at =
      (Γ.comps.take j ++ Γ.comps.drop j).filter RunOtimes_at := by rw [List.take_append_drop]
  rw [h1, List.drop_eq_getElem_cons hj, List.filter_append, List.filter_append,
    List.filter_cons_of_neg (by simp [hp])]

/-- **The removal of a redundant dotted edge** keeps the three properties. -/
private theorem RunOtimes_inv_dropDot {Γ Γ' : Graph 3 n} (h : RunOtimes_Inv Γ)
    (hd : DotNormStep Γ Γ') : RunOtimes_Inv Γ' := by
  obtain ⟨i, c, hc, hk, -, rfl⟩ := hd
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hc
  exact RunOtimes_inv_erase h hi (by rw [e, hk]; simp)

/-- **A reordering** ([II, Strategy 6.6]: a permutation of the internal atoms, of the components,
and of the two atoms of waved `s`, dotted and `×`-dotted edges) keeps the three properties: the
`Θ` edge at `⊗` keeps its orientation. -/
private theorem RunOtimes_inv_reorder {Γ Γ' : Graph 3 n} (h : RunOtimes_Inv Γ)
    (hr : Γ.Reorder Γ') : RunOtimes_Inv Γ' := by
  obtain ⟨-, π, cs, h2, hp⟩ := hr
  set σ : Atom 3 n → Atom 3 n := Sum.map id π with hσ
  have hf : RunOtimes_AtomOK σ := ⟨fun _ => rfl, fun _ => rfl⟩
  have hrel : (Γ.relabel π).comps = Γ.comps.map (Comp.map σ) := rfl
  have hInv' : RunOtimes_Inv (Γ.relabel π) := by
    obtain ⟨⟨v, hv, hvr, hroot⟩, hL, hM⟩ := h
    refine ⟨⟨σ v, hf.ne0 hv, ?_, ?_⟩, RunOtimes_LM_of hf id hL hM fun c' hc' => ?_⟩
    · rcases hvr with hvr | hvr
      · exact Or.inl (hf.isRight hvr)
      · exact Or.inr hvr
    · rw [hrel, RunOtimes_filter_map hf, hroot, List.map_singleton, RunOtimes_root_map, hf.1 0]
    · rw [hrel] at hc'
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      exact Or.inl ⟨c, hc, rfl, rfl⟩
  -- the swaps keep the components at `⊗`
  have key : ∀ (l l' : List (Comp (Atom 3 n))), List.Forall₂ (fun c c' => c' = c ∨
      ((c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) ∧
        c' = { c with x := c.y, y := c.x })) l l' →
      (∀ c ∈ l, RunOtimes_at c = true → c.kind = .theta []) →
      l'.filter RunOtimes_at = l.filter RunOtimes_at ∧
      ∀ c' ∈ l', ∃ c ∈ l, c'.label = c.label ∧ c'.minor = c.minor := by
    intro l l' hl
    induction hl with
    | nil => exact fun _ => ⟨rfl, fun _ h => by simp at h⟩
    | @cons c c' l l' hcc _ ih =>
      intro hth
      obtain ⟨ih1, ih2⟩ := ih fun d hd => hth d (List.mem_cons_of_mem _ hd)
      refine ⟨?_, fun d hd => ?_⟩
      · rcases hcc with rfl | ⟨hk, rfl⟩
        · rw [List.filter_cons, List.filter_cons, ih1]
        · have hc0 : RunOtimes_at c = false := by
            cases h0 : RunOtimes_at c
            · rfl
            · have := hth c List.mem_cons_self h0
              rcases hk with hk | hk | hk <;> rw [hk] at this <;> cases this
          have hc0' : RunOtimes_at { c with x := c.y, y := c.x } = false := by
            simp only [RunOtimes_at, decide_eq_false_iff_not] at hc0 ⊢
            tauto
          rw [List.filter_cons_of_neg (by simp [hc0']), List.filter_cons_of_neg (by simp [hc0]),
            ih1]
      · rcases List.mem_cons.1 hd with rfl | hd
        · rcases hcc with rfl | ⟨-, rfl⟩
          · exact ⟨d, List.mem_cons_self, rfl, rfl⟩
          · exact ⟨c, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨e, he, h1, h2⟩ := ih2 d hd
          exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩
  obtain ⟨k1, k2⟩ := key _ _ h2 fun c hc h0 => RunOtimes_inv_root hInv' hc h0
  obtain ⟨⟨v, hv, hvr, hroot⟩, hL, hM⟩ := hInv'
  refine ⟨⟨v, hv, hvr, ?_⟩, fun c hc => ?_, fun c hc => ?_⟩
  · exact List.perm_singleton.1 ((hp.filter _).symm.trans (by rw [k1, hroot]))
  · obtain ⟨e, he, h1, -⟩ := k2 c (hp.symm.subset hc)
    rw [h1]
    exact hL e he
  · obtain ⟨e, he, -, h2⟩ := k2 c (hp.symm.subset hc)
    rw [h2]
    exact hM e he

/-- **Step 1** ([II, Strategy 6.6]): a term of a local expansion at an internal atom that is plain
with internal label atoms keeps the three properties. -/
private theorem RunOtimes_inv_loc {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) (x : Fin n) (o : Fin 5)
    (hs : Γ.LocSide o (.inr x)) {t : Tracked 3 n}
    (ht : t ∈ localOp' o (.inr x) Γ) (hP : t.g.Plain) (hLI : t.g.LabelsInt) :
    RunOtimes_Inv t.g := by
  have hT := RunOtimes_inv_td h
  obtain ⟨hf1, hf2, hperm⟩ := RunOtimes_localOp_otimes x o hs t ht
  have hf : RunOtimes_AtomOK t.f := ⟨hf1, hf2⟩
  obtain ⟨⟨v, hv, hvr, hroot⟩, -, -⟩ := h
  have hvr : v.isRight = true := hvr.resolve_right fun h0 => by have := x.2; omega
  have hsf : RunOtimes_sf Γ.comps = [mkC (.theta []) (.inl 0) v] := by
    rw [RunOtimes_sf_eq, hroot]
    rfl
  have hsf' : RunOtimes_sf t.g.comps = [mkC (.theta []) (.inl 0) (t.f v)] := by
    have := hperm hT
    change (RunOtimes_sf t.g.comps).Perm ((RunOtimes_sf Γ.comps).map (Comp.map t.f)) at this
    rw [hsf, List.map_singleton, RunOtimes_root_map, hf.1 0] at this
    exact List.perm_singleton.1 this
  rw [RunOtimes_sf_eq, List.map_eq_singleton_iff] at hsf'
  obtain ⟨c, hc, hcs⟩ := hsf'
  have hcm : c ∈ t.g.comps := (List.mem_filter.1 (hc ▸ List.mem_singleton_self c)).1
  have hk : c.kind = .theta [] := congrArg Comp.kind hcs
  have hl : c.label = none := by
    have hwf := ((hP c hcm).2.2.2.2).2
    cases hcl : c.label with
    | none => rfl
    | some p =>
      have := hwf (by rw [hcl]; rfl)
      rw [hk] at this
      cases this
  have hce : c = mkC (.theta []) (.inl 0) (t.f v) := by
    rw [← hcs]
    obtain ⟨κ, a, b, mi, lab⟩ := c
    simp only at hl
    subst hl
    rfl
  refine ⟨⟨t.f v, hf.ne0 hv, Or.inl (hf.isRight hvr), by rw [hc, hce]⟩,
    fun c hc pq u hl => Or.inl ?_, fun c hc => (hP c hc).1⟩
  have := hLI c hc
  rw [hl] at this
  simpa using this


/-- A component `×`-duplicated from the graph, without an end at `⊗`, keeps the three
properties. -/
private theorem RunOtimes_inv_dup {Γ : Graph 3 n} (h : RunOtimes_Inv Γ) {i : ℕ}
    (hi : i < Γ.comps.length) (hk : Γ.comps[i].kind ≠ .theta []) :
    RunOtimes_Inv ⟨Γ.comps ++ (Γ.comps[i]?).toList, Γ.coeff⟩ := by
  rw [List.getElem?_eq_getElem hi]
  refine RunOtimes_inv_sub h (fun c hc => ?_) ?_
  · rcases List.mem_append.1 hc with hc | hc
    · exact hc
    · rw [List.mem_singleton.1 hc]
      exact List.getElem_mem hi
  · have hp : RunOtimes_at Γ.comps[i] = false := RunOtimes_inv_not_at h (List.getElem_mem hi) hk
    change (Γ.comps ++ [Γ.comps[i]]).filter RunOtimes_at = Γ.comps.filter RunOtimes_at
    rw [List.filter_append, List.filter_cons_of_neg (by simp [hp]), List.filter_nil,
      List.append_nil]

/-- The image of an atom of a substituted graph is internal when `x`, `y₁`, `y₂` are. -/
private theorem RunOtimes_glueAtom_int {m n' : ℕ} {x y₁ y₂ : Atom 3 m} (hx : x.isRight = true)
    (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true) (u : Atom 3 n') :
    (glueAtom x y₁ y₂ u : Atom 3 (m + n')).isRight = true := by
  have hl : ∀ w : Atom 3 m, w.isRight = true → (liftA n' w : Atom 3 (m + n')).isRight = true :=
    fun w hw => (RunOtimes_atomOK_liftA n').isRight hw
  cases u with
  | inl i =>
    match i with
    | 0 => exact hl x hx
    | 1 => exact hl y₁ hy₁
    | 2 => exact hl y₂ hy₂
  | inr j => rfl

/-- **The substitution of Steps 2–3** ([II, (4.14)–(4.15)]) at internal atoms `x`, `y₁`, `y₂` of a
graph `H` without labels: if `H.glue x y₁ y₂ (tVar true)` has the three properties, so has
`H.glue x y₁ y₂ 𝒢` for every graph `𝒢` without minor; its component at `⊗` is that of `H`. -/
private theorem RunOtimes_inv_glue {m n' : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    (hx : x.isRight = true) (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (hH : H.LabelFree) (h : RunOtimes_Inv (H.glue x y₁ y₂ (tVar true)))
    {𝒢 : Graph 3 n'} (hM : ∀ c ∈ 𝒢.comps, c.minor = []) :
    RunOtimes_Inv (H.glue x y₁ y₂ 𝒢) := by
  have hglue : ∀ {l : ℕ} (𝒢 : Graph 3 l), (H.glue x y₁ y₂ 𝒢).comps.filter RunOtimes_at =
      (H.comps.filter RunOtimes_at).map (Comp.map (liftA l)) := by
    intro l 𝒢
    change (liftCs l H.comps ++ 𝒢.comps.map (Comp.map (glueAtom x y₁ y₂))).filter RunOtimes_at = _
    have hz : (𝒢.comps.map (Comp.map (glueAtom x y₁ y₂))).filter RunOtimes_at = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc h0
      obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 hc
      have h0 : glueAtom x y₁ y₂ c₀.x = (.inl 0 : Atom 3 (m + l)) ∨
          glueAtom x y₁ y₂ c₀.y = (.inl 0 : Atom 3 (m + l)) := of_decide_eq_true h0
      rcases h0 with h0 | h0
      · have := RunOtimes_glueAtom_int (n' := l) hx hy₁ hy₂ c₀.x
        rw [h0] at this
        simp at this
      · have := RunOtimes_glueAtom_int (n' := l) hx hy₁ hy₂ c₀.y
        rw [h0] at this
        simp at this
    rw [List.filter_append, hz, List.append_nil]
    exact RunOtimes_filter_map (RunOtimes_atomOK_liftA l) H.comps
  obtain ⟨⟨v, hv, hvr, hroot⟩, -, hM₀⟩ := h
  rw [hglue, List.map_eq_singleton_iff] at hroot
  obtain ⟨c₀, hc₀, hce⟩ := hroot
  obtain ⟨κ, a, b, mi, lab⟩ := c₀
  simp only [Comp.map, mkC, Comp.mk.injEq] at hce
  obtain ⟨rfl, ha, hb, hmi, hlab⟩ := hce
  have ha' : a = .inl 0 := ((RunOtimes_atomOK_liftA 1).eq0 a).1 ha
  have hmi' : mi = [] := List.map_eq_nil_iff.1 hmi
  have hlab' : lab = none := Option.map_eq_none_iff.1 hlab
  subst ha' hmi' hlab'
  have hvr' : v.isRight = true := hvr.resolve_right (by omega)
  have hb' : b.isRight = true := by
    rw [← hb] at hvr'
    cases b with
    | inl _ => simp [liftA] at hvr'
    | inr _ => rfl
  have hbne : b ≠ .inl 0 := by
    rintro rfl
    simp at hb'
  refine ⟨⟨liftA n' b, (RunOtimes_atomOK_liftA n').ne0 hbne,
    Or.inl ((RunOtimes_atomOK_liftA n').isRight hb'), ?_⟩, ?_, ?_⟩
  · rw [hglue, hc₀]
    rfl
  · intro c hc pq u hl
    left
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c₁, hc₁, rfl⟩ := Local_mem_liftCs.1 hc
      have hl' : c₁.label.map (Prod.map id (liftA n')) = some (pq, u) := hl
      rw [hH c₁ hc₁] at hl'
      cases hl'
    · obtain ⟨c₁, -, rfl⟩ := List.mem_map.1 hc
      have hl' : c₁.label.map (Prod.map id (glueAtom x y₁ y₂)) = some (pq, u) := hl
      cases hcl : c₁.label with
      | none => rw [hcl] at hl'; cases hl'
      | some p =>
        obtain ⟨pq₀, u₀⟩ := p
        rw [hcl] at hl'
        simp only [Option.map_some, Prod.map, id, Option.some.injEq, Prod.mk.injEq] at hl'
        rw [← hl'.2]
        exact RunOtimes_glueAtom_int hx hy₁ hy₂ u₀
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c₁, hc₁, rfl⟩ := Local_mem_liftCs.1 hc
      have h1 := hM₀ (c₁.map (liftA 1))
        (List.mem_append_left _ (Local_mem_liftCs.2 ⟨c₁, hc₁, rfl⟩))
      have h2 : c₁.minor = [] := List.map_eq_nil_iff.1 h1
      change c₁.minor.map _ = []
      rw [h2]
      rfl
    · obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hc
      change c₁.minor.map _ = []
      rw [hM c₁ hc₁]
      rfl

/-- The graphs of `R`, `A`, `Q`, `Err` of a `T`-expansion have no minor ([II, Def 3.2 (2), (8)]:
the kinds `Graph.TKinds`, `Graph.TKindsErr`). -/
private theorem RunOtimes_minor_of_struct {Sig : ℕ → Expansion 2} {N D : ℕ} {𝒯 : TRec}
    (hT : 𝒯.IsTExpStruct Sig N D) :
    ∀ g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err, ∀ c ∈ g.2.comps, c.minor = [] := by
  obtain ⟨-, -, -, ⟨⟨h1, h2⟩, -⟩, -⟩ := hT
  intro g hg c hc
  rcases List.mem_append.1 hg with hg | hg
  · have := List.all_eq_true.1 (h1 g hg).2.1 c hc
    unfold Comp.isTKind at this
    simp only [Bool.and_eq_true, List.isEmpty_iff] at this
    exact this.1
  · have := List.all_eq_true.1 (h2 g hg).2.1 c hc
    unfold Comp.isTKind at this
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at this
    rcases this with h | h
    · exact h.1
    · exact h.1

/-- The graphs of the right side of [II, (4.15)] substituted in Steps 2–3 have no minor. -/
private theorem RunOtimes_tSubst_minor {Sig : ℕ → Expansion 2} {N D : ℕ} {𝒯 : TRec}
    (hT : 𝒯.IsTExpStruct Sig N D) :
    ∀ g ∈ (𝒯.tSubst N).swapSolid, ∀ c ∈ g.2.comps, c.minor = [] := by
  intro g hg c hc
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  have hm : c₀.minor = [] := by
    simp only [TRec.tSubst, TRec.rhs, List.mem_append] at hg₀
    rcases hg₀ with (((((h | h) | h) | h) | h) | h) | h
    · exact ((leadSigmaCorr_plain N g₀ (by simp [h])) c₀ hc₀).1
    · exact ((leadSigmaCorr_plain N g₀ (by simp [h])) c₀ hc₀).1
    · exact RunOtimes_minor_of_struct hT g₀ (by simp [h]) c₀ hc₀
    · exact RunOtimes_minor_of_struct hT g₀ (by simp [h]) c₀ hc₀
    · exact RunOtimes_minor_of_struct hT g₀ (by simp [h]) c₀ hc₀
    · exact RunOtimes_minor_of_struct hT g₀ (by simp [h]) c₀ hc₀
    · exact ((leadSigmaCorr_plain N g₀ (by simp [h])) c₀ hc₀).1
  unfold Comp.swapSolid
  split_ifs <;> exact hm

/-- **A `Q`-expansion of Step 3** ([II, Lemma 4.15]) at an internal label atom of a graph with the
invariant `Graph.InvB'` that is not a `Q`-graph keeps the three properties: by the clause on `⊗`
the component at `⊗` of an output graph is the image of `Θ_{⊗v}`, and by (F6) the internal atom
`v` goes to an internal atom, so that `⊗` is fixed. -/
private theorem RunOtimes_inv_qexp {D n₀ : ℕ}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    {Γ : Graph 3 n₀} {x : Fin n₀} (h : RunOtimes_Inv Γ) (hN : ∃ C, Γ.Normal C) (hP : Γ.Plain)
    (hform : Γ.IsQFormAt (.inr x)) (hnQ : ¬ Γ.IsQGraph) (hB : Γ.InvB')
    (hcl : qexpClauseB D x Γ (𝔈 D n₀ x Γ)) : ∀ u ∈ 𝔈 D n₀ x Γ, RunOtimes_Inv u.g := by
  intro u hu
  have hT := RunOtimes_inv_td h
  have hmono := (hF.2.2.2.2.2 D n₀ x Γ hN hform hP hnQ hB u hu).1
  obtain ⟨C', hC'⟩ := hcl.1
  obtain ⟨hout, hot⟩ := hC' u hu
  obtain ⟨⟨v, -, hvr, hroot⟩, -, -⟩ := h
  have hvr : v.isRight = true := hvr.resolve_right fun h0 => by have := x.2; omega
  have hfv : (u.f v).isRight = true := by
    cases v with
    | inl a => simp at hvr
    | inr a => exact hmono.isRight a
  have hfv0 : u.f v ≠ .inl 0 := by
    intro e
    rw [e] at hfv
    simp at hfv
  have hp := hot hT
  change (u.g.comps.filter RunOtimes_at).Perm ((Γ.comps.filter RunOtimes_at).map (Comp.map u.f))
    at hp
  rw [hroot, List.map_singleton, RunOtimes_root_map] at hp
  have he := List.perm_singleton.1 hp
  have hf0 : u.f (.inl 0) = .inl 0 := by
    have hm : mkC (.theta []) (u.f (.inl 0)) (u.f v) ∈ u.g.comps.filter RunOtimes_at := by
      rw [he]
      exact List.mem_singleton_self _
    have h0 : u.f (.inl 0) = .inl 0 ∨ u.f v = .inl 0 := of_decide_eq_true (List.mem_filter.1 hm).2
    exact h0.resolve_right hfv0
  rw [hf0] at he
  refine ⟨⟨u.f v, hfv0, Or.inl hfv, he⟩, fun c hc pq w hl => Or.inl ?_, fun c hc => ?_⟩
  · have := (hcl.2 hB u hu).2.2.2.2 c hc
    rw [hl] at this
    simpa using this
  · rcases hout.2.1 with ⟨hPl, -⟩ | ⟨-, hCl⟩
    · exact (hPl c hc).1
    · exact (hCl c hc).1

end Steps

/-! ## The run of the selector -/

section Run

/-- **One step of the run** of [II, Strategy 6.6] at an admissible location of a graph of the
domain of the selector keeps the three properties. -/
private theorem RunOtimes_inv_step {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {g : Σ n₀ : ℕ, Graph 3 n₀} (h : RunOtimes_Inv g.2)
    (hD : TerminationC_Dom n D g) {l : TerminationC_Loc g.1} (hA : TerminationC_Adm n D 𝔈 g l) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, RunOtimes_Inv s.2 := by
  obtain ⟨n₀, Γ⟩ := g
  intro s hs
  cases l with
  | loc o x =>
    obtain ⟨hS, hDo, ⟨C, hN⟩, hL, hP, hgs, -, hside, hLA, hX⟩ := hA
    have hR : TerminationC_RI n D ⟨n₀, Γ⟩ := hD.resolve_left fun h => h ⟨C, hN⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    obtain ⟨-, -, hst, -⟩ :=
      TerminationB_inv_loc hR.1 hR.2.1 hS hDo hN hL hP hgs hX hLA hside t ht
    obtain ⟨hB, hTD⟩ := TerminationC_invB hR hL hDo
    have hnr : ¬ Γ.IsRecollision {1, 2} := fun hr => hS ⟨⟨C, hN⟩, Or.inl hr⟩
    obtain ⟨-, -, hLI, -⟩ := localOp_clausesB n₀ C x Γ hN hL hP hB hTD hnr o hside t ht
    exact RunOtimes_inv_loc h x o hside ht hst.2.2.2.2.2.1 hLI
  | dot =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact RunOtimes_inv_oDot h t ht
  | dropDot Γ' =>
    rw [List.mem_singleton.1 hs]
    exact RunOtimes_inv_dropDot h hA.1
  | reorder Γ' =>
    rw [List.mem_singleton.1 hs]
    exact RunOtimes_inv_reorder h hA.1
  | xdotDup i =>
    obtain ⟨hi, ⟨hk, -⟩, -⟩ := hA
    have hk' : Γ.comps[i].kind = .xdot := hk
    rw [List.mem_singleton.1 hs]
    exact RunOtimes_inv_dup h hi (by rw [hk']; simp)
  | xdotDrop i j =>
    obtain ⟨hi, hj, ⟨-, hc, hk, -⟩, -⟩ := hA
    have hk' : Γ.comps[i].kind = .xdot := hk
    have hjk : Γ.comps[j].kind = Γ.comps[i].kind := by
      rcases hc with e | e
      · exact congrArg Comp.kind e
      · have := congrArg Comp.kind e
        exact this
    rw [List.mem_singleton.1 hs]
    exact RunOtimes_inv_erase h hj (by rw [hjk, hk']; simp)
  | xdotLoop i => exact absurd hs List.not_mem_nil
  | coeffNorm =>
    rw [List.mem_singleton.1 hs]
    exact RunOtimes_inv_sub h (fun c hc => hc) rfl
  | subst m H x y₁ y₂ =>
    obtain ⟨he, -, -, hprem⟩ := hA
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hprem.2.2.2.2.2.2.2.2
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hs
    exact RunOtimes_inv_glue hx hy₁ hy₂ hprem.2.2.2.1 h (RunOtimes_tSubst_minor hT g' hg')
  | qexp x =>
    obtain ⟨⟨C, hN⟩, hP, hDo, hform, hnQ, -, hcl⟩ := hA
    have hR : TerminationC_RI n D ⟨n₀, Γ⟩ := hD.resolve_left fun h => h ⟨C, hN⟩
    have hB : Γ.InvB' := by
      rcases hR.1 with ⟨hB, -⟩ | ⟨-, hq⟩ | ⟨hlt, -⟩
      · exact hB
      · exact absurd hq hnQ
      · exact absurd (lt_of_lt_of_le hlt (SelRun_paperOrd_le Γ)) hDo
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
    exact RunOtimes_inv_qexp hF h ⟨C, hN⟩ hP hform hnQ hB hcl u hu

/-- **The three properties along the run** of the selector `TerminationC_sel`: from graphs with
the three properties that are outputs or graphs of the run ([II, Lemma 6.8]), every output graph
has them. -/
private theorem RunOtimes_run {n D : ℕ} {Sig : ℕ → Expansion 2} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (hF : QExpFamilyStmt 𝔈)
    (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D) {E F : Expansion 3}
    (hr : SelRunB n D 𝒯 𝔈 TerminationC_sel E F) :
    (∀ g ∈ E, RunOtimes_Inv g.2 ∧
      (TerminationC_Out n D g ∨ ∃ r, TerminationC2_Good n D 𝒯 g r)) →
    ∀ g ∈ F, RunOtimes_Inv g.2 := by
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  have hℓ := TerminationC_sel_adm 𝔈 hF n D 𝒯
  have hkey := TerminationC2_key hH hF (TerminationC2_tSubst_runKinds hH) hℓ
  induction hr with
  | nil =>
    intro _ g hg
    simp at hg
  | out _ _ ih =>
    intro hE g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact (hE _ List.mem_cons_self).1
    · exact ih (fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')) g hg
  | @step g E F hO _ _ ih =>
    intro hE
    obtain ⟨hI, hc⟩ := hE g List.mem_cons_self
    obtain ⟨r, hr⟩ := hc.resolve_left hO
    obtain ⟨hD, hs⟩ := hkey g r hr hO
    have hA := (hℓ g hD hO).1
    refine ih fun s hs' => ?_
    rcases List.mem_append.1 hs' with hs' | hs'
    · refine ⟨RunOtimes_inv_step hF hT hI hD hA s hs', ?_⟩
      rcases hs s hs' with h | ⟨r', -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨r', h⟩
    · exact hE s (List.mem_cons_of_mem _ hs')

set_option maxRecDepth 100000 in
/-- The root atom and the label atoms of the graphs of `A` and `Q` of the second order
`T`-expansion. -/
private theorem RunOtimes_h2_facts : ∀ g ∈ h2Rec.A ++ h2Rec.Q,
    (g.1 = 0 ∨ g.2.comps.all (fun c => !(c.x == .inl 0) || c.y.isRight) = true) ∧
    g.2.comps.all (fun c => c.label.all (fun l => l.2.isRight || (g.1 == 0 && l.2 == .inl 1))) =
      true := by
  decide +kernel

/-- The graphs of `A` and `Q` of the second order `T`-expansion, the inputs of the run, have the
three properties. -/
private theorem RunOtimes_inputs : ∀ g ∈ h2Rec.A ++ h2Rec.Q, RunOtimes_Inv g.2 := by
  intro g hg
  obtain ⟨j, v, hv, h1, h2, h3, ⟨h4, h5⟩, h6, -⟩ := h2Rec_root g hg
  obtain ⟨hr, hl⟩ := RunOtimes_h2_facts g hg
  have hroot := RunOtimes_of_fields j v h1 h2 h3 h4 h5 fun c hc => ⟨(h6 c hc).1, (h6 c hc).2.1⟩
  have hmin : ∀ c ∈ g.2.comps, c.minor = [] := by
    have hS := (h2Rec_struct (fun _ => []) 3 (by norm_num))
    exact RunOtimes_minor_of_struct hS g (by
      rcases List.mem_append.1 hg with h | h <;> simp [h])
  refine ⟨⟨v, hv, ?_, hroot⟩, fun c hc pq u hlab => ?_, hmin⟩
  · rcases hr with hr | hr
    · exact Or.inr hr
    · left
      have := List.all_eq_true.1 hr _ (List.getElem_mem j.2)
      have h4' : g.2.comps[(j : ℕ)].x = .inl 0 := h4
      have h5' : g.2.comps[(j : ℕ)].y = v := h5
      rw [h4', h5'] at this
      simpa using this
  · have := List.all_eq_true.1 hl c hc
    rw [hlab] at this
    simp only [Option.all_some, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    exact this

end Run

/-! ## [II, Def 3.3 (4)] on the output graphs of the run -/

/-- **[II, Def 3.3 (4)] on the output graphs of the run of the selector** ([II, Strategy 6.6],
[II, Lemma 6.8]): for a family `𝔈` of `Q`-expansions of [II, Lemma 4.15] (`QExpFamilyStmt`), a
cutoff order `n ≥ 3` and an `(n - 1)`-th order `T`-expansion `𝒯` with error order `D`, every output
graph of the run driven by `TerminationC_sel` from the graphs of `A` and `Q` of the second order
`T`-expansion has
* exactly one component with an end at `⊗`: a plain `Θ` edge from `⊗` to an atom `v ≠ ⊗`, without
  minor and without label (the field form of `Graph.ThetaRooted`);
* every label atom internal, or no internal atom and the label atom `⊕`;
* no minor. -/
theorem RunOtimes.selRun_otimes :
    ∀ 𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀, QExpFamilyStmt 𝔈 →
    ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n → 𝒯.IsTExpStruct Sig (n - 1) D →
    ∀ F : Expansion 3, SelRunB n D 𝒯 𝔈 TerminationC_sel (h2Rec.A ++ h2Rec.Q) F →
    ∀ g ∈ F,
      (∃ (j : Fin g.2.comps.length) (v : Atom 3 g.1), v ≠ .inl 0 ∧
        g.2.comps[j].kind = .theta [] ∧ g.2.comps[j].minor = [] ∧ g.2.comps[j].label = none ∧
        (g.2.comps[j].x = .inl 0 ∧ g.2.comps[j].y = v) ∧
        ∀ c ∈ (g.2.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0) ∧
      (∀ c ∈ g.2.comps, ∀ (pq : PQ) (u : Atom 3 g.1), c.label = some (pq, u) →
        u.isRight = true ∨ (g.1 = 0 ∧ u = .inl 1)) ∧
      (∀ c ∈ g.2.comps, c.minor = []) := by
  intro 𝔈 hF n D Sig 𝒯 hn hT F hr g hg
  have hH : TerminationC2_Hyp n D Sig 𝒯 := ⟨hn, hT⟩
  obtain ⟨⟨v, hv, -, hroot⟩, hL, hM⟩ := RunOtimes_run hF hn hT hr
    (fun g hg => ⟨RunOtimes_inputs g hg, TerminationC2_inputs hH g hg⟩) g hg
  exact ⟨RunOtimes_fields hv hroot, hL, hM⟩


/-! ## The graphs of `Q` of the second order `T`-expansion -/

section Instances

/-- The graphs of `Q` with an internal atom of the second order `T`-expansion are outputs of the
run at every cutoff order and every error order `D > 2`. -/
private theorem RunOtimes_q_out {n D : ℕ} (hD : 2 < D) {g : Σ n₀ : ℕ, Graph 3 n₀}
    (hg : g ∈ h2Rec.Q) (h1 : g.1 ≠ 0) : TerminationC_Out n D g := by
  have hS := h2Rec_struct (fun _ => []) D hD
  have hSh := hS.2.2.2.1
  have hDef := hS.2.2.2.2
  have hRAQ : g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q := List.mem_append_right _ hg
  obtain ⟨hN, -, -, hdc⟩ := hSh.1.1 g hRAQ
  obtain ⟨hTD, hX, hNL, hlab⟩ := RunCompare_def63_leaf hDef g (List.mem_append_left _ hRAQ)
  have hq := (hSh.2.2.2.1 g hg).1
  obtain ⟨hspd, hql, hcase⟩ := RunCompare_def63_Q hDef g hg
  have hEC : g.2.ExtClause ∧ g.2.ColourInvB := by
    rcases hcase with ⟨h0, -⟩ | h
    · exact absurd h0 h1
    · exact h
  refine ⟨⟨hX, Or.inl ⟨hN, Or.inr (Or.inr (Or.inl hq))⟩⟩, hdc, hN, ⟨hTD, hX, hNL, hlab⟩,
    fun _ => TRec.plain_of_def63 hDef g hRAQ, Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hq, hspd, hql,
      RunCompare_def63_pmQ hDef g hg, RunCompare_def63_rg hDef g (List.mem_append_left _ hg)⟩,
      fun _ => hEC, fun h0 => absurd h0 h1⟩)))⟩

end Instances

end RBM8D.Graphs
