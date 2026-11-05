import RBM8D.GlobalExp.TerminationC

/-!
# The component kinds along a run of [II, Strategy 6.6]

The kinds of the components that occur in a run of [II, Strategy 6.6]: the kinds of
[II, Def 3.2 (2)] together with the minors `G^{(T)}` and the weights `(G_{xx})⁻¹` and `W_D` of
[II, §4.4] (`Comp.isRunKind`, `Graph.RunKinds`).

* On a graph without minors and without `(G_{xx})⁻¹` and `W_D` weights (`Graph.Plain`) these are
  the kinds of [II, Def 3.2] (`Graph.RunKinds.tKinds`).
* Every step of a run (`TerminationC_Adm`, with the output `TerminationC_stepOut`) keeps them,
  when the substituted formal sum of Steps 2–3 has them (`TerminationK_step`): the local
  expansions of [II, Defs 4.3–4.6], `O_dot` and `O_merge` ([II, Defs 4.1, 4.2]), the elementary
  steps of the `Q`-expansions of [II, §4.4], the substitution [II, (4.15)], the removal of a
  dotted edge, the reorderings, and the steps on `×`-dotted edges and on the coefficient create no
  `Θ` edge, no `Θ^{(n)}_err` edge, no ghost edge and no auxiliary edge.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The component kinds that occur in a run of [II, Strategy 6.6]: solid edges, regular and light
weights, `(G_{xx})⁻¹` and `W_D` weights, waved edges, `Θ` edges whose labels have entries even in
`[4, N]`, dotted and `×`-dotted edges; minors and labels are allowed. -/
def Comp.isRunKind {V : Type*} (N : ℕ) (c : Comp V) : Bool :=
  match c.kind with
  | .G _ | .weight _ | .light _ | .inv _ | .wD _ _ | .waved _ | .dot | .xdot => true
  | .theta o => labelOK N o
  | _ => false

/-- Every component of `Γ` has a run kind (`Comp.isRunKind`). -/
def Graph.RunKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) : Prop :=
  Γ.comps.all (Comp.isRunKind N) = true

/-- `RunKinds` together with `Plain` gives the kinds of [II, Def 3.2]. -/
theorem Graph.RunKinds.tKinds {k n N : ℕ} {Γ : Graph k n} (hK : Γ.RunKinds N) (hP : Γ.Plain) :
    Γ.TKinds N := by
  unfold Graph.TKinds
  rw [List.all_eq_true]
  intro c hc
  have h1 := List.all_eq_true.1 hK c hc
  obtain ⟨hm, hi, hw, -, -⟩ := hP c hc
  unfold Comp.isTKind
  unfold Comp.isRunKind at h1
  rw [hm]
  cases h : c.kind with
  | inv ch => exact absurd h (hi ch)
  | wD ch d => exact absurd h (hw ch d)
  | _ => simp_all

/-! ## The run kinds on lists of components -/

/-- The run kinds, read on the kind alone. -/
private def TerminationK_kok (N : ℕ) : Kind → Bool
  | .G _ | .weight _ | .light _ | .inv _ | .wD _ _ | .waved _ | .dot | .xdot => true
  | .theta o => labelOK N o
  | _ => false

private theorem TerminationK_isRunKind_eq {V : Type*} (N : ℕ) (c : Comp V) :
    c.isRunKind N = TerminationK_kok N c.kind := by
  unfold Comp.isRunKind TerminationK_kok
  cases c.kind <;> rfl

/-- Every component of the list has a run kind. -/
private def TerminationK_ok {V : Type*} (N : ℕ) (L : List (Comp V)) : Prop :=
  ∀ c ∈ L, TerminationK_kok N c.kind = true

private theorem TerminationK_runKinds_iff {k n N : ℕ} (Γ : Graph k n) :
    Γ.RunKinds N ↔ TerminationK_ok N Γ.comps := by
  unfold Graph.RunKinds TerminationK_ok
  simp only [List.all_eq_true, TerminationK_isRunKind_eq]

private theorem TerminationK_kok_conj (N : ℕ) (κ : Kind) :
    TerminationK_kok N κ.conj = TerminationK_kok N κ := by
  cases κ with
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem TerminationK_kok_toWeight (N : ℕ) (κ : Kind) :
    TerminationK_kok N κ.toWeight = TerminationK_kok N κ := by
  cases κ <;> rfl

section Lists

variable {V W : Type*} {N : ℕ}

@[simp] private theorem TerminationK_ok_nil : TerminationK_ok N ([] : List (Comp V)) := by
  simp [TerminationK_ok]

@[simp] private theorem TerminationK_ok_cons {c : Comp V} {L : List (Comp V)} :
    TerminationK_ok N (c :: L) ↔ TerminationK_kok N c.kind = true ∧ TerminationK_ok N L := by
  simp [TerminationK_ok]

@[simp] private theorem TerminationK_ok_append {L L' : List (Comp V)} :
    TerminationK_ok N (L ++ L') ↔ TerminationK_ok N L ∧ TerminationK_ok N L' := by
  simp [TerminationK_ok, or_imp, forall_and]

private theorem TerminationK_ok_map {L : List (Comp V)} (g : Comp V → Comp W)
    (hg : ∀ c ∈ L, TerminationK_kok N (g c).kind = TerminationK_kok N c.kind) :
    TerminationK_ok N (L.map g) ↔ TerminationK_ok N L := by
  simp only [TerminationK_ok, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun c hc => by rw [hg c hc]

@[simp] private theorem TerminationK_ok_mapComp {L : List (Comp V)} (f : V → W) :
    TerminationK_ok N (L.map (Comp.map f)) ↔ TerminationK_ok N L :=
  TerminationK_ok_map _ fun _ _ => rfl

private theorem TerminationK_ok_sub {L L' : List (Comp V)} (h : ∀ c ∈ L', c ∈ L)
    (hL : TerminationK_ok N L) : TerminationK_ok N L' :=
  fun c hc => hL c (h c hc)

private theorem TerminationK_ok_eraseIdx {L : List (Comp V)} (hL : TerminationK_ok N L) (i : ℕ) :
    TerminationK_ok N (L.eraseIdx i) :=
  TerminationK_ok_sub (fun _ hc => List.mem_of_mem_eraseIdx hc) hL

private theorem TerminationK_ok_filter {L : List (Comp V)} (hL : TerminationK_ok N L)
    (p : Comp V → Bool) : TerminationK_ok N (L.filter p) :=
  TerminationK_ok_sub (fun _ hc => List.mem_of_mem_filter hc) hL

end Lists

section Ops

variable {N : ℕ}

@[simp] private theorem TerminationK_ok_liftCs {k n : ℕ} (j : ℕ) (L : List (Comp (Atom k n))) :
    TerminationK_ok N (liftCs j L) ↔ TerminationK_ok N L := by
  unfold liftCs
  exact TerminationK_ok_mapComp _

@[simp] private theorem TerminationK_ok_labelQs {V : Type*} (u : V) (L : List (Comp V)) :
    TerminationK_ok N (labelQs u L) ↔ TerminationK_ok N L :=
  TerminationK_ok_map _ fun c _ => by unfold Comp.labelQ; split <;> rfl

private theorem TerminationK_ok_eraseIdxs {V : Type*} {L : List (Comp V)}
    (hL : TerminationK_ok N L) (is : List ℕ) : TerminationK_ok N (eraseIdxs is L) := by
  refine TerminationK_ok_sub (fun c hc => ?_) hL
  unfold eraseIdxs at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact List.fst_mem_of_mem_zipIdx (List.mem_of_mem_filter hp)

private theorem TerminationK_ok_pickIdxs {V : Type*} {L : List (Comp V)}
    (hL : TerminationK_ok N L) (is : List ℕ) : TerminationK_ok N (pickIdxs is L) := by
  refine TerminationK_ok_sub (fun c hc => ?_) hL
  unfold pickIdxs at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact List.fst_mem_of_mem_zipIdx (List.mem_of_mem_filter hp)

@[simp] private theorem TerminationK_kok_solidC {V : Type*} [DecidableEq V] (ch : Charge)
    (u v : V) : TerminationK_kok N (solidC ch u v).kind = true := by
  unfold solidC; split <;> rfl

@[simp] private theorem TerminationK_kok_G (c : Charge) : TerminationK_kok N (.G c) = true := rfl
@[simp] private theorem TerminationK_kok_weight (c : Charge) :
    TerminationK_kok N (.weight c) = true := rfl
@[simp] private theorem TerminationK_kok_light (c : Charge) :
    TerminationK_kok N (.light c) = true := rfl
@[simp] private theorem TerminationK_kok_inv (c : Charge) : TerminationK_kok N (.inv c) = true :=
  rfl
@[simp] private theorem TerminationK_kok_wD (c : Charge) (d : ℕ) :
    TerminationK_kok N (.wD c d) = true := rfl
@[simp] private theorem TerminationK_kok_waved (w : Wave) :
    TerminationK_kok N (.waved w) = true := rfl
@[simp] private theorem TerminationK_kok_dot : TerminationK_kok N .dot = true := rfl
@[simp] private theorem TerminationK_kok_xdot : TerminationK_kok N .xdot = true := rfl

@[simp] private theorem TerminationK_kok_ite (c : Prop) [Decidable c] (κ κ' : Kind) :
    TerminationK_kok N (if c then κ else κ') = if c then TerminationK_kok N κ else
      TerminationK_kok N κ' :=
  apply_ite _ _ _ _

@[simp] private theorem TerminationK_kok_mkC {V : Type*} (κ : Kind) (u v : V) :
    (mkC κ u v).kind = κ := rfl

private theorem TerminationK_ok_dTerms {V : Type*} [DecidableEq V] {p q : V}
    {L : List (Comp V)} {d : List (Comp V)} (hd : d ∈ dTerms p q L) (hL : TerminationK_ok N L) :
    TerminationK_ok N d := by
  unfold dTerms at hd
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hd
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hi
  refine TerminationK_ok_append.2 ⟨TerminationK_ok_eraseIdx hL _, ?_⟩
  generalize L[i] = c at hps
  obtain ⟨κ, a, b, m, l⟩ := c
  cases κ <;> (try rename_i ch; cases ch) <;>
    simp only [Comp.dPieces, Option.some.injEq, reduceCtorEq] at hps <;> subst hps <;>
    simp only [TerminationK_ok_cons, TerminationK_ok_nil, TerminationK_kok_solidC, and_self]

@[simp] private theorem TerminationK_ok_replicate {V : Type*} (j : ℕ) (c : Comp V) :
    TerminationK_ok N (List.replicate j c) ↔ (j ≠ 0 → TerminationK_kok N c.kind = true) := by
  simp only [TerminationK_ok, List.mem_replicate, and_imp]
  exact ⟨fun h hj => h c hj rfl, fun h _ hj e => e ▸ h hj⟩

private theorem TerminationK_forall_dTerms {V : Type*} [DecidableEq V] {p q : V}
    {L : List (Comp V)} (hL : TerminationK_ok N L) :
    (∀ d ∈ dTerms p q L, TerminationK_ok N d) = True :=
  eq_true fun _ hd => TerminationK_ok_dTerms hd hL

@[simp] private theorem TerminationK_ok_conj {k n : ℕ} (Γ : Graph k n) :
    TerminationK_ok N Γ.conj.comps ↔ TerminationK_ok N Γ.comps :=
  TerminationK_ok_map _ fun c _ => TerminationK_kok_conj N c.kind

@[simp] private theorem TerminationK_ok_swapSolid {k n : ℕ} (Γ : Graph k n) :
    TerminationK_ok N Γ.swapSolid.comps ↔ TerminationK_ok N Γ.comps :=
  TerminationK_ok_map _ fun c _ => by unfold Comp.swapSolid; split <;> rfl

@[simp] private theorem TerminationK_ok_dropLabels {k n : ℕ} (Γ : Graph k n) :
    TerminationK_ok N Γ.dropLabels.comps ↔ TerminationK_ok N Γ.comps :=
  TerminationK_ok_map _ fun _ _ => rfl

/-- Every graph of the tracked formal sum has run kinds only. -/
private def TerminationK_okE {k n : ℕ} (N : ℕ) (E : TExpansion k n) : Prop :=
  ∀ t ∈ E, TerminationK_ok N t.g.comps

section OkE

variable {k n : ℕ}

@[simp] private theorem TerminationK_okE_nil : TerminationK_okE N ([] : TExpansion k n) := by
  simp [TerminationK_okE]

@[simp] private theorem TerminationK_okE_cons {t : Tracked k n} {E : TExpansion k n} :
    TerminationK_okE N (t :: E) ↔ TerminationK_ok N t.g.comps ∧ TerminationK_okE N E := by
  simp [TerminationK_okE]

@[simp] private theorem TerminationK_okE_append {E E' : TExpansion k n} :
    TerminationK_okE N (E ++ E') ↔ TerminationK_okE N E ∧ TerminationK_okE N E' := by
  simp [TerminationK_okE, or_imp, forall_and]

@[simp] private theorem TerminationK_okE_map {α : Type*} {L : List α} {g : α → Tracked k n} :
    TerminationK_okE N (L.map g) ↔ ∀ a ∈ L, TerminationK_ok N (g a).g.comps := by
  simp [TerminationK_okE]

@[simp] private theorem TerminationK_okE_ite {c : Prop} [Decidable c] {E E' : TExpansion k n} :
    TerminationK_okE N (if c then E else E') ↔ (c → TerminationK_okE N E) ∧
      (¬ c → TerminationK_okE N E') := by
  split_ifs with h <;> simp [h]

@[simp high] private theorem TerminationK_okE_self {Γ : Graph k n} :
    TerminationK_okE N [Tracked.self Γ] ↔ TerminationK_ok N Γ.comps :=
  ⟨fun h => h _ (List.mem_singleton_self _), fun h t ht => by
    rw [List.mem_singleton.1 ht]; exact h⟩

@[simp high] private theorem TerminationK_okE_self_cons {Γ : Graph k n} {E : TExpansion k n} :
    TerminationK_okE N (Tracked.self Γ :: E) ↔ TerminationK_ok N Γ.comps ∧ TerminationK_okE N E :=
  TerminationK_okE_cons

@[simp] private theorem TerminationK_okE_conj {E : TExpansion k n} :
    TerminationK_okE N E.conj ↔ TerminationK_okE N E := by
  simp [TerminationK_okE, TExpansion.conj]

@[simp] private theorem TerminationK_okE_swapSolid {E : TExpansion k n} :
    TerminationK_okE N E.swapSolid ↔ TerminationK_okE N E := by
  simp [TerminationK_okE, TExpansion.swapSolid]

private theorem TerminationK_okE_bind {E : TExpansion k n}
    {O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n'}
    (hE : TerminationK_okE N E)
    (hO : ∀ {n' : ℕ} (f : Atom k n → Atom k n') (g : Graph k n'),
      TerminationK_ok N g.comps → TerminationK_okE N (O f g)) :
    TerminationK_okE N (E.bind O) := by
  intro s hs
  unfold TExpansion.bind at hs
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
  exact hO t.f t.g (hE t ht) u hu

end OkE

/-! ### `O^{(x),1}_weight` and `O^{(x),2}_weight` -/

private theorem TerminationK_splitRegular {V : Type*} [DecidableEq V] (x : V) :
    ∀ (L : List (Comp V)), TerminationK_ok N L → ∀ p ∈ splitRegular x L, TerminationK_ok N p.1
  | [], _, p, hp => by
    rw [splitRegular, List.mem_singleton] at hp
    subst hp
    exact TerminationK_ok_nil
  | c :: L, hL, p, hp => by
    rw [TerminationK_ok_cons] at hL
    have ih := TerminationK_splitRegular x L hL.2
    unfold splitRegular at hp
    simp only at hp
    split at hp
    · split_ifs at hp
      · rcases List.mem_append.1 hp with hp | hp <;>
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        · exact ih q hq
        · exact TerminationK_ok_cons.2 ⟨rfl, ih q hq⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact TerminationK_ok_cons.2 ⟨hL.1, ih q hq⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact TerminationK_ok_cons.2 ⟨hL.1, ih q hq⟩

private theorem TerminationK_oWeight1T {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oWeight1T x Γ) := by
  unfold oWeight1T
  simp only [TerminationK_okE_map]
  exact fun p hp => TerminationK_splitRegular x _ h p hp

private theorem TerminationK_oWeight2Pos {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : oWeight2Pos x Γ = some E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N E := by
  unfold oWeight2Pos at hE
  split at hE
  · cases hE
  · cases hE
    have h1 := TerminationK_ok_eraseIdx h
    simp [h, h1, TerminationK_forall_dTerms]

private theorem TerminationK_oWeight2T {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oWeight2T x Γ) := by
  unfold oWeight2T
  split_ifs
  · exact TerminationK_okE_self.2 h
  · split
    · exact TerminationK_oWeight2Pos ‹_› h
    · split
      · exact TerminationK_okE_conj.2 (TerminationK_oWeight2Pos ‹_› ((TerminationK_ok_conj Γ).2 h))
      · exact TerminationK_okE_self.2 h

/-! ### `O_merge` and `O_dot` -/

private theorem TerminationK_mergeT {k n : ℕ} {Γ : Graph k n} {t : Tracked k n}
    (ht : Γ.mergeT = some t) (h : TerminationK_ok N Γ.comps) : TerminationK_ok N t.g.comps := by
  unfold Graph.mergeT at ht
  simp only at ht
  split_ifs at ht
  cases ht
  intro c hc
  obtain ⟨c', hc', hc⟩ := List.mem_filterMap.1 hc
  split_ifs at hc
  · obtain rfl := Option.some.inj hc
    change TerminationK_kok N c'.kind.toWeight = true
    rw [TerminationK_kok_toWeight]
    exact h c' hc'
  · obtain rfl := Option.some.inj hc
    exact h c' hc'

private theorem TerminationK_dotChoice {k n : ℕ} {Γ : Graph k n}
    (SP A : List (Atom k n × Atom k n × Bool)) (h : TerminationK_ok N Γ.comps) :
    TerminationK_ok N (Γ.dotChoice SP A).comps := by
  unfold Graph.dotChoice
  simp only [TerminationK_ok_append]
  refine ⟨TerminationK_ok_filter h _, fun c hc => ?_⟩
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hc
  split_ifs at hp <;> cases hp <;> rfl

private theorem TerminationK_oDotT {k n : ℕ} {Γ : Graph k n} (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N (oDotT Γ) := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact h
  · exact TerminationK_mergeT hm (TerminationK_dotChoice _ _ h)

/-! ### The local expansions -/

private theorem TerminationK_oWeightT {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oWeightT x Γ) := by
  unfold oWeightT
  split_ifs
  · exact TerminationK_okE_bind (TerminationK_okE_bind (TerminationK_okE_bind
      (TerminationK_oWeight1T x h) fun _ _ hg => TerminationK_oWeight2T _ hg)
      fun _ _ hg => TerminationK_oDotT hg) fun _ _ hg => TerminationK_oWeight1T _ hg
  · exact TerminationK_okE_self.2 h

private theorem TerminationK_multiEOut {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : multiEOut x Γ = some E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N E := by
  unfold multiEOut at hE
  split at hE
  · cases hE
  · split at hE
    · cases hE
    · simp only at hE
      split at hE
      · cases hE
      · cases hE
        have h1 := TerminationK_ok_eraseIdx h
        have h2 := TerminationK_ok_eraseIdxs h
        have h3 := TerminationK_ok_pickIdxs h
        simp [h, h1, h2, h3, TerminationK_forall_dTerms]

private theorem TerminationK_multiEIn {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : multiEIn x Γ = some E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N E := by
  unfold multiEIn at hE
  split at hE
  · cases hE
  · split at hE
    · cases hE
    · simp only at hE
      split at hE
      · cases hE
      · cases hE
        have h1 := TerminationK_ok_eraseIdx h
        have h2 := TerminationK_ok_eraseIdxs h
        have h3 := TerminationK_ok_pickIdxs h
        simp [h, h1, h2, h3, TerminationK_forall_dTerms]

private theorem TerminationK_multiEHat {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : multiEHat x Γ = some E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N E := by
  have hc := (TerminationK_ok_conj Γ).2 h
  unfold multiEHat at hE
  split_ifs at hE
  · exact TerminationK_multiEOut hE h
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    exact TerminationK_okE_conj.2 (TerminationK_multiEOut hE' hc)
  · exact TerminationK_multiEIn hE h
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    exact TerminationK_okE_conj.2 (TerminationK_multiEIn hE' hc)

private theorem TerminationK_oMultiET {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oMultiET x Γ) := by
  unfold oMultiET
  split_ifs
  · exact TerminationK_okE_self.2 h
  · split
    · exact TerminationK_okE_bind (TerminationK_multiEHat ‹_› h)
        fun _ _ hg => TerminationK_oDotT hg
    · exact TerminationK_okE_self.2 h

private theorem TerminationK_ggPos {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : ggPos x Γ = some E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N E := by
  unfold ggPos at hE
  split_ifs at hE
  split at hE
  · split at hE
    · simp only at hE
      split_ifs at hE
      cases hE
      have h2 := TerminationK_ok_eraseIdxs h
      simp [h, h2, TerminationK_forall_dTerms]
    · cases hE
  · cases hE

private theorem TerminationK_oGGT {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oGGT x Γ) := by
  unfold oGGT
  split_ifs
  · exact TerminationK_okE_self.2 h
  · split
    · exact TerminationK_okE_bind (TerminationK_ggPos ‹_› h) fun _ _ hg => TerminationK_oDotT hg
    · split
      · exact TerminationK_okE_bind
          (TerminationK_okE_conj.2 (TerminationK_ggPos ‹_› ((TerminationK_ok_conj Γ).2 h)))
          fun _ _ hg => TerminationK_oDotT hg
      · exact TerminationK_okE_self.2 h

private theorem TerminationK_oGGTT {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oGGTT x Γ) := by
  have hs := (TerminationK_ok_swapSolid Γ).2 h
  unfold oGGTT
  split_ifs
  · exact TerminationK_okE_self.2 h
  · split
    · exact TerminationK_okE_bind (TerminationK_okE_swapSolid.2 (TerminationK_ggPos ‹_› hs))
        fun _ _ hg => TerminationK_oDotT hg
    · split
      · exact TerminationK_okE_bind (TerminationK_okE_swapSolid.2 (TerminationK_okE_conj.2
          (TerminationK_ggPos ‹_› ((TerminationK_ok_conj _).2 hs))))
          fun _ _ hg => TerminationK_oDotT hg
      · exact TerminationK_okE_self.2 h

private theorem TerminationK_oGGbarT {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oGGbarT x Γ) := by
  unfold oGGbarT
  dsimp only
  split_ifs
  · exact TerminationK_oMultiET x h
  · exact TerminationK_okE_self.2 h

private theorem TerminationK_localOp' {k n : ℕ} (o : Fin 5) (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (localOp' o x Γ) := by
  fin_cases o
  · exact TerminationK_oWeightT x h
  · exact TerminationK_oMultiET x h
  · exact TerminationK_oGGT x h
  · exact TerminationK_oGGbarT x h
  · exact TerminationK_oGGTT x h

/-! ### The elementary steps of the `Q`-expansions -/

private theorem TerminationK_oSchurT {k n : ℕ} (x : Atom k n) (i : ℕ) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oSchurT x i Γ) := by
  have h1 := TerminationK_ok_eraseIdx h i
  unfold oSchurT
  repeat' split
  all_goals first
    | exact TerminationK_okE_self.2 h
    | simp [*]

private theorem TerminationK_oSchurRevT {k n : ℕ} (x : Atom k n) (i : ℕ) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oSchurRevT x i Γ) := by
  have h1 := TerminationK_ok_eraseIdx h i
  unfold oSchurRevT
  repeat' split
  all_goals first
    | exact TerminationK_okE_self.2 h
    | simp [*]

private theorem TerminationK_oSchurWT {k n : ℕ} (x : Atom k n) (i : ℕ) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oSchurWT x i Γ) := by
  have h1 := TerminationK_ok_eraseIdx h i
  unfold oSchurWT
  repeat' split
  all_goals first
    | exact TerminationK_okE_self.2 h
    | simp [*]

private theorem TerminationK_oSchurWRevT {k n : ℕ} (x : Atom k n) (i : ℕ) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oSchurWRevT x i Γ) := by
  have h1 := TerminationK_ok_eraseIdx h i
  unfold oSchurWRevT
  repeat' split
  all_goals first
    | exact TerminationK_okE_self.2 h
    | simp [*]

private theorem TerminationK_oTaylorT {k n : ℕ} (D i : ℕ) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oTaylorT D i Γ) := by
  have h1 := TerminationK_ok_eraseIdx h i
  unfold oTaylorT
  repeat' split
  all_goals first
    | exact TerminationK_okE_self.2 h
    | simp [*]

private theorem TerminationK_oSplitT {k n : ℕ} (u v : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oSplitT u v Γ) := by
  unfold oSplitT
  split_ifs
  · exact TerminationK_okE_self.2 h
  · simp [h]

private theorem TerminationK_oXdotT {k n : ℕ} (i : ℕ) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oXdotT i Γ) := by
  have h1 := TerminationK_ok_eraseIdx h i
  unfold oXdotT
  repeat' split
  all_goals first
    | exact TerminationK_okE_self.2 h
    | simp [*]

private theorem TerminationK_oQPT {k n : ℕ} (u : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oQPT u Γ) := by
  unfold oQPT
  simp only [TerminationK_okE_self_cons, TerminationK_ok_dropLabels]
  exact ⟨h, (TerminationK_ok_map _ fun c _ => by split <;> rfl).2 h, TerminationK_okE_nil⟩

private theorem TerminationK_absorb {k n : ℕ} (ℓ : PQ × Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_ok N (Γ.absorb ℓ).comps :=
  (TerminationK_ok_map _ fun c _ => by split <;> rfl).2 h

private theorem TerminationK_pCore {k n : ℕ} {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_ok N Γ.pCore.comps := by
  unfold Graph.pCore
  refine (TerminationK_ok_map _ ?_).2 (TerminationK_ok_filter h _)
  intro c _
  rfl

private theorem TerminationK_pLiftT {k n : ℕ} (u : Atom k n) {Γ : Graph k n}
    {E : TExpansion k n} (hE : TerminationK_okE N E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N (pLiftT u Γ E) := by
  intro s hs
  unfold pLiftT at hs
  obtain ⟨t, ht, hs⟩ := List.mem_filterMap.1 hs
  split_ifs at hs
  obtain rfl := Option.some.inj hs
  simp only [TerminationK_ok_append, TerminationK_ok_mapComp]
  exact ⟨(TerminationK_ok_map _ fun c _ => by split <;> rfl).2 (hE t ht),
    TerminationK_ok_filter h _⟩

private theorem TerminationK_oWeightP2Pos {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
    {E : TExpansion k n} (hE : oWeightP2Pos x Γ = some E) (h : TerminationK_ok N Γ.comps) :
    TerminationK_okE N E := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  · cases hE
    have h1 := TerminationK_ok_eraseIdx h
    simp [h, h1, TerminationK_forall_dTerms]

private theorem TerminationK_oWeightP2T {k n : ℕ} (x : Atom k n) {Γ : Graph k n}
    (h : TerminationK_ok N Γ.comps) : TerminationK_okE N (oWeightP2T x Γ) := by
  have hp := TerminationK_pCore h
  unfold oWeightP2T
  split
  · exact TerminationK_pLiftT x (TerminationK_oWeightP2Pos ‹_› hp) h
  · split
    · exact TerminationK_pLiftT x
        (TerminationK_okE_conj.2 (TerminationK_oWeightP2Pos ‹_› ((TerminationK_ok_conj _).2 hp))) h
    · exact TerminationK_okE_self.2 h

/-- Every elementary step of the `Q`-expansions keeps the run kinds. -/
private theorem TerminationK_qElemStep {k : ℕ} {g g' : Σ n, Graph k n} (hs : QElemStep g g')
    (h : TerminationK_ok N g.2.comps) : TerminationK_ok N g'.2.comps := by
  cases hs with
  | schur x i Γ t hx ht => exact TerminationK_oSchurT x i h t ht
  | schurRev x i Γ t hx ht => exact TerminationK_oSchurRevT x i h t ht
  | schurW x i Γ t hx ht => exact TerminationK_oSchurWT x i h t ht
  | schurWRev x i Γ t hx ht => exact TerminationK_oSchurWRevT x i h t ht
  | taylor D i Γ t ht => exact TerminationK_oTaylorT D i h t ht
  | weight1 x Γ t ht => exact TerminationK_oWeight1T x h t ht
  | dot Γ t ht => exact TerminationK_oDotT h t ht
  | merge Γ t ht => exact TerminationK_mergeT ht h
  | split u v Γ t hv ht => exact TerminationK_oSplitT u v h t ht
  | xdot i Γ t ht => exact TerminationK_oXdotT i h t ht
  | dropDot i Γ c hc hk hb => exact TerminationK_ok_eraseIdx h i
  | rebase i Γ c u v hc hk hb =>
    intro d hd
    rcases List.mem_or_eq_of_mem_set hd with hd | rfl
    · exact h d hd
    · exact h c (List.mem_of_getElem? hc)
  | qToP u Γ t hQ ht => exact TerminationK_oQPT u h t ht
  | absorb ℓ Γ hℓ hl => exact TerminationK_absorb ℓ h
  | dropP u Γ hP hm => exact (TerminationK_ok_dropLabels Γ).2 h
  | pWeight1 x Γ t hP hp ht =>
    exact TerminationK_pLiftT x (TerminationK_oWeight1T x (TerminationK_pCore h)) h t ht
  | pWeight2 x Γ t hP hp ht => exact TerminationK_oWeightP2T x h t ht
  | pMultiE x Γ E t hP hp hE ht =>
    exact TerminationK_pLiftT x (TerminationK_multiEHat hE (TerminationK_pCore h)) h t ht

/-- A chain of elementary steps of the `Q`-expansions keeps the run kinds. -/
private theorem TerminationK_qElemChain {k : ℕ} {g g' : Σ n, Graph k n}
    (hs : Relation.ReflTransGen QElemStep g g') (h : TerminationK_ok N g.2.comps) :
    TerminationK_ok N g'.2.comps := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact TerminationK_qElemStep hs ih

/-! ### The other steps of a run -/

private theorem TerminationK_forget {k n : ℕ} {E : TExpansion k n} (hE : TerminationK_okE N E) :
    ∀ s ∈ E.forget, TerminationK_ok N s.2.comps := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
  exact hE t ht

@[simp] private theorem TerminationK_ok_glue {k n n' : ℕ} (H : Graph k n) (x y₁ y₂ : Atom k n)
    (G : Graph 3 n') :
    TerminationK_ok N (H.glue x y₁ y₂ G).comps ↔ TerminationK_ok N H.comps ∧
      TerminationK_ok N G.comps := by
  simp [Graph.glue]

private theorem TerminationK_forall₂ {V : Type*} {R : Comp V → Comp V → Prop}
    (hR : ∀ c c', R c c' → c'.kind = c.kind) :
    ∀ {L L' : List (Comp V)}, List.Forall₂ R L L' → TerminationK_ok N L → TerminationK_ok N L'
  | _, _, .nil, _ => TerminationK_ok_nil
  | _, _, .cons hr hl, h => by
    rw [TerminationK_ok_cons] at h ⊢
    exact ⟨hR _ _ hr ▸ h.1, TerminationK_forall₂ hR hl h.2⟩

private theorem TerminationK_reorder {k n : ℕ} {Γ Γ' : Graph k n} (h : Γ.Reorder Γ')
    (hK : TerminationK_ok N Γ.comps) : TerminationK_ok N Γ'.comps := by
  obtain ⟨-, π, cs, h2, h3⟩ := h
  have h1 : TerminationK_ok N (Γ.relabel π).comps := by
    simpa [Graph.relabel, Graph.mapAtoms] using hK
  have hcs := TerminationK_forall₂ (by rintro c c' (rfl | ⟨-, rfl⟩) <;> rfl) h2 h1
  exact fun c hc => hcs c (h3.mem_iff.2 hc)

end Ops

/-! ## Every step of a run keeps the run kinds -/

/-- **Every step of a run of [II, Strategy 6.6] keeps the run kinds**: at an admissible location
(`TerminationC_Adm`), if the graph has run kinds only (`Graph.RunKinds`) and so has every graph of
the formal sum substituted in Steps 2–3 (the right side of [II, (4.15)] for the `T`-expansion of
order `n - 1`), every graph of the output `TerminationC_stepOut` has run kinds only. The local
expansions of [II, Defs 4.3–4.6], `O_dot`, the elementary steps of the `Q`-expansions of
[II, §4.4] and the substitution [II, (4.15)] create no `Θ`, `Θ^{(n)}_err`, ghost or auxiliary
edge. -/
theorem TerminationK_step {n D N : ℕ} {𝒯 : TRec}
    {𝔈 : ℕ → (n₀ : ℕ) → Fin n₀ → Graph 3 n₀ → TExpansion 3 n₀} (h𝔈 : QExpFamilyStmt 𝔈)
    (h𝒯 : ∀ g ∈ 𝒯.tSubst (n - 1), g.2.RunKinds N)
    {g : Σ n₀ : ℕ, Graph 3 n₀} {l : TerminationC_Loc g.1} (h : TerminationC_Adm n D 𝔈 g l)
    (hK : g.2.RunKinds N) :
    ∀ s ∈ TerminationC_stepOut n D 𝒯 𝔈 g l, s.2.RunKinds N := by
  have _ := h𝔈
  simp only [TerminationK_runKinds_iff] at hK h𝒯 ⊢
  obtain ⟨n₀, Γ⟩ := g
  cases l with
  | loc o x => exact TerminationK_forget (TerminationK_localOp' o (.inr x) hK)
  | dot => exact TerminationK_forget (TerminationK_oDotT hK)
  | dropDot Γ' =>
    obtain ⟨⟨i, c, -, -, -, rfl⟩, -, -⟩ := h
    intro s hs
    rw [List.mem_singleton.1 hs]
    exact TerminationK_ok_eraseIdx hK i
  | reorder Γ' =>
    intro s hs
    rw [List.mem_singleton.1 hs]
    exact TerminationK_reorder h.1 hK
  | xdotDup i =>
    intro s hs
    rw [List.mem_singleton.1 hs]
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hK c hc
    · exact hK c (List.mem_of_getElem? (Option.mem_toList.1 hc))
  | xdotDrop i j =>
    intro s hs
    rw [List.mem_singleton.1 hs]
    exact TerminationK_ok_eraseIdx hK j
  | xdotLoop i =>
    intro s hs
    cases hs
  | coeffNorm =>
    intro s hs
    rw [List.mem_singleton.1 hs]
    exact hK
  | subst m H x y₁ y₂ =>
    obtain ⟨he, -⟩ := h
    obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.1 he
    cases eq_of_heq he
    intro s hs
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hs
    obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 hg'
    rw [TerminationK_ok_glue] at hK ⊢
    exact ⟨hK.1, (TerminationK_ok_swapSolid _).2 (h𝒯 g'' hg'')⟩
  | qexp x =>
    obtain ⟨-, -, -, -, -, -, ⟨C', hC⟩, -⟩ := h
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    exact TerminationK_qElemChain (hC t ht).1.1.2.2.2.2.2.2 hK

section Instances

end Instances

end RBM8D.Graphs
