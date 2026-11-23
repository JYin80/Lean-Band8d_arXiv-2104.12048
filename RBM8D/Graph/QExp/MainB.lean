module

public import RBM8D.Graph.QExp.FlatSchur
public import RBM8D.Graph.QExp.FlatSplit
public import RBM8D.Graph.QExp.Clauses
public import RBM8D.Graph.QExp.Main

@[expose] public section

/-!
# [II, Lemma 5.13] in the block reading

Every elementary step of the `Q`-expansions keeps the invariant `Graph.InvB'`, and the
`Q`-expansion of [II, Lemma 4.15] passes it to every output graph.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The multiset of the present edges of a molecular multigraph -/

section Multi

variable {V E V' E' : Type}

/-- The multiset with the entry of an optional value. -/
private def MainB_om {α : Type} : Option α → Multiset α
  | none => 0
  | some a => {a}

/-- The datum of the edge `e`: its class and its two ends; `none` if the edge is absent. -/
private def MainB_D (G : MGraph V E) (e : E) : Option (MClass × V × V) :=
  (G.cls e).map fun c => (c, (G.ends e).1, (G.ends e).2)

/-- The multiset of the data of the present edges. -/
private def MainB_pm [Fintype E] (G : MGraph V E) : Multiset (MClass × V × V) :=
  ∑ e, MainB_om (MainB_D G e)

/-- A datum with its two ends mapped by `f`. -/
private def MainB_F (f : V → V') (d : MClass × V × V) : MClass × V' × V' :=
  (d.1, f d.2.1, f d.2.2)

@[simp] private theorem MainB_om_none {α : Type} : MainB_om (none : Option α) = 0 := rfl

private theorem MainB_om_map {α β : Type} (F : α → β) (o : Option α) :
    (MainB_om o).map F = MainB_om (o.map F) := by
  cases o <;> simp [MainB_om]

private theorem MainB_count_om {α : Type} [DecidableEq α] (a : α) (o : Option α) :
    (MainB_om o).count a = if o = some a then 1 else 0 := by
  cases o with
  | none => simp [MainB_om]
  | some b =>
    simp only [MainB_om, Multiset.count_singleton, Option.some.injEq]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]

private theorem MainB_mem_om {α : Type} {a : α} {o : Option α} : a ∈ MainB_om o ↔ o = some a := by
  cases o <;> simp [MainB_om, eq_comm]

private theorem MainB_map_sum {ι α β : Type} (F : α → β) (s : Finset ι) (m : ι → Multiset α) :
    (∑ i ∈ s, m i).map F = ∑ i ∈ s, (m i).map F :=
  map_sum (Multiset.mapAddMonoidHom F) m s

/-- The number of edges with a given datum. -/
private theorem MainB_count_pm [Fintype E] (G : MGraph V E)
    (F : MClass × V × V → MClass × V' × V') [DecidableEq V'] (d : MClass × V' × V') :
    ((MainB_pm G).map F).count d = Fintype.card {e : E // (MainB_D G e).map F = some d} := by
  rw [MainB_pm, MainB_map_sum, Multiset.count_sum']
  simp only [MainB_om_map, MainB_count_om]
  rw [Finset.sum_boole, Fintype.card_subtype]
  simp

/-- Two molecular multigraphs whose multisets of present edges correspond under a map of the
vertices that is injective on the vertices are changes of names of each other. -/
private theorem MainB_tr [Fintype E] [Fintype E'] [DecidableEq V'] [Inhabited E']
    (G : MGraph V E) (G' : MGraph V' E') (f : V → V')
    (hinj : Set.InjOn f (↑G.int ∪ ↑G.ext)) (hint : G'.int = G.int.image f)
    (hext : G'.ext = G.ext.image f)
    (hv : ∀ d ∈ MainB_pm G, G.IsVtx d.2.1 ∧ G.IsVtx d.2.2)
    (hpm : MainB_pm G' = (MainB_pm G).map (MainB_F f)) : G.Transported G' := by
  classical
  set F := MainB_F (V := V) f with hF
  have hcard : ∀ d, Fintype.card {e : E // (MainB_D G e).map F = some d} =
      Fintype.card {e' : E' // MainB_D G' e' = some d} := by
    intro d
    rw [← MainB_count_pm, ← hpm]
    have := MainB_count_pm G' id d
    rw [Multiset.map_id] at this
    simpa using this
  let φ : ∀ d, {e : E // (MainB_D G e).map F = some d} ≃ {e' : E' // MainB_D G' e' = some d} :=
    fun d => Fintype.equivOfCardEq (hcard d)
  let g : E → E' := fun e =>
    if h : ∃ d, (MainB_D G e).map F = some d then (φ h.choose ⟨e, h.choose_spec⟩).1 else default
  have key : ∀ (d d' : MClass × V' × V') (hd : d = d')
      (x : {e : E // (MainB_D G e).map F = some d})
      (y : {e : E // (MainB_D G e).map F = some d'}), (φ d x).1 = (φ d' y).1 → x.1 = y.1 := by
    rintro d _ rfl x y h
    exact congrArg Subtype.val ((φ d).injective (Subtype.ext h))
  have hD : ∀ e, G.cls e ≠ none → ∃ d, (MainB_D G e).map F = some d := by
    intro e he
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 he
    exact ⟨F (c, (G.ends e).1, (G.ends e).2), by simp [MainB_D, hc]⟩
  have hgd : ∀ e (h : ∃ d, (MainB_D G e).map F = some d),
      g e = (φ h.choose ⟨e, h.choose_spec⟩).1 := by
    intro e h
    simp only [g]
    rw [dite_eq_left_of_eq_true (eq_true h)]
  have hg : ∀ e (h : ∃ d, (MainB_D G e).map F = some d), MainB_D G' (g e) = some h.choose := by
    intro e h
    rw [hgd e h]
    exact (φ h.choose ⟨e, h.choose_spec⟩).2
  have hch : ∀ e (c : MClass) (hc : G.cls e = some c) (k : ∃ d, (MainB_D G e).map F = some d),
      k.choose = (c, f (G.ends e).1, f (G.ends e).2) := by
    intro e c hc k
    exact Option.some.inj (k.choose_spec.symm.trans (by simp [MainB_D, hc, F, MainB_F]))
  refine ⟨f, g, ?_, hinj, hint, hext, ?_, ?_, ?_, ?_⟩
  · intro e₁ e₂ h₁ h₂ h
    have k₁ := hD e₁ h₁
    have k₂ := hD e₂ h₂
    have d₁ := hg e₁ k₁
    have d₂ := hg e₂ k₂
    rw [h] at d₁
    have hdd : k₁.choose = k₂.choose := Option.some.inj (d₁.symm.trans d₂)
    have := key _ _ hdd ⟨e₁, k₁.choose_spec⟩ ⟨e₂, k₂.choose_spec⟩ (by
      rw [← hgd e₁ k₁, ← hgd e₂ k₂]; exact h)
    exact this
  · intro e he
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 he
    have hm : (c, (G.ends e).1, (G.ends e).2) ∈ MainB_pm G := by
      rw [MainB_pm, Multiset.mem_sum]
      exact ⟨e, Finset.mem_univ _, MainB_mem_om.2 (by simp [MainB_D, hc])⟩
    exact hv _ hm
  · intro e he
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 he
    have k := hD e he
    have h1 := hg e k
    rw [hch e c hc k] at h1
    simp only [MainB_D] at h1
    rw [hc]
    cases h : G'.cls (g e) with
    | none => rw [h] at h1; simp at h1
    | some c' =>
      rw [h] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      rw [h1.1]
  · intro e he
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 he
    have k := hD e he
    have h1 := hg e k
    rw [hch e c hc k] at h1
    simp only [MainB_D] at h1
    left
    cases h : G'.cls (g e) with
    | none => rw [h] at h1; simp at h1
    | some c' =>
      rw [h] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      exact Prod.ext h1.2.1 h1.2.2
  · intro e' he'
    by_contra hne
    obtain ⟨d, hd⟩ : ∃ d, MainB_D G' e' = some d := by
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
      exact ⟨(c, (G'.ends e').1, (G'.ends e').2), by simp [MainB_D, hc]⟩
    set x := (φ d).symm ⟨e', hd⟩ with hx
    have hxe : G.cls x.1 ≠ none := by
      intro hn
      have := x.2
      simp [MainB_D, hn] at this
    apply he' x.1 hxe
    have k : ∃ d, (MainB_D G x.1).map F = some d := ⟨d, x.2⟩
    have hkd : k.choose = d := Option.some.inj (k.choose_spec.symm.trans x.2)
    rw [hgd _ k]
    have e1 : (φ d x).1 = e' := by rw [hx, Equiv.apply_symm_apply]
    rw [← e1]
    have key2 : ∀ (d₁ d₂ : MClass × V' × V') (hd : d₁ = d₂)
        (x₁ : {e : E // (MainB_D G e).map F = some d₁})
        (x₂ : {e : E // (MainB_D G e).map F = some d₂}), x₁.1 = x₂.1 →
          (φ d₁ x₁).1 = (φ d₂ x₂).1 := by
      rintro d₁ _ rfl x₁ x₂ h
      rw [Subtype.ext h]
    exact key2 _ _ hkd _ _ rfl

/-- The multiset of present edges changes only at the edges where the graphs differ. -/
private theorem MainB_pm_two [Fintype E] (G H : MGraph V E) (a b : E) (hab : a ≠ b)
    (h : ∀ e, e ≠ a → e ≠ b → MainB_D H e = MainB_D G e) :
    MainB_pm H + MainB_om (MainB_D G a) + MainB_om (MainB_D G b) =
      MainB_pm G + MainB_om (MainB_D H a) + MainB_om (MainB_D H b) := by
  classical
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩
  have hs : ∀ X : MGraph V E, MainB_pm X = MainB_om (MainB_D X a) + MainB_om (MainB_D X b) +
      ∑ e ∈ (Finset.univ.erase a).erase b, MainB_om (MainB_D X e) := by
    intro X
    rw [MainB_pm, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hb]
    abel
  have hr : ∑ e ∈ (Finset.univ.erase a).erase b, MainB_om (MainB_D H e) =
      ∑ e ∈ (Finset.univ.erase a).erase b, MainB_om (MainB_D G e) := by
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨heb, hea⟩ := Finset.mem_erase.1 he
    rw [h e (Finset.mem_erase.1 hea).1 heb]
  rw [hs H, hs G, hr]
  abel

/-- Every datum of the multiset of present edges is that of a present edge. -/
private theorem MainB_of_mem_pm [Fintype E] {G : MGraph V E} {d : MClass × V × V}
    (h : d ∈ MainB_pm G) : ∃ e, MainB_D G e = some d := by
  rw [MainB_pm, Multiset.mem_sum] at h
  obtain ⟨e, -, he⟩ := h
  exact ⟨e, MainB_mem_om.1 he⟩

/-- If the present edges join vertices, so do the data of the multiset. -/
private theorem MainB_pm_vtx [Fintype E] {G : MGraph V E}
    (h : ∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) :
    ∀ d ∈ MainB_pm G, G.IsVtx d.2.1 ∧ G.IsVtx d.2.2 := by
  intro d hd
  obtain ⟨e, he⟩ := MainB_of_mem_pm hd
  cases hc : G.cls e with
  | none => simp [MainB_D, hc] at he
  | some c =>
    simp only [MainB_D, hc, Option.map_some, Option.some.injEq] at he
    subst he
    exact h e (by simp [hc])

/-- The molecular multigraph `G` with `m` more edges, all absent. -/
private def MainB_ext [Inhabited V] (G : MGraph V E) (m : ℕ) : MGraph V (E ⊕ Fin m) where
  int := G.int
  ext := G.ext
  ends := Sum.elim G.ends fun _ => (default, default)
  cls := Sum.elim G.cls fun _ => none

private theorem MainB_pm_ext [Fintype E] [Inhabited V] (G : MGraph V E) (m : ℕ) :
    MainB_pm (MainB_ext G m) = MainB_pm G := by
  rw [MainB_pm, Fintype.sum_sum_type]
  simp [MainB_pm, MainB_ext, MainB_D, MainB_om]

/-- The datum of an edge from `A` to `B` of class `m`, absent if `A = B`. -/
private def MainB_od [DecidableEq V] (m : MClass) (A B : V) : Option (MClass × V × V) :=
  if A = B then none else some (m, A, B)

/-- Operation (B) at an edge from the internal vertex `A` to `B` through the internal vertex `X`
(after a blue solid loop at `A` when the edge is absent), or two moves of a red edge, followed by
the removal of the loops: the edge `A – B` of class `m` is replaced by the edges `A – X` and
`X – B` of class `m`, each absent when its ends are equal. -/
private theorem MainB_chain [Fintype E] [DecidableEq V] [DecidableEq E] (H : MGraph V E)
    (e e' : E) (hne : e ≠ e') (A B X : V) (m : MClass) (hm : m = .plus ∨ m = .minus)
    (hA : A ∈ H.int) (hB : H.IsVtx B) (hX : X ∈ H.int)
    (he : MainB_D H e = MainB_od m A B) (he' : H.cls e' = none) :
    ∃ G₁, Relation.ReflTransGen MGraph.CarStep H G₁ ∧ G₁.int = H.int ∧ G₁.ext = H.ext ∧
      MainB_pm G₁ + MainB_om (MainB_od m A B) =
        MainB_pm H + MainB_om (MainB_od m A X) + MainB_om (MainB_od m X B) := by
  have hne' : e' ≠ e := fun h => hne h.symm
  have hD' : MainB_D H e' = none := by simp [MainB_D, he']
  have hcls : H.cls e = if A = B then none else some m := by
    unfold MainB_D MainB_od at he
    split_ifs at he with hAB
    · simpa [hAB] using he
    · simp only [hAB, ↓reduceIte]
      cases h : H.cls e with
      | none => rw [h] at he; simp at he
      | some c =>
        rw [h] at he
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
        rw [he.1]
  have hends : A ≠ B → H.ends e = (A, B) := by
    intro hAB
    unfold MainB_D MainB_od at he
    simp only [hAB, ↓reduceIte] at he
    cases h : H.cls e with
    | none => rw [h] at he; simp at he
    | some c =>
      rw [h] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      exact Prod.ext he.2.1 he.2.2
  -- the general bookkeeping
  have fin : ∀ G₁ : MGraph V E, (∀ f, f ≠ e → f ≠ e' → MainB_D G₁ f = MainB_D H f) →
      MainB_om (MainB_D G₁ e) + MainB_om (MainB_D G₁ e') =
        MainB_om (MainB_od m A X) + MainB_om (MainB_od m X B) →
      MainB_pm G₁ + MainB_om (MainB_od m A B) =
        MainB_pm H + MainB_om (MainB_od m A X) + MainB_om (MainB_od m X B) := by
    intro G₁ h1 h2
    have := MainB_pm_two H G₁ e e' hne h1
    rw [he, hD', MainB_om_none, add_zero] at this
    rw [this, add_assoc, h2, ← add_assoc]
  rcases hm with rfl | rfl
  · by_cases hAB : A = B
    · subst hAB
      by_cases hAX : A = X
      · subst hAX
        refine ⟨H, .refl, rfl, rfl, ?_⟩
        simp [MainB_od]
      · have hc0 : H.cls e = none := by simpa using hcls
        have s1 : MGraph.CarStep H (H.setEdge e A A (some .plus)) := .loop _ e A hc0 hA
        have s2 : MGraph.CarStep (H.setEdge e A A (some .plus))
            ((H.setEdge e A A (some .plus)).split e e' X) :=
          .split _ e e' X (by simp [MGraph.setEdge])
            (by simp [MGraph.setEdge, MGraph.IsVtx, hA])
            (by simp [MGraph.setEdge, MGraph.IsVtx, hA])
            (by simp [MGraph.setEdge, hA]) hne (by simp [MGraph.setEdge, hne', he']) hX
        refine ⟨_, .tail (.single s1) s2, rfl, rfl, fin _ (fun f h1 h2 => ?_) ?_⟩
        · simp [MainB_D, MGraph.split, MGraph.setEdge, h1, h2]
        · simp [MainB_D, MGraph.split, MGraph.setEdge, hne', MainB_od, hAX, Ne.symm hAX]
    · have hs : MGraph.CarStep H (H.split e e' X) :=
        .split _ e e' X (by simp [hcls, hAB])
          (by rw [hends hAB]; exact Or.inl hA) (by rw [hends hAB]; exact hB)
          (by rw [hends hAB]; exact Or.inl hA) hne he' hX
      by_cases hXA : X = A
      · subst hXA
        have hu : MGraph.CarStep (H.split e e' X) ((H.split e e' X).erase e) :=
          .unloop _ e (by simp [MGraph.split, hne, hcls, hAB]) (by simp [MGraph.split, hends hAB])
        refine ⟨_, .tail (.single hs) hu, rfl, rfl, fin _ (fun f h1 h2 => ?_) ?_⟩
        · simp [MainB_D, MGraph.split, MGraph.erase, h1, h2]
        · simp [MainB_D, MGraph.split, MGraph.erase, hne', hcls, hAB, hends hAB, MainB_od]
      · by_cases hXB : X = B
        · subst hXB
          have hu : MGraph.CarStep (H.split e e' X) ((H.split e e' X).erase e') :=
            .unloop _ e' (by simp [MGraph.split, hcls, hAB])
              (by simp [MGraph.split, hne', hends hAB])
          refine ⟨_, .tail (.single hs) hu, rfl, rfl, fin _ (fun f h1 h2 => ?_) ?_⟩
          · simp [MainB_D, MGraph.split, MGraph.erase, h1, h2]
          · simp [MainB_D, MGraph.split, MGraph.erase, hne, hcls, hAB, hends hAB, MainB_od]
        · refine ⟨_, .single hs, rfl, rfl, fin _ (fun f h1 h2 => ?_) ?_⟩
          · simp [MainB_D, MGraph.split, h1, h2]
          · simp [MainB_D, MGraph.split, hne', hcls, hAB, hends hAB, MainB_od, Ne.symm hXA, hXB]
  · have s1 : MGraph.CarStep H (H.setEdge e A X (if A = X then none else some .minus)) :=
      .red _ e A X _ (by rw [hcls]; split_ifs <;> simp) (by split_ifs <;> simp)
    have s2 : MGraph.CarStep (H.setEdge e A X (if A = X then none else some .minus))
        ((H.setEdge e A X (if A = X then none else some .minus)).setEdge e' X B
          (if X = B then none else some .minus)) :=
      .red _ e' X B _ (by simp [MGraph.setEdge, hne', he']) (by split_ifs <;> simp)
    refine ⟨_, .tail (.single s1) s2, rfl, rfl, fin _ (fun f h1 h2 => ?_) ?_⟩
    · simp [MainB_D, MGraph.setEdge, h1, h2]
    · by_cases hAX : A = X <;> by_cases hXB : X = B <;>
        simp [MainB_D, MGraph.setEdge, MainB_od, hne, hAX, hXB]
      split_ifs <;> rfl

end Multi

/-! ## Blocks, molecules and the block normal form -/

instance MainB_instInhAtom {n : ℕ} : Inhabited (Atom 3 n) := ⟨.inl 0⟩

instance MainB_instInhE {L : ℕ} : Inhabited (Fin L ⊕ Fin 3) := ⟨.inr 0⟩

instance MainB_instInhE' {L m : ℕ} : Inhabited ((Fin L ⊕ Fin 3) ⊕ Fin m) := ⟨.inl (.inr 0)⟩

section Generic

variable {k n : ℕ}

/-- The least internal atom of the block of `u` lies in that block. -/
private theorem MainB_anchor_some {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor at h
  have hb := List.find?_some h
  exact of_decide_eq_true hb

/-- The block of `u` has no internal atom exactly when `Graph.anchor` is `none` at `u`. -/
private theorem MainB_anchor_none {Γ : Graph k n} {u : Atom k n} :
    Γ.anchor u = none ↔ ∀ b, ¬ Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  simp

/-- An atom lies in the block of its atom in the block normal form. -/
private theorem MainB_flat_block (Γ : Graph k n) (u : Atom k n) :
    Γ.SameBlock u (Γ.flatAtom u) := by
  cases u with
  | inr b => exact SimpleGraph.Reachable.refl _
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b
    · simp only [Graph.flatAtom, hA]
      exact SimpleGraph.Reachable.refl _
    · simp only [Graph.flatAtom, hA]
      exact MainB_anchor_some hA

/-- The block of an atom that is not unpinned has an internal atom. -/
private theorem MainB_block_of_not_unpinned {Γ : Graph k n} {u : Atom k n}
    (h : ¬ Γ.Unpinned u) : ∃ b, Γ.SameBlock u (.inr b) := by
  cases u with
  | inr b => exact ⟨b, SimpleGraph.Reachable.refl _⟩
  | inl a =>
    by_contra hn
    push Not at hn
    exact h ⟨rfl, hn⟩

/-- An atom whose block has an internal atom is not unpinned. -/
private theorem MainB_not_unpinned {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.SameBlock u (.inr b)) : ¬ Γ.Unpinned u := fun hu => hu.2 b h

/-- The default value of `List.find?` does not matter when some element satisfies the
predicate. -/
private theorem MainB_find_congr {α : Type} (l : List α) (P P' : α → Bool) (d d' : α)
    (hPP : ∀ x, P x = P' x) (h : ∃ x ∈ l, P x = true) :
    (l.find? P).getD d = (l.find? P').getD d' := by
  have e : P = P' := funext hPP
  subst e
  obtain ⟨x, hx, hp⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨x, hx, hp⟩)
  simp [hr]

/-- A property of all elements satisfying `P` and of the default value holds for the value of
`List.find?`. -/
private theorem MainB_find_getD {α : Type} (l : List α) (P : α → Bool) (d : α)
    (Q : α → Prop) (hP : ∀ b, P b = true → Q b) (hd : Q d) : Q ((l.find? P).getD d) := by
  cases h : l.find? P with
  | none => simpa using hd
  | some r => simpa using hP r (List.find?_some h)

/-- An atom lies in the molecule of its representative. -/
private theorem MainB_molRep_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.SameMol u (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inl rfl
  | inr a =>
    unfold Graph.molRep
    exact MainB_find_getD _ _ a (fun r => Γ.SameMol (.inr a) (.inr r))
      (fun b hb => of_decide_eq_true hb) (Or.inl rfl)

/-- Two atoms have the same representative exactly when they lie in one molecule. -/
private theorem MainB_molRep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.molRep u = Γ.molRep v ↔ Γ.SameMol u v := by
  have E := Γ.sameMol_equivalence
  constructor
  · intro h
    exact E.trans (MainB_molRep_spec Γ u) (h ▸ E.symm (MainB_molRep_spec Γ v))
  · intro h
    cases u with
    | inl a =>
      rcases h with rfl | ⟨h1, -⟩
      · rfl
      · exact absurd h1 (by simp)
    | inr a =>
      cases v with
      | inl b =>
        rcases h with h | ⟨-, h2, -⟩
        · exact absurd h (by simp)
        · exact absurd h2 (by simp)
      | inr b =>
        unfold Graph.molRep
        refine congrArg Sum.inr (MainB_find_congr _ _ _ _ _ (fun c => ?_)
          ⟨b, List.mem_finRange _, decide_eq_true h⟩)
        exact decide_eq_decide.2 ⟨fun h' => E.trans (E.symm h) h', fun h' => E.trans h h'⟩

/-- The representative of a representative. -/
private theorem MainB_molRep_idem (Γ : Graph k n) (u : Atom k n) :
    Γ.molRep (Γ.molRep u) = Γ.molRep u :=
  (MainB_molRep_eq_iff Γ _ _).2 (Γ.sameMol_equivalence.symm (MainB_molRep_spec Γ u))

/-- The dotted edges are edges of the molecular graph. -/
private theorem MainB_dot_le_mol (Γ : Graph k n) : Γ.dotGraph ≤ Γ.molGraph := by
  intro u v huv
  simp only [Graph.dotGraph, Graph.molGraph, SimpleGraph.fromRel_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
  · exact Or.inl ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩
  · exact Or.inr ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩

/-- Two internal atoms of one block lie in one molecule. -/
private theorem MainB_sameMol_of_block {Γ : Graph k n} {u v : Atom k n} (hu : u.isRight = true)
    (hv : v.isRight = true) (h : Γ.SameBlock u v) : Γ.SameMol u v :=
  Or.inr ⟨hu, hv, SimpleGraph.Reachable.mono (MainB_dot_le_mol Γ) h⟩

/-- The representative of every atom is a vertex of `Graph.toMG'`. -/
private theorem MainB_molRep_vtx (Γ : Graph k n) (u : Atom k n) :
    Γ.toMG'.IsVtx (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  | inr a => exact Or.inl (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)

/-- The representative of an internal atom is an internal vertex. -/
private theorem MainB_molRep_int (Γ : Graph k n) {u : Atom k n} (hu : u.isRight = true) :
    Γ.molRep u ∈ Γ.toMG'.int := by
  cases u with
  | inl a => simp at hu
  | inr b => exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩

/-- The vertices of `Graph.toMG'` are their own representatives. -/
private theorem MainB_vtx_fix {Γ : Graph k n} {v : Atom k n} (h : Γ.toMG'.IsVtx v) :
    Γ.molRep v = v := by
  rcases h with h | h
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
    exact MainB_molRep_idem Γ _
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
    rfl

/-- The present edges of `Graph.toMG'` join vertices. -/
private theorem MainB_pv (Γ : Graph k n) :
    ∀ e, Γ.toMG'.cls e ≠ none →
      Γ.toMG'.IsVtx (Γ.toMG'.ends e).1 ∧ Γ.toMG'.IsVtx (Γ.toMG'.ends e).2 := by
  rintro (i | a) h
  · exact ⟨MainB_molRep_vtx _ _, MainB_molRep_vtx _ _⟩
  · revert h
    simp only [Graph.toMG']
    split
    · rename_i b _
      intro _
      exact ⟨MainB_molRep_vtx Γ (.inr b), Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)⟩
    · intro h
      exact absurd rfl h

/-- Reachability is the same in two graphs whose edges are joined by paths in the other. -/
private theorem MainB_reach_iff {V : Type} {G H : SimpleGraph V}
    (h₁ : ∀ u v, G.Adj u v → H.Reachable u v) (h₂ : ∀ u v, H.Adj u v → G.Reachable u v)
    (u v : V) : G.Reachable u v ↔ H.Reachable u v := by
  have key : ∀ {G H : SimpleGraph V}, (∀ u v, G.Adj u v → H.Reachable u v) →
      ∀ u v, G.Reachable u v → H.Reachable u v := by
    intro G H h u v ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons ha _ ih => exact (h _ _ ha).trans ih
  exact ⟨key h₁ u v, key h₂ u v⟩

/-- A map of the vertices sending adjacent vertices to vertices joined by a path sends reachable
vertices to reachable vertices. -/
private theorem MainB_reach_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W)
    (h : ∀ u v, G.Adj u v → H.Reachable (f u) (f v)) {u v : V} (huv : G.Reachable u v) :
    H.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons ha _ ih => exact (h _ _ ha).trans ih

end Generic

/-! ## The edges of `Graph.toMG'` given by the components -/

section Read

variable {k n : ℕ}

/-- The kind and the two ends of a component. -/
private def MainB_st (c : Comp (Atom k n)) : Kind × Atom k n × Atom k n := (c.kind, c.x, c.y)

/-- The datum of the edge of `Graph.toMG'` given by a component of kind `p.1` from `p.2.1` to
`p.2.2`. -/
private def MainB_edS (Γ : Graph k n) (p : Kind × Atom k n × Atom k n) :
    Option (MClass × Atom k n × Atom k n) :=
  if p.1 = .dot ∨ Γ.molRep (Γ.flatAtom p.2.1) = Γ.molRep (Γ.flatAtom p.2.2) then none
  else p.1.mclass.map fun m => (m, Γ.molRep (Γ.flatAtom p.2.1), Γ.molRep (Γ.flatAtom p.2.2))

/-- The datum of the pin edge `.inr a` of `Graph.toMG'`. -/
private def MainB_pin (Γ : Graph k n) (a : Fin k) : Option (MClass × Atom k n × Atom k n) :=
  match Γ.anchor (.inl a) with
  | some b => some (pinClass a, Γ.molRep (.inr b), .inl a)
  | none => none

/-- The multiset of the data of the edges given by a list of kinds and ends. -/
private def MainB_cm (Γ : Graph k n) (L : List (Kind × Atom k n × Atom k n)) :
    Multiset (MClass × Atom k n × Atom k n) :=
  (L.map fun p => MainB_om (MainB_edS Γ p)).sum

/-- The multiset of the data of the pin edges. -/
private def MainB_pins (Γ : Graph k n) : Multiset (MClass × Atom k n × Atom k n) :=
  ∑ a, MainB_om (MainB_pin Γ a)

private theorem MainB_D_inl (Γ : Graph k n) (i : Fin Γ.comps.length) :
    MainB_D Γ.toMG' (.inl i) = MainB_edS Γ (MainB_st Γ.comps[i]) := by
  by_cases hk : Γ.comps[(i : ℕ)].kind = .dot
  · simp [MainB_D, Graph.toMG', MainB_edS, Graph.flatComp, hk, MainB_st]
  · simp only [MainB_D, Graph.toMG', MainB_edS, Graph.flatComp, hk, MainB_st, ↓reduceIte,
      false_or, Fin.getElem_fin]
    split_ifs <;> rfl

private theorem MainB_D_inr (Γ : Graph k n) (a : Fin k) :
    MainB_D Γ.toMG' (.inr a) = MainB_pin Γ a := by
  rcases h : Γ.anchor (.inl a) with _ | b <;> simp [MainB_D, Graph.toMG', MainB_pin, h]

private theorem MainB_pm_toMG' (Γ : Graph k n) :
    MainB_pm Γ.toMG' = MainB_cm Γ (Γ.comps.map MainB_st) + MainB_pins Γ := by
  rw [MainB_pm, Fintype.sum_sum_type]
  simp only [MainB_D_inl, MainB_D_inr]
  congr 1
  have e : ∀ x : Fin Γ.comps.length, MainB_om (MainB_edS Γ (MainB_st Γ.comps[x])) =
      (fun c => MainB_om (MainB_edS Γ (MainB_st c))) Γ.comps[(x : ℕ)] := fun x => rfl
  rw [Finset.sum_congr rfl (fun x _ => e x)]
  refine (Fin.sum_univ_fun_getElem Γ.comps (fun c => MainB_om (MainB_edS Γ (MainB_st c)))).trans ?_
  unfold MainB_cm
  rw [List.map_map]
  rfl

@[simp] private theorem MainB_cm_nil (Γ : Graph k n) : MainB_cm Γ [] = 0 := rfl

private theorem MainB_cm_append (Γ : Graph k n) (L M : List (Kind × Atom k n × Atom k n)) :
    MainB_cm Γ (L ++ M) = MainB_cm Γ L + MainB_cm Γ M := by
  simp [MainB_cm]

private theorem MainB_cm_cons (Γ : Graph k n) (p : Kind × Atom k n × Atom k n)
    (L : List (Kind × Atom k n × Atom k n)) :
    MainB_cm Γ (p :: L) = MainB_om (MainB_edS Γ p) + MainB_cm Γ L := by
  simp [MainB_cm]

private theorem MainB_cm_perm (Γ : Graph k n) {L M : List (Kind × Atom k n × Atom k n)}
    (h : L.Perm M) : MainB_cm Γ L = MainB_cm Γ M :=
  (h.map _).sum_eq

/-- A list whose components give no edge. -/
private theorem MainB_cm_zero (Γ : Graph k n) {L : List (Kind × Atom k n × Atom k n)}
    (h : ∀ p ∈ L, MainB_edS Γ p = none) : MainB_cm Γ L = 0 := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [MainB_cm_cons, h p (List.mem_cons_self ..), MainB_om_none, zero_add]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- A component of a kind that is never an edge gives no edge. -/
private theorem MainB_edS_none (Γ : Graph k n) {p : Kind × Atom k n × Atom k n}
    (h : p.1.mclass = none) : MainB_edS Γ p = none := by
  unfold MainB_edS
  split_ifs
  · rfl
  · rw [h]; rfl

/-- A dotted edge gives no edge. -/
private theorem MainB_edS_dot (Γ : Graph k n) {u v : Atom k n} :
    MainB_edS Γ (.dot, u, v) = none := by
  simp [MainB_edS]

end Read

/-! ## Molecular graphs carried along a correspondence of atoms -/

section Corr

variable {n n' : ℕ}

/-- A correspondence of the atoms of `Γ` with atoms of `Γ'` along `ι`: molecules and blocks
correspond, a block of `Γ'` meeting the image of `ι` lies in it, external atoms are fixed,
internal atoms go to internal atoms, and every internal atom of `Γ'` lies in the molecule of the
image of an internal atom. -/
private structure MainB_Corr (Γ : Graph 3 n) (Γ' : Graph 3 n') (ι : Atom 3 n → Atom 3 n') :
    Prop where
  mol : ∀ u v, Γ'.SameMol (ι u) (ι v) ↔ Γ.SameMol u v
  blk : ∀ u v, Γ'.SameBlock (ι u) (ι v) ↔ Γ.SameBlock u v
  img : ∀ u v', Γ'.SameBlock (ι u) v' → ∃ v, v' = ι v
  inl : ∀ a, ι (.inl a) = .inl a
  inr : ∀ b, (ι (.inr b)).isRight = true
  cov : ∀ a', ∃ a, Γ'.SameMol (.inr a') (ι (.inr a))

/-- The map of the vertices of `Graph.toMG'` along a correspondence. -/
private def MainB_f (Γ' : Graph 3 n') (ι : Atom 3 n → Atom 3 n') (v : Atom 3 n) : Atom 3 n' :=
  Γ'.molRep (ι v)

private theorem MainB_f_molRep {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (u : Atom 3 n) : MainB_f Γ' ι (Γ.molRep u) = MainB_f Γ' ι u :=
  (MainB_molRep_eq_iff Γ' _ _).2
    ((hC.mol _ _).2 (Γ.sameMol_equivalence.symm (MainB_molRep_spec Γ u)))

private theorem MainB_f_eq_iff {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (u v : Atom 3 n) :
    MainB_f Γ' ι u = MainB_f Γ' ι v ↔ Γ.molRep u = Γ.molRep v := by
  rw [MainB_f, MainB_f, MainB_molRep_eq_iff, MainB_molRep_eq_iff, hC.mol]

private theorem MainB_f_inl {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (a : Fin 3) : MainB_f Γ' ι (.inl a) = .inl a := by
  rw [MainB_f, hC.inl]
  rfl

/-- The pin edges correspond. -/
private theorem MainB_anchor_corr {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (a : Fin 3) :
    (Γ'.anchor (.inl a) = none ↔ Γ.anchor (.inl a) = none) ∧
      ∀ b b', Γ.anchor (.inl a) = some b → Γ'.anchor (.inl a) = some b' →
        Γ'.molRep (.inr b') = MainB_f Γ' ι (.inr b) := by
  have hi := hC.inl a
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun b b' h h' => ?_⟩
  · rw [MainB_anchor_none] at h ⊢
    intro b hb
    have := (hC.blk _ _).2 hb
    rw [hi] at this
    obtain ⟨b', hb'⟩ : ∃ b', ι (.inr b) = .inr b' := by
      have := hC.inr b
      revert this
      cases ι (.inr b) with
      | inl _ => simp
      | inr b' => exact fun _ => ⟨b', rfl⟩
    rw [hb'] at this
    exact h b' this
  · rw [MainB_anchor_none] at h ⊢
    intro b' hb'
    rw [← hi] at hb'
    obtain ⟨v, hv⟩ := hC.img _ _ hb'
    have hvb := (hC.blk _ _).1 (hv ▸ hb')
    cases v with
    | inl a' =>
      rw [hC.inl] at hv
      cases hv
    | inr b => exact h b hvb
  · have h1 := (hC.blk _ _).2 (MainB_anchor_some h)
    rw [hi] at h1
    have h2 := MainB_anchor_some h'
    have h3 : Γ'.SameBlock (.inr b') (ι (.inr b)) := h2.symm.trans h1
    exact (MainB_molRep_eq_iff Γ' _ _).2 (MainB_sameMol_of_block rfl (hC.inr b) h3)

/-- The block normal forms correspond. -/
private theorem MainB_flat_corr {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (u : Atom 3 n) :
    Γ'.molRep (Γ'.flatAtom (ι u)) = MainB_f Γ' ι (Γ.molRep (Γ.flatAtom u)) := by
  rw [MainB_f_molRep hC]
  cases u with
  | inr b =>
    obtain ⟨b', hb'⟩ : ∃ b', ι (.inr b) = .inr b' := by
      have := hC.inr b
      revert this
      cases ι (.inr b) with
      | inl _ => simp
      | inr b' => exact fun _ => ⟨b', rfl⟩
    rw [hb']
    simp [Graph.flatAtom, MainB_f, hb']
  | inl a =>
    obtain ⟨hn, hs⟩ := MainB_anchor_corr hC a
    rw [hC.inl]
    rcases hA : Γ.anchor (.inl a) with _ | b <;> rcases hA' : Γ'.anchor (.inl a) with _ | b'
    · simp [Graph.flatAtom, hA, hA', MainB_f, hC.inl]
    · exact absurd (hn.2 hA) (by simp [hA'])
    · exact absurd (hn.1 hA') (by simp [hA])
    · simp only [Graph.flatAtom, hA, hA']
      exact hs b b' hA hA'

/-- The datum of a component of `Γ'` corresponding to a component of `Γ`. -/
private theorem MainB_edS_corr {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (p' : Kind × Atom 3 n' × Atom 3 n') (p : Kind × Atom 3 n × Atom 3 n)
    (hd : p'.1 = .dot ↔ p.1 = .dot)
    (hk : Γ.molRep (Γ.flatAtom p.2.1) ≠ Γ.molRep (Γ.flatAtom p.2.2) → p'.1.mclass = p.1.mclass)
    (h1 : Γ'.molRep (Γ'.flatAtom p'.2.1) = MainB_f Γ' ι (Γ.molRep (Γ.flatAtom p.2.1)))
    (h2 : Γ'.molRep (Γ'.flatAtom p'.2.2) = MainB_f Γ' ι (Γ.molRep (Γ.flatAtom p.2.2))) :
    MainB_edS Γ' p' = (MainB_edS Γ p).map (MainB_F (MainB_f Γ' ι)) := by
  have he : MainB_f Γ' ι (Γ.molRep (Γ.flatAtom p.2.1)) =
      MainB_f Γ' ι (Γ.molRep (Γ.flatAtom p.2.2)) ↔
      Γ.molRep (Γ.flatAtom p.2.1) = Γ.molRep (Γ.flatAtom p.2.2) := by
    rw [MainB_f_eq_iff hC, MainB_molRep_idem, MainB_molRep_idem]
  unfold MainB_edS
  rw [h1, h2]
  by_cases hdot : p.1 = .dot
  · simp [hdot, hd.2 hdot]
  · have hdot' : p'.1 ≠ .dot := fun h => hdot (hd.1 h)
    by_cases heq : Γ.molRep (Γ.flatAtom p.2.1) = Γ.molRep (Γ.flatAtom p.2.2)
    · simp [hdot, hdot', heq]
    · have heq' := mt he.1 heq
      simp only [hdot, hdot', heq, heq', or_self, ↓reduceIte, hk heq, Option.map_map]
      rfl

/-- The image of a component under `ι`. -/
private theorem MainB_edS_map {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (p : Kind × Atom 3 n × Atom 3 n) :
    MainB_edS Γ' (p.1, ι p.2.1, ι p.2.2) = (MainB_edS Γ p).map (MainB_F (MainB_f Γ' ι)) :=
  MainB_edS_corr hC _ p Iff.rfl (fun _ => rfl) (MainB_flat_corr hC _) (MainB_flat_corr hC _)

private theorem MainB_pins_corr {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) :
    MainB_pins Γ' = (MainB_pins Γ).map (MainB_F (MainB_f Γ' ι)) := by
  rw [MainB_pins, MainB_pins, MainB_map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MainB_om_map]
  congr 1
  obtain ⟨hn, hs⟩ := MainB_anchor_corr hC a
  unfold MainB_pin
  rcases hA : Γ.anchor (.inl a) with _ | b <;> rcases hA' : Γ'.anchor (.inl a) with _ | b'
  · rfl
  · exact absurd (hn.2 hA) (by simp [hA'])
  · exact absurd (hn.1 hA') (by simp [hA])
  · simp only [Option.map_some, MainB_F, MainB_f_inl hC, hs b b' hA hA']
    rw [MainB_f_molRep hC]

/-- The vertices correspond. -/
private theorem MainB_vtx_corr {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) :
    Γ'.toMG'.int = Γ.toMG'.int.image (MainB_f Γ' ι) ∧
      Γ'.toMG'.ext = Γ.toMG'.ext.image (MainB_f Γ' ι) ∧
      Set.InjOn (MainB_f Γ' ι) (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext) := by
  refine ⟨?_, ?_, ?_⟩
  · ext y
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a', rfl⟩
      obtain ⟨a, ha⟩ := hC.cov a'
      exact ⟨_, ⟨a, rfl⟩, by rw [MainB_f_molRep hC]; exact ((MainB_molRep_eq_iff Γ' _ _).2 ha).symm⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      rw [MainB_f_molRep hC, MainB_f]
      obtain ⟨b', hb'⟩ : ∃ b', ι (.inr a) = .inr b' := by
        have := hC.inr a
        revert this
        cases ι (.inr a) with
        | inl _ => simp
        | inr b' => exact fun _ => ⟨b', rfl⟩
      exact ⟨b', by rw [hb']⟩
  · ext y
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, MainB_f_inl hC a⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (MainB_f_inl hC a).symm⟩
  · intro u hu v hv h
    have hu' : Γ.toMG'.IsVtx u := by simpa [MGraph.IsVtx] using hu
    have hv' : Γ.toMG'.IsVtx v := by simpa [MGraph.IsVtx] using hv
    have := (MainB_f_eq_iff hC u v).1 h
    rwa [MainB_vtx_fix hu', MainB_vtx_fix hv'] at this

/-- The images of components under `ι`. -/
private theorem MainB_cm_map {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) (L : List (Kind × Atom 3 n × Atom 3 n)) :
    MainB_cm Γ' (L.map fun p => (p.1, ι p.2.1, ι p.2.2)) =
      (MainB_cm Γ L).map (MainB_F (MainB_f Γ' ι)) := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, MainB_cm_cons, MainB_cm_cons, ih, Multiset.map_add, MainB_om_map,
      MainB_edS_map hC]

/-- `Graph.FlatCarried` from a correspondence of atoms under which the edges of the components
correspond: a change of names. -/
private theorem MainB_flat_iso {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι)
    (h : MainB_cm Γ' (Γ'.comps.map MainB_st) =
      (MainB_cm Γ (Γ.comps.map MainB_st)).map (MainB_F (MainB_f Γ' ι))) :
    Γ.FlatCarried Γ' := by
  obtain ⟨hi, he, hinj⟩ := MainB_vtx_corr hC
  exact MolDot_flatCarried_of_transported (MainB_tr _ _ _ hinj hi he
    (MainB_pm_vtx (MainB_pv Γ))
    (by rw [MainB_pm_toMG', MainB_pm_toMG', h, MainB_pins_corr hC, Multiset.map_add]))

/-- `Graph.FlatCarried` from a correspondence of atoms and a chain of the operations
`MGraph.CarStep` on `Graph.toMG'` of the first graph with `m` more absent edges, whose result has
the edges of the components of the second graph. -/
private theorem MainB_flat_chain {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}
    (hC : MainB_Corr Γ Γ' ι) {m : ℕ}
    (G₁ : MGraph (Atom 3 n) ((Fin Γ.comps.length ⊕ Fin 3) ⊕ Fin m))
    (hch : Relation.ReflTransGen MGraph.CarStep (MainB_ext Γ.toMG' m) G₁)
    (hi : G₁.int = Γ.toMG'.int) (he : G₁.ext = Γ.toMG'.ext)
    (hv : ∀ d ∈ MainB_pm G₁, G₁.IsVtx d.2.1 ∧ G₁.IsVtx d.2.2)
    (L : List (Kind × Atom 3 n × Atom 3 n))
    (hG : MainB_pm G₁ = MainB_cm Γ L + MainB_pins Γ)
    (h : MainB_cm Γ' (Γ'.comps.map MainB_st) = (MainB_cm Γ L).map (MainB_F (MainB_f Γ' ι))) :
    Γ.FlatCarried Γ' := by
  obtain ⟨hi', he', hinj⟩ := MainB_vtx_corr hC
  have hF : MainB_F (id : Atom 3 n → Atom 3 n) = id := by
    funext d; rfl
  refine MolDot_flatCarried_of_chain (MainB_ext Γ.toMG' m) G₁ ?_ hch ?_
  · refine MainB_tr _ _ id (Set.injOn_id _) (by simp [MainB_ext]) (by simp [MainB_ext])
      (MainB_pm_vtx (MainB_pv Γ)) ?_
    rw [MainB_pm_ext, hF, Multiset.map_id]
  · refine MainB_tr _ _ _ (by rw [hi, he]; exact hinj) (by rw [hi]; exact hi')
      (by rw [he]; exact he') hv ?_
    rw [MainB_pm_toMG', hG, h, MainB_pins_corr hC, Multiset.map_add]

end Corr

/-! ## Correspondences of atoms -/

section CorrOf

variable {n : ℕ}

/-- Two simple graphs given by relations with the same symmetric closure are equal. -/
private theorem MainB_fromRel_eq {V : Type} {R R' : V → V → Prop}
    (h₁ : ∀ u v, R' u v → R u v ∨ R v u) (h₂ : ∀ u v, R u v → R' u v ∨ R' v u) :
    SimpleGraph.fromRel R' = SimpleGraph.fromRel R := by
  ext u v
  simp only [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h₁ u v h⟩
    · exact ⟨hne, (h₁ v u h).symm⟩
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h₂ u v h⟩
    · exact ⟨hne, (h₂ v u h).symm⟩

/-- The identity is a correspondence between graphs with the same blocks and molecules. -/
private theorem MainB_corr_id {Γ Γ' : Graph 3 n} (hm : ∀ u v, Γ'.SameMol u v ↔ Γ.SameMol u v)
    (hb : ∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v) : MainB_Corr Γ Γ' id where
  mol := hm
  blk := hb
  img := fun _ v' _ => ⟨v', rfl⟩
  inl := fun _ => rfl
  inr := fun _ => rfl
  cov := fun a' => ⟨a', Or.inl rfl⟩

/-- Graphs with the same waved and dotted edges, up to orientation, have the same blocks and
molecules. -/
private theorem MainB_same {Γ Γ' : Graph 3 n}
    (h₁ : ∀ c ∈ Γ'.comps, c.kind.joinsMol = true →
      ∃ d ∈ Γ.comps, d.kind = c.kind ∧ (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x))
    (h₂ : ∀ d ∈ Γ.comps, d.kind.joinsMol = true →
      ∃ c ∈ Γ'.comps, c.kind = d.kind ∧ (c.x = d.x ∧ c.y = d.y ∨ c.x = d.y ∧ c.y = d.x)) :
    MainB_Corr Γ Γ' id := by
  have hd : Γ'.dotGraph = Γ.dotGraph := by
    apply MainB_fromRel_eq
    · rintro u v ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, hdk, h | h⟩ := h₁ c hc (by rw [hk]; rfl)
      · exact Or.inl ⟨d, hd, hdk.trans hk, h.1, h.2⟩
      · exact Or.inr ⟨d, hd, hdk.trans hk, h.1, h.2⟩
    · rintro u v ⟨d, hd, hk, rfl, rfl⟩
      obtain ⟨c, hc, hck, h | h⟩ := h₂ d hd (by rw [hk]; rfl)
      · exact Or.inl ⟨c, hc, hck.trans hk, h.1, h.2⟩
      · exact Or.inr ⟨c, hc, hck.trans hk, h.1, h.2⟩
  have hm : Γ'.molGraph = Γ.molGraph := by
    apply MainB_fromRel_eq
    · rintro u v ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, hdk, h | h⟩ := h₁ c hc hk
      · exact Or.inl ⟨d, hd, hdk ▸ hk, h.1, h.2⟩
      · exact Or.inr ⟨d, hd, hdk ▸ hk, h.1, h.2⟩
    · rintro u v ⟨d, hd, hk, rfl, rfl⟩
      obtain ⟨c, hc, hck, h | h⟩ := h₂ d hd hk
      · exact Or.inl ⟨c, hc, hck ▸ hk, h.1, h.2⟩
      · exact Or.inr ⟨c, hc, hck ▸ hk, h.1, h.2⟩
  refine MainB_corr_id (fun u v => ?_) (fun u v => ?_)
  · change u = v ∨ (u.isRight = true ∧ v.isRight = true ∧ Γ'.molGraph.Reachable u v) ↔
      u = v ∨ (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)
    rw [hm]
  · change Γ'.dotGraph.Reachable u v ↔ Γ.dotGraph.Reachable u v
    rw [hd]

/-- The atom map collapsing the new internal atom `n` onto `x`. -/
private def MainB_pi (x : Atom 3 n) : Atom 3 (n + 1) → Atom 3 n
  | .inl a => .inl a
  | .inr a => if h : a.val < n then .inr ⟨a.val, h⟩ else x

private theorem MainB_pi_lift (x : Atom 3 n) (u : Atom 3 n) : MainB_pi x (liftA 1 u) = u := by
  cases u with
  | inl a => rfl
  | inr a => simp [MainB_pi, liftA]

private theorem MainB_pi_new (x : Atom 3 n) : MainB_pi x (newA 0 : Atom 3 (n + 1)) = x := by
  simp [MainB_pi, newA]

private theorem MainB_lift_inj {u v : Atom 3 n} (h : (liftA 1 u : Atom 3 (n + 1)) = liftA 1 v) :
    u = v := by
  have := congrArg (MainB_pi u) h
  rwa [MainB_pi_lift, MainB_pi_lift] at this

private theorem MainB_lift_ne_new (u : Atom 3 n) : (liftA 1 u : Atom 3 (n + 1)) ≠ newA 0 := by
  cases u with
  | inl a => simp [liftA, newA]
  | inr a =>
    simp only [liftA, newA, Sum.map_inr, ne_eq, Sum.inr.injEq]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

/-- Every atom of a graph with one more internal atom is a lifted atom or the new atom. -/
private theorem MainB_lift_or_new (u' : Atom 3 (n + 1)) :
    (∃ u, u' = liftA 1 u) ∨ u' = newA 0 := by
  rcases u' with a | a
  · exact Or.inl ⟨.inl a, rfl⟩
  · by_cases h : a.val < n
    · exact Or.inl ⟨.inr ⟨a.val, h⟩, by simp [liftA]⟩
    · right
      simp only [newA, Sum.inr.injEq]
      ext
      simp
      have := a.2
      omega

/-- The graph `Γ'` with one more internal atom, joined to the internal atom `x` by a waved edge, and
otherwise with the lifted waved and dotted edges of `Γ`, corresponds to `Γ` along `liftA 1`. -/
private theorem MainB_corr_lift {Γ : Graph 3 n} {Γ' : Graph 3 (n + 1)} {x : Atom 3 n}
    (hx : x.isRight = true)
    (h₁ : ∀ c ∈ Γ'.comps, c.kind.joinsMol = true →
      (∃ d ∈ Γ.comps, d.kind = c.kind ∧ c.x = liftA 1 d.x ∧ c.y = liftA 1 d.y) ∨
        (c.kind ≠ .dot ∧ (c.x = liftA 1 x ∧ c.y = newA 0 ∨ c.x = newA 0 ∧ c.y = liftA 1 x)))
    (h₂ : ∀ d ∈ Γ.comps, d.kind.joinsMol = true →
      ∃ c ∈ Γ'.comps, c.kind = d.kind ∧ c.x = liftA 1 d.x ∧ c.y = liftA 1 d.y)
    (h₃ : ∃ c ∈ Γ'.comps, c.kind.joinsMol = true ∧ c.x = liftA 1 x ∧ c.y = newA 0) :
    MainB_Corr Γ Γ' (liftA 1) := by
  -- reachability through `liftA 1` and `MainB_pi x`
  have hP : ∀ (P : Kind → Prop), (∀ κ, P κ → κ.joinsMol = true) →
      ∀ u v, (SimpleGraph.fromRel fun u v => ∃ c ∈ Γ'.comps, P c.kind ∧ c.x = u ∧ c.y = v).Reachable
          (liftA 1 u) (liftA 1 v) ↔
        (SimpleGraph.fromRel fun u v =>
          ∃ c ∈ Γ.comps, P c.kind ∧ c.x = u ∧ c.y = v).Reachable u v := by
    intro P hPj u v
    constructor
    · intro h
      have := MainB_reach_map
        (H := SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, P c.kind ∧ c.x = u ∧ c.y = v)
        (MainB_pi x) (fun a b hab => ?_) h
      · rwa [MainB_pi_lift, MainB_pi_lift] at this
      obtain ⟨hne, hab⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
      have key : ∀ a b, (∃ c ∈ Γ'.comps, P c.kind ∧ c.x = a ∧ c.y = b) →
          (SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, P c.kind ∧ c.x = u ∧ c.y = v).Reachable
            (MainB_pi x a) (MainB_pi x b) := by
        rintro a b ⟨c, hc, hPc, rfl, rfl⟩
        rcases h₁ c hc (hPj _ hPc) with ⟨d, hd, hdk, hcx, hcy⟩ | ⟨-, h | h⟩
        · rw [hcx, hcy, MainB_pi_lift, MainB_pi_lift]
          by_cases hdd : d.x = d.y
          · rw [hdd]
          · exact ((SimpleGraph.fromRel_adj _ _ _).2
              ⟨hdd, Or.inl ⟨d, hd, hdk ▸ hPc, rfl, rfl⟩⟩).reachable
        · rw [h.1, h.2, MainB_pi_lift, MainB_pi_new]
        · rw [h.1, h.2, MainB_pi_lift, MainB_pi_new]
      rcases hab with hab | hab
      · exact key a b hab
      · exact (key b a hab).symm
    · intro h
      refine MainB_reach_map (liftA 1) (fun a b hab => ?_) h
      obtain ⟨hne, hab⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
      have hne' : (liftA 1 a : Atom 3 (n + 1)) ≠ liftA 1 b := fun e => hne (MainB_lift_inj e)
      rcases hab with ⟨d, hd, hPd, rfl, rfl⟩ | ⟨d, hd, hPd, rfl, rfl⟩
      · obtain ⟨c, hc, hck, hcx, hcy⟩ := h₂ d hd (hPj _ hPd)
        exact ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hne', Or.inl ⟨c, hc, hck ▸ hPd, hcx, hcy⟩⟩).reachable
      · obtain ⟨c, hc, hck, hcx, hcy⟩ := h₂ d hd (hPj _ hPd)
        exact ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hne', Or.inr ⟨c, hc, hck ▸ hPd, hcx, hcy⟩⟩).reachable
  have hdotP := hP (fun κ => κ = .dot) (fun κ h => by rw [h]; rfl)
  have hmolP := hP (fun κ => κ.joinsMol = true) (fun κ h => h)
  have hrI : ∀ u : Atom 3 n, (liftA 1 u : Atom 3 (n + 1)).isRight = u.isRight := by
    intro u; cases u <;> rfl
  refine ⟨fun u v => ?_, fun u v => ?_, fun u v' h => ?_, fun a => rfl, fun b => rfl, fun a' => ?_⟩
  · unfold Graph.SameMol
    rw [hrI, hrI]
    have := hmolP u v
    simp only [Graph.molGraph] at this ⊢
    rw [this]
    constructor
    · rintro (h | h)
      · exact Or.inl (MainB_lift_inj h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (by rw [h])
      · exact Or.inr h
  · unfold Graph.SameBlock Graph.dotGraph
    exact hdotP u v
  · -- the new atom has no dotted edge
    have key : ∀ a b : Atom 3 (n + 1), Γ'.dotGraph.Reachable a b → (∃ u, a = liftA 1 u) →
        ∃ v, b = liftA 1 v := by
      intro a b ⟨w⟩
      induction w with
      | nil => exact id
      | cons hadj _ ih =>
        rintro ⟨u, rfl⟩
        apply ih
        obtain ⟨hne, hab⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hadj
        rcases hab with ⟨c, hc, hk, hcx, hcy⟩ | ⟨c, hc, hk, hcx, hcy⟩
        · rcases h₁ c hc (by rw [hk]; rfl) with ⟨d, -, -, -, hdy⟩ | ⟨hk', -⟩
          · exact ⟨d.y, hcy ▸ hdy⟩
          · exact absurd hk hk'
        · rcases h₁ c hc (by rw [hk]; rfl) with ⟨d, -, -, hdx, -⟩ | ⟨hk', -⟩
          · exact ⟨d.x, hcx ▸ hdx⟩
          · exact absurd hk hk'
    exact key _ _ h ⟨u, rfl⟩
  · rcases MainB_lift_or_new (.inr a' : Atom 3 (n + 1)) with ⟨u, hu⟩ | hu
    · cases u with
      | inl a => simp [liftA] at hu
      | inr a => exact ⟨a, by rw [hu]; exact Or.inl rfl⟩
    · obtain ⟨b, rfl⟩ : ∃ b, x = .inr b := by
        cases x with
        | inl a => simp at hx
        | inr b => exact ⟨b, rfl⟩
      refine ⟨b, Or.inr ⟨rfl, rfl, ?_⟩⟩
      rw [hu]
      obtain ⟨c, hc, hk, hcx, hcy⟩ := h₃
      have hne : (newA 0 : Atom 3 (n + 1)) ≠ liftA 1 (.inr b) := (MainB_lift_ne_new _).symm
      exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr ⟨c, hc, hk, hcx, hcy⟩⟩).reachable

end CorrOf

/-! ## A component split through a molecule -/

section Split

variable {n : ℕ}

/-- The datum of the edge given by a solid edge of charge `ch`. -/
private theorem MainB_edS_G {Γ : Graph 3 n} {ch : Charge} {m : MClass}
    (hm : (Kind.G ch).mclass = some m) (u v : Atom 3 n) :
    MainB_edS Γ (.G ch, u, v) =
      MainB_od m (Γ.molRep (Γ.flatAtom u)) (Γ.molRep (Γ.flatAtom v)) := by
  simp only [MainB_edS, MainB_od, hm, reduceCtorEq, false_or]
  split_ifs <;> rfl

private theorem MainB_flat_right {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true) :
    Γ.flatAtom x = x := by
  cases x with
  | inl a => simp at hx
  | inr b => rfl

/-- The graph `Γ` with the component `i` (a solid edge of charge `ch` from `c.x` to `b`, or a
component that is never an edge with `b = c.x`) replaced by solid edges of charge `ch` from `c.x` to
the internal atom `x` and from `x` to `b`, read on `Graph.toMG'` of `Γ`: operation (B) (after a
blue solid loop) or two moves of a red edge, then the removal of loops. -/
private theorem MainB_src_split {Γ : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c) (ch : Charge) (b x : Atom 3 n) (hx : x.isRight = true)
    (hcase : (c.kind = .G ch ∧ b = c.y) ∨ (c.kind.mclass = none ∧ b = c.x))
    (hcx : (Γ.flatAtom c.x).isRight = true) :
    ∃ G₁ : MGraph (Atom 3 n) ((Fin Γ.comps.length ⊕ Fin 3) ⊕ Fin 1),
      Relation.ReflTransGen MGraph.CarStep (MainB_ext Γ.toMG' 1) G₁ ∧
      G₁.int = Γ.toMG'.int ∧ G₁.ext = Γ.toMG'.ext ∧
      (∀ d ∈ MainB_pm G₁, G₁.IsVtx d.2.1 ∧ G₁.IsVtx d.2.2) ∧
      MainB_pm G₁ = MainB_cm Γ ((Γ.comps.eraseIdx i).map MainB_st ++
        [(.G ch, c.x, x), (.G ch, x, b)]) + MainB_pins Γ := by
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  set H := MainB_ext Γ.toMG' 1 with hH
  obtain ⟨m, hm, hmm⟩ : ∃ m, (Kind.G ch).mclass = some m ∧ (m = .plus ∨ m = .minus) := by
    cases ch <;> simp [Kind.mclass]
  set A := Γ.molRep (Γ.flatAtom c.x) with hA
  set X := Γ.molRep x with hX
  set B := Γ.molRep (Γ.flatAtom b) with hB
  have hfx := MainB_flat_right (Γ := Γ) hx
  have hsc : MainB_edS Γ (MainB_st c) = MainB_od m A B := by
    rcases hcase with ⟨hk, rfl⟩ | ⟨hk, rfl⟩
    · have : MainB_st c = (.G ch, c.x, c.y) := by simp [MainB_st, hk]
      rw [this, MainB_edS_G hm]
    · rw [MainB_edS_none Γ (by simpa [MainB_st] using hk)]
      simp [MainB_od, hB, hA]
  have hDe : MainB_D H (.inl (.inl ⟨i, hi⟩)) = MainB_od m A B := by
    have : MainB_D H (.inl (.inl ⟨i, hi⟩)) = MainB_D Γ.toMG' (.inl ⟨i, hi⟩) := rfl
    rw [this, MainB_D_inl]
    simp only [Fin.getElem_fin]
    rw [hci, hsc]
  have hDe' : H.cls (.inr 0) = none := rfl
  have hvH : ∀ d ∈ MainB_pm H, H.IsVtx d.2.1 ∧ H.IsVtx d.2.2 := by
    rw [hH, MainB_pm_ext]
    exact MainB_pm_vtx (MainB_pv Γ)
  obtain ⟨G₁, hch, hGi, hGe, hpm⟩ := MainB_chain H _ _ (by simp) A B X m hmm
    (MainB_molRep_int Γ hcx) (MainB_molRep_vtx Γ _) (MainB_molRep_int Γ hx) hDe hDe'
  refine ⟨G₁, hch, hGi, hGe, fun d hd => ?_, ?_⟩
  · have hd' : d ∈ MainB_pm G₁ + MainB_om (MainB_od m A B) := Multiset.mem_add.2 (Or.inl hd)
    rw [hpm] at hd'
    have hiv : ∀ v, H.IsVtx v → G₁.IsVtx v := by
      intro v hv
      simpa [MGraph.IsVtx, hGi, hGe] using hv
    rcases Multiset.mem_add.1 hd' with hd' | hd'
    · rcases Multiset.mem_add.1 hd' with hd' | hd'
      · exact ⟨hiv _ (hvH d hd').1, hiv _ (hvH d hd').2⟩
      · rw [MainB_mem_om] at hd'
        unfold MainB_od at hd'
        split_ifs at hd'
        cases hd'
        exact ⟨hiv _ (Or.inl (MainB_molRep_int Γ hcx)), hiv _ (Or.inl (MainB_molRep_int Γ hx))⟩
    · rw [MainB_mem_om] at hd'
      unfold MainB_od at hd'
      split_ifs at hd'
      cases hd'
      exact ⟨hiv _ (Or.inl (MainB_molRep_int Γ hx)), hiv _ (MainB_molRep_vtx Γ _)⟩
  · have hpmH : MainB_pm H = MainB_cm Γ (Γ.comps.map MainB_st) + MainB_pins Γ := by
      rw [hH, MainB_pm_ext, MainB_pm_toMG']
    have hperm : (Γ.comps.map MainB_st).Perm
        (MainB_st c :: (Γ.comps.eraseIdx i).map MainB_st) := by
      have := (List.getElem_cons_eraseIdx_perm hi).symm.map MainB_st
      rw [hci] at this
      simpa using this
    rw [hpmH, MainB_cm_perm Γ hperm, MainB_cm_cons, hsc] at hpm
    apply add_right_cancel (b := MainB_om (MainB_od m A B))
    rw [hpm, MainB_cm_append, MainB_cm_cons, MainB_cm_cons, MainB_edS_G hm, MainB_edS_G hm, hfx]
    simp only [MainB_cm_nil, add_zero]
    abel

end Split

/-! ## Steps that change no edge of the molecular graph -/

section Iso

variable {n : ℕ}

/-- The kinds that are edges of the molecular graph or join atoms into molecules. -/
private def MainB_rel (κ : Kind) : Bool := κ.joinsMol || κ.mclass.isSome

private theorem MainB_cm_filter (Γ : Graph 3 n) (L : List (Kind × Atom 3 n × Atom 3 n)) :
    MainB_cm Γ L = MainB_cm Γ (L.filter fun p => MainB_rel p.1) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [MainB_cm_cons, MainB_cm_cons, ih]
    · have : p.1.mclass = none := by
        simp only [MainB_rel, Bool.or_eq_true, not_or, Bool.not_eq_true] at h
        simpa using h.2
      rw [MainB_cm_cons, MainB_edS_none Γ this, MainB_om_none, zero_add, ih]

/-- Two graphs on the same atoms whose components that are edges of the molecular graph or join
atoms into molecules agree up to order, with their kinds and ends: a change of names. -/
private theorem MainB_flat_perm {Γ Γ' : Graph 3 n}
    (h : ((Γ'.comps.map MainB_st).filter fun p => MainB_rel p.1).Perm
      ((Γ.comps.map MainB_st).filter fun p => MainB_rel p.1)) : Γ.FlatCarried Γ' := by
  have hmem : ∀ {Δ Δ' : Graph 3 n},
      ((Δ'.comps.map MainB_st).filter fun p => MainB_rel p.1).Perm
        ((Δ.comps.map MainB_st).filter fun p => MainB_rel p.1) →
      ∀ c ∈ Δ'.comps, c.kind.joinsMol = true →
        ∃ d ∈ Δ.comps, d.kind = c.kind ∧ (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x) := by
    intro Δ Δ' hp c hc hj
    have h1 : MainB_st c ∈ (Δ'.comps.map MainB_st).filter fun p => MainB_rel p.1 :=
      List.mem_filter.2 ⟨List.mem_map_of_mem hc, by simp [MainB_rel, MainB_st, hj]⟩
    obtain ⟨d, hd, e⟩ := List.mem_map.1 (List.mem_filter.1 (hp.mem_iff.1 h1)).1
    simp only [MainB_st, Prod.mk.injEq] at e
    exact ⟨d, hd, e.1, Or.inl ⟨e.2.1, e.2.2⟩⟩
  have hC : MainB_Corr Γ Γ' id := MainB_same (hmem h) (hmem h.symm)
  refine MainB_flat_iso hC ?_
  rw [MainB_cm_filter, MainB_cm_perm _ h, ← MainB_cm_filter]
  have := MainB_cm_map hC (Γ.comps.map MainB_st)
  have e : (Γ.comps.map MainB_st).map (fun p => (p.1, id p.2.1, id p.2.2)) =
      Γ.comps.map MainB_st :=
    (List.map_congr_left (fun p _ => rfl)).trans (List.map_id _)
  rwa [e] at this

/-- The kind and ends of a component, read through `List.map`. -/
private theorem MainB_map_st_eq {L : List (Comp (Atom 3 n))} (g : Comp (Atom 3 n) → Comp (Atom 3 n))
    (hg : ∀ c ∈ L, MainB_st (g c) = MainB_st c) : (L.map g).map MainB_st = L.map MainB_st := by
  rw [List.map_map]
  exact List.map_congr_left fun c hc => hg c hc

/-- Components changed in their labels or minors only: a change of names. -/
private theorem MainB_flat_map {Γ : Graph 3 n} (g : Comp (Atom 3 n) → Comp (Atom 3 n))
    (hg : ∀ c ∈ Γ.comps, MainB_st (g c) = MainB_st c) (co : Coeff) :
    Γ.FlatCarried (⟨Γ.comps.map g, co⟩ : Graph 3 n) := by
  apply MainB_flat_perm
  rw [MainB_map_st_eq g hg]

/-- The component `i`, not an edge of the molecular graph, replaced by components that are not
edges of the molecular graph: a change of names. -/
private theorem MainB_flat_repl {Γ : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c) (hrc : MainB_rel c.kind = false) {N : List (Comp (Atom 3 n))}
    (hN : ∀ d ∈ N, MainB_rel d.kind = false) (co : Coeff) :
    Γ.FlatCarried (⟨Γ.comps.eraseIdx i ++ N, co⟩ : Graph 3 n) := by
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  apply MainB_flat_perm
  have hperm : (Γ.comps.map MainB_st).Perm (MainB_st c :: (Γ.comps.eraseIdx i).map MainB_st) := by
    have := (List.getElem_cons_eraseIdx_perm hi).symm.map MainB_st
    rw [hci] at this
    simpa using this
  refine List.Perm.trans ?_ (hperm.filter _).symm
  have hN' : (N.map MainB_st).filter (fun p => MainB_rel p.1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
    simp [MainB_st, hN d hd]
  simp only [List.map_append, List.filter_append, hN', List.append_nil, List.filter_cons]
  simp [MainB_st, hrc]

/-- The kinds and ends of the relevant components are kept by `splitRegular`. -/
private theorem MainB_splitRegular (x : Atom 3 n) :
    ∀ cs : List (Comp (Atom 3 n)), ∀ p ∈ splitRegular x cs,
      (p.1.map MainB_st).filter (fun q => MainB_rel q.1) =
        (cs.map MainB_st).filter (fun q => MainB_rel q.1)
  | [], p, hp => by
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    rfl
  | c :: cs, p, hp => by
    have ih := MainB_splitRegular x cs
    have hcons : ∀ q ∈ splitRegular x cs,
        ((c :: q.1).map MainB_st).filter (fun q => MainB_rel q.1) =
          ((c :: cs).map MainB_st).filter (fun q => MainB_rel q.1) := by
      intro q hq
      simp only [List.map_cons, List.filter_cons, ih q hq]
    simp only [splitRegular] at hp
    split at hp
    · rename_i ch hk
      have hw : MainB_rel c.kind = false := by rw [hk]; rfl
      split_ifs at hp
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          simp only [List.map_cons, List.filter_cons, MainB_st, hw, ih q hq]
          rfl
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          simp only [List.map_cons, List.filter_cons, MainB_st, hw, ih q hq]
          rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hcons q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hcons q hq

/-- `Graph.FlatCarried` is reflexive. -/
private theorem MainB_refl (Γ : Graph 3 n) : Γ.FlatCarried Γ := Relation.ReflTransGen.refl

/-- [II, (4.21)]: the weight `(G_{xx})⁻¹` replaced by light weights or `W_D`. -/
private theorem MainB_taylor {Γ : Graph 3 n} {D i : ℕ} {t : Tracked 3 n}
    (ht : t ∈ oTaylorT D i Γ) : Γ.FlatCarried t.g := by
  unfold oTaylorT at ht
  split at ht
  · rename_i c hc
    split at ht
    · rename_i ch hk
      have hrc : MainB_rel c.kind = false := by rw [hk]; rfl
      dsimp only at ht
      split_ifs at ht
      · rcases List.mem_append.1 ht with ht | ht
        · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
          exact MainB_flat_repl hc hrc (fun d hd => by rw [List.eq_of_mem_replicate hd]; rfl) _
        · rw [List.mem_singleton] at ht
          subst ht
          exact MainB_flat_repl hc hrc (fun d hd => by
            rw [List.mem_singleton] at hd; subst hd; rfl) _
      · rw [List.mem_singleton] at ht
        subst ht
        exact MainB_refl Γ
    · rw [List.mem_singleton] at ht
      subst ht
      exact MainB_refl Γ
  · rw [List.mem_singleton] at ht
    subst ht
    exact MainB_refl Γ

/-- `O^{(x),1}_weight`: weights replaced by light weights or removed. -/
private theorem MainB_weight1 {Γ : Graph 3 n} {x : Atom 3 n} {t : Tracked 3 n}
    (ht : t ∈ oWeight1T x Γ) : Γ.FlatCarried t.g := by
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  apply MainB_flat_perm
  rw [MainB_splitRegular x Γ.comps p hp]

/-- The labels removed. -/
private theorem MainB_dropLabels (Γ : Graph 3 n) : Γ.FlatCarried Γ.dropLabels := by
  unfold Graph.dropLabels
  exact MainB_flat_map (fun c => { c with label := none }) (fun c _ => rfl) Γ.coeff

/-- `Q_u = 1 - P_u`. -/
private theorem MainB_qToP {Γ : Graph 3 n} {u : Atom 3 n} {t : Tracked 3 n}
    (ht : t ∈ oQPT u Γ) : Γ.FlatCarried t.g := by
  unfold oQPT at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact MainB_dropLabels Γ
  · exact MainB_flat_map _ (fun c _ => by simp only [MainB_st]; split_ifs <;> rfl) _

/-- The factors with minor `{u}` moved into the label group. -/
private theorem MainB_absorb {Γ : Graph 3 n} (ℓ : PQ × Atom 3 n) :
    Γ.FlatCarried (Γ.absorb ℓ) := by
  unfold Graph.absorb
  exact MainB_flat_map _ (fun c _ => by simp only [MainB_st]; split_ifs <;> rfl) _

/-- `Graph.FlatCarried` between graphs on the same atoms with the same blocks and molecules whose
components give the same edges of the molecular graph. -/
private theorem MainB_flat_id {Γ Γ' : Graph 3 n} (hC : MainB_Corr Γ Γ' id)
    (h : MainB_cm Γ' (Γ'.comps.map MainB_st) = MainB_cm Γ' (Γ.comps.map MainB_st)) :
    Γ.FlatCarried Γ' := by
  refine MainB_flat_iso hC ?_
  rw [h]
  have := MainB_cm_map hC (Γ.comps.map MainB_st)
  have e : (Γ.comps.map MainB_st).map (fun p => (p.1, id p.2.1, id p.2.2)) =
      Γ.comps.map MainB_st :=
    (List.map_congr_left (fun p _ => rfl)).trans (List.map_id _)
  rwa [e] at this

/-- A dotted edge whose ends are joined by the other dotted edges removed. -/
private theorem MainB_dropDot {Γ : Graph 3 n} {i : ℕ} {c : Comp (Atom 3 n)}
    (hc : Γ.comps[i]? = some c) (hk : c.kind = .dot)
    (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n).SameBlock c.x c.y) :
    Γ.FlatCarried (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph 3 n) := by
  set Γ' : Graph 3 n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ'
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  have hperm : Γ.comps.Perm (c :: Γ.comps.eraseIdx i) := by
    have := (List.getElem_cons_eraseIdx_perm hi).symm
    rwa [hci] at this
  have hsub : ∀ d ∈ Γ'.comps, d ∈ Γ.comps := fun d hd => List.mem_of_mem_eraseIdx hd
  have hcases : ∀ d ∈ Γ.comps, d = c ∨ d ∈ Γ'.comps := fun d hd =>
    List.mem_cons.1 (hperm.mem_iff.1 hd)
  -- the graph of dotted edges and the molecular graph
  have hreach : ∀ (P : Kind → Prop), P .dot →
      ∀ u v, (SimpleGraph.fromRel fun u v => ∃ d ∈ Γ'.comps, P d.kind ∧ d.x = u ∧ d.y = v).Reachable
          u v ↔
        (SimpleGraph.fromRel fun u v =>
          ∃ d ∈ Γ.comps, P d.kind ∧ d.x = u ∧ d.y = v).Reachable u v := by
    intro P hP u v
    have hb' : (SimpleGraph.fromRel fun u v =>
        ∃ d ∈ Γ'.comps, P d.kind ∧ d.x = u ∧ d.y = v).Reachable c.x c.y := by
      refine SimpleGraph.Reachable.mono (fun a b hab => ?_) hb
      obtain ⟨hne, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
      · obtain ⟨d, hd, hdk, h1, h2⟩ := h
        exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨d, hd, hdk ▸ hP, h1, h2⟩⟩
      · obtain ⟨d, hd, hdk, h1, h2⟩ := h
        exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr ⟨d, hd, hdk ▸ hP, h1, h2⟩⟩
    refine MainB_reach_iff (fun a b hab => ?_) (fun a b hab => ?_) u v
    · obtain ⟨hne, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
      · obtain ⟨d, hd, hdk, h1, h2⟩ := h
        exact ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hne, Or.inl ⟨d, hsub d hd, hdk, h1, h2⟩⟩).reachable
      · obtain ⟨d, hd, hdk, h1, h2⟩ := h
        exact ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hne, Or.inr ⟨d, hsub d hd, hdk, h1, h2⟩⟩).reachable
    · obtain ⟨hne, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
      · obtain ⟨d, hd, hdk, h1, h2⟩ := h
        rcases hcases d hd with rfl | hd'
        · rw [← h1, ← h2]; exact hb'
        · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨d, hd', hdk, h1, h2⟩⟩).reachable
      · obtain ⟨d, hd, hdk, h1, h2⟩ := h
        rcases hcases d hd with rfl | hd'
        · rw [← h1, ← h2]; exact hb'.symm
        · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr ⟨d, hd', hdk, h1, h2⟩⟩).reachable
  have hC : MainB_Corr Γ Γ' id := by
    refine MainB_corr_id (fun u v => ?_) (fun u v => ?_)
    · have := hreach (fun κ => κ.joinsMol = true) rfl u v
      unfold Graph.SameMol Graph.molGraph
      rw [this]
    · exact hreach (fun κ => κ = .dot) rfl u v
  refine MainB_flat_id hC ?_
  rw [MainB_cm_perm Γ' (hperm.map MainB_st), List.map_cons, MainB_cm_cons]
  have : MainB_st c = (.dot, c.x, c.y) := by simp [MainB_st, hk]
  rw [this, MainB_edS_dot, MainB_om_none, zero_add]

end Iso

/-! ## Lists of components with corresponding edges -/

section Rel

variable {n n' : ℕ}

/-- The components with kinds and ends `L'` of `Γ'` give the images of the edges given by the
components `L` of `Γ`. -/
private def MainB_R (Γ : Graph 3 n) (Γ' : Graph 3 n') (ι : Atom 3 n → Atom 3 n')
    (L' : List (Kind × Atom 3 n' × Atom 3 n')) (L : List (Kind × Atom 3 n × Atom 3 n)) : Prop :=
  MainB_cm Γ' L' = (MainB_cm Γ L).map (MainB_F (MainB_f Γ' ι))

variable {Γ : Graph 3 n} {Γ' : Graph 3 n'} {ι : Atom 3 n → Atom 3 n'}

private theorem MainB_R_nil : MainB_R Γ Γ' ι [] [] := by simp [MainB_R]

private theorem MainB_R_append {A' B' : List (Kind × Atom 3 n' × Atom 3 n')}
    {A B : List (Kind × Atom 3 n × Atom 3 n)} (h₁ : MainB_R Γ Γ' ι A' A)
    (h₂ : MainB_R Γ Γ' ι B' B) : MainB_R Γ Γ' ι (A' ++ B') (A ++ B) := by
  unfold MainB_R at *
  rw [MainB_cm_append, MainB_cm_append, h₁, h₂, Multiset.map_add]

private theorem MainB_R_perm {A' B' : List (Kind × Atom 3 n' × Atom 3 n')}
    {A B : List (Kind × Atom 3 n × Atom 3 n)} (h' : A'.Perm B') (h : A.Perm B)
    (hR : MainB_R Γ Γ' ι A' A) : MainB_R Γ Γ' ι B' B := by
  unfold MainB_R at *
  rwa [← MainB_cm_perm Γ' h', ← MainB_cm_perm Γ h]

private theorem MainB_R_absL {L' : List (Kind × Atom 3 n' × Atom 3 n')}
    {L : List (Kind × Atom 3 n × Atom 3 n)} {N : List (Kind × Atom 3 n' × Atom 3 n')}
    (hN : ∀ p ∈ N, MainB_edS Γ' p = none) (hR : MainB_R Γ Γ' ι L' L) :
    MainB_R Γ Γ' ι (L' ++ N) L := by
  unfold MainB_R at *
  rw [MainB_cm_append, MainB_cm_zero Γ' hN, add_zero, hR]

private theorem MainB_R_absR {L' : List (Kind × Atom 3 n' × Atom 3 n')}
    {L : List (Kind × Atom 3 n × Atom 3 n)} {N : List (Kind × Atom 3 n × Atom 3 n)}
    (hN : ∀ p ∈ N, MainB_edS Γ p = none) (hR : MainB_R Γ Γ' ι L' L) :
    MainB_R Γ Γ' ι L' (L ++ N) := by
  unfold MainB_R at *
  rw [MainB_cm_append, MainB_cm_zero Γ hN, add_zero, hR]

private theorem MainB_R_lift (hC : MainB_Corr Γ Γ' ι) (L : List (Kind × Atom 3 n × Atom 3 n)) :
    MainB_R Γ Γ' ι (L.map fun p => (p.1, ι p.2.1, ι p.2.2)) L :=
  MainB_cm_map hC L

/-- The atom `v'` of `Γ'` and the atom `v` of `Γ` have corresponding molecules in the block
normal forms. -/
private def MainB_va (Γ : Graph 3 n) (Γ' : Graph 3 n') (ι : Atom 3 n → Atom 3 n')
    (v' : Atom 3 n') (v : Atom 3 n) : Prop :=
  Γ'.molRep (Γ'.flatAtom v') = MainB_f Γ' ι (Γ.molRep (Γ.flatAtom v))

private theorem MainB_va_map (hC : MainB_Corr Γ Γ' ι) (u : Atom 3 n) :
    MainB_va Γ Γ' ι (ι u) u :=
  MainB_flat_corr hC u

/-- An internal atom of `Γ'` in the molecule of the image of the internal atom `x`. -/
private theorem MainB_va_mol (hC : MainB_Corr Γ Γ' ι) {v' : Atom 3 n'} {x : Atom 3 n}
    (hv : v'.isRight = true) (hx : x.isRight = true) (h : Γ'.SameMol v' (ι x)) :
    MainB_va Γ Γ' ι v' x := by
  unfold MainB_va
  rw [MainB_flat_right hv, MainB_flat_right hx, MainB_f_molRep hC]
  exact (MainB_molRep_eq_iff Γ' _ _).2 h

private theorem MainB_R_single (hC : MainB_Corr Γ Γ' ι) {p' : Kind × Atom 3 n' × Atom 3 n'}
    {p : Kind × Atom 3 n × Atom 3 n} (hd : p'.1 = .dot ↔ p.1 = .dot)
    (hk : Γ.molRep (Γ.flatAtom p.2.1) ≠ Γ.molRep (Γ.flatAtom p.2.2) → p'.1.mclass = p.1.mclass)
    (h1 : MainB_va Γ Γ' ι p'.2.1 p.2.1) (h2 : MainB_va Γ Γ' ι p'.2.2 p.2.2) :
    MainB_R Γ Γ' ι [p'] [p] := by
  unfold MainB_R
  rw [MainB_cm_cons, MainB_cm_cons, MainB_cm_nil, MainB_cm_nil, add_zero, add_zero,
    MainB_om_map, MainB_edS_corr hC p' p hd hk h1 h2]

private theorem MainB_R_mkC (hC : MainB_Corr Γ Γ' ι) (κ : Kind) {u' v' : Atom 3 n'}
    {u v : Atom 3 n} (hu : MainB_va Γ Γ' ι u' u) (hv : MainB_va Γ Γ' ι v' v) :
    MainB_R Γ Γ' ι [(κ, u', v')] [(κ, u, v)] :=
  MainB_R_single hC Iff.rfl (fun _ => rfl) hu hv

private theorem MainB_R_solidC (hC : MainB_Corr Γ Γ' ι) (ch : Charge) {u' v' : Atom 3 n'}
    {u v : Atom 3 n} (hu : MainB_va Γ Γ' ι u' u) (hv : MainB_va Γ Γ' ι v' v) :
    MainB_R Γ Γ' ι [MainB_st (solidC ch u' v')] [(.G ch, u, v)] := by
  unfold solidC
  split_ifs with h
  · subst h
    refine MainB_R_single hC (by simp [MainB_st, mkC]) (fun hne => ?_) hu hv
    exfalso
    apply hne
    have e : MainB_f Γ' ι (Γ.molRep (Γ.flatAtom u)) = MainB_f Γ' ι (Γ.molRep (Γ.flatAtom v)) := by
      rw [← hu, ← hv]
    rwa [MainB_f_eq_iff hC, MainB_molRep_idem, MainB_molRep_idem] at e
  · exact MainB_R_mkC hC _ hu hv

/-- A component between two atoms of one molecule of the block normal form gives no edge. -/
private theorem MainB_edS_same {Δ : Graph 3 n'} {κ : Kind} {u v : Atom 3 n'}
    (h : Δ.molRep (Δ.flatAtom u) = Δ.molRep (Δ.flatAtom v)) : MainB_edS Δ (κ, u, v) = none := by
  simp [MainB_edS, h]

/-! ### Complex conjugation -/

/-- The classes of the complex conjugate components: blue and red solid edges exchanged. -/
private def MainB_sw : MClass → MClass
  | .plus => .minus
  | .minus => .plus
  | c => c

private def MainB_swC {V : Type} (d : MClass × V × V) : MClass × V × V :=
  (MainB_sw d.1, d.2.1, d.2.2)

/-- The kind and ends of the complex conjugate component. -/
private def MainB_cT {V : Type} (p : Kind × V × V) : Kind × V × V := (p.1.conj, p.2.1, p.2.2)

private theorem MainB_mclass_conj (κ : Kind) : κ.conj.mclass = κ.mclass.map MainB_sw := by
  rcases κ with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _
  · cases ch <;> rfl
  · cases ch <;> rfl
  · cases ch <;> rfl
  · cases ch <;> rfl
  · cases ch <;> rfl
  · cases w <;> rfl
  · rfl
  · rfl
  · rfl
  · cases b <;> rfl
  · rfl
  · rfl

private theorem MainB_conj_dot (κ : Kind) : κ.conj = .dot ↔ κ = .dot := by
  rcases κ with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
    first | (cases ch <;> simp [Kind.conj, Charge.flip]) | (cases w <;> simp [Kind.conj]) |
      simp [Kind.conj]

private theorem MainB_conj_conj (κ : Kind) : κ.conj.conj = κ := by
  rcases κ with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
    first | (cases ch <;> rfl) | (cases w <;> rfl) | rfl

private theorem MainB_cT_cT {V : Type} (p : Kind × V × V) : MainB_cT (MainB_cT p) = p := by
  simp [MainB_cT, MainB_conj_conj]

private theorem MainB_map_cT_cT {V : Type} (L : List (Kind × V × V)) :
    (L.map MainB_cT).map MainB_cT = L := by
  rw [List.map_map]
  exact (List.map_congr_left fun p _ => MainB_cT_cT p).trans (List.map_id _)

private theorem MainB_edS_cT (Δ : Graph 3 n') (p : Kind × Atom 3 n' × Atom 3 n') :
    MainB_edS Δ (MainB_cT p) = (MainB_edS Δ p).map MainB_swC := by
  unfold MainB_edS MainB_cT
  simp only [MainB_conj_dot, MainB_mclass_conj]
  split_ifs
  · rfl
  · cases p.1.mclass <;> rfl

private theorem MainB_cm_cT (Δ : Graph 3 n') (L : List (Kind × Atom 3 n' × Atom 3 n')) :
    MainB_cm Δ (L.map MainB_cT) = (MainB_cm Δ L).map MainB_swC := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, MainB_cm_cons, MainB_cm_cons, ih, Multiset.map_add, MainB_om_map,
      MainB_edS_cT]

private theorem MainB_R_conj {L' : List (Kind × Atom 3 n' × Atom 3 n')}
    {L : List (Kind × Atom 3 n × Atom 3 n)} (h : MainB_R Γ Γ' ι L' L) :
    MainB_R Γ Γ' ι (L'.map MainB_cT) (L.map MainB_cT) := by
  unfold MainB_R at *
  rw [MainB_cm_cT, MainB_cm_cT, h, Multiset.map_map, Multiset.map_map]
  rfl

end Rel

/-! ## The operations inside `P_x` -/

/-- A rearrangement of appended lists, by counting. -/
local macro "MainB_perm" : tactic => `(tactic| (
  rw [List.perm_iff_count]; intro a
  simp only [List.count_append, List.count_cons, List.count_nil, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, MainB_st]; omega))

section PSteps

variable {n : ℕ}

/-- The kind and ends of a component with its ends lifted. -/
private def MainB_lT (p : Kind × Atom 3 n × Atom 3 n) : Kind × Atom 3 (n + 1) × Atom 3 (n + 1) :=
  (p.1, liftA 1 p.2.1, liftA 1 p.2.2)

private theorem MainB_st_liftCs (L : List (Comp (Atom 3 n))) :
    (liftCs 1 L).map MainB_st = (L.map MainB_st).map MainB_lT := by
  simp [liftCs, MainB_st, MainB_lT, Comp.map, Function.comp_def]

private theorem MainB_st_pCore (Γ : Graph 3 n) :
    Γ.pCore.comps.map MainB_st =
      (Γ.comps.filter fun c => c.label.isSome || !c.kind.isRandom).map MainB_st := by
  simp [Graph.pCore, Function.comp_def, MainB_st]

private theorem MainB_perm_pCore (Γ : Graph 3 n) :
    (Γ.comps.map MainB_st).Perm (Γ.pCore.comps.map MainB_st ++ Γ.pEnv.map MainB_st) := by
  rw [MainB_st_pCore, Graph.pEnv, ← List.map_append]
  apply List.Perm.map
  have h1 := List.filter_append_perm
    (fun c : Comp (Atom 3 n) => c.label.isSome || !c.kind.isRandom) Γ.comps
  have h2 : (Γ.comps.filter fun c => !(c.label.isSome || !c.kind.isRandom)) =
      Γ.comps.filter fun c => c.label.isNone && c.kind.isRandom :=
    List.filter_congr fun c _ => by cases c.label <;> simp
  rw [h2] at h1
  exact h1.symm

/-- The waved and dotted edges are components of `Γ.pCore`. -/
private theorem MainB_jm_pCore (Γ : Graph 3 n) :
    (Γ.pCore.comps.map MainB_st).filter (fun p => p.1.joinsMol) =
      (Γ.comps.map MainB_st).filter (fun p => p.1.joinsMol) := by
  rw [MainB_st_pCore, List.filter_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c _
  simp only [Function.comp_apply, MainB_st]
  cases h : c.kind.joinsMol
  · simp
  · have : c.kind.isRandom = false := by
      rcases hk : c.kind with
        ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
        rw [hk] at h <;> first | rfl | (simp [Kind.joinsMol] at h)
    simp [this]

/-- A component of `Γ.pCore` is a component of `Γ` without its label. -/
private theorem MainB_mem_pCore {Γ : Graph 3 n} {c : Comp (Atom 3 n)} (h : c ∈ Γ.pCore.comps) :
    ∃ c₀ ∈ Γ.comps, MainB_st c₀ = MainB_st c := by
  simp only [Graph.pCore, List.mem_map, List.mem_filter] at h
  obtain ⟨d, ⟨hd, -⟩, rfl⟩ := h
  exact ⟨d, hd, rfl⟩

/-- The terms of `pLiftT`. -/
private theorem MainB_mem_pLift {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n}
    {t : Tracked 3 n} (ht : t ∈ pLiftT x Γ E) :
    ∃ t₀ ∈ E, t = ⟨t₀.nOut, ⟨t₀.g.comps.map (fun c =>
        if c.kind.isRandom then { c with label := some (.P, t₀.f x) } else c) ++
      Γ.pEnv.map (Comp.map t₀.f), t₀.g.coeff⟩, t₀.f⟩ := by
  unfold pLiftT at ht
  obtain ⟨t₀, ht₀, he⟩ := List.mem_filterMap.1 ht
  split_ifs at he
  exact ⟨t₀, ht₀, (Option.some.inj he).symm⟩

private theorem MainB_st_rl {m : ℕ} (u : Atom 3 m) (L : List (Comp (Atom 3 m))) :
    (L.map fun c => if c.kind.isRandom then { c with label := some (.P, u) } else c).map
      MainB_st = L.map MainB_st :=
  MainB_map_st_eq _ fun c _ => by simp only [MainB_st]; split_ifs <;> rfl

/-- `O^{(x),1}_weight` inside `P_x`. -/
private theorem MainB_pWeight1 {Γ : Graph 3 n} {x : Atom 3 n} {t : Tracked 3 n}
    (ht : t ∈ pLiftT x Γ (oWeight1T x Γ.pCore)) : Γ.FlatCarried t.g := by
  obtain ⟨t₀, ht₀, rfl⟩ := MainB_mem_pLift ht
  unfold oWeight1T at ht₀
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht₀
  apply MainB_flat_perm
  dsimp only
  have e : (Γ.pEnv.map (Comp.map id)).map MainB_st = Γ.pEnv.map MainB_st := by
    rw [List.map_map]; rfl
  rw [List.map_append, MainB_st_rl, e, List.filter_append, MainB_splitRegular x _ p hp,
    ← List.filter_append]
  exact ((MainB_perm_pCore Γ).filter _).symm

/-- On a graph with the charge pattern of the block normal form, the block normal form of the
first atom of a random component is internal. -/
private theorem MainB_colour {Γ : Graph 3 n} (h : Γ.ColourInvB) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) : (Γ.flatAtom c.x).isRight = true := by
  have hk : c.kind ≠ .dot := by
    intro h'
    rw [h'] at hr
    exact absurd hr (by decide)
  unfold Graph.ColourInvB Graph.ColourInv' at h
  have hm : Γ.flatComp c ∈ Γ.blockNorm.comps := List.mem_map_of_mem hc
  have := ((h _ hm).1 (by rw [Graph.flatComp_kind]; exact hr)).1
  simpa [Graph.flatComp, hk] using this

/-- The lifted waved and dotted edges of `Γ` and a waved edge from `x` to the new atom: a
correspondence along `liftA 1`, with the new atom in the molecule of `x`. -/
private theorem MainB_corr_of_jm {Γ : Graph 3 n} {Γ' : Graph 3 (n + 1)} {x : Atom 3 n}
    (hx : x.isRight = true)
    (hJ : ((Γ'.comps.map MainB_st).filter fun p => p.1.joinsMol).Perm
      (((Γ.comps.map MainB_st).filter fun p => p.1.joinsMol).map MainB_lT ++
        [(.waved .s, liftA 1 x, newA 0)])) :
    MainB_Corr Γ Γ' (liftA 1) ∧ Γ'.SameMol (newA 0) (liftA 1 x) := by
  have h₃ : ∃ c ∈ Γ'.comps, c.kind.joinsMol = true ∧ c.x = liftA 1 x ∧ c.y = newA 0 := by
    have : ((.waved .s, liftA 1 x, newA 0) : Kind × Atom 3 (n + 1) × Atom 3 (n + 1)) ∈
        (Γ'.comps.map MainB_st).filter fun p => p.1.joinsMol :=
      hJ.mem_iff.2 (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨c, hc, e⟩ := List.mem_map.1 (List.mem_filter.1 this).1
    simp only [MainB_st, Prod.mk.injEq] at e
    exact ⟨c, hc, by rw [e.1]; rfl, e.2.1, e.2.2⟩
  refine ⟨MainB_corr_lift hx (fun c hc hj => ?_) (fun d hd hj => ?_) h₃, ?_⟩
  · have : MainB_st c ∈ (Γ'.comps.map MainB_st).filter fun p => p.1.joinsMol :=
      List.mem_filter.2 ⟨List.mem_map_of_mem hc, by simpa [MainB_st] using hj⟩
    rcases List.mem_append.1 (hJ.mem_iff.1 this) with h | h
    · obtain ⟨q, hq, e⟩ := List.mem_map.1 h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hq).1
      simp only [MainB_st, MainB_lT, Prod.mk.injEq] at e
      exact Or.inl ⟨d, hd, e.1, e.2.1.symm, e.2.2.symm⟩
    · rw [List.mem_singleton] at h
      simp only [MainB_st, Prod.mk.injEq] at h
      exact Or.inr ⟨by rw [h.1]; simp, Or.inl ⟨h.2.1, h.2.2⟩⟩
  · have : MainB_lT (MainB_st d) ∈ (((Γ.comps.map MainB_st).filter fun p => p.1.joinsMol).map
        MainB_lT ++ [(.waved .s, liftA 1 x, newA 0)]) :=
      List.mem_append_left _ (List.mem_map_of_mem (List.mem_filter.2
        ⟨List.mem_map_of_mem hd, by simpa [MainB_st] using hj⟩))
    obtain ⟨c, hc, e⟩ := List.mem_map.1 (List.mem_filter.1 (hJ.mem_iff.2 this)).1
    simp only [MainB_st, MainB_lT, Prod.mk.injEq] at e
    exact ⟨c, hc, e.1, e.2.1, e.2.2⟩
  · obtain ⟨c, hc, hj, hcx, hcy⟩ := h₃
    have hne : (newA 0 : Atom 3 (n + 1)) ≠ liftA 1 x := (MainB_lift_ne_new x).symm
    have hxr : (liftA 1 x : Atom 3 (n + 1)).isRight = true := by
      cases x with
      | inl a => simp at hx
      | inr b => rfl
    exact Or.inr ⟨rfl, hxr, ((SimpleGraph.fromRel_adj _ _ _).2
      ⟨hne, Or.inr ⟨c, hc, hj, hcx, hcy⟩⟩).reachable⟩

/-- The relation of a term of an operation on `H` inside `P_x` to `H`: either the edges of its
components correspond to those of `H`, or one random component `p` of `H` is split through `x`. -/
private def MainB_Out (Γ : Graph 3 n) (Γ' : Graph 3 (n + 1)) (x : Atom 3 n)
    (L' : List (Kind × Atom 3 (n + 1) × Atom 3 (n + 1))) (Q : List (Kind × Atom 3 n × Atom 3 n)) :
    Prop :=
  MainB_R Γ Γ' (liftA 1) L' Q ∨
    ∃ (p : Kind × Atom 3 n × Atom 3 n) (Q' : List (Kind × Atom 3 n × Atom 3 n)) (ch : Charge)
      (bb : Atom 3 n), Q.Perm (p :: Q') ∧ p.1.isRandom = true ∧
      ((p.1 = .G ch ∧ bb = p.2.2) ∨ (p.1.mclass = none ∧ bb = p.2.1)) ∧
      MainB_R Γ Γ' (liftA 1) L' (Q' ++ [(.G ch, p.2.1, x), (.G ch, x, bb)])

/-- The obligation of a term of an operation on `H` inside `P_x`: one more internal atom, joined to
`x` by a waved edge; the waved and dotted edges of `H` lifted; `MainB_Out` for every graph with
those waved and dotted edges. -/
private def MainB_Good (Γ : Graph 3 n) (x : Atom 3 n) (Q : List (Kind × Atom 3 n × Atom 3 n))
    (t₀ : Tracked 3 n) : Prop :=
  ∃ (cs : List (Comp (Atom 3 (n + 1)))) (co : Coeff), t₀ = ⟨n + 1, ⟨cs, co⟩, liftA 1⟩ ∧
    ((cs.map MainB_st).filter fun p => p.1.joinsMol).Perm
      ((Q.filter fun p => p.1.joinsMol).map MainB_lT ++ [(.waved .s, liftA 1 x, newA 0)]) ∧
    ∀ Γ' : Graph 3 (n + 1), MainB_Corr Γ Γ' (liftA 1) → Γ'.SameMol (newA 0) (liftA 1 x) →
      MainB_Out Γ Γ' x (cs.map MainB_st) Q

private theorem MainB_joinsMol_conj (κ : Kind) : κ.conj.joinsMol = κ.joinsMol := by
  rcases κ with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
    first | (cases ch <;> rfl) | (cases w <;> rfl) | rfl

private theorem MainB_filter_cT {m : ℕ} (L : List (Kind × Atom 3 m × Atom 3 m)) :
    (L.map MainB_cT).filter (fun p => p.1.joinsMol) =
      (L.filter fun p => p.1.joinsMol).map MainB_cT := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp [MainB_cT, MainB_joinsMol_conj]

private theorem MainB_isRandom_conj (κ : Kind) : κ.conj.isRandom = κ.isRandom := by
  rcases κ with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
    first | (cases ch <;> rfl) | (cases w <;> rfl) | rfl

/-- A term of an operation on the complex conjugate graph, conjugated back. -/
private theorem MainB_good_conj {Γ : Graph 3 n} {x : Atom 3 n}
    {Q : List (Kind × Atom 3 n × Atom 3 n)} {t₀ : Tracked 3 n}
    (h : MainB_Good Γ x (Q.map MainB_cT) t₀) :
    MainB_Good Γ x Q ⟨t₀.nOut, t₀.g.conj, t₀.f⟩ := by
  obtain ⟨cs, co, rfl, hJ, hO⟩ := h
  have hst : (cs.map fun c => { c with kind := c.kind.conj }).map MainB_st =
      (cs.map MainB_st).map MainB_cT := by
    simp [MainB_st, MainB_cT, Function.comp_def]
  refine ⟨cs.map fun c => { c with kind := c.kind.conj }, Coeff.conj co, rfl, ?_, ?_⟩
  · rw [hst, MainB_filter_cT]
    have := hJ.map MainB_cT
    rw [MainB_filter_cT, List.map_append] at this
    refine this.trans (List.Perm.of_eq ?_)
    have e : ∀ L : List (Kind × Atom 3 n × Atom 3 n),
        ((L.map MainB_cT).map MainB_lT).map MainB_cT = L.map MainB_lT := by
      intro L
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun p _ => by simp [MainB_cT, MainB_lT, MainB_conj_conj]
    rw [e]
    rfl
  · intro Γ' hC hα
    rw [hst]
    rcases hO Γ' hC hα with h | ⟨p, Q', ch, bb, hp, hr, hcase, hR⟩
    · left
      have := MainB_R_conj h
      rwa [MainB_map_cT_cT] at this
    · right
      refine ⟨MainB_cT p, Q'.map MainB_cT, ch.flip, bb, ?_, ?_, ?_, ?_⟩
      · have := hp.map MainB_cT
        rwa [MainB_map_cT_cT, List.map_cons] at this
      · simpa [MainB_cT, MainB_isRandom_conj] using hr
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by simp [MainB_cT, h1, Kind.conj], h2⟩
        · exact Or.inr ⟨by simp [MainB_cT, MainB_mclass_conj, h1], h2⟩
      · have := MainB_R_conj hR
        rw [List.map_append] at this
        refine MainB_R_perm (List.Perm.refl _) (List.Perm.of_eq ?_) this
        simp [MainB_cT, Kind.conj]

/-- `Graph.FlatCarried` from `Γ` to a term of `pLiftT` whose term on `Γ.pCore` has the
obligation `MainB_Good`. -/
private theorem MainB_P_final {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true)
    (hCB : Γ.ColourInvB) {t₀ : Tracked 3 n}
    (h : MainB_Good Γ x (Γ.pCore.comps.map MainB_st) t₀) :
    Γ.FlatCarried (⟨t₀.nOut, ⟨t₀.g.comps.map (fun c =>
        if c.kind.isRandom then { c with label := some (.P, t₀.f x) } else c) ++
      Γ.pEnv.map (Comp.map t₀.f), t₀.g.coeff⟩, t₀.f⟩ : Tracked 3 n).g := by
  obtain ⟨cs, co, rfl, hJ, hO⟩ := h
  dsimp only
  set Γ' : Graph 3 (n + 1) := ⟨cs.map (fun c => if c.kind.isRandom then
    { c with label := some (.P, liftA 1 x) } else c) ++ Γ.pEnv.map (Comp.map (liftA 1)), co⟩
    with hΓ'
  have hst : Γ'.comps.map MainB_st = cs.map MainB_st ++ (Γ.pEnv.map MainB_st).map MainB_lT := by
    simp only [hΓ', List.map_append, MainB_st_rl]
    congr 1
    simp [MainB_st, MainB_lT, Comp.map, Function.comp_def]
  have hEnv : ((Γ.pEnv.map MainB_st).map MainB_lT).filter (fun p => p.1.joinsMol) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    have := (List.mem_filter.1 hc).2
    simp only [Bool.and_eq_true] at this
    have hr := this.2
    simp only [MainB_lT, MainB_st]
    rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
      rw [hk] at hr <;> simp_all [Kind.isRandom, Kind.joinsMol]
  have hJ' : ((Γ'.comps.map MainB_st).filter fun p => p.1.joinsMol).Perm
      (((Γ.comps.map MainB_st).filter fun p => p.1.joinsMol).map MainB_lT ++
        [(.waved .s, liftA 1 x, newA 0)]) := by
    rw [hst, List.filter_append, hEnv, List.append_nil, ← MainB_jm_pCore]
    exact hJ
  obtain ⟨hC, hα⟩ := MainB_corr_of_jm hx hJ'
  have hEnvR : MainB_R Γ Γ' (liftA 1) ((Γ.pEnv.map MainB_st).map MainB_lT)
      (Γ.pEnv.map MainB_st) := MainB_R_lift hC _
  rcases hO Γ' hC hα with hR | ⟨p, Q', ch, bb, hp, hr, hcase, hR⟩
  · refine MainB_flat_iso hC ?_
    have := MainB_R_append hR hEnvR
    rw [← hst] at this
    exact MainB_R_perm (List.Perm.refl _) (MainB_perm_pCore Γ).symm this
  · -- the split component of `Γ`
    have hpm : p ∈ Γ.pCore.comps.map MainB_st := hp.mem_iff.2 (List.mem_cons_self ..)
    obtain ⟨c₁, hc₁, e₁⟩ := List.mem_map.1 hpm
    obtain ⟨c₀, hc₀, e₀⟩ := MainB_mem_pCore hc₁
    obtain ⟨k, hk, hck⟩ := List.getElem_of_mem hc₀
    have hc₀k : Γ.comps[k]? = some c₀ := by rw [List.getElem?_eq_getElem hk, hck]
    have hst₀ : MainB_st c₀ = p := e₀.trans e₁
    have hk₀ : c₀.kind = p.1 := congrArg Prod.fst hst₀
    have hx₀ : c₀.x = p.2.1 := congrArg (fun q => q.2.1) hst₀
    have hy₀ : c₀.y = p.2.2 := congrArg (fun q => q.2.2) hst₀
    have hcase₀ : (c₀.kind = .G ch ∧ bb = c₀.y) ∨ (c₀.kind.mclass = none ∧ bb = c₀.x) := by
      rw [hk₀, hx₀, hy₀]; exact hcase
    have hcx := MainB_colour hCB hc₀ (by rw [hk₀]; exact hr)
    obtain ⟨G₁, hch, hGi, hGe, hGv, hGpm⟩ := MainB_src_split hc₀k ch bb x hx hcase₀ hcx
    refine MainB_flat_chain hC G₁ hch hGi hGe hGv _ hGpm ?_
    have h1 := MainB_R_append hR hEnvR
    rw [← hst] at h1
    refine MainB_R_perm (List.Perm.refl _) ?_ h1
    have e2 : (Γ.comps.map MainB_st).Perm (p :: (Γ.comps.eraseIdx k).map MainB_st) := by
      have := (List.getElem_cons_eraseIdx_perm hk).symm.map MainB_st
      rw [hck, List.map_cons, hst₀] at this
      exact this
    have e3 : (Γ.comps.map MainB_st).Perm (p :: (Q' ++ Γ.pEnv.map MainB_st)) :=
      (MainB_perm_pCore Γ).trans ((hp.append_right _).trans (List.Perm.refl _))
    have e4 : ((Γ.comps.eraseIdx k).map MainB_st).Perm (Q' ++ Γ.pEnv.map MainB_st) :=
      (e2.symm.trans e3).cons_inv
    rw [hx₀]
    refine List.perm_iff_count.2 fun a => ?_
    have := e4.count_eq a
    simp only [List.count_append] at this ⊢
    omega

/-! ### `-∂_{h_{pq}}` and [II, (4.23)] inside `P_x` -/

private theorem MainB_mem_dTerms {V : Type} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    {d : List (Comp V)} (hd : d ∈ dTerms p q cs) :
    ∃ m : Fin cs.length, ∃ ps, cs[m].dPieces p q = some ps ∧ d = cs.eraseIdx m ++ ps := by
  unfold dTerms at hd
  obtain ⟨m, -, hm⟩ := List.mem_filterMap.1 hd
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hm
  exact ⟨m, ps, hps, rfl⟩

private theorem MainB_dPieces_eq {V : Type} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) :
    ∃ ch : Charge, (c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧
      ps = [solidC ch c.x (if ch = .plus then p else q),
        solidC ch (if ch = .plus then q else p) (if c.kind.isWeight then c.x else c.y)] := by
  unfold Comp.dPieces at h
  rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
    simp only [hk] at h
  all_goals first | cases h | (cases ch <;> simp only at h <;> cases h <;> simp [Kind.isWeight])

private theorem MainB_filter_lT (L : List (Kind × Atom 3 n × Atom 3 n)) :
    (L.map MainB_lT).filter (fun p => p.1.joinsMol) =
      (L.filter fun p => p.1.joinsMol).map MainB_lT := by
  rw [List.filter_map]
  rfl

/-- A component that is not a waved or dotted edge does not change the waved and dotted edges. -/
private theorem MainB_filter_perm {m : ℕ} {L : List (Kind × Atom 3 m × Atom 3 m)}
    {p : Kind × Atom 3 m × Atom 3 m} {L' : List (Kind × Atom 3 m × Atom 3 m)}
    (h : L.Perm (p :: L')) (hp : p.1.joinsMol = false) :
    (L.filter fun p => p.1.joinsMol).Perm (L'.filter fun p => p.1.joinsMol) := by
  refine (h.filter _).trans ?_
  rw [List.filter_cons_of_neg (by simp [hp])]

/-- The terms of `-∂_{h_{PQ}}` of a lifted product, at atoms `P`, `Q` of the molecule of `x`: one
random component split through `x`. -/
private theorem MainB_dTerms_lift {Γ : Graph 3 n} {x : Atom 3 n} {P Q : Atom 3 (n + 1)}
    (L : List (Comp (Atom 3 n))) {d : List (Comp (Atom 3 (n + 1)))}
    (hd : d ∈ dTerms P Q (liftCs 1 L)) :
    ∃ (m : ℕ) (hm : m < L.length) (ch : Charge) (bb : Atom 3 n)
      (ps : List (Comp (Atom 3 (n + 1)))),
      d = liftCs 1 (L.eraseIdx m) ++ ps ∧ L[m].kind.isRandom = true ∧
      ((L[m].kind = .G ch ∧ bb = L[m].y) ∨ (L[m].kind.mclass = none ∧ bb = L[m].x)) ∧
      (ps.map MainB_st).filter (fun p => p.1.joinsMol) = [] ∧
      ∀ Γ' : Graph 3 (n + 1), MainB_Corr Γ Γ' (liftA 1) → MainB_va Γ Γ' (liftA 1) P x →
        MainB_va Γ Γ' (liftA 1) Q x →
        MainB_R Γ Γ' (liftA 1) (ps.map MainB_st) [(.G ch, L[m].x, x), (.G ch, x, bb)] := by
  obtain ⟨m, ps, hps, rfl⟩ := MainB_mem_dTerms hd
  have hm : m.1 < L.length := by simpa [liftCs] using m.2
  have hcm : (liftCs 1 L)[m] = (L[m.1]'hm).map (liftA 1) := by
    rw [Fin.getElem_fin]; unfold liftCs; rw [List.getElem_map]
  have he : (liftCs 1 L).eraseIdx m = liftCs 1 (L.eraseIdx m) := by
    simp [liftCs, List.eraseIdx_map]
  rw [hcm] at hps
  obtain ⟨ch, hk, rfl⟩ := MainB_dPieces_eq hps
  set c := L[m.1]'hm with hc
  have hkc : c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch := hk
  refine ⟨m, hm, ch, if c.kind.isWeight then c.x else c.y, _, by rw [he], ?_, ?_, ?_, ?_⟩
  · rcases hkc with h | h | h <;> rw [h] <;> rfl
  · rcases hkc with h | h | h
    · left
      have e : (if c.kind.isWeight then c.x else c.y) = c.y := by simp [h, Kind.isWeight]
      exact ⟨h, e⟩
    · right
      have e : (if c.kind.isWeight then c.x else c.y) = c.x := by simp [h, Kind.isWeight]
      exact ⟨by rw [h]; rfl, e⟩
    · right
      have e : (if c.kind.isWeight then c.x else c.y) = c.x := by simp [h, Kind.isWeight]
      exact ⟨by rw [h]; rfl, e⟩
  · rw [List.filter_eq_nil_iff]
    intro p hp
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (unfold solidC; split_ifs <;> simp [MainB_st, mkC, Kind.joinsMol])
  · intro Γ' hC hP hQ
    have hx1 : ∀ u : Atom 3 n, MainB_va Γ Γ' (liftA 1) (liftA 1 u) u := MainB_va_map hC
    have hk' : (c.map (liftA 1)).kind = c.kind := rfl
    simp only [hk'] at *
    change MainB_R Γ Γ' (liftA 1) ([MainB_st _] ++ [MainB_st _]) ([_] ++ [_])
    refine MainB_R_append (MainB_R_solidC hC ch (hx1 c.x) ?_) (MainB_R_solidC hC ch ?_ ?_)
    · split_ifs <;> assumption
    · split_ifs <;> assumption
    · split_ifs
      · exact hx1 c.x
      · exact hx1 c.y

/-- The new atom and the image of `x`: atoms of the molecule of `x`. -/
private theorem MainB_va_new {Γ : Graph 3 n} {Γ' : Graph 3 (n + 1)} {x : Atom 3 n}
    (hx : x.isRight = true) (hC : MainB_Corr Γ Γ' (liftA 1))
    (hα : Γ'.SameMol (newA 0) (liftA 1 x)) : MainB_va Γ Γ' (liftA 1) (newA 0) x :=
  MainB_va_mol hC rfl hx hα

/-- Two atoms of `Γ'` with the molecule of `x`: no edge between them. -/
private theorem MainB_edS_va {Γ : Graph 3 n} {Γ' : Graph 3 (n + 1)} {x : Atom 3 n} {κ : Kind}
    {u v : Atom 3 (n + 1)} (hu : MainB_va Γ Γ' (liftA 1) u x) (hv : MainB_va Γ Γ' (liftA 1) v x) :
    MainB_edS Γ' (κ, u, v) = none :=
  MainB_edS_same (hu.trans hv.symm)

/-- [II, (4.23)] at the first light weight of positive charge on `x`. -/
private theorem MainB_good_wP2Pos {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true)
    {H : Graph 3 n} {E : TExpansion 3 n} (hE : oWeightP2Pos x H = some E) :
    ∀ t₀ ∈ E, MainB_Good Γ x (H.comps.map MainB_st) t₀ := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i hi
  dsimp only at hE
  obtain rfl := Option.some.inj hE
  obtain ⟨hil, hik, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hik
  set w := MainB_st H.comps[i] with hw
  have hwk : w.1 = .light .plus := hik.1
  have hperm : (H.comps.map MainB_st).Perm (w :: (H.comps.eraseIdx i).map MainB_st) := by
    have := (List.getElem_cons_eraseIdx_perm hil).symm.map MainB_st
    simpa using this
  have hwj : w.1.joinsMol = false := by rw [hwk]; rfl
  have hwe : MainB_edS Γ w = none := MainB_edS_none Γ (by rw [hwk]; rfl)
  have hjm := MainB_filter_perm hperm hwj
  have hnew : ∀ Γ' : Graph 3 (n + 1), MainB_Corr Γ Γ' (liftA 1) →
      Γ'.SameMol (newA 0) (liftA 1 x) →
      MainB_va Γ Γ' (liftA 1) (newA 0) x ∧ MainB_va Γ Γ' (liftA 1) (liftA 1 x) x :=
    fun Γ' hC hα => ⟨MainB_va_new hx hC hα, MainB_va_map hC x⟩
  intro t₀ ht₀
  rw [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map] at ht₀
  rcases ht₀ with (rfl | rfl) | ⟨d, hd, rfl⟩
  · refine ⟨_, _, rfl, ?_, fun Γ' hC hα => Or.inl ?_⟩
    · rw [List.map_append, MainB_st_liftCs, List.filter_append, MainB_filter_lT]
      refine List.Perm.append ((hjm.symm.map _)) ?_
      simp [MainB_st, mkC, Kind.joinsMol]
    · rw [List.map_append, MainB_st_liftCs]
      refine MainB_R_perm (List.Perm.refl _) (List.perm_append_comm.trans hperm.symm)
        (MainB_R_absR (N := [w]) (by simpa using hwe)
          (MainB_R_absL (fun p hp => ?_) (MainB_R_lift hC _)))
      simp only [MainB_st, mkC, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl <;> exact MainB_edS_none Γ' rfl
  · refine ⟨_, _, rfl, ?_, fun Γ' hC hα => Or.inl ?_⟩
    · rw [List.map_append, MainB_st_liftCs, List.filter_append, MainB_filter_lT]
      refine List.Perm.append (List.Perm.refl _) ?_
      simp [MainB_st, mkC, Kind.joinsMol]
    · rw [List.map_append, MainB_st_liftCs]
      refine MainB_R_absL (fun p hp => ?_) (MainB_R_lift hC _)
      simp only [MainB_st, mkC, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl <;> exact MainB_edS_none Γ' rfl
  · obtain ⟨m, hm, ch, bb, ps, rfl, hr, hcase, hpj, hpR⟩ :=
      MainB_dTerms_lift (Γ := Γ) (x := x) (H.comps.eraseIdx i) hd
    have hpermL : ((H.comps.eraseIdx i).map MainB_st).Perm (MainB_st (H.comps.eraseIdx i)[m] ::
        ((H.comps.eraseIdx i).eraseIdx m).map MainB_st) := by
      have := (List.getElem_cons_eraseIdx_perm hm).symm.map MainB_st
      simpa using this
    have hLj : (MainB_st (H.comps.eraseIdx i)[m]).1.joinsMol = false := by
      have : (H.comps.eraseIdx i)[m].kind.joinsMol = false := by
        rcases hk : (H.comps.eraseIdx i)[m].kind with
          ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
          rw [hk] at hr <;> first | rfl | simp [Kind.isRandom] at hr
      exact this
    refine ⟨_, _, rfl, ?_, fun Γ' hC hα => Or.inr ?_⟩
    · rw [List.map_append, List.map_append, MainB_st_liftCs, List.filter_append,
        List.filter_append, hpj, MainB_filter_lT, List.append_nil]
      refine List.Perm.append ((hjm.trans (MainB_filter_perm hpermL hLj)).symm.map _) ?_
      simp [MainB_st, mkC, Kind.joinsMol]
    · obtain ⟨hn, hx1⟩ := hnew Γ' hC hα
      refine ⟨MainB_st (H.comps.eraseIdx i)[m],
        w :: ((H.comps.eraseIdx i).eraseIdx m).map MainB_st, ch, bb, ?_, hr, hcase, ?_⟩
      · exact hperm.trans ((List.Perm.cons _ hpermL).trans (List.Perm.swap _ _ _))
      · rw [List.map_append, List.map_append, MainB_st_liftCs]
        have h1 := MainB_R_append
          (MainB_R_lift hC (((H.comps.eraseIdx i).eraseIdx m).map MainB_st)) (hpR Γ' hC hn hx1)
        have h2 := MainB_R_absL (N := [MainB_st (mkC (.waved .s) (liftA 1 x) (newA 0)),
          MainB_st (mkC (.G .plus) (newA 0) (liftA 1 x))]) (fun p hp => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl
            · exact MainB_edS_none Γ' rfl
            · exact MainB_edS_va hn hx1) h1
        have h3 := MainB_R_absR (N := [w]) (by simpa using hwe) h2
        refine MainB_R_perm (List.Perm.refl _) ?_ h3
        refine List.perm_iff_count.2 fun a => ?_
        simp only [List.count_append, List.count_cons, List.count_nil, MainB_st]
        omega

/-- `x` is internal on a graph `Γ_ω P_x(𝒢)` with internal label atoms. -/
private theorem MainB_x_int {Γ : Graph 3 n} {x : Atom 3 n} (hL : Γ.LabelsInt)
    (hP : Γ.IsPFormAt x) : x.isRight = true := by
  obtain ⟨c, hc, hl⟩ := hP.1
  have := hL c hc
  rw [hl] at this
  simpa using this

private theorem MainB_st_conj (H : Graph 3 n) :
    H.conj.comps.map MainB_st = (H.comps.map MainB_st).map MainB_cT := by
  simp [Graph.conj, MainB_st, MainB_cT, Function.comp_def]

/-- [II, (4.23)] inside `P_x`. -/
private theorem MainB_pWeight2 {Γ : Graph 3 n} {x : Atom 3 n} {t : Tracked 3 n}
    (hI : Γ.InvB') (hP : Γ.IsPFormAt x) (ht : t ∈ oWeightP2T x Γ) : Γ.FlatCarried t.g := by
  have hx := MainB_x_int hI.2.2.2.2 hP
  unfold oWeightP2T at ht
  split at ht
  · rename_i E hE
    obtain ⟨t₀, ht₀, rfl⟩ := MainB_mem_pLift ht
    exact MainB_P_final hx hI.2.1 (MainB_good_wP2Pos hx hE t₀ ht₀)
  · split at ht
    · rename_i E hE
      obtain ⟨t₀, ht₀, rfl⟩ := MainB_mem_pLift ht
      obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.1 ht₀
      have h1 := MainB_good_wP2Pos (Γ := Γ) hx hE t₁ ht₁
      rw [MainB_st_conj] at h1
      exact MainB_P_final hx hI.2.1 (MainB_good_conj h1)
    · rw [List.mem_singleton] at ht
      subst ht
      exact MainB_refl Γ

/-! ### [II, (4.24)] inside `P_x` -/

/-- An obligation `MainB_Good` from a description of the components: `K` lifted and `N`, where `N`
gives the edges of `M` and has the waved edge to the new atom as its only waved or dotted edge. -/
private theorem MainB_good_iso {Γ : Graph 3 n} {x : Atom 3 n}
    {Q K M : List (Kind × Atom 3 n × Atom 3 n)} {N : List (Kind × Atom 3 (n + 1) × Atom 3 (n + 1))}
    (hQ : Q.Perm (K ++ M)) (hMj : M.filter (fun p => p.1.joinsMol) = [])
    (hNj : N.filter (fun p => p.1.joinsMol) = [(.waved .s, liftA 1 x, newA 0)])
    (hR : ∀ Γ' : Graph 3 (n + 1), MainB_Corr Γ Γ' (liftA 1) →
      MainB_va Γ Γ' (liftA 1) (newA 0) x → MainB_R Γ Γ' (liftA 1) N M)
    (hx : x.isRight = true) {cs : List (Comp (Atom 3 (n + 1)))}
    (hcs : cs.map MainB_st = K.map MainB_lT ++ N) (co : Coeff) :
    MainB_Good Γ x Q ⟨n + 1, ⟨cs, co⟩, liftA 1⟩ := by
  refine ⟨cs, co, rfl, ?_, fun Γ' hC hα => Or.inl ?_⟩
  · rw [hcs, List.filter_append, MainB_filter_lT, hNj]
    refine List.Perm.append (List.Perm.map _ ?_) (List.Perm.refl _)
    refine ((hQ.filter _).trans ?_).symm
    rw [List.filter_append, hMj, List.append_nil]
  · rw [hcs]
    exact MainB_R_perm (List.Perm.refl _) hQ.symm
      (MainB_R_append (MainB_R_lift hC K) (hR Γ' hC (MainB_va_new hx hC hα)))

/-- An obligation `MainB_Good` with one random component `p` split through `x`. -/
private theorem MainB_good_split {Γ : Graph 3 n} {x : Atom 3 n}
    {Q K M : List (Kind × Atom 3 n × Atom 3 n)} {N : List (Kind × Atom 3 (n + 1) × Atom 3 (n + 1))}
    {p : Kind × Atom 3 n × Atom 3 n} {ch : Charge} {bb : Atom 3 n}
    (hQ : Q.Perm (p :: (K ++ M))) (hr : p.1.isRandom = true)
    (hcase : (p.1 = .G ch ∧ bb = p.2.2) ∨ (p.1.mclass = none ∧ bb = p.2.1))
    (hMj : M.filter (fun p => p.1.joinsMol) = [])
    (hNj : N.filter (fun p => p.1.joinsMol) = [(.waved .s, liftA 1 x, newA 0)])
    (hR : ∀ Γ' : Graph 3 (n + 1), MainB_Corr Γ Γ' (liftA 1) →
      MainB_va Γ Γ' (liftA 1) (newA 0) x →
      MainB_R Γ Γ' (liftA 1) N (M ++ [(.G ch, p.2.1, x), (.G ch, x, bb)]))
    (hx : x.isRight = true) {cs : List (Comp (Atom 3 (n + 1)))}
    (hcs : cs.map MainB_st = K.map MainB_lT ++ N) (co : Coeff) :
    MainB_Good Γ x Q ⟨n + 1, ⟨cs, co⟩, liftA 1⟩ := by
  have hpj : p.1.joinsMol = false := by
    rcases hk : p.1 with ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
      rw [hk] at hr <;> first | rfl | simp [Kind.isRandom] at hr
  refine ⟨cs, co, rfl, ?_, fun Γ' hC hα => Or.inr ⟨p, K ++ M, ch, bb, hQ, hr, hcase, ?_⟩⟩
  · rw [hcs, List.filter_append, MainB_filter_lT, hNj]
    refine List.Perm.append (List.Perm.map _ ?_) (List.Perm.refl _)
    refine ((MainB_filter_perm hQ hpj).trans ?_).symm
    rw [List.filter_append, hMj, List.append_nil]
  · rw [hcs, List.append_assoc]
    exact MainB_R_append (MainB_R_lift hC K) (hR Γ' hC (MainB_va_new hx hC hα))

/-- The obligation depends only on the kinds and ends of the components. -/
private theorem MainB_good_st {Γ : Graph 3 n} {x : Atom 3 n} {Q : List (Kind × Atom 3 n × Atom 3 n)}
    {cs cs' : List (Comp (Atom 3 (n + 1)))} (h : cs'.map MainB_st = cs.map MainB_st)
    (co co' : Coeff) (hg : MainB_Good Γ x Q ⟨n + 1, ⟨cs, co⟩, liftA 1⟩) :
    MainB_Good Γ x Q ⟨n + 1, ⟨cs', co'⟩, liftA 1⟩ := by
  obtain ⟨cs₀, co₀, e, hJ, hO⟩ := hg
  simp only [Tracked.mk.injEq, heq_eq_eq, Graph.mk.injEq, true_and] at e
  obtain ⟨⟨rfl, rfl⟩, -⟩ := e
  exact ⟨cs', co', rfl, h ▸ hJ, fun Γ' hC hα => h ▸ hO Γ' hC hα⟩

private theorem MainB_st_labelQs {m : ℕ} (u : Atom 3 m) (cs : List (Comp (Atom 3 m))) :
    (labelQs u cs).map MainB_st = cs.map MainB_st := by
  unfold labelQs
  exact MainB_map_st_eq _ fun c _ => by simp only [Comp.labelQ, MainB_st]; split_ifs <;> rfl

private theorem MainB_mem_edgeIdx {H : Graph 3 n} {x : Atom 3 n} {ch : Charge} {out : Bool} {j : ℕ}
    (h : j ∈ H.edgeIdx x ch out) :
    ∃ hj : j < H.comps.length, H.comps[j].kind = .G ch ∧
      (if out then H.comps[j].x = x ∧ H.comps[j].y ≠ x
        else H.comps[j].y = x ∧ H.comps[j].x ≠ x) := by
  unfold Graph.edgeIdx at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨hpz, hpp⟩ := List.mem_filter.1 hp
  obtain ⟨hlt, hpe⟩ := List.mem_zipIdx' (x := p.1) (i := p.2) hpz
  refine ⟨hlt, ?_⟩
  rw [← hpe]
  simp only [Bool.and_eq_true, beq_iff_eq] at hpp
  refine ⟨hpp.1, ?_⟩
  cases out <;> simpa using hpp.2

private theorem MainB_getD_of_lt {α : Type} {L : List α} {j : ℕ} (h : j < L.length) (d : α) :
    L.getD j d = L[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

private theorem MainB_perm_pick_erase {α : Type} (is : List ℕ) (L : List α) :
    L.Perm (pickIdxs is L ++ eraseIdxs is L) := by
  unfold pickIdxs eraseIdxs
  rw [← List.map_append]
  conv_lhs => rw [← List.zipIdx_map_fst 0 L]
  exact ((List.filter_append_perm _ _).map Prod.fst).symm

private theorem MainB_pick_split {α : Type} (is : List ℕ) (P : ℕ → Bool) (L : List α) :
    (pickIdxs is L).Perm (pickIdxs (is.filter P) L ++ pickIdxs (is.filter fun i => !P i) L) := by
  unfold pickIdxs
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have h1 := List.filter_append_perm (fun p : α × ℕ => P p.2)
    (L.zipIdx.filter fun p => is.contains p.2)
  rw [List.filter_filter, List.filter_filter] at h1
  refine h1.symm.trans (List.Perm.of_eq ?_)
  congr 1 <;> apply List.filter_congr <;> intro p _ <;> simp [Bool.and_comm]

private theorem MainB_zipIdx_filter_single {α : Type} (L : List α) (k i : ℕ) (h1 : k ≤ i)
    (h2 : i < k + L.length) :
    ((L.zipIdx k).filter fun p => [i].contains p.2).map Prod.fst = [L[i - k]'(by omega)] := by
  induction L generalizing k with
  | nil => simp at h2; omega
  | cons a L ih =>
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases hk : k = i
    · subst hk
      have : (L.zipIdx (k + 1)).filter (fun p => [k].contains p.2) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        have := List.le_snd_of_mem_zipIdx hp
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq]
        omega
      rw [show ([k].contains k) = true by simp]
      simp only [↓reduceIte, this, List.map_cons, List.map_nil, Nat.sub_self,
        List.getElem_cons_zero]
    · have hki : k + 1 ≤ i := by omega
      have hne : ([i].contains k) = false := by simp; omega
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (k + 1) hki (by simp at h2; omega)]
      simp only [List.cons.injEq, and_true]
      rw [List.getElem_cons]
      split_ifs with h0
      · omega
      · congr 1

private theorem MainB_pick_single {α : Type} {L : List α} {i : ℕ} (hi : i < L.length) :
    pickIdxs [i] L = [L[i]] := by
  unfold pickIdxs
  rw [MainB_zipIdx_filter_single L 0 i (Nat.zero_le _) (by omega)]
  simp only [Nat.sub_zero]

private theorem MainB_pick_congr {α : Type} {is js : List ℕ} (L : List α)
    (h : ∀ i, i ∈ is ↔ i ∈ js) : pickIdxs is L = pickIdxs js L := by
  unfold pickIdxs
  congr 1
  exact List.filter_congr fun p _ => by simp [h]

/-- Two components removed at distinct indices. -/
private theorem MainB_perm_two {α : Type} {L : List α} {i j : ℕ} (hij : i ≠ j)
    (hi : i < L.length) (hj : j < L.length) : L.Perm (L[i] :: L[j] :: eraseIdxs [i, j] L) := by
  refine (MainB_perm_pick_erase [i, j] L).trans ?_
  have h1 := MainB_pick_split [i, j] (· == i) L
  have e1 : [i, j].filter (· == i) = [i] := by simp [Ne.symm hij]
  have e2 : [i, j].filter (fun k => !(k == i)) = [j] := by simp [Ne.symm hij]
  rw [e1, e2, MainB_pick_single hi, MainB_pick_single hj] at h1
  exact (h1.append_right _).trans (List.Perm.refl _)

/-- The indices `xIdx` with `i₁` among them: the component `i₁`, the other picked components and
the remaining ones. -/
private theorem MainB_perm_xIdx {α : Type} {L : List α} {xIdx : List ℕ} {i₁ : ℕ}
    (hi : i₁ < L.length) (hx : i₁ ∈ xIdx) :
    L.Perm (L[i₁] :: (pickIdxs (xIdx.filter (· != i₁)) L ++ eraseIdxs xIdx L)) := by
  have hpc : ∀ k, k ∈ xIdx.filter (fun i => !(i != i₁)) ↔ k ∈ [i₁] := by
    intro k
    by_cases hk : k = i₁
    · subst hk; simp [hx]
    · simp [hk]
  have e1 := MainB_perm_pick_erase xIdx L
  have e2 := MainB_pick_split xIdx (· != i₁) L
  rw [MainB_pick_congr L hpc, MainB_pick_single hi] at e2
  refine e1.trans ((e2.append_right _).trans ?_)
  rw [List.append_assoc, List.singleton_append]
  exact List.perm_middle

/-- The obligation of a term inside `P_x`: `MainB_Good`, or the term is the graph itself up to
labels, with the same atoms. -/
private def MainB_GoodX (Γ : Graph 3 n) (x : Atom 3 n) (Q : List (Kind × Atom 3 n × Atom 3 n))
    (t₀ : Tracked 3 n) : Prop :=
  MainB_Good Γ x Q t₀ ∨ ∃ (cs : List (Comp (Atom 3 n))) (co : Coeff),
    t₀ = ⟨n, ⟨cs, co⟩, id⟩ ∧ cs.map MainB_st = Q

/-- A solid edge from `α` (in the molecule of `x`) to the image of `v`, and the solid edge from
`x` to `v`. -/
private theorem MainB_R_moved {Γ : Graph 3 n} {Γ' : Graph 3 (n + 1)} {x : Atom 3 n}
    (hC : MainB_Corr Γ Γ' (liftA 1)) (hn : MainB_va Γ Γ' (liftA 1) (newA 0) x) (κ : Kind)
    (v : Atom 3 n) :
    MainB_R Γ Γ' (liftA 1) [(κ, newA 0, liftA 1 v)] [(κ, x, v)] ∧
      MainB_R Γ Γ' (liftA 1) [(κ, liftA 1 v, newA 0)] [(κ, v, x)] :=
  ⟨MainB_R_mkC hC κ hn (MainB_va_map hC v), MainB_R_mkC hC κ (MainB_va_map hC v) hn⟩

/-- The multi-edge expansion [I, (3.13)] at an atom with an edge of charge `plus` leaving it. -/
private theorem MainB_good_multiEOut {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true)
    {H : Graph 3 n} {E : TExpansion 3 n} (hE : multiEOut x H = some E) :
    ∀ t₀ ∈ E, MainB_GoodX Γ x (H.comps.map MainB_st) t₀ := by
  unfold multiEOut at hE
  split at hE
  · cases hE
  rename_i i₁ is₂ hi
  split at hE
  · cases hE
  rename_i e₁ he₁
  dsimp only at hE
  split at hE
  · cases hE
  obtain rfl := Option.some.inj hE
  have hi₁ : i₁ ∈ H.edgeIdx x .plus true := by rw [hi]; exact List.mem_cons_self ..
  obtain ⟨hi₁l, he₁k, he₁x⟩ := MainB_mem_edgeIdx hi₁
  simp only [↓reduceIte] at he₁x
  have he₁e : H.comps[i₁] = e₁ := (List.getElem?_eq_some_iff.1 he₁).2
  rw [he₁e] at he₁k he₁x
  have hs₁ : MainB_st e₁ = (.G .plus, x, e₁.y) := by simp [MainB_st, he₁k, he₁x.1]
  have hQ1 : (H.comps.map MainB_st).Perm ((H.comps.eraseIdx i₁).map MainB_st ++ [MainB_st e₁]) := by
    have := (List.getElem_cons_eraseIdx_perm hi₁l).symm.map MainB_st
    rw [he₁e] at this
    exact this.trans (by simpa using List.perm_append_comm (l₁ := [MainB_st e₁]))
  have hwj : ∀ (u v : Atom 3 (n + 1)),
      ([((.waved .s : Kind), u, v)].filter fun p => p.1.joinsMol) = [((.waved .s : Kind), u, v)] :=
    fun u v => rfl
  have hG : ∀ (ch : Charge) (u v : Atom 3 (n + 1)),
      ([((.G ch : Kind), u, v)].filter fun p => p.1.joinsMol) = [] := fun ch u v => by
    cases ch <;> rfl
  have habs : ∀ {Γ' : Graph 3 (n + 1)} {κ : Kind} (u v : Atom 3 (n + 1)),
      κ.mclass = none → MainB_edS Γ' (κ, u, v) = none := fun u v h => MainB_edS_none _ h
  -- the main terms, with absent extra components `T`
  have gM : ∀ j ∈ H.edgeIdx x .minus true, ∀ T : List (Comp (Atom 3 (n + 1))),
      (∀ c ∈ T, c.kind.mclass = none ∧ c.kind.joinsMol = false) → ∀ co,
      MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨(liftCs 1 (eraseIdxs [i₁, j] H.comps) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e₁.y),
          mkC (.G .minus) (newA 0) (liftA 1 ((H.comps.getD j e₁).y))]) ++ T, co⟩, liftA 1⟩ := by
    intro j hj T hT co
    obtain ⟨hjl, hjk, hjx⟩ := MainB_mem_edgeIdx hj
    simp only [↓reduceIte] at hjx
    have hne : j ≠ i₁ := by
      rintro rfl; rw [he₁e, he₁k] at hjk; cases hjk
    rw [MainB_getD_of_lt hjl]
    have hsj : MainB_st H.comps[j] = (.G .minus, x, H.comps[j].y) := by
      simp [MainB_st, hjk, hjx.1]
    have hTj : (T.map MainB_st).filter (fun p => p.1.joinsMol) = [] :=
      List.filter_eq_nil_iff.2 fun p hp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; simp [MainB_st, (hT c hc).2]
    have hTa : ∀ {Γ' : Graph 3 (n + 1)}, ∀ p ∈ T.map MainB_st, MainB_edS Γ' p = none :=
      fun p hp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; exact MainB_edS_none _ (hT c hc).1
    refine MainB_good_iso (K := (eraseIdxs [i₁, j] H.comps).map MainB_st)
      (M := [MainB_st e₁, MainB_st H.comps[j]])
      (N := [(.waved .s, liftA 1 x, newA 0), (.G .plus, newA 0, liftA 1 e₁.y),
        (.G .minus, newA 0, liftA 1 H.comps[j].y)] ++ T.map MainB_st) ?_ ?_ ?_ ?_ hx ?_ co
    · have := (MainB_perm_two (Ne.symm hne) hi₁l hjl).map MainB_st
      rw [he₁e] at this
      refine this.trans ?_
      MainB_perm
    · rw [hs₁, hsj]; rfl
    · rw [List.filter_append, hTj]; rfl
    · intro Γ' hC hn
      rw [hs₁, hsj]
      have h1 := MainB_R_append (MainB_R_moved hC hn (.G .plus) e₁.y).1
        (MainB_R_moved hC hn (.G .minus) H.comps[j].y).1
      have h2 := MainB_R_absL (N := (.waved .s, liftA 1 x, newA 0) :: T.map MainB_st)
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact habs _ _ rfl
          · exact hTa p hp) h1
      refine MainB_R_perm ?_ (List.Perm.refl _) h2
      MainB_perm
    · rw [List.map_append, List.map_append, MainB_st_liftCs, List.append_assoc]
      rfl
  have gP : ∀ j ∈ H.edgeIdx x .plus false, ∀ T : List (Comp (Atom 3 (n + 1))),
      (∀ c ∈ T, c.kind.mclass = none ∧ c.kind.joinsMol = false) → ∀ co,
      MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨(liftCs 1 (eraseIdxs [i₁, j] H.comps) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e₁.y),
          mkC (.G .plus) (liftA 1 ((H.comps.getD j e₁).x)) (newA 0)]) ++ T, co⟩, liftA 1⟩ := by
    intro j hj T hT co
    obtain ⟨hjl, hjk, hjx⟩ := MainB_mem_edgeIdx hj
    simp only [Bool.false_eq_true, ↓reduceIte] at hjx
    have hne : j ≠ i₁ := by
      rintro rfl; rw [he₁e] at hjx; exact hjx.2 he₁x.1
    rw [MainB_getD_of_lt hjl]
    have hsj : MainB_st H.comps[j] = (.G .plus, H.comps[j].x, x) := by
      simp [MainB_st, hjk, hjx.1]
    have hTj : (T.map MainB_st).filter (fun p => p.1.joinsMol) = [] :=
      List.filter_eq_nil_iff.2 fun p hp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; simp [MainB_st, (hT c hc).2]
    have hTa : ∀ {Γ' : Graph 3 (n + 1)}, ∀ p ∈ T.map MainB_st, MainB_edS Γ' p = none :=
      fun p hp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; exact MainB_edS_none _ (hT c hc).1
    refine MainB_good_iso (K := (eraseIdxs [i₁, j] H.comps).map MainB_st)
      (M := [MainB_st e₁, MainB_st H.comps[j]])
      (N := [(.waved .s, liftA 1 x, newA 0), (.G .plus, newA 0, liftA 1 e₁.y),
        (.G .plus, liftA 1 H.comps[j].x, newA 0)] ++ T.map MainB_st) ?_ ?_ ?_ ?_ hx ?_ co
    · have := (MainB_perm_two (Ne.symm hne) hi₁l hjl).map MainB_st
      rw [he₁e] at this
      refine this.trans ?_
      MainB_perm
    · rw [hs₁, hsj]; rfl
    · rw [List.filter_append, hTj]; rfl
    · intro Γ' hC hn
      rw [hs₁, hsj]
      have h1 := MainB_R_append (MainB_R_moved hC hn (.G .plus) e₁.y).1
        (MainB_R_moved hC hn (.G .plus) H.comps[j].x).2
      have h2 := MainB_R_absL (N := (.waved .s, liftA 1 x, newA 0) :: T.map MainB_st)
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact habs _ _ rfl
          · exact hTa p hp) h1
      refine MainB_R_perm ?_ (List.Perm.refl _) h2
      MainB_perm
    · rw [List.map_append, List.map_append, MainB_st_liftCs, List.append_assoc]
      rfl
  have gL : ∀ co, MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨liftCs 1 H.comps ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)], co⟩,
        liftA 1⟩ := by
    intro co
    refine MainB_good_iso (K := H.comps.map MainB_st) (M := [])
      (N := [(.waved .s, liftA 1 x, newA 0), (.light .plus, newA 0, newA 0)])
      (by simp) rfl rfl (fun Γ' hC hn => ?_) hx ?_ co
    · exact MainB_R_absL (L' := []) (N := [_, _]) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact habs _ _ rfl) MainB_R_nil
    · rw [List.map_append, MainB_st_liftCs]
      rfl
  have g1 : ∀ (κ : Kind) (u v : Atom 3 (n + 1)), (κ = .G .plus ∨ κ = .G .minus) →
      ((u = liftA 1 x ∧ v = newA 0) ∨ (u = newA 0 ∧ v = liftA 1 x)) → ∀ co,
      MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨liftCs 1 (H.comps.eraseIdx i₁) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC κ u v, mkC (.G .plus) (newA 0) (liftA 1 e₁.y)],
          co⟩, liftA 1⟩ := by
    intro κ u v hκ huv co
    refine MainB_good_iso (K := (H.comps.eraseIdx i₁).map MainB_st) (M := [MainB_st e₁])
      (N := [(.waved .s, liftA 1 x, newA 0), (κ, u, v), (.G .plus, newA 0, liftA 1 e₁.y)])
      hQ1 (by rw [hs₁]; rfl) (by rcases hκ with rfl | rfl <;> rfl) (fun Γ' hC hn => ?_) hx ?_ co
    · rw [hs₁]
      have hx1 := MainB_va_map hC x
      have h2 := MainB_R_absL (N := [(.waved .s, liftA 1 x, newA 0), (κ, u, v)]) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact habs _ _ rfl
        · rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact MainB_edS_va hx1 hn
          · exact MainB_edS_va hn hx1) (MainB_R_moved hC hn (.G .plus) e₁.y).1
      refine MainB_R_perm ?_ (List.Perm.refl _) h2
      MainB_perm
    · rw [List.map_append, MainB_st_liftCs]
      rfl
  set xIdx := H.edgeIdx x .plus true ++ H.edgeIdx x .minus true ++ H.edgeIdx x .plus false ++
    H.edgeIdx x .minus false with hxIdx
  have hi₁x : i₁ ∈ xIdx := by simp [xIdx, hi₁]
  have gD : ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs xIdx H.comps)), ∀ co,
      MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨liftCs 1 (pickIdxs (xIdx.filter (· != i₁))
        H.comps) ++ d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 e₁.y)], co⟩, liftA 1⟩ := by
    intro d hd co
    obtain ⟨m, hm, ch, bb, ps, rfl, hr, hcase, hpj, hpR⟩ :=
      MainB_dTerms_lift (Γ := Γ) (x := x) (eraseIdxs xIdx H.comps) hd
    have hpermL : ((eraseIdxs xIdx H.comps).map MainB_st).Perm
        (MainB_st (eraseIdxs xIdx H.comps)[m] ::
          ((eraseIdxs xIdx H.comps).eraseIdx m).map MainB_st) := by
      have := (List.getElem_cons_eraseIdx_perm hm).symm.map MainB_st
      simpa using this
    have hX := (MainB_perm_xIdx hi₁l hi₁x).map MainB_st
    rw [he₁e] at hX
    refine MainB_good_split (p := MainB_st (eraseIdxs xIdx H.comps)[m])
      (K := (pickIdxs (xIdx.filter (· != i₁)) H.comps).map MainB_st ++
        ((eraseIdxs xIdx H.comps).eraseIdx m).map MainB_st)
      (M := [MainB_st e₁]) (N := ps.map MainB_st ++ [(.waved .s, liftA 1 x, newA 0),
        (.G .plus, newA 0, liftA 1 e₁.y)]) ?_ hr hcase (by rw [hs₁]; rfl)
      (by rw [List.filter_append, hpj]; rfl) (fun Γ' hC hn => ?_) hx ?_ co
    · refine hX.trans ?_
      have h2 := hpermL
      rw [List.perm_iff_count] at h2 ⊢
      intro a
      have := h2 a
      simp only [List.count_append, List.count_cons, List.count_nil, List.map_append,
        List.map_cons, MainB_st] at this ⊢
      omega
    · rw [hs₁]
      have h1 := MainB_R_append (hpR Γ' hC hn (MainB_va_map hC x))
        (MainB_R_absL (N := [(.waved .s, liftA 1 x, newA 0)]) (fun p hp => by
          rw [List.mem_singleton] at hp; subst hp; exact habs _ _ rfl)
          (MainB_R_moved hC hn (.G .plus) e₁.y).1)
      refine MainB_R_perm ?_ ?_ h1
      · MainB_perm
      · MainB_perm
    · simp only [List.map_append, MainB_st_liftCs, List.append_assoc]
      rfl
  intro t₀ ht₀
  simp only [List.mem_append, List.mem_map, List.mem_singleton, List.mem_ite_nil_left,
    or_assoc] at ht₀
  have hW : ∀ ch : Charge, ∀ c ∈ [mkC (.weight ch) (liftA 1 x) (liftA 1 x : Atom 3 (n + 1))],
      c.kind.mclass = none ∧ c.kind.joinsMol = false := by
    intro ch c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨rfl, rfl⟩
  have hLi : ∀ ch : Charge, ∀ c ∈ [mkC (.light ch) (liftA 1 x) (liftA 1 x : Atom 3 (n + 1))],
      c.kind.mclass = none ∧ c.kind.joinsMol = false := by
    intro ch c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨rfl, rfl⟩
  have hnil : ∀ c ∈ ([] : List (Comp (Atom 3 (n + 1)))),
      c.kind.mclass = none ∧ c.kind.joinsMol = false := fun c hc => absurd hc (List.not_mem_nil)
  rcases ht₀ with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩
  · left; have := gM j hj [] hnil (cm * cmb * H.coeff); rwa [List.append_nil] at this
  · left; have := gP j hj [] hnil (cm * cm * H.coeff); rwa [List.append_nil] at this
  · left; exact gM j hj _ (hLi _) _
  · left; exact gP j hj _ (hLi _) _
  · left; exact gL _
  · left; exact g1 _ _ _ (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩) _
  · left; exact g1 _ _ _ (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩) _
  · left; exact gD d hd _
  · right; exact ⟨_, _, rfl, MainB_st_labelQs x H.comps⟩
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gM j hj _ (hW _) (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gP j hj _ (hW _) (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gL (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _
      (g1 _ _ _ (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩) (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _
      (g1 _ _ _ (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩) (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gD d hd (cm * H.coeff))

/-- The multi-edge expansion [I, (3.14)] at an atom with an edge of charge `plus` entering it. -/
private theorem MainB_good_multiEIn {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true)
    {H : Graph 3 n} {E : TExpansion 3 n} (hE : multiEIn x H = some E) :
    ∀ t₀ ∈ E, MainB_GoodX Γ x (H.comps.map MainB_st) t₀ := by
  unfold multiEIn at hE
  split at hE
  · cases hE
  rename_i i₁ is₂ hi
  split at hE
  · cases hE
  rename_i e₁ he₁
  dsimp only at hE
  split at hE
  · cases hE
  obtain rfl := Option.some.inj hE
  have hi₁ : i₁ ∈ H.edgeIdx x .plus false := by rw [hi]; exact List.mem_cons_self ..
  obtain ⟨hi₁l, he₁k, he₁x⟩ := MainB_mem_edgeIdx hi₁
  simp only [Bool.false_eq_true, ↓reduceIte] at he₁x
  have he₁e : H.comps[i₁] = e₁ := (List.getElem?_eq_some_iff.1 he₁).2
  rw [he₁e] at he₁k he₁x
  have hs₁ : MainB_st e₁ = (.G .plus, e₁.x, x) := by simp [MainB_st, he₁k, he₁x.1]
  have hQ1 : (H.comps.map MainB_st).Perm ((H.comps.eraseIdx i₁).map MainB_st ++ [MainB_st e₁]) := by
    have := (List.getElem_cons_eraseIdx_perm hi₁l).symm.map MainB_st
    rw [he₁e] at this
    exact this.trans (by simpa using List.perm_append_comm (l₁ := [MainB_st e₁]))
  have habs : ∀ {Γ' : Graph 3 (n + 1)} {κ : Kind} (u v : Atom 3 (n + 1)),
      κ.mclass = none → MainB_edS Γ' (κ, u, v) = none := fun u v h => MainB_edS_none _ h
  have gM : ∀ j ∈ H.edgeIdx x .minus false, ∀ T : List (Comp (Atom 3 (n + 1))),
      (∀ c ∈ T, c.kind.mclass = none ∧ c.kind.joinsMol = false) → ∀ co,
      MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨(liftCs 1 (eraseIdxs [i₁, j] H.comps) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (liftA 1 e₁.x) (newA 0),
          mkC (.G .minus) (liftA 1 ((H.comps.getD j e₁).x)) (newA 0)]) ++ T, co⟩, liftA 1⟩ := by
    intro j hj T hT co
    obtain ⟨hjl, hjk, hjx⟩ := MainB_mem_edgeIdx hj
    simp only [Bool.false_eq_true, ↓reduceIte] at hjx
    have hne : j ≠ i₁ := by
      rintro rfl; rw [he₁e, he₁k] at hjk; cases hjk
    rw [MainB_getD_of_lt hjl]
    have hsj : MainB_st H.comps[j] = (.G .minus, H.comps[j].x, x) := by
      simp [MainB_st, hjk, hjx.1]
    have hTj : (T.map MainB_st).filter (fun p => p.1.joinsMol) = [] :=
      List.filter_eq_nil_iff.2 fun p hp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; simp [MainB_st, (hT c hc).2]
    have hTa : ∀ {Γ' : Graph 3 (n + 1)}, ∀ p ∈ T.map MainB_st, MainB_edS Γ' p = none :=
      fun p hp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp; exact MainB_edS_none _ (hT c hc).1
    refine MainB_good_iso (K := (eraseIdxs [i₁, j] H.comps).map MainB_st)
      (M := [MainB_st e₁, MainB_st H.comps[j]])
      (N := [(.waved .s, liftA 1 x, newA 0), (.G .plus, liftA 1 e₁.x, newA 0),
        (.G .minus, liftA 1 H.comps[j].x, newA 0)] ++ T.map MainB_st) ?_ ?_ ?_ ?_ hx ?_ co
    · have := (MainB_perm_two (Ne.symm hne) hi₁l hjl).map MainB_st
      rw [he₁e] at this
      refine this.trans ?_
      MainB_perm
    · rw [hs₁, hsj]; rfl
    · rw [List.filter_append, hTj]; rfl
    · intro Γ' hC hn
      rw [hs₁, hsj]
      have h1 := MainB_R_append (MainB_R_moved hC hn (.G .plus) e₁.x).2
        (MainB_R_moved hC hn (.G .minus) H.comps[j].x).2
      have h2 := MainB_R_absL (N := (.waved .s, liftA 1 x, newA 0) :: T.map MainB_st)
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact habs _ _ rfl
          · exact hTa p hp) h1
      refine MainB_R_perm ?_ (List.Perm.refl _) h2
      MainB_perm
    · rw [List.map_append, List.map_append, MainB_st_liftCs, List.append_assoc]
      rfl
  have gL : ∀ co, MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨liftCs 1 H.comps ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)], co⟩,
        liftA 1⟩ := by
    intro co
    refine MainB_good_iso (K := H.comps.map MainB_st) (M := [])
      (N := [(.waved .s, liftA 1 x, newA 0), (.light .plus, newA 0, newA 0)])
      (by simp) rfl rfl (fun Γ' hC hn => ?_) hx ?_ co
    · exact MainB_R_absL (L' := []) (N := [_, _]) (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact habs _ _ rfl) MainB_R_nil
    · rw [List.map_append, MainB_st_liftCs]
      rfl
  have g1 : ∀ co, MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨liftCs 1 (H.comps.eraseIdx i₁) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (liftA 1 e₁.x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 x)], co⟩, liftA 1⟩ := by
    intro co
    refine MainB_good_iso (K := (H.comps.eraseIdx i₁).map MainB_st) (M := [MainB_st e₁])
      (N := [(.waved .s, liftA 1 x, newA 0), (.G .plus, liftA 1 e₁.x, newA 0),
        (.G .plus, newA 0, liftA 1 x)])
      hQ1 (by rw [hs₁]; rfl) rfl (fun Γ' hC hn => ?_) hx ?_ co
    · rw [hs₁]
      have hx1 := MainB_va_map hC x
      have h2 := MainB_R_absL (N := [(.waved .s, liftA 1 x, newA 0), (.G .plus, newA 0, liftA 1 x)])
        (fun p hp => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact habs _ _ rfl
          · exact MainB_edS_va hn hx1) (MainB_R_moved hC hn (.G .plus) e₁.x).2
      refine MainB_R_perm ?_ (List.Perm.refl _) h2
      MainB_perm
    · rw [List.map_append, MainB_st_liftCs]
      rfl
  set xIdx := H.edgeIdx x .plus false ++ H.edgeIdx x .minus false with hxIdx
  have hi₁x : i₁ ∈ xIdx := by simp [xIdx, hi₁]
  have gD : ∀ d ∈ dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs xIdx H.comps)), ∀ co,
      MainB_Good Γ x (H.comps.map MainB_st) ⟨n + 1, ⟨liftCs 1 (pickIdxs (xIdx.filter (· != i₁))
        H.comps) ++ d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (liftA 1 e₁.x) (newA 0)], co⟩, liftA 1⟩ := by
    intro d hd co
    obtain ⟨m, hm, ch, bb, ps, rfl, hr, hcase, hpj, hpR⟩ :=
      MainB_dTerms_lift (Γ := Γ) (x := x) (eraseIdxs xIdx H.comps) hd
    have hpermL : ((eraseIdxs xIdx H.comps).map MainB_st).Perm
        (MainB_st (eraseIdxs xIdx H.comps)[m] ::
          ((eraseIdxs xIdx H.comps).eraseIdx m).map MainB_st) := by
      have := (List.getElem_cons_eraseIdx_perm hm).symm.map MainB_st
      simpa using this
    have hX := (MainB_perm_xIdx hi₁l hi₁x).map MainB_st
    rw [he₁e] at hX
    refine MainB_good_split (p := MainB_st (eraseIdxs xIdx H.comps)[m])
      (K := (pickIdxs (xIdx.filter (· != i₁)) H.comps).map MainB_st ++
        ((eraseIdxs xIdx H.comps).eraseIdx m).map MainB_st)
      (M := [MainB_st e₁]) (N := ps.map MainB_st ++ [(.waved .s, liftA 1 x, newA 0),
        (.G .plus, liftA 1 e₁.x, newA 0)]) ?_ hr hcase (by rw [hs₁]; rfl)
      (by rw [List.filter_append, hpj]; rfl) (fun Γ' hC hn => ?_) hx ?_ co
    · refine hX.trans ?_
      have h2 := hpermL
      rw [List.perm_iff_count] at h2 ⊢
      intro a
      have := h2 a
      simp only [List.count_append, List.count_cons, List.count_nil, List.map_append,
        List.map_cons, MainB_st] at this ⊢
      omega
    · rw [hs₁]
      have h1 := MainB_R_append (hpR Γ' hC (MainB_va_map hC x) hn)
        (MainB_R_absL (N := [(.waved .s, liftA 1 x, newA 0)]) (fun p hp => by
          rw [List.mem_singleton] at hp; subst hp; exact habs _ _ rfl)
          (MainB_R_moved hC hn (.G .plus) e₁.x).2)
      refine MainB_R_perm ?_ ?_ h1
      · MainB_perm
      · MainB_perm
    · simp only [List.map_append, MainB_st_liftCs, List.append_assoc]
      rfl
  intro t₀ ht₀
  simp only [List.mem_append, List.mem_map, List.mem_singleton, List.mem_ite_nil_left,
    or_assoc] at ht₀
  have hW : ∀ ch : Charge, ∀ c ∈ [mkC (.weight ch) (liftA 1 x) (liftA 1 x : Atom 3 (n + 1))],
      c.kind.mclass = none ∧ c.kind.joinsMol = false := by
    intro ch c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨rfl, rfl⟩
  have hLi : ∀ ch : Charge, ∀ c ∈ [mkC (.light ch) (liftA 1 x) (liftA 1 x : Atom 3 (n + 1))],
      c.kind.mclass = none ∧ c.kind.joinsMol = false := by
    intro ch c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨rfl, rfl⟩
  have hnil : ∀ c ∈ ([] : List (Comp (Atom 3 (n + 1)))),
      c.kind.mclass = none ∧ c.kind.joinsMol = false := fun c hc => absurd hc (List.not_mem_nil)
  rcases ht₀ with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩ | rfl |
    ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ | ⟨_, ⟨d, hd, rfl⟩, rfl⟩
  · left; have := gM j hj [] hnil (cm * cmb * H.coeff); rwa [List.append_nil] at this
  · left; exact gM j hj _ (hLi _) _
  · left; exact gL _
  · left; exact g1 _
  · left; exact gD d hd _
  · right; exact ⟨_, _, rfl, MainB_st_labelQs x H.comps⟩
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gM j hj _ (hW _) (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gL (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (g1 (cm * H.coeff))
  · left; exact MainB_good_st (MainB_st_labelQs _ _) _ _ (gD d hd (cm * H.coeff))

/-- The obligation `MainB_GoodX` of a term on the complex conjugate graph, conjugated back. -/
private theorem MainB_goodX_conj {Γ : Graph 3 n} {x : Atom 3 n}
    {Q : List (Kind × Atom 3 n × Atom 3 n)} {t₀ : Tracked 3 n}
    (h : MainB_GoodX Γ x (Q.map MainB_cT) t₀) :
    MainB_GoodX Γ x Q ⟨t₀.nOut, t₀.g.conj, t₀.f⟩ := by
  rcases h with h | ⟨cs, co, rfl, hcs⟩
  · exact Or.inl (MainB_good_conj h)
  · right
    refine ⟨cs.map fun c => { c with kind := c.kind.conj }, Coeff.conj co, rfl, ?_⟩
    have : (cs.map fun c => { c with kind := c.kind.conj }).map MainB_st =
        (cs.map MainB_st).map MainB_cT := by
      simp [MainB_st, MainB_cT, Function.comp_def]
    rw [this, hcs, MainB_map_cT_cT]

/-- `Graph.FlatCarried` from `Γ` to a term of `pLiftT` with the obligation `MainB_GoodX`. -/
private theorem MainB_P_finalX {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true)
    (hCB : Γ.ColourInvB) {t₀ : Tracked 3 n}
    (h : MainB_GoodX Γ x (Γ.pCore.comps.map MainB_st) t₀) :
    Γ.FlatCarried (⟨t₀.nOut, ⟨t₀.g.comps.map (fun c =>
        if c.kind.isRandom then { c with label := some (.P, t₀.f x) } else c) ++
      Γ.pEnv.map (Comp.map t₀.f), t₀.g.coeff⟩, t₀.f⟩ : Tracked 3 n).g := by
  rcases h with h | ⟨cs, co, rfl, hcs⟩
  · exact MainB_P_final hx hCB h
  · apply MainB_flat_perm
    dsimp only
    have e : (Γ.pEnv.map (Comp.map id)).map MainB_st = Γ.pEnv.map MainB_st := by
      rw [List.map_map]; rfl
    rw [List.map_append, MainB_st_rl, e, hcs]
    exact ((MainB_perm_pCore Γ).filter _).symm

/-- [II, (4.24)] inside `P_x`: the multi-edge expansion of [I, Def 3.11] in its four cases. -/
private theorem MainB_pMultiE {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n}
    {t : Tracked 3 n} (hI : Γ.InvB') (hP : Γ.IsPFormAt x) (hE : multiEHat x Γ.pCore = some E)
    (ht : t ∈ pLiftT x Γ E) : Γ.FlatCarried t.g := by
  have hx := MainB_x_int hI.2.2.2.2 hP
  obtain ⟨t₀, ht₀, rfl⟩ := MainB_mem_pLift ht
  refine MainB_P_finalX hx hI.2.1 ?_
  have hc : ∀ {E₁ : TExpansion 3 n},
      (∀ t₁ ∈ E₁, MainB_GoodX Γ x (Γ.pCore.conj.comps.map MainB_st) t₁) →
      ∀ t₀ ∈ E₁.conj, MainB_GoodX Γ x (Γ.pCore.comps.map MainB_st) t₀ := by
    intro E₁ h₁ t₀ ht₀
    obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.1 ht₀
    have := h₁ t₁ ht₁
    rw [MainB_st_conj] at this
    exact MainB_goodX_conj this
  unfold multiEHat at hE
  split_ifs at hE
  · exact MainB_good_multiEOut hx hE t₀ ht₀
  · obtain ⟨E₁, hE₁, rfl⟩ := Option.map_eq_some_iff.1 hE
    exact hc (MainB_good_multiEOut hx hE₁) t₀ ht₀
  · exact MainB_good_multiEIn hx hE t₀ ht₀
  · obtain ⟨E₁, hE₁, rfl⟩ := Option.map_eq_some_iff.1 hE
    exact hc (MainB_good_multiEIn hx hE₁) t₀ ht₀

end PSteps

/-! ## `O_dot` -/

section Dot

variable {n : ℕ}

private theorem MainB_diff_ne {κ : Kind} (h : κ.isDiffusive = true) : κ ≠ .dot ∧ κ ≠ .xdot := by
  constructor <;> rintro rfl <;> simp [Kind.isDiffusive] at h

/-- The components other than dotted and `×`-dotted edges. -/
private def MainB_nd (c : Comp (Atom 3 n)) : Bool := decide (c.kind ≠ .dot ∧ c.kind ≠ .xdot)

private theorem MainB_nonDotDeg (Γ : Graph 3 n) (u : Atom 3 n) :
    Γ.nonDotDeg u =
      ((Γ.comps.filter MainB_nd).filter fun c => decide (c.x = u ∨ c.y = u)).length := by
  unfold Graph.nonDotDeg
  rw [List.filter_filter]
  congr 1

/-- The invariant `Graph.InvB'` passes to a graph with the same blocks, carried molecular graph,
the same components other than dotted and `×`-dotted edges up to order, new dotted or `×`-dotted
edges without label only, and new `×`-dotted edges between atoms not both unpinned. -/
private theorem MainB_invB_transfer {Γ Γ' : Graph 3 n} (hI : Γ.InvB') (hF : Γ.FlatCarried Γ')
    (hB : ∀ u v, Γ'.SameBlock u v ↔ Γ.SameBlock u v)
    (hnd : (Γ'.comps.filter MainB_nd).Perm (Γ.comps.filter MainB_nd))
    (hsub : ∀ c ∈ Γ'.comps, c ∈ Γ.comps ∨ ((c.kind = .dot ∨ c.kind = .xdot) ∧ c.label = none))
    (hE2 : ∀ c ∈ Γ'.comps, c.kind = .xdot → ¬ (Γ'.Unpinned c.x ∧ Γ'.Unpinned c.y)) :
    Γ'.InvB' := by
  obtain ⟨hs, hC, hE, hG, hL⟩ := hI
  have hU : ∀ u, Γ'.Unpinned u ↔ Γ.Unpinned u := by
    intro u
    unfold Graph.Unpinned
    simp only [hB]
  have ha : Γ'.anchor = Γ.anchor := by
    funext u
    unfold Graph.anchor
    congr 1
    funext b
    exact decide_eq_decide.2 (hB _ _)
  have hfa : Γ'.flatAtom = Γ.flatAtom := by
    funext u
    cases u with
    | inl a => simp only [Graph.flatAtom, ha]
    | inr a => rfl
  have hfc : Γ'.flatComp = Γ.flatComp := by
    funext c
    simp only [Graph.flatComp, hfa]
  have hmem : ∀ c, MainB_nd c = true → (c ∈ Γ'.comps ↔ c ∈ Γ.comps) := by
    intro c hc
    constructor
    · intro h
      exact (List.mem_filter.1 (hnd.mem_iff.1 (List.mem_filter.2 ⟨h, hc⟩))).1
    · intro h
      exact (List.mem_filter.1 (hnd.mem_iff.2 (List.mem_filter.2 ⟨h, hc⟩))).1
  have hdiff : ∀ {c : Comp (Atom 3 n)}, c.kind.isDiffusive = true → MainB_nd c = true := by
    intro c h
    have := MainB_diff_ne h
    simp [MainB_nd, this.1, this.2]
  have hGp : ∀ {c : Comp (Atom 3 n)}, c.kind = .G .plus → MainB_nd c = true := by
    intro c h; simp [MainB_nd, h]
  have hdeg : ∀ u, Γ'.nonDotDeg u = Γ.nonDotDeg u := by
    intro u
    rw [MainB_nonDotDeg, MainB_nonDotDeg]
    exact (hnd.filter _).length_eq
  have hHas : ∀ u, Γ'.HasDiffToPinned u ↔ Γ.HasDiffToPinned u := by
    intro u
    unfold Graph.HasDiffToPinned
    simp only [hU]
    constructor
    · rintro ⟨c, hc, hd, h⟩
      exact ⟨c, (hmem c (hdiff hd)).1 hc, hd, h⟩
    · rintro ⟨c, hc, hd, h⟩
      exact ⟨c, (hmem c (hdiff hd)).2 hc, hd, h⟩
  have hDiff : ∀ u, Γ'.DiffToPinned u ↔ Γ.DiffToPinned u := by
    intro u
    unfold Graph.DiffToPinned
    simp only [hU]
    constructor
    · intro h c hc hd
      exact h c ((hmem c (hdiff hd)).2 hc) hd
    · intro h c hc hd
      exact h c ((hmem c (hdiff hd)).1 hc) hd
  refine ⟨flatCarried_spd 3 n n Γ Γ' hF hG hs, ?_, ?_, ?_, ?_⟩
  · intro c hc
    unfold Graph.blockNorm at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [hfc]
    rcases hsub d hd with hd' | ⟨hk, -⟩
    · exact hC _ (List.mem_map_of_mem hd')
    · have hk' : (Γ.flatComp d).kind = .dot ∨ (Γ.flatComp d).kind = .xdot := by
        rw [Graph.flatComp_kind]; exact hk
      refine ⟨fun hr => ?_, fun hw => ?_⟩
      · rcases hk' with h | h <;> rw [h] at hr <;> simp [Kind.isRandom] at hr
      · rcases hk' with h | h <;> rw [h] at hw <;> cases hw
  · obtain ⟨E1, E2, E3, E4, E5⟩ := hE
    refine ⟨fun u v huv h => ?_, hE2, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb⟩ := E1 u v huv ((hB u v).1 h)
      exact ⟨b, (hB _ _).2 hb⟩
    · rw [hU] at h
      exact ⟨(hHas _).2 (E3 h).1, (hDiff _).2 (E3 h).2⟩
    · rw [hU] at h
      refine ⟨fun c hc hd => ?_, by rw [hdeg]; exact (E4 h).2⟩
      exact (E4 h).1 c ((hmem c (hdiff hd)).1 hc) hd
    · rw [hU] at h
      obtain ⟨h1, h2, h3⟩ := E5 h
      refine ⟨?_, (hDiff _).2 h2, by rw [hdeg]; exact h3⟩
      rcases h1 with ⟨c, hc, hk, hx⟩ | h1
      · exact Or.inl ⟨c, (hmem c (hGp hk)).2 hc, hk, hx⟩
      · exact Or.inr ((hHas _).2 h1)
  · intro c hc
    rcases hsub c hc with h | ⟨hk, -⟩
    · exact hG c h
    · rcases hk with h | h <;> rw [h] <;> simp
  · intro c hc
    rcases hsub c hc with h | ⟨-, hl⟩
    · exact hL c h
    · rw [hl]; rfl

/-- Blocks grow when components are added. -/
private theorem MainB_block_mono {Γ : Graph 3 n} (ad : List (Comp (Atom 3 n))) (co : Coeff)
    {u v : Atom 3 n} (h : Γ.SameBlock u v) : (⟨Γ.comps ++ ad, co⟩ : Graph 3 n).SameBlock u v := by
  refine SimpleGraph.Reachable.mono (fun a b hab => ?_) h
  obtain ⟨hne, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
  · obtain ⟨c, hc, hk, h1, h2⟩ := h
    exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
  · obtain ⟨c, hc, hk, h1, h2⟩ := h
    exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩

/-- A `×`-dotted edge added at atoms not both unpinned. -/
private theorem MainB_add_xdot {H : Graph 3 n} (hI : H.InvB') (p q : Atom 3 n)
    (hpq : (∃ b, H.SameBlock p (.inr b)) ∨ (∃ b, H.SameBlock q (.inr b))) :
    (⟨H.comps ++ [mkC .xdot p q], H.coeff⟩ : Graph 3 n).InvB' ∧
      H.FlatCarried ⟨H.comps ++ [mkC .xdot p q], H.coeff⟩ := by
  set H' : Graph 3 n := ⟨H.comps ++ [mkC .xdot p q], H.coeff⟩ with hH'
  have hC : MainB_Corr H H' id := MainB_same
    (fun c hc hj => by
      rcases List.mem_append.1 hc with hc | hc
      · exact ⟨c, hc, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · rw [List.mem_singleton] at hc; subst hc; cases hj)
    (fun d hd _ => ⟨d, List.mem_append_left _ hd, rfl, Or.inl ⟨rfl, rfl⟩⟩)
  have hF : H.FlatCarried H' := by
    apply MainB_flat_perm
    rw [hH', List.map_append, List.filter_append]
    have e : (([mkC .xdot p q] : List (Comp (Atom 3 n))).map MainB_st).filter
        (fun p => MainB_rel p.1) = [] := rfl
    rw [e, List.append_nil]
  refine ⟨MainB_invB_transfer hI hF (hC.blk) ?_ ?_ ?_, hF⟩
  · rw [hH', List.filter_append]
    have e : ([mkC .xdot p q] : List (Comp (Atom 3 n))).filter MainB_nd = [] := by
      simp [MainB_nd, mkC]
    rw [e, List.append_nil]
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl hc
    · rw [List.mem_singleton] at hc; subst hc; exact Or.inr ⟨Or.inr rfl, rfl⟩
  · have hU : ∀ u, H'.Unpinned u ↔ H.Unpinned u := by
      intro u; unfold Graph.Unpinned
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => h2 b ((hC.blk _ _).2 hb)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => h2 b ((hC.blk _ _).1 hb)⟩
    intro c hc hk
    rw [hU, hU]
    rcases List.mem_append.1 hc with hc | hc
    · exact hI.2.2.1.2.1 c hc hk
    · rw [List.mem_singleton] at hc; subst hc
      rintro ⟨h1, h2⟩
      rcases hpq with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact MainB_not_unpinned hb h1
      · exact MainB_not_unpinned hb h2

/-- A dotted edge added at atoms one of which lies in a block with an internal atom. -/
private theorem MainB_add_dot {H : Graph 3 n} (hI : H.InvB') (p q : Atom 3 n)
    (hpq : (∃ b, H.SameBlock p (.inr b)) ∨ (∃ b, H.SameBlock q (.inr b))) :
    (⟨H.comps ++ [mkC .dot p q], H.coeff⟩ : Graph 3 n).InvB' ∧
      H.FlatCarried ⟨H.comps ++ [mkC .dot p q], H.coeff⟩ := by
  rcases hpq with hp | hq
  · exact ⟨invB'_addDot n H p q hI hp, addDot_flat n H p q hI.2.1 hI.2.2.1 hI.2.2.2.1 hp⟩
  set H₂ : Graph 3 n := ⟨H.comps ++ [mkC .dot q p], H.coeff⟩ with hH₂
  set H' : Graph 3 n := ⟨H.comps ++ [mkC .dot p q], H.coeff⟩ with hH'
  have hI₂ : H₂.InvB' := invB'_addDot n H q p hI hq
  have hF₂ : H.FlatCarried H₂ := addDot_flat n H q p hI.2.1 hI.2.2.1 hI.2.2.2.1 hq
  have hC : MainB_Corr H₂ H' id := MainB_same
    (fun c hc _ => by
      rcases List.mem_append.1 hc with hc | hc
      · exact ⟨c, List.mem_append_left _ hc, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · rw [List.mem_singleton] at hc; subst hc
        exact ⟨mkC .dot q p, List.mem_append_right _ (List.mem_singleton_self _), rfl,
          Or.inr ⟨rfl, rfl⟩⟩)
    (fun d hd _ => by
      rcases List.mem_append.1 hd with hd | hd
      · exact ⟨d, List.mem_append_left _ hd, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · rw [List.mem_singleton] at hd; subst hd
        exact ⟨mkC .dot p q, List.mem_append_right _ (List.mem_singleton_self _), rfl,
          Or.inr ⟨rfl, rfl⟩⟩)
  have hF : H₂.FlatCarried H' := by
    refine MainB_flat_id hC ?_
    rw [hH', hH₂, List.map_append, List.map_append, MainB_cm_append, MainB_cm_append]
    simp [MainB_cm, MainB_st, mkC, MainB_edS_dot]
  refine ⟨MainB_invB_transfer hI₂ hF hC.blk ?_ ?_ ?_, flatCarried_trans 3 n n n H H₂ H' hF₂ hF⟩
  · rw [hH', hH₂, List.filter_append, List.filter_append]
    simp [MainB_nd, mkC]
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl (List.mem_append_left _ hc)
    · rw [List.mem_singleton] at hc; subst hc; exact Or.inr ⟨Or.inl rfl, rfl⟩
  · have hU : ∀ u, H'.Unpinned u ↔ H₂.Unpinned u := by
      intro u; unfold Graph.Unpinned
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => h2 b ((hC.blk _ _).2 hb)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => h2 b ((hC.blk _ _).1 hb)⟩
    intro c hc hk
    rw [hU, hU]
    rcases List.mem_append.1 hc with hc | hc
    · exact hI₂.2.2.1.2.1 c (List.mem_append_left _ hc) hk
    · rw [List.mem_singleton] at hc; subst hc; cases hk

/-- Dotted and `×`-dotted edges added one at a time, each at atoms one of which lies in a block
of `Γ` with an internal atom. -/
private theorem MainB_add_list {Γ : Graph 3 n} : ∀ (ad : List (Comp (Atom 3 n))) (H : Graph 3 n),
    H.InvB' → Γ.FlatCarried H → (∀ u v, Γ.SameBlock u v → H.SameBlock u v) →
    (∀ d ∈ ad, ∃ p q, (d = mkC .dot p q ∨ d = mkC .xdot p q) ∧
      ((∃ b, Γ.SameBlock p (.inr b)) ∨ (∃ b, Γ.SameBlock q (.inr b)))) →
    (⟨H.comps ++ ad, H.coeff⟩ : Graph 3 n).InvB' ∧ Γ.FlatCarried ⟨H.comps ++ ad, H.coeff⟩
  | [], H, hI, hF, _, _ => by
    rw [List.append_nil]
    exact ⟨hI, hF⟩
  | d :: ad, H, hI, hF, hB, hd => by
    obtain ⟨p, q, hdpq, hanc⟩ := hd d (List.mem_cons_self ..)
    have hanc' : (∃ b, H.SameBlock p (.inr b)) ∨ (∃ b, H.SameBlock q (.inr b)) := by
      rcases hanc with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact Or.inl ⟨b, hB _ _ hb⟩
      · exact Or.inr ⟨b, hB _ _ hb⟩
    obtain ⟨hI', hF'⟩ : (⟨H.comps ++ [d], H.coeff⟩ : Graph 3 n).InvB' ∧
        H.FlatCarried ⟨H.comps ++ [d], H.coeff⟩ := by
      rcases hdpq with rfl | rfl
      · exact MainB_add_dot hI p q hanc'
      · exact MainB_add_xdot hI p q hanc'
    have := MainB_add_list ad ⟨H.comps ++ [d], H.coeff⟩ hI'
      (flatCarried_trans 3 n n n Γ H _ hF hF')
      (fun u v h => MainB_block_mono [d] H.coeff (hB u v h))
      (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd'))
    simpa [List.append_assoc] using this

private theorem MainB_mem_foldl_uniq {α : Type} (F : List α → α → List α)
    (hF : ∀ acc p, F acc p = acc ∨ F acc p = acc ++ [p]) :
    ∀ (cand acc : List α) (q : α), q ∈ cand.foldl F acc → q ∈ acc ∨ q ∈ cand
  | [], acc, q, hq => Or.inl hq
  | p :: cand, acc, q, hq => by
    rw [List.foldl_cons] at hq
    rcases MainB_mem_foldl_uniq F hF cand (F acc p) q hq with h | h
    · rcases hF acc p with e | e
      · rw [e] at h; exact Or.inl h
      · rw [e, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The pairs of `Graph.splitPairs` are the ends of a solid or `×`-dotted edge. -/
private theorem MainB_splitPairs_mem {Γ : Graph 3 n} {p : Atom 3 n × Atom 3 n × Bool}
    (hp : p ∈ Γ.splitPairs) :
    ∃ c ∈ Γ.comps, (c.kind.isSolid = true ∨ c.kind = .xdot) ∧ c.x = p.1 ∧ c.y = p.2.1 := by
  unfold Graph.splitPairs at hp
  simp only [List.mem_filterMap] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  have hpq : p.1 = q.1 ∧ p.2.1 = q.2 := by
    split_ifs at hqp
    obtain rfl := Option.some.inj hqp
    exact ⟨rfl, rfl⟩
  rcases MainB_mem_foldl_uniq _ (fun acc p => by split_ifs <;> simp) _ [] q hq with hq | hq
  · cases hq
  obtain ⟨c, hc, hcq⟩ := List.mem_filterMap.1 hq
  split_ifs at hcq with hcond
  obtain rfl := Option.some.inj hcq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hcond
  exact ⟨c, hc, hcond.1, hpq.1.symm, hpq.2.symm⟩

/-- The ends of a solid or `×`-dotted edge: one lies in a block with an internal atom. -/
private theorem MainB_anchored_of {Γ : Graph 3 n} (hI : Γ.InvB') {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hk : c.kind.isSolid = true ∨ c.kind = .xdot) :
    (∃ b, Γ.SameBlock c.x (.inr b)) ∨ (∃ b, Γ.SameBlock c.y (.inr b)) := by
  rcases hk with hk | hk
  · left
    have hr : c.kind.isRandom = true := by
      rcases hc' : c.kind with
        ch | ch | ch | ch | ⟨ch, D⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _ <;>
        rw [hc'] at hk <;> first | rfl | simp [Kind.isSolid] at hk
    have h1 := MainB_colour hI.2.1 hc hr
    obtain ⟨b, hb⟩ : ∃ b, Γ.flatAtom c.x = .inr b := by
      revert h1
      cases Γ.flatAtom c.x with
      | inl _ => simp
      | inr b => exact fun _ => ⟨b, rfl⟩
    exact ⟨b, hb ▸ MainB_flat_block Γ c.x⟩
  · by_cases hx : Γ.Unpinned c.x
    · exact Or.inr (MainB_block_of_not_unpinned fun hy => hI.2.2.1.2.1 c hc hk ⟨hx, hy⟩)
    · exact Or.inl (MainB_block_of_not_unpinned hx)

/-- `O_dot` ([II, Def 4.2]): `×`-dotted edges removed, dotted and `×`-dotted edges added, then
`O_merge`. -/
private theorem MainB_dot {Γ : Graph 3 n} {t : Tracked 3 n} (hI : Γ.InvB') (ht : t ∈ oDotT Γ) :
    Γ.FlatCarried t.g := by
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht
  · rw [List.mem_singleton] at ht; subst ht; exact MainB_refl Γ
  · rw [List.mem_singleton] at ht; subst ht; exact MainB_refl Γ
  obtain ⟨A, -, hA⟩ := List.mem_filterMap.1 ht
  unfold Graph.dotChoice at hA
  dsimp only at hA
  set P : Comp (Atom 3 n) → Bool := fun c => !(c.kind == .xdot &&
    Γ.splitPairs.any fun p => !p.2.2 && ((p.1 == c.x && p.2.1 == c.y) ||
      (p.1 == c.y && p.2.1 == c.x))) with hP
  set co' : Coeff := (-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * Γ.coeff with hco
  set K : Graph 3 n := ⟨Γ.comps.filter P, co'⟩ with hK
  have hPx : ∀ c, c.kind ≠ .xdot → P c = true := by
    intro c hc
    simp [hP, hc]
  have hsubK : ∀ c ∈ K.comps, c ∈ Γ.comps := fun c hc => List.mem_of_mem_filter hc
  have hCK : MainB_Corr Γ K id := MainB_same
    (fun c hc _ => ⟨c, hsubK c hc, rfl, Or.inl ⟨rfl, rfl⟩⟩)
    (fun d hd hj => ⟨d, List.mem_filter.2 ⟨hd, hPx d (by intro h; rw [h] at hj; cases hj)⟩, rfl,
      Or.inl ⟨rfl, rfl⟩⟩)
  have hFK : Γ.FlatCarried K := by
    apply MainB_flat_perm
    refine List.Perm.of_eq ?_
    rw [hK, List.filter_map, List.filter_map, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro c _
    by_cases h : c.kind = .xdot
    · have e : MainB_rel c.kind = false := by rw [h]; rfl
      simp [MainB_st, e]
    · simp [hPx c h]
  have hIK : K.InvB' := by
    refine MainB_invB_transfer hI hFK hCK.blk (List.Perm.of_eq ?_) (fun c hc => Or.inl (hsubK c hc))
      ?_
    · rw [hK, List.filter_filter]
      apply List.filter_congr
      intro c _
      by_cases h : c.kind = .xdot
      · simp [MainB_nd, h]
      · simp [hPx c h]
    · intro c hc hk
      have hU : ∀ u, K.Unpinned u ↔ Γ.Unpinned u := by
        intro u; unfold Graph.Unpinned
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => h2 b ((hCK.blk _ _).2 hb)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun b hb => h2 b ((hCK.blk _ _).1 hb)⟩
      rw [hU, hU]
      exact hI.2.2.1.2.1 c (hsubK c hc) hk
  have hadd := MainB_add_list (Γ := Γ) (Γ.splitPairs.filterMap fun p =>
      if p ∈ A then some (mkC .dot p.1 p.2.1) else if p.2.2 then some (mkC .xdot p.1 p.2.1)
      else none) K hIK hFK (fun u v h => (hCK.blk u v).2 h) (fun d hd => by
        obtain ⟨p, hp, hpd⟩ := List.mem_filterMap.1 hd
        obtain ⟨c, hc, hck, hcx, hcy⟩ := MainB_splitPairs_mem hp
        have hanc := MainB_anchored_of hI hc hck
        rw [hcx, hcy] at hanc
        split_ifs at hpd
        · exact ⟨p.1, p.2.1, Or.inl (Option.some.inj hpd).symm, hanc⟩
        · exact ⟨p.1, p.2.1, Or.inr (Option.some.inj hpd).symm, hanc⟩)
  exact flatCarried_trans 3 n n t.nOut Γ _ t.g hadd.2 (qElemStep_merge_flat n _ t hA hadd.1)

end Dot

/-! ## [II, Lemma 5.13] in the block reading -/

/-- The block normal form at every elementary step of the `Q`-expansions: the molecular graph of
the second graph is carried from that of the first. -/
theorem qElemStep_flat :
  ∀ g g' : Σ n, Graph 3 n, QElemStep g g' → g.2.InvB' → g.2.FlatCarried g'.2 := by
  intro g g' hs hI
  cases hs with
  | schur x i Γ t hx ht => exact qElemStep_schur_flat _ x i Γ hx hI t ht
  | schurRev x i Γ t hx ht => exact qElemStep_schurRev_flat _ x i Γ hx hI t ht
  | schurW x i Γ t hx ht => exact qElemStep_schurW_flat _ x i Γ hx hI t ht
  | schurWRev x i Γ t hx ht => exact qElemStep_schurWRev_flat _ x i Γ hx hI t ht
  | taylor D i Γ t ht => exact MainB_taylor ht
  | weight1 x Γ t ht => exact MainB_weight1 ht
  | dot Γ t ht => exact MainB_dot hI ht
  | merge Γ t ht => exact qElemStep_merge_flat _ Γ t ht hI
  | split u v Γ t hv ht => exact qElemStep_split_flat _ u v Γ hv hI t ht
  | xdot i Γ t ht => exact qElemStep_xdot_flat _ i Γ hI t ht
  | dropDot i Γ c hc hk hb => exact MainB_dropDot hc hk hb
  | rebase i Γ c u v hc hk hb => exact qElemStep_rebase_flat _ i Γ c u v hc hk hb hI
  | qToP u Γ t hQ ht => exact MainB_qToP ht
  | absorb ℓ Γ hℓ hl => exact MainB_absorb ℓ
  | dropP u Γ hP hm => exact MainB_dropLabels Γ
  | pWeight1 x Γ t hP hp ht => exact MainB_pWeight1 ht
  | pWeight2 x Γ t hP hp ht => exact MainB_pWeight2 hI hP ht
  | pMultiE x Γ E t hP hp hE ht => exact MainB_pMultiE hI hP hE ht

/-- Every elementary step of the `Q`-expansions keeps the invariant `Graph.InvB'`. -/
theorem qElemStep_invB :
  ∀ g g' : Σ n, Graph 3 n, QElemStep g g' → g.2.InvB' → g'.2.InvB' := by
  intro g g' hs hi
  obtain ⟨h1, h2, h3, h4⟩ := qElemStep_clauses g g' hs hi
  exact ⟨flatCarried_spd 3 g.1 g'.1 g.2 g'.2 (qElemStep_flat g g' hs hi) hi.2.2.2.1 hi.1,
    h1, h2, h3, h4⟩

/-- Every output graph of a `Q`-expansion (`qExpansionOut`) of a graph with the invariant
`Graph.InvB'` has it. -/
theorem qExpansionOut_invB :
  ∀ (D C' n : ℕ) (x : Fin n) (Γ : Graph 3 n) (t : Tracked 3 n),
    qExpansionOut D C' (.inr x) Γ t → Γ.InvB' → t.g.InvB' := by
  intro D C' n x Γ t ht hΓ
  have hc := ht.1.2.2.2.2.2.2
  have key : ∀ g, Relation.ReflTransGen QElemStep ⟨n, Γ⟩ g → g.2.InvB' := by
    intro g hg
    induction hg with
    | refl => exact hΓ
    | tail _ hst ih => exact qElemStep_invB _ _ hst ih
  exact key _ hc

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

section Helpers

variable {V E : Type}

end Helpers

end Instances

end RBM8D.Graphs
