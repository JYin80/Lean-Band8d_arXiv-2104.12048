import RBM8D.LocalLaw.Defs

/-!
# The structure of the label-free graphs `Γ_S`

The combinatorial half of the removal of the `P`/`Q` labels in the proofs of [II, Claim 8.6]
(8.24) and [II, Claim 8.7]: for a normal regular graph `Γ` with the kinds of [II, Def 3.2],
condition [II, Def 3.2 (9)], doubly connected, with only diffusive components at `⊗`, dotted edges
forming a forest and rooted at the external atoms, the graph `Γ_S = Graph.pathRepl Γ S` (each
component of `S` replaced by the path `x–v–y` through its internal label atom `v`, the other labels
erased, and the `×`-dotted edges without a solid edge removed) has the same properties, no label,
the same dotted blocks, and scaling order and diagonal scaling order larger by at least `|S|`
(`labelPathsStmt`).

The blue net of `Γ_S` has, in place of a blue solid edge `x–y` of `S`, the two blue solid edges
`x–v`, `v–y` through the internal atom `v`, so it stays connected through the molecule of `v`.
-/

namespace RBM8D.Graphs

variable {n : ℕ}

/-- The component `c` with its label erased. -/
private def LabelPaths_strip {V : Type*} (c : Comp V) : Comp V := { c with label := none }

/-- The charge of the path replacing the component `c` (`Comp.pathVia`). -/
private def LabelPaths_ch {V : Type*} (c : Comp V) : Charge :=
  match c.kind with
  | .G ch | .weight ch | .light ch | .inv ch | .wD ch _ => ch
  | _ => .plus

/-- The four components of the path `x–v–y` replacing `c`. -/
private theorem LabelPaths_pathVia_eq {V : Type*} (c : Comp V) (v : V) :
    c.pathVia v = [⟨.G (LabelPaths_ch c), c.x, v, [], none⟩,
      ⟨.G (LabelPaths_ch c), v, c.y, [], none⟩,
      ⟨.xdot, c.x, v, [], none⟩, ⟨.xdot, v, c.y, [], none⟩] := rfl

/-- The components of `Γ.pathRepl S` before the removal of `×`-dotted edges that come from the
component with index `i`. -/
private def LabelPaths_piece (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length))
    (i : Fin Γ.comps.length) : List (Comp (Atom 3 n)) :=
  match Γ.comps[i].label with
  | some (_, v) => if i ∈ S then Γ.comps[i].pathVia v else [{ Γ.comps[i] with label := none }]
  | none => [Γ.comps[i]]

/-- The components of `Γ.pathRepl S` before the removal of `×`-dotted edges. -/
private def LabelPaths_cs (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length)) :
    List (Comp (Atom 3 n)) :=
  (List.finRange Γ.comps.length).flatMap (LabelPaths_piece Γ S)

/-- A component is kept in `Γ.pathRepl S` unless it is a `×`-dotted edge between two distinct atoms
that carry no solid edge. -/
private def LabelPaths_keep (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length))
    (c : Comp (Atom 3 n)) : Bool :=
  !(c.kind == .xdot && c.x != c.y &&
      !(LabelPaths_cs Γ S).any fun c' => c'.kind.isSolid &&
        ((c'.x == c.x && c'.y == c.y) || (c'.x == c.y && c'.y == c.x)))

/-- The components of `Γ.pathRepl S`. -/
private theorem LabelPaths_comps (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length)) :
    (Γ.pathRepl S).comps = (LabelPaths_cs Γ S).filter (LabelPaths_keep Γ S) := rfl


/-- Erasing the label of an unlabelled component changes nothing. -/
private theorem LabelPaths_strip_of_none {V : Type*} (c : Comp V) (h : c.label = none) :
    LabelPaths_strip c = c := by
  cases c; simp_all [LabelPaths_strip]

/-- The components of the path `x–v–y`: no minor, no label, solid or `×`-dotted, with ends
`x, v` or `v, y`. -/
private theorem LabelPaths_mem_pathVia {V : Type*} {c d : Comp V} {v : V} (hd : d ∈ c.pathVia v) :
    d.minor = [] ∧ d.label = none ∧ (d.kind = .xdot ∨ ∃ ch, d.kind = .G ch) ∧
      (d.x = c.x ∧ d.y = v ∨ d.x = v ∧ d.y = c.y) := by
  rw [LabelPaths_pathVia_eq] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp

/-- Every atom of `as` lies in a block of `dotBlocks as cs`. -/
private theorem LabelPaths_cover {V : Type*} [DecidableEq V] (as : List V) (cs : List (Comp V))
    {u : V} (hu : u ∈ as) : ∃ B ∈ dotBlocks as cs, u ∈ B := by
  unfold dotBlocks
  have h0 : ∃ B ∈ as.map (fun a => [a]), u ∈ B := ⟨[u], List.mem_map.2 ⟨u, hu, rfl⟩, by simp⟩
  generalize as.map (fun a => [a]) = P at h0
  induction cs generalizing P with
  | nil => exact h0
  | cons c cs ih =>
    apply ih
    obtain ⟨B, hB, huB⟩ := h0
    by_cases hk : c.kind = .dot
    · simp only [hk, ite_true, joinBlocks]
      by_cases hc : (B.contains c.x || B.contains c.y) = true
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          List.mem_flatten.2 ⟨B, List.mem_filter.2 ⟨hB, hc⟩, huB⟩⟩
      · exact ⟨B, List.mem_append_left _ (List.mem_filter.2 ⟨hB, by simpa using hc⟩), huB⟩
    · simp only [hk, ite_false]
      exact ⟨B, hB, huB⟩

/-- An atom whose dotted block has no external atom is internal. -/
private theorem LabelPaths_isRight_of_labelFixedB (Γ : Graph 3 n) {v : Atom 3 n}
    (h : Γ.labelFixedB v = false) : v.isRight = true := by
  cases v with
  | inr a => rfl
  | inl a =>
    exfalso
    have hu : (Sum.inl a : Atom 3 n) ∈ allAtoms 3 n := by simp [allAtoms]
    obtain ⟨B, hB, huB⟩ := LabelPaths_cover _ Γ.comps hu
    have : Γ.labelFixedB (.inl a) = true := by
      unfold Graph.labelFixedB
      exact List.any_eq_true.2 ⟨B, hB, by simp [huB]; exact ⟨a, huB⟩⟩
    simp [this] at h

/-- The facts on a replaceable component. -/
private theorem LabelPaths_of_pathEligB (Γ : Graph 3 n) {c : Comp (Atom 3 n)}
    (h : Γ.pathEligB c = true) : ∃ pq v, c.label = some (pq, v) ∧ c.kind.isRandom = true ∧
      v.isRight = true ∧ c.x ≠ v ∧ c.y ≠ v := by
  unfold Graph.pathEligB at h
  rcases hl : c.label with _ | ⟨pq, v⟩
  · simp [hl] at h
  · simp only [hl, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    exact ⟨pq, v, rfl, h.1.1.1, LabelPaths_isRight_of_labelFixedB Γ h.1.1.2, h.1.2, h.2⟩


section Pieces

variable (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length))

/-- A component outside `S` keeps its kind, ends and minor; its label is erased. -/
private theorem LabelPaths_piece_not_mem {i : Fin Γ.comps.length} (hi : i ∉ S) :
    LabelPaths_piece Γ S i = [LabelPaths_strip Γ.comps[i]] := by
  unfold LabelPaths_piece
  split
  · simp [hi, LabelPaths_strip]
  · next hl => rw [LabelPaths_strip_of_none _ hl]

/-- A component of `S` is random and is replaced by the path through its internal label atom. -/
private theorem LabelPaths_piece_mem (hS : S ⊆ Γ.pathElig) {i : Fin Γ.comps.length} (hi : i ∈ S) :
    ∃ v, LabelPaths_piece Γ S i = Γ.comps[i].pathVia v ∧ Γ.comps[i].kind.isRandom = true ∧
      v.isRight = true ∧ Γ.comps[i].x ≠ v ∧ Γ.comps[i].y ≠ v := by
  have h := hS hi
  simp only [Graph.pathElig, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨pq, v, hl, hr, hv, hx, hy⟩ := LabelPaths_of_pathEligB Γ h
  refine ⟨v, ?_, hr, hv, hx, hy⟩
  unfold LabelPaths_piece
  split
  · next pq' v' hl' =>
    rw [hl] at hl'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hl')
    simp [hi]
  · next hl' => rw [hl] at hl'; cases hl'

/-- The elements of the piece of the component with index `i`. -/
private theorem LabelPaths_mem_piece (hS : S ⊆ Γ.pathElig) {i : Fin Γ.comps.length}
    {d : Comp (Atom 3 n)} (hd : d ∈ LabelPaths_piece Γ S i) :
    (i ∉ S ∧ d = LabelPaths_strip Γ.comps[i]) ∨
      (i ∈ S ∧ ∃ v, v.isRight = true ∧ Γ.comps[i].x ≠ v ∧ Γ.comps[i].y ≠ v ∧
        Γ.comps[i].kind.isRandom = true ∧ d ∈ Γ.comps[i].pathVia v ∧
        LabelPaths_piece Γ S i = Γ.comps[i].pathVia v) := by
  by_cases hi : i ∈ S
  · obtain ⟨v, hp, hr, hv, hx, hy⟩ := LabelPaths_piece_mem Γ S hS hi
    exact Or.inr ⟨hi, v, hv, hx, hy, hr, hp ▸ hd, hp⟩
  · rw [LabelPaths_piece_not_mem Γ S hi] at hd
    exact Or.inl ⟨hi, List.mem_singleton.1 hd⟩

/-- The pieces are contained in the list before the removal of `×`-dotted edges. -/
private theorem LabelPaths_mem_cs {i : Fin Γ.comps.length} {d : Comp (Atom 3 n)}
    (hd : d ∈ LabelPaths_piece Γ S i) : d ∈ LabelPaths_cs Γ S :=
  List.mem_flatMap.2 ⟨i, List.mem_finRange i, hd⟩

/-- Membership in `Γ.pathRepl S`: an element of some piece that is kept. -/
private theorem LabelPaths_mem_iff (d : Comp (Atom 3 n)) :
    d ∈ (Γ.pathRepl S).comps ↔
      (∃ i, d ∈ LabelPaths_piece Γ S i) ∧ LabelPaths_keep Γ S d = true := by
  rw [LabelPaths_comps, List.mem_filter, LabelPaths_cs, List.mem_flatMap]
  simp

/-- Every component other than a `×`-dotted edge is kept. -/
private theorem LabelPaths_keep_of_ne {d : Comp (Atom 3 n)} (h : d.kind ≠ .xdot) :
    LabelPaths_keep Γ S d = true := by
  unfold LabelPaths_keep
  simp [h]

/-- A component whose ends carry a solid edge is kept. -/
private theorem LabelPaths_keep_of_solid {d c : Comp (Atom 3 n)} (hc : c ∈ LabelPaths_cs Γ S)
    (hs : c.kind.isSolid = true) (he : c.x = d.x ∧ c.y = d.y ∨ c.x = d.y ∧ c.y = d.x) :
    LabelPaths_keep Γ S d = true := by
  unfold LabelPaths_keep
  have : (LabelPaths_cs Γ S).any (fun c' => c'.kind.isSolid &&
      ((c'.x == d.x && c'.y == d.y) || (c'.x == d.y && c'.y == d.x))) = true :=
    List.any_eq_true.2 ⟨c, hc, by simpa [hs] using he⟩
  simp [this]

/-- A removed component is a `×`-dotted edge between distinct atoms without a solid edge. -/
private theorem LabelPaths_keep_false {d : Comp (Atom 3 n)} (h : LabelPaths_keep Γ S d = false) :
    d.kind = .xdot ∧ d.x ≠ d.y ∧ ∀ c ∈ LabelPaths_cs Γ S, c.kind.isSolid = true →
      ¬ (c.x = d.x ∧ c.y = d.y ∨ c.x = d.y ∧ c.y = d.x) := by
  refine ⟨?_, ?_, fun c hc hs he => ?_⟩
  · by_contra hk; simp [LabelPaths_keep_of_ne Γ S hk] at h
  · intro he
    unfold LabelPaths_keep at h
    simp [he] at h
  · simp [LabelPaths_keep_of_solid Γ S hc hs he] at h

/-- The origin of each component of `Γ.pathRepl S`: the index of the component of `Γ` whose piece
contains it; each kept element of a piece is a component of `Γ.pathRepl S` with that origin. -/
private theorem LabelPaths_index : ∃ o : Fin (Γ.pathRepl S).comps.length → Fin Γ.comps.length,
    (∀ j, (Γ.pathRepl S).comps[j] ∈ LabelPaths_piece Γ S (o j)) ∧
    ∀ i, ∀ d ∈ LabelPaths_piece Γ S i, LabelPaths_keep Γ S d = true →
      ∃ j, o j = i ∧ (Γ.pathRepl S).comps[j] = d := by
  set csT := (List.finRange Γ.comps.length).flatMap
    (fun i => (LabelPaths_piece Γ S i).map (fun d => (i, d))) with hcsT
  have hcs : LabelPaths_cs Γ S = csT.map Prod.snd := by
    rw [hcsT, LabelPaths_cs, List.map_flatMap]
    simp [List.map_map, Function.comp_def]
  set L := csT.filter (fun t => LabelPaths_keep Γ S t.2) with hLdef
  have hL : (Γ.pathRepl S).comps = L.map Prod.snd := by
    rw [LabelPaths_comps, hcs, List.filter_map]
    rfl
  have hlen : (Γ.pathRepl S).comps.length = L.length := by rw [hL, List.length_map]
  have hget : ∀ (j : ℕ) (hj : j < (Γ.pathRepl S).comps.length),
      (Γ.pathRepl S).comps[j] = (L[j]'(hlen ▸ hj)).2 := by
    intro j hj
    rw [List.getElem_of_eq hL hj, List.getElem_map]
  refine ⟨fun j => (L[j.1]'(hlen ▸ j.2)).1, fun j => ?_, fun i d hd hk => ?_⟩
  · rw [Fin.getElem_fin, hget j.1 j.2]
    have hm : L[j.1]'(hlen ▸ j.2) ∈ csT := (List.mem_filter.1 (List.getElem_mem _)).1
    rw [hcsT, List.mem_flatMap] at hm
    obtain ⟨i, -, hi⟩ := hm
    obtain ⟨d, hd, hdi⟩ := List.mem_map.1 hi
    dsimp only
    rw [← hdi]
    exact hd
  · have hm : (i, d) ∈ L := List.mem_filter.2
      ⟨List.mem_flatMap.2 ⟨i, List.mem_finRange i, List.mem_map.2 ⟨d, hd, rfl⟩⟩, hk⟩
    obtain ⟨k, hk', hLk⟩ := List.mem_iff_getElem.1 hm
    refine ⟨⟨k, hlen ▸ hk'⟩, ?_, ?_⟩
    · simp only [hLk]
    · rw [Fin.getElem_fin, hget k (hlen ▸ hk')]
      simp only [hLk]

/-- The components with a property `p` that holds on no random component and on no `×`-dotted
edge and does not read the label are, labels erased and in order, the same in `Γ.pathRepl S`
and in `Γ`. -/
private theorem LabelPaths_filter_map (hS : S ⊆ Γ.pathElig) (p : Comp (Atom 3 n) → Bool)
    (h1 : ∀ c, p (LabelPaths_strip c) = p c) (h2 : ∀ c, p c = true → c.kind.isRandom = false)
    (h3 : ∀ c, p c = true → c.kind ≠ .xdot) :
    ((Γ.pathRepl S).comps.filter p).map LabelPaths_strip =
      (Γ.comps.filter p).map LabelPaths_strip := by
  rw [LabelPaths_comps, List.filter_filter]
  have e1 : (LabelPaths_cs Γ S).filter (fun a => p a && LabelPaths_keep Γ S a) =
      (LabelPaths_cs Γ S).filter p := by
    apply List.filter_congr
    intro c _
    by_cases hp : p c = true
    · simp [hp, LabelPaths_keep_of_ne Γ S (h3 c hp)]
    · simp [hp]
  rw [e1, LabelPaths_cs]
  conv_rhs => rw [← List.map_getElem_finRange Γ.comps]
  rw [List.filter_flatMap, List.map_flatMap, List.filter_map, List.map_map, List.flatMap_def]
  have hpt : ∀ a : Fin Γ.comps.length,
      ((LabelPaths_piece Γ S a).filter p).map LabelPaths_strip =
        if p Γ.comps[(a : ℕ)] then [LabelPaths_strip Γ.comps[(a : ℕ)]] else [] := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨v, hp, hr, -⟩ := LabelPaths_piece_mem Γ S hS ha
      simp only [Fin.getElem_fin] at hp hr
      have hpa : p Γ.comps[(a : ℕ)] = false := by
        by_contra h
        have := h2 _ (by simpa using h)
        simp_all
      have hnil : (Γ.comps[(a : ℕ)].pathVia v).filter p = [] := by
        refine List.filter_eq_nil_iff.2 fun d hd => ?_
        obtain ⟨-, -, hk, -⟩ := LabelPaths_mem_pathVia hd
        intro hpd
        rcases hk with hk | ⟨ch, hk⟩
        · exact h3 d hpd hk
        · have := h2 d hpd
          simp [hk, Kind.isRandom] at this
      rw [hp, hnil]
      simp [hpa]
    · rw [LabelPaths_piece_not_mem Γ S ha]
      simp only [Fin.getElem_fin]
      by_cases hpa : p Γ.comps[(a : ℕ)] = true
      · simp only [List.filter_cons, h1, hpa, ite_true, List.filter_nil, List.map_cons,
          List.map_nil]
        rfl
      · simp [h1, hpa]
  simp only [hpt]
  generalize List.finRange Γ.comps.length = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p Γ.comps[(a : ℕ)] = true
    · simp [h, ih]
    · simp [h, ih]

/-- The components of a kind with a property `P` that holds on no random kind and not on the
`×`-dotted edge, with ends satisfying `Q`, exist in `Γ.pathRepl S` exactly when they exist in
`Γ`. -/
private theorem LabelPaths_exists_iff (hS : S ⊆ Γ.pathElig) (P : Kind → Prop) [DecidablePred P]
    (hr : ∀ k, P k → k.isRandom = false) (hx : ∀ k, P k → k ≠ .xdot)
    (Q : Atom 3 n → Atom 3 n → Prop) :
    (∃ d ∈ (Γ.pathRepl S).comps, P d.kind ∧ Q d.x d.y) ↔ ∃ c ∈ Γ.comps, P c.kind ∧ Q c.x c.y := by
  have hm := LabelPaths_filter_map Γ S hS (fun c => decide (P c.kind)) (fun _ => rfl)
    (fun c h => hr _ (of_decide_eq_true h)) (fun c h => hx _ (of_decide_eq_true h))
  constructor
  · rintro ⟨d, hd, hP, hQ⟩
    have : LabelPaths_strip d ∈
        ((Γ.comps.filter fun c => decide (P c.kind)).map LabelPaths_strip) :=
      hm ▸ List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd, decide_eq_true hP⟩, rfl⟩
    obtain ⟨c, hc, he⟩ := List.mem_map.1 this
    obtain ⟨hc, hPc⟩ := List.mem_filter.1 hc
    have hk : c.kind = d.kind := (congrArg Comp.kind he :)
    have hx : c.x = d.x := (congrArg Comp.x he :)
    have hy : c.y = d.y := (congrArg Comp.y he :)
    exact ⟨c, hc, of_decide_eq_true hPc, hx ▸ hy ▸ hQ⟩
  · rintro ⟨c, hc, hP, hQ⟩
    have : LabelPaths_strip c ∈ (((Γ.pathRepl S).comps.filter fun c => decide (P c.kind)).map
        LabelPaths_strip) :=
      hm.symm ▸ List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, decide_eq_true hP⟩, rfl⟩
    obtain ⟨d, hd, he⟩ := List.mem_map.1 this
    obtain ⟨hd, hPd⟩ := List.mem_filter.1 hd
    have hx : d.x = c.x := (congrArg Comp.x he :)
    have hy : d.y = c.y := (congrArg Comp.y he :)
    exact ⟨d, hd, of_decide_eq_true hPd, hx ▸ hy ▸ hQ⟩

end Pieces

/-- The dotted blocks read only the ends of the dotted edges, in order. -/
private theorem LabelPaths_dotBlocks_eq {V : Type*} [DecidableEq V] (as : List V)
    (cs : List (Comp V)) : dotBlocks as cs =
      dotBlocks as ((cs.filter fun c => decide (c.kind = .dot)).map LabelPaths_strip) := by
  unfold dotBlocks
  rw [List.foldl_map, List.foldl_filter]
  congr 1
  funext P c
  by_cases h : c.kind = .dot <;> simp [h, LabelPaths_strip]

section Dots

variable (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length)) (hS : S ⊆ Γ.pathElig)
include hS

/-- The dotted edges of `Γ.pathRepl S` are those of `Γ`, labels erased, in order. -/
private theorem LabelPaths_dots_map :
    (((Γ.pathRepl S).comps.filter fun c => decide (c.kind = .dot)).map LabelPaths_strip) =
      ((Γ.comps.filter fun c => decide (c.kind = .dot)).map LabelPaths_strip) :=
  LabelPaths_filter_map Γ S hS _ (fun _ => rfl)
    (fun c h => by rw [of_decide_eq_true h]; rfl)
    (fun c h => by rw [of_decide_eq_true h]; decide)

/-- `Γ.pathRepl S` and `Γ` have the same dotted blocks. -/
private theorem LabelPaths_dotBlocks :
    dotBlocks (allAtoms 3 n) (Γ.pathRepl S).comps = dotBlocks (allAtoms 3 n) Γ.comps := by
  rw [LabelPaths_dotBlocks_eq, LabelPaths_dots_map Γ S hS, ← LabelPaths_dotBlocks_eq]

/-- The dotted edges of `Γ.pathRepl S` form a forest exactly when those of `Γ` do. -/
private theorem LabelPaths_dotsAcyclic : (Γ.pathRepl S).DotsAcyclic ↔ Γ.DotsAcyclic := by
  unfold Graph.DotsAcyclic
  have := congrArg List.length (LabelPaths_dots_map Γ S hS)
  simp only [List.length_map] at this
  rw [this, LabelPaths_dotBlocks Γ S hS]

/-- `⊕`, `⊖` lie in one dotted block of `Γ.pathRepl S` exactly when they do in `Γ`. -/
private theorem LabelPaths_pmBlockB : (Γ.pathRepl S).pmBlockB = Γ.pmBlockB := by
  unfold Graph.pmBlockB
  rw [LabelPaths_dotBlocks Γ S hS]

/-- `Γ.pathRepl S` is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` exactly when `Γ` is. -/
private theorem LabelPaths_diagRecoll : (Γ.pathRepl S).DiagRecoll ↔ Γ.DiagRecoll := by
  unfold Graph.DiagRecoll
  rw [LabelPaths_dotBlocks Γ S hS]

/-- `Γ.pathRepl S` and `Γ` have the same graph of dotted edges. -/
private theorem LabelPaths_dotGraph : (Γ.pathRepl S).dotGraph = Γ.dotGraph := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
  have h := fun (u v : Atom 3 n) => LabelPaths_exists_iff Γ S hS (fun k => k = .dot)
    (fun k hk => by rw [hk]; rfl) (fun k hk => by rw [hk]; decide) (fun a b => a = u ∧ b = v)
  have h' := fun (u v : Atom 3 n) => LabelPaths_exists_iff Γ S hS (fun k => k = .dot)
    (fun k hk => by rw [hk]; rfl) (fun k hk => by rw [hk]; decide) (fun a b => a = v ∧ b = u)
  rw [h u v, h' u v]

/-- An external atom is identified with an internal atom in `Γ.pathRepl S` exactly when it is in
`Γ`. -/
private theorem LabelPaths_unpinned (u : Atom 3 n) : (Γ.pathRepl S).Unpinned u ↔ Γ.Unpinned u := by
  unfold Graph.Unpinned Graph.SameBlock
  rw [LabelPaths_dotGraph Γ S hS]

/-- `Γ.pathRepl S` and `Γ` have the same graph of waved and dotted edges. -/
private theorem LabelPaths_molGraph : (Γ.pathRepl S).molGraph = Γ.molGraph := by
  ext u v
  simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
  have hr : ∀ k : Kind, k.joinsMol = true → k.isRandom = false := by
    intro k hk; cases k <;> simp_all [Kind.joinsMol, Kind.isRandom]
  have hx : ∀ k : Kind, k.joinsMol = true → k ≠ .xdot := by
    intro k hk; cases k <;> simp_all [Kind.joinsMol]
  have h := LabelPaths_exists_iff Γ S hS (fun k => k.joinsMol = true) hr hx
    (fun a b => a = u ∧ b = v)
  have h' := LabelPaths_exists_iff Γ S hS (fun k => k.joinsMol = true) hr hx
    (fun a b => a = v ∧ b = u)
  rw [h, h']

/-- `Γ.pathRepl S` and `Γ` have the same molecules. -/
private theorem LabelPaths_sameMol (u v : Atom 3 n) :
    (Γ.pathRepl S).SameMol u v ↔ Γ.SameMol u v := by
  unfold Graph.SameMol
  rw [LabelPaths_molGraph Γ S hS]

end Dots

/-- A reachability transfer: each edge of `G` is a path of `H`. -/
private theorem LabelPaths_reach_lift {V : Type*} {G H : SimpleGraph V}
    (h : ∀ a b, G.Adj a b → H.Reachable a b) {a b : V} (hab : G.Reachable a b) :
    H.Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab
  induction hab with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

/-- Random kinds are not diffusive. -/
private theorem LabelPaths_random_not_diffusive {k : Kind} (h : k.isRandom = true) :
    k.isDiffusive = false := by
  cases k <;> simp_all [Kind.isRandom, Kind.isDiffusive]

section Comps

variable (Γ : Graph 3 n) (S : Finset (Fin Γ.comps.length)) (hS : S ⊆ Γ.pathElig)
include hS

/-- Each component of `Γ.pathRepl S` is the component of `Γ` with its label erased, or lies on the
path replacing a component of `S` through an internal label atom. -/
private theorem LabelPaths_origin {d : Comp (Atom 3 n)} (hd : d ∈ (Γ.pathRepl S).comps) :
    ∃ i : Fin Γ.comps.length, (i ∉ S ∧ d = LabelPaths_strip Γ.comps[i]) ∨
      (i ∈ S ∧ ∃ v, v.isRight = true ∧ Γ.comps[i].x ≠ v ∧ Γ.comps[i].y ≠ v ∧
        Γ.comps[i].kind.isRandom = true ∧ d ∈ Γ.comps[i].pathVia v ∧
        LabelPaths_piece Γ S i = Γ.comps[i].pathVia v) := by
  obtain ⟨⟨i, hi⟩, -⟩ := (LabelPaths_mem_iff Γ S d).1 hd
  exact ⟨i, LabelPaths_mem_piece Γ S hS hi⟩

/-- A component that is not random is not in `S`. -/
private theorem LabelPaths_not_mem_of_random {i : Fin Γ.comps.length}
    (h : Γ.comps[i].kind.isRandom = false) : i ∉ S := by
  intro hi
  obtain ⟨v, -, hr, -⟩ := LabelPaths_piece_mem Γ S hS hi
  simp only [Fin.getElem_fin] at h hr
  simp [hr] at h

omit hS in
/-- A component outside `S` that is not a `×`-dotted edge survives with its label erased. -/
private theorem LabelPaths_strip_mem {i : Fin Γ.comps.length} (hi : i ∉ S)
    (hk : Γ.comps[i].kind ≠ .xdot) : LabelPaths_strip Γ.comps[i] ∈ (Γ.pathRepl S).comps := by
  refine (LabelPaths_mem_iff Γ S _).2 ⟨⟨i, ?_⟩, LabelPaths_keep_of_ne Γ S hk⟩
  rw [LabelPaths_piece_not_mem Γ S hi]
  exact List.mem_singleton_self _

/-- The path replacing a component of `S`: its two solid edges are components of `Γ.pathRepl S`. -/
private theorem LabelPaths_path_mem {i : Fin Γ.comps.length} (hi : i ∈ S) :
    ∃ v, v.isRight = true ∧ Γ.comps[i].x ≠ v ∧ Γ.comps[i].y ≠ v ∧
      Γ.comps[i].kind.isRandom = true ∧
      (⟨.G (LabelPaths_ch Γ.comps[i]), Γ.comps[i].x, v, [], none⟩ : Comp (Atom 3 n)) ∈
        (Γ.pathRepl S).comps ∧
      (⟨.G (LabelPaths_ch Γ.comps[i]), v, Γ.comps[i].y, [], none⟩ : Comp (Atom 3 n)) ∈
        (Γ.pathRepl S).comps := by
  obtain ⟨v, hp, hr, hv, hx, hy⟩ := LabelPaths_piece_mem Γ S hS hi
  refine ⟨v, hv, hx, hy, hr, (LabelPaths_mem_iff Γ S _).2 ⟨⟨i, ?_⟩, ?_⟩,
    (LabelPaths_mem_iff Γ S _).2 ⟨⟨i, ?_⟩, ?_⟩⟩
  · rw [hp, LabelPaths_pathVia_eq]; simp
  · exact LabelPaths_keep_of_ne Γ S (by simp)
  · rw [hp, LabelPaths_pathVia_eq]; simp
  · exact LabelPaths_keep_of_ne Γ S (by simp)

/-- `Γ.pathRepl S` carries no `P`/`Q` label. -/
private theorem LabelPaths_labelFree : (Γ.pathRepl S).LabelFree := by
  intro d hd
  obtain ⟨i, ⟨-, rfl⟩ | ⟨-, v, -, -, -, -, hdv, -⟩⟩ := LabelPaths_origin Γ S hS hd
  · rfl
  · exact (LabelPaths_mem_pathVia hdv).2.1

/-- `Γ.pathRepl S` has the kinds of [II, Def 3.2] when `Γ` has them. -/
private theorem LabelPaths_tKinds {N : ℕ} (hT : Γ.TKinds N) : (Γ.pathRepl S).TKinds N := by
  unfold Graph.TKinds at *
  refine List.all_eq_true.2 fun d hd => ?_
  obtain ⟨i, ⟨-, rfl⟩ | ⟨-, v, -, -, -, -, hdv, -⟩⟩ := LabelPaths_origin Γ S hS hd
  · exact List.all_eq_true.1 hT Γ.comps[(i : ℕ)] (List.getElem_mem i.2)
  · obtain ⟨hm, -, hk, -⟩ := LabelPaths_mem_pathVia hdv
    unfold Comp.isTKind
    rcases hk with hk | ⟨ch, hk⟩ <;> simp [hm, hk]

/-- Every component of `Γ.pathRepl S` at `⊗` is diffusive when this holds for `Γ`. -/
private theorem LabelPaths_tensorDiffusive (hT : Γ.TensorDiffusive) :
    (Γ.pathRepl S).TensorDiffusive := by
  unfold Graph.TensorDiffusive at *
  refine List.all_eq_true.2 fun d hd => ?_
  obtain ⟨i, ⟨-, rfl⟩ | ⟨-, v, hv, -, -, hr, hdv, -⟩⟩ := LabelPaths_origin Γ S hS hd
  · exact List.all_eq_true.1 hT Γ.comps[(i : ℕ)] (List.getElem_mem i.2)
  · have h0 := List.all_eq_true.1 hT Γ.comps[(i : ℕ)] (List.getElem_mem i.2)
    simp only [Fin.getElem_fin] at hr
    rw [LabelPaths_random_not_diffusive hr] at h0
    simp only [Bool.or_false, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h0
    have hv0 : v ≠ .inl 0 := by rintro rfl; simp at hv
    obtain ⟨-, -, -, he⟩ := LabelPaths_mem_pathVia hdv
    simp only [Fin.getElem_fin] at he
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    left
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact ⟨h0.1, hv0⟩
    · exact ⟨hv0, h0.2⟩

/-- A component with a property `P` that does not read the label, holds on no `×`-dotted edge, and
holds on a random component only if it is a solid edge whose path through an internal atom has an
edge with the property, is carried from `Γ` to `Γ.pathRepl S`. -/
private theorem LabelPaths_exists_transfer (P : Comp (Atom 3 n) → Prop)
    (h1 : ∀ c, P (LabelPaths_strip c) ↔ P c) (hx : ∀ c, P c → c.kind ≠ .xdot)
    (hr : ∀ c, P c → c.kind.isRandom = true → ∃ ch, c.kind = .G ch ∧ ∀ v : Atom 3 n,
      v.isRight = true → P ⟨.G ch, c.x, v, [], none⟩ ∨ P ⟨.G ch, v, c.y, [], none⟩)
    (h : ∃ c ∈ Γ.comps, P c) : ∃ d ∈ (Γ.pathRepl S).comps, P d := by
  obtain ⟨c, hc, hP⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
  by_cases hi : (⟨j, hj⟩ : Fin Γ.comps.length) ∈ S
  · obtain ⟨v, hv, -, -, hrand, hm1, hm2⟩ := LabelPaths_path_mem Γ S hS hi
    obtain ⟨ch, hk, hP'⟩ := hr _ hP hrand
    have hch : LabelPaths_ch Γ.comps[j] = ch := by simp [LabelPaths_ch, hk]
    simp only [Fin.getElem_fin, hch] at hm1 hm2
    rcases hP' v hv with h' | h'
    · exact ⟨_, hm1, h'⟩
    · exact ⟨_, hm2, h'⟩
  · exact ⟨_, LabelPaths_strip_mem Γ S hi (hx _ hP), (h1 _).2 hP⟩

/-- A solid edge of charge `ch`, a diffusive edge or a dotted edge at the atom `a` is carried from
`Γ` to `Γ.pathRepl S`. -/
private theorem LabelPaths_pm_witness (ch : Charge) (a : Atom 3 n)
    (h : Γ.comps.any (fun c => (c.kind == .G ch || c.kind.isDiffusive || c.kind == .dot) &&
      (c.x == a || c.y == a)) = true) :
    (Γ.pathRepl S).comps.any (fun c => (c.kind == .G ch || c.kind.isDiffusive || c.kind == .dot) &&
      (c.x == a || c.y == a)) = true := by
  obtain ⟨c, hc, hp⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 (LabelPaths_exists_transfer Γ S hS _ (fun _ => Iff.rfl)
    (fun c h hk => ?_) (fun c h hr => ?_) ⟨c, hc, hp⟩)
  · simp [hk, Kind.isDiffusive] at h
  · cases hk : c.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
    all_goals (intro b; tauto)

/-- Condition [II, Def 3.2 (9)] is carried from `Γ` to `Γ.pathRepl S`. -/
private theorem LabelPaths_atExternals (hA : Γ.AtExternals) : (Γ.pathRepl S).AtExternals := by
  obtain ⟨h0, h1, h2⟩ := hA
  refine ⟨?_, LabelPaths_pm_witness Γ S hS _ _ h1, LabelPaths_pm_witness Γ S hS _ _ h2⟩
  have hm := LabelPaths_filter_map Γ S hS
    (fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)) (fun _ => rfl)
    (fun c h => by
      cases hk : c.kind.isRandom
      · rfl
      · simp [LabelPaths_random_not_diffusive hk] at h)
    (fun c h hk => by simp [hk, Kind.isDiffusive] at h)
  have := congrArg List.length hm
  simp only [List.length_map] at this
  rw [this]
  exact h0

omit hS in
/-- A kept element of the list before the removal is a component of `Γ.pathRepl S`. -/
private theorem LabelPaths_mem_of_cs {d : Comp (Atom 3 n)} (hd : d ∈ LabelPaths_cs Γ S)
    (hk : LabelPaths_keep Γ S d = true) : d ∈ (Γ.pathRepl S).comps := by
  rw [LabelPaths_comps]
  exact List.mem_filter.2 ⟨hd, hk⟩

omit hS in
/-- The components of `Γ.pathRepl S` lie in the list before the removal. -/
private theorem LabelPaths_cs_of_mem {d : Comp (Atom 3 n)} (hd : d ∈ (Γ.pathRepl S).comps) :
    d ∈ LabelPaths_cs Γ S := by
  rw [LabelPaths_comps] at hd
  exact (List.mem_filter.1 hd).1

omit hS in
/-- The ends of a component of `Γ.pathRepl S` are joined in its graph of all components. -/
private theorem LabelPaths_edge_reach {d : Comp (Atom 3 n)} (hd : d ∈ (Γ.pathRepl S).comps) :
    (Γ.pathRepl S).edgeGraph.Reachable d.x d.y := by
  by_cases h : d.x = d.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨d, hd, rfl, rfl⟩⟩ |>.reachable

/-- The ends of a component of `S` are joined through the label atom in `Γ.pathRepl S`. -/
private theorem LabelPaths_reach_S {i : Fin Γ.comps.length} (hi : i ∈ S) :
    (Γ.pathRepl S).edgeGraph.Reachable Γ.comps[i].x Γ.comps[i].y := by
  obtain ⟨v, -, -, -, -, h1, h2⟩ := LabelPaths_path_mem Γ S hS hi
  exact (LabelPaths_edge_reach Γ S h1).trans (LabelPaths_edge_reach Γ S h2)

/-- For a normal graph `Γ`, the ends of every component of `Γ` are joined in the graph of all
components of `Γ.pathRepl S`; a removed `×`-dotted edge has a solid edge of `S` on its ends. -/
private theorem LabelPaths_reach {C : ℕ} (hN : Γ.Normal C) (i : Fin Γ.comps.length) :
    (Γ.pathRepl S).edgeGraph.Reachable Γ.comps[i].x Γ.comps[i].y := by
  by_cases hi : i ∈ S
  · exact LabelPaths_reach_S Γ S hS hi
  have hpc : LabelPaths_strip Γ.comps[i] ∈ LabelPaths_cs Γ S :=
    LabelPaths_mem_cs Γ S (i := i) (by rw [LabelPaths_piece_not_mem Γ S hi]; simp)
  cases hk : LabelPaths_keep Γ S (LabelPaths_strip Γ.comps[i])
  · obtain ⟨hx, hne, hno⟩ := LabelPaths_keep_false Γ S hk
    obtain ⟨c', hc', hs, he⟩ := (hN.2.2 _ _ hne).1 ⟨Γ.comps[i], List.getElem_mem i.2, hx,
      Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc'
    by_cases hjS : (⟨j, hj⟩ : Fin Γ.comps.length) ∈ S
    · have := LabelPaths_reach_S Γ S hS hjS
      simp only [Fin.getElem_fin] at this
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at this; exact this
      · rw [h1, h2] at this; exact this.symm
    · exfalso
      have hpj : LabelPaths_strip Γ.comps[j] ∈ LabelPaths_cs Γ S :=
        LabelPaths_mem_cs Γ S (i := ⟨j, hj⟩) (by rw [LabelPaths_piece_not_mem Γ S hjS]; simp)
      exact hno _ hpj hs (by simpa [LabelPaths_strip] using he)
  · exact LabelPaths_edge_reach Γ S (d := LabelPaths_strip Γ.comps[i])
      (LabelPaths_mem_of_cs Γ S hpc hk)

omit hS in
/-- Each solid edge of the path `x–v–y` has a `×`-dotted edge of the path on its ends. -/
private theorem LabelPaths_solid_xdot {V : Type*} {c d : Comp V} {v : V} (hd : d ∈ c.pathVia v)
    (hs : d.kind.isSolid = true) :
    ∃ e ∈ c.pathVia v, e.kind = .xdot ∧ e.x = d.x ∧ e.y = d.y := by
  rw [LabelPaths_pathVia_eq] at hd ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact ⟨⟨.xdot, c.x, v, [], none⟩, by simp, rfl, rfl, rfl⟩
  · exact ⟨⟨.xdot, v, c.y, [], none⟩, by simp, rfl, rfl, rfl⟩
  · simp [Kind.isSolid] at hs
  · simp [Kind.isSolid] at hs

/-- `Γ.pathRepl S` is normal regular when `Γ` is ([II, Def 2.5]). -/
private theorem LabelPaths_normal {C : ℕ} (hN : Γ.Normal C) :
    (Γ.pathRepl S).Normal (3 + n + (Γ.pathRepl S).comps.length) := by
  have hN' := hN
  obtain ⟨⟨-, hconn, hint, hdot⟩, hsolid, hxs⟩ := hN
  refine ⟨⟨le_rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b
    refine LabelPaths_reach_lift (fun a b hab => ?_) (hconn a b)
    obtain ⟨-, ⟨c, hc, rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
      exact LabelPaths_reach Γ S hS hN' ⟨j, hj⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
      exact (LabelPaths_reach Γ S hS hN' ⟨j, hj⟩).symm
  · have hr : ∀ k : Kind, (k.joinsMol = true ∧ k ≠ .dot ∨ k.isDiffusive = true) →
        k.isRandom = false := by
      intro k hk; cases k <;> simp_all [Kind.joinsMol, Kind.isDiffusive, Kind.isRandom]
    have hx : ∀ k : Kind, (k.joinsMol = true ∧ k ≠ .dot ∨ k.isDiffusive = true) → k ≠ .xdot := by
      intro k hk; cases k <;> simp_all [Kind.joinsMol, Kind.isDiffusive]
    have hle : Γ.wavedThetaGraph ≤ (Γ.pathRepl S).wavedThetaGraph := by
      intro u v huv
      rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv ⊢
      obtain ⟨hne, h | h⟩ := huv
      · exact ⟨hne, Or.inl ((LabelPaths_exists_iff Γ S hS _ hr hx (fun a b => a = u ∧ b = v)).2 h)⟩
      · exact ⟨hne, Or.inr ((LabelPaths_exists_iff Γ S hS _ hr hx (fun a b => a = v ∧ b = u)).2 h)⟩
    intro a b
    exact (hint a b).mono hle
  · intro d hd hk
    obtain ⟨i, ⟨-, rfl⟩ | ⟨-, v, -, -, -, -, hdv, -⟩⟩ := LabelPaths_origin Γ S hS hd
    · exact hdot Γ.comps[(i : ℕ)] (List.getElem_mem i.2) hk
    · obtain ⟨-, -, hk', -⟩ := LabelPaths_mem_pathVia hdv
      rcases hk' with hk' | ⟨ch, hk'⟩ <;> rw [hk'] at hk <;> cases hk
  · intro d hd hs
    obtain ⟨i, ⟨-, rfl⟩ | ⟨-, v, -, hx, hy, -, hdv, -⟩⟩ := LabelPaths_origin Γ S hS hd
    · exact hsolid Γ.comps[(i : ℕ)] (List.getElem_mem i.2) hs
    · rw [LabelPaths_pathVia_eq] at hdv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdv
      rcases hdv with rfl | rfl | rfl | rfl
      · exact hx
      · exact fun h => hy h.symm
      · simp [Kind.isSolid] at hs
      · simp [Kind.isSolid] at hs
  · intro u w huw
    constructor
    · rintro ⟨d, hd, hk, he⟩
      obtain ⟨-, hkeep⟩ := (LabelPaths_mem_iff Γ S d).1 hd
      have hne : d.x ≠ d.y := by
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact huw
        · exact huw.symm
      have hany : (LabelPaths_cs Γ S).any (fun c' => c'.kind.isSolid &&
          ((c'.x == d.x && c'.y == d.y) || (c'.x == d.y && c'.y == d.x))) = true := by
        unfold LabelPaths_keep at hkeep
        simpa [hk, hne] using hkeep
      obtain ⟨c, hc, hcs⟩ := List.any_eq_true.1 hany
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcs
      refine ⟨c, LabelPaths_mem_of_cs Γ S hc (LabelPaths_keep_of_ne Γ S ?_), hcs.1, ?_⟩
      · intro h; simp [h, Kind.isSolid] at hcs
      · rcases hcs.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    · rintro ⟨d, hd, hs, he⟩
      obtain ⟨i, ⟨hi, rfl⟩ | ⟨hi, v, -, -, -, -, hdv, hp⟩⟩ := LabelPaths_origin Γ S hS hd
      · obtain ⟨e, he', hek, hee⟩ :=
          (hxs u w huw).2 ⟨Γ.comps[(i : ℕ)], List.getElem_mem i.2, hs, he⟩
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he'
        have hjS : (⟨j, hj⟩ : Fin Γ.comps.length) ∉ S :=
          LabelPaths_not_mem_of_random Γ S hS (by simp [hek, Kind.isRandom])
        refine ⟨LabelPaths_strip Γ.comps[j], LabelPaths_mem_of_cs Γ S
          (LabelPaths_mem_cs Γ S (i := ⟨j, hj⟩) (by rw [LabelPaths_piece_not_mem Γ S hjS]; simp))
          (LabelPaths_keep_of_solid Γ S (LabelPaths_cs_of_mem Γ S hd) hs ?_), hek, hee⟩
        dsimp only [LabelPaths_strip] at he ⊢
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hee with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
          rw [h1, h2, h3, h4] <;> tauto
      · obtain ⟨e, he1, hek, hex, hey⟩ := LabelPaths_solid_xdot hdv hs
        refine ⟨e, LabelPaths_mem_of_cs Γ S (LabelPaths_mem_cs Γ S (i := i) (hp ▸ he1))
          (LabelPaths_keep_of_solid Γ S (LabelPaths_cs_of_mem Γ S hd) hs
            (Or.inl ⟨hex.symm, hey.symm⟩)), hek, by rw [hex, hey]; exact he⟩

omit hS in
/-- The ends of an edge of the set `B'` are joined in `net B'`. -/
private theorem LabelPaths_net_reach {Γ' : Graph 3 n} {B' : Finset (Fin Γ'.comps.length)}
    {j : Fin Γ'.comps.length} (hj : j ∈ B') {a b : Fin n} (ha : Γ'.comps[j].x = .inr a)
    (hb : Γ'.comps[j].y = .inr b) : (Γ'.net B').Reachable a b := by
  by_cases h : a = b
  · rw [h]
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl (Or.inr ⟨j, hj, ha, hb⟩)⟩).reachable

omit hS in
/-- A spanning net of `Γ` gives a spanning net of a graph with the same molecules in which every
edge of the net between internal atoms is a path. -/
private theorem LabelPaths_spans_lift {Γ' : Graph 3 n} {B : Finset (Fin Γ.comps.length)}
    {B' : Finset (Fin Γ'.comps.length)} (hmol : ∀ u v, Γ'.SameMol u v ↔ Γ.SameMol u v)
    (hB : ∀ i ∈ B, ∀ a b, Γ.comps[i].x = .inr a → Γ.comps[i].y = .inr b →
      (Γ'.net B').Reachable a b) (h : Γ.Spans B) : Γ'.Spans B' := by
  intro a b
  refine LabelPaths_reach_lift (fun a b hab => ?_) (h a b)
  obtain ⟨hne, h1 | h1⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hab
  · rcases h1 with hm | ⟨i, hi, ha, hb⟩
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl (Or.inl ((hmol _ _).2 hm))⟩).reachable
    · exact hB i hi a b ha hb
  · rcases h1 with hm | ⟨i, hi, ha, hb⟩
    · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inr (Or.inl ((hmol _ _).2 hm))⟩).reachable
    · exact (hB i hi b a ha hb).symm

/-- `Γ.pathRepl S` is doubly connected when `Γ` is: the black net is carried over, and the blue
net with each blue solid edge of `S` replaced by its two blue solid edges through the internal
label atom. -/
private theorem LabelPaths_doublyConnected (hD : Γ.DoublyConnected) :
    (Γ.pathRepl S).DoublyConnected := by
  classical
  obtain ⟨black, blue, hdis, hbk, hbl, hsb, hsu⟩ := hD
  obtain ⟨o, ho1, ho2⟩ := LabelPaths_index Γ S
  have hdiffS : ∀ i : Fin Γ.comps.length, Γ.comps[i].kind.isDiffusive = true → i ∉ S := by
    intro i hi
    refine LabelPaths_not_mem_of_random Γ S hS ?_
    cases hr : Γ.comps[i].kind.isRandom
    · rfl
    · simp only [Fin.getElem_fin] at hi hr
      simp [LabelPaths_random_not_diffusive hr] at hi
  have hstrip : ∀ j, o j ∉ S → (Γ.pathRepl S).comps[j] = LabelPaths_strip Γ.comps[o j] := by
    intro j hj
    have := ho1 j
    rw [LabelPaths_piece_not_mem Γ S hj] at this
    exact List.mem_singleton.1 this
  have hkept : ∀ i : Fin Γ.comps.length, i ∉ S → Γ.comps[i].kind ≠ .xdot →
      ∃ j, o j = i ∧ (Γ.pathRepl S).comps[j] = LabelPaths_strip Γ.comps[i] := by
    intro i hi hk
    exact ho2 i _ (by rw [LabelPaths_piece_not_mem Γ S hi]; simp) (LabelPaths_keep_of_ne Γ S hk)
  refine ⟨Finset.univ.filter (fun j => o j ∈ black),
    Finset.univ.filter (fun j => o j ∈ blue ∧ (Γ.pathRepl S).comps[j].kind ≠ .xdot), ?_, ?_, ?_,
    LabelPaths_spans_lift Γ (LabelPaths_sameMol Γ S hS) ?_ hsb,
    LabelPaths_spans_lift Γ (LabelPaths_sameMol Γ S hS) ?_ hsu⟩
  · refine Finset.disjoint_left.2 fun j h1 h2 => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact Finset.disjoint_left.1 hdis h1 h2.1
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hd := hbk _ hj
    rw [hstrip j (hdiffS _ hd)]
    exact hd
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hd := hbl _ hj.1
    by_cases hjS : o j ∈ S
    · obtain ⟨v, hp, hr, -⟩ := LabelPaths_piece_mem Γ S hS hjS
      have hm := ho1 j
      rw [hp, LabelPaths_pathVia_eq] at hm
      have hG : Γ.comps[o j].kind = .G .plus := by
        revert hd hr
        cases Γ.comps[o j].kind <;> simp [Kind.isRandom, Kind.isDiffusive, Kind.isBlue]
        all_goals
          rename_i ch
          cases ch <;> simp
      have hch : LabelPaths_ch Γ.comps[o j] = .plus := by
        simp only [Fin.getElem_fin] at hG ⊢
        simp [LabelPaths_ch, hG]
      rw [hch] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> rw [h] at hj ⊢
      · simp [Kind.isBlue]
      · simp [Kind.isBlue]
      · exact absurd rfl hj.2
      · exact absurd rfl hj.2
    · rw [hstrip j hjS]
      exact hd
  · intro i hi a b ha hb
    have hd := hbk _ hi
    obtain ⟨j, hj, hc⟩ := hkept i (hdiffS _ hd) (by
      intro hk; rw [hk] at hd; simp [Kind.isDiffusive] at hd)
    simp only [Fin.getElem_fin] at hc ha hb
    exact LabelPaths_net_reach (j := j) (by simp [hj, hi])
      (by simp only [Fin.getElem_fin]; rw [hc]; exact ha)
      (by simp only [Fin.getElem_fin]; rw [hc]; exact hb)
  · intro i hi a b ha hb
    have hd := hbl _ hi
    have hnx : Γ.comps[i].kind ≠ .xdot := by
      intro hk; rw [hk] at hd; simp [Kind.isDiffusive, Kind.isBlue] at hd
    by_cases hiS : i ∈ S
    · obtain ⟨v, hp, -, hv, -⟩ := LabelPaths_piece_mem Γ S hS hiS
      obtain ⟨c, rfl⟩ : ∃ c, v = .inr c := by
        cases v with
        | inl _ => simp at hv
        | inr c => exact ⟨c, rfl⟩
      obtain ⟨j1, hj1, hc1⟩ := ho2 i ⟨.G (LabelPaths_ch Γ.comps[i]), Γ.comps[i].x, .inr c, [], none⟩
        (by rw [hp, LabelPaths_pathVia_eq]; simp) (LabelPaths_keep_of_ne Γ S (by simp))
      obtain ⟨j2, hj2, hc2⟩ := ho2 i ⟨.G (LabelPaths_ch Γ.comps[i]), .inr c, Γ.comps[i].y, [], none⟩
        (by rw [hp, LabelPaths_pathVia_eq]; simp) (LabelPaths_keep_of_ne Γ S (by simp))
      simp only [Fin.getElem_fin] at hc1 hc2 ha hb
      refine (LabelPaths_net_reach (j := j1) ?_ (by simp only [Fin.getElem_fin]; rw [hc1]; exact ha)
        (by simp only [Fin.getElem_fin]; rw [hc1])).trans
        (LabelPaths_net_reach (j := j2) ?_ (by simp only [Fin.getElem_fin]; rw [hc2])
          (by simp only [Fin.getElem_fin]; rw [hc2]; exact hb))
      · simp [hj1, hi, hc1]
      · simp [hj2, hi, hc2]
    · obtain ⟨j, hj, hc⟩ := hkept i hiS hnx
      simp only [Fin.getElem_fin] at hc ha hb hnx
      refine LabelPaths_net_reach (j := j) ?_
        (by simp only [Fin.getElem_fin]; rw [hc]; exact ha)
        (by simp only [Fin.getElem_fin]; rw [hc]; exact hb)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.getElem_fin]
      rw [hj, hc]
      exact ⟨hi, hnx⟩

/-- `Γ.pathRepl S` is rooted at the external atoms when `Γ` is (`Graph.RootedAtExt`). -/
private theorem LabelPaths_rooted (hR : Γ.RootedAtExt) : (Γ.pathRepl S).RootedAtExt := by
  have hU : ∀ u, (Γ.pathRepl S).Unpinned u ↔ Γ.Unpinned u := LabelPaths_unpinned Γ S hS
  have hr : ∀ k : Kind, k.isDiffusive = true → k.isRandom = false := by
    intro k hk; cases k <;> simp_all [Kind.isDiffusive, Kind.isRandom]
  have hx : ∀ k : Kind, k.isDiffusive = true → k ≠ .xdot := by
    intro k hk; cases k <;> simp_all [Kind.isDiffusive]
  have hHas : ∀ u, Γ.HasDiffToPinned u → (Γ.pathRepl S).HasDiffToPinned u := by
    intro u h
    unfold Graph.HasDiffToPinned at *
    simp only [hU]
    exact (LabelPaths_exists_iff Γ S hS (fun k => k.isDiffusive = true) hr hx
      (fun a b => a = u ∧ ¬ Γ.Unpinned b ∨ b = u ∧ ¬ Γ.Unpinned a)).2 h
  have hTo : ∀ u, Γ.DiffToPinned u → (Γ.pathRepl S).DiffToPinned u := by
    intro u h d hd hdd
    simp only [hU]
    by_contra hneg
    obtain ⟨c, hc, hcd, hq⟩ := (LabelPaths_exists_iff Γ S hS (fun k => k.isDiffusive = true) hr hx
      (fun a b => ¬ ((a = u → ¬ Γ.Unpinned b) ∧ (b = u → ¬ Γ.Unpinned a)))).1 ⟨d, hd, hdd, hneg⟩
    exact hq (h c hc hcd)
  have hG : ∀ (ch : Charge) (a : Atom 3 n),
      (∃ c ∈ Γ.comps, c.kind = .G ch ∧
        (c.x = a ∧ c.y.isRight = true ∨ c.y = a ∧ c.x.isRight = true)) →
      ∃ c ∈ (Γ.pathRepl S).comps, c.kind = .G ch ∧
        (c.x = a ∧ c.y.isRight = true ∨ c.y = a ∧ c.x.isRight = true) := by
    intro ch a h
    refine LabelPaths_exists_transfer Γ S hS _ (fun _ => Iff.rfl) (fun c h hk => ?_)
      (fun c h _ => ?_) h
    · rw [h.1] at hk; cases hk
    · refine ⟨ch, h.1, fun v hv => ?_⟩
      rcases h.2 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl ⟨rfl, Or.inl ⟨h1, hv⟩⟩
      · exact Or.inr ⟨rfl, Or.inr ⟨h1, hv⟩⟩
  obtain ⟨⟨h0, h0'⟩, h1, h2⟩ := hR
  exact ⟨⟨hHas _ h0, hTo _ h0'⟩, h1.imp (hG _ _) (hHas _), h2.imp (hG _ _) (hHas _)⟩

omit hS in
/-- The removed `×`-dotted edges have scaling order `0`. -/
private theorem LabelPaths_sum_keep (l : List (Comp (Atom 3 n))) :
    ((l.filter (LabelPaths_keep Γ S)).map fun c => c.kind.ord).sum =
      (l.map fun c => c.kind.ord).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    cases hk : LabelPaths_keep Γ S c
    · obtain ⟨hx, -⟩ := LabelPaths_keep_false Γ S hk
      simp only [List.filter_cons, hk, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons]
      rw [ih, hx]
      simp [Kind.ord]
    · simp [hk, ih]

omit hS in
/-- A random component with a kind of [II, Def 3.2] has scaling order at most `1`. -/
private theorem LabelPaths_ord_le_one {N : ℕ} {c : Comp (Atom 3 n)} (hT : c.isTKind N = true)
    (hr : c.kind.isRandom = true) : c.kind.ord ≤ 1 := by
  rcases c with ⟨k, x, y, m, l⟩
  cases k <;> simp_all [Comp.isTKind, Kind.isRandom, Kind.ord]

/-- The scaling order of `Γ.pathRepl S` exceeds that of `Γ` by at least `|S|`: each component of
`S` (scaling order at most `1`) becomes a path of scaling order `2`. -/
private theorem LabelPaths_ord {N : ℕ} (hT : Γ.TKinds N) :
    Γ.ord + (S.card : ℤ) ≤ (Γ.pathRepl S).ord := by
  unfold Graph.ord
  rw [LabelPaths_comps, LabelPaths_sum_keep, LabelPaths_cs, List.map_flatMap, List.flatMap_def,
    List.sum_flatten, List.map_map, ← Fin.sum_univ_def]
  have hΓ : (Γ.comps.map fun c => c.kind.ord).sum =
      ∑ i : Fin Γ.comps.length, Γ.comps[(i : ℕ)].kind.ord := by
    rw [Fin.sum_univ_def]
    conv_lhs => rw [← List.map_getElem_finRange Γ.comps]
    rw [List.map_map]
    rfl
  rw [hΓ]
  have key : ∀ i : Fin Γ.comps.length,
      Γ.comps[(i : ℕ)].kind.ord + (if i ∈ S then 1 else 0) ≤
        ((LabelPaths_piece Γ S i).map fun c => c.kind.ord).sum := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨v, hp, hr, -⟩ := LabelPaths_piece_mem Γ S hS hi
      rw [hp, LabelPaths_pathVia_eq]
      have := LabelPaths_ord_le_one
        (List.all_eq_true.1 hT Γ.comps[(i : ℕ)] (List.getElem_mem i.2)) hr
      simp only [hi, ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have h1 : (Kind.G (LabelPaths_ch Γ.comps[i])).ord = 1 := rfl
      have h0 : Kind.xdot.ord = 0 := rfl
      rw [h1, h0]
      linarith
    · rw [LabelPaths_piece_not_mem Γ S hi]
      simp [hi, LabelPaths_strip]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_univ_mem] at hsum
  simp only [Function.comp_def] at hsum ⊢
  linarith

end Comps

end RBM8D.Graphs

namespace RBM8D

open Graphs

/-- The structure of the label-free graphs `Γ_S` of the label removal in the proofs of
[II, Claims 8.6, 8.7] (`labelPathsStmt`). -/
theorem labelPaths : labelPathsStmt := by
  intro nI C N Γ hN hT hA hD hTD hDA hR S hS
  have hDR := LabelPaths_diagRecoll Γ S hS
  have hord := LabelPaths_ord Γ S hS hT
  refine ⟨⟨_, LabelPaths_normal Γ S hS hN⟩, LabelPaths_tKinds Γ S hS hT,
    LabelPaths_atExternals Γ S hS hA, LabelPaths_doublyConnected Γ S hS hD,
    LabelPaths_tensorDiffusive Γ S hS hTD, (LabelPaths_dotsAcyclic Γ S hS).2 hDA,
    LabelPaths_labelFree Γ S hS, LabelPaths_pmBlockB Γ S hS, hDR,
    fun hn hd => LabelPaths_rooted Γ S hS (hR hn fun h => hd (hDR.2 h)), hord, ?_⟩
  unfold Graph.diagOrd
  rw [LabelPaths_pmBlockB Γ S hS]
  linarith

end RBM8D
