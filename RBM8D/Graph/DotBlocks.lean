module

public import RBM8D.Graph.Rooting
public import RBM8D.TExp.Defs

@[expose] public section

/-!
# Dotted blocks as connected components

The partition `dotBlocks` of the atoms of a graph into the blocks of atoms joined by paths of
dotted edges ([II, §4.4]) is the partition into the connected components of the graph of dotted
edges `Graph.dotGraph`:

* two atoms lie in one block of `dotBlocks` exactly when `Graph.SameBlock` holds;
* the number of blocks is the number of connected components of `Graph.dotGraph`;
* `⊕` and `⊖` lie in one dotted block (`Graph.PMBlock`) exactly when `Graph.SameBlock ⊕ ⊖`;
* the dotted edges form a forest without loops (`Graph.DotsAcyclic`) exactly when the dot excess
  is `0`; a dotted loop gives a positive dot excess.

With these, the rooting at the external atoms ([II, (8.33)–(8.42)], in the proof of
[II, Claim 8.6]): a graph with the clause on the external atoms, the charge pattern of the block
normal form, only diffusive edges at `⊗`, [II, Def 3.2 (9)] and dot excess `0` that is not a
`⊕`-recollision graph at `𝔟₁ = 𝔟₂` is rooted at `⊗`, `⊕`, `⊖`.
-/

namespace RBM8D.Graphs

/-! ## The fold `dotBlocks` -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
private def dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
private theorem dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    dotRel cs ≤ dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

omit [DecidableEq V] in
private theorem flatten_map_singleton (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
private def blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

private theorem dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, blockStep]

private theorem dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

private theorem dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [dotBlocks_nil, flatten_map_singleton]
  | append_singleton cs c ih =>
    rw [dotBlocks_snoc, blockStep]
    split_ifs
    · exact (joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

private theorem mem_dotBlocks_of_mem (as : List V) (cs : List (Comp V)) {a : V} (ha : a ∈ as) :
    ∃ B ∈ dotBlocks as cs, a ∈ B := by
  have := (dotBlocks_flatten_perm as cs).mem_iff.2 ha
  rwa [List.mem_flatten] at this

private theorem dotBlocks_conn (as : List V) (cs : List (Comp V)) :
    ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, Relation.EqvGen (dotRel cs) u v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB u hu v hv
    rw [dotBlocks_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact Relation.EqvGen.refl _
  | append_singleton cs c ih =>
    have hmono : ∀ u v, Relation.EqvGen (dotRel cs) u v →
        Relation.EqvGen (dotRel (cs ++ [c])) u v := fun u v h =>
      Relation.EqvGen.mono (dotRel_mono fun c' hc' => List.mem_append_left _ hc') u v h
    intro B hB u hu v hv
    rw [dotBlocks_snoc, blockStep] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact hmono _ _ (ih B (List.mem_of_mem_filter hB) u hu v hv)
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : Relation.EqvGen (dotRel (cs ++ [c])) c.x c.y :=
          Relation.EqvGen.rel _ _ ⟨c, List.mem_append_right _ (List.mem_singleton_self _), hk, rfl,
            rfl⟩
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, Relation.EqvGen (dotRel (cs ++ [c])) z c.x := by
          intro w hw z hz
          have hw' := List.mem_filter.1 hw
          have hcont := hw'.2
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hcont
          rcases hcont with hx | hy
          · exact hmono _ _ (ih w hw'.1 z hz _ hx)
          · exact (hmono _ _ (ih w hw'.1 z hz _ hy)).trans _ _ _ hxy.symm
        rw [List.mem_flatten] at hu hv
        obtain ⟨w₁, hw₁, hu⟩ := hu
        obtain ⟨w₂, hw₂, hv⟩ := hv
        exact (key w₁ hw₁ u hu).trans _ _ _ (key w₂ hw₂ v hv).symm
    · exact hmono _ _ (ih B hB u hu v hv)

private theorem dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [dotBlocks_snoc, blockStep]
    split_ifs with hk
    · rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨B, hB, hx, hy⟩ := ih' c' hc' hk'
        by_cases hcB : (B.contains c.x || B.contains c.y) = true
        · refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c.x || B.contains c.y).flatten,
            ?_, ?_, ?_⟩
          · unfold joinBlocks
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hx⟩
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hy⟩
        · refine ⟨B, ?_, hx, hy⟩
          unfold joinBlocks
          refine List.mem_append_left _ (List.mem_filter.2 ⟨hB, ?_⟩)
          simpa using hcB
      · rw [List.mem_singleton] at hc'
        subst hc'
        obtain ⟨hxa, hya⟩ := hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨B₁, hB₁, hx⟩ := mem_dotBlocks_of_mem as cs hxa
        obtain ⟨B₂, hB₂, hy⟩ := mem_dotBlocks_of_mem as cs hya
        refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c'.x || B.contains c'.y).flatten,
          ?_, ?_, ?_⟩
        · unfold joinBlocks
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [List.mem_flatten]
          exact ⟨B₁, List.mem_filter.2 ⟨hB₁, by simp [hx]⟩, hx⟩
        · rw [List.mem_flatten]
          exact ⟨B₂, List.mem_filter.2 ⟨hB₂, by simp [hy]⟩, hy⟩
    · rcases List.mem_append.1 hc' with hc' | hc'
      · exact ih' c' hc' hk'
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact absurd hk' hk

/-- Every block of `dotBlocks` is nonempty when the ends of the dotted components are atoms of
`as`. -/
private theorem dotBlocks_ne_nil (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as) : ∀ B ∈ dotBlocks as cs, B ≠ [] := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB
    rw [dotBlocks_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    exact List.cons_ne_nil _ _
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro B hB
    rw [dotBlocks_snoc, blockStep] at hB
    split_ifs at hB
    · unfold joinBlocks at hB
      rcases List.mem_append.1 hB with hB | hB
      · exact ih' B (List.mem_of_mem_filter hB)
      · rw [List.mem_singleton] at hB
        subst hB
        obtain ⟨B₁, hB₁, hx⟩ := mem_dotBlocks_of_mem as cs
          (hcs c (List.mem_append_right _ (List.mem_singleton_self _)))
        exact List.ne_nil_of_mem
          (List.mem_flatten.2 ⟨B₁, List.mem_filter.2 ⟨hB₁, by simp [hx]⟩, hx⟩)
    · exact ih' B hB

omit [DecidableEq V] in
/-- In a partition (a list of lists whose concatenation has no duplicate), an element lies in at
most one block. -/
private theorem block_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B₁ B₂ : List V}
    (h₁ : B₁ ∈ P) (h₂ : B₂ ∈ P) {v : V} (hv₁ : v ∈ B₁) (hv₂ : v ∈ B₂) : B₁ = B₂ := by
  by_contra hne
  rw [List.nodup_flatten] at hnd
  exact hnd.2.forall (R := List.Disjoint) h₁ h₂ hne hv₁ hv₂

omit [DecidableEq V] in
private theorem length_filter_or_le (P : List (List V)) (p q : List V → Bool) :
    (P.filter fun B => p B || q B).length ≤ (P.filter p).length + (P.filter q).length := by
  induction P with
  | nil => simp
  | cons a P ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

private theorem length_filter_contains_le {P : List (List V)} (hnd : P.flatten.Nodup) (u : V) :
    (P.filter fun B => B.contains u).length ≤ 1 := by
  induction P with
  | nil => simp
  | cons B P ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    by_cases hu : u ∈ B
    · have hnil : (P.filter fun B => B.contains u) = [] := by
        rw [List.filter_eq_nil_iff]
        intro B' hB' hc
        simp only [List.contains_iff_mem] at hc
        exact hnd.2.2 u hu u (List.mem_flatten.2 ⟨B', hB', hc⟩) rfl
      rw [List.filter_cons_of_pos (by simpa using hu), hnil]
      simp
    · rw [List.filter_cons_of_neg (by simpa using hu)]
      exact ih hnd.2.1

/-- Joining the blocks of `u` and `v` in a partition lowers the number of blocks by at most `1`,
and does not lower it when `u = v`. -/
private theorem length_joinBlocks_ge {P : List (List V)} (hnd : P.flatten.Nodup) (u v : V) :
    P.length ≤ (joinBlocks P u v).length + (if u = v then 0 else 1) := by
  unfold joinBlocks
  rw [List.length_append, List.length_singleton]
  have hsplit := List.length_eq_length_filter_add (l := P)
    (fun B : List V => B.contains u || B.contains v)
  have hu := length_filter_contains_le hnd u
  have hv := length_filter_contains_le hnd v
  have hor := length_filter_or_le P (fun B => B.contains u) (fun B => B.contains v)
  split_ifs with h
  · subst h
    simp only [Bool.or_self] at hsplit ⊢
    omega
  · omega

omit [DecidableEq V] in
private theorem length_filter_filter_singleton (c : Comp V) (p q : Comp V → Bool) :
    (([c].filter p).filter q).length = if p c = true ∧ q c = true then 1 else 0 := by
  cases hp : p c <;> cases hq : q c <;> simp [hp, hq]

/-- The number of blocks plus the number of dotted components that are not loops is at least
the number of atoms. -/
private theorem length_le_dotBlocks_add (as : List V) (hnd : as.Nodup) (cs : List (Comp V)) :
    as.length ≤ (dotBlocks as cs).length +
      ((cs.filter fun c => decide (c.kind = .dot)).filter fun c => decide (c.x ≠ c.y)).length := by
  induction cs using List.reverseRecOn with
  | nil => simp [dotBlocks_nil]
  | append_singleton cs c ih =>
    have hP : (dotBlocks as cs).flatten.Nodup := (dotBlocks_flatten_perm as cs).nodup_iff.2 hnd
    rw [dotBlocks_snoc, blockStep, List.filter_append, List.filter_append, List.length_append,
      length_filter_filter_singleton]
    generalize ((cs.filter fun c => decide (c.kind = .dot)).filter
      fun c => decide (c.x ≠ c.y)).length = F at ih ⊢
    by_cases hk : c.kind = .dot
    · have hj := length_joinBlocks_ge hP c.x c.y
      by_cases hxy : c.x = c.y
      · simp only [hk, hxy, ite_true, decide_true, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, and_false, ite_false] at hj ⊢
        omega
      · simp only [hk, hxy, ite_true, ite_false, decide_true, ne_eq, not_false_eq_true,
          and_self] at hj ⊢
        omega
    · simp only [hk, ite_false, decide_false, Bool.false_eq_true, false_and]
      omega

end Blocks

/-! ## The atoms -/

section Atoms

variable {k n : ℕ}

private theorem mem_allAtoms (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

private theorem allAtoms_nodup : (allAtoms k n).Nodup := by
  unfold allAtoms
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).map Sum.inl_injective,
    (List.nodup_finRange n).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  simp at hab

private theorem dotBlocks_nodup_flatten (Γ : Graph k n) :
    (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
  (dotBlocks_flatten_perm _ _).nodup_iff.2 allAtoms_nodup

private theorem reachable_of_eqvGen (Γ : Graph k n) {u v : Atom k n}
    (h : Relation.EqvGen (dotRel Γ.comps) u v) : Γ.dotGraph.Reachable u v := by
  induction h with
  | rel x y hxy =>
    by_cases hne : x = y
    · subst hne; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl hxy⟩
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two atoms lie in one block of `dotBlocks` exactly when they are joined by a path of dotted
edges (`Graph.SameBlock`): the blocks of [II, §4.4] are the connected components of
`Graph.dotGraph`. -/
theorem Graph.sameBlock_iff_mem_dotBlocks (Γ : Graph k n) (u v : Atom k n) :
    Γ.SameBlock u v ↔ ∃ B ∈ dotBlocks (allAtoms k n) Γ.comps, u ∈ B ∧ v ∈ B := by
  constructor
  · intro h
    rw [Graph.SameBlock, SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => obtain ⟨B, hB, hu⟩ := mem_dotBlocks_of_mem _ Γ.comps (mem_allAtoms u)
              exact ⟨B, hB, hu, hu⟩
    | tail _ hadj ih =>
      obtain ⟨B, hB, hu, hb⟩ := ih
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      have hcs : ∀ c ∈ Γ.comps, c.x ∈ allAtoms k n ∧ c.y ∈ allAtoms k n :=
        fun c _ => ⟨mem_allAtoms _, mem_allAtoms _⟩
      obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := hadj
      · obtain ⟨B', hB', hx, hy⟩ := dotBlocks_joined _ _ hcs c hc hk
        exact ⟨B', hB', block_eq_of_mem (dotBlocks_nodup_flatten Γ) hB hB' hb hx ▸ hu, hy⟩
      · obtain ⟨B', hB', hx, hy⟩ := dotBlocks_joined _ _ hcs c hc hk
        exact ⟨B', hB', block_eq_of_mem (dotBlocks_nodup_flatten Γ) hB hB' hb hy ▸ hu, hx⟩
  · rintro ⟨B, hB, hu, hv⟩
    exact reachable_of_eqvGen Γ (dotBlocks_conn _ _ B hB u hu v hv)

/-- The number of blocks of `dotBlocks` is the number of connected components of the graph of
dotted edges. -/
theorem Graph.dotBlocks_length_eq_card (Γ : Graph k n) :
    (dotBlocks (allAtoms k n) Γ.comps).length = Nat.card Γ.dotGraph.ConnectedComponent := by
  set P := dotBlocks (allAtoms k n) Γ.comps with hPdef
  have hnd : P.flatten.Nodup := dotBlocks_nodup_flatten Γ
  have hne : ∀ B ∈ P, B ≠ [] :=
    dotBlocks_ne_nil _ _ fun c _ => mem_allAtoms _
  have hPnd : P.Nodup := by
    have hpw := (List.nodup_flatten.1 hnd).2
    refine hpw.imp_of_mem fun {B₁ B₂} h₁ _ hd heq => ?_
    subst heq
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hne B₁ h₁)
    exact hd ha ha
  let f : Fin P.length → Γ.dotGraph.ConnectedComponent := fun i =>
    Γ.dotGraph.connectedComponentMk (P[i].head (hne _ (List.getElem_mem _)))
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hr := SimpleGraph.ConnectedComponent.exact hij
      obtain ⟨B, hB, hi, hj⟩ := (Γ.sameBlock_iff_mem_dotBlocks _ _).1 hr
      have e₁ := block_eq_of_mem hnd hB (List.getElem_mem (l := P) i.2) hi (List.head_mem _)
      have e₂ := block_eq_of_mem hnd hB (List.getElem_mem (l := P) j.2) hj (List.head_mem _)
      exact Fin.ext ((List.Nodup.getElem_inj_iff hPnd).1 (e₁.symm.trans e₂))
    · intro C
      induction C using SimpleGraph.ConnectedComponent.ind with
      | h v =>
        obtain ⟨B, hB, hv⟩ := mem_dotBlocks_of_mem _ Γ.comps (mem_allAtoms v)
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
        refine ⟨⟨i, hi⟩, SimpleGraph.ConnectedComponent.sound ?_⟩
        exact (Γ.sameBlock_iff_mem_dotBlocks _ _).2 ⟨P[i], hB, List.head_mem _, hv⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- `⊕` and `⊖` lie in one dotted block (`Graph.PMBlock`) exactly when they are joined by a path
of dotted edges. -/
theorem Graph.pmBlock_iff_sameBlock {n : ℕ} (Γ : Graph 3 n) :
    Γ.PMBlock ↔ Γ.SameBlock (.inl 1) (.inl 2) := by
  rw [Graph.sameBlock_iff_mem_dotBlocks, Graph.PMBlock, Graph.pmBlockB]
  simp [List.any_eq_true]

/-- The dotted edges form a forest without loops (`Graph.DotsAcyclic`) exactly when the dot
excess is `0`. -/
theorem Graph.dotsAcyclic_iff_dotExcess_eq_zero (Γ : Graph k n) :
    Γ.DotsAcyclic ↔ Γ.dotExcess = 0 := by
  rw [Graph.DotsAcyclic, Graph.dotExcess, Graph.nDots, ← Graph.dotBlocks_length_eq_card]
  push_cast
  omega

/-- A dotted loop gives a positive dot excess. -/
private theorem dotExcess_pos_of_loop (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) (hxy : c.x = c.y) : 0 < Γ.dotExcess := by
  have hle := length_le_dotBlocks_add (allAtoms k n) allAtoms_nodup Γ.comps
  have hlen : (allAtoms k n).length = k + n := by simp [allAtoms]
  set D := Γ.comps.filter fun c => decide (c.kind = .dot)
  have hsplit := List.length_eq_length_filter_add (l := D) (fun c => decide (c.x ≠ c.y))
  have hloop : 0 < (D.filter fun c => !decide (c.x ≠ c.y)).length :=
    List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_filter.2 ⟨hc, by simpa using hk⟩,
      by simp [hxy]⟩)
  rw [Graph.dotExcess, Graph.nDots, ← Graph.dotBlocks_length_eq_card]
  change 0 < (D.length : ℤ) - ((k + n : ℕ) : ℤ) + _
  omega

end Atoms

/-! ## The rooting at the external atoms -/

section Rooting

variable {n : ℕ}

private theorem unpinned_of_not_diagRecoll (Γ : Graph 3 n) (hD : ¬ Γ.DiagRecoll) {a : Fin 3}
    (ha : a = 1 ∨ a = 2) : Γ.Unpinned (.inl a) := by
  refine ⟨rfl, fun b hb => hD ?_⟩
  obtain ⟨B, hB, hu, hv⟩ := (Γ.sameBlock_iff_mem_dotBlocks _ _).1 hb
  rw [Graph.DiagRecoll, List.any_eq_true]
  refine ⟨B, hB, ?_⟩
  rcases ha with rfl | rfl <;>
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] <;>
    exact ⟨by simp [hu], .inr b, hv, rfl⟩

private theorem unpinned_zero_of_tensorDiffusive (Γ : Graph 3 n) (hT : Γ.TensorDiffusive) :
    Γ.Unpinned (.inl 0) := by
  refine ⟨rfl, fun b hb => ?_⟩
  rw [Graph.SameBlock, SimpleGraph.reachable_iff_reflTransGen] at hb
  rcases hb.cases_head with h | ⟨w, hadj, -⟩
  · exact Sum.inl_ne_inr h
  · rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    rw [Graph.TensorDiffusive, List.all_eq_true] at hT
    obtain ⟨-, ⟨c, hc, hk, hx, -⟩ | ⟨c, hc, hk, -, hy⟩⟩ := hadj
    · have := hT c hc
      simp [hk, hx, Kind.isDiffusive] at this
    · have := hT c hc
      simp [hk, hy, Kind.isDiffusive] at this

private theorem blockNorm_eq_self (Γ : Graph 3 n) (h : ∀ a : Fin 3, Γ.Unpinned (.inl a)) :
    Γ.blockNorm = Γ := by
  have hfa : ∀ u, Γ.flatAtom u = u := by
    rintro (a | i)
    · have hnone : Γ.anchor (.inl a) = none := by
        rw [Graph.anchor, List.find?_eq_none]
        intro b _
        simpa using (h a).2 b
      simp [Graph.flatAtom, hnone]
    · rfl
  have hfc : ∀ c, Γ.flatComp c = c := by
    intro c
    unfold Graph.flatComp
    split_ifs
    · rfl
    · rw [hfa, hfa]
  obtain ⟨cs, co⟩ := Γ
  simp only [Graph.blockNorm, Graph.mk.injEq, and_true]
  conv_rhs => rw [← List.map_id cs]
  exact List.map_congr_left fun c _ => hfc c

/-- **The rooting at the external atoms** (the properties (3)–(4) of the auxiliary graph of
[II, (8.33)–(8.42)] in the proof of [II, Claim 8.6]): a graph with the clause on the external
atoms, the charge pattern of the block normal form, only diffusive edges at `⊗`,
[II, Def 3.2 (9)] (`Graph.AtExternals`) and dot excess `0` (the dotted edges form a forest; in
particular no dotted edge is a loop) that is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`
(`Graph.DiagRecoll`) is rooted at the external atoms (`Graph.RootedAtExt`). -/
theorem rootedAtExt_of_extClause :
    ∀ (n₀ : ℕ) (Γ : Graph 3 n₀), Γ.ExtClause → Γ.ColourInvB → Γ.TensorDiffusive →
      Γ.AtExternals → Γ.dotExcess = 0 → ¬ Γ.DiagRecoll → Γ.RootedAtExt := by
  intro n₀ Γ hE hC hT hA hX hD
  obtain ⟨hE1, -, hE3, hE4, hE5⟩ := hE
  have hU0 := unpinned_zero_of_tensorDiffusive Γ hT
  have hU1 := unpinned_of_not_diagRecoll Γ hD (a := 1) (.inl rfl)
  have hU2 := unpinned_of_not_diagRecoll Γ hD (a := 2) (.inr rfl)
  have hC' : Γ.ColourInv' := by
    have hbn : Γ.blockNorm = Γ := blockNorm_eq_self Γ fun a => by
      fin_cases a
      exacts [hU0, hU1, hU2]
    rwa [Graph.ColourInvB, hbn] at hC
  -- the first atom of a solid edge is internal
  have hGx : ∀ c ∈ Γ.comps, ∀ ch, c.kind = .G ch → c.x.isRight = true := fun c hc ch hk =>
    ((hC' c hc).1 (by rw [hk]; rfl)).1
  refine ⟨hE3 hU0, ?_, ?_⟩
  · rcases (hE5 hU1).1 with ⟨c, hc, hk, hxy⟩ | h
    · have hx := hGx c hc _ hk
      rcases hxy with hx1 | hy1
      · rw [hx1] at hx; simp at hx
      · exact .inl ⟨c, hc, hk, .inr ⟨hy1, hx⟩⟩
    · exact .inr h
  · obtain ⟨c, hc, hck⟩ := List.any_eq_true.1 hA.2.2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hck
    obtain ⟨hkind, hend⟩ := hck
    rcases hkind with (hk | hk) | hk
    · -- a red solid edge at `⊖`
      have hx := hGx c hc _ hk
      rcases hend with hx2 | hy2
      · rw [hx2] at hx; simp at hx
      · exact .inl ⟨c, hc, hk, .inr ⟨hy2, hx⟩⟩
    · -- no diffusive edge is at the unpinned atom `⊖`
      have := (hE4 hU2).1 c hc hk
      rcases hend with h | h
      · exact absurd h this.1
      · exact absurd h this.2
    · -- a dotted edge at `⊖`: a loop gives a positive dot excess, another dotted edge puts an
      -- internal atom in the block of `⊖`
      by_cases hxy : c.x = c.y
      · exact absurd hX (dotExcess_pos_of_loop Γ hc hk hxy).ne'
      · exfalso
        have hr : Γ.SameBlock c.x c.y := by
          refine SimpleGraph.Adj.reachable ?_
          rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
          exact ⟨hxy, .inl ⟨c, hc, hk, rfl, rfl⟩⟩
        rcases hend with h | h
        · obtain ⟨b, hb⟩ := hE1 c.x c.y hxy hr
          exact hU2.2 b (h ▸ hb)
        · obtain ⟨b, hb⟩ := hE1 c.y c.x (Ne.symm hxy) hr.symm
          exact hU2.2 b (h ▸ hb)

end Rooting

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end Instances

end RBM8D.Graphs
