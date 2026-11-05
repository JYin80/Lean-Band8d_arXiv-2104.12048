import RBM8D.GlobalExp.SubstDC
import RBM8D.GlobalExp.SubstMol
import RBM8D.GlobalExp.GlueNormal

/-!
# [II, Lemma 6.5 (1), (2)]: the substituted graphs in the block reading

The substitution of a graph `g` for the `t`-variable `t_{y₁y₂,x}` of
`G = H.glue x y₁ y₂ (tVar true)` ([II, §4.3], picture (6.5) of [II, Lemma 6.5 (2)]), read on the
molecular graph of the block reading (`Graph.toMG'`):

* `substSPDB`: when `G` has no dotted edge, the invariant `Graph.InvB'` and the blue solid edge
  `G_{y₁α}` chosen by Step 2, and `g` is sequentially pre-deterministic with the clause on the
  external atoms, the charge pattern of the block normal form, only diffusive edges at `⊗`,
  [II, Def 3.2 (9)], no ghost edge and dot excess `0`, the substituted graph
  `H.glue x y₁ y₂ g.swapSolid` and its `O_dot` forms are sequentially pre-deterministic
  ([II, Def 5.9]). The molecular graph of `g` has exactly one present edge at each of `⊗`, `⊕`,
  `⊖`: a diffusive edge at `⊗`, a blue solid or diffusive edge at `⊕`, a red solid edge at `⊖`;
  it is inserted into that of `G` in place of `G_{y₁α}` and `Ḡ_{y₂α}` (the chain (6.6));
* `substGSB`: when moreover `G` and `g` are globally standard ([II, Def 6.2]) and `g` is a
  `⊕`-recollision graph at `𝔟₁ = 𝔟₂`, the substituted graph and its `O_dot` forms are globally
  standard;
* `globalGood_row1`, `globalGood_row2`: the conjunct of [II, Lemma 6.5 (1), (2)] on
  the leading term, the terms of `Σ_T` and the recollision terms of
  [II, (4.15)] (`globalGood_row1`), and on the graphs of `R` (`globalGood_row2`).

The dot excess `0` is needed for `substGSB`: when `⊖` is not identified with an internal atom
and the only component of `g` at `⊖` is a dotted loop `1_{⊖ = ⊖}`, no red solid edge takes the
place of `Ḡ_{y₂α}`, and an isolated subset of the molecular graph of `G` that is weakly isolated
([II, Def 6.1]) through `Ḡ_{y₂α}` becomes strongly isolated. The negative example:
`H = Θ_{⊗w} Θ_{xw} Θ_{xw} G_{w⊕} Ḡ_{x⊖}` with the `×`-dotted edges `w ≠ ⊕`, `x ≠ ⊖`, at
`y₁ = x`, `y₂ = w`, and `g = Θ_{⊗a} 1_{a = ⊕} 1_{⊖ = ⊖}` (dot excess `1`); the substituted
graph is sequentially pre-deterministic in the block reading but not globally standard: the
molecule of `x` is isolated with the single red solid edge `Ḡ_{x⊖}` to its complement.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

/-- `decide`, checked by the kernel. -/
local macro "kdec" : tactic => `(tactic| decide +kernel)

/-! ## Decision procedures -/

private instance SubstSPD_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance SubstSPD_decSameBlock {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameBlock :=
  fun u v => @SimpleGraph.instDecidableRelReachable _ _ _ _ (SubstSPD_decAdjDot Γ) u v

private instance SubstSPD_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

private instance SubstSPD_decAdjEdge {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.edgeGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.x = u ∧ c.y = v) ∨ (∃ c ∈ Γ.comps, c.x = v ∧ c.y = u))))

private instance SubstSPD_decAdjWavedTheta {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.wavedThetaGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = v ∧ c.y = u))))

private instance SubstSPD_decRegular {k n : ℕ} (C : ℕ) (Γ : Graph k n) :
    Decidable (Γ.Regular C) :=
  haveI : DecidableRel Γ.edgeGraph.Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (SubstSPD_decAdjEdge Γ)
  haveI : DecidableRel Γ.wavedThetaGraph.Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (SubstSPD_decAdjWavedTheta Γ)
  haveI : Decidable Γ.edgeGraph.Preconnected :=
    inferInstanceAs (Decidable (∀ u v, Γ.edgeGraph.Reachable u v))
  decidable_of_iff (k + n + Γ.comps.length ≤ C ∧ Γ.edgeGraph.Preconnected ∧
      (∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (.inr a) (.inr b)) ∧
      ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

private instance SubstSPD_decNormal {k n : ℕ} (C : ℕ) (Γ : Graph k n) :
    Decidable (Γ.Normal C) :=
  inferInstanceAs (Decidable (Γ.Regular C ∧ (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧
    ∀ u v : Atom k n, u ≠ v →
      ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))))

section MGraphs

variable {X Z : Type}

end MGraphs

/-! ## A dotted loop gives a positive dot excess -/

section DotLoop

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem SubstSPD_flatten_single (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem SubstSPD_join_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

private theorem SubstSPD_blocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) =
      if c.kind = .dot then joinBlocks (dotBlocks as cs) c.x c.y else dotBlocks as cs := by
  simp [dotBlocks, List.foldl_append]

private theorem SubstSPD_blocks_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => simp only [dotBlocks, List.foldl_nil]; rw [SubstSPD_flatten_single]
  | append_singleton cs c ih =>
    rw [SubstSPD_blocks_snoc]
    split_ifs
    · exact (SubstSPD_join_perm _ _ _).trans ih
    · exact ih

omit [DecidableEq V] in
private theorem SubstSPD_filter_or_le (P : List (List V)) (p q : List V → Bool) :
    (P.filter fun B => p B || q B).length ≤ (P.filter p).length + (P.filter q).length := by
  induction P with
  | nil => simp
  | cons a P ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> omega

private theorem SubstSPD_filter_contains_le {P : List (List V)} (hnd : P.flatten.Nodup) (u : V) :
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

private theorem SubstSPD_join_length {P : List (List V)} (hnd : P.flatten.Nodup) (u v : V) :
    P.length ≤ (joinBlocks P u v).length + (if u = v then 0 else 1) := by
  unfold joinBlocks
  rw [List.length_append, List.length_singleton]
  have hsplit := List.length_eq_length_filter_add (l := P)
    (fun B : List V => B.contains u || B.contains v)
  have hu := SubstSPD_filter_contains_le hnd u
  have hv := SubstSPD_filter_contains_le hnd v
  have hor := SubstSPD_filter_or_le P (fun B => B.contains u) (fun B => B.contains v)
  split_ifs with h
  · subst h
    simp only [Bool.or_self] at hsplit ⊢
    omega
  · omega

omit [DecidableEq V] in
private theorem SubstSPD_filter_single (c : Comp V) (p q : Comp V → Bool) :
    (([c].filter p).filter q).length = if p c = true ∧ q c = true then 1 else 0 := by
  cases hp : p c <;> cases hq : q c <;> simp [hp, hq]

/-- The number of blocks plus the number of dotted components that are not loops is at least the
number of atoms. -/
private theorem SubstSPD_length_le (as : List V) (hnd : as.Nodup) (cs : List (Comp V)) :
    as.length ≤ (dotBlocks as cs).length +
      ((cs.filter fun c => decide (c.kind = .dot)).filter fun c => decide (c.x ≠ c.y)).length := by
  induction cs using List.reverseRecOn with
  | nil => simp [dotBlocks]
  | append_singleton cs c ih =>
    have hP : (dotBlocks as cs).flatten.Nodup := (SubstSPD_blocks_perm as cs).nodup_iff.2 hnd
    rw [SubstSPD_blocks_snoc, List.filter_append, List.filter_append, List.length_append,
      SubstSPD_filter_single]
    generalize ((cs.filter fun c => decide (c.kind = .dot)).filter
      fun c => decide (c.x ≠ c.y)).length = F at ih ⊢
    by_cases hk : c.kind = .dot
    · have hj := SubstSPD_join_length hP c.x c.y
      by_cases hxy : c.x = c.y
      · simp only [hk, hxy, ite_true, decide_true, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, and_false, ite_false] at hj ⊢
        omega
      · simp only [hk, hxy, ite_true, ite_false, decide_true, ne_eq, not_false_eq_true,
          and_self] at hj ⊢
        omega
    · simp only [hk, ite_false, decide_false, Bool.false_eq_true, false_and]
      omega

end DotLoop

private theorem SubstSPD_allAtoms_nodup {k n : ℕ} : (allAtoms k n).Nodup := by
  unfold allAtoms
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).map Sum.inl_injective,
    (List.nodup_finRange n).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  simp at hab

/-- A dotted loop gives a positive dot excess. -/
private theorem SubstSPD_dotExcess_pos {k n : ℕ} (Γ : Graph k n) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hxy : c.x = c.y) : 0 < Γ.dotExcess := by
  have hle := SubstSPD_length_le (allAtoms k n) SubstSPD_allAtoms_nodup Γ.comps
  have hlen : (allAtoms k n).length = k + n := by simp [allAtoms]
  set D := Γ.comps.filter fun c => decide (c.kind = .dot)
  have hsplit := List.length_eq_length_filter_add (l := D) (fun c => decide (c.x ≠ c.y))
  have hloop : 0 < (D.filter fun c => !decide (c.x ≠ c.y)).length :=
    List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_filter.2 ⟨hc, by simpa using hk⟩,
      by simp [hxy]⟩)
  rw [Graph.dotExcess, Graph.nDots, ← Graph.dotBlocks_length_eq_card]
  change 0 < (D.length : ℤ) - ((k + n : ℕ) : ℤ) + _
  omega

/-! ## Two entries of a list with a property -/

/-- Two entries of a list at distinct positions with the property `p` give at least two entries
of the filtered list. -/
private theorem SubstSPD_two_le_filter {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≠ j →
      p l[i] = true → p l[j] = true → 2 ≤ (l.filter p).length
  | [], _, _, hi, _, _, _, _ => absurd hi (by simp)
  | a :: l, i, j, hi, hj, hij, hpi, hpj => by
    rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hij
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpi hpj
      have : 1 ≤ (l.filter p).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨List.getElem_mem _, hpj⟩)
      rw [List.filter_cons_of_pos hpi, List.length_cons]
      omega
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpi hpj
      have : 1 ≤ (l.filter p).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨List.getElem_mem _, hpi⟩)
      rw [List.filter_cons_of_pos hpj, List.length_cons]
      omega
    · have := SubstSPD_two_le_filter p l i j (by simpa using hi) (by simpa using hj)
        (fun h => hij (by rw [h])) hpi hpj
      rw [List.filter_cons]
      split_ifs <;> (try simp only [List.length_cons]) <;> omega


/-! ## The edges of the molecular graph of the block reading -/

section ToMG

variable {k n : ℕ} (Γ : Graph k n)

private theorem SubstSPD_anchor_none {a : Fin k} :
    Γ.anchor (.inl a) = none ↔ Γ.Unpinned (.inl a) := by
  rw [Graph.anchor, List.find?_eq_none]
  constructor
  · intro h
    exact ⟨rfl, fun b hb => by simpa [hb] using h b (List.mem_finRange b)⟩
  · intro h b _
    simpa using h.2 b

/-- The atom of the block normal form is internal, or the atom is an external atom not identified
with an internal atom. -/
private theorem SubstSPD_flat_cases (u : Atom k n) :
    (Γ.flatAtom u).isRight = true ∨
      ∃ a, u = .inl a ∧ Γ.Unpinned (.inl a) ∧ Γ.flatAtom u = .inl a := by
  rcases u with a | b
  · rcases h : Γ.anchor (.inl a) with _ | b
    · exact Or.inr ⟨a, rfl, (SubstSPD_anchor_none Γ).1 h, by simp [Graph.flatAtom, h]⟩
    · exact Or.inl (by simp [Graph.flatAtom, h])
  · exact Or.inl rfl

private theorem SubstSPD_flat_unpinned {a : Fin k} (h : Γ.Unpinned (.inl a)) :
    Γ.flatAtom (.inl a) = .inl a := by
  have h' := (SubstSPD_anchor_none Γ).2 h
  simp [Graph.flatAtom, h']

private theorem SubstSPD_flat_pinned {u : Atom k n} (h : ¬ Γ.Unpinned u) :
    (Γ.flatAtom u).isRight = true := by
  rcases SubstSPD_flat_cases Γ u with h' | ⟨a, rfl, hu, -⟩
  · exact h'
  · exact absurd hu h

private theorem SubstSPD_molRep_mem (b : Fin n) : Γ.molRep (.inr b) ∈ Γ.toMG'.int :=
  Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩

private theorem SubstSPD_mem_int_of_isRight {u : Atom k n} (h : u.isRight = true) :
    Γ.molRep u ∈ Γ.toMG'.int := by
  rcases u with a | b
  · simp at h
  · exact SubstSPD_molRep_mem Γ b

private theorem SubstSPD_isRight_of_mem_int {u : Atom k n} (h : u ∈ Γ.toMG'.int) :
    u.isRight = true := by
  simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and] at h
  obtain ⟨b, rfl⟩ := h
  rfl

private theorem SubstSPD_inl_mem_ext (a : Fin k) : (.inl a : Atom k n) ∈ Γ.toMG'.ext :=
  Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩

private theorem SubstSPD_inl_not_int (a : Fin k) : (.inl a : Atom k n) ∉ Γ.toMG'.int :=
  fun h => by simpa using SubstSPD_isRight_of_mem_int Γ h

/-- The end of a component in the molecular graph: an internal vertex, or an external atom not
identified with an internal atom. -/
private theorem SubstSPD_end_cases (u : Atom k n) :
    Γ.molRep (Γ.flatAtom u) ∈ Γ.toMG'.int ∨
      ∃ a, u = .inl a ∧ Γ.Unpinned (.inl a) ∧ Γ.molRep (Γ.flatAtom u) = .inl a := by
  rcases SubstSPD_flat_cases Γ u with h | ⟨a, rfl, hu, hf⟩
  · exact Or.inl (SubstSPD_mem_int_of_isRight Γ h)
  · exact Or.inr ⟨a, rfl, hu, by rw [hf]; rfl⟩

private theorem SubstSPD_flatComp_x {c : Comp (Atom k n)} (h : c.kind ≠ .dot) :
    (Γ.flatComp c).x = Γ.flatAtom c.x := by
  simp [Graph.flatComp, h]

private theorem SubstSPD_flatComp_y {c : Comp (Atom k n)} (h : c.kind ≠ .dot) :
    (Γ.flatComp c).y = Γ.flatAtom c.y := by
  simp [Graph.flatComp, h]

private theorem SubstSPD_ends_inl (i : Fin Γ.comps.length) (h : Γ.comps[i].kind ≠ .dot) :
    Γ.toMG'.ends (.inl i) =
      (Γ.molRep (Γ.flatAtom Γ.comps[i].x), Γ.molRep (Γ.flatAtom Γ.comps[i].y)) := by
  change (Γ.molRep (Γ.flatComp Γ.comps[i]).x, Γ.molRep (Γ.flatComp Γ.comps[i]).y) = _
  rw [SubstSPD_flatComp_x Γ h, SubstSPD_flatComp_y Γ h]

private theorem SubstSPD_cls_inl (i : Fin Γ.comps.length) (h : Γ.comps[i].kind ≠ .dot) :
    Γ.toMG'.cls (.inl i) =
      if Γ.molRep (Γ.flatAtom Γ.comps[i].x) = Γ.molRep (Γ.flatAtom Γ.comps[i].y) then none
      else Γ.comps[i].kind.mclass := by
  change (if (Γ.flatComp Γ.comps[i]).kind = .dot ∨
      Γ.molRep (Γ.flatComp Γ.comps[i]).x = Γ.molRep (Γ.flatComp Γ.comps[i]).y then none
      else (Γ.flatComp Γ.comps[i]).kind.mclass) = _
  rw [SubstSPD_flatComp_x Γ h, SubstSPD_flatComp_y Γ h, Graph.flatComp_kind]
  exact if_congr (or_iff_right h) rfl rfl

private theorem SubstSPD_cls_dot (i : Fin Γ.comps.length) (h : Γ.comps[i].kind = .dot) :
    Γ.toMG'.cls (.inl i) = none := by
  change (if (Γ.flatComp Γ.comps[i]).kind = .dot ∨
      Γ.molRep (Γ.flatComp Γ.comps[i]).x = Γ.molRep (Γ.flatComp Γ.comps[i]).y then none
      else (Γ.flatComp Γ.comps[i]).kind.mclass) = _
  rw [Graph.flatComp_kind]
  exact ite_eq_left (Or.inl h)

private theorem SubstSPD_pin_unpinned {a : Fin k} (h : Γ.Unpinned (.inl a)) :
    Γ.toMG'.cls (.inr a) = none := by
  have h' := (SubstSPD_anchor_none Γ).2 h
  change (match Γ.anchor (.inl a) with
    | some _ => some (pinClass a)
    | none => none) = none
  rw [h']

private theorem SubstSPD_pin_pinned {a : Fin k} (h : ¬ Γ.Unpinned (.inl a)) :
    ∃ b, Γ.toMG'.cls (.inr a) = some (pinClass a) ∧
      Γ.toMG'.ends (.inr a) = (Γ.molRep (.inr b), .inl a) := by
  rcases h' : Γ.anchor (.inl a) with _ | b
  · exact absurd ((SubstSPD_anchor_none Γ).1 h') h
  · refine ⟨b, ?_, ?_⟩
    · change (match Γ.anchor (.inl a) with
        | some _ => some (pinClass a)
        | none => none) = _
      rw [h']
    · change (match Γ.anchor (.inl a) with
        | some b => (Γ.molRep (.inr b), (.inl a : Atom k n))
        | none => ((.inl a : Atom k n), (.inl a : Atom k n))) = _
      rw [h']

/-- Every edge of the molecular graph joins two vertices. -/
private theorem SubstSPD_vtx (e : Fin Γ.comps.length ⊕ Fin k) :
    Γ.toMG'.IsVtx (Γ.toMG'.ends e).1 ∧ Γ.toMG'.IsVtx (Γ.toMG'.ends e).2 :=
  MolInsert_toMG'_ends_vtx k n Γ e

end ToMG


/-! ## The three edges of a substituted graph at its external atoms -/

section AtVertex

variable {V E : Type}

/-- The edge `f` of `L` joins the external vertex `w` to an internal vertex, its class satisfies
`P`, and every present edge with an end `w` is `f`. -/
private def SubstSPD_AtV (L : MGraph V E) (w : V) (f : E) (P : Option MClass → Prop) : Prop :=
  (∃ x ∈ L.int, L.ends f = (w, x) ∨ L.ends f = (x, w)) ∧ P (L.cls f) ∧
    ∀ f', L.cls f' ≠ none → ((L.ends f').1 = w ∨ (L.ends f').2 = w) → f' = f

private theorem SubstSPD_AtV_ne {L : MGraph V E} {w w' : V} {f f' : E}
    {P P' : Option MClass → Prop} (hd : Disjoint L.int L.ext) (hw : w ∈ L.ext) (hw' : w' ∈ L.ext)
    (hne : w ≠ w') (h : SubstSPD_AtV L w f P) (h' : SubstSPD_AtV L w' f' P') : f ≠ f' := by
  rintro rfl
  obtain ⟨x, hx, hx'⟩ := h.1
  obtain ⟨y, hy, hy'⟩ := h'.1
  have hxw : x ≠ w' := fun e => Finset.disjoint_left.1 hd hx (e ▸ hw')
  have hyw : y ≠ w := fun e => Finset.disjoint_left.1 hd hy (e ▸ hw)
  rcases hx' with e1 | e1 <;> rcases hy' with e2 | e2 <;> rw [e1] at e2 <;>
    simp only [Prod.mk.injEq] at e2 <;> tauto

/-- From the three edges at the external vertices `w₀`, `w₁`, `w₂`: every other present edge
joins two internal vertices. -/
private theorem SubstSPD_AtV_oth {L : MGraph V E} {w₀ w₁ w₂ : V} {f₀ f₁ f₂ : E}
    {P₀ P₁ P₂ : Option MClass → Prop} (hext : ∀ v ∈ L.ext, v = w₀ ∨ v = w₁ ∨ v = w₂)
    (hvtx : ∀ f, L.IsVtx (L.ends f).1 ∧ L.IsVtx (L.ends f).2)
    (h₀ : SubstSPD_AtV L w₀ f₀ P₀) (h₁ : SubstSPD_AtV L w₁ f₁ P₁)
    (h₂ : SubstSPD_AtV L w₂ f₂ P₂) :
    ∀ f, f ≠ f₀ → f ≠ f₁ → f ≠ f₂ → L.cls f ≠ none →
      (L.ends f).1 ∈ L.int ∧ (L.ends f).2 ∈ L.int := by
  intro f n₀ n₁ n₂ hf
  have key : ∀ v, L.IsVtx v → (v = (L.ends f).1 ∨ v = (L.ends f).2) → v ∈ L.int := by
    intro v hv hve
    rcases hv with hv | hv
    · exact hv
    · exfalso
      have hend : ∀ w, v = w → (L.ends f).1 = w ∨ (L.ends f).2 = w := by
        rintro w rfl
        rcases hve with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      rcases hext v hv with rfl | rfl | rfl
      · exact n₀ (h₀.2.2 f hf (hend _ rfl))
      · exact n₁ (h₁.2.2 f hf (hend _ rfl))
      · exact n₂ (h₂.2.2 f hf (hend _ rfl))
  exact ⟨key _ (hvtx f).1 (Or.inl rfl), key _ (hvtx f).2 (Or.inr rfl)⟩

end AtVertex

section LFacts

variable {n : ℕ} (Γ : Graph 3 n)

/-- Without dotted edges at `⊗`, the atom `⊗` is not identified with an internal atom. -/
private theorem SubstSPD_unpinned_zero (hT : Γ.TensorDiffusive) : Γ.Unpinned (.inl 0) := by
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

private theorem SubstSPD_mclass_diff {κ : Kind} (h : κ.isDiffusive = true) :
    κ.mclass = some .diff := by
  cases κ with
  | aux j r b => cases b <;> simp_all [Kind.isDiffusive, Kind.mclass]
  | _ => simp_all [Kind.isDiffusive, Kind.mclass]

/-- The edge of a component from an unpinned external atom `a` to an atom whose block normal form
is internal. -/
private theorem SubstSPD_comp_edge {a : Fin 3} (ha : Γ.Unpinned (.inl a))
    (i : Fin Γ.comps.length) (hk : Γ.comps[i].kind ≠ .dot)
    (he : (Γ.comps[i].x = .inl a ∧ (Γ.flatAtom Γ.comps[i].y).isRight = true) ∨
      (Γ.comps[i].y = .inl a ∧ (Γ.flatAtom Γ.comps[i].x).isRight = true)) :
    (∃ x ∈ Γ.toMG'.int, Γ.toMG'.ends (.inl i) = (.inl a, x) ∨
      Γ.toMG'.ends (.inl i) = (x, .inl a)) ∧
      Γ.toMG'.cls (.inl i) = Γ.comps[i].kind.mclass := by
  rw [SubstSPD_ends_inl Γ i hk, SubstSPD_cls_inl Γ i hk]
  rcases he with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · have hm := SubstSPD_mem_int_of_isRight Γ hy
    have hfa : Γ.molRep (Γ.flatAtom Γ.comps[i].x) = .inl a := by
      rw [hx, SubstSPD_flat_unpinned Γ ha]; rfl
    refine ⟨⟨_, hm, Or.inl (by rw [hfa])⟩, ?_⟩
    rw [hfa]
    exact ite_eq_right fun (h : (Sum.inl a : Atom 3 n) = _) =>
      SubstSPD_inl_not_int Γ a (h ▸ hm)
  · have hm := SubstSPD_mem_int_of_isRight Γ hx
    have hfa : Γ.molRep (Γ.flatAtom Γ.comps[i].y) = .inl a := by
      rw [hy, SubstSPD_flat_unpinned Γ ha]; rfl
    refine ⟨⟨_, hm, Or.inr (by rw [hfa])⟩, ?_⟩
    rw [hfa]
    exact ite_eq_right fun (h : _ = (Sum.inl a : Atom 3 n)) =>
      SubstSPD_inl_not_int Γ a (h ▸ hm)

/-- A present edge of the molecular graph at an unpinned external atom `a` is the edge of a
component at `a`, other than a dotted edge, of a kind with a class. -/
private theorem SubstSPD_at_unpinned {a : Fin 3} (ha : Γ.Unpinned (.inl a))
    (f : Fin Γ.comps.length ⊕ Fin 3) (hf : Γ.toMG'.cls f ≠ none)
    (hfa : (Γ.toMG'.ends f).1 = .inl a ∨ (Γ.toMG'.ends f).2 = .inl a) :
    ∃ i : Fin Γ.comps.length, f = .inl i ∧ Γ.comps[i].kind ≠ .dot ∧
      (Γ.comps[i].x = .inl a ∨ Γ.comps[i].y = .inl a) ∧ Γ.comps[i].kind.mclass ≠ none := by
  rcases f with i | a'
  · have hk : Γ.comps[i].kind ≠ .dot := fun h => hf (SubstSPD_cls_dot Γ i h)
    refine ⟨i, rfl, hk, ?_, ?_⟩
    · rw [SubstSPD_ends_inl Γ i hk] at hfa
      have key : ∀ u, Γ.molRep (Γ.flatAtom u) = .inl a → u = .inl a := by
        intro u hu
        rcases SubstSPD_end_cases Γ u with h | ⟨a', rfl, -, h⟩
        · exact absurd (hu ▸ h) (SubstSPD_inl_not_int Γ a)
        · rw [h] at hu
          rw [hu]
      rcases hfa with h | h
      · exact Or.inl (key _ h)
      · exact Or.inr (key _ h)
    · rw [SubstSPD_cls_inl Γ i hk] at hf
      intro h
      apply hf
      split_ifs
      · rfl
      · exact h
  · exfalso
    by_cases hp : Γ.Unpinned (.inl a')
    · exact hf (SubstSPD_pin_unpinned Γ hp)
    · obtain ⟨b, -, he⟩ := SubstSPD_pin_pinned Γ hp
      rw [he] at hfa
      rcases hfa with h | h
      · simp [Graph.molRep] at h
      · simp only [Sum.inl.injEq] at h
        subst h
        exact hp ha

/-- At a pinned external atom `a`, the only present edge is the edge `.inr a` from the molecule of
its block. -/
private theorem SubstSPD_AtV_pinned {a : Fin 3} (ha : ¬ Γ.Unpinned (.inl a)) :
    SubstSPD_AtV Γ.toMG' (.inl a) (.inr a) (fun c => c = some (pinClass a)) := by
  obtain ⟨b, hc, he⟩ := SubstSPD_pin_pinned Γ ha
  refine ⟨⟨_, SubstSPD_molRep_mem Γ b, Or.inr he⟩, hc, fun f hf hfa => ?_⟩
  rcases f with i | a'
  · exfalso
    have hk : Γ.comps[i].kind ≠ .dot := fun h => hf (SubstSPD_cls_dot Γ i h)
    rw [SubstSPD_ends_inl Γ i hk] at hfa
    have key : ∀ u, Γ.molRep (Γ.flatAtom u) ≠ .inl a := by
      intro u hu
      rcases SubstSPD_end_cases Γ u with h | ⟨a', rfl, hu', h⟩
      · exact SubstSPD_inl_not_int Γ a (hu ▸ h)
      · rw [h] at hu
        simp only [Sum.inl.injEq] at hu
        subst hu
        exact ha hu'
    rcases hfa with h | h
    · exact key _ h
    · exact key _ h
  · by_cases hp : Γ.Unpinned (.inl a')
    · exact absurd (SubstSPD_pin_unpinned Γ hp) hf
    · obtain ⟨b', -, he'⟩ := SubstSPD_pin_pinned Γ hp
      rw [he'] at hfa
      rcases hfa with h | h
      · simp [Graph.molRep] at h
      · simp only [Sum.inl.injEq] at h
        rw [h]


/-- An entry of a list as an entry at a position. -/
private theorem SubstSPD_idx {α : Type*} {l : List α} {c : α} (h : c ∈ l) :
    ∃ i : Fin l.length, l[i] = c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨⟨i, hi⟩, rfl⟩

/-- Two components at positions `i ≠ j` with the property `p` contradict a bound `≤ 1` on the
number of components with `p`. -/
private theorem SubstSPD_eq_of_le_one {α : Type*} {l : List α} (p : α → Bool)
    (hle : (l.filter p).length ≤ 1) (i j : Fin l.length) (hi : p l[i] = true)
    (hj : p l[j] = true) : i = j := by
  by_contra hne
  have := SubstSPD_two_le_filter p l i j i.2 j.2 (fun h => hne (Fin.ext h)) hi hj
  omega


/-- The edge at `⊗`: the single diffusive edge at `⊗`, to an internal or identified atom. -/
private theorem SubstSPD_AtV_zero (hE : Γ.ExtClause) (hT : Γ.TensorDiffusive)
    (hA : Γ.AtExternals) : ∃ f, SubstSPD_AtV Γ.toMG' (.inl 0) f (fun c => c = some .diff) := by
  have hU := SubstSPD_unpinned_zero Γ hT
  obtain ⟨-, hDP⟩ := hE.2.2.1 hU
  set p0 : Comp (Atom 3 n) → Bool :=
    fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0) with hp0
  have hlen : (Γ.comps.filter p0).length = 1 := hA.1
  obtain ⟨c, hc⟩ := List.length_pos_iff_exists_mem.1 (by omega : 0 < (Γ.comps.filter p0).length)
  obtain ⟨hcm, hcp⟩ := List.mem_filter.1 hc
  obtain ⟨i₀, rfl⟩ := SubstSPD_idx hcm
  have hdif : Γ.comps[i₀].kind.isDiffusive = true := by
    simp only [hp0, Bool.and_eq_true] at hcp
    exact hcp.1
  have hk : Γ.comps[i₀].kind ≠ .dot := by
    intro h
    rw [h] at hdif
    exact absurd hdif (by decide)
  have he : (Γ.comps[i₀].x = .inl 0 ∧ (Γ.flatAtom Γ.comps[i₀].y).isRight = true) ∨
      (Γ.comps[i₀].y = .inl 0 ∧ (Γ.flatAtom Γ.comps[i₀].x).isRight = true) := by
    have hat : Γ.comps[i₀].x = .inl 0 ∨ Γ.comps[i₀].y = .inl 0 := by
      simp only [hp0, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcp
      exact hcp.2
    obtain ⟨h1, h2⟩ := hDP _ hcm hdif
    rcases hat with h | h
    · exact Or.inl ⟨h, SubstSPD_flat_pinned Γ (h1 h)⟩
    · exact Or.inr ⟨h, SubstSPD_flat_pinned Γ (h2 h)⟩
  obtain ⟨hends, hcls⟩ := SubstSPD_comp_edge Γ hU i₀ hk he
  refine ⟨.inl i₀, hends, by rw [hcls]; exact SubstSPD_mclass_diff hdif, fun f hf hfa => ?_⟩
  obtain ⟨j, rfl, -, hj, -⟩ := SubstSPD_at_unpinned Γ hU f hf hfa
  have hpj : p0 Γ.comps[j] = true := by
    have hTD := List.all_eq_true.1 hT _ (List.getElem_mem (l := Γ.comps) j.2)
    have hj' : (Γ.comps[j].x == .inl 0 || Γ.comps[j].y == .inl 0) = true := by
      simpa using hj
    simp only [Fin.getElem_fin] at hj' hTD ⊢
    rw [hj'] at hTD
    simp only [Bool.not_true, Bool.false_or] at hTD
    simp only [hp0, hTD, hj', Bool.and_self]
  rw [SubstSPD_eq_of_le_one p0 (by omega) j i₀ hpj hcp]

/-- The edge at an unpinned `⊕`: the single component at `⊕` other than dotted and `×`-dotted
edges, a blue solid or a diffusive edge to an internal or identified atom. -/
private theorem SubstSPD_AtV_one (hE : Γ.ExtClause)
    (hCI : ∀ c ∈ Γ.comps, c.kind.isSolid = true →
      (Γ.flatAtom c.x).isRight = true ∨ (Γ.flatAtom c.y).isRight = true) :
    ∃ f, SubstSPD_AtV Γ.toMG' (.inl 1) f (fun c => c = some .plus ∨ c = some .diff) := by
  by_cases hU : Γ.Unpinned (.inl 1)
  swap
  · exact ⟨_, SubstSPD_AtV_pinned Γ hU |>.imp_right (And.imp_left (fun h => Or.inl h))⟩
  obtain ⟨hex, hDP, hdeg⟩ := hE.2.2.2.2 hU
  set p1 : Comp (Atom 3 n) → Bool := fun c => decide ((c.x = .inl 1 ∨ c.y = .inl 1) ∧
    c.kind ≠ .dot ∧ c.kind ≠ .xdot) with hp1
  have hdeg' : (Γ.comps.filter p1).length ≤ 1 := hdeg
  -- the component at `⊕`
  obtain ⟨i₁, hat, hk, hkx, he, hm⟩ : ∃ i₁ : Fin Γ.comps.length,
      (Γ.comps[i₁].x = .inl 1 ∨ Γ.comps[i₁].y = .inl 1) ∧ Γ.comps[i₁].kind ≠ .dot ∧
      Γ.comps[i₁].kind ≠ .xdot ∧
      ((Γ.comps[i₁].x = .inl 1 ∧ (Γ.flatAtom Γ.comps[i₁].y).isRight = true) ∨
        (Γ.comps[i₁].y = .inl 1 ∧ (Γ.flatAtom Γ.comps[i₁].x).isRight = true)) ∧
      (Γ.comps[i₁].kind.mclass = some .plus ∨ Γ.comps[i₁].kind.mclass = some .diff) := by
    have hfl : Γ.flatAtom (.inl 1) = .inl 1 := SubstSPD_flat_unpinned Γ hU
    rcases hex with ⟨c, hc, hkc, hat⟩ | ⟨c, hc, hdif, hat⟩
    · obtain ⟨i, rfl⟩ := SubstSPD_idx hc
      refine ⟨i, hat, by rw [hkc]; decide, by rw [hkc]; decide, ?_, Or.inl (by rw [hkc]; rfl)⟩
      have hci := hCI _ hc (by rw [hkc]; rfl)
      rcases hat with h | h
      · refine Or.inl ⟨h, hci.resolve_left ?_⟩
        rw [h, hfl]; simp
      · refine Or.inr ⟨h, hci.resolve_right ?_⟩
        rw [h, hfl]; simp
    · obtain ⟨i, rfl⟩ := SubstSPD_idx hc
      have hk : Γ.comps[i].kind ≠ .dot := fun h => by rw [h] at hdif; exact absurd hdif (by decide)
      have hkx : Γ.comps[i].kind ≠ .xdot := fun h => by
        rw [h] at hdif; exact absurd hdif (by decide)
      refine ⟨i, ?_, hk, hkx, ?_, Or.inr (SubstSPD_mclass_diff hdif)⟩
      · rcases hat with ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h
      · rcases hat with ⟨h, h'⟩ | ⟨h, h'⟩
        · exact Or.inl ⟨h, SubstSPD_flat_pinned Γ h'⟩
        · exact Or.inr ⟨h, SubstSPD_flat_pinned Γ h'⟩
  obtain ⟨hends, hcls⟩ := SubstSPD_comp_edge Γ hU i₁ hk he
  have hp1i : p1 Γ.comps[i₁] = true := by
    simp only [hp1, decide_eq_true_eq]; exact ⟨hat, hk, hkx⟩
  refine ⟨.inl i₁, hends, by rw [hcls]; exact hm, fun f hf hfa => ?_⟩
  obtain ⟨j, rfl, hjk, hj, hjm⟩ := SubstSPD_at_unpinned Γ hU f hf hfa
  have hjx : Γ.comps[j].kind ≠ .xdot := fun h => hjm (by rw [h]; rfl)
  have hpj : p1 Γ.comps[j] = true := by
    simp only [hp1, decide_eq_true_eq]; exact ⟨hj, hjk, hjx⟩
  rw [SubstSPD_eq_of_le_one p1 hdeg' j i₁ hpj hp1i]

/-- The edge at an unpinned `⊖`: the single red solid edge at `⊖`, from an internal or identified
atom. A dotted edge at `⊖` is excluded: to another atom it identifies `⊖` with an internal atom,
and a dotted loop gives a positive dot excess. -/
private theorem SubstSPD_AtV_two (hE : Γ.ExtClause) (hA : Γ.AtExternals)
    (hX : Γ.dotExcess = 0)
    (hCI : ∀ c ∈ Γ.comps, c.kind.isSolid = true →
      (Γ.flatAtom c.x).isRight = true ∨ (Γ.flatAtom c.y).isRight = true) :
    ∃ f, SubstSPD_AtV Γ.toMG' (.inl 2) f (fun c => c = some .minus) := by
  by_cases hU : Γ.Unpinned (.inl 2)
  swap
  · exact ⟨_, SubstSPD_AtV_pinned Γ hU⟩
  obtain ⟨hnd, hdeg⟩ := hE.2.2.2.1 hU
  set p2 : Comp (Atom 3 n) → Bool := fun c => decide ((c.x = .inl 2 ∨ c.y = .inl 2) ∧
    c.kind ≠ .dot ∧ c.kind ≠ .xdot) with hp2
  have hdeg' : (Γ.comps.filter p2).length ≤ 1 := hdeg
  have hfl : Γ.flatAtom (.inl 2) = .inl 2 := SubstSPD_flat_unpinned Γ hU
  obtain ⟨c, hc, hcp⟩ := List.any_eq_true.1 hA.2.2
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcp
  obtain ⟨hkind, hat⟩ := hcp
  have hkc : c.kind = .G .minus := by
    rcases hkind with (h | h) | h
    · exact h
    · exact absurd hat (by have := hnd c hc h; tauto)
    · exfalso
      by_cases hxy : c.x = c.y
      · have := SubstSPD_dotExcess_pos Γ hc h hxy
        omega
      · have hsb : Γ.SameBlock c.x c.y := by
          refine SimpleGraph.Adj.reachable ?_
          rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
          exact ⟨hxy, Or.inl ⟨c, hc, h, rfl, rfl⟩⟩
        obtain ⟨b, hb⟩ := hE.1 _ _ hxy hsb
        rcases hat with h2 | h2
        · rw [h2] at hb
          exact hU.2 b hb
        · rw [h2] at hsb
          exact hU.2 b (hsb.symm.trans hb)
  obtain ⟨i₂, rfl⟩ := SubstSPD_idx hc
  have hk : Γ.comps[i₂].kind ≠ .dot := by rw [hkc]; decide
  have hkx : Γ.comps[i₂].kind ≠ .xdot := by rw [hkc]; decide
  have he : (Γ.comps[i₂].x = .inl 2 ∧ (Γ.flatAtom Γ.comps[i₂].y).isRight = true) ∨
      (Γ.comps[i₂].y = .inl 2 ∧ (Γ.flatAtom Γ.comps[i₂].x).isRight = true) := by
    have hci := hCI _ hc (by rw [hkc]; rfl)
    rcases hat with h | h
    · refine Or.inl ⟨h, hci.resolve_left ?_⟩
      rw [h, hfl]; simp
    · refine Or.inr ⟨h, hci.resolve_right ?_⟩
      rw [h, hfl]; simp
  obtain ⟨hends, hcls⟩ := SubstSPD_comp_edge Γ hU i₂ hk he
  have hp2i : p2 Γ.comps[i₂] = true := by
    simp only [hp2, decide_eq_true_eq]; exact ⟨hat, hk, hkx⟩
  refine ⟨.inl i₂, hends, by rw [hcls, hkc]; rfl, fun f hf hfa => ?_⟩
  obtain ⟨j, rfl, hjk, hj, hjm⟩ := SubstSPD_at_unpinned Γ hU f hf hfa
  have hjx : Γ.comps[j].kind ≠ .xdot := fun h => hjm (by rw [h]; rfl)
  have hpj : p2 Γ.comps[j] = true := by
    simp only [hp2, decide_eq_true_eq]; exact ⟨hj, hjk, hjx⟩
  rw [SubstSPD_eq_of_le_one p2 hdeg' j i₂ hpj hp2i]


/-- **The three edges at the external atoms** of the molecular graph of `Γ`: under the clause on
the external atoms, only diffusive edges at `⊗`, [II, Def 3.2 (9)], dot excess `0` and an end in
the block normal form internal for every solid edge, the molecular graph of `Γ` has hypothesis
(L2) of `MGraph.spd_insert` at the external atoms `⊗`, `⊕`, `⊖`. -/
private theorem SubstSPD_L2 {V : Type} (σ : Atom 3 n → V) (u₀ u₁ u₂ : V)
    (h0 : σ (.inl 0) = u₀) (h1 : σ (.inl 1) = u₁) (h2 : σ (.inl 2) = u₂)
    (hE : Γ.ExtClause) (hT : Γ.TensorDiffusive) (hA : Γ.AtExternals) (hX : Γ.dotExcess = 0)
    (hCI : ∀ c ∈ Γ.comps, c.kind.isSolid = true →
      (Γ.flatAtom c.x).isRight = true ∨ (Γ.flatAtom c.y).isRight = true) :
    ∃ (f₀ f₁ f₂ : Fin Γ.comps.length ⊕ Fin 3) (w₀ w₁ w₂ : Atom 3 n), f₀ ≠ f₁ ∧ f₀ ≠ f₂ ∧
      f₁ ≠ f₂ ∧ w₀ ∈ Γ.toMG'.ext ∧ w₁ ∈ Γ.toMG'.ext ∧ w₂ ∈ Γ.toMG'.ext ∧ w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧
      w₁ ≠ w₂ ∧ σ w₀ = u₀ ∧ σ w₁ = u₁ ∧ σ w₂ = u₂ ∧
      (∃ x ∈ Γ.toMG'.int, Γ.toMG'.ends f₀ = (w₀, x) ∨ Γ.toMG'.ends f₀ = (x, w₀)) ∧
      (∃ x ∈ Γ.toMG'.int, Γ.toMG'.ends f₁ = (w₁, x) ∨ Γ.toMG'.ends f₁ = (x, w₁)) ∧
      (∃ x ∈ Γ.toMG'.int, Γ.toMG'.ends f₂ = (w₂, x) ∨ Γ.toMG'.ends f₂ = (x, w₂)) ∧
      Γ.toMG'.cls f₀ = some .diff ∧
      (Γ.toMG'.cls f₁ = some .plus ∨ Γ.toMG'.cls f₁ = some .diff) ∧
      Γ.toMG'.cls f₂ = some .minus ∧
      ∀ f, f ≠ f₀ → f ≠ f₁ → f ≠ f₂ → Γ.toMG'.cls f ≠ none →
        (Γ.toMG'.ends f).1 ∈ Γ.toMG'.int ∧ (Γ.toMG'.ends f).2 ∈ Γ.toMG'.int := by
  obtain ⟨f₀, A0⟩ := SubstSPD_AtV_zero Γ hE hT hA
  obtain ⟨f₁, A1⟩ := SubstSPD_AtV_one Γ hE hCI
  obtain ⟨f₂, A2⟩ := SubstSPD_AtV_two Γ hE hA hX hCI
  have hd := Graph.toMG'_disjoint Γ
  have e0 := SubstSPD_inl_mem_ext Γ 0
  have e1 := SubstSPD_inl_mem_ext Γ 1
  have e2 := SubstSPD_inl_mem_ext Γ 2
  have n01 : (.inl 0 : Atom 3 n) ≠ .inl 1 := by simp
  have n02 : (.inl 0 : Atom 3 n) ≠ .inl 2 := by simp
  have n12 : (.inl 1 : Atom 3 n) ≠ .inl 2 := by simp
  have hext : ∀ v ∈ Γ.toMG'.ext, v = .inl 0 ∨ v = .inl 1 ∨ v = .inl 2 := by
    intro v hv
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨a, rfl⟩ := hv
    fin_cases a <;> simp
  refine ⟨f₀, f₁, f₂, .inl 0, .inl 1, .inl 2, SubstSPD_AtV_ne hd e0 e1 n01 A0 A1,
    SubstSPD_AtV_ne hd e0 e2 n02 A0 A2, SubstSPD_AtV_ne hd e1 e2 n12 A1 A2, e0, e1, e2, n01, n02,
    n12, h0, h1, h2, A0.1, A1.1, A2.1, A0.2.1, A1.2.1, A2.2.1,
    SubstSPD_AtV_oth hext (SubstSPD_vtx Γ) A0 A1 A2⟩

end LFacts

/-! ## Reversing the solid edges -/

section Swap

variable {k n : ℕ} (g : Graph k n)

private theorem SubstSPD_swap_kind (c : Comp (Atom k n)) : c.swapSolid.kind = c.kind := by
  unfold Comp.swapSolid; split <;> rfl

private theorem SubstSPD_swap_of_ns {c : Comp (Atom k n)} (h : c.kind.isSolid = false) :
    c.swapSolid = c := by
  simp [Comp.swapSolid, h]

private theorem SubstSPD_swap_ends (c : Comp (Atom k n)) :
    (c.swapSolid.x = c.x ∧ c.swapSolid.y = c.y) ∨ (c.swapSolid.x = c.y ∧ c.swapSolid.y = c.x) := by
  unfold Comp.swapSolid
  split
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

private theorem SubstSPD_swap_mem {c : Comp (Atom k n)} :
    c ∈ g.swapSolid.comps ↔ ∃ d ∈ g.comps, d.swapSolid = c := List.mem_map

private theorem SubstSPD_swap_dotGraph : g.swapSolid.dotGraph = g.dotGraph := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
  have key : ∀ u v, (∃ c ∈ g.swapSolid.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ↔
      (∃ c ∈ g.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) := by
    intro u v
    constructor
    · rintro ⟨c, hc, hk, hx, hy⟩
      obtain ⟨d, hd, rfl⟩ := (SubstSPD_swap_mem g).1 hc
      rw [SubstSPD_swap_kind] at hk
      rw [SubstSPD_swap_of_ns (by rw [hk]; rfl)] at hx hy
      exact ⟨d, hd, hk, hx, hy⟩
    · rintro ⟨d, hd, hk, hx, hy⟩
      refine ⟨d.swapSolid, (SubstSPD_swap_mem g).2 ⟨d, hd, rfl⟩, ?_⟩
      rw [SubstSPD_swap_kind, SubstSPD_swap_of_ns (by rw [hk]; rfl)]
      exact ⟨hk, hx, hy⟩
  rw [key u v, key v u]

private theorem SubstSPD_swap_sameBlock (u v : Atom k n) :
    g.swapSolid.SameBlock u v ↔ g.SameBlock u v := by
  simp only [Graph.SameBlock, SubstSPD_swap_dotGraph]

private theorem SubstSPD_swap_unpinned (u : Atom k n) :
    g.swapSolid.Unpinned u ↔ g.Unpinned u := by
  simp only [Graph.Unpinned, SubstSPD_swap_sameBlock]

private theorem SubstSPD_swap_anchor (u : Atom k n) : g.swapSolid.anchor u = g.anchor u := by
  unfold Graph.anchor
  congr 1
  funext b
  exact decide_eq_decide.2 (SubstSPD_swap_sameBlock g _ _)

private theorem SubstSPD_swap_flatAtom (u : Atom k n) :
    g.swapSolid.flatAtom u = g.flatAtom u := by
  unfold Graph.flatAtom
  rw [SubstSPD_swap_anchor]

private theorem SubstSPD_swap_molRep (u : Atom k n) : g.swapSolid.molRep u = g.molRep u := by
  rcases u with a | a
  · rfl
  · simp only [Graph.molRep]
    congr 3
    funext b
    exact decide_eq_decide.2 ((swapSolid_basic k n g).2.2.2.2.1 _ _)

/-- A statement about some component, symmetric in the two ends, holds for the graph with the
solid edges reversed exactly when it holds for the graph. -/
private theorem SubstSPD_swap_exists {P : Comp (Atom k n) → Prop}
    (hP : ∀ c, P c.swapSolid ↔ P c) :
    (∃ c ∈ g.swapSolid.comps, P c) ↔ ∃ c ∈ g.comps, P c := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨d, hd, rfl⟩ := (SubstSPD_swap_mem g).1 hc
    exact ⟨d, hd, (hP d).1 h⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d.swapSolid, (SubstSPD_swap_mem g).2 ⟨d, hd, rfl⟩, (hP d).2 h⟩

private theorem SubstSPD_swap_forall {P : Comp (Atom k n) → Prop}
    (hP : ∀ c, P c.swapSolid ↔ P c) :
    (∀ c ∈ g.swapSolid.comps, P c) ↔ ∀ c ∈ g.comps, P c := by
  constructor
  · intro h d hd
    exact (hP d).1 (h _ ((SubstSPD_swap_mem g).2 ⟨d, hd, rfl⟩))
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := (SubstSPD_swap_mem g).1 hc
    exact (hP d).2 (h d hd)

private theorem SubstSPD_swap_filter {p : Comp (Atom k n) → Bool}
    (hp : ∀ c, p c.swapSolid = p c) :
    (g.swapSolid.comps.filter p).length = (g.comps.filter p).length := by
  simp only [Graph.swapSolid, List.filter_map, List.length_map]
  congr 1
  exact List.filter_congr fun c _ => hp c

end Swap

section SwapThree

/-- A predicate of a component symmetric in its two ends is unchanged by `Comp.swapSolid`. -/
local macro "swapsym" : tactic => `(tactic| (intro c; unfold Comp.swapSolid; split <;>
  first | exact Iff.rfl | (simp only; tauto) | (simp only [Bool.or_comm])))

variable {n : ℕ} (g : Graph 3 n)

private theorem SubstSPD_swap_extClause (h : g.ExtClause) : g.swapSolid.ExtClause := by
  have hu := SubstSPD_swap_unpinned g
  have hsb := SubstSPD_swap_sameBlock g
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hdtp : ∀ u, g.swapSolid.DiffToPinned u ↔ g.DiffToPinned u := by
    intro u
    unfold Graph.DiffToPinned
    simp only [hu]
    exact SubstSPD_swap_forall g (P := fun c => c.kind.isDiffusive = true →
      (c.x = u → ¬ g.Unpinned c.y) ∧ (c.y = u → ¬ g.Unpinned c.x))
      (by swapsym)
  have hhdp : ∀ u, g.swapSolid.HasDiffToPinned u ↔ g.HasDiffToPinned u := by
    intro u
    unfold Graph.HasDiffToPinned
    simp only [hu]
    exact SubstSPD_swap_exists g (P := fun c => c.kind.isDiffusive = true ∧
      (c.x = u ∧ ¬ g.Unpinned c.y ∨ c.y = u ∧ ¬ g.Unpinned c.x))
      (by swapsym)
  have hdeg : ∀ u, g.swapSolid.nonDotDeg u = g.nonDotDeg u := by
    intro u
    unfold Graph.nonDotDeg
    exact SubstSPD_swap_filter g fun c => by
      unfold Comp.swapSolid
      split
      · simp only; congr 1; exact propext (by tauto)
      · rfl
  refine ⟨fun u v huv hb => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb'⟩ := h1 u v huv ((hsb u v).1 hb)
    exact ⟨b, (hsb _ _).2 hb'⟩
  · simp only [hu]
    exact (SubstSPD_swap_forall g (P := fun c => c.kind = .xdot →
      ¬ (g.Unpinned c.x ∧ g.Unpinned c.y)) (by swapsym)).2 h2
  · rw [hu, hhdp, hdtp]
    exact h3
  · rw [hu, hdeg]
    intro hU
    obtain ⟨ha, hb⟩ := h4 hU
    refine ⟨(SubstSPD_swap_forall g (P := fun c => c.kind.isDiffusive = true →
      c.x ≠ .inl 2 ∧ c.y ≠ .inl 2) (by swapsym)).2 ha, hb⟩
  · rw [hu, hhdp, hdtp, hdeg]
    intro hU
    obtain ⟨ha, hb, hc⟩ := h5 hU
    refine ⟨?_, hb, hc⟩
    rcases ha with ha | ha
    · exact Or.inl ((SubstSPD_swap_exists g (P := fun c => c.kind = .G .plus ∧
        (c.x = .inl 1 ∨ c.y = .inl 1)) (by swapsym)).2 ha)
    · exact Or.inr ha

private theorem SubstSPD_swap_tensor (h : g.TensorDiffusive) : g.swapSolid.TensorDiffusive := by
  unfold Graph.TensorDiffusive at h ⊢
  rw [List.all_eq_true] at h ⊢
  refine (SubstSPD_swap_forall g (P := fun c =>
    (!(c.x == .inl 0 || c.y == .inl 0) || c.kind.isDiffusive) = true) ?_).2 h
  swapsym

private theorem SubstSPD_swap_atExt (h : g.AtExternals) : g.swapSolid.AtExternals := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]
    exact SubstSPD_swap_filter g fun c => by
      unfold Comp.swapSolid
      split
      · simp only [Bool.or_comm (c.y == _)]
      · rfl
  · rw [List.any_eq_true] at h2 ⊢
    refine (SubstSPD_swap_exists g (P := fun c =>
      ((c.kind == .G .plus || c.kind.isDiffusive || c.kind == .dot) &&
        (c.x == .inl 1 || c.y == .inl 1)) = true) ?_).2 h2
    swapsym
  · rw [List.any_eq_true] at h3 ⊢
    refine (SubstSPD_swap_exists g (P := fun c =>
      ((c.kind == .G .minus || c.kind.isDiffusive || c.kind == .dot) &&
        (c.x == .inl 2 || c.y == .inl 2)) = true) ?_).2 h3
    swapsym

private theorem SubstSPD_swap_dotExcess : g.swapSolid.dotExcess = g.dotExcess := by
  unfold Graph.dotExcess Graph.nDots
  rw [SubstSPD_swap_dotGraph, SubstSPD_swap_filter g fun c => by rw [SubstSPD_swap_kind]]

/-- The charge pattern of the block normal form gives, after reversing the solid edges, an end
of every solid edge whose atom in the block normal form is internal. -/
private theorem SubstSPD_swap_ci (h : g.ColourInvB) :
    ∀ c ∈ g.swapSolid.comps, c.kind.isSolid = true →
      (g.swapSolid.flatAtom c.x).isRight = true ∨ (g.swapSolid.flatAtom c.y).isRight = true := by
  intro c hc hk
  obtain ⟨d, hd, rfl⟩ := (SubstSPD_swap_mem g).1 hc
  rw [SubstSPD_swap_kind] at hk
  have hd' : d.kind ≠ .dot := fun e => by rw [e] at hk; exact absurd hk (by decide)
  have hci := (h (g.flatComp d) (List.mem_map.2 ⟨d, hd, rfl⟩)).1
    (by rw [Graph.flatComp_kind]; cases hk' : d.kind <;> simp_all [Kind.isSolid, Kind.isRandom])
  rw [SubstSPD_flatComp_x g hd'] at hci
  rw [SubstSPD_swap_flatAtom, SubstSPD_swap_flatAtom]
  have hs : d.swapSolid.y = d.x := by simp [Comp.swapSolid, hk]
  exact Or.inr (by rw [hs]; exact hci.1)

end SwapThree

section SwapTr

variable {k n : ℕ} (g : Graph k n)

private theorem SubstSPD_swap_len : g.comps.length = g.swapSolid.comps.length := by
  simp [Graph.swapSolid]

private theorem SubstSPD_swap_get (i : Fin g.comps.length) :
    g.swapSolid.comps[Fin.cast (SubstSPD_swap_len g) i] = g.comps[i].swapSolid := by
  simp only [Graph.swapSolid, Fin.getElem_fin, List.getElem_map]; rfl

/-- The edge map from the molecular graph of `g` to that of `g` with its solid edges reversed. -/
private def SubstSPD_swapE : Fin g.comps.length ⊕ Fin k → Fin g.swapSolid.comps.length ⊕ Fin k :=
  Sum.map (Fin.cast (SubstSPD_swap_len g)) id

private theorem SubstSPD_swap_cls (e : Fin g.comps.length ⊕ Fin k) :
    g.swapSolid.toMG'.cls (SubstSPD_swapE g e) = g.toMG'.cls e := by
  have hm : ∀ u, g.swapSolid.molRep (g.swapSolid.flatAtom u) = g.molRep (g.flatAtom u) := by
    intro u; rw [SubstSPD_swap_flatAtom, SubstSPD_swap_molRep]
  rcases e with i | a
  · change g.swapSolid.toMG'.cls (.inl (Fin.cast (SubstSPD_swap_len g) i)) = _
    have hget := SubstSPD_swap_get g i
    by_cases hd : g.comps[i].kind = .dot
    · have hd' : g.swapSolid.comps[Fin.cast (SubstSPD_swap_len g) i].kind = .dot := by
        rw [hget, SubstSPD_swap_kind, hd]
      rw [SubstSPD_cls_dot _ _ hd', SubstSPD_cls_dot _ _ hd]
    · have hd' : g.swapSolid.comps[Fin.cast (SubstSPD_swap_len g) i].kind ≠ .dot := by
        rw [hget, SubstSPD_swap_kind]; exact hd
      rw [SubstSPD_cls_inl _ _ hd', SubstSPD_cls_inl _ _ hd, hget, hm, hm, SubstSPD_swap_kind]
      rcases SubstSPD_swap_ends g.comps[i] with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      exact if_congr eq_comm rfl rfl
  · simp only [SubstSPD_swapE, Sum.map_inr, id, Graph.toMG', SubstSPD_swap_anchor]

private theorem SubstSPD_swap_ends' (e : Fin g.comps.length ⊕ Fin k) (he : g.toMG'.cls e ≠ none) :
    g.swapSolid.toMG'.ends (SubstSPD_swapE g e) = g.toMG'.ends e ∨
      g.swapSolid.toMG'.ends (SubstSPD_swapE g e) = ((g.toMG'.ends e).2, (g.toMG'.ends e).1) := by
  have hm : ∀ u, g.swapSolid.molRep (g.swapSolid.flatAtom u) = g.molRep (g.flatAtom u) := by
    intro u; rw [SubstSPD_swap_flatAtom, SubstSPD_swap_molRep]
  rcases e with i | a
  · change g.swapSolid.toMG'.ends (.inl (Fin.cast (SubstSPD_swap_len g) i)) = _ ∨
      g.swapSolid.toMG'.ends (.inl (Fin.cast (SubstSPD_swap_len g) i)) = _
    have hget := SubstSPD_swap_get g i
    have hd : g.comps[i].kind ≠ .dot := fun h => he (SubstSPD_cls_dot _ _ h)
    have hd' : g.swapSolid.comps[Fin.cast (SubstSPD_swap_len g) i].kind ≠ .dot := by
      rw [hget, SubstSPD_swap_kind]; exact hd
    rw [SubstSPD_ends_inl _ _ hd', SubstSPD_ends_inl _ _ hd, hget, hm, hm]
    rcases SubstSPD_swap_ends g.comps[i] with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · left
    simp only [SubstSPD_swapE, Sum.map_inr, id, Graph.toMG', SubstSPD_swap_anchor,
      SubstSPD_swap_molRep]

/-- Reversing the solid edges changes the molecular graph only by the names of the edges and the
orientation of the solid edges. -/
private theorem SubstSPD_swap_tr : g.toMG'.Transported g.swapSolid.toMG' := by
  have hm : ∀ u, g.swapSolid.molRep u = g.molRep u := SubstSPD_swap_molRep g
  have hinj : Function.Injective (SubstSPD_swapE g) :=
    Sum.map_injective.2 ⟨Fin.cast_injective _, Function.injective_id⟩
  refine ⟨id, SubstSPD_swapE g, fun e₁ e₂ _ _ h => hinj h, Set.injOn_id _, ?_, ?_,
    fun e _ => MolInsert_toMG'_ends_vtx k n g e, fun e _ => SubstSPD_swap_cls g e,
    fun e he => SubstSPD_swap_ends' g e he, fun e' he' => ?_⟩
  · simp only [Finset.image_id, Graph.toMG', hm]
  · simp only [Finset.image_id, Graph.toMG']
  · rcases e' with j | a
    · have hij : SubstSPD_swapE g (.inl (Fin.cast (SubstSPD_swap_len g).symm j)) = .inl j := by
        simp [SubstSPD_swapE]
      rw [← hij, SubstSPD_swap_cls]
      by_contra hn
      exact he' _ hn hij
    · have hij : SubstSPD_swapE g (.inr a) = .inr a := rfl
      rw [← hij, SubstSPD_swap_cls]
      by_contra hn
      exact he' _ hn hij

end SwapTr

/-! ## The graph with the `t`-variable -/

section Host

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

private theorem SubstSPD_G_comps : (H.glue x y₁ y₂ (tVar true)).comps = liftCs 1 H.comps ++
    [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
      mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
      mkC .xdot (liftA 1 y₂) (newA 0)] := by
  simp [Graph.glue, tVar, tVarGraph, Graph.swapEnds, mkC, Comp.map, glueAtom]

private theorem SubstSPD_G_len :
    (H.glue x y₁ y₂ (tVar true)).comps.length = H.comps.length + 5 := by
  rw [SubstSPD_G_comps]; simp [liftCs]

/-- The index of the blue solid edge `G_{y₁α}` of the `t`-variable. -/
private def SubstSPD_bI : Fin (H.glue x y₁ y₂ (tVar true)).comps.length :=
  ⟨H.comps.length + 1, by rw [SubstSPD_G_len]; omega⟩

/-- The index of the red solid edge `Ḡ_{y₂α}` of the `t`-variable. -/
private def SubstSPD_rI : Fin (H.glue x y₁ y₂ (tVar true)).comps.length :=
  ⟨H.comps.length + 2, by rw [SubstSPD_G_len]; omega⟩

private theorem SubstSPD_G_get (j : ℕ) (hj : j < 5) :
    (H.glue x y₁ y₂ (tVar true)).comps[H.comps.length + j]'(by rw [SubstSPD_G_len]; omega) =
      [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
        mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
        mkC .xdot (liftA 1 y₂) (newA 0)][j]'hj := by
  simp only [SubstSPD_G_comps]
  rw [List.getElem_append_right (by simp [liftCs])]
  simp [liftCs]

private theorem SubstSPD_G_b :
    (H.glue x y₁ y₂ (tVar true)).comps[SubstSPD_bI H x y₁ y₂] =
      mkC (.G .plus) (liftA 1 y₁) (newA 0) :=
  SubstSPD_G_get H x y₁ y₂ 1 (by omega)

private theorem SubstSPD_G_r :
    (H.glue x y₁ y₂ (tVar true)).comps[SubstSPD_rI H x y₁ y₂] =
      mkC (.G .minus) (liftA 1 y₂) (newA 0) :=
  SubstSPD_G_get H x y₁ y₂ 2 (by omega)

private theorem SubstSPD_G_s_mem :
    mkC (.waved .s) (newA 0) (liftA 1 x) ∈ (H.glue x y₁ y₂ (tVar true)).comps := by
  rw [SubstSPD_G_comps]; simp

/-- Two atoms joined by a waved or dotted edge lie in one molecule. -/
private theorem SubstSPD_sameMol_of_comp {k n : ℕ} {Γ : Graph k n} {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind.joinsMol = true) (hx : c.x.isRight = true)
    (hy : c.y.isRight = true) : Γ.SameMol c.x c.y := by
  by_cases h : c.x = c.y
  · exact Or.inl h
  · refine Or.inr ⟨hx, hy, SimpleGraph.Adj.reachable ?_⟩
    rw [Graph.molGraph, SimpleGraph.fromRel_adj]
    exact ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩

/-- Two internal atoms in one molecule have the same representative. -/
private theorem SubstSPD_molRep_eq {k n : ℕ} {Γ : Graph k n} {u v : Atom k n}
    (hu : u.isRight = true) (hv : v.isRight = true) (h : Γ.SameMol u v) :
    Γ.molRep u = Γ.molRep v := by
  rcases u with a | a
  · simp at hu
  rcases v with b | b
  · simp at hv
  exact (MolMono_molRep_eq_iff Γ a b).2 h

private theorem SubstSPD_liftA_isRight {j : ℕ} {u : Atom 3 m} (h : u.isRight = true) :
    (liftA j u).isRight = true := by
  rcases u with a | a
  · simp at h
  · rfl

/-- The facts on `K = Graph.toMG'` of `G = H.glue x y₁ y₂ (tVar true)` read by
`MGraph.spd_insert` and `MGraph.insert_weakIso`. -/
private theorem SubstSPD_host (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) :
    let G := H.glue x y₁ y₂ (tVar true)
    let K := G.toMG'
    let u₀ := G.molRep (liftA 1 x)
    let u₁ := G.molRep (liftA 1 y₁)
    let u₂ := G.molRep (liftA 1 y₂)
    let b : Fin G.comps.length ⊕ Fin 3 := .inl (SubstSPD_bI H x y₁ y₂)
    let r : Fin G.comps.length ⊕ Fin 3 := .inl (SubstSPD_rI H x y₁ y₂)
    K.SPD ∧ (∀ e, K.cls e ≠ some .ghost) ∧ Disjoint K.int K.ext ∧
      u₀ ∈ K.int ∧ u₁ ∈ K.int ∧ u₂ ∈ K.int ∧ u₀ ∈ K.MIS ∧ u₁ ∈ K.MIS ∧
      ((K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
        ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b)) ∧
      (K.cls r = none ∨ K.cls r = some .minus) ∧
      (∃ e, K.cls e ≠ none ∧ K.cls e ≠ some .minus ∧
        (((K.ends e).1 ∈ K.int ∧ (K.ends e).2 ∈ K.ext) ∨
          ((K.ends e).1 ∈ K.ext ∧ (K.ends e).2 ∈ K.int))) ∧
      (K.ends r = (u₂, u₀) ∧ (K.cls r = some .minus ∨ u₂ = u₀)) := by
  intro G K u₀ u₁ u₂ b r
  have hα : (newA 0 : Atom 3 (m + 1)).isRight = true := rfl
  have hX := SubstSPD_liftA_isRight (j := 1) hx
  have hY₁ := SubstSPD_liftA_isRight (j := 1) hy₁
  have hY₂ := SubstSPD_liftA_isRight (j := 1) hy₂
  have hαx : G.molRep (newA 0) = u₀ :=
    SubstSPD_molRep_eq hα hX (SubstSPD_sameMol_of_comp (SubstSPD_G_s_mem H x y₁ y₂) rfl hα hX)
  have hflat : ∀ u : Atom 3 (m + 1), u.isRight = true → G.flatAtom u = u := by
    rintro (a | a) h
    · simp at h
    · rfl
  -- the step-2 edge
  obtain ⟨⟨hkb, hm1, hm2, hcase⟩, -⟩ := hst (SubstSPD_bI H x y₁ y₂) rfl
  rw [SubstSPD_G_b] at hkb hm1 hm2 hcase
  simp only [mkC] at hm1 hm2 hcase
  rw [hαx] at hm2
  have hbk : G.comps[SubstSPD_bI H x y₁ y₂].kind ≠ .dot := by rw [SubstSPD_G_b]; simp [mkC]
  have hrk : G.comps[SubstSPD_rI H x y₁ y₂].kind ≠ .dot := by rw [SubstSPD_G_r]; simp [mkC]
  have hbe : K.ends b = (u₁, u₀) := by
    change G.toMG'.ends (.inl (SubstSPD_bI H x y₁ y₂)) = _
    rw [SubstSPD_ends_inl G _ hbk, SubstSPD_G_b]
    simp only [mkC]
    rw [hflat _ hY₁, hflat _ hα, hαx]
  have hbc : K.cls b = if u₁ = u₀ then none else some .plus := by
    change G.toMG'.cls (.inl (SubstSPD_bI H x y₁ y₂)) = _
    rw [SubstSPD_cls_inl G _ hbk, SubstSPD_G_b]
    simp only [mkC, hflat _ hY₁, hflat _ hα, hαx]
    rfl
  have hre : K.ends r = (u₂, u₀) := by
    change G.toMG'.ends (.inl (SubstSPD_rI H x y₁ y₂)) = _
    rw [SubstSPD_ends_inl G _ hrk, SubstSPD_G_r]
    simp only [mkC]
    rw [hflat _ hY₂, hflat _ hα, hαx]
  have hrc : K.cls r = if u₂ = u₀ then none else some .minus := by
    change G.toMG'.cls (.inl (SubstSPD_rI H x y₁ y₂)) = _
    rw [SubstSPD_cls_inl G _ hrk, SubstSPD_G_r]
    simp only [mkC, hflat _ hY₂, hflat _ hα, hαx]
    rfl
  have hint : ∀ u : Atom 3 (m + 1), u.isRight = true → G.molRep u ∈ K.int :=
    fun u h => SubstSPD_mem_int_of_isRight G h
  refine ⟨hI.1, Graph.toMG'_noGhost G hI.2.2.2.1, Graph.toMG'_disjoint G, hint _ hX, hint _ hY₁,
    hint _ hY₂, hm2, hm1, ?_, ?_, ?_, hre, ?_⟩
  · by_cases h : u₁ = u₀
    · exact Or.inl ⟨by rw [hbc]; exact ite_eq_left h, h.symm⟩
    · refine Or.inr ⟨by rw [hbc]; exact ite_eq_right h, hbe, ?_⟩
      rcases hcase with hs | hpd
      · exact absurd ((SubstSPD_molRep_eq hY₁ hα hs).trans hαx) h
      · exact hpd
  · rw [hrc]; split_ifs <;> simp
  · -- an edge from `⊗` to an internal molecule
    have hU : ∀ a : Fin 3, G.Unpinned (.inl a) := fun a => ⟨rfl, fun b hb => by
      have := (Graph.sameBlock_iff_eq G (fun c hc hk => absurd hk (hD c hc)) _ _).1 hb
      simp at this⟩
    obtain ⟨c, hc, hdif, hat⟩ := (hI.2.2.1.2.2.1 (hU 0)).1
    obtain ⟨i, rfl⟩ := SubstSPD_idx hc
    have hk : G.comps[i].kind ≠ .dot := hD _ hc
    have hR : ∀ v : Atom 3 (m + 1), ¬ G.Unpinned v → (G.flatAtom v).isRight = true :=
      fun v hv => SubstSPD_flat_pinned G hv
    have he : (G.comps[i].x = .inl 0 ∧ (G.flatAtom G.comps[i].y).isRight = true) ∨
        (G.comps[i].y = .inl 0 ∧ (G.flatAtom G.comps[i].x).isRight = true) := by
      rcases hat with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hR _ h2⟩
      · exact Or.inr ⟨h1, hR _ h2⟩
    obtain ⟨⟨y, hy, hends⟩, hcls⟩ := SubstSPD_comp_edge G (hU 0) i hk he
    refine ⟨.inl i, ?_, ?_, ?_⟩
    · rw [hcls, SubstSPD_mclass_diff hdif]; simp
    · rw [hcls, SubstSPD_mclass_diff hdif]; simp
    · have h0 := SubstSPD_inl_mem_ext G 0
      rcases hends with h | h <;> rw [h]
      · exact Or.inr ⟨h0, hy⟩
      · exact Or.inl ⟨hy, h0⟩
  · rw [hrc]
    by_cases h : u₂ = u₀
    · exact Or.inr h
    · exact Or.inl (ite_eq_right h)

end Host

/-! ## The `O_dot` forms of a balanced graph -/

section Balanced

/-- Every solid edge carries a `×`-dotted edge with the same ends, and every `×`-dotted edge
between distinct atoms carries a solid edge. -/
private def SubstSPD_Bal {V : Type*} (cs : List (Comp V)) : Prop :=
  (∀ c ∈ cs, c.kind.isSolid = true → ∃ d ∈ cs, d.kind = .xdot ∧
    (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x)) ∧
  (∀ c ∈ cs, c.kind = .xdot → c.x ≠ c.y → ∃ d ∈ cs, d.kind.isSolid = true ∧
    (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x))

private theorem SubstSPD_Bal_map {V W : Type*} {cs : List (Comp V)} (f : V → W)
    (h : SubstSPD_Bal cs) : SubstSPD_Bal (cs.map (Comp.map f)) := by
  refine ⟨fun c hc hk => ?_, fun c hc hk hne => ?_⟩
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨d, hd, hdk, hde⟩ := h.1 c₀ hc₀ hk
    refine ⟨d.map f, List.mem_map.2 ⟨d, hd, rfl⟩, hdk, ?_⟩
    simp only [Comp.map]
    rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    have hne' : c₀.x ≠ c₀.y := fun e => hne (by simp [Comp.map, e])
    obtain ⟨d, hd, hdk, hde⟩ := h.2 c₀ hc₀ hk hne'
    refine ⟨d.map f, List.mem_map.2 ⟨d, hd, rfl⟩, hdk, ?_⟩
    simp only [Comp.map]
    rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

private theorem SubstSPD_Bal_append {V : Type*} {a b : List (Comp V)} (ha : SubstSPD_Bal a)
    (hb : SubstSPD_Bal b) : SubstSPD_Bal (a ++ b) := by
  refine ⟨fun c hc hk => ?_, fun c hc hk hne => ?_⟩
  · rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨d, hd, h⟩ := ha.1 c hc hk
      exact ⟨d, List.mem_append_left _ hd, h⟩
    · obtain ⟨d, hd, h⟩ := hb.1 c hc hk
      exact ⟨d, List.mem_append_right _ hd, h⟩
  · rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨d, hd, h⟩ := ha.2 c hc hk hne
      exact ⟨d, List.mem_append_left _ hd, h⟩
    · obtain ⟨d, hd, h⟩ := hb.2 c hc hk hne
      exact ⟨d, List.mem_append_right _ hd, h⟩

private theorem SubstSPD_Bal_normal {k n C : ℕ} {Γ : Graph k n} (h : Γ.Normal C) :
    SubstSPD_Bal Γ.comps := by
  refine ⟨fun c hc hk => ?_, fun c hc hk hne => ?_⟩
  · obtain ⟨d, hd, hdk, hde⟩ := (h.2.2 c.x c.y (h.2.1 c hc hk)).2 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨d, hd, hdk, hde⟩
  · exact (h.2.2 c.x c.y hne).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩

private theorem SubstSPD_liftA_inj {m j : ℕ} : Function.Injective (liftA (k := 3) (n := m) j) :=
  Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective _ _⟩

private theorem SubstSPD_liftA_ne_newA {m j : ℕ} (u : Atom 3 m) (i : Fin j) :
    liftA j u ≠ newA i := by
  rcases u with a | a
  · simp [liftA, newA]
  · simp only [liftA, newA, Sum.map_inr, ne_eq, Sum.inr.injEq, Fin.ext_iff, Fin.val_castAdd,
      Fin.val_natAdd]
    omega

/-- The components of `H` are balanced when `H.glue x y₁ y₂ (tVar true)` is normal regular: the
components of the `t`-variable all end at its new atom. -/
private theorem SubstSPD_Bal_H {m C : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)
    (hN : (H.glue x y₁ y₂ (tVar true)).Normal C) : SubstSPD_Bal H.comps := by
  have hB := SubstSPD_Bal_normal hN
  rw [SubstSPD_G_comps] at hB
  have hmem : ∀ c ∈ H.comps, c.map (liftA 1) ∈ liftCs 1 H.comps ++
      [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
        mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
        mkC .xdot (liftA 1 y₂) (newA 0)] :=
    fun c hc => List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩)
  have hback : ∀ (c : Comp (Atom 3 m)) (d : Comp (Atom 3 (m + 1))), d ∈ liftCs 1 H.comps ++
      [mkC (.waved .s) (newA 0) (liftA 1 x), mkC (.G .plus) (liftA 1 y₁) (newA 0),
        mkC (.G .minus) (liftA 1 y₂) (newA 0), mkC .xdot (liftA 1 y₁) (newA 0),
        mkC .xdot (liftA 1 y₂) (newA 0)] →
      (d.x = liftA 1 c.x ∧ d.y = liftA 1 c.y ∨ d.x = liftA 1 c.y ∧ d.y = liftA 1 c.x) →
      ∃ d₀ ∈ H.comps, d₀.kind = d.kind ∧ (d₀.x = c.x ∧ d₀.y = c.y ∨ d₀.x = c.y ∧ d₀.y = c.x) := by
    intro c d hd hde
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      refine ⟨d₀, hd₀, rfl, ?_⟩
      simp only [Comp.map] at hde
      rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨SubstSPD_liftA_inj h1, SubstSPD_liftA_inj h2⟩
      · exact Or.inr ⟨SubstSPD_liftA_inj h1, SubstSPD_liftA_inj h2⟩
    · exfalso
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [mkC] at hde <;>
        rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        first
        | exact SubstSPD_liftA_ne_newA _ _ h1.symm
        | exact SubstSPD_liftA_ne_newA _ _ h2.symm
  refine ⟨fun c hc hk => ?_, fun c hc hk hne => ?_⟩
  · obtain ⟨d, hd, hdk, hde⟩ := hB.1 _ (hmem c hc) hk
    obtain ⟨d₀, hd₀, hk₀, hde₀⟩ := hback c d hd hde
    exact ⟨d₀, hd₀, hk₀.trans hdk, hde₀⟩
  · obtain ⟨d, hd, hdk, hde⟩ := hB.2 _ (hmem c hc) hk
      (fun e => hne (SubstSPD_liftA_inj e))
    obtain ⟨d₀, hd₀, hk₀, hde₀⟩ := hback c d hd hde
    exact ⟨d₀, hd₀, by rw [hk₀]; exact hdk, hde₀⟩

private theorem SubstSPD_foldl_mem {α : Type*} (F : List α → α → List α)
    (hF : ∀ acc p, F acc p = acc ∨ F acc p = acc ++ [p]) :
    ∀ (l acc : List α) (q : α), q ∈ l.foldl F acc → q ∈ acc ∨ q ∈ l
  | [], _, _, h => Or.inl h
  | p :: l, acc, q, h => by
    rcases SubstSPD_foldl_mem F hF l (F acc p) q h with h1 | h1
    · rcases hF acc p with h2 | h2
      · rw [h2] at h1
        exact Or.inl h1
      · rw [h2, List.mem_append, List.mem_singleton] at h1
        rcases h1 with h1 | rfl
        · exact Or.inl h1
        · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- A balanced graph has no pair to split in `O_dot`. -/
private theorem SubstSPD_splitPairs_nil {k n : ℕ} {Γ : Graph k n} (hb : SubstSPD_Bal Γ.comps) :
    Γ.splitPairs = [] := by
  unfold Graph.splitPairs
  dsimp only
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  rcases SubstSPD_foldl_mem _ (fun acc q => by split_ifs <;> simp) _ [] p hp with h | h
  · simp at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hcp⟩ := h
  split_ifs at hcp with hk
  obtain rfl := Option.some.inj hcp
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
  obtain ⟨hk, hne⟩ := hk
  have h1 : spJoined Γ Kind.isSolid c.x c.y = true := by
    rw [spJoined_iff]
    rcases hk with hk | hk
    · exact ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨d, hd, hdk, hde⟩ := hb.2 c hc hk hne
      exact ⟨d, hd, hdk, hde⟩
  have h2 : spJoined Γ (· == .xdot) c.x c.y = true := by
    rw [spJoined_iff]
    rcases hk with hk | hk
    · obtain ⟨d, hd, hdk, hde⟩ := hb.1 c hc hk
      exact ⟨d, hd, by simp [hdk], hde⟩
    · exact ⟨c, hc, by simp [hk], Or.inl ⟨rfl, rfl⟩⟩
  change (if (spJoined Γ Kind.isSolid c.x c.y != spJoined Γ (· == .xdot) c.x c.y) = true then
    some (c.x, c.y, spJoined Γ Kind.isSolid c.x c.y) else none) = none
  rw [h1, h2]
  rfl

private theorem SubstSPD_dotChoice_nil {k n : ℕ} (Γ : Graph k n) : Γ.dotChoice [] [] = Γ := by
  obtain ⟨cs, c⟩ := Γ
  simp [Graph.dotChoice]

/-- On a balanced graph whose dotted edges join internal atoms, the `O_dot` forms have the
molecular graph of the graph, up to names. -/
private theorem SubstSPD_oDotT_bal {n : ℕ} {Γ : Graph 3 n} (hb : SubstSPD_Bal Γ.comps)
    (hdots : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true) :
    ∀ t ∈ oDotT Γ, (spdPM' t.g ↔ spdPM' Γ) ∧ (gsPM' t.g ↔ gsPM' Γ) := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, hA, hm⟩
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · rw [SubstSPD_splitPairs_nil hb, List.sublist_nil] at hA
    subst hA
    rw [SubstSPD_splitPairs_nil hb, SubstSPD_dotChoice_nil] at hm
    exact ⟨(SubstMol_spdPM'_mergeT 3 n _ t (by norm_num) hdots hm).symm,
      (SubstMol_gsPM'_mergeT 3 n _ t (by norm_num) hdots hm).symm⟩

end Balanced

/-! ## The substituted graph -/

section Subst

variable {m n' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

private theorem SubstSPD_glueAtom_isRight (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (u : Atom 3 n') : (glueAtom x y₁ y₂ u).isRight = true := by
  rcases u with a | a
  · fin_cases a
    · exact SubstSPD_liftA_isRight hx
    · exact SubstSPD_liftA_isRight hy₁
    · exact SubstSPD_liftA_isRight hy₂
  · rfl

/-- The components of `H` have no dotted edge when `H.glue x y₁ y₂ (tVar true)` has none. -/
private theorem SubstSPD_H_nodot (hD : (H.glue x y₁ y₂ (tVar true)).DotFree) :
    ∀ c ∈ H.comps, c.kind ≠ .dot := by
  intro c hc
  have := hD (c.map (liftA 1)) (by
    rw [SubstSPD_G_comps]; exact List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩))
  exact this

/-- In `H.glue x y₁ y₂ g`, every dotted edge joins two internal atoms. -/
private theorem SubstSPD_glue_dots (g : Graph 3 n') (hx : x.isRight = true)
    (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (hD : (H.glue x y₁ y₂ (tVar true)).DotFree) :
    ∀ c ∈ (H.glue x y₁ y₂ g).comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true := by
  intro c hc hk
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact absurd hk (SubstSPD_H_nodot H x y₁ y₂ hD c₀ hc₀)
  · obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨SubstSPD_glueAtom_isRight x y₁ y₂ hx hy₁ hy₂ _,
      SubstSPD_glueAtom_isRight x y₁ y₂ hx hy₁ hy₂ _⟩

/-- `H.glue x y₁ y₂ g` is balanced when `H.glue x y₁ y₂ (tVar true)` and `g` are normal
regular. -/
private theorem SubstSPD_glue_bal {C C' : ℕ} (g : Graph 3 n')
    (hN : (H.glue x y₁ y₂ (tVar true)).Normal C) (hN' : g.Normal C') :
    SubstSPD_Bal (H.glue x y₁ y₂ g).comps :=
  SubstSPD_Bal_append (SubstSPD_Bal_map _ (SubstSPD_Bal_H H x y₁ y₂ hN))
    (SubstSPD_Bal_map _ (SubstSPD_Bal_normal hN'))

private theorem SubstSPD_swap_noGhost (g : Graph 3 n') (h : g.NoGhost) : g.swapSolid.NoGhost := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := (SubstSPD_swap_mem g).1 hc
  rw [SubstSPD_swap_kind]
  exact h d hd

/-- The molecular graph of `g` with its solid edges reversed, inserted into that of
`H.glue x y₁ y₂ (tVar true)` as in `toMG'_glue`, is sequentially pre-deterministic. -/
private theorem SubstSPD_glue_spd (g : Graph 3 n') (hx : x.isRight = true)
    (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (hD : (H.glue x y₁ y₂ (tVar true)).DotFree) (hI : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hs : spdPM' g) (hE : g.ExtClause) (hC : g.ColourInvB) (hT : g.TensorDiffusive)
    (hA : g.AtExternals) (hG : g.NoGhost) (hX : g.dotExcess = 0) :
    ((H.glue x y₁ y₂ (tVar true)).toMG'.insert g.swapSolid.toMG'
      (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
        fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
      {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).SPD := by
  obtain ⟨hK1, hK2, hK3, hu₀, hu₁, hu₂, hm₀, hm₁, hk3, hk4, hk5, -⟩ :=
    SubstSPD_host H x y₁ y₂ hx hy₁ hy₂ hD hI hst
  have hL2 := SubstSPD_L2 g.swapSolid
    (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
    _ _ _ rfl rfl rfl (SubstSPD_swap_extClause g hE) (SubstSPD_swap_tensor g hT)
    (SubstSPD_swap_atExt g hA) (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstSPD_swap_ci g hC)
  have hLs : g.swapSolid.toMG'.SPD :=
    (MGraph.spd_transport _ _ _ _ _ _ (SubstSPD_swap_tr g)).2 hs
  exact MGraph.spd_insert _ _ _ _ _ _ _ _ _ _ _ _ hK1 hK2 hK3 hu₀ hu₁ hu₂ hm₀ hm₁ hk3 hk4 hk5
    hLs (Graph.toMG'_noGhost _ (SubstSPD_swap_noGhost g hG)) (Graph.toMG'_disjoint _) hL2

end Subst

/-- Inserting a graph without ghost edges into a graph without ghost edges creates none. -/
private theorem SubstSPD_insert_noGhost {V W E F : Type} [DecidableEq V] [DecidableEq W]
    [DecidableEq E] {K : MGraph V E} {L : MGraph W F} (σ : W → V) (B : Finset E)
    (hK : ∀ e, K.cls e ≠ some .ghost) (hL : ∀ f, L.cls f ≠ some .ghost) :
    ∀ e, (K.insert L σ B).cls e ≠ some .ghost := by
  rintro (e | f)
  · change (if e ∈ B then none else K.cls e) ≠ _
    split_ifs
    · simp
    · exact hK e
  · exact hL f

/-- **[II, Lemma 6.5 (2)], the sequentially pre-deterministic property** in the block reading
(picture (6.5)): let `G = H.glue x y₁ y₂ (tVar true)` have no dotted edge, the invariant
`Graph.InvB'` and the blue solid edge `G_{y₁α}` chosen by Step 2 of [II, Strategy 6.6], and let
`g` be sequentially pre-deterministic in the block reading, with the clause on the external atoms,
the charge pattern of the block normal form, only diffusive edges at `⊗`, [II, Def 3.2 (9)], no
ghost edge and dot excess `0`. Then `H.glue x y₁ y₂ g.swapSolid` is sequentially
pre-deterministic in the block reading, and so are its `O_dot` forms when `G` and `g` are normal
regular. -/
theorem substSPDB :
  ∀ (m n' : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n'),
    (H.glue x y₁ y₂ (tVar true)).DotFree → (H.glue x y₁ y₂ (tVar true)).InvB' →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    spdPM' g → g.ExtClause → g.ColourInvB → g.TensorDiffusive → g.AtExternals → g.NoGhost →
    g.dotExcess = 0 →
    spdPM' (H.glue x y₁ y₂ g.swapSolid) ∧
      ∀ C C', (H.glue x y₁ y₂ (tVar true)).Normal C → g.Normal C' →
        ∀ t ∈ oDotT (H.glue x y₁ y₂ g.swapSolid), spdPM' t.g := by
  intro m n' H x y₁ y₂ g hD hI hst hs hE hC hT hA hG hX
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hGl := SubstSPD_glue_spd H x y₁ y₂ g hx hy₁ hy₂ hD hI hst hs hE hC hT hA hG hX
  obtain ⟨π, hidem, hint, hext, hnie, hdis, hR2, -, ht⟩ :=
    toMG'_glue m n' H x y₁ y₂ g.swapSolid hD hx hy₁ hy₂
  have hng := SubstSPD_insert_noGhost (K := (H.glue x y₁ y₂ (tVar true)).toMG')
    (L := g.swapSolid.toMG')
    (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
    {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}
    (Graph.toMG'_noGhost _ hI.2.2.2.1) (Graph.toMG'_noGhost _ (SubstSPD_swap_noGhost g hG))
  have h1 := MGraph.spd_mapV_merge _ _ _ π hidem hint hext hnie hGl hng hdis hR2
  have hspd : spdPM' (H.glue x y₁ y₂ g.swapSolid) := (MGraph.spd_transport _ _ _ _ _ _ ht).2 h1
  refine ⟨hspd, fun C C' hN hN' t ht' => ?_⟩
  exact (SubstSPD_oDotT_bal (SubstSPD_glue_bal H x y₁ y₂ g.swapSolid hN
    (Graph.swapSolid_Normal hN')) (SubstSPD_glue_dots H x y₁ y₂ g.swapSolid hx hy₁ hy₂ hD) t
    ht').1.2 hspd


/-! ## Molecules under maps of the atoms -/

section MolMap

variable {k n k' n' : ℕ}

/-- A map that sends every waved or dotted component to one atom or to a waved or dotted component
keeps two atoms joined by a path of waved and dotted edges. -/
private theorem SubstSPD_reach_map {Γ : Graph k n} {Γ' : Graph k' n'}
    (f : Atom k n → Atom k' n')
    (hf : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → f c.x = f c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind.joinsMol = true ∧ c'.x = f c.x ∧ c'.y = f c.y) {u v : Atom k n}
    (h : Γ.molGraph.Reachable u v) : Γ'.molGraph.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj _ ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hadj
    by_cases he : f a = f b
    · rw [he]
    · refine SimpleGraph.Adj.reachable ?_
      rw [Graph.molGraph, SimpleGraph.fromRel_adj]
      obtain ⟨-, ⟨d, hd, hj, rfl, rfl⟩ | ⟨d, hd, hj, rfl, rfl⟩⟩ := hadj
      · rcases hf d hd hj with h' | ⟨d', hd', hj', hx, hy⟩
        · exact absurd h' he
        · exact ⟨he, Or.inl ⟨d', hd', hj', hx, hy⟩⟩
      · rcases hf d hd hj with h' | ⟨d', hd', hj', hx, hy⟩
        · exact absurd h'.symm he
        · exact ⟨he, Or.inr ⟨d', hd', hj', hx, hy⟩⟩

private theorem SubstSPD_sameMol_map {Γ : Graph k n} {Γ' : Graph k' n'}
    (f : Atom k n → Atom k' n')
    (hf : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → f c.x = f c.y ∨
      ∃ c' ∈ Γ'.comps, c'.kind.joinsMol = true ∧ c'.x = f c.x ∧ c'.y = f c.y)
    {u v : Atom k n} (hu : (f u).isRight = true) (hv : (f v).isRight = true)
    (h : Γ.SameMol u v) : Γ'.SameMol (f u) (f v) := by
  rcases h with rfl | ⟨-, -, hr⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hu, hv, SubstSPD_reach_map f hf hr⟩

end MolMap

section Recoll

variable {m n' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n')

/-- The reading of the atoms of `H` times the `t`-variable in `H` times a substituted graph: the
atoms of `H` keep their names and the atom `α` goes to `x`. -/
private def SubstSPD_lift : Atom 3 (m + 1) → Atom 3 (m + n') :=
  Sum.elim (fun a => .inl a) (fun i => if h : i.val < m then .inr ⟨i.val, by omega⟩ else liftA n' x)

private theorem SubstSPD_lift_liftA (u : Atom 3 m) :
    SubstSPD_lift (n' := n') x (liftA 1 u) = liftA n' u := by
  rcases u with a | a
  · rfl
  · simp only [SubstSPD_lift, liftA, Sum.map_inr, Sum.elim_inr]
    rw [dite_eq_left (by simp)]
    rfl

/-- The molecules of `H.glue x y₁ y₂ (tVar true)` are carried into those of `H.glue x y₁ y₂ g`. -/
private theorem SubstSPD_sameMol_host {u v : Atom 3 (m + 1)}
    (hu : (SubstSPD_lift (n' := n') x u).isRight = true)
    (hv : (SubstSPD_lift (n' := n') x v).isRight = true)
    (h : (H.glue x y₁ y₂ (tVar true)).SameMol u v) :
    (H.glue x y₁ y₂ g).SameMol (SubstSPD_lift x u) (SubstSPD_lift x v) := by
  refine SubstSPD_sameMol_map _ (fun c hc hj => ?_) hu hv h
  rw [SubstSPD_G_comps] at hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    refine Or.inr ⟨c₀.map (liftA n'), List.mem_append_left _ (List.mem_map.2 ⟨c₀, hc₀, rfl⟩),
      hj, ?_, ?_⟩ <;> simp [Comp.map, SubstSPD_lift_liftA]
  · left
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      first
      | (simp [mkC, Kind.joinsMol] at hj; done)
      | (change SubstSPD_lift x (newA 0) = SubstSPD_lift x (liftA 1 x)
         rw [SubstSPD_lift_liftA]
         simp [SubstSPD_lift, newA])

/-- The molecules of `g` are carried into those of `H.glue x y₁ y₂ g`. -/
private theorem SubstSPD_sameMol_g (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) {u v : Atom 3 n'} (h : g.molGraph.Reachable u v) :
    (H.glue x y₁ y₂ g).SameMol (glueAtom x y₁ y₂ u) (glueAtom x y₁ y₂ v) := by
  refine Or.inr ⟨SubstSPD_glueAtom_isRight x y₁ y₂ hx hy₁ hy₂ u,
    SubstSPD_glueAtom_isRight x y₁ y₂ hx hy₁ hy₂ v, SubstSPD_reach_map _ (fun c hc hj => ?_) h⟩
  exact Or.inr ⟨c.map (glueAtom x y₁ y₂), List.mem_append_right _ (List.mem_map.2 ⟨c, hc, rfl⟩),
    hj, rfl, rfl⟩

private theorem SubstSPD_dot_reach {k n : ℕ} {Γ : Graph k n} {u v : Atom k n}
    (h : Γ.SameBlock u v) : Γ.molGraph.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj _ ih =>
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) ih
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    rw [Graph.molGraph, SimpleGraph.fromRel_adj]
    obtain ⟨hne, ⟨d, hd, hk, rfl, rfl⟩ | ⟨d, hd, hk, rfl, rfl⟩⟩ := hadj
    · exact ⟨hne, Or.inl ⟨d, hd, by rw [hk]; rfl, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨d, hd, by rw [hk]; rfl, rfl, rfl⟩⟩

/-- For a `⊕`-recollision graph `g` at `𝔟₁ = 𝔟₂`, the molecule of an internal atom of the block of
`⊕` or `⊖` lies, in `H.glue x y₁ y₂ g`, in the molecule of `y₁` or `y₂`. -/
private theorem SubstSPD_recoll (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (hR : g.DiagRecoll) :
    ∃ (b : Fin n') (e : Fin 3), (e = 1 ∨ e = 2) ∧
      (H.glue x y₁ y₂ g).SameMol
        (SubstSPD_lift x ((H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] e))))
        (glueAtom x y₁ y₂ (g.molRep (.inr b))) := by
  rw [Graph.DiagRecoll, List.any_eq_true] at hR
  obtain ⟨B, hB, hb⟩ := hR
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] at hb
  obtain ⟨hpm, u, hu, hur⟩ := hb
  rcases u with a | b
  · simp at hur
  have key : ∀ e : Fin 3, (e = 1 ∨ e = 2) → (.inl e : Atom 3 n') ∈ B → ∃ (b : Fin n') (e' : Fin 3),
      (e' = 1 ∨ e' = 2) ∧ (H.glue x y₁ y₂ g).SameMol
        (SubstSPD_lift x ((H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] e'))))
        (glueAtom x y₁ y₂ (g.molRep (.inr b))) := by
    intro e he heB
    refine ⟨b, e, he, ?_⟩
    have E := (H.glue x y₁ y₂ g).sameMol_equivalence
    have hye : (![x, y₁, y₂] e).isRight = true := by rcases he with rfl | rfl <;> assumption
    have hY : (liftA 1 (![x, y₁, y₂] e)).isRight = true := SubstSPD_liftA_isRight hye
    obtain ⟨c, hc, hcm⟩ : ∃ c, (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] e)) =
        .inr c ∧ (H.glue x y₁ y₂ (tVar true)).SameMol (liftA 1 (![x, y₁, y₂] e)) (.inr c) := by
      rcases hl : liftA 1 (![x, y₁, y₂] e) with a' | a'
      · rw [hl] at hY; simp at hY
      · obtain ⟨c, h1, h2⟩ := MolMono_molRep_inr (H.glue x y₁ y₂ (tVar true)) a'
        exact ⟨c, h1, h2⟩
    have hcR : (SubstSPD_lift (n' := n') x (.inr c)).isRight = true := by
      simp only [SubstSPD_lift, Sum.elim_inr]
      split_ifs
      · rfl
      · exact SubstSPD_liftA_isRight hx
    have h1 : (H.glue x y₁ y₂ g).SameMol (liftA n' (![x, y₁, y₂] e))
        (SubstSPD_lift x (.inr c)) := by
      have := SubstSPD_sameMol_host H x y₁ y₂ g (u := liftA 1 (![x, y₁, y₂] e)) (v := .inr c)
        (by rw [SubstSPD_lift_liftA]; exact SubstSPD_liftA_isRight hye) hcR hcm
      rwa [SubstSPD_lift_liftA] at this
    have h2 : (H.glue x y₁ y₂ g).SameMol (glueAtom x y₁ y₂ (.inl e))
        (glueAtom x y₁ y₂ (.inr b)) :=
      SubstSPD_sameMol_g H x y₁ y₂ g hx hy₁ hy₂ (SubstSPD_dot_reach
        ((g.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, heB, hu⟩))
    obtain ⟨b', hb', hbm⟩ := MolMono_molRep_inr g b
    have h3 : (H.glue x y₁ y₂ g).SameMol (glueAtom x y₁ y₂ (.inr b))
        (glueAtom x y₁ y₂ (g.molRep (.inr b))) := by
      rw [hb']
      rcases hbm with h | ⟨-, -, hr⟩
      · rw [h]; exact Or.inl rfl
      · exact SubstSPD_sameMol_g H x y₁ y₂ g hx hy₁ hy₂ hr
    rw [hc]
    exact E.trans (E.symm h1) (E.trans h2 h3)
  rcases hpm with h | h
  · exact key 1 (Or.inl rfl) h
  · exact key 2 (Or.inr rfl) h

end Recoll

private theorem SubstSPD_swap_blocks {n : ℕ} (g : Graph 3 n) :
    dotBlocks (allAtoms 3 n) g.swapSolid.comps = dotBlocks (allAtoms 3 n) g.comps := by
  unfold dotBlocks
  simp only [Graph.swapSolid, List.foldl_map]
  congr 1
  funext P c
  rw [SubstSPD_swap_kind]
  split_ifs with h
  · rw [SubstSPD_swap_of_ns (by rw [h]; rfl)]
  · rfl

/-- **[II, Lemma 6.5 (2)], the globally standard property** in the block reading (picture (6.5),
the chain (6.6)): under the hypotheses of `substSPDB`, with `G = H.glue x y₁ y₂ (tVar true)` and
`g` globally standard in the block reading ([II, Def 6.2]) and `g` a `⊕`-recollision graph at
`𝔟₁ = 𝔟₂` (`Graph.DiagRecoll`), the graph `H.glue x y₁ y₂ g.swapSolid` is globally standard in the
block reading, and so are its `O_dot` forms when `G` and `g` are normal regular. The set of the
molecules of `g` is the only member of the chain (6.6) that can be strongly isolated; the dotted
edge of `g` from `⊕` or `⊖` to an internal atom puts one of its molecules into the molecule of
`y₁` or `y₂`. -/
theorem substGSB :
  ∀ (m n' : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (g : Graph 3 n'),
    (H.glue x y₁ y₂ (tVar true)).DotFree → (H.glue x y₁ y₂ (tVar true)).InvB' →
    gsPM' (H.glue x y₁ y₂ (tVar true)) →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    gsPM' g → g.ExtClause → g.ColourInvB → g.TensorDiffusive → g.AtExternals → g.NoGhost →
    g.dotExcess = 0 → g.DiagRecoll →
    gsPM' (H.glue x y₁ y₂ g.swapSolid) ∧
      ∀ C C', (H.glue x y₁ y₂ (tVar true)).Normal C → g.Normal C' →
        ∀ t ∈ oDotT (H.glue x y₁ y₂ g.swapSolid), gsPM' t.g := by
  intro m n' H x y₁ y₂ g hD hI hGs hst hgs hE hC hT hA hG hX hR
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hGl := SubstSPD_glue_spd H x y₁ y₂ g hx hy₁ hy₂ hD hI hst hgs.1 hE hC hT hA hG hX
  obtain ⟨π, hidem, hint, hext, hnie, hdis, hR2, hmol, ht⟩ :=
    toMG'_glue m n' H x y₁ y₂ g.swapSolid hD hx hy₁ hy₂
  obtain ⟨hK1, hK2, hK3, hu₀, hu₁, hu₂, hm₀, hm₁, hk3, hk4, hk5, hr⟩ :=
    SubstSPD_host H x y₁ y₂ hx hy₁ hy₂ hD hI hst
  have hL2 := SubstSPD_L2 g.swapSolid
    (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
    _ _ _ rfl rfl rfl (SubstSPD_swap_extClause g hE) (SubstSPD_swap_tensor g hT)
    (SubstSPD_swap_atExt g hA) (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstSPD_swap_ci g hC)
  have hLg : g.swapSolid.toMG'.GloballyStandard :=
    (SubstMol_gs_transport (SubstSPD_swap_tr g)).2 hgs
  have hw := MGraph.insert_weakIso _ _ _ _ _ _ _ _ _ _ _ _ hK1 hK2 hK3 hu₀ hu₁ hu₂ hm₀ hm₁ hk3 hk4
    hk5 hLg.1 (Graph.toMG'_noGhost _ (SubstSPD_swap_noGhost g hG)) (Graph.toMG'_disjoint _) hL2
    hGs hLg hr
  have hng := SubstSPD_insert_noGhost (K := (H.glue x y₁ y₂ (tVar true)).toMG')
    (L := g.swapSolid.toMG')
    (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
    {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}
    (Graph.toMG'_noGhost _ hI.2.2.2.1) (Graph.toMG'_noGhost _ (SubstSPD_swap_noGhost g hG))
  have hR' : g.swapSolid.DiagRecoll := by
    unfold Graph.DiagRecoll at hR ⊢
    rw [SubstSPD_swap_blocks]
    exact hR
  obtain ⟨b, e, he, hsm⟩ := SubstSPD_recoll H x y₁ y₂ g.swapSolid hx hy₁ hy₂ hR'
  have hsat : ∀ P, ((H.glue x y₁ y₂ (tVar true)).toMG'.insert g.swapSolid.toMG'
      (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
        fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
      {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).IsProperIso
      ((H.glue x y₁ y₂ (tVar true)).toMG'.insert g.swapSolid.toMG'
      (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
        fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
      {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).int P →
      P = ((H.glue x y₁ y₂ (tVar true)).toMG'.insert g.swapSolid.toMG'
      (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
        fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
      {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).int.filter
        (fun v => π v ∈ P.image π) →
      ((H.glue x y₁ y₂ (tVar true)).toMG'.insert g.swapSolid.toMG'
      (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
        fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
      {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).IsWeaklyIso P := by
    intro P hP hPs
    refine hw P hP (fun hPX => ?_)
    have huI : (.inl ((H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] e))) :
        Atom 3 (m + 1) ⊕ Atom 3 n') ∈ ((H.glue x y₁ y₂ (tVar true)).toMG'.int).disjSum
          g.swapSolid.toMG'.int := by
      refine Finset.inl_mem_disjSum.2 (SubstSPD_mem_int_of_isRight _ ?_)
      refine SubstSPD_liftA_isRight ?_
      rcases he with rfl | rfl
      · exact hy₁
      · exact hy₂
    have hMI : (.inr (g.swapSolid.molRep (.inr b)) : Atom 3 (m + 1) ⊕ Atom 3 n') ∈
        ((H.glue x y₁ y₂ (tVar true)).toMG'.int).disjSum g.swapSolid.toMG'.int :=
      Finset.inr_mem_disjSum.2 (SubstSPD_molRep_mem _ b)
    have hπ := (hmol _ huI _ hMI).2 hsm
    have hin : (.inl ((H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] e))) :
        Atom 3 (m + 1) ⊕ Atom 3 n') ∈ P := by
      rw [hPs]
      refine Finset.mem_filter.2 ⟨huI, Finset.mem_image.2 ⟨_, ?_, hπ.symm⟩⟩
      rw [hPX]
      exact Finset.inr_mem_disjSum.2 (SubstSPD_molRep_mem _ b)
    rw [hPX] at hin
    simp at hin
  have h1 := MGraph.gs_mapV_merge _ _ _ π hidem hint hext hnie hGl hng hdis hR2 hsat
  have hgs' : gsPM' (H.glue x y₁ y₂ g.swapSolid) := (SubstMol_gs_transport ht).2 h1
  refine ⟨hgs', fun C C' hN hN' t ht' => ?_⟩
  exact (SubstSPD_oDotT_bal (SubstSPD_glue_bal H x y₁ y₂ g.swapSolid hN
    (Graph.swapSolid_Normal hN')) (SubstSPD_glue_dots H x y₁ y₂ g.swapSolid hx hy₁ hy₂ hD) t
    ht').2.2 hgs'

/-! ## Row (2): the graphs of `R` -/

section Row2

private theorem SubstSPD_swap_label {k n : ℕ} (c : Comp (Atom k n)) :
    c.swapSolid.label = c.label := by
  unfold Comp.swapSolid; split <;> rfl

private theorem SubstSPD_swap_otimesNoDot {n : ℕ} {Γ : Graph 3 n} (h : Γ.TensorDiffusive) :
    Γ.swapSolid.OtimesNoDot := by
  intro c hc hx hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  rw [SubstSPD_swap_kind] at hk
  rw [SubstSPD_swap_of_ns (by rw [hk]; rfl)] at hx
  have := List.all_eq_true.1 h a ha
  rcases hx with hx | hx <;> simp [hx, hk, Kind.isDiffusive] at this

private theorem SubstSPD_swap_labels {k n : ℕ} (Γ : Graph k n) :
    Γ.swapSolid.labels = Γ.labels := by
  simp only [Graph.labels, Graph.swapSolid, List.filterMap_map]
  congr 2
  funext c
  simp [SubstSPD_swap_label]

private theorem SubstSPD_swap_noLabDot {k n : ℕ} {Γ : Graph k n} (h : Γ.NoLabDot) :
    Γ.swapSolid.NoLabDot := by
  intro c hc hk
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  rw [SubstSPD_swap_kind] at hk
  rw [SubstSPD_swap_label]
  exact h a ha hk

private theorem SubstSPD_swap_labelFree {k n : ℕ} {Γ : Graph k n} (h : Γ.LabelFree) :
    Γ.swapSolid.LabelFree := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  rw [SubstSPD_swap_label]
  exact h a ha

private theorem SubstSPD_tVar_ord : (tVar true).ord = 2 := by
  decide +kernel

/-- A recollision graph `𝔟₁ = 𝔟₂` is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`. -/
private theorem SubstSPD_diagRecoll_of {n : ℕ} {Γ : Graph 3 n} (h : Γ.IsRecollision {1, 2}) :
    Γ.DiagRecoll := by
  obtain ⟨c, hc, hk, hb⟩ := h
  have key : ∀ (b : Fin 3) (i : Fin n), (b = 1 ∨ b = 2) → Γ.SameBlock (.inl b) (.inr i) →
      Γ.DiagRecoll := by
    intro b i hb' hs
    obtain ⟨B, hB, hu, hv⟩ := (Γ.sameBlock_iff_mem_dotBlocks _ _).1 hs
    rw [Graph.DiagRecoll, List.any_eq_true]
    refine ⟨B, hB, ?_⟩
    rcases hb' with rfl | rfl <;>
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] <;>
      exact ⟨by simp [hu], .inr i, hv, rfl⟩
  have hsb : Γ.SameBlock c.x c.y := by
    by_cases hxy : c.x = c.y
    · rw [hxy]; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
      exact ⟨hxy, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
  rcases hb with ⟨⟨b, hbB, hx⟩, hy⟩ | ⟨⟨b, hbB, hy⟩, hx⟩
  · rcases hcy : c.y with a | i
    · rw [hcy] at hy; simp at hy
    · rw [hx, hcy] at hsb
      exact key b i (by simpa using hbB) hsb
  · rcases hcx : c.x with a | i
    · rw [hcx] at hx; simp at hx
    · rw [hy, hcx] at hsb
      exact key b i (by simpa using hbB) hsb.symm

/-- The `O_dot` forms of a graph without labels have no labels. -/
private theorem SubstSPD_oDotT_labelFree {k n : ℕ} {Γ : Graph k n} (h : Γ.LabelFree) :
    ∀ t ∈ oDotT Γ, t.g.LabelFree := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact h
  · have hs := mergeT_spec hm
    have hd : (Γ.dotChoice Γ.splitPairs A).LabelFree := by
      intro c hc
      simp only [Graph.dotChoice, List.mem_append, List.mem_filter, List.mem_filterMap] at hc
      rcases hc with ⟨hc, -⟩ | ⟨p, -, hp⟩
      · exact h c hc
      · split_ifs at hp <;> simp only [Option.some.injEq] at hp <;>
          rw [← hp] <;> rfl
    intro c hc
    rw [hs.comps_eq, List.mem_filterMap] at hc
    obtain ⟨c₀, hc₀, hm₀⟩ := hc
    unfold mergeComp at hm₀
    split_ifs at hm₀ <;> simp only [Option.some.injEq] at hm₀ <;> rw [← hm₀] <;>
      simp [Comp.map, hd c₀ hc₀]

end Row2

private theorem SubstSPD_noGhost_of_tKinds {k n N : ℕ} {Γ : Graph k n} (h : Γ.TKinds N) :
    Γ.NoGhost := by
  intro c hc hk
  have := List.all_eq_true.1 h c hc
  simp [Comp.isTKind, hk] at this

private theorem SubstSPD_swap_pmBlock {n : ℕ} (g : Graph 3 n) :
    g.swapSolid.PMBlock ↔ g.PMBlock := by
  unfold Graph.PMBlock Graph.pmBlockB
  rw [SubstSPD_swap_blocks]

/-- **Row (2) of [II, Lemma 6.5]** in the block reading (the conjunct of [II, Lemma 6.5] on the
graphs of `R`, [II, Lemma 6.5 (1), (2)]): under the hypotheses of [II, Lemma 6.5], with the
hypotheses on `𝒯` of [II, Def 3.2] at order `n - 1` and of [II, Def 6.3], every `O_dot` form `t`
of the substitution of a graph of `R` is normal regular without dotted edges and without labels,
globally standard in the block reading, of scaling order `≥ ord G + 1`, where
`G = H.glue x y₁ y₂ (tVar true)`. -/
theorem globalGood_row2 :
  ∀ (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    3 ≤ n → (n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (∀ g ∈ 𝒯.R, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ t.g.LabelFree ∧ gsPM' t.g ∧
        ((H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord ∨
          (y₁ = y₂ ∧ t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord ∧
            t.g.solidN < (H.glue x y₁ y₂ (tVar true)).solidN))) := by
  intro n D 𝒯 m C H x y₁ y₂ _ ⟨_, hSh, hDef⟩ hL hN hd _ _ hI _ hgs _ _ hst g hg t ht
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  have hall : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, hTK, hAE, -⟩ := hSh.1.1 g (by simp [hg])
  obtain ⟨hgL, hRec, hk3, -⟩ := hSh.2.1 g hg
  obtain ⟨hggs, hE, hCI⟩ := hDef.1.1 g hg
  obtain ⟨hT, hX, hNL, hlab⟩ := hDef.2.1 g hall
  have h5 := hDef.2.2.2.1 g (by simp [hg])
  have hRg : g.2.swapSolid.RgCheck := by
    obtain ⟨c, hc, hk, hb⟩ := hRec
    refine Or.inr ⟨c, List.mem_map.2 ⟨c, hc, SubstSPD_swap_of_ns (by rw [hk]; rfl)⟩,
      Or.inl (by rw [hk]; rfl), ?_⟩
    rcases hb with ⟨⟨b, -, hx'⟩, hy'⟩ | ⟨⟨b, -, hy'⟩, hx'⟩
    · exact Or.inr ⟨by rw [hx']; rfl, hy'⟩
    · exact Or.inl ⟨hx', by rw [hy']; rfl⟩
  obtain ⟨hN', hd', hε, hε', -⟩ := glue_oDotT_normal m g.1 C C' H x y₁ y₂ g.2.swapSolid hx hy₁ hy₂
    hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hT)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) hRg (by rw [SubstSPD_swap_labels]; exact hlab)
    (SubstSPD_swap_noLabDot hNL) t ht
  have hgsP := (substGSB m g.1 H x y₁ y₂ g.2 hd hI hgs hst hggs hE hCI hT hAE
    (SubstSPD_noGhost_of_tKinds hTK) hX (SubstSPD_diagRecoll_of hRec)).2 C C' hN hgN t ht
  have hLF : (H.glue x y₁ y₂ g.2.swapSolid).LabelFree := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      simp [Comp.map, hL c₀ hc₀]
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      simp [Comp.map, SubstSPD_swap_labelFree hgL c₀ hc₀]
  refine ⟨hN', hd', SubstSPD_oDotT_labelFree hLF t ht, hgsP, Or.inl ?_⟩
  have e1 := glue_ord 3 m g.1 H x y₁ y₂ g.2.swapSolid
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  have e3 : g.2.swapSolid.ord = g.2.ord := (swapSolid_basic 3 g.1 g.2).2.1
  rw [SubstSPD_tVar_ord] at e2
  by_cases hε0 : y₁ = y₂ ∧ g.2.swapSolid.PMBlock
  · have := hε hε0
    have h5' := h5 ((SubstSPD_swap_pmBlock g.2).1 hε0.2)
    omega
  · have := hε' hε0
    omega

/-! ## The molecular graph of `G` with the edges of the `t`-variable re-ended -/

section KPrime

variable {V E : Type} [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
private theorem SubstSPD_mgext {G G' : MGraph V E} (h1 : G.int = G'.int) (h2 : G.ext = G'.ext)
    (h3 : ∀ e, G.ends e = G'.ends e) (h4 : ∀ e, G.cls e = G'.cls e) : G = G' := by
  cases G; cases G'; simp only at h1 h2 h3 h4; subst h1 h2
  simp only [MGraph.mk.injEq, true_and]
  exact ⟨funext h3, funext h4⟩

omit [DecidableEq E] in
/-- Two graphs with the same vertices and the same present edges up to their orientation are
names of each other. -/
private theorem SubstSPD_tr_orient {G G' : MGraph V E} (h1 : G.int = G'.int) (h2 : G.ext = G'.ext)
    (hc : ∀ e, G'.cls e = G.cls e)
    (he : ∀ e, G.cls e ≠ none → G'.ends e = G.ends e ∨
      G'.ends e = ((G.ends e).2, (G.ends e).1))
    (hv : ∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) :
    G.Transported G' := by
  refine ⟨id, id, fun _ _ _ _ h => h, Set.injOn_id _, by rw [Finset.image_id, h1],
    by rw [Finset.image_id, h2], hv, fun e _ => hc e, fun e h => ?_, fun e' h' => ?_⟩
  · rcases he e h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · by_contra hn
    exact h' e' (by rw [← hc]; exact hn) rfl

variable (K : MGraph V E) (b r : E) (u₀ u₁ u₂ : V)

/-- The edges `b` and `r` of `K` set to join `u₀`, `u₁` with class `cb` and `p`, `q` with the red
class. -/
private def SubstSPD_Kp (cb : MClass) (p q : V) : MGraph V E :=
  (K.setEdge b u₀ u₁ (some cb)).setEdge r p q (some .minus)

variable {K b r u₀ u₁ u₂}

omit [DecidableEq V] in
private theorem SubstSPD_Kp_cls {cb : MClass} {p q : V} (e : E) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).cls e =
      if e = r then some .minus else if e = b then some cb else K.cls e := by
  simp only [SubstSPD_Kp, MGraph.setEdge, Function.update]
  split_ifs <;> simp_all

omit [DecidableEq V] in
private theorem SubstSPD_Kp_ends {cb : MClass} {p q : V} (e : E) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).ends e =
      if e = r then (p, q) else if e = b then (u₀, u₁) else K.ends e := by
  simp only [SubstSPD_Kp, MGraph.setEdge]

/-- The re-ended graph `K'` is sequentially pre-deterministic: `b` is an internal blue solid edge
of `K` turned into a diffusive edge or kept (with its ends exchanged), or a loop added where `b`
is absent; `r` is red or absent and stays red. -/
private theorem SubstSPD_Kp_spd (hs : K.SPD) (hbr : b ≠ r) (hu₀ : u₀ ∈ K.int)
    (hu₁ : u₁ ∈ K.int)
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus) {cb : MClass}
    (hcb : cb = .plus ∨ cb = .diff) (p q : V)
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).SPD := by
  have h1 : (K.setEdge b u₀ u₁ (some cb)).SPD := by
    rcases hk3 with ⟨hb, rfl⟩ | ⟨hb, he, -⟩
    · have hl : ((K.setEdge b u₀ u₀ (some cb)).ends b).1 =
          ((K.setEdge b u₀ u₀ (some cb)).ends b).2 := by simp [MGraph.setEdge]
      rw [← MGraph.spd_unloop _ _ _ b hl]
      have : (K.setEdge b u₀ u₀ (some cb)).erase b = K.setEdge b u₀ u₀ none :=
        SubstSPD_mgext rfl rfl (fun _ => rfl) (fun e => by
          simp [MGraph.erase, MGraph.setEdge, Function.update])
      rw [this, MGraph.spd_red _ _ K b u₀ u₀ none (Or.inl hb) (Or.inl rfl)]
      exact hs
    · have hK : (K.recolor b (some cb)).SPD := by
        rcases hcb with rfl | rfl
        · have : K.recolor b (some .plus) = K := SubstSPD_mgext rfl rfl (fun _ => rfl)
            (fun e => by
              simp only [MGraph.recolor, Function.update]
              split_ifs with h
              · subst h; exact hb.symm
              · rfl)
          rw [this]; exact hs
        · refine MGraph.spd_conv _ _ K b ⟨hb, ?_, ?_⟩ hs <;> rw [he]
          exacts [hu₁, hu₀]
      refine (MGraph.spd_transport _ _ _ _ (K.recolor b (some cb)) (K.setEdge b u₀ u₁ (some cb))
        (SubstSPD_tr_orient rfl rfl (fun e => rfl) (fun e _ => ?_) (fun e he' => ?_))).2 hK
      · change (if e = b then (u₀, u₁) else K.ends e) = K.ends e ∨
          (if e = b then (u₀, u₁) else K.ends e) = ((K.ends e).2, (K.ends e).1)
        split_ifs with h
        · subst h; rw [he]; exact Or.inr rfl
        · exact Or.inl rfl
      · change Function.update K.cls b (some cb) e ≠ none at he'
        change K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2
        by_cases h : e = b
        · subst h; rw [he]; exact ⟨Or.inl hu₁, Or.inl hu₀⟩
        · rw [Function.update_of_ne h] at he'
          exact hv e he'
  have : (SubstSPD_Kp K b r u₀ u₁ cb p q).SPD ↔ (K.setEdge b u₀ u₁ (some cb)).SPD := by
    refine MGraph.spd_red _ _ _ r p q _ ?_ (Or.inr rfl)
    simp only [MGraph.setEdge, Function.update, hbr.symm, dite_false]
    exact hk4
  exact this.2 h1

omit [DecidableEq V] [DecidableEq E] in
private theorem SubstSPD_cut_swap {G G' : MGraph V E} {P : Finset V} {e e' : E}
    (h : G'.ends e' = ((G.ends e).2, (G.ends e).1)) (hc : G.Cut P e) : G'.Cut P e' := by
  unfold MGraph.Cut at hc ⊢
  rw [h]
  exact hc.symm.imp And.symm And.symm

omit [DecidableEq V] [DecidableEq E] in
/-- Two edges with the same crossing classes and the same ends up to orientation cross the same
sets. -/
private theorem SubstSPD_crosses_congr {G G' : MGraph V E} (h1 : G.int = G'.int)
    (h2 : G.ext = G'.ext) (P : Finset V) (e e' : E)
    (hcl : (G.cls e ≠ none ∧ G.cls e ≠ some .minus) ↔ (G'.cls e' ≠ none ∧ G'.cls e' ≠ some .minus))
    (hends : (G.cls e ≠ none ∧ G.cls e ≠ some .minus) → G'.ends e' = G.ends e ∨
      G'.ends e' = ((G.ends e).2, (G.ends e).1)) :
    G.Crosses P e ↔ G'.Crosses P e' := by
  have hv : ∀ v, G.IsVtx v ↔ G'.IsVtx v := fun v => by unfold MGraph.IsVtx; rw [h1, h2]
  constructor
  · rintro ⟨c1, c2, v1, v2, hc⟩
    obtain ⟨d1, d2⟩ := hcl.1 ⟨c1, c2⟩
    rcases hends ⟨c1, c2⟩ with h | h
    · refine ⟨d1, d2, ?_, ?_, ?_⟩
      · rw [h]; exact (hv _).1 v1
      · rw [h]; exact (hv _).1 v2
      · unfold MGraph.Cut at hc ⊢; rw [h]; exact hc
    · refine ⟨d1, d2, ?_, ?_, SubstSPD_cut_swap h hc⟩
      · rw [h]; exact (hv _).1 v2
      · rw [h]; exact (hv _).1 v1
  · rintro ⟨d1, d2, v1, v2, hc⟩
    obtain ⟨c1, c2⟩ := hcl.2 ⟨d1, d2⟩
    rcases hends ⟨c1, c2⟩ with h | h
    · refine ⟨c1, c2, ?_, ?_, ?_⟩
      · rw [h] at v1; exact (hv _).2 v1
      · rw [h] at v2; exact (hv _).2 v2
      · unfold MGraph.Cut at hc ⊢; rw [h] at hc; exact hc
    · refine ⟨c1, c2, ?_, ?_, ?_⟩
      · rw [h] at v2; exact (hv _).2 v2
      · rw [h] at v1; exact (hv _).2 v1
      · unfold MGraph.Cut at hc ⊢; rw [h] at hc; exact hc.symm.imp And.symm And.symm

section Edges

variable {cb : MClass} {p q : V}

omit [DecidableEq V]

private theorem SubstSPD_Kp_cls_r : (SubstSPD_Kp K b r u₀ u₁ cb p q).cls r = some .minus := by
  rw [SubstSPD_Kp_cls, ite_eq_left rfl]

private theorem SubstSPD_Kp_ends_r : (SubstSPD_Kp K b r u₀ u₁ cb p q).ends r = (p, q) := by
  rw [SubstSPD_Kp_ends, ite_eq_left rfl]

private theorem SubstSPD_Kp_cls_b (hbr : b ≠ r) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).cls b = some cb := by
  rw [SubstSPD_Kp_cls, ite_eq_right hbr, ite_eq_left rfl]

private theorem SubstSPD_Kp_ends_b (hbr : b ≠ r) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).ends b = (u₀, u₁) := by
  rw [SubstSPD_Kp_ends, ite_eq_right hbr, ite_eq_left rfl]

private theorem SubstSPD_Kp_cls_o {e : E} (her : e ≠ r) (heb : e ≠ b) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).cls e = K.cls e := by
  rw [SubstSPD_Kp_cls, ite_eq_right her, ite_eq_right heb]

private theorem SubstSPD_Kp_ends_o {e : E} (her : e ≠ r) (heb : e ≠ b) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).ends e = K.ends e := by
  rw [SubstSPD_Kp_ends, ite_eq_right her, ite_eq_right heb]

end Edges

omit [DecidableEq V] in
/-- The edges crossing a set of vertices of `K'` are those of `K` when `b` joins `u₀` to `u₁` in
`K` or is absent with `u₀ = u₁`. -/
private theorem SubstSPD_Kp_crosses {cb : MClass} (hcb : cb = .plus ∨ cb = .diff) (hbr : b ≠ r)
    {p q : V}
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀)))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus) (P : Finset V) (e : E) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).Crosses P e ↔ K.Crosses P e := by
  have hcb' : (some cb : Option MClass) ≠ none ∧ (some cb : Option MClass) ≠ some .minus := by
    rcases hcb with rfl | rfl <;> simp
  by_cases her : e = r
  · rw [her]
    refine (SubstSPD_crosses_congr (G := K) (G' := SubstSPD_Kp K b r u₀ u₁ cb p q) rfl rfl P r r
      ?_ ?_).symm
    · rw [SubstSPD_Kp_cls_r]
      rcases hk4 with h | h <;> simp [h]
    · intro h; rcases hk4 with h' | h' <;> rw [h'] at h <;> simp at h
  · by_cases heb : e = b
    · rw [heb]
      rcases hk3 with ⟨h, rfl⟩ | ⟨h, he⟩
      · constructor
        · rintro ⟨-, -, -, -, hc⟩
          unfold MGraph.Cut at hc
          rw [SubstSPD_Kp_ends_b hbr] at hc
          simp only at hc
          tauto
        · rintro ⟨hc, -⟩
          exact absurd h hc
      · refine (SubstSPD_crosses_congr (G := K) (G' := SubstSPD_Kp K b r u₀ u₁ cb p q) rfl rfl P
          b b ?_ ?_).symm
        · rw [SubstSPD_Kp_cls_b hbr, h]
          simpa using hcb'
        · intro _
          rw [SubstSPD_Kp_ends_b hbr, he]
          exact Or.inr rfl
    · refine SubstSPD_crosses_congr (G := SubstSPD_Kp K b r u₀ u₁ cb p q) (G' := K) rfl rfl P e e
        ?_ ?_
      · rw [SubstSPD_Kp_cls_o her heb]
      · intro _
        rw [SubstSPD_Kp_ends_o her heb]
        exact Or.inl rfl

/-- `K'` is globally standard when `K` is: the isolated subsets are those of `K`, each contains
`u₀` and `u₁`, and the red solid edge `r` crosses them exactly when it does in `K`. -/
private theorem SubstSPD_Kp_gs (hgs : K.GloballyStandard) (hbr : b ≠ r) (hu₀ : u₀ ∈ K.int)
    (hu₁ : u₁ ∈ K.int) (hu₂ : u₂ ∈ K.int) (hm₀ : u₀ ∈ K.MIS) (hm₁ : u₁ ∈ K.MIS)
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus)
    (hr : K.ends r = (u₂, u₀) ∧ (K.cls r = some .minus ∨ u₂ = u₀)) {cb : MClass}
    (hcb : cb = .plus ∨ cb = .diff) {p q : V}
    (hpq : (p = u₂ ∧ (q = u₀ ∨ q = u₁)) ∨ (q = u₂ ∧ (p = u₀ ∨ p = u₁)))
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).GloballyStandard := by
  have hk3' : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀)) := by
    rcases hk3 with h | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hcr := SubstSPD_Kp_crosses (p := p) (q := q) hcb hbr hk3' hk4
  have hpi : ∀ P, (SubstSPD_Kp K b r u₀ u₁ cb p q).IsProperIso
      (SubstSPD_Kp K b r u₀ u₁ cb p q).int P ↔ K.IsProperIso K.int P := by
    intro P
    unfold MGraph.IsProperIso MGraph.IsIsolated
    simp only [hcr]
    rfl
  have hmis : ∀ P, K.IsProperIso K.int P → u₀ ∈ P ∧ u₁ ∈ P := by
    intro P hP
    simp only [MGraph.MIS, Finset.mem_filter] at hm₀ hm₁
    exact ⟨hm₀.2 P hP, hm₁.2 P hP⟩
  refine ⟨SubstSPD_Kp_spd hgs.1 hbr hu₀ hu₁ hk3 hk4 hcb p q hv, fun P hP => ?_⟩
  have hP := (hpi P).1 hP
  obtain ⟨hP0, hP1⟩ := hmis P hP
  obtain ⟨-, e, e', hee, he, he'⟩ := hgs.2 P hP
  have hred : ∀ e, K.RedCrosses P e → (SubstSPD_Kp K b r u₀ u₁ cb p q).RedCrosses P e := by
    rintro e ⟨hm, h1, h2, hc⟩
    by_cases her : e = r
    · rw [her] at hc ⊢
      have hu₂P : u₂ ∉ P := by
        unfold MGraph.Cut at hc
        rw [hr.1] at hc
        rcases hc with ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd hP0 h
        · exact h
      have hpP : p ∈ P ∨ q ∈ P := by
        rcases hpq with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> rw [h]
        exacts [Or.inr hP0, Or.inr hP1, Or.inl hP0, Or.inl hP1]
      refine ⟨SubstSPD_Kp_cls_r, ?_, ?_, ?_⟩ <;> (try unfold MGraph.Cut) <;>
        rw [SubstSPD_Kp_ends_r]
      · rcases hpq with ⟨rfl, -⟩ | ⟨-, rfl | rfl⟩
        exacts [Or.inl hu₂, Or.inl hu₀, Or.inl hu₁]
      · rcases hpq with ⟨-, rfl | rfl⟩ | ⟨rfl, -⟩
        exacts [Or.inl hu₀, Or.inl hu₁, Or.inl hu₂]
      · rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Or.inr ⟨hu₂P, hpP.resolve_left hu₂P⟩
        · exact Or.inl ⟨hpP.resolve_right hu₂P, hu₂P⟩
    · by_cases heb : e = b
      · rw [heb] at hm
        rcases hk3' with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hm <;> simp at hm
      · refine ⟨by rw [SubstSPD_Kp_cls_o her heb]; exact hm, ?_, ?_, ?_⟩
        · rw [SubstSPD_Kp_ends_o her heb]; exact h1
        · rw [SubstSPD_Kp_ends_o her heb]; exact h2
        · unfold MGraph.Cut at hc ⊢; rw [SubstSPD_Kp_ends_o her heb]; exact hc
  exact ⟨(hpi P).2 hP |>.1, e, e', hee, hred e he, hred e' he'⟩

end KPrime

/-! ## Merging molecules after a first identification -/

section Pipe

variable {V E : Type} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
/-- Mapping the vertices by `π`, or first by `ρ` and then by `ρ ∘ π`, gives the same graph up to
names, when `π ∘ ρ = π` and `π` is idempotent. -/
private theorem SubstSPD_tr_rho (Gl : MGraph V E) (π ρ : V → V) (hidem : ∀ v, π (π v) = π v)
    (hρπ : ∀ z, π (ρ z) = π z)
    (hR2 : ∀ e, Gl.cls e ≠ none → Gl.IsVtx (Gl.ends e).1 ∧ Gl.IsVtx (Gl.ends e).2) :
    ((Gl.mapV π).unloop).Transported (((Gl.mapV ρ).mapV (ρ ∘ π)).unloop) := by
  have hinj : ∀ a b, π a = a → π b = b → ρ a = ρ b → a = b := by
    intro a b ha hb h
    rw [← ha, ← hb, ← hρπ a, ← hρπ b, h]
  have hfix : ∀ v ∈ (↑((Gl.mapV π).unloop).int ∪ ↑((Gl.mapV π).unloop).ext : Set V),
      π v = v := by
    intro v hv
    simp only [MGraph.unloop, MGraph.mapV, Set.mem_union, Finset.mem_coe,
      Finset.mem_image] at hv
    rcases hv with ⟨w, -, rfl⟩ | ⟨w, -, rfl⟩ <;> exact hidem w
  have hcl : ∀ e, (((Gl.mapV ρ).mapV (ρ ∘ π)).unloop).cls e = ((Gl.mapV π).unloop).cls e := by
    intro e
    change (if ρ (π (ρ (Gl.ends e).1)) = ρ (π (ρ (Gl.ends e).2)) then none else Gl.cls e) =
      (if π (Gl.ends e).1 = π (Gl.ends e).2 then none else Gl.cls e)
    rw [hρπ, hρπ]
    congr 1
    exact propext ⟨hinj _ _ (hidem _) (hidem _), fun h => by rw [h]⟩
  refine ⟨ρ, id, fun _ _ _ _ h => h, fun a ha b hb h => hinj a b (hfix a ha) (hfix b hb) h,
    ?_, ?_, fun e he => ?_, fun e _ => hcl e, fun e _ => ?_, fun e' he' => ?_⟩
  · simp only [MGraph.unloop, MGraph.mapV, Finset.image_image]
    exact Finset.image_congr fun v _ => by simp [hρπ]
  · simp only [MGraph.unloop, MGraph.mapV, Finset.image_image]
    exact Finset.image_congr fun v _ => by simp [hρπ]
  · have he' : Gl.cls e ≠ none := by
      intro h; apply he
      change (if _ then none else Gl.cls e) = none
      rw [h]; split_ifs <;> rfl
    obtain ⟨h1, h2⟩ := hR2 e he'
    have key : ∀ v, Gl.IsVtx v → ((Gl.mapV π).unloop).IsVtx (π v) := by
      rintro v (hv | hv)
      · exact Or.inl (Finset.mem_image_of_mem _ hv)
      · exact Or.inr (Finset.mem_image_of_mem _ hv)
    exact ⟨key _ h1, key _ h2⟩
  · left
    change (ρ (π (ρ (Gl.ends e).1)), ρ (π (ρ (Gl.ends e).2))) =
      (ρ (π (Gl.ends e).1), ρ (π (Gl.ends e).2))
    rw [hρπ, hρπ]
  · by_contra hn
    exact he' e' (by rw [← hcl]; exact hn) rfl

/-- **The molecular graph of a substituted graph from a re-ended host graph.** Let `π` be as in
`toMG'_glue` for the inserted graph `Gl`, let `ρ` identify some vertices of `Gl` that `π`
identifies, and let `Gl` with its vertices mapped by `ρ` be a renaming of a graph `K'`. If `K'` is
sequentially pre-deterministic, resp. globally standard, so is `Gl` with its vertices mapped by
`π` and its loops removed. -/
private theorem SubstSPD_pipe {V' E' : Type} [DecidableEq V'] [DecidableEq E'] [Finite E]
    (Gl : MGraph V E) (π ρ : V → V) (hidem : ∀ v, π (π v) = π v)
    (hint : ∀ v ∈ Gl.int, π v ∈ Gl.int) (hext : ∀ v ∈ Gl.ext, π v = v)
    (hnie : ∀ v ∈ Gl.int, π v ∉ Gl.ext) (hdis : Disjoint Gl.int Gl.ext)
    (hR2 : ∀ e, Gl.cls e ≠ none → Gl.IsVtx (Gl.ends e).1 ∧ Gl.IsVtx (Gl.ends e).2)
    (hng : ∀ e, Gl.cls e ≠ some .ghost) (hρπ : ∀ z, π (ρ z) = π z)
    (hρint : ∀ z ∈ Gl.int, ρ z ∈ Gl.int) (hρext : ∀ z ∈ Gl.ext, ρ z = z)
    (K' : MGraph V' E') (htr : K'.Transported (Gl.mapV ρ)) :
    (K'.SPD → ((Gl.mapV π).unloop).SPD) ∧
      (K'.GloballyStandard → ((Gl.mapV π).unloop).GloballyStandard) := by
  have tr := SubstSPD_tr_rho Gl π ρ hidem hρπ hR2
  have hidem₁ : ∀ v, (ρ ∘ π) ((ρ ∘ π) v) = (ρ ∘ π) v := by
    intro v; simp only [Function.comp, hρπ, hidem]
  have hint₁ : ∀ v ∈ (Gl.mapV ρ).int, (ρ ∘ π) v ∈ (Gl.mapV ρ).int := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    simp only [Function.comp, hρπ]
    exact Finset.mem_image_of_mem _ (hint w hw)
  have hext₁ : ∀ v ∈ (Gl.mapV ρ).ext, (ρ ∘ π) v = v := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    simp only [Function.comp, hext w hw, hρext w hw]
  have hnie₁ : ∀ v ∈ (Gl.mapV ρ).int, (ρ ∘ π) v ∉ (Gl.mapV ρ).ext := by
    intro v hv hv'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨w', hw', he⟩ := Finset.mem_image.1 hv'
    simp only [Function.comp, hρπ] at he
    rw [hρext w' hw'] at he
    have : π w = w' := by
      calc π w = π (π w) := (hidem w).symm
        _ = π (ρ (π w)) := (hρπ _).symm
        _ = π w' := by rw [he]
        _ = w' := hext w' hw'
    exact hnie w hw (this ▸ hw')
  have hdis₁ : Disjoint (Gl.mapV ρ).int (Gl.mapV ρ).ext := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨w', hw', he⟩ := Finset.mem_image.1 hv'
    rw [hρext w' hw'] at he
    exact Finset.disjoint_left.1 hdis (hρint w hw) (he ▸ hw')
  have hR2₁ : ∀ e, (Gl.mapV ρ).cls e ≠ none →
      (Gl.mapV ρ).IsVtx ((Gl.mapV ρ).ends e).1 ∧ (Gl.mapV ρ).IsVtx ((Gl.mapV ρ).ends e).2 := by
    intro e he
    obtain ⟨h1, h2⟩ := hR2 e he
    have key : ∀ v, Gl.IsVtx v → (Gl.mapV ρ).IsVtx (ρ v) := by
      rintro v (hv | hv)
      · exact Or.inl (Finset.mem_image_of_mem _ hv)
      · exact Or.inr (Finset.mem_image_of_mem _ hv)
    exact ⟨key _ h1, key _ h2⟩
  refine ⟨fun hs => ?_, fun hg => ?_⟩
  · have h1 : (Gl.mapV ρ).SPD := (MGraph.spd_transport _ _ _ _ _ _ htr).2 hs
    have h2 := MGraph.spd_mapV_merge _ _ (Gl.mapV ρ) (ρ ∘ π) hidem₁ hint₁ hext₁ hnie₁ h1 hng hdis₁
      hR2₁
    exact (MGraph.spd_transport _ _ _ _ _ _ tr).1 h2
  · have h1 : (Gl.mapV ρ).GloballyStandard := (SubstMol_gs_transport htr).2 hg
    have h2 := MGraph.gs_mapV_merge _ _ (Gl.mapV ρ) (ρ ∘ π) hidem₁ hint₁ hext₁ hnie₁ h1.1 hng
      hdis₁ hR2₁ (fun P hP _ => h1.2 P hP)
    exact (SubstMol_gs_transport tr).1 h2

end Pipe

/-! ## The inserted graph as a renaming of the re-ended host graph -/

section GlueTr

variable {V W E F : Type} [DecidableEq V] [DecidableEq W] [DecidableEq E]

/-- When the edges of `L` other than `fb` and `fr` are absent and `ρ` sends the internal vertices
of `L` to internal vertices of `K`, the graph `L` inserted into `K` (with `b`, `r` removed) and
mapped by `ρ` is the re-ended graph `K'`, up to names: `fb` takes the place of `b` and `fr` that
of `r`. -/
private theorem SubstSPD_glue_tr (K : MGraph V E) (L : MGraph W F) (σ : W → V) (b r : E)
    (hbr : b ≠ r) (ρ : V ⊕ W → V ⊕ W) (hρ : ∀ v, ρ (.inl v) = .inl v)
    (hρL : ∀ w ∈ L.int, ∃ v ∈ K.int, ρ (.inr w) = .inl v) (u₀ u₁ p q : V) (cb : MClass)
    (hu₀ : u₀ ∈ K.int) (hu₁ : u₁ ∈ K.int) (hp : p ∈ K.int) (hq : q ∈ K.int)
    (fb fr : F) (hfbr : fb ≠ fr) (hcb : L.cls fb = some cb)
    (heb : ((K.insert L σ {b, r}).mapV ρ).ends (.inr fb) = (.inl u₀, .inl u₁) ∨
      ((K.insert L σ {b, r}).mapV ρ).ends (.inr fb) = (.inl u₁, .inl u₀))
    (hcr : L.cls fr = some .minus)
    (her : ((K.insert L σ {b, r}).mapV ρ).ends (.inr fr) = (.inl p, .inl q) ∨
      ((K.insert L σ {b, r}).mapV ρ).ends (.inr fr) = (.inl q, .inl p))
    (hoth : ∀ f, f ≠ fb → f ≠ fr → L.cls f = none)
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2) :
    (SubstSPD_Kp K b r u₀ u₁ cb p q).Transported ((K.insert L σ {b, r}).mapV ρ) := by
  set Gl := (K.insert L σ {b, r}).mapV ρ with hGl
  have hcl : ∀ e, Gl.cls (.inl e) = if e ∈ ({b, r} : Finset E) then none else K.cls e :=
    fun e => rfl
  have hen : ∀ e, Gl.ends (.inl e) = (.inl (K.ends e).1, .inl (K.ends e).2) := by
    intro e
    change (ρ (.inl (K.ends e).1), ρ (.inl (K.ends e).2)) = _
    rw [hρ, hρ]
  have hcf : ∀ f, Gl.cls (.inr f) = L.cls f := fun f => rfl
  let g : E → E ⊕ F := fun e => if e = b then .inr fb else if e = r then .inr fr else .inl e
  have hgb : g b = .inr fb := by simp [g]
  have hgr : g r = .inr fr := by simp [g, hbr.symm]
  have hgo : ∀ e, e ≠ b → e ≠ r → g e = .inl e := fun e h1 h2 => by simp [g, h1, h2]
  have hginj : Function.Injective g := by
    intro e₁ e₂ h
    by_cases h1 : e₁ = b <;> by_cases h2 : e₂ = b <;> by_cases h3 : e₁ = r <;>
      by_cases h4 : e₂ = r <;> simp_all [g, hfbr.symm]
  refine ⟨Sum.inl, g, fun e₁ e₂ _ _ h => hginj h, Sum.inl_injective.injOn, ?_, ?_,
    fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · ext z
    simp only [hGl, MGraph.mapV, MGraph.insert, SubstSPD_Kp, MGraph.setEdge, Finset.mem_image,
      Finset.mem_disjSum]
    constructor
    · rintro ⟨w, (⟨v, hv', rfl⟩ | ⟨w', hw', rfl⟩), rfl⟩
      · exact ⟨v, hv', (hρ v).symm⟩
      · obtain ⟨v, hv', he⟩ := hρL w' hw'
        exact ⟨v, hv', he.symm⟩
    · rintro ⟨v, hv', rfl⟩
      exact ⟨.inl v, Or.inl ⟨v, hv', rfl⟩, hρ v⟩
  · ext z
    simp only [hGl, MGraph.mapV, MGraph.insert, SubstSPD_Kp, MGraph.setEdge, Finset.mem_image,
      Finset.mem_map, Function.Embedding.inl_apply]
    constructor
    · rintro ⟨w, ⟨v, hv', rfl⟩, rfl⟩
      exact ⟨v, hv', (hρ v).symm⟩
    · rintro ⟨v, hv', rfl⟩
      exact ⟨.inl v, ⟨v, hv', rfl⟩, hρ v⟩
  · rw [SubstSPD_Kp_cls] at he
    rw [SubstSPD_Kp_ends]
    split_ifs with h1 h2
    · exact ⟨Or.inl hp, Or.inl hq⟩
    · exact ⟨Or.inl hu₀, Or.inl hu₁⟩
    · rw [ite_eq_right h1, ite_eq_right h2] at he
      exact hv e he
  · by_cases h1 : e = r
    · subst h1; rw [hgr, hcf, hcr, SubstSPD_Kp_cls_r]
    · by_cases h2 : e = b
      · subst h2; rw [hgb, hcf, hcb, SubstSPD_Kp_cls_b hbr]
      · rw [hgo e h2 h1, hcl, SubstSPD_Kp_cls_o h1 h2, ite_eq_right (by simp [h1, h2])]
  · by_cases h1 : e = r
    · subst h1; rw [hgr, SubstSPD_Kp_ends_r]; exact her
    · by_cases h2 : e = b
      · subst h2; rw [hgb, SubstSPD_Kp_ends_b hbr]; exact heb
      · rw [hgo e h2 h1, hen, SubstSPD_Kp_ends_o h1 h2]; exact Or.inl rfl
  · rcases e' with e | f
    · by_cases h1 : e = b ∨ e = r
      · rw [hcl, ite_eq_left (by simpa using h1)]
      · push Not at h1
        rw [hcl, ite_eq_right (by simp [h1.1, h1.2])]
        by_contra hn
        exact he' e (by rw [SubstSPD_Kp_cls_o h1.2 h1.1]; exact hn) (hgo e h1.1 h1.2)
    · by_cases h1 : f = fb
      · subst h1
        exact absurd hgb (he' b (by rw [SubstSPD_Kp_cls_b hbr]; simp))
      · by_cases h2 : f = fr
        · subst h2
          exact absurd hgr (he' r (by rw [SubstSPD_Kp_cls_r]; simp))
        · rw [hcf]; exact hoth f h1 h2

end GlueTr

/-! ## The leading term and the terms of `Σ_T`: the molecular graph -/

section LeadGs

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

/-- The graph `Θ^{[o]}_{⊗⊕} Ḡ_{⊖⊕}` followed by the dotted and `×`-dotted edges `extra`: the
graph `m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` of `leadExp` and `sigmaTExp` with its solid edge reversed,
and the terms of its `O_dot` expansion. -/
private def SubstSPD_lg (o : List ℕ) (extra : List (Comp (Atom 3 0))) (c : Coeff) : Graph 3 0 :=
  ⟨[mkC (.theta o) (.inl 0) (.inl 1), mkC (.G .minus) (.inl 2) (.inl 1)] ++ extra, c⟩

private theorem SubstSPD_lg_len (o : List ℕ) (extra : List (Comp (Atom 3 0))) (c : Coeff) :
    (SubstSPD_lg o extra c).comps.length = extra.length + 2 := by
  simp only [SubstSPD_lg, List.length_append, List.length_cons, List.length_nil]; omega

/-- The edges of the molecular graph of `SubstSPD_lg`: the diffusive edge `⊗ ⊕`, the red solid
edge `⊖ ⊕`, and no other present edge. -/
private theorem SubstSPD_lg_edges (o : List ℕ) (extra : List (Comp (Atom 3 0))) (c : Coeff)
    (hex : ∀ d ∈ extra, d.kind = .dot ∨ d.kind = .xdot) :
    let g := SubstSPD_lg o extra c
    ∃ fb fr : Fin g.comps.length ⊕ Fin 3, fb ≠ fr ∧ g.toMG'.cls fb = some .diff ∧
      g.toMG'.ends fb = (.inl 0, .inl 1) ∧ g.toMG'.cls fr = some .minus ∧
      g.toMG'.ends fr = (.inl 2, .inl 1) ∧ (∀ f, f ≠ fb → f ≠ fr → g.toMG'.cls f = none) ∧
      g.toMG'.int = ∅ := by
  intro g
  have hlen := SubstSPD_lg_len o extra c
  have hanc : ∀ a : Fin 3, g.Unpinned (.inl a) := fun a => ⟨rfl, fun b => b.elim0⟩
  have hfl : ∀ a : Fin 3, g.molRep (g.flatAtom (.inl a)) = .inl a := by
    intro a; rw [SubstSPD_flat_unpinned g (hanc a)]; rfl
  have h0 : 0 < g.comps.length := by simp only [g]; rw [hlen]; omega
  have h1 : 1 < g.comps.length := by simp only [g]; rw [hlen]; omega
  have hk0 : g.comps[(⟨0, h0⟩ : Fin g.comps.length)] = mkC (.theta o) (.inl 0) (.inl 1) := rfl
  have hk1 : g.comps[(⟨1, h1⟩ : Fin g.comps.length)] = mkC (.G .minus) (.inl 2) (.inl 1) := rfl
  have hd0 : g.comps[(⟨0, h0⟩ : Fin g.comps.length)].kind ≠ .dot := by rw [hk0]; simp [mkC]
  have hd1 : g.comps[(⟨1, h1⟩ : Fin g.comps.length)].kind ≠ .dot := by rw [hk1]; simp [mkC]
  refine ⟨.inl ⟨0, h0⟩, .inl ⟨1, h1⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SubstSPD_cls_inl g _ hd0, hk0]
    simp only [mkC, hfl]
    rfl
  · rw [SubstSPD_ends_inl g _ hd0, hk0]
    simp only [mkC, hfl]
  · rw [SubstSPD_cls_inl g _ hd1, hk1]
    simp only [mkC, hfl]
    rfl
  · rw [SubstSPD_ends_inl g _ hd1, hk1]
    simp only [mkC, hfl]
  · rintro (i | a) hb hr
    · have hi : 2 ≤ i.val := by
        by_contra h
        have : i.val = 0 ∨ i.val = 1 := by omega
        rcases this with hv | hv
        · exact hb (by rw [Sum.inl.injEq]; exact Fin.ext hv)
        · exact hr (by rw [Sum.inl.injEq]; exact Fin.ext hv)
      have hd : g.comps[i] ∈ extra := by
        have hi' : i.val - 2 < extra.length := by have := i.2; simp only [g] at this; omega
        have : g.comps[i.val] = extra[i.val - 2] := by
          change ([mkC (.theta o) (.inl 0) (.inl 1), mkC (.G .minus) (.inl 2) (.inl 1)] ++
            extra)[i.val] = _
          rw [List.getElem_append_right (by simp; omega)]
          simp
        rw [Fin.getElem_fin, this]; exact List.getElem_mem _
      rcases hex _ hd with h | h
      · exact SubstSPD_cls_dot g i h
      · rw [SubstSPD_cls_inl g i (by rw [h]; decide), h]
        split_ifs <;> rfl
    · exact SubstSPD_pin_unpinned g (hanc a)
  · simp [g, Graph.toMG']

/-- **`gsPM'` of `H` times `Θ^{[o]}_{⊗⊕} Ḡ_{⊖⊕}` (with dotted or `×`-dotted edges added)**: the
inserted graph is the molecular graph of `G` with `G_{y₁α}` turned into the diffusive edge
`Θ_{xy₁}` and `Ḡ_{y₂α}` into `Ḡ_{y₂y₁}`. -/
private theorem SubstSPD_lg_gs (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hGs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (o : List ℕ) (extra : List (Comp (Atom 3 0))) (c : Coeff)
    (hex : ∀ d ∈ extra, d.kind = .dot ∨ d.kind = .xdot) :
    gsPM' (H.glue x y₁ y₂ (SubstSPD_lg o extra c)) := by
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨π, hidem, hint, hext, hnie, hdis, hR2, -, ht⟩ :=
    toMG'_glue m 0 H x y₁ y₂ (SubstSPD_lg o extra c) hD hx hy₁ hy₂
  obtain ⟨hK1, hK2, hK3, hu₀, hu₁, hu₂, hm₀, hm₁, hk3, hk4, hk5, hr⟩ :=
    SubstSPD_host H x y₁ y₂ hx hy₁ hy₂ hD hI hst
  obtain ⟨fb, fr, hfbr, hcb, heb, hcr, her, hoth, hLint⟩ := SubstSPD_lg_edges o extra c hex
  set K := (H.glue x y₁ y₂ (tVar true)).toMG' with hK
  set L := (SubstSPD_lg o extra c).toMG' with hL
  set σ : Atom 3 0 → Atom 3 (m + 1) :=
    Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x) with hσ
  have hbr : (Sum.inl (SubstSPD_bI H x y₁ y₂) : Fin (H.glue x y₁ y₂ (tVar true)).comps.length ⊕
      Fin 3) ≠ .inl (SubstSPD_rI H x y₁ y₂) := by
    simp [SubstSPD_bI, SubstSPD_rI]
  have hτ : ∀ w : Atom 3 0, (if w ∈ L.int then (.inr w : Atom 3 (m + 1) ⊕ Atom 3 0)
      else .inl (σ w)) = .inl (σ w) := by
    intro w; rw [hLint]; simp
  have heb' : ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).mapV
      id).ends (.inr fb) = (.inl (σ (.inl 0)), .inl (σ (.inl 1))) := by
    change (id (if (L.ends fb).1 ∈ L.int then (.inr (L.ends fb).1 : Atom 3 (m + 1) ⊕ Atom 3 0)
      else .inl (σ (L.ends fb).1)), id (if (L.ends fb).2 ∈ L.int then
        (.inr (L.ends fb).2 : Atom 3 (m + 1) ⊕ Atom 3 0) else .inl (σ (L.ends fb).2))) = _
    rw [heb]; simp only [id, hτ]
  have her' : ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)}).mapV
      id).ends (.inr fr) = (.inl (σ (.inl 2)), .inl (σ (.inl 1))) := by
    change (id (if (L.ends fr).1 ∈ L.int then (.inr (L.ends fr).1 : Atom 3 (m + 1) ⊕ Atom 3 0)
      else .inl (σ (L.ends fr).1)), id (if (L.ends fr).2 ∈ L.int then
        (.inr (L.ends fr).2 : Atom 3 (m + 1) ⊕ Atom 3 0) else .inl (σ (L.ends fr).2))) = _
    rw [her]; simp only [id, hτ]
  have htr := SubstSPD_glue_tr K L σ _ _ hbr id (fun _ => rfl)
    (fun w hw => by rw [hLint] at hw; simp at hw) _ _ _ _ .diff hu₀ hu₁ hu₂ hu₁ fb fr hfbr hcb
    (Or.inl heb') hcr (Or.inl her') hoth (fun e _ => MolInsert_toMG'_ends_vtx 3 _ _ e)
  have hng := SubstSPD_insert_noGhost (K := K) (L := L) σ
    {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)} hK2 (fun f => by
      by_cases h : f = fb
      · rw [h, hcb]; simp
      · by_cases h' : f = fr
        · rw [h', hcr]; simp
        · rw [hoth _ h h']; simp)
  have hKp := SubstSPD_Kp_gs hGs hbr hu₀ hu₁ hu₂ hm₀ hm₁ hk3 hk4 hr (Or.inr rfl)
    (Or.inl ⟨rfl, Or.inr rfl⟩) (fun e _ => MolInsert_toMG'_ends_vtx 3 _ _ e)
  have hgs := (SubstSPD_pipe _ π id hidem hint hext hnie hdis hR2 hng (fun _ => rfl)
    (fun z hz => hz) (fun _ _ => rfl) _ htr).2 hKp
  exact (SubstMol_gs_transport ht).2 hgs

end LeadGs

/-! ## The recollision terms: the molecular graph -/

section TcGs

/-- The molecular graph of the block reading depends only on the components. -/
private theorem SubstSPD_toMG'_coeff {k n : ℕ} (cs : List (Comp (Atom k n))) (c₁ c₂ : Coeff) :
    (⟨cs, c₁⟩ : Graph k n).toMG' = (⟨cs, c₂⟩ : Graph k n).toMG' := by
  have hm : (⟨cs, c₁⟩ : Graph k n).molRep = (⟨cs, c₂⟩ : Graph k n).molRep := by
    funext u
    rcases u with a | a
    · rfl
    · simp only [Graph.molRep]
      congr 3
  have ha : (⟨cs, c₁⟩ : Graph k n).anchor = (⟨cs, c₂⟩ : Graph k n).anchor := by
    funext u
    unfold Graph.anchor
    congr 1
  have hf : (⟨cs, c₁⟩ : Graph k n).flatComp = (⟨cs, c₂⟩ : Graph k n).flatComp := by
    funext c
    unfold Graph.flatComp Graph.flatAtom
    rw [ha]
  refine SubstSPD_mgext ?_ rfl (fun e => ?_) (fun e => ?_)
  · simp only [Graph.toMG', hm]
  · rcases e with i | a
    · change ((⟨cs, c₁⟩ : Graph k n).molRep _, (⟨cs, c₁⟩ : Graph k n).molRep _) =
        ((⟨cs, c₂⟩ : Graph k n).molRep _, (⟨cs, c₂⟩ : Graph k n).molRep _)
      rw [hm, hf]
    · simp only [Graph.toMG', ha, hm]
  · rcases e with i | a
    · change (if _ ∨ (⟨cs, c₁⟩ : Graph k n).molRep _ = (⟨cs, c₁⟩ : Graph k n).molRep _ then none
        else _) = (if _ ∨ (⟨cs, c₂⟩ : Graph k n).molRep _ = (⟨cs, c₂⟩ : Graph k n).molRep _
          then none else _)
      simp only [hm, hf]
    · simp only [Graph.toMG', ha]

private theorem SubstSPD_gs_comps {k n : ℕ} {Γ₁ Γ₂ : Graph k n} (h : Γ₁.comps = Γ₂.comps) :
    gsPM' Γ₁ ↔ gsPM' Γ₂ := by
  obtain ⟨c₁, k₁⟩ := Γ₁
  obtain ⟨c₂, k₂⟩ := Γ₂
  simp only at h
  subst h
  unfold gsPM'
  rw [SubstSPD_toMG'_coeff c₁ k₁ k₂]

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

/-- **`gsPM'` of `H` times a recollision term**: a graph `g` with one internal atom `a`, joined
to `⊗` by a waved edge, whose molecular graph has exactly two present edges, a blue one between
`a` and `⊕` and a red one between `a` and `⊖`. The inserted graph, with `a` identified with the
molecule of `x`, is the molecular graph of `G` with `G_{y₁α}` and `Ḡ_{y₂α}` re-ended at that
molecule. -/
private theorem SubstSPD_tc_gs (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hGs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (g : Graph 3 1) (hs : mkC (.waved .s) (.inl 0) (.inr 0) ∈ g.comps)
    (hLint : g.toMG'.int = {.inr 0}) (fb fr : Fin g.comps.length ⊕ Fin 3) (hfbr : fb ≠ fr)
    (hcb : g.toMG'.cls fb = some .plus)
    (heb : g.toMG'.ends fb = (.inr 0, .inl 1) ∨ g.toMG'.ends fb = (.inl 1, .inr 0))
    (hcr : g.toMG'.cls fr = some .minus)
    (her : g.toMG'.ends fr = (.inr 0, .inl 2) ∨ g.toMG'.ends fr = (.inl 2, .inr 0))
    (hoth : ∀ f, f ≠ fb → f ≠ fr → g.toMG'.cls f = none) :
    gsPM' (H.glue x y₁ y₂ g) := by
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨π, hidem, hint, hext, hnie, hdis, hR2, hmol, ht⟩ :=
    toMG'_glue m 1 H x y₁ y₂ g hD hx hy₁ hy₂
  obtain ⟨hK1, hK2, hK3, hu₀, hu₁, hu₂, hm₀, hm₁, hk3, hk4, hk5, hr⟩ :=
    SubstSPD_host H x y₁ y₂ hx hy₁ hy₂ hD hI hst
  set K := (H.glue x y₁ y₂ (tVar true)).toMG' with hK
  set L := g.toMG' with hL
  set u₀ := (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x) with hu₀d
  set σ : Atom 3 1 → Atom 3 (m + 1) :=
    Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => u₀ with hσ
  have hbr : (Sum.inl (SubstSPD_bI H x y₁ y₂) : Fin (H.glue x y₁ y₂ (tVar true)).comps.length ⊕
      Fin 3) ≠ .inl (SubstSPD_rI H x y₁ y₂) := by
    simp [SubstSPD_bI, SubstSPD_rI]
  set ρ : Atom 3 (m + 1) ⊕ Atom 3 1 → Atom 3 (m + 1) ⊕ Atom 3 1 :=
    fun z => if z = .inr (.inr 0) then .inl u₀ else z with hρd
  have hρ : ∀ v, ρ (.inl v) = .inl v := fun v => by simp [hρd]
  have hρa : ρ (.inr (.inr 0)) = .inl u₀ := by simp [hρd]
  have hτ0 : (if (.inr 0 : Atom 3 1) ∈ L.int then (.inr (.inr 0) : Atom 3 (m + 1) ⊕ Atom 3 1)
      else .inl (σ (.inr 0))) = .inr (.inr 0) := by rw [hLint]; simp
  have hτe : ∀ a : Fin 3, (if (.inl a : Atom 3 1) ∈ L.int then
      (.inr (.inl a) : Atom 3 (m + 1) ⊕ Atom 3 1) else .inl (σ (.inl a))) = .inl (σ (.inl a)) := by
    intro a; rw [hLint]; simp
  have hend : ∀ f, ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂),
      .inl (SubstSPD_rI H x y₁ y₂)}).mapV ρ).ends (.inr f) =
      (ρ (if (L.ends f).1 ∈ L.int then .inr (L.ends f).1 else .inl (σ (L.ends f).1)),
        ρ (if (L.ends f).2 ∈ L.int then .inr (L.ends f).2 else .inl (σ (L.ends f).2))) :=
    fun _ => rfl
  have heb' : ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂),
      .inl (SubstSPD_rI H x y₁ y₂)}).mapV ρ).ends (.inr fb) = (.inl u₀, .inl (σ (.inl 1))) ∨
      ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂),
      .inl (SubstSPD_rI H x y₁ y₂)}).mapV ρ).ends (.inr fb) = (.inl (σ (.inl 1)), .inl u₀) := by
    rw [hend]
    rcases heb with h | h <;> rw [h] <;> simp [hτ0, hτe, hρa, hρ]
  have her' : ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂),
      .inl (SubstSPD_rI H x y₁ y₂)}).mapV ρ).ends (.inr fr) = (.inl (σ (.inl 2)), .inl u₀) ∨
      ((K.insert L σ {.inl (SubstSPD_bI H x y₁ y₂),
      .inl (SubstSPD_rI H x y₁ y₂)}).mapV ρ).ends (.inr fr) = (.inl u₀, .inl (σ (.inl 2))) := by
    rw [hend]
    rcases her with h | h <;> rw [h] <;> simp [hτ0, hτe, hρa, hρ]
  have htr := SubstSPD_glue_tr K L σ _ _ hbr ρ hρ (fun w hw => by
      rw [hLint, Finset.mem_singleton] at hw
      subst hw
      exact ⟨u₀, hu₀, hρa⟩) _ _ _ _ .plus hu₀ hu₁ hu₂ hu₀ fb fr hfbr hcb heb' hcr her' hoth
    (fun e _ => MolInsert_toMG'_ends_vtx 3 _ _ e)
  have hng := SubstSPD_insert_noGhost (K := K) (L := L) σ
    {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)} hK2 (fun f => by
      by_cases h : f = fb
      · rw [h, hcb]; simp
      · by_cases h' : f = fr
        · rw [h', hcr]; simp
        · rw [hoth _ h h']; simp)
  have hKp := SubstSPD_Kp_gs hGs hbr hu₀ hu₁ hu₂ hm₀ hm₁ hk3 hk4 hr (Or.inl rfl)
    (Or.inl ⟨rfl, Or.inl rfl⟩) (fun e _ => MolInsert_toMG'_ends_vtx 3 _ _ e)
  -- `π` identifies `a` with the molecule of `x`
  have hu₀I : (.inl u₀ : Atom 3 (m + 1) ⊕ Atom 3 1) ∈ K.int.disjSum L.int :=
    Finset.inl_mem_disjSum.2 hu₀
  have haI : (.inr (.inr 0) : Atom 3 (m + 1) ⊕ Atom 3 1) ∈ K.int.disjSum L.int :=
    Finset.inr_mem_disjSum.2 (by rw [hLint]; simp)
  have hsm : (H.glue x y₁ y₂ g).SameMol (SubstSPD_lift x u₀) (glueAtom x y₁ y₂ (.inr 0)) := by
    have E := (H.glue x y₁ y₂ g).sameMol_equivalence
    have hX : (liftA 1 x).isRight = true := SubstSPD_liftA_isRight hx
    obtain ⟨c, hc, hcm⟩ : ∃ c, u₀ = .inr c ∧
        (H.glue x y₁ y₂ (tVar true)).SameMol (liftA 1 x) (.inr c) := by
      rcases hl : liftA 1 x with a' | a'
      · rw [hl] at hX; simp at hX
      · obtain ⟨c, h1, h2⟩ := MolMono_molRep_inr (H.glue x y₁ y₂ (tVar true)) a'
        exact ⟨c, by rw [hu₀d, hl, h1], h2⟩
    have hcR : (SubstSPD_lift (n' := 1) x (.inr c)).isRight = true := by
      simp only [SubstSPD_lift, Sum.elim_inr]
      split_ifs
      · rfl
      · exact SubstSPD_liftA_isRight hx
    have h1 := SubstSPD_sameMol_host H x y₁ y₂ g (u := liftA 1 x) (v := .inr c)
      (by rw [SubstSPD_lift_liftA]; exact SubstSPD_liftA_isRight hx) hcR hcm
    rw [SubstSPD_lift_liftA] at h1
    have h2 : (H.glue x y₁ y₂ g).SameMol (liftA 1 x) (glueAtom x y₁ y₂ (.inr 0)) :=
      SubstSPD_sameMol_of_comp (c := (mkC (.waved .s) (.inl 0) (.inr 0)).map (glueAtom x y₁ y₂))
        (List.mem_append_right _ (List.mem_map.2 ⟨_, hs, rfl⟩)) rfl
        (by exact SubstSPD_liftA_isRight hx) rfl
    rw [hc]
    exact E.trans (E.symm h1) h2
  have hπa : π (.inl u₀) = π (.inr (.inr 0)) := (hmol _ hu₀I _ haI).2 hsm
  have hρπ : ∀ z, π (ρ z) = π z := by
    intro z
    by_cases h : z = .inr (.inr 0)
    · rw [h, hρa, hπa]
    · simp only [hρd, h, ite_false]
  have hρint : ∀ z ∈ K.int.disjSum L.int, ρ z ∈ K.int.disjSum L.int := by
    intro z hz
    by_cases h : z = .inr (.inr 0)
    · rw [h, hρa]; exact hu₀I
    · simp only [hρd, h, ite_false]; exact hz
  have hρext : ∀ z ∈ K.ext.map Function.Embedding.inl, ρ z = z := by
    intro z hz
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 hz
    exact hρ v
  have hgs := (SubstSPD_pipe _ π ρ hidem hint hext hnie hdis hR2 hng hρπ hρint hρext _ htr).2 hKp
  exact (SubstMol_gs_transport ht).2 hgs

end TcGs

/-! ## Outputs of `O_merge` on graphs without dotted edges -/

section Out

variable {k n : ℕ}

private theorem SubstSPD_reach_rel {V W : Type*} {r : V → V → Prop} {G : SimpleGraph W}
    (ψ : V → W) (h : ∀ a b, r a b → G.Reachable (ψ a) (ψ b)) {u v : V}
    (hr : (SimpleGraph.fromRel r).Reachable u v) : G.Reachable (ψ u) (ψ v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hadj ih =>
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h1 | h1
    · exact ih.trans (h _ _ h1)
    · exact ih.trans (h _ _ h1).symm

private theorem SubstSPD_rel_reach {V : Type*} {r : V → V → Prop} {a b : V} (h : r a b) :
    (SimpleGraph.fromRel r).Reachable a b := by
  by_cases hab : a = b
  · rw [hab]
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩).reachable

/-- The tracked graph `t` is `Γ` with its atoms mapped by `t.f`, its dotted edges removed, the ends
of every dotted edge identified and those of every solid edge kept apart. -/
private structure SubstSPD_Out (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps =
    Γ.comps.filterMap fun c => if c.kind = .dot then none else some (c.map t.f)
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_inr : ∃ h : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (h i)) ∧ Function.Surjective h
  f_dot : ∀ c ∈ Γ.comps, c.kind = .dot → t.f c.x = t.f c.y
  f_solid : ∀ c ∈ Γ.comps, c.kind.isSolid = true → t.f c.x ≠ t.f c.y

variable {Γ : Graph k n} {t : Tracked k n}

private theorem SubstSPD_Out.mem (hs : SubstSPD_Out Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, c.kind ≠ .dot ∧ c.map t.f = c' := by
  rw [hs.comps_eq, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    split_ifs at h with hk
    exact ⟨c, hc, hk, Option.some.inj h⟩
  · rintro ⟨c, hc, hk, rfl⟩
    exact ⟨c, hc, by simp [hk]⟩

private theorem SubstSPD_Out.f_surj (hs : SubstSPD_Out Γ t) : Function.Surjective t.f := by
  obtain ⟨h, hh, hsurj⟩ := hs.f_inr
  intro u
  rcases u with a | j
  · exact ⟨.inl a, hs.f_inl a⟩
  · obtain ⟨i, rfl⟩ := hsurj j
    exact ⟨.inr i, hh i⟩

private theorem SubstSPD_Out.dotFree (hs : SubstSPD_Out Γ t) : t.g.DotFree := by
  intro c' hc'
  obtain ⟨c, -, hk, rfl⟩ := hs.mem.1 hc'
  exact hk

private theorem SubstSPD_Out.normal (hs : SubstSPD_Out Γ t) (hb : SubstSPD_Bal Γ.comps)
    (hc : Γ.edgeGraph.Preconnected)
    (hw : ∀ a b : Fin n, (SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps,
      (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v).Reachable
        (.inr a) (.inr b)) :
    t.g.Normal (k + n + Γ.comps.length) := by
  have hsize : k + t.nOut + t.g.comps.length ≤ k + n + Γ.comps.length := by
    have h1 := hs.nOut_le
    have h2 : t.g.comps.length ≤ Γ.comps.length := by
      rw [hs.comps_eq]; exact List.length_filterMap_le _ _
    omega
  have hconn : t.g.edgeGraph.Preconnected := by
    have hedge : ∀ a b, (∃ c ∈ Γ.comps, c.x = a ∧ c.y = b) →
        t.g.edgeGraph.Reachable (t.f a) (t.f b) := by
      rintro a b ⟨c, hc, rfl, rfl⟩
      by_cases hk : c.kind = .dot
      · rw [hs.f_dot c hc hk]
      · exact SubstSPD_rel_reach ⟨c.map t.f, hs.mem.2 ⟨c, hc, hk, rfl⟩, rfl, rfl⟩
    intro u' v'
    obtain ⟨u, rfl⟩ := hs.f_surj u'
    obtain ⟨v, rfl⟩ := hs.f_surj v'
    exact SubstSPD_reach_rel t.f hedge (hc u v)
  have hint : ∀ a b : Fin t.nOut, t.g.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    have hedge : ∀ a b, (∃ c ∈ Γ.comps,
        (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = a ∧ c.y = b) →
        t.g.wavedThetaGraph.Reachable (t.f a) (t.f b) := by
      rintro a b ⟨c, hc, hk, rfl, rfl⟩
      by_cases hd : c.kind = .dot
      · rw [hs.f_dot c hc hd]
      · refine SubstSPD_rel_reach ⟨c.map t.f, hs.mem.2 ⟨c, hc, hd, rfl⟩, ?_, rfl, rfl⟩
        change (c.kind.joinsMol = true ∧ c.kind ≠ .dot) ∨ c.kind.isDiffusive = true
        tauto
    obtain ⟨h, hh, hsurj⟩ := hs.f_inr
    intro a b
    obtain ⟨i, rfl⟩ := hsurj a
    obtain ⟨j, rfl⟩ := hsurj b
    rw [← hh, ← hh]
    exact SubstSPD_reach_rel t.f hedge (hw i j)
  have hsolid : ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → c'.x ≠ c'.y := by
    intro c' hc' hk
    obtain ⟨c, hc, -, rfl⟩ := hs.mem.1 hc'
    exact hs.f_solid c hc hk
  have hbal : ∀ u v : Atom k t.nOut, u ≠ v →
      ((∃ c ∈ t.g.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ t.g.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))) := by
    intro u v huv
    constructor
    · rintro ⟨c', hc', hk, hends⟩
      obtain ⟨c, hc, -, rfl⟩ := hs.mem.1 hc'
      have hne : c.x ≠ c.y := by
        intro h
        apply huv
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; simp [Comp.map, h]
        · rw [← h1, ← h2]; simp [Comp.map, h]
      obtain ⟨d, hd, hdk, hde⟩ := hb.2 c hc hk hne
      have hdnd : d.kind ≠ .dot := by intro h; rw [h] at hdk; cases hdk
      refine ⟨d.map t.f, hs.mem.2 ⟨d, hd, hdnd, rfl⟩, hdk, ?_⟩
      simp only [Comp.map] at hends ⊢
      rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    · rintro ⟨c', hc', hk, hends⟩
      obtain ⟨c, hc, -, rfl⟩ := hs.mem.1 hc'
      obtain ⟨d, hd, hdk, hde⟩ := hb.1 c hc hk
      have hdnd : d.kind ≠ .dot := by intro h; rw [h] at hdk; cases hdk
      refine ⟨d.map t.f, hs.mem.2 ⟨d, hd, hdnd, rfl⟩, hdk, ?_⟩
      simp only [Comp.map] at hends ⊢
      rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  refine ⟨⟨hsize, hconn, hint, fun c hc hk => absurd hk (hs.dotFree c hc)⟩, hsolid, hbal⟩

/-- The scaling order of the output is at least that of the input. -/
private theorem SubstSPD_Out.ord_ge (hs : SubstSPD_Out Γ t) (hd : Γ.DotFree) :
    Γ.ord ≤ t.g.ord := by
  have hc : t.g.comps = Γ.comps.map (Comp.map t.f) := by
    rw [hs.comps_eq]
    rw [← List.filterMap_eq_map]
    exact List.filterMap_congr fun c hc => by simp [hd c hc]
  unfold Graph.ord
  rw [hc, List.map_map]
  have : (Γ.comps.map ((fun c => c.kind.ord) ∘ Comp.map t.f)) = Γ.comps.map fun c => c.kind.ord :=
    List.map_congr_left fun c _ => rfl
  rw [this]
  have := hs.nOut_le
  omega

/-- The identity is an output on a graph without dotted edges and without solid loops. -/
private theorem SubstSPD_out_self (hdf : Γ.DotFree)
    (hsl : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) :
    SubstSPD_Out Γ (Tracked.self Γ) := by
  refine ⟨?_, le_refl _, fun _ => rfl, ⟨id, fun _ => rfl, Function.surjective_id⟩,
    fun c hc hk => absurd hk (hdf c hc), hsl⟩
  change Γ.comps = _
  conv_lhs => rw [← List.filterMap_some (l := Γ.comps)]
  apply List.filterMap_congr
  intro c hc
  change some c = if c.kind = .dot then none else some (c.map id)
  rw [ite_eq_right (hdf c hc)]
  obtain ⟨κ, u, v, T, ℓ⟩ := c
  simp [Comp.map]

/-- `O_merge` on a balanced graph without dotted edges is an output. -/
private theorem SubstSPD_out_merge (hdf : Γ.DotFree) (hb : SubstSPD_Bal Γ.comps)
    (hm : Γ.mergeT = some t) : SubstSPD_Out Γ t := by
  have hs := mergeT_spec hm
  have hsol : ∀ c ∈ Γ.comps, c.kind.isSolid = true → Γ.mrep c.x ≠ Γ.mrep c.y := by
    intro c hc' hk heq
    obtain ⟨d, hd, hdk, hde⟩ := hb.1 c hc' hk
    apply hs.xdot_ne d hd hdk
    rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact heq
    · exact heq.symm
  refine ⟨?_, hs.nOut_le, hs.f_inl, hs.f_inr, fun c hc hk => absurd hk (hdf c hc),
    fun c hc' hk => hs.f_ne _ _ (hsol c hc' hk)⟩
  rw [hs.comps_eq]
  apply List.filterMap_congr
  intro c hc'
  by_cases hk : c.kind.isSolid = true
  · rw [mergeComp_solid hk, ite_eq_right (hsol c hc' hk), ite_eq_right (hdf c hc')]
  · have hk' : c.kind.isSolid = false := by simpa using hk
    unfold mergeComp
    simp [hdf c hc', hk']

end Out

/-! ## `O_merge` as a function of the representatives of the blocks -/

section MergeForm

variable {k n : ℕ}

/-- The representatives of the internal atoms, without repetition. -/
private def SubstSPD_roots (rep : Atom k n → Atom k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => rep (Sum.inr i)).dedup

/-- The atom map of `O_merge` for the representatives `rep`. -/
private def SubstSPD_fm (rep : Atom k n → Atom k n) :
    Atom k n → Atom k (SubstSPD_roots rep).length := fun u =>
  match u with
  | .inl a => .inl a
  | .inr i => .inr ⟨(SubstSPD_roots rep).idxOf (rep (.inr i)),
      List.idxOf_lt_length_of_mem
        (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩

/-- The image of a component under `O_merge` for the representatives `rep`. -/
private def SubstSPD_F (rep : Atom k n → Atom k n) (c : Comp (Atom k n)) :
    Option (Comp (Atom k (SubstSPD_roots rep).length)) :=
  if c.kind == .dot && SubstSPD_fm rep c.x == SubstSPD_fm rep c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map (SubstSPD_fm rep) with kind := c.kind.toWeight, y := SubstSPD_fm rep c.x }
  else some (c.map (SubstSPD_fm rep))

/-- `O_merge` for the representatives `rep`, the components `cs` and the coefficient `co`. -/
private def SubstSPD_M (rep : Atom k n → Atom k n) (cs : List (Comp (Atom k n))) (co : Coeff) :
    Option (Tracked k n) :=
  if cs.any (fun c => c.kind == .xdot && rep c.x == rep c.y) then none else
  some ⟨(SubstSPD_roots rep).length, ⟨cs.filterMap (SubstSPD_F rep), co⟩, SubstSPD_fm rep⟩

private theorem SubstSPD_mergeT_M (Γ : Graph k n) :
    Γ.mergeT = SubstSPD_M (blockRep (dotBlocks (allAtoms k n) Γ.comps)) Γ.comps Γ.coeff := rfl

/-- `O_merge` is determined by the representatives, the test for `×`-dotted edges inside a block,
the images of the components and the coefficient. -/
private theorem SubstSPD_M_congr (rep : Atom k n → Atom k n) {cs₁ cs₂ : List (Comp (Atom k n))}
    {co₁ co₂ : Coeff}
    (hx : cs₁.any (fun c => c.kind == .xdot && rep c.x == rep c.y) =
      cs₂.any (fun c => c.kind == .xdot && rep c.x == rep c.y))
    (hf : cs₁.filterMap (SubstSPD_F rep) = cs₂.filterMap (SubstSPD_F rep)) (hc : co₁ = co₂) :
    SubstSPD_M rep cs₁ co₁ = SubstSPD_M rep cs₂ co₂ := by
  unfold SubstSPD_M
  rw [hx, hf, hc]

private theorem SubstSPD_fm_eq (rep : Atom k n → Atom k n) {i j : Fin n}
    (h : rep (.inr i) = rep (.inr j)) : SubstSPD_fm rep (.inr i) = SubstSPD_fm rep (.inr j) := by
  simp only [SubstSPD_fm, h]

end MergeForm

section BlocksRep

variable {V : Type*} [DecidableEq V]

private theorem SubstSPD_find?_congr {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- Components other than dotted edges do not change the blocks. -/
private theorem SubstSPD_blocks_nondot (as : List V) (cs ds : List (Comp V))
    (h : ∀ d ∈ ds, d.kind ≠ .dot) : dotBlocks as (cs ++ ds) = dotBlocks as cs := by
  induction ds using List.reverseRecOn with
  | nil => simp
  | append_singleton ds d ih =>
    rw [← List.append_assoc, SubstSPD_blocks_snoc, ite_eq_right (h d (by simp)),
      ih (fun d' hd' => h d' (List.mem_append_left _ hd'))]

/-- Two atoms of a partition have the same representative after their blocks are joined. -/
private theorem SubstSPD_blockRep_join (P : List (List V)) {u v : V} (hu : u ∈ P.flatten)
    (hv : v ∈ P.flatten) : blockRep (joinBlocks P u v) u = blockRep (joinBlocks P u v) v := by
  set J := (P.filter fun B => B.contains u || B.contains v).flatten with hJ
  have hJu : u ∈ J := by
    obtain ⟨B, hB, huB⟩ := List.mem_flatten.1 hu
    exact List.mem_flatten.2 ⟨B, List.mem_filter.2 ⟨hB, by simp [huB]⟩, huB⟩
  have hJv : v ∈ J := by
    obtain ⟨B, hB, hvB⟩ := List.mem_flatten.1 hv
    exact List.mem_flatten.2 ⟨B, List.mem_filter.2 ⟨hB, by simp [hvB]⟩, hvB⟩
  have hjoin : joinBlocks P u v = (P.filter fun B => !(B.contains u || B.contains v)) ++ [J] := rfl
  clear_value J
  have hfind : ∀ w, (w = u ∨ w = v) → w ∈ J →
      (joinBlocks P u v).find? (fun B => B.contains w) = some J := by
    intro w hw hwJ
    rw [hjoin, List.find?_append]
    have hn : (P.filter fun B => !(B.contains u || B.contains v)).find?
        (fun B => B.contains w) = none := by
      rw [List.find?_eq_none]
      intro B hB
      obtain ⟨-, hB'⟩ := List.mem_filter.1 hB
      rcases hw with rfl | rfl <;> simp_all
    rw [hn]
    simp [hwJ]
  unfold blockRep
  rw [hfind u (Or.inl rfl) hJu, hfind v (Or.inr rfl) hJv]
  obtain ⟨r, rest, hr⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hJu)
  rw [hr]

/-- Joining the block of `u` with itself does not change the representatives. -/
private theorem SubstSPD_blockRep_join_self {P : List (List V)} (hnd : P.flatten.Nodup) {u : V}
    (hu : u ∈ P.flatten) (w : V) : blockRep (joinBlocks P u u) w = blockRep P w := by
  obtain ⟨B, hB, huB⟩ := List.mem_flatten.1 hu
  have huniq : ∀ B' ∈ P, ∀ a ∈ B', a ∈ B → B' = B := by
    intro B' hB' a ha haB
    by_contra hne
    rw [List.nodup_flatten] at hnd
    exact (hnd.2.forall (R := List.Disjoint) hB' hB hne) ha haB
  have hfilt : (P.filter fun B' => B'.contains u || B'.contains u) = [B] := by
    have hle := SubstSPD_filter_contains_le hnd u
    simp only [Bool.or_self]
    have hmem : B ∈ P.filter fun B' => B'.contains u := List.mem_filter.2 ⟨hB, by simp [huB]⟩
    match hl : P.filter fun B' => B'.contains u with
    | [] => rw [hl] at hmem; simp at hmem
    | [B'] =>
      rw [hl, List.mem_singleton] at hmem
      rw [hmem]; exact hl
    | _ :: _ :: _ => rw [hl] at hle; simp at hle
  unfold blockRep joinBlocks
  rw [hfilt, List.flatten_singleton, List.find?_append]
  by_cases hwB : w ∈ B
  · have hn : (P.filter fun B' => !(B'.contains u || B'.contains u)).find?
        (fun B' => B'.contains w) = none := by
      rw [List.find?_eq_none]
      intro B' hB'
      obtain ⟨hB'P, hB'u⟩ := List.mem_filter.1 hB'
      intro hw
      have : B' = B := huniq B' hB'P w (by simpa using hw) hwB
      subst this
      simp [huB] at hB'u
    have hf : P.find? (fun B' => B'.contains w) = some B := by
      have hex : (P.find? (fun B' => B'.contains w)).isSome = true :=
        List.find?_isSome.2 ⟨B, hB, by simpa using hwB⟩
      obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 hex
      rw [hB']
      have := huniq B' (List.mem_of_find?_eq_some hB') w (by simpa using List.find?_some hB') hwB
      rw [this]
    rw [hn, hf]
    simp [hwB]
  · have hsame : (P.filter fun B' => !(B'.contains u || B'.contains u)).find?
        (fun B' => B'.contains w) = P.find? (fun B' => B'.contains w) := by
      rw [List.find?_filter]
      refine SubstSPD_find?_congr fun B' hB' => ?_
      by_cases hc : B'.contains w = true
      · by_cases hcu : B'.contains u = true
        · exfalso
          have : B' = B := huniq B' hB' u (by simpa using hcu) huB
          subst this
          exact hwB (by simpa using hc)
        · simp only [hc, hcu, Bool.or_self, Bool.not_false]; simp
      · simp only [hc]; simp
    rw [hsame]
    simp [hwB]

end BlocksRep

/-! ## The pairs to split of a graph with one unbalanced solid edge -/

section SplitOne

variable {k n : ℕ}

/-- A graph whose solid edges between distinct atoms carry a `×`-dotted edge with the same ends,
and whose `×`-dotted edges between distinct atoms carry a solid edge, has no pair to split. -/
private theorem SubstSPD_sp_nil {Γ : Graph k n}
    (h1 : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y → ∃ d ∈ Γ.comps, d.kind = .xdot ∧
      (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x))
    (h2 : ∀ c ∈ Γ.comps, c.kind = .xdot → c.x ≠ c.y → ∃ d ∈ Γ.comps, d.kind.isSolid = true ∧
      (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x)) :
    Γ.splitPairs = [] := by
  unfold Graph.splitPairs
  dsimp only
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  rcases SubstSPD_foldl_mem _ (fun acc q => by split_ifs <;> simp) _ [] p hp with h | h
  · simp at h
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hcp⟩ := h
  split_ifs at hcp with hk
  obtain rfl := Option.some.inj hcp
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
  obtain ⟨hk, hne⟩ := hk
  have e1 : spJoined Γ Kind.isSolid c.x c.y = true := by
    rw [spJoined_iff]
    rcases hk with hk | hk
    · exact ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨d, hd, hdk, hde⟩ := h2 c hc hk hne
      exact ⟨d, hd, hdk, hde⟩
  have e2 : spJoined Γ (· == .xdot) c.x c.y = true := by
    rw [spJoined_iff]
    rcases hk with hk | hk
    · obtain ⟨d, hd, hdk, hde⟩ := h1 c hc hk hne
      exact ⟨d, hd, by simp [hdk], hde⟩
    · exact ⟨c, hc, by simp [hk], Or.inl ⟨rfl, rfl⟩⟩
  change (if (spJoined Γ Kind.isSolid c.x c.y != spJoined Γ (· == .xdot) c.x c.y) = true then
    some (c.x, c.y, spJoined Γ Kind.isSolid c.x c.y) else none) = none
  rw [e1, e2]
  rfl

/-- Appending to a balanced list one solid edge between distinct atoms with no solid or `×`-dotted
edge on the same pair gives exactly one pair to split. -/
private theorem SubstSPD_sp_one (A : List (Comp (Atom k n))) (c : Comp (Atom k n)) (co : Coeff)
    (h1 : ∀ d ∈ A, d.kind.isSolid = true → d.x ≠ d.y → ∃ e ∈ A, e.kind = .xdot ∧
      (e.x = d.x ∧ e.y = d.y ∨ e.x = d.y ∧ e.y = d.x))
    (h2 : ∀ d ∈ A, d.kind = .xdot → d.x ≠ d.y → ∃ e ∈ A, e.kind.isSolid = true ∧
      (e.x = d.x ∧ e.y = d.y ∨ e.x = d.y ∧ e.y = d.x))
    (hc : c.kind.isSolid = true) (hne : c.x ≠ c.y)
    (hnot : ∀ d ∈ A, (d.kind.isSolid = true ∨ d.kind = .xdot) →
      ¬ (d.x = c.x ∧ d.y = c.y ∨ d.x = c.y ∧ d.y = c.x)) :
    (⟨A ++ [c], co⟩ : Graph k n).splitPairs = [(c.x, c.y, true)] := by
  set Γ : Graph k n := ⟨A ++ [c], co⟩ with hΓ
  have hmemΓ : ∀ d, d ∈ Γ.comps ↔ d ∈ A ∨ d = c := by
    intro d; simp [hΓ]
  unfold Graph.splitPairs
  dsimp only
  have hcand : (Γ.comps.filterMap fun d => if (d.kind.isSolid || d.kind == .xdot) && d.x != d.y
      then some (d.x, d.y) else none) = (A.filterMap fun d =>
        if (d.kind.isSolid || d.kind == .xdot) && d.x != d.y then some (d.x, d.y) else none) ++
        [(c.x, c.y)] := by
    simp only [hΓ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    simp [hc, hne]
  rw [hcand, List.foldl_append]
  set U := (A.filterMap fun d => if (d.kind.isSolid || d.kind == .xdot) && d.x != d.y
      then some (d.x, d.y) else none).foldl (fun acc p =>
        if acc.any (fun q => q == p || q == p.swap) then acc else acc ++ [p]) [] with hU
  have hUsub : ∀ q ∈ U, ∃ d ∈ A, (d.kind.isSolid = true ∨ d.kind = .xdot) ∧ d.x ≠ d.y ∧
      q = (d.x, d.y) := by
    intro q hq
    rcases SubstSPD_foldl_mem _ (fun acc q => by split_ifs <;> simp) _ [] q hq with h | h
    · simp at h
    obtain ⟨d, hd, hdq⟩ := List.mem_filterMap.1 h
    split_ifs at hdq with hk
    obtain rfl := Option.some.inj hdq
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
    exact ⟨d, hd, hk.1, hk.2, rfl⟩
  have hstep : (List.foldl (fun acc p =>
      if acc.any (fun q => q == p || q == p.swap) then acc else acc ++ [p]) U [(c.x, c.y)]) =
      U ++ [(c.x, c.y)] := by
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ite_eq_right]
    rw [List.any_eq_true]
    rintro ⟨q, hq, hqe⟩
    obtain ⟨d, hd, hk, -, rfl⟩ := hUsub q hq
    simp only [Bool.or_eq_true, beq_iff_eq, Prod.swap_prod_mk, Prod.mk.injEq] at hqe
    exact hnot d hd hk (by tauto)
  rw [hstep, List.filterMap_append]
  have hnil : U.filterMap (fun p =>
      if (spJoined Γ Kind.isSolid p.1 p.2 != spJoined Γ (· == .xdot) p.1 p.2) = true then
        some (p.1, p.2, spJoined Γ Kind.isSolid p.1 p.2) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro q hq
    obtain ⟨d, hd, hk, hne', rfl⟩ := hUsub q hq
    have e1 : spJoined Γ Kind.isSolid d.x d.y = true := by
      rw [spJoined_iff]
      rcases hk with hk | hk
      · exact ⟨d, (hmemΓ d).2 (Or.inl hd), hk, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨e, he, hek, hee⟩ := h2 d hd hk hne'
        exact ⟨e, (hmemΓ e).2 (Or.inl he), hek, hee⟩
    have e2 : spJoined Γ (· == .xdot) d.x d.y = true := by
      rw [spJoined_iff]
      rcases hk with hk | hk
      · obtain ⟨e, he, hek, hee⟩ := h1 d hd hk hne'
        exact ⟨e, (hmemΓ e).2 (Or.inl he), by simp [hek], hee⟩
      · exact ⟨d, (hmemΓ d).2 (Or.inl hd), by simp [hk], Or.inl ⟨rfl, rfl⟩⟩
    simp only
    rw [e1, e2]
    rfl
  have e1 : spJoined Γ Kind.isSolid c.x c.y = true := by
    rw [spJoined_iff]
    exact ⟨c, (hmemΓ c).2 (Or.inr rfl), hc, Or.inl ⟨rfl, rfl⟩⟩
  have e2 : spJoined Γ (· == .xdot) c.x c.y = false := by
    rw [Bool.eq_false_iff, ne_eq, spJoined_iff]
    rintro ⟨d, hd, hdk, hde⟩
    have hdk' : d.kind = .xdot := by simpa using hdk
    rcases (hmemΓ d).1 hd with hd | rfl
    · exact hnot d hd (Or.inr hdk') (by tauto)
    · rw [hdk'] at hc; exact absurd hc (by decide)
  change U.filterMap (fun p =>
      if (spJoined Γ Kind.isSolid p.1 p.2 != spJoined Γ (· == .xdot) p.1 p.2) = true then
        some (p.1, p.2, spJoined Γ Kind.isSolid p.1 p.2) else none) ++
    [(c.x, c.y)].filterMap (fun p =>
      if (spJoined Γ Kind.isSolid p.1 p.2 != spJoined Γ (· == .xdot) p.1 p.2) = true then
        some (p.1, p.2, spJoined Γ Kind.isSolid p.1 p.2) else none) = _
  rw [hnil, List.nil_append]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [e1, e2]
  rfl

end SplitOne

/-! ## The leading term and the terms of `Σ_T`: the `O_dot` forms -/

section LeadPieces

/-- The graph `Θ^{[o]}_{⊗⊕} (Ḡ_{⊖⊕})_{weight} 1_{⊖ = ⊕}`: its substitution has, after `O_merge`,
the `O_dot` forms of `H` times `Θ^{[o]}_{⊗⊕} Ḡ_{⊖⊕}` in which `y₁` and `y₂` are identified. -/
private def SubstSPD_bb (o : List ℕ) : Graph 3 0 :=
  ⟨[mkC (.theta o) (.inl 0) (.inl 1), mkC (.weight .minus) (.inl 2) (.inl 1),
    mkC .dot (.inl 2) (.inl 1)], cm⟩

private theorem SubstSPD_bb_c2 (o : List ℕ) : (SubstSPD_bb o).Normal 6 ∧
    (SubstSPD_bb o).OtimesNoDot ∧ (SubstSPD_bb o).dotExcess = 0 ∧ (SubstSPD_bb o).RgCheck ∧
    (SubstSPD_bb o).labels.length ≤ 1 ∧ (SubstSPD_bb o).NoLabDot ∧ (SubstSPD_bb o).PMBlock :=
  ⟨of_decide_eq_true (by rfl), of_decide_eq_true (by rfl),
    (Graph.dotsAcyclic_iff_dotExcess_eq_zero _).1 (of_decide_eq_true (by rfl)), Or.inl rfl,
    of_decide_eq_true (by rfl), of_decide_eq_true (by rfl), of_decide_eq_true (by rfl)⟩

private theorem SubstSPD_lgx_c2 (o : List ℕ) :
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).Normal 6 ∧
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).OtimesNoDot ∧
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).dotExcess = 0 ∧
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).RgCheck ∧
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).labels.length ≤ 1 ∧
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).NoLabDot ∧
    ¬ (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm).PMBlock :=
  ⟨of_decide_eq_true (by rfl), of_decide_eq_true (by rfl),
    (Graph.dotsAcyclic_iff_dotExcess_eq_zero _).1 (of_decide_eq_true (by rfl)), Or.inl rfl,
    of_decide_eq_true (by rfl), of_decide_eq_true (by rfl), of_decide_eq_false (by rfl)⟩

private theorem SubstSPD_theta_swap (o : List ℕ) :
    (thetaLabelGraph o).swapSolid = SubstSPD_lg o [] cm := rfl

private theorem SubstSPD_bb_ord (o : List ℕ) :
    (SubstSPD_bb o).ord = (o.sum : ℤ) + 2 - 2 * o.length + 2 := by
  simp [Graph.ord, SubstSPD_bb, mkC, Kind.ord]

private theorem SubstSPD_lg_ord_nil (o : List ℕ) (c : Coeff) :
    (SubstSPD_lg o [] c).ord = (o.sum : ℤ) + 2 - 2 * o.length + 1 := by
  simp [Graph.ord, SubstSPD_lg, mkC, Kind.ord]

private theorem SubstSPD_lg_ord_x (o : List ℕ) (c : Coeff) :
    (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] c).ord = (o.sum : ℤ) + 2 - 2 * o.length + 1 := by
  simp [Graph.ord, SubstSPD_lg, mkC, Kind.ord]

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

private theorem SubstSPD_lg_glue (o : List ℕ) (extra : List (Comp (Atom 3 0))) (c : Coeff) :
    (H.glue x y₁ y₂ (SubstSPD_lg o extra c)).comps = liftCs 0 H.comps ++
      ([mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.G .minus) (liftA 0 y₂) (liftA 0 y₁)] ++
        extra.map (Comp.map (glueAtom x y₁ y₂))) := by
  simp [Graph.glue, SubstSPD_lg, mkC, Comp.map, glueAtom]

private theorem SubstSPD_bb_glue (o : List ℕ) :
    (H.glue x y₁ y₂ (SubstSPD_bb o)).comps = liftCs 0 H.comps ++
      [mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.weight .minus) (liftA 0 y₂) (liftA 0 y₁),
        mkC .dot (liftA 0 y₂) (liftA 0 y₁)] := by
  simp [Graph.glue, SubstSPD_bb, mkC, Comp.map, glueAtom]

end LeadPieces

section LeadPieces2

variable {k n : ℕ}

private theorem SubstSPD_labels_nil {Γ : Graph k n} (h : Γ.LabelFree) : Γ.labels = [] := by
  unfold Graph.labels
  rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
  intro c hc
  exact h c hc

private theorem SubstSPD_b1 {Γ : Graph k n} (h : Γ.LabelFree) :
    ¬ (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true) := by
  rw [SubstSPD_labels_nil h]
  rintro (h2 | h2)
  · simp at h2
  · obtain ⟨c, hc, hb⟩ := List.any_eq_true.1 h2
    simp [h c hc] at hb

/-- The `O_dot` forms of a graph without labels and without a pair to split, with a dotted edge
between internal atoms or a solid loop: the output of `O_merge`. -/
private theorem SubstSPD_oDotT_b3_nil {Γ : Graph k n} (hlab : Γ.LabelFree)
    (hsp : Γ.splitPairs = [])
    (hb : (Γ.comps.any fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) ||
      (c.kind.isSolid && c.x == c.y)) = true) (t : Tracked k n) :
    t ∈ oDotT Γ ↔ Γ.mergeT = some t := by
  unfold oDotT
  dsimp only
  rw [ite_eq_right (SubstSPD_b1 hlab), ite_eq_right (by rw [hsp, hb]; simp), hsp]
  simp [SubstSPD_dotChoice_nil]

/-- The `O_dot` forms of a graph without labels with exactly one pair to split, a solid edge
without `×`-dotted edge: the outputs of `O_merge` with a `×`-dotted edge and with a dotted edge on
that pair. -/
private theorem SubstSPD_oDotT_one {Γ : Graph k n} (hlab : Γ.LabelFree) {u v : Atom k n}
    (hsp : Γ.splitPairs = [(u, v, true)]) (t : Tracked k n) :
    t ∈ oDotT Γ ↔ (⟨Γ.comps ++ [mkC .xdot u v], Γ.coeff⟩ : Graph k n).mergeT = some t ∨
      (⟨Γ.comps ++ [mkC .dot u v], Γ.coeff⟩ : Graph k n).mergeT = some t := by
  unfold oDotT
  dsimp only
  rw [ite_eq_right (SubstSPD_b1 hlab), ite_eq_right (by rw [hsp]; simp), hsp]
  have h1 : Γ.dotChoice [(u, v, true)] [] = ⟨Γ.comps ++ [mkC .xdot u v], Γ.coeff⟩ := by
    obtain ⟨cs, co⟩ := Γ
    simp [Graph.dotChoice]
  have h2 : Γ.dotChoice [(u, v, true)] [(u, v, true)] = ⟨Γ.comps ++ [mkC .dot u v], Γ.coeff⟩ := by
    obtain ⟨cs, co⟩ := Γ
    simp [Graph.dotChoice]
  simp [List.sublists, h1, h2]

private theorem SubstSPD_filterMap_solid {α β : Type*} (F : Comp α → Option (Comp β))
    (hF : ∀ c c', F c = some c' → c'.kind.isSolid = true → c.kind.isSolid = true)
    (cs : List (Comp α)) :
    ((cs.filterMap F).filter fun c => c.kind.isSolid).length ≤
      (cs.filter fun c => c.kind.isSolid).length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.filterMap_cons]
    cases hc : F c with
    | none =>
      simp only
      rw [List.filter_cons]
      split_ifs <;> (try simp only [List.length_cons]) <;> omega
    | some c' =>
      simp only [List.filter_cons]
      by_cases h1 : c'.kind.isSolid = true
      · simp only [h1, hF c c' hc h1, ite_true, List.length_cons]; omega
      · simp only [h1, Bool.false_eq_true, ite_false]
        split_ifs <;> (try simp only [List.length_cons]) <;> omega

/-- The solid edges of an output of `O_merge` come from solid edges of the input. -/
private theorem SubstSPD_solidN_merge {Γ : Graph k n} {t : Tracked k n}
    (hm : Γ.mergeT = some t) :
    t.g.solidN ≤ (Γ.comps.filter fun c => c.kind.isSolid).length := by
  have hs := mergeT_spec hm
  unfold Graph.solidN
  rw [hs.comps_eq]
  refine SubstSPD_filterMap_solid _ (fun c c' hc h => ?_) _
  rcases mergeComp_kind hc with hk | ⟨ch, hk1, hk2⟩
  · rw [← hk]; exact h
  · rw [hk2] at h; simp [Kind.isSolid] at h

end LeadPieces2

section LeadPieces3

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

private theorem SubstSPD_theta_ne (o : List ℕ) : (Kind.theta o == Kind.xdot) = false ∧
    (Kind.theta o == Kind.dot) = false := by
  constructor <;> rw [beq_eq_false_iff_ne] <;> intro h <;> cases h

private theorem SubstSPD_kind_beq : (Kind.G .minus == Kind.xdot) = false ∧
    (Kind.weight .minus == Kind.xdot) = false ∧ (Kind.dot == Kind.xdot) = false ∧
    (Kind.G .minus == Kind.dot) = false ∧ (Kind.weight .minus == Kind.dot) = false ∧
    (Kind.dot == Kind.dot) = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem SubstSPD_mem_allAtoms {k n : ℕ} (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

private theorem SubstSPD_mem_flatten_blocks {k n : ℕ} (cs : List (Comp (Atom k n)))
    (u : Atom k n) : u ∈ (dotBlocks (allAtoms k n) cs).flatten :=
  (SubstSPD_blocks_perm _ cs).mem_iff.2 (SubstSPD_mem_allAtoms u)

private theorem SubstSPD_blocks_nodup {k n : ℕ} (cs : List (Comp (Atom k n))) :
    (dotBlocks (allAtoms k n) cs).flatten.Nodup :=
  (SubstSPD_blocks_perm _ cs).nodup_iff.2 SubstSPD_allAtoms_nodup

/-- The components of `H` lifted to `H` times a graph without internal atoms: balanced, without
dotted edges and labels, without solid loops. -/
private theorem SubstSPD_H0 {C : ℕ} (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hD : (H.glue x y₁ y₂ (tVar true)).DotFree) (hL : H.LabelFree) :
    SubstSPD_Bal (liftCs 0 H.comps) ∧ (∀ c ∈ liftCs 0 H.comps, c.kind ≠ .dot) ∧
      (∀ c ∈ liftCs 0 H.comps, c.label = none) ∧
      (∀ c ∈ liftCs 0 H.comps, c.kind.isSolid = true → c.x ≠ c.y) := by
  refine ⟨SubstSPD_Bal_map _ (SubstSPD_Bal_H H x y₁ y₂ hN), fun c hc => ?_, fun c hc => ?_,
    fun c hc hk => ?_⟩ <;> obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  · exact SubstSPD_H_nodot H x y₁ y₂ hD c₀ hc₀
  · simp [Comp.map, hL c₀ hc₀]
  · have hmem : c₀.map (liftA 1) ∈ (H.glue x y₁ y₂ (tVar true)).comps := by
      rw [SubstSPD_G_comps]; exact List.mem_append_left _ (List.mem_map.2 ⟨c₀, hc₀, rfl⟩)
    have h1 := hN.2.1 _ hmem hk
    simp only [Comp.map] at h1 ⊢
    intro h2
    exact h1 (by rw [SubstSPD_liftA_inj h2])

/-- At `y₁ = y₂`, `O_merge` of `H` times `Θ^{[o]}_{⊗⊕} Ḡ_{⊖⊕}` is `O_merge` of `H` times
`SubstSPD_bb o`: the solid loop `Ḡ_{yy}` becomes the weight that `SubstSPD_bb o` carries, and
the dotted loop of the latter is removed. -/
private theorem SubstSPD_mergeT_a (hyy : y₁ = y₂) (o : List ℕ) :
    (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).mergeT = (H.glue x y₁ y₂ (SubstSPD_bb o)).mergeT := by
  subst hyy
  rw [SubstSPD_mergeT_M, SubstSPD_mergeT_M, SubstSPD_lg_glue, SubstSPD_bb_glue]
  have hb1 : dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps ++
      ([mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.G .minus) (liftA 0 y₁) (liftA 0 y₁)] ++
        List.map (Comp.map (glueAtom x y₁ y₁)) [])) =
      dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps) :=
    SubstSPD_blocks_nondot _ _ _ (by simp [mkC])
  have hb2 : blockRep (dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps ++
      [mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.weight .minus) (liftA 0 y₁) (liftA 0 y₁),
        mkC .dot (liftA 0 y₁) (liftA 0 y₁)])) =
      blockRep (dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps)) := by
    have e : liftCs 0 H.comps ++ [mkC (.theta o) (liftA 0 x) (liftA 0 y₁),
        mkC (.weight .minus) (liftA 0 y₁) (liftA 0 y₁), mkC .dot (liftA 0 y₁) (liftA 0 y₁)] =
        (liftCs 0 H.comps ++ [mkC (.theta o) (liftA 0 x) (liftA 0 y₁),
          mkC (.weight .minus) (liftA 0 y₁) (liftA 0 y₁)]) ++
          [mkC .dot (liftA 0 y₁) (liftA 0 y₁)] := by simp
    rw [e, SubstSPD_blocks_snoc]
    simp only [mkC, ite_true]
    rw [SubstSPD_blocks_nondot _ _ _ (by simp)]
    funext w
    exact SubstSPD_blockRep_join_self (SubstSPD_blocks_nodup _) (SubstSPD_mem_flatten_blocks _ _) w
  rw [hb1, hb2]
  refine SubstSPD_M_congr _ ?_ ?_ rfl
  · simp only [List.any_append]
    simp [mkC, (SubstSPD_theta_ne o).1, SubstSPD_kind_beq]
  · simp only [List.filterMap_append]
    congr 1
    simp [SubstSPD_F, mkC, Comp.map, Kind.toWeight, Kind.isSolid, (SubstSPD_theta_ne o).2,
      SubstSPD_kind_beq]

/-- At `y₁ ≠ y₂`, `O_merge` of `H` times `Θ^{[o]}_{⊗⊕} Ḡ_{⊖⊕}` with the dotted edge `y₂ = y₁`
added is `O_merge` of `H` times `SubstSPD_bb o`. -/
private theorem SubstSPD_mergeT_c (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
    (o : List ℕ) :
    (⟨(H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).comps ++ [mkC .dot (liftA 0 y₂) (liftA 0 y₁)],
      (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).coeff⟩ : Graph 3 (m + 0)).mergeT =
      (H.glue x y₁ y₂ (SubstSPD_bb o)).mergeT := by
  rw [SubstSPD_mergeT_M, SubstSPD_mergeT_M, SubstSPD_lg_glue, SubstSPD_bb_glue]
  set P := dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps) with hP
  have hb1 : dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps ++
      ([mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.G .minus) (liftA 0 y₂) (liftA 0 y₁)] ++
        List.map (Comp.map (glueAtom x y₁ y₂)) []) ++ [mkC .dot (liftA 0 y₂) (liftA 0 y₁)]) =
      joinBlocks P (liftA 0 y₂) (liftA 0 y₁) := by
    rw [SubstSPD_blocks_snoc]
    simp only [mkC, ite_true]
    rw [SubstSPD_blocks_nondot _ _ _ (by simp)]
  have hb2 : dotBlocks (allAtoms 3 (m + 0)) (liftCs 0 H.comps ++
      [mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.weight .minus) (liftA 0 y₂) (liftA 0 y₁),
        mkC .dot (liftA 0 y₂) (liftA 0 y₁)]) = joinBlocks P (liftA 0 y₂) (liftA 0 y₁) := by
    have e : liftCs 0 H.comps ++ [mkC (.theta o) (liftA 0 x) (liftA 0 y₁),
        mkC (.weight .minus) (liftA 0 y₂) (liftA 0 y₁), mkC .dot (liftA 0 y₂) (liftA 0 y₁)] =
        (liftCs 0 H.comps ++ [mkC (.theta o) (liftA 0 x) (liftA 0 y₁),
          mkC (.weight .minus) (liftA 0 y₂) (liftA 0 y₁)]) ++
          [mkC .dot (liftA 0 y₂) (liftA 0 y₁)] := by simp
    rw [e, SubstSPD_blocks_snoc]
    simp only [mkC, ite_true]
    rw [SubstSPD_blocks_nondot _ _ _ (by simp)]
  rw [hb1, hb2]
  set rep := blockRep (joinBlocks P (liftA 0 y₂) (liftA 0 y₁)) with hrep
  have hr : rep (liftA 0 y₂) = rep (liftA 0 y₁) :=
    SubstSPD_blockRep_join P (SubstSPD_mem_flatten_blocks _ _) (SubstSPD_mem_flatten_blocks _ _)
  obtain ⟨a₁, ha₁⟩ : ∃ a, liftA 0 y₁ = (.inr a : Atom 3 (m + 0)) := by
    rcases y₁ with a | a
    · simp at hy₁
    · exact ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, liftA 0 y₂ = (.inr a : Atom 3 (m + 0)) := by
    rcases y₂ with a | a
    · simp at hy₂
    · exact ⟨_, rfl⟩
  have hf : SubstSPD_fm rep (liftA 0 y₂) = SubstSPD_fm rep (liftA 0 y₁) := by
    rw [ha₁, ha₂] at hr ⊢
    exact SubstSPD_fm_eq rep hr
  refine SubstSPD_M_congr _ ?_ ?_ rfl
  · simp only [List.any_append]
    simp [mkC, (SubstSPD_theta_ne o).1, SubstSPD_kind_beq]
  · simp only [List.filterMap_append, List.append_assoc]
    congr 1
    simp only [List.filterMap_nil, List.map_nil, List.filterMap_cons]
    simp [SubstSPD_F, mkC, Comp.map, Kind.toWeight, Kind.isSolid, hr, hf,
      (SubstSPD_theta_ne o).2, SubstSPD_kind_beq]

end LeadPieces3

section LeadMain

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

private theorem SubstSPD_liftCs_solid (j : ℕ) (cs : List (Comp (Atom 3 m))) :
    ((liftCs j cs).filter fun c => c.kind.isSolid).length =
      (cs.filter fun c => c.kind.isSolid).length := by
  simp only [liftCs, List.filter_map, List.length_map]
  rfl

private theorem SubstSPD_G_solidN :
    (H.glue x y₁ y₂ (tVar true)).solidN = (H.comps.filter fun c => c.kind.isSolid).length + 2 := by
  unfold Graph.solidN
  rw [SubstSPD_G_comps, List.filter_append, List.length_append, SubstSPD_liftCs_solid]
  simp [mkC, Kind.isSolid]

/-- The components of the substituted graphs of the leading term and of `Σ_T`, and of the graphs
compared with their `O_dot` forms. -/
private theorem SubstSPD_lead_comps (o : List ℕ) :
    (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).comps = liftCs 0 H.comps ++
      [mkC (.theta o) (liftA 0 x) (liftA 0 y₁), mkC (.G .minus) (liftA 0 y₂) (liftA 0 y₁)] ∧
    (H.glue x y₁ y₂ (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm)).comps =
      (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).comps ++ [mkC .xdot (liftA 0 y₂) (liftA 0 y₁)] ∧
    (H.glue x y₁ y₂ (SubstSPD_lg o [mkC .dot (.inl 2) (.inl 1)] cm)).comps =
      (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).comps ++ [mkC .dot (liftA 0 y₂) (liftA 0 y₁)] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [SubstSPD_lg_glue, glueAtom, mkC, Comp.map]

/-- An edge of a graph with the components of `Γ` and a further component `d` whose ends are
joined by a component of `Γ` keeps the reachability of the edge graph of `Γ`. -/
private theorem SubstSPD_edge_reach {k n : ℕ} {Γ Γ' : Graph k n} {d : Comp (Atom k n)}
    (hc : Γ'.comps = Γ.comps ++ [d]) (hd : ∃ c ∈ Γ.comps, c.x = d.x ∧ c.y = d.y)
    (h : Γ'.edgeGraph.Preconnected) : Γ.edgeGraph.Preconnected := by
  intro u v
  refine SubstSPD_reach_rel id (fun a b hab => ?_) (h u v)
  obtain ⟨c, hc', rfl, rfl⟩ := hab
  rw [hc, List.mem_append, List.mem_singleton] at hc'
  rcases hc' with hc' | rfl
  · exact SubstSPD_rel_reach ⟨c, hc', rfl, rfl⟩
  · obtain ⟨c', hc'', h1, h2⟩ := hd
    exact SubstSPD_rel_reach ⟨c', hc'', h1, h2⟩

/-- Waved, dotted and diffusive reachability between internal atoms from the reachability of the
waved and diffusive edges of a graph with the same components and one further component. -/
private theorem SubstSPD_wtd_reach {k n : ℕ} {Γ Γ' : Graph k n} {d : Comp (Atom k n)}
    (hc : Γ'.comps = Γ.comps ++ [d]) (hd : d.kind = .xdot)
    (h : ∀ a b : Fin n, Γ'.wavedThetaGraph.Reachable (.inr a) (.inr b)) :
    ∀ a b : Fin n, (SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps,
      (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v).Reachable
        (.inr a) (.inr b) := by
  intro a b
  refine SubstSPD_reach_rel id (fun u v huv => ?_) (h a b)
  obtain ⟨c, hc', hk, rfl, rfl⟩ := huv
  rw [hc, List.mem_append, List.mem_singleton] at hc'
  rcases hc' with hc' | rfl
  · exact SubstSPD_rel_reach ⟨c, hc', by tauto, rfl, rfl⟩
  · rw [hd] at hk; simp [Kind.joinsMol, Kind.isDiffusive] at hk

end LeadMain

section LeadMain2

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

set_option maxHeartbeats 1000000 in
-- the three cases of the pairs to split
/-- **The `O_dot` forms of the substitution of the leading term or of a term of `Σ_T`**
(`m Θ^{[o]}_{a b₁} Ḡ_{b₁ b₂}` with its solid edge reversed): they are normal regular without dotted
edges and labels, globally standard in the block reading, and of scaling order `≥ ord G + 1`, or
`y₁ = y₂` and the form is the `O_merge` form, of scaling order `ord G - 2 + ord Θ^{[o]}` with
fewer solid edges than `G = H.glue x y₁ y₂ (tVar true)`. -/
private theorem SubstSPD_lead_pieces {C : ℕ} (o : List ℕ) (hk : 2 * o.length ≤ o.sum)
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hD : (H.glue x y₁ y₂ (tVar true)).DotFree) (hI : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hGs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) :
    ∀ t ∈ oDotT (H.glue x y₁ y₂ (thetaLabelGraph o).swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ t.g.LabelFree ∧ gsPM' t.g ∧
        ((H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord ∨
          (y₁ = y₂ ∧ t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord - 2 +
            ((o.sum : ℤ) + 2 - 2 * o.length) ∧
            t.g.solidN < (H.glue x y₁ y₂ (tVar true)).solidN)) := by
  intro t ht
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  rw [SubstSPD_theta_swap] at ht
  obtain ⟨hHb, hHnd, hHl, hHsl⟩ := SubstSPD_H0 H x y₁ y₂ hN hD hL
  obtain ⟨hc0, hcx, hcd⟩ := SubstSPD_lead_comps H x y₁ y₂ o
  have hYc := SubstSPD_bb_glue H x y₁ y₂ o
  have hgs0 : gsPM' (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)) :=
    SubstSPD_lg_gs H x y₁ y₂ hD hI hGs hst o [] cm (by simp)
  -- the scaling orders
  have e1 := glue_ord 3 m 0 H x y₁ y₂ (SubstSPD_lg o [] cm)
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  rw [SubstSPD_tVar_ord] at e2
  rw [SubstSPD_lg_ord_nil] at e1
  have e3 := glue_ord 3 m 0 H x y₁ y₂ (SubstSPD_bb o)
  rw [SubstSPD_bb_ord] at e3
  have e4 := glue_ord 3 m 0 H x y₁ y₂ (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm)
  rw [SubstSPD_lg_ord_x] at e4
  have hk' : (2 : ℤ) * o.length ≤ o.sum := by exact_mod_cast hk
  have hsolG := SubstSPD_G_solidN H x y₁ y₂
  obtain ⟨bN, bO, bX, bR, bLab, bNL, bPM⟩ := SubstSPD_bb_c2 o
  have hC2Y := glue_oDotT_normal m 0 C 6 H x y₁ y₂ (SubstSPD_bb o) hx hy₁ hy₂ hL hN hD bN bO bX
    bR bLab bNL
  obtain ⟨sN, sO, sX, sR, sLab, sNL, sPM⟩ := SubstSPD_lgx_c2 o
  have hC2s := glue_oDotT_normal m 0 C 6 H x y₁ y₂ _ hx hy₁ hy₂ hL hN hD sN sO sX sR sLab sNL
  set Gt := H.glue x y₁ y₂ (SubstSPD_lg o [] cm) with hGt
  set Y := H.glue x y₁ y₂ (SubstSPD_bb o) with hY
  set Ys := H.glue x y₁ y₂ (SubstSPD_lg o [mkC .xdot (.inl 2) (.inl 1)] cm) with hYs
  set Y₁ : Atom 3 (m + 0) := liftA 0 y₁ with hY₁
  set Y₂ : Atom 3 (m + 0) := liftA 0 y₂ with hY₂
  set X : Atom 3 (m + 0) := liftA 0 x with hX
  have hGtL : Gt.LabelFree := by
    intro c hc
    rw [hc0] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hHl c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> rfl
  have hYL : Y.LabelFree := by
    intro c hc
    rw [hYc] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hHl c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> rfl
  have hLF := SubstSPD_oDotT_labelFree hGtL t ht
  have hGtd : Gt.DotFree := by
    intro c hc
    rw [hc0] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hHnd c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> simp [mkC]
  have hGtdots : ∀ c ∈ Gt.comps, c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true :=
    fun c hc hk => absurd hk (hGtd c hc)
  -- the graph `Y`: `O_dot` forms by `O_merge`
  have hspY : Y.splitPairs = [] := by
    refine SubstSPD_sp_nil (fun c hc hks hne => ?_) (fun c hc hkx hne => ?_)
    · rw [hYc] at hc ⊢
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
        exact ⟨d, List.mem_append_left _ hd, h⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [mkC, Kind.isSolid] at hks
    · rw [hYc] at hc ⊢
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
        exact ⟨d, List.mem_append_left _ hd, h⟩
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [mkC] at hkx
  have hbY : (Y.comps.any fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) ||
      (c.kind.isSolid && c.x == c.y)) = true := by
    rw [List.any_eq_true]
    refine ⟨mkC .dot Y₂ Y₁, by rw [hYc]; simp, ?_⟩
    simp only [mkC, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨SubstSPD_liftA_isRight hy₂, SubstSPD_liftA_isRight hy₁⟩
  by_cases hyy : y₁ = y₂
  · -- `y₁ = y₂`: the solid loop `Ḡ_{yy}` becomes a weight
    have hY12 : Y₂ = Y₁ := by rw [hY₁, hY₂, hyy]
    have hsp : Gt.splitPairs = [] := by
      refine SubstSPD_sp_nil (fun c hc hks hne => ?_) (fun c hc hkx hne => ?_)
      · rw [hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
          exact ⟨d, List.mem_append_left _ hd, h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · simp [mkC, Kind.isSolid] at hks
          · exact absurd hY12 hne
      · rw [hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
          exact ⟨d, List.mem_append_left _ hd, h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl <;> simp [mkC] at hkx
    have hb : (Gt.comps.any fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) ||
        (c.kind.isSolid && c.x == c.y)) = true := by
      rw [List.any_eq_true]
      refine ⟨mkC (.G .minus) Y₂ Y₁, by rw [hc0]; simp, ?_⟩
      simp [mkC, Kind.isSolid, hY12]
    rw [SubstSPD_oDotT_b3_nil hGtL hsp hb] at ht
    have hgs : gsPM' t.g := (SubstMol_gsPM'_mergeT 3 (m + 0) Gt t (by norm_num) hGtdots ht).1 hgs0
    rw [SubstSPD_mergeT_a H x y₁ y₂ hyy o] at ht
    have htY : t ∈ oDotT Y := (SubstSPD_oDotT_b3_nil hYL hspY hbY t).2 ht
    obtain ⟨hNt, hDt, hε, -, -⟩ := hC2Y t htY
    have hord := hε ⟨hyy, bPM⟩
    have q1 : t.g.ord + 2 = H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 2) := hord.trans e3
    refine ⟨hNt, hDt, hLF, hgs, Or.inr ⟨hyy, by omega, ?_⟩⟩
    have h1 : t.g.solidN ≤ ((H.glue x y₁ y₂ (SubstSPD_bb o)).comps.filter
        fun c => c.kind.isSolid).length := SubstSPD_solidN_merge ht
    have h2 : ((H.glue x y₁ y₂ (SubstSPD_bb o)).comps.filter fun c => c.kind.isSolid).length =
        (H.comps.filter fun c => c.kind.isSolid).length := by
      rw [SubstSPD_bb_glue, List.filter_append, List.length_append, SubstSPD_liftCs_solid]
      rfl
    omega
  · have hne12 : Y₁ ≠ Y₂ := fun h => hyy (SubstSPD_liftA_inj h)
    -- the graph `Ys` with the `×`-dotted edge `y₂ ≠ y₁`
    have hYsc : Ys.comps = Gt.comps ++ [mkC .xdot Y₂ Y₁] := hcx
    have hspYs : Ys.splitPairs = [] := by
      refine SubstSPD_sp_nil (fun c hc hks hne => ?_) (fun c hc hkx hne => ?_)
      · rw [hYsc, hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
            exact ⟨d, by simp [hd], h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl
            · simp [mkC, Kind.isSolid] at hks
            · exact ⟨mkC .xdot Y₂ Y₁, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · simp only [List.mem_singleton] at hc
          subst hc; simp [mkC, Kind.isSolid] at hks
      · rw [hYsc, hc0] at hc ⊢
        rcases List.mem_append.1 hc with hc | hc
        · rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
            exact ⟨d, by simp [hd], h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl <;> simp [mkC] at hkx
        · simp only [List.mem_singleton] at hc
          subst hc
          exact ⟨mkC (.G .minus) Y₂ Y₁, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
    have hb2Ys : (Ys.splitPairs.isEmpty && !(Ys.comps.any fun c =>
        (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) =
        true := by
      rw [hspYs]
      simp only [List.isEmpty_nil, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.any_eq_false]
      intro c hc
      rw [hYsc, hc0] at hc
      rcases List.mem_append.1 hc with hc | hc
      · rcases List.mem_append.1 hc with hc | hc
        · have h1 := hHnd c hc
          have h2 := hHsl c hc
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and]
          refine ⟨fun h => absurd h.1 h1, fun hs h => h2 hs h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · simp [mkC, (SubstSPD_theta_ne o).2, Kind.isSolid]
          · simp [mkC, Kind.isSolid, Ne.symm hne12]
      · simp only [List.mem_singleton] at hc
        subst hc; simp [mkC, Kind.isSolid]
    have hYsL : Ys.LabelFree := by
      intro c hc
      rw [hYsc] at hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hGtL c hc
      · simp only [List.mem_singleton] at hc; subst hc; rfl
    have hNs : ∃ C'', Ys.Normal C'' := by
      have hself : Tracked.self Ys ∈ oDotT Ys := by
        rw [oDotT_branch2 (SubstSPD_b1 hYsL) hb2Ys]; exact List.mem_singleton_self _
      exact (hC2s _ hself).1
    obtain ⟨Cs, hNs⟩ := hNs
    by_cases hS : ∃ c ∈ H.comps, c.kind.isSolid = true ∧
        (c.x = y₁ ∧ c.y = y₂ ∨ c.x = y₂ ∧ c.y = y₁)
    · -- `H` has a solid edge `y₁ y₂`: no pair to split
      obtain ⟨c₀, hc₀, hk₀, he₀⟩ := hS
      obtain ⟨d₀, hd₀, hdk₀, hde₀⟩ := (SubstSPD_Bal_H H x y₁ y₂ hN).1 c₀ hc₀ hk₀
      have hxd : ∃ d ∈ liftCs 0 H.comps, d.kind = .xdot ∧
          (d.x = Y₂ ∧ d.y = Y₁ ∨ d.x = Y₁ ∧ d.y = Y₂) := by
        refine ⟨d₀.map (liftA 0), List.mem_map.2 ⟨d₀, hd₀, rfl⟩, hdk₀, ?_⟩
        simp only [Comp.map, hY₁, hY₂]
        rcases he₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hde₀ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
          simp_all
      have hbal : SubstSPD_Bal Gt.comps := by
        refine ⟨fun c hc hks => ?_, fun c hc hkx hne => ?_⟩
        · rw [hc0] at hc ⊢
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.1 c hc hks
            exact ⟨d, List.mem_append_left _ hd, h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl
            · simp [mkC, Kind.isSolid] at hks
            · obtain ⟨d, hd, hdk, hde⟩ := hxd
              exact ⟨d, List.mem_append_left _ hd, hdk, by simpa [mkC] using hde⟩
        · rw [hc0] at hc ⊢
          rcases List.mem_append.1 hc with hc | hc
          · obtain ⟨d, hd, h⟩ := hHb.2 c hc hkx hne
            exact ⟨d, List.mem_append_left _ hd, h⟩
          · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
            rcases hc with rfl | rfl <;> simp [mkC] at hkx
      have hb2 : (Gt.splitPairs.isEmpty && !(Gt.comps.any fun c =>
          (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) =
          true := by
        rw [SubstSPD_splitPairs_nil hbal]
        simp only [List.isEmpty_nil, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.any_eq_false]
        intro c hc
        rw [hc0] at hc
        rcases List.mem_append.1 hc with hc | hc
        · have h1 := hHnd c hc
          have h2 := hHsl c hc
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, not_or, not_and]
          refine ⟨fun h => absurd h.1 h1, fun hs h => h2 hs h⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · simp [mkC, (SubstSPD_theta_ne o).2, Kind.isSolid]
          · simp [mkC, Kind.isSolid, Ne.symm hne12]
      rw [oDotT_branch2 (SubstSPD_b1 hGtL) hb2, List.mem_singleton] at ht
      subst ht
      have hout := SubstSPD_out_self hGtd (fun c hc hks => hNs.2.1 c
        (by rw [hYsc]; exact List.mem_append_left _ hc) hks)
      refine ⟨⟨_, hout.normal hbal ?_ ?_⟩, hGtd, hLF, hgs0, Or.inl ?_⟩
      · exact SubstSPD_edge_reach hYsc ⟨mkC (.G .minus) Y₂ Y₁, by rw [hc0]; simp, rfl, rfl⟩
          hNs.1.connected
      · exact SubstSPD_wtd_reach hYsc rfl hNs.1.internal
      · have q : (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).ord =
            H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 1) := e1
        change _ ≤ (H.glue x y₁ y₂ (SubstSPD_lg o [] cm)).ord
        omega
    · -- no solid edge `y₁ y₂` in `H`: the pair `y₂ y₁` is split
      have hnot : ∀ d ∈ liftCs 0 H.comps ++ [mkC (.theta o) X Y₁], (d.kind.isSolid = true ∨
          d.kind = .xdot) → ¬ (d.x = Y₂ ∧ d.y = Y₁ ∨ d.x = Y₁ ∧ d.y = Y₂) := by
        intro d hd hk hde
        rcases List.mem_append.1 hd with hd | hd
        · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
          simp only [Comp.map, hY₁, hY₂] at hde
          have hde' : d₀.x = y₂ ∧ d₀.y = y₁ ∨ d₀.x = y₁ ∧ d₀.y = y₂ := by
            rcases hde with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨SubstSPD_liftA_inj h1, SubstSPD_liftA_inj h2⟩
            · exact Or.inr ⟨SubstSPD_liftA_inj h1, SubstSPD_liftA_inj h2⟩
          rcases hk with hk | hk
          · exact hS ⟨d₀, hd₀, hk, by tauto⟩
          · have hne : d₀.x ≠ d₀.y := by
              rcases hde' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
              exacts [Ne.symm hyy, hyy]
            obtain ⟨e, he, hek, hee⟩ := (SubstSPD_Bal_H H x y₁ y₂ hN).2 d₀ hd₀ hk hne
            exact hS ⟨e, he, hek, by
              rcases hde' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hee with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
                simp_all⟩
        · simp only [List.mem_singleton] at hd
          subst hd
          rcases hk with hk | hk <;> simp [mkC, Kind.isSolid] at hk
      have hsp : Gt.splitPairs = [(Y₂, Y₁, true)] := by
        have hGt' : Gt = ⟨(liftCs 0 H.comps ++ [mkC (.theta o) X Y₁]) ++
            [mkC (.G .minus) Y₂ Y₁], Gt.coeff⟩ := by
          rw [show Gt = ⟨Gt.comps, Gt.coeff⟩ from rfl, hc0]; simp
        rw [hGt']
        refine SubstSPD_sp_one _ _ _ (fun d hd hks hne => ?_) (fun d hd hkx hne => ?_) rfl
          (Ne.symm hne12) hnot
        · rcases List.mem_append.1 hd with hd | hd
          · obtain ⟨e, he, h⟩ := hHb.1 d hd hks
            exact ⟨e, List.mem_append_left _ he, h⟩
          · simp only [List.mem_singleton] at hd; subst hd; simp [mkC, Kind.isSolid] at hks
        · rcases List.mem_append.1 hd with hd | hd
          · obtain ⟨e, he, h⟩ := hHb.2 d hd hkx hne
            exact ⟨e, List.mem_append_left _ he, h⟩
          · simp only [List.mem_singleton] at hd; subst hd; simp [mkC] at hkx
      rw [SubstSPD_oDotT_one hGtL hsp] at ht
      rcases ht with hm | hm
      · -- the `×`-dotted piece
        have hX1 : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).comps =
            Ys.comps := hYsc.symm
        have hX1d : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).DotFree := by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact hGtd c hc
          · simp only [List.mem_singleton] at hc; subst hc; simp [mkC]
        have hX1b : SubstSPD_Bal (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ :
            Graph 3 (m + 0)).comps := by
          rw [hX1]; exact SubstSPD_Bal_normal hNs
        have hout := SubstSPD_out_merge hX1d hX1b hm
        have hcon : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ :
            Graph 3 (m + 0)).edgeGraph.Preconnected := by
          have : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).edgeGraph =
              Ys.edgeGraph := by simp only [Graph.edgeGraph, hYsc]
          rw [this]; exact hNs.1.connected
        have hw : ∀ a b : Fin (m + 0), (SimpleGraph.fromRel fun u v => ∃ c ∈ (⟨Gt.comps ++
            [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).comps,
            (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v).Reachable
              (.inr a) (.inr b) := by
          intro a b
          refine SubstSPD_reach_rel id (fun u v huv => ?_) (hNs.1.internal a b)
          obtain ⟨c, hc, hk, rfl, rfl⟩ := huv
          exact SubstSPD_rel_reach ⟨c, by rw [hYsc] at hc; exact hc, by tauto, rfl, rfl⟩
        have hgsX : gsPM' (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)) :=
          (SubstSPD_gs_comps hX1).2 (SubstSPD_lg_gs H x y₁ y₂ hD hI hGs hst o _ cm
            (by simp [mkC]))
        refine ⟨⟨_, hout.normal hX1b hcon hw⟩, hout.dotFree, hLF,
          (SubstMol_gsPM'_mergeT 3 (m + 0) _ t (by norm_num)
            (fun c hc hk => absurd hk (hX1d c hc)) hm).1 hgsX, Or.inl ?_⟩
        have h1 := hout.ord_ge hX1d
        have h2 : (⟨Gt.comps ++ [mkC .xdot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).ord =
            H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 1) := by
          refine Eq.trans ?_ e4
          simp only [Graph.ord, hYsc]
        omega
      · -- the dotted piece
        have hgsX : gsPM' (⟨Gt.comps ++ [mkC .dot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)) :=
          (SubstSPD_gs_comps hcd.symm).2 (SubstSPD_lg_gs H x y₁ y₂ hD hI hGs hst o _ cm
            (by simp [mkC]))
        have hdots : ∀ c ∈ (⟨Gt.comps ++ [mkC .dot Y₂ Y₁], Gt.coeff⟩ : Graph 3 (m + 0)).comps,
            c.kind = .dot → c.x.isRight = true ∧ c.y.isRight = true := by
          intro c hc hk
          rcases List.mem_append.1 hc with hc | hc
          · exact absurd hk (hGtd c hc)
          · simp only [List.mem_singleton] at hc
            subst hc
            exact ⟨SubstSPD_liftA_isRight hy₂, SubstSPD_liftA_isRight hy₁⟩
        have hgs : gsPM' t.g := (SubstMol_gsPM'_mergeT 3 (m + 0) _ t (by norm_num) hdots hm).1 hgsX
        rw [SubstSPD_mergeT_c H x y₁ y₂ hy₁ hy₂ o] at hm
        have htY : t ∈ oDotT Y := (SubstSPD_oDotT_b3_nil hYL hspY hbY t).2 hm
        obtain ⟨hNt, hDt, -, hε', -⟩ := hC2Y t htY
        have hord := hε' (fun h => hyy h.1)
        have q1 : t.g.ord = H.ord + ((o.sum : ℤ) + 2 - 2 * o.length + 2) := hord.trans e3
        refine ⟨hNt, hDt, hLF, hgs, Or.inl ?_⟩
        omega

end LeadMain2

/-! ## The recollision terms of [II, (4.15)] -/

section Tc

/-- The first recollision term with its solid edge reversed: `s_{⊗a} w⁺_a Ḡ_{⊖a} 1_{a = ⊕}
1_{a ≠ ⊖}`. -/
private def SubstSPD_tc1 : Graph 3 1 :=
  ⟨[mkC (.waved .s) (.inl 0) (.inr 0), mkC (.weight .plus) (.inr 0) (.inr 0),
    mkC (.G .minus) (.inl 2) (.inr 0), mkC .dot (.inr 0) (.inl 1), mkC .xdot (.inr 0) (.inl 2)], 1⟩

/-- The second recollision term with its solid edge reversed: `s_{⊗a} G_{⊕a} w⁻_a 1_{a ≠ ⊕}
1_{a = ⊖}`. -/
private def SubstSPD_tc2 : Graph 3 1 :=
  ⟨[mkC (.waved .s) (.inl 0) (.inr 0), mkC (.G .plus) (.inl 1) (.inr 0),
    mkC (.weight .minus) (.inr 0) (.inr 0), mkC .xdot (.inr 0) (.inl 1),
    mkC .dot (.inr 0) (.inl 2)],
    1⟩

/-- The third recollision term: `s_{⊗a} w⁺_a w⁻_a 1_{a = ⊕} 1_{a = ⊖}`. -/
private def SubstSPD_tc3 : Graph 3 1 :=
  ⟨[mkC (.waved .s) (.inl 0) (.inr 0), mkC (.weight .plus) (.inr 0) (.inr 0),
    mkC (.weight .minus) (.inr 0) (.inr 0), mkC .dot (.inr 0) (.inl 1), mkC .dot (.inr 0) (.inl 2)],
    1⟩

private theorem SubstSPD_code_inj {k n : ℕ} {c d : Comp (Atom k n)} (h : c.code = d.code) :
    c = d := by
  have ha : Function.Injective
      (Sum.elim (fun i : Fin k => i.val) (fun i : Fin n => k + i.val)) := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg _ (Fin.ext hab)
    · have := a.2; omega
    · have := b.2; omega
    · exact congrArg _ (Fin.ext (by omega))
  obtain ⟨κ, u, v, T, ℓ⟩ := c
  obtain ⟨κ', u', v', T', ℓ'⟩ := d
  simp only [Comp.code, CompCode.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have h4' := List.map_injective_iff.2 ha h4
  have h5' : ℓ = ℓ' := by
    refine Option.map_injective ?_ h5
    rintro ⟨p, a⟩ ⟨q, b⟩ hpq
    simp only [Prod.map, Prod.mk.injEq, id] at hpq
    rw [hpq.1, ha hpq.2]
  rw [h1, ha h2, ha h3, h4', h5']

private theorem SubstSPD_comps_of_code {k n : ℕ} {Γ Γ' : Graph k n} (h : Γ.code = Γ'.code) :
    Γ.comps = Γ'.comps :=
  List.map_injective_iff.2 (fun _ _ => SubstSPD_code_inj) h

set_option maxHeartbeats 4000000 in
-- kernel evaluation of the recollision terms
/-- The recollision terms of [II, (4.15)], with their solid edges reversed, are the three graphs
above, up to the coefficient. -/
private theorem SubstSPD_tVarCorr_cases : ∀ g ∈ tVarCorr, g.1 = 1 ∧
    (g.2.swapSolid.code = SubstSPD_tc1.code ∨ g.2.swapSolid.code = SubstSPD_tc2.code ∨
      g.2.swapSolid.code = SubstSPD_tc3.code) := by
  kdec

set_option maxHeartbeats 4000000 in
-- kernel evaluation
private theorem SubstSPD_tc_c2 : ∀ g ∈ [SubstSPD_tc1, SubstSPD_tc2, SubstSPD_tc3],
    g.Normal 12 ∧ g.OtimesNoDot ∧ g.DotsAcyclic ∧ g.RgCheck ∧ g.labels.length ≤ 1 ∧ g.NoLabDot ∧
      g.LabelFree := by
  kdec

end Tc

section TcRow

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m)

set_option maxHeartbeats 4000000 in
-- kernel evaluation of the molecular graphs of the recollision terms
private theorem SubstSPD_tc_gs123 (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hGs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) :
    gsPM' (H.glue x y₁ y₂ SubstSPD_tc1) ∧ gsPM' (H.glue x y₁ y₂ SubstSPD_tc2) ∧
      gsPM' (H.glue x y₁ y₂ SubstSPD_tc3) :=
  ⟨SubstSPD_tc_gs H x y₁ y₂ hD hI hGs hst SubstSPD_tc1 List.mem_cons_self (by kdec) (.inr 1)
      (.inl ⟨2, by kdec⟩) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec),
    SubstSPD_tc_gs H x y₁ y₂ hD hI hGs hst SubstSPD_tc2 List.mem_cons_self (by kdec)
      (.inl ⟨1, by kdec⟩)
      (.inr 2) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec),
    SubstSPD_tc_gs H x y₁ y₂ hD hI hGs hst SubstSPD_tc3 List.mem_cons_self (by kdec) (.inr 1)
      (.inr 2)
      (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec)⟩

set_option maxHeartbeats 4000000 in
-- kernel evaluation
private theorem SubstSPD_tc_ord :
    (¬ SubstSPD_tc1.PMBlock ∧ SubstSPD_tc1.ord = 3) ∧ (¬ SubstSPD_tc2.PMBlock ∧
      SubstSPD_tc2.ord = 3) ∧ (SubstSPD_tc3.PMBlock ∧ SubstSPD_tc3.ord = 4 ∧
        (SubstSPD_tc3.comps.filter fun c => c.kind.isSolid).length = 0) := by
  kdec

/-- The solid edges of an `O_dot` form of a balanced graph come from solid edges of the graph. -/
private theorem SubstSPD_solidN_oDotT {k n : ℕ} {Γ : Graph k n} (hb : SubstSPD_Bal Γ.comps)
    {t : Tracked k n} (ht : t ∈ oDotT Γ) :
    t.g.solidN ≤ (Γ.comps.filter fun c => c.kind.isSolid).length := by
  rcases mem_oDotT_cases ht with rfl | ⟨A, hA, hm⟩
  · exact le_refl _
  · rw [SubstSPD_splitPairs_nil hb, List.sublist_nil] at hA
    subst hA
    rw [SubstSPD_splitPairs_nil hb, SubstSPD_dotChoice_nil] at hm
    exact SubstSPD_solidN_merge hm

/-- **The `O_dot` forms of the substitution of a recollision term** of [II, (4.15)]: normal
regular without dotted edges and labels (by `glue_oDotT_normal`), globally standard in the block
reading, of scaling order `ord G + 1`; for the third term at `y₁ = y₂`, of scaling order `ord G`
with fewer solid edges than `G`. -/
private theorem SubstSPD_tc_row {C : ℕ} (tc : Graph 3 1) (hN' : tc.Normal 12)
    (hO : tc.OtimesNoDot) (hX : tc.DotsAcyclic) (hR : tc.RgCheck) (hlab : tc.labels.length ≤ 1)
    (hNL : tc.NoLabDot) (hLF : tc.LabelFree) (hgs : gsPM' (H.glue x y₁ y₂ tc))
    (hord : (tc.PMBlock ∧ tc.ord = 4 ∧ (tc.comps.filter fun c => c.kind.isSolid).length = 0) ∨
      (¬ tc.PMBlock ∧ 3 ≤ tc.ord))
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) :
    ∀ t ∈ oDotT (H.glue x y₁ y₂ tc), (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧ t.g.LabelFree ∧
      gsPM' t.g ∧ ((H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord ∨
        (y₁ = y₂ ∧ t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord ∧
          t.g.solidN < (H.glue x y₁ y₂ (tVar true)).solidN)) := by
  intro t ht
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨hNt, hDt, hε, hε', -⟩ := glue_oDotT_normal m 1 C 12 H x y₁ y₂ tc hx hy₁ hy₂ hL hN hD
    hN' hO ((Graph.dotsAcyclic_iff_dotExcess_eq_zero _).1 hX) hR hlab hNL t ht
  have hbal := SubstSPD_glue_bal H x y₁ y₂ tc hN hN'
  have hdots := SubstSPD_glue_dots H x y₁ y₂ tc hx hy₁ hy₂ hD
  have hGtL : (H.glue x y₁ y₂ tc).LabelFree := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      simp [Comp.map, hL c₀ hc₀]
    · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      simp [Comp.map, hLF c₀ hc₀]
  refine ⟨hNt, hDt, SubstSPD_oDotT_labelFree hGtL t ht,
    (SubstSPD_oDotT_bal hbal hdots t ht).2.2 hgs, ?_⟩
  have e1 := glue_ord 3 m 1 H x y₁ y₂ tc
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  rw [SubstSPD_tVar_ord] at e2
  rcases hord with ⟨hPM, ho, hs0⟩ | ⟨hPM, ho⟩
  · by_cases hyy : y₁ = y₂
    · have h1 := hε ⟨hyy, hPM⟩
      refine Or.inr ⟨hyy, by omega, ?_⟩
      have h2 := SubstSPD_solidN_oDotT hbal ht
      have h3 : ((H.glue x y₁ y₂ tc).comps.filter fun c => c.kind.isSolid).length =
          (H.comps.filter fun c => c.kind.isSolid).length := by
        simp only [Graph.glue, List.filter_append, List.length_append, SubstSPD_liftCs_solid]
        have : ((tc.comps.map (Comp.map (glueAtom x y₁ y₂))).filter
            fun c => c.kind.isSolid).length = (tc.comps.filter fun c => c.kind.isSolid).length := by
          simp only [List.filter_map, List.length_map]
          rfl
        omega
      have h4 := SubstSPD_G_solidN H x y₁ y₂
      omega
    · have h1 := hε' (fun h => hyy h.1)
      exact Or.inl (by omega)
  · have h1 := hε' (fun h => hPM h.2)
    exact Or.inl (by omega)

end TcRow

/-! ## Row (1): the leading term, the terms of `Σ_T` and the recollision terms -/

section Row1

private theorem SubstSPD_normal_coeff {k n C : ℕ} {cs : List (Comp (Atom k n))} {c₁ c₂ : Coeff}
    (h : (⟨cs, c₁⟩ : Graph k n).Normal C) : (⟨cs, c₂⟩ : Graph k n).Normal C :=
  ⟨⟨h.1.size, h.1.connected, h.1.internal, h.1.noIntDot⟩, h.2.1, h.2.2⟩

private theorem SubstSPD_chain_mem : ∀ (f b : ℕ) (o : List ℕ), o ∈ chainLabelsAux f b →
    o ≠ [] ∧ ∀ j ∈ o, 4 ≤ j
  | 0, _, o, h => by simp [chainLabelsAux] at h
  | f + 1, b, o, h => by
    simp only [chainLabelsAux, List.mem_flatMap, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.mem_cons, List.mem_map] at h
    obtain ⟨j, ⟨-, hj2, -⟩, rfl | ⟨o', ho', rfl⟩⟩ := h
    · refine ⟨by simp, ?_⟩
      intro i hi; simp at hi; omega
    · refine ⟨by simp, ?_⟩
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · omega
      · exact (SubstSPD_chain_mem f _ o' ho').2 i hi

private theorem SubstSPD_sum_ge (o : List ℕ) (h : ∀ j ∈ o, 4 ≤ j) : 4 * o.length ≤ o.sum := by
  induction o with
  | nil => simp
  | cons a o ih =>
    simp only [List.length_cons, List.sum_cons]
    have := h a List.mem_cons_self
    have := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    omega

/-- **Row (1) of [II, Lemma 6.5]** in the block reading (the conjunct of [II, Lemma 6.5] on the
leading term, the terms of `Σ_T` and the three recollision terms of [II, (4.15)],
[II, Lemma 6.5 (1), (2)]): under the hypotheses of [II, Lemma 6.5], every `O_dot` form `t` of
the substitution of one of these graphs is normal regular without dotted edges and without
labels, globally standard in the block reading, of scaling order `≥ ord G + 1`, or `y₁ = y₂` and
`t` has the scaling order of `G = H.glue x y₁ y₂ (tVar true)` and fewer solid edges. -/
theorem globalGood_row1 :
  ∀ (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    3 ≤ n → (n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (∀ g ∈ leadExp ++ sigmaTExp (n - 1) ++ tVarCorr,
      ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧
        t.g.DotFree ∧ t.g.LabelFree ∧ gsPM' t.g ∧
          ((H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord ∨
            (y₁ = y₂ ∧ t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord ∧
              t.g.solidN < (H.glue x y₁ y₂ (tVar true)).solidN))) := by
  intro n D 𝒯 m C H x y₁ y₂ _ _ hL hN hd _ _ hI _ hgs _ _ hst g hg t ht
  rw [List.mem_append, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · -- the leading term
    simp only [leadExp, List.mem_singleton] at hg
    subst hg
    obtain ⟨h1, h2, h3, h4, h5⟩ := SubstSPD_lead_pieces H x y₁ y₂ [] (by simp) hL hN hd hI hgs
      hst t ht
    refine ⟨h1, h2, h3, h4, ?_⟩
    rcases h5 with h5 | ⟨h5, h6, h7⟩
    · exact Or.inl h5
    · exact Or.inr ⟨h5, by simpa using h6, h7⟩
  · -- the terms of `Σ_T`
    simp only [sigmaTExp, List.mem_map] at hg
    obtain ⟨o, ho, rfl⟩ := hg
    obtain ⟨hne, h4⟩ := SubstSPD_chain_mem _ _ o ho
    have hs := SubstSPD_sum_ge o h4
    have hl : 1 ≤ o.length := List.length_pos_iff.2 hne
    obtain ⟨h1, h2, h3, h4', h5⟩ := SubstSPD_lead_pieces H x y₁ y₂ o (by omega) hL hN hd hI hgs
      hst t ht
    refine ⟨h1, h2, h3, h4', Or.inl ?_⟩
    rcases h5 with h5 | ⟨-, h6, -⟩
    · exact h5
    · have : (4 : ℤ) * o.length ≤ o.sum := by exact_mod_cast hs
      have : (1 : ℤ) ≤ o.length := by exact_mod_cast hl
      omega
  · -- the recollision terms
    obtain ⟨h1, hcode⟩ := SubstSPD_tVarCorr_cases g hg
    obtain ⟨n₁, g₂⟩ := g
    simp only at h1
    subst h1
    simp only at ht hcode
    obtain ⟨g1, g2, g3⟩ := SubstSPD_tc_gs123 H x y₁ y₂ hd hI hgs hst
    obtain ⟨o1, o2, o3⟩ := SubstSPD_tc_ord
    have key : ∀ tc ∈ [SubstSPD_tc1, SubstSPD_tc2, SubstSPD_tc3],
        g₂.swapSolid.code = tc.code → gsPM' (H.glue x y₁ y₂ tc) →
        ((tc.PMBlock ∧ tc.ord = 4 ∧ (tc.comps.filter fun c => c.kind.isSolid).length = 0) ∨
          (¬ tc.PMBlock ∧ 3 ≤ tc.ord)) →
        (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧ t.g.LabelFree ∧ gsPM' t.g ∧
          ((H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord ∨
            (y₁ = y₂ ∧ t.g.ord = (H.glue x y₁ y₂ (tVar true)).ord ∧
              t.g.solidN < (H.glue x y₁ y₂ (tVar true)).solidN)) := by
      intro tc htc hc hgtc hord
      obtain ⟨cN, cO, cX, cR, cLab, cNL, cLF⟩ := SubstSPD_tc_c2 tc htc
      have hcomps := SubstSPD_comps_of_code hc
      have heq : g₂.swapSolid = ⟨tc.comps, g₂.swapSolid.coeff⟩ := by
        rw [← hcomps]
      rw [heq] at ht
      obtain ⟨cs, co⟩ := tc
      exact SubstSPD_tc_row H x y₁ y₂ ⟨cs, g₂.swapSolid.coeff⟩ (SubstSPD_normal_coeff cN) cO cX
        cR cLab cNL cLF ((SubstSPD_gs_comps (Γ₁ := H.glue x y₁ y₂ ⟨cs, g₂.swapSolid.coeff⟩)
          (Γ₂ := H.glue x y₁ y₂ ⟨cs, co⟩) rfl).2 hgtc) hord hL hN hd hst t ht
    rcases hcode with hc | hc | hc
    · exact key _ (by simp) hc g1 (Or.inr ⟨o1.1, by rw [o1.2]⟩)
    · exact key _ (by simp) hc g2 (Or.inr ⟨o2.1, by rw [o2.2]⟩)
    · exact key _ (by simp) hc g3 (Or.inl o3)

end Row1

section Instance

end Instance

section Witness

end Witness

end RBM8D.Graphs
