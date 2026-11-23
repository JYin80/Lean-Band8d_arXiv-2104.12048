module

public import RBM8D.Graph.Local.Edge

@[expose] public section

/-!
# Order properties of the edge expansions

[I, Lemmas 3.13, 3.16, 3.19].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The solid edges attached to `x` are `G_{xy}` and `G_{yx}` of the charge `ch` (with
`×`-dotted edges between `x` and `y`), the shape of case (b) of [I, Lemmas 3.16, 3.19] for the
`GG` expansion; for the `GḠ` expansion the shape is `G_{xy} Ḡ_{xy}` or `G_{yx} Ḡ_{yx}`. -/
def Graph.GGShapeAt {k n : ℕ} (Γ : Graph k n) (x y : Atom k n) : Prop :=
  Γ.deg x = 2 ∧ ∃ ch : Charge, (∃ c ∈ Γ.comps, c.kind = .G ch ∧ c.x = x ∧ c.y = y) ∧
    ∃ c ∈ Γ.comps, c.kind = .G ch ∧ c.x = y ∧ c.y = x

/-- The input shape of [I, Lemma 3.16]: `deg(x) = 2` and the solid edges attached to `x` are
`G_{xy} G_{y'x}` or `Ḡ_{xy} Ḡ_{y'x}`. -/
def Graph.GGInputAt {k n : ℕ} (Γ : Graph k n) (x y y' : Atom k n) : Prop :=
  Γ.deg x = 2 ∧ ∃ ch : Charge, (∃ c ∈ Γ.comps, c.kind = .G ch ∧ c.x = x ∧ c.y = y) ∧
    ∃ c ∈ Γ.comps, c.kind = .G ch ∧ c.x = y' ∧ c.y = x

/-- The input shape of [I, Lemma 3.19]: `deg(x) = 2` and the solid edges attached to `x` are
`G_{xy} Ḡ_{xy'}` or `G_{yx} Ḡ_{y'x}`. -/
def Graph.GGbarInputAt {k n : ℕ} (Γ : Graph k n) (x y y' : Atom k n) : Prop :=
  Γ.deg x = 2 ∧ ∃ out : Bool,
    (∃ c ∈ Γ.comps, c.kind = .G .plus ∧ (if out then c.x = x ∧ c.y = y else c.x = y ∧ c.y = x)) ∧
    ∃ c ∈ Γ.comps, c.kind = .G .minus ∧ (if out then c.x = x ∧ c.y = y' else c.x = y' ∧ c.y = x)

/-! ## Dot blocks -/

section Blocks

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem flatten_map_singleton' (as : List V) : (as.map fun a => [a]).flatten = as := by
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
  | nil => rw [dotBlocks_nil, flatten_map_singleton']
  | append_singleton cs c ih =>
    rw [dotBlocks_snoc, blockStep]
    split_ifs
    · exact (joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

private theorem dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [dotBlocks_snoc, blockStep]
    -- membership of an atom of `as` in some block
    have hmem : ∀ a ∈ as, ∃ B ∈ dotBlocks as cs, a ∈ B := by
      intro a ha
      have := (dotBlocks_flatten_perm as cs).mem_iff.2 ha
      rwa [List.mem_flatten] at this
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
        obtain ⟨B₁, hB₁, hx⟩ := hmem _ hxa
        obtain ⟨B₂, hB₂, hy⟩ := hmem _ hya
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

/-- Two atoms of one block of a partition have the same representative. -/
private theorem blockRep_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B : List V}
    (hB : B ∈ P) {u v : V} (hu : u ∈ B) (hv : v ∈ B) : blockRep P u = blockRep P v := by
  have hfind : ∀ w ∈ B, P.find? (fun B' => B'.contains w) = some B := by
    intro w hw
    have hex : (P.find? (fun B' => B'.contains w)).isSome = true :=
      List.find?_isSome.2 ⟨B, hB, by simpa [List.contains_iff_mem] using hw⟩
    obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 hex
    rw [hB']
    have hB'mem := List.mem_of_find?_eq_some hB'
    have hw' : w ∈ B' := by simpa [List.contains_iff_mem] using List.find?_some hB'
    congr 1
    by_contra hne
    rw [List.nodup_flatten] at hnd
    have := hnd.2.forall (R := List.Disjoint) hB'mem hB hne
    exact this hw' hw
  unfold blockRep
  rw [hfind u hu, hfind v hv]
  cases B with
  | nil => simp at hu
  | cons r rest => rfl

end Blocks

/-! ## The data of `O_merge` -/

section MergeData

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

/-- The representative of an atom in the dot blocks of a graph. -/
private def Graph.mrep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

private theorem Graph.mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.mrep c.x = Γ.mrep c.y := by
  obtain ⟨B, hB, hx, hy⟩ := dotBlocks_joined (allAtoms k n) Γ.comps
    (fun c _ => ⟨mem_allAtoms _, mem_allAtoms _⟩) c hc hk
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (dotBlocks_flatten_perm _ _).nodup_iff.2 allAtoms_nodup
  exact blockRep_eq_of_mem hnd hB hx hy

/-- The roots: the representatives of the internal atoms, without repetition. -/
private def Graph.mroots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => Γ.mrep (Sum.inr i)).dedup

private theorem Graph.mem_mroots (Γ : Graph k n) (i : Fin n) : Γ.mrep (.inr i) ∈ Γ.mroots :=
  List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- The new internal atom of an internal atom: the position of its root. -/
private def Graph.midx (Γ : Graph k n) (i : Fin n) : Fin Γ.mroots.length :=
  ⟨Γ.mroots.idxOf (Γ.mrep (.inr i)), List.idxOf_lt_length_of_mem (Γ.mem_mroots i)⟩

/-- The atom map of `O_merge`. -/
private def Graph.mmap (Γ : Graph k n) : Atom k n → Atom k Γ.mroots.length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr (Γ.midx i)

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
private def mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

private theorem mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && Γ.mrep c.x == Γ.mrep c.y) then none else
    some ⟨Γ.mroots.length, ⟨Γ.comps.filterMap (mergeComp Γ.mrep Γ.mmap), Γ.coeff⟩, Γ.mmap⟩ := rfl

/-- The structure of a tracked graph `t` with `Γ.mergeT = some t`: its components, its atom map
and its blocks. -/
private structure MergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (mergeComp Γ.mrep t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, Γ.mrep u = Γ.mrep v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, Γ.mrep u ≠ Γ.mrep v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → Γ.mrep c.x ≠ Γ.mrep c.y

private theorem mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
    MergeSpec Γ t := by
  rw [mergeT_eq] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hsurj : Function.Surjective Γ.midx := by
    intro j
    have hj : Γ.mroots[j.1] ∈ Γ.mroots := List.getElem_mem j.2
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
    refine ⟨i, Fin.ext ?_⟩
    simp only [Graph.midx]
    rw [hi]
    exact (List.nodup_dedup _).idxOf_getElem j.1 j.2
  refine ⟨rfl, rfl, ?_, fun a => rfl, ?_, ⟨Γ.midx, fun i => rfl, hsurj⟩, ?_, ?_, ?_⟩
  · exact (List.dedup_sublist _).length_le.trans (by simp)
  · intro u'
    rcases u' with a | j
    · exact ⟨.inl a, rfl⟩
    · obtain ⟨i, hi⟩ := hsurj j
      exact ⟨.inr i, by simp [Graph.mmap, hi]⟩
  · intro u v huv hu hv
    rcases u with a | i
    · simp at hu
    rcases v with b | j
    · simp at hv
    have : Γ.midx i = Γ.midx j := Fin.ext (by
      change Γ.mroots.idxOf (Γ.mrep (.inr i)) = Γ.mroots.idxOf (Γ.mrep (.inr j))
      rw [huv])
    simp [Graph.mmap, this]
  · intro u v huv hf
    rcases u with a | i <;> rcases v with b | j
    · simp only [Graph.mmap, Sum.inl.injEq] at hf
      exact huv (by rw [hf])
    · simp [Graph.mmap] at hf
    · simp [Graph.mmap] at hf
    · simp only [Graph.mmap, Sum.inr.injEq] at hf
      have h2 := congrArg Fin.val hf
      simp only [Graph.midx] at h2
      exact huv ((List.idxOf_inj (Γ.mem_mroots i)).1 h2)
  · intro c hcm hk hcc
    apply hc
    rw [List.any_eq_true]
    exact ⟨c, hcm, by simp [hk, hcc]⟩

end MergeData

section SplitPairs

variable {k n : ℕ}

/-- The test "joined by a component whose kind satisfies `p`". -/
private def spJoined (Γ : Graph k n) (p : Kind → Bool) (u v : Atom k n) : Bool :=
  Γ.comps.any fun c => p c.kind && ((c.x == u && c.y == v) || (c.x == v && c.y == u))

/-- The ordered candidate pairs. -/
private def spCand (Γ : Graph k n) : List (Atom k n × Atom k n) :=
  Γ.comps.filterMap fun c =>
    if (c.kind.isSolid || c.kind == .xdot) && c.x != c.y then some (c.x, c.y) else none

/-- One step of the removal of repeated unordered pairs. -/
private def spStep (acc : List (Atom k n × Atom k n)) (p : Atom k n × Atom k n) :
    List (Atom k n × Atom k n) :=
  if acc.any (fun q => q == p || q == p.swap) then acc else acc ++ [p]

/-- The candidate pairs, each unordered pair once. -/
private def spUniq (Γ : Graph k n) : List (Atom k n × Atom k n) := (spCand Γ).foldl spStep []

private theorem splitPairs_eq (Γ : Graph k n) : Γ.splitPairs =
    (spUniq Γ).filterMap fun p =>
      if (spJoined Γ Kind.isSolid p.1 p.2 != spJoined Γ (· == .xdot) p.1 p.2) = true then
        some (p.1, p.2, spJoined Γ Kind.isSolid p.1 p.2) else none := rfl

private theorem spJoined_iff (Γ : Graph k n) (pr : Kind → Bool) (u v : Atom k n) :
    spJoined Γ pr u v = true ↔
      ∃ c ∈ Γ.comps, pr c.kind = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
  unfold spJoined
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

private theorem spStep_mono (acc : List (Atom k n × Atom k n)) (p) : acc ⊆ spStep acc p := by
  unfold spStep
  split_ifs
  · exact List.Subset.refl _
  · exact List.subset_append_left _ _

private theorem foldl_spStep_mono (l acc : List (Atom k n × Atom k n)) :
    acc ⊆ l.foldl spStep acc := by
  induction l generalizing acc with
  | nil => exact List.Subset.refl _
  | cons p l ih => exact List.Subset.trans (spStep_mono acc p) (ih _)

private theorem foldl_spStep_cover (l acc : List (Atom k n × Atom k n)) :
    ∀ p ∈ l, ∃ q ∈ l.foldl spStep acc, q = p ∨ q = p.swap := by
  induction l generalizing acc with
  | nil => intro p hp; simp at hp
  | cons p₀ l ih =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · have h : ∃ q ∈ spStep acc p, q = p ∨ q = p.swap := by
        unfold spStep
        split_ifs with h
        · obtain ⟨q, hq, hqb⟩ := List.any_eq_true.1 h
          simp only [Bool.or_eq_true, beq_iff_eq] at hqb
          exact ⟨q, hq, hqb⟩
        · exact ⟨p, List.mem_append_right _ (List.mem_singleton_self _), Or.inl rfl⟩
      obtain ⟨q, hq, hqp⟩ := h
      exact ⟨q, foldl_spStep_mono l _ hq, hqp⟩
    · exact ih _ p hp

private theorem foldl_spStep_pairwise (l acc : List (Atom k n × Atom k n))
    (h : acc.Pairwise fun a b => ¬(b = a ∨ b = a.swap)) :
    (l.foldl spStep acc).Pairwise fun a b => ¬(b = a ∨ b = a.swap) := by
  induction l generalizing acc with
  | nil => exact h
  | cons p l ih =>
    apply ih
    unfold spStep
    split_ifs with hany
    · exact h
    · rw [List.pairwise_append]
      refine ⟨h, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro hab
      apply hany
      rw [List.any_eq_true]
      refine ⟨a, ha, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq]
      rcases hab with h1 | h1
      · exact Or.inl h1.symm
      · right
        rw [h1]
        simp

private theorem spUniq_pairwise (Γ : Graph k n) :
    (spUniq Γ).Pairwise fun a b => ¬(b = a ∨ b = a.swap) :=
  foldl_spStep_pairwise _ _ List.Pairwise.nil

private theorem spUniq_cover (Γ : Graph k n) :
    ∀ p ∈ spCand Γ, ∃ q ∈ spUniq Γ, q = p ∨ q = p.swap :=
  foldl_spStep_cover _ _

/-- Two members of `spUniq` that are equal as unordered pairs are equal. -/
private theorem spUniq_eq {Γ : Graph k n} {q q' : Atom k n × Atom k n} (hq : q ∈ spUniq Γ)
    (hq' : q' ∈ spUniq Γ) (h : q' = q ∨ q' = q.swap) : q' = q := by
  by_contra hne
  have : Std.Symm fun a b : Atom k n × Atom k n => ¬(b = a ∨ b = a.swap) := by
    refine ⟨fun a b hab hba => hab ?_⟩
    rcases hba with h | h
    · exact Or.inl h.symm
    · right
      rw [h]
      simp
  exact (spUniq_pairwise Γ).forall hq hq' (Ne.symm hne) h

/-- Membership in `splitPairs`. -/
private theorem mem_splitPairs {Γ : Graph k n} {p : Atom k n × Atom k n × Bool} :
    p ∈ Γ.splitPairs ↔ (p.1, p.2.1) ∈ spUniq Γ ∧
      spJoined Γ Kind.isSolid p.1 p.2.1 != spJoined Γ (· == .xdot) p.1 p.2.1 ∧
      p.2.2 = spJoined Γ Kind.isSolid p.1 p.2.1 := by
  rw [splitPairs_eq, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hp⟩
    split_ifs at hp with hne
    · obtain rfl := Option.some.inj hp
      exact ⟨hq, by simpa using hne, rfl⟩
  · rintro ⟨hq, hne, hs⟩
    refine ⟨(p.1, p.2.1), hq, ?_⟩
    have hne' : (spJoined Γ Kind.isSolid p.1 p.2.1 != spJoined Γ (· == .xdot) p.1 p.2.1) =
        true := by simpa using hne
    simp only [hne', ↓reduceIte]
    rw [← hs]

end SplitPairs

/-! ## The terms of `O_dot` -/

section DotChoice

variable {k n : ℕ}

/-- The test "the pair `{u, v}` is a pair without solid edge". -/
private def xonlyB (SP : List (Atom k n × Atom k n × Bool)) (u v : Atom k n) : Bool :=
  SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))

/-- The components of `Γ` that stay in `dotChoice Γ SP A`. -/
private def keptComps (Γ : Graph k n) (SP : List (Atom k n × Atom k n × Bool)) :
    List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => !(c.kind == .xdot && xonlyB SP c.x c.y)

/-- The components added in `dotChoice Γ SP A`. -/
private def addedComps (SP A : List (Atom k n × Atom k n × Bool)) : List (Comp (Atom k n)) :=
  SP.filterMap fun p =>
    if p ∈ A then some (mkC .dot p.1 p.2.1) else if p.2.2 then some (mkC .xdot p.1 p.2.1)
    else none

private theorem dotChoice_eq (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    Γ.dotChoice SP A = ⟨keptComps Γ SP ++ addedComps SP A,
      (-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * Γ.coeff⟩ := rfl

private theorem xonlyB_iff (SP : List (Atom k n × Atom k n × Bool)) (u v : Atom k n) :
    xonlyB SP u v = true ↔
      ∃ p ∈ SP, p.2.2 = false ∧ (p.1 = u ∧ p.2.1 = v ∨ p.1 = v ∧ p.2.1 = u) := by
  unfold xonlyB
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']

private theorem mem_keptComps (Γ : Graph k n) (SP : List (Atom k n × Atom k n × Bool))
    (c : Comp (Atom k n)) :
    c ∈ keptComps Γ SP ↔ c ∈ Γ.comps ∧ ¬ (c.kind = .xdot ∧ xonlyB SP c.x c.y = true) := by
  unfold keptComps
  simp [List.mem_filter, imp_iff_not_or]

private theorem mem_addedComps {SP A : List (Atom k n × Atom k n × Bool)} {c : Comp (Atom k n)} :
    c ∈ addedComps SP A ↔ ∃ p ∈ SP, (p ∈ A ∧ c = mkC .dot p.1 p.2.1) ∨
      (p ∉ A ∧ p.2.2 = true ∧ c = mkC .xdot p.1 p.2.1) := by
  unfold addedComps
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, ?_⟩
    split_ifs at h with h1 h2
    · exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
    · exact Or.inr ⟨h1, h2, (Option.some.inj h).symm⟩
  · rintro ⟨p, hp, h | h⟩
    · exact ⟨p, hp, by rw [ite_eq_left h.1, h.2]⟩
    · exact ⟨p, hp, by rw [ite_eq_right h.1, ite_eq_left h.2.1, h.2.2]⟩

private theorem addedComps_label {SP A : List (Atom k n × Atom k n × Bool)}
    {c : Comp (Atom k n)} (h : c ∈ addedComps SP A) : c.label = none ∧
      (c.kind = .dot ∨ c.kind = .xdot) := by
  obtain ⟨p, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 h
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

end DotChoice

section ODotBranches

variable {k n : ℕ}

private theorem oDotT_branch1 {Γ : Graph k n}
    (h : 2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true) :
    oDotT Γ = [Tracked.self Γ] := by
  unfold oDotT
  dsimp only
  rw [ite_eq_left h]

private theorem oDotT_branch2 {Γ : Graph k n}
    (h1 : ¬ (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true))
    (h2 : (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true) :
    oDotT Γ = [Tracked.self Γ] := by
  unfold oDotT
  dsimp only
  rw [ite_eq_right h1, ite_eq_left h2]

end ODotBranches

/-! ## Structure of the result of `mergeT` -/

section MergeFacts

variable {k n : ℕ}

private theorem mergeComp_dot {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    mergeComp rep f c = if f c.x = f c.y then none else some (c.map f) := by
  unfold mergeComp
  by_cases h : f c.x = f c.y
  · simp [hk, h]
  · simp [hk, h, Kind.isSolid]

private theorem mergeComp_solid {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hs : c.kind.isSolid = true) :
    mergeComp rep f c = if rep c.x = rep c.y then
      some { c.map f with kind := c.kind.toWeight, y := f c.x } else some (c.map f) := by
  have hnd : c.kind ≠ .dot := by
    intro h
    rw [h] at hs
    simp [Kind.isSolid] at hs
  unfold mergeComp
  by_cases h : rep c.x = rep c.y
  · simp [hs, h, hnd]
  · simp [hs, h, hnd]

private theorem mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hd : c.kind ≠ .dot) (hs : c.kind.isSolid = false) :
    mergeComp rep f c = some (c.map f) := by
  unfold mergeComp
  simp [hd, hs]

variable {Γ : Graph k n} {t : Tracked k n}

private theorem MergeSpec.mem_comps (hs : MergeSpec Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, mergeComp Γ.mrep t.f c = some c' := by
  rw [hs.comps_eq, List.mem_filterMap]

/-- A component that is neither a dotted edge nor a solid edge keeps its kind and is mapped. -/
private theorem MergeSpec.mem_of_other (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hd : c.kind ≠ .dot) (hsol : c.kind.isSolid = false) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, mergeComp_other hd hsol⟩

end MergeFacts

/-! ## Facts about the pairs to split -/

section SplitFacts

variable {k n : ℕ}

/-- `c₂` joins the same two atoms as `c`. -/
def SamePair (c c₂ : Comp (Atom k n)) : Prop :=
  c₂.x = c.x ∧ c₂.y = c.y ∨ c₂.x = c.y ∧ c₂.y = c.x

private theorem spJoined_samePair {Γ : Graph k n} {pr : Kind → Bool} {c : Comp (Atom k n)}
    {q : Atom k n × Atom k n} (hq : q.1 = c.x ∧ q.2 = c.y ∨ q.1 = c.y ∧ q.2 = c.x)
    (h : spJoined Γ pr q.1 q.2 = true) :
    ∃ c₂ ∈ Γ.comps, pr c₂.kind = true ∧ SamePair c c₂ := by
  obtain ⟨c₂, hc₂, hk₂, hm⟩ := (spJoined_iff _ _ _ _).1 h
  refine ⟨c₂, hc₂, hk₂, ?_⟩
  unfold SamePair
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hm with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp_all

private theorem joined_of {Γ : Graph k n} {pr : Kind → Bool} {c : Comp (Atom k n)}
    {q : Atom k n × Atom k n} (hc : c ∈ Γ.comps) (hk : pr c.kind = true)
    (hq : q.1 = c.x ∧ q.2 = c.y ∨ q.1 = c.y ∧ q.2 = c.x) :
    spJoined Γ pr q.1 q.2 = true := by
  rw [spJoined_iff]
  refine ⟨c, hc, hk, ?_⟩
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

private theorem rep_of {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.isSolid = true ∨ c.kind = .xdot) (hne : c.x ≠ c.y) :
    ∃ q ∈ spUniq Γ, q.1 = c.x ∧ q.2 = c.y ∨ q.1 = c.y ∧ q.2 = c.x := by
  have hmem : (c.x, c.y) ∈ spCand Γ := by
    unfold spCand
    rw [List.mem_filterMap]
    refine ⟨c, hc, ?_⟩
    have : ((c.kind.isSolid || c.kind == .xdot) && c.x != c.y) = true := by
      rcases hk with h | h <;> simp [h, hne]
    rw [ite_eq_left this]
  obtain ⟨q, hq, hqc⟩ := spUniq_cover Γ _ hmem
  refine ⟨q, hq, ?_⟩
  rcases hqc with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private theorem solid_split {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.isSolid = true) (hne : c.x ≠ c.y) :
    (∃ c₃ ∈ Γ.comps, c₃.kind = .xdot ∧ SamePair c c₃ ∧
        xonlyB Γ.splitPairs c₃.x c₃.y = false) ∨
      ∃ p ∈ Γ.splitPairs, p.2.2 = true ∧ (p.1 = c.x ∧ p.2.1 = c.y ∨ p.1 = c.y ∧ p.2.1 = c.x) := by
  obtain ⟨q, hq, hqc⟩ := rep_of hc (Or.inl hk) hne
  have hs : spJoined Γ Kind.isSolid q.1 q.2 = true := joined_of hc hk hqc
  by_cases hx : spJoined Γ (· == .xdot) q.1 q.2 = true
  · left
    obtain ⟨c₃, hc₃, hk₃, hsp⟩ := spJoined_samePair hqc hx
    refine ⟨c₃, hc₃, by simpa using hk₃, hsp, ?_⟩
    by_contra hcon
    have hcon' : xonlyB Γ.splitPairs c₃.x c₃.y = true := by simpa using hcon
    obtain ⟨p, hp, hpf, hpm⟩ := (xonlyB_iff _ _ _).1 hcon'
    obtain ⟨hpq, -, hp2⟩ := mem_splitPairs.1 hp
    have hrel : (p.1, p.2.1) = q ∨ (p.1, p.2.1) = q.swap := by
      unfold SamePair at hsp
      rcases hqc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hsp with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        rcases hpm with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> simp_all [Prod.ext_iff]
    have heq := spUniq_eq hq hpq hrel
    have h1 : p.1 = q.1 := congrArg Prod.fst heq
    have h2 : p.2.1 = q.2 := congrArg Prod.snd heq
    rw [h1, h2, hs, hpf] at hp2
    exact Bool.false_ne_true hp2
  · right
    have hx' : spJoined Γ (· == .xdot) q.1 q.2 = false := by simpa using hx
    have hp : (q.1, q.2, true) ∈ Γ.splitPairs :=
      mem_splitPairs.2 ⟨hq, by simp [hs, hx'], hs.symm⟩
    exact ⟨_, hp, rfl, hqc⟩

private theorem mem_dotChoice_of_ne_xdot (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hk : c.kind ≠ .xdot) :
    c ∈ (Γ.dotChoice SP A).comps := by
  rw [dotChoice_eq]
  exact List.mem_append_left _ ((mem_keptComps Γ SP c).2 ⟨hc, fun h => hk h.1⟩)

end SplitFacts

section MergeOrder

variable {k n : ℕ}

private theorem Kind.ord_toWeight_solid {κ : Kind} (h : κ.isSolid = true) :
    κ.toWeight.ord = κ.ord - 1 := by
  cases κ <;> simp_all [Kind.isSolid, Kind.ord, Kind.toWeight]

private theorem sum_ord_mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (cs : List (Comp (Atom k n))) :
    ((cs.filterMap (mergeComp rep f)).map fun c => c.kind.ord).sum =
      (cs.map fun c => c.kind.ord).sum
        - 2 * ((cs.filter fun c => c.kind == .dot && f c.x == f c.y).length : ℤ)
        - ((cs.filter fun c => c.kind.isSolid && rep c.x == rep c.y).length : ℤ) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.filterMap_cons]
    by_cases hd : c.kind = .dot
    · have hdo : Kind.ord .dot = 2 := rfl
      have hsd : Kind.isSolid .dot = false := rfl
      by_cases hf : f c.x = f c.y
      · rw [mergeComp_dot hd, ite_eq_left hf]
        simp only [List.map_cons, List.sum_cons, List.filter_cons, hd, hf, beq_self_eq_true,
          Bool.and_self, ite_true, hsd, Bool.false_and, Bool.false_eq_true, ite_false,
          List.length_cons, Nat.cast_add, Nat.cast_one, hdo]
        rw [ih]
        ring
      · rw [mergeComp_dot hd, ite_eq_right hf]
        have hfb : (f c.x == f c.y) = false := by simpa using hf
        simp only [List.map_cons, List.sum_cons, List.filter_cons, hd, hfb, beq_self_eq_true,
          Bool.and_false, hsd, Bool.false_and, Bool.false_eq_true, ite_false, Comp.map, hdo]
        rw [ih]
        ring
    · by_cases hs : c.kind.isSolid = true
      · have hnd : (c.kind == .dot) = false := by simpa using hd
        by_cases hr : rep c.x = rep c.y
        · rw [mergeComp_solid hs, ite_eq_left hr]
          simp only [List.map_cons, List.sum_cons, List.filter_cons, hnd, Bool.false_and,
            Bool.false_eq_true, ite_false, hs, hr, beq_self_eq_true, Bool.and_self, ite_true,
            List.length_cons, Comp.map, Nat.cast_add, Nat.cast_one]
          rw [ih, Kind.ord_toWeight_solid hs]
          ring
        · rw [mergeComp_solid hs, ite_eq_right hr]
          have hrb : (rep c.x == rep c.y) = false := by simpa using hr
          simp only [List.map_cons, List.sum_cons, List.filter_cons, hnd, Bool.false_and,
            Bool.false_eq_true, ite_false, hs, hrb, Bool.and_false, Comp.map]
          rw [ih]
          ring
      · have hs' : c.kind.isSolid = false := by simpa using hs
        have hnd : (c.kind == .dot) = false := by simpa using hd
        rw [mergeComp_other hd hs']
        simp only [List.map_cons, List.sum_cons, List.filter_cons, hnd, Bool.false_and,
          Bool.false_eq_true, ite_false, hs', Comp.map]
        rw [ih]
        ring

private theorem MergeSpec.ord_eq {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t) :
    t.g.ord = h.ord
      - 2 * ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ)
      - ((h.comps.filter fun c => c.kind.isSolid && h.mrep c.x == h.mrep c.y).length : ℤ)
      + 2 * ((n : ℤ) - t.nOut) := by
  unfold Graph.ord
  rw [hs.comps_eq, sum_ord_mergeComp]
  ring

private theorem sum_ord_filter_xdot {V : Type*} (cs : List (Comp V)) (p : Comp V → Bool)
    (h : ∀ c ∈ cs, p c = false → c.kind = .xdot) :
    ((cs.filter p).map fun c => c.kind.ord).sum = (cs.map fun c => c.kind.ord).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    by_cases hp : p c = true
    · rw [List.filter_cons_of_pos hp]
      simp [ih']
    · have hp' : p c = false := by simpa using hp
      have hx := h c (List.mem_cons_self ..) hp'
      have ho : c.kind.ord = 0 := by rw [hx]; rfl
      rw [List.filter_cons_of_neg hp]
      simp [ih', ho]

private theorem addedComps_ord (SP A : List (Atom k n × Atom k n × Bool)) :
    (((addedComps SP A).map fun c => c.kind.ord).sum : ℤ) =
      2 * (((addedComps SP A).filter fun c => c.kind == .dot).length : ℤ) := by
  have key : ∀ l : List (Comp (Atom k n)), (∀ c ∈ l, c.kind = .dot ∨ c.kind = .xdot) →
      (((l.map fun c => c.kind.ord).sum : ℤ)) =
        2 * ((l.filter fun c => c.kind == .dot).length : ℤ) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons c l ih =>
      intro h
      have ih' := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
      rcases h c (List.mem_cons_self ..) with hc | hc
      · have ho : c.kind.ord = 2 := by rw [hc]; rfl
        have hb : (c.kind == .dot) = true := by simp [hc]
        rw [List.map_cons, List.sum_cons, ho, ih']
        simp only [List.filter_cons, hb, ite_true, List.length_cons]
        push_cast
        ring
      · have ho : c.kind.ord = 0 := by rw [hc]; rfl
        have hb : (c.kind == .dot) = false := by simp [hc]
        rw [List.map_cons, List.sum_cons, ho, ih']
        simp only [List.filter_cons, hb, Bool.false_eq_true, ite_false]
        simp
  exact key _ fun c hc => (addedComps_label hc).2

private theorem dotChoice_ord (g : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    (g.dotChoice SP A).ord = g.ord +
      2 * (((addedComps SP A).filter fun c => c.kind == .dot).length : ℤ) := by
  unfold Graph.ord
  rw [dotChoice_eq]
  simp only [List.map_append, List.sum_append]
  have h1 : ((keptComps g SP).map fun c => c.kind.ord).sum =
      (g.comps.map fun c => c.kind.ord).sum := by
    unfold keptComps
    apply sum_ord_filter_xdot
    intro c _ hp
    simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hp
    exact hp.1
  rw [h1, ← addedComps_ord]
  ring

/-- The dotted edges of `g` join distinct atoms, one of them external. -/
def DotOK (g : Graph k n) : Prop :=
  ∀ c ∈ g.comps, c.kind = .dot → c.x ≠ c.y ∧ (c.x.isRight = false ∨ c.y.isRight = false)

/-- The number of added dotted edges whose ends have different images. -/
private def odK (g : Graph k n) (A : List (Atom k n × Atom k n × Bool)) (t : Tracked k n) : ℕ :=
  ((addedComps g.splitPairs A).filter fun c => c.kind == .dot && t.f c.x != t.f c.y).length

/-- The number of solid edges whose ends are in one dot block. -/
private def odConv (h : Graph k n) : ℕ :=
  (h.comps.filter fun c => c.kind.isSolid && h.mrep c.x == h.mrep c.y).length

private theorem length_filter_split {α : Type*} (l : List α) (p q : α → Bool) :
    (l.filter fun c => p c && q c).length + (l.filter fun c => p c && !q c).length =
      (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    by_cases hp : p c = true
    · by_cases hq : q c = true
      · simp [hp, hq]
        omega
      · have hq' : q c = false := by simpa using hq
        simp [hp, hq']
        omega
    · have hp' : p c = false := by simpa using hp
      simpa [hp'] using ih

private theorem MergeSpec.old_dot_ne {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    {c : Comp (Atom k n)} (hxy : c.x ≠ c.y) (hext : c.x.isRight = false ∨ c.y.isRight = false) :
    t.f c.x ≠ t.f c.y := by
  obtain ⟨g, hg, -⟩ := hs.f_inr
  rcases hx : c.x with a | i <;> rcases hy : c.y with b | j
  · rw [hx, hy] at hxy
    rw [hs.f_inl, hs.f_inl]
    intro h
    exact hxy (by simpa using h)
  · rw [hs.f_inl, hg]
    simp
  · rw [hs.f_inl, hg]
    simp
  · rw [hx, hy] at hext
    simp at hext

private theorem merge_rem_add_K {g : Graph k n} (hd : DotOK g)
    {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (g.dotChoice g.splitPairs A).mergeT = some t) :
    ((g.dotChoice g.splitPairs A).comps.filter
        fun c => c.kind == .dot && t.f c.x == t.f c.y).length + odK g A t =
      ((addedComps g.splitPairs A).filter fun c => c.kind == .dot).length := by
  have hs := mergeT_spec hm
  have hsplit := length_filter_split (addedComps g.splitPairs A) (fun c => c.kind == .dot)
    (fun c => t.f c.x == t.f c.y)
  rw [dotChoice_eq]
  change ((keptComps g g.splitPairs ++ addedComps g.splitPairs A).filter _).length + _ = _
  rw [List.filter_append, List.length_append]
  have hk : (keptComps g g.splitPairs).filter
      (fun c => c.kind == .dot && t.f c.x == t.f c.y) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    have hcg := ((mem_keptComps g g.splitPairs c).1 hc).1
    by_contra hcon
    simp only [beq_iff_eq, Bool.and_eq_true] at hcon
    obtain ⟨hk, hf⟩ := hcon
    exact hs.old_dot_ne (hd c hcg hk).1 (hd c hcg hk).2 (hf)
  rw [hk, List.length_nil, zero_add, odK]
  exact hsplit

private theorem merge_ord_eq {g : Graph k n} (hd : DotOK g) {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (g.dotChoice g.splitPairs A).mergeT = some t) :
    t.g.ord = g.ord + 2 * (odK g A t : ℤ) + 2 * ((n : ℤ) - t.nOut) -
      (odConv (g.dotChoice g.splitPairs A) : ℤ) := by
  have hs := mergeT_spec hm
  have hr := merge_rem_add_K hd hm
  rw [hs.ord_eq, dotChoice_ord]
  unfold odConv
  have : (((g.dotChoice g.splitPairs A).comps.filter
        fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ) + odK g A t =
      (((addedComps g.splitPairs A).filter fun c => c.kind == .dot).length : ℤ) := by
    exact_mod_cast hr
  linarith

/-- `c` has a `×`-dotted component joining the same two atoms. -/
def partnered (g : Graph k n) (c : Comp (Atom k n)) : Bool :=
  g.comps.any fun c₂ => c₂.kind == .xdot &&
    ((c₂.x == c.x && c₂.y == c.y) || (c₂.x == c.y && c₂.y == c.x))

private theorem partnered_iff (g : Graph k n) (c : Comp (Atom k n)) :
    partnered g c = true ↔ ∃ c₃ ∈ g.comps, c₃.kind = .xdot ∧ SamePair c c₃ := by
  unfold partnered SamePair
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

private theorem xdot_kept {g : Graph k n} {c c₃ : Comp (Atom k n)} (hc : c ∈ g.comps)
    (hs : c.kind.isSolid = true) (hc₃ : c₃ ∈ g.comps) (_hk₃ : c₃.kind = .xdot)
    (hsp : SamePair c c₃) : c₃ ∈ keptComps g g.splitPairs := by
  rw [mem_keptComps]
  refine ⟨hc₃, ?_⟩
  rintro ⟨-, hx⟩
  obtain ⟨p, hp, hpf, hpm⟩ := (xonlyB_iff _ _ _).1 hx
  obtain ⟨-, -, hp2⟩ := mem_splitPairs.1 hp
  have hjs : spJoined g Kind.isSolid p.1 p.2.1 = true := by
    refine joined_of (q := (p.1, p.2.1)) hc hs ?_
    unfold SamePair at hsp
    rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hsp with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp_all
  rw [hpf] at hp2
  rw [hjs] at hp2
  exact Bool.false_ne_true hp2

private theorem solid_conv_pair {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) {c : Comp (Atom k n)} (hc : c ∈ g.comps)
    (hs : c.kind.isSolid = true) (hne : c.x ≠ c.y)
    (hr : (g.dotChoice g.splitPairs A).mrep c.x = (g.dotChoice g.splitPairs A).mrep c.y) :
    ∃ p ∈ g.splitPairs, p ∈ A ∧ p.2.2 = true ∧
      (p.1 = c.x ∧ p.2.1 = c.y ∨ p.1 = c.y ∧ p.2.1 = c.x) := by
  have hms := mergeT_spec hm
  rcases solid_split hc hs hne with ⟨c₃, hc₃, hk₃, hsp, hx⟩ | ⟨p, hp, hpf, hpm⟩
  · exfalso
    have hc₃' : c₃ ∈ (g.dotChoice g.splitPairs A).comps := by
      rw [dotChoice_eq]
      refine List.mem_append_left _ ((mem_keptComps g _ c₃).2 ⟨hc₃, ?_⟩)
      rintro ⟨-, h⟩
      rw [hx] at h
      exact Bool.false_ne_true h
    have := hms.xdot_ne c₃ hc₃' hk₃
    unfold SamePair at hsp
    rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this
      exact this hr
    · rw [h1, h2] at this
      exact this hr.symm
  · refine ⟨p, hp, ?_, hpf, hpm⟩
    by_contra hpA
    have hmem : mkC .xdot p.1 p.2.1 ∈ (g.dotChoice g.splitPairs A).comps := by
      rw [dotChoice_eq]
      exact List.mem_append_right _ (mem_addedComps.2 ⟨p, hp, Or.inr ⟨hpA, hpf, rfl⟩⟩)
    have := hms.xdot_ne _ hmem rfl
    simp only [mkC] at this
    rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this
      exact this hr
    · rw [h1, h2] at this
      exact this hr.symm

private theorem foldl_spStep_subset (l acc : List (Atom k n × Atom k n)) :
    ∀ q ∈ l.foldl spStep acc, q ∈ acc ∨ q ∈ l := by
  induction l generalizing acc with
  | nil => intro q hq; exact Or.inl hq
  | cons p l ih =>
    intro q hq
    rcases ih _ q hq with h | h
    · unfold spStep at h
      split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.2 (Or.inl (List.mem_singleton.1 h)))
    · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem sp_ne {g : Graph k n} {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) :
    p.1 ≠ p.2.1 := by
  obtain ⟨hq, -, -⟩ := mem_splitPairs.1 hp
  unfold spUniq at hq
  rcases foldl_spStep_subset _ [] _ hq with h | h
  · simp at h
  · unfold spCand at h
    obtain ⟨c, -, hc⟩ := List.mem_filterMap.1 h
    split_ifs at hc with hcc
    · have h1 := Option.some.inj hc
      have h2 : c.x = p.1 := congrArg Prod.fst h1
      have h3 : c.y = p.2.1 := congrArg Prod.snd h1
      have : c.x ≠ c.y := by simpa using (by simpa using hcc : _ ∧ c.x ≠ c.y).2
      rw [h2, h3] at this
      exact this

private theorem card_le_of_twins {m : ℕ} (g : Fin n → Fin m) (hg : Function.Surjective g)
    (T : Finset (Fin n)) (htw : ∀ v ∈ T, ∃ u, u ∉ T ∧ g u = g v) : m + T.card ≤ n := by
  classical
  have himg : Finset.univ.image g ⊆ (Tᶜ).image g := by
    intro j _
    obtain ⟨v, rfl⟩ := hg j
    by_cases hv : v ∈ T
    · obtain ⟨u, hu, hgu⟩ := htw v hv
      exact Finset.mem_image.2 ⟨u, by simpa using hu, hgu⟩
    · exact Finset.mem_image.2 ⟨v, by simpa using hv, rfl⟩
  have h1 : (Finset.univ : Finset (Fin m)) ⊆ (Tᶜ).image g := by
    intro j hj
    exact himg (Finset.mem_image.2 ⟨(hg j).choose, Finset.mem_univ _, (hg j).choose_spec⟩)
  have h2 := Finset.card_le_card h1
  have h3 := Finset.card_image_le (s := Tᶜ) (f := g)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h4 := Finset.card_compl T
  rw [Fintype.card_fin] at h4
  have h5 := Finset.card_le_univ T
  rw [Fintype.card_fin] at h5
  omega

private theorem pair_dot_mem {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) (hpA : p ∈ A) :
    mkC .dot p.1 p.2.1 ∈ (g.dotChoice g.splitPairs A).comps := by
  rw [dotChoice_eq]
  exact List.mem_append_right _ (mem_addedComps.2 ⟨p, hp, Or.inl ⟨hpA, rfl⟩⟩)

private theorem pair_rep {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) (hpA : p ∈ A) :
    (g.dotChoice g.splitPairs A).mrep p.1 = (g.dotChoice g.splitPairs A).mrep p.2.1 :=
  (g.dotChoice g.splitPairs A).mrep_dot (pair_dot_mem hp hpA) rfl

private theorem odK_pos {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)} {t : Tracked k n}
    {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) (hpA : p ∈ A)
    (hf : t.f p.1 ≠ t.f p.2.1) : 1 ≤ odK g A t := by
  unfold odK
  apply List.length_pos_of_mem (a := mkC .dot p.1 p.2.1)
  rw [List.mem_filter]
  refine ⟨mem_addedComps.2 ⟨p, hp, Or.inl ⟨hpA, rfl⟩⟩, ?_⟩
  simp [mkC, hf]

private theorem MergeSpec.g_eq {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    {g : Fin n → Fin t.nOut} (hg : ∀ i, t.f (.inr i) = .inr (g i)) {i j : Fin n}
    (hr : h.mrep (.inr i) = h.mrep (.inr j)) : g i = g j := by
  have := hs.f_eq _ _ hr rfl rfl
  rw [hg, hg] at this
  exact Sum.inr.inj this

/-- Two distinct internal atoms in one dot block make `n - nOut` positive. -/
private theorem MergeSpec.r_one {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t) {i j : Fin n}
    (hij : i ≠ j) (hr : h.mrep (.inr i) = h.mrep (.inr j)) : t.nOut + 1 ≤ n := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hgij := hs.g_eq hg hr
  have := card_le_of_twins g hgs {j}
    (fun v hv => ⟨i, by simpa [Finset.mem_singleton.1 hv] using hij,
      by rw [Finset.mem_singleton.1 hv]; exact hgij⟩)
  simpa using this

private theorem Kr_pos {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)} {t : Tracked k n}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) {p : Atom k n × Atom k n × Bool}
    (hp : p ∈ g.splitPairs) (hpA : p ∈ A) : 1 ≤ odK g A t + (n - t.nOut) := by
  have hs := mergeT_spec hm
  by_cases hf : t.f p.1 = t.f p.2.1
  · have hne := sp_ne hp
    have hr := pair_rep hp hpA
    obtain ⟨g', hg', -⟩ := hs.f_inr
    have hle := hs.nOut_le
    rcases h1 : p.1 with a | i <;> rcases h2 : p.2.1 with b | j
    · rw [h1, h2] at hf hne
      rw [hs.f_inl, hs.f_inl] at hf
      exact absurd (by simpa using hf) hne
    · rw [h1, h2] at hf
      rw [hs.f_inl, hg'] at hf
      simp at hf
    · rw [h1, h2] at hf
      rw [hs.f_inl, hg'] at hf
      simp at hf
    · rw [h1, h2] at hne hr
      have hij : i ≠ j := fun h => hne (by rw [h])
      have := hs.r_one hij hr
      omega
  · have := odK_pos hp hpA hf
    omega

end MergeOrder

/-! ## Orders and weight counts of lists of components -/

section Lists

variable {V : Type*}

/-- The sum of the scaling orders of a list of components. -/
private def ordL (cs : List (Comp V)) : ℤ := (cs.map fun c => c.kind.ord).sum

@[simp] private theorem ordL_nil : ordL ([] : List (Comp V)) = 0 := rfl

@[simp] private theorem ordL_cons (c : Comp V) (cs : List (Comp V)) :
    ordL (c :: cs) = c.kind.ord + ordL cs := by simp [ordL]

@[simp] private theorem ordL_append (cs cs' : List (Comp V)) :
    ordL (cs ++ cs') = ordL cs + ordL cs' := by simp [ordL]

private theorem Graph.ord_eq {k n : ℕ} (Γ : Graph k n) : Γ.ord = ordL Γ.comps - 2 * n := rfl

end Lists

/-! ## The order of `O_dot`: the solid edges inside a block -/

section OC

variable {k n : ℕ}

/-- The solid edges without a `×`-dotted partner. -/
def unpartL (g : Graph k n) : List (Comp (Atom k n)) :=
  g.comps.filter fun c => c.kind.isSolid && !partnered g c

/-- The solid edges whose ends are in one dot block of `h`. -/
private def convS (g h : Graph k n) : List (Comp (Atom k n)) :=
  g.comps.filter fun c => c.kind.isSolid && h.mrep c.x == h.mrep c.y

private theorem odConv_dotChoice (g : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    odConv (g.dotChoice SP A) = (convS g (g.dotChoice SP A)).length := by
  unfold odConv convS
  have hcomps : (g.dotChoice SP A).comps = keptComps g SP ++ addedComps SP A := rfl
  rw [hcomps, List.filter_append, List.length_append]
  have hadd : (addedComps SP A).filter
      (fun c => c.kind.isSolid &&
        (g.dotChoice SP A).mrep c.x == (g.dotChoice SP A).mrep c.y) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    rcases (addedComps_label hc).2 with h | h <;> simp [h, Kind.isSolid]
  rw [hadd, List.length_nil, add_zero]
  unfold keptComps
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hs : c.kind.isSolid = true
  · have : (c.kind == .xdot) = false := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    simp [this]
  · simp [hs]

private theorem convS_eq_filter_unpart {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (g.dotChoice g.splitPairs A).mergeT = some t) :
    convS g (g.dotChoice g.splitPairs A) = (unpartL g).filter
      (fun c => (g.dotChoice g.splitPairs A).mrep c.x ==
        (g.dotChoice g.splitPairs A).mrep c.y) := by
  have hms := mergeT_spec hm
  set h := g.dotChoice g.splitPairs A with hh
  have hcomps : h.comps = keptComps g g.splitPairs ++ addedComps g.splitPairs A := rfl
  unfold convS unpartL
  rw [List.filter_filter]
  apply List.filter_congr
  intro c hc
  rw [Bool.eq_iff_iff]
  constructor
  · intro hP
    simp only [Bool.and_eq_true, beq_iff_eq] at hP
    have : partnered g c = false := by
      by_contra hpart
      have hpart' : partnered g c = true := by simpa using hpart
      obtain ⟨c₃, hc₃, hk₃, hsp⟩ := (partnered_iff g c).1 hpart'
      have hc₃' : c₃ ∈ h.comps := by
        rw [hcomps]
        exact List.mem_append_left _ (xdot_kept hc hP.1 hc₃ hk₃ hsp)
      have := hms.xdot_ne c₃ hc₃' hk₃
      unfold SamePair at hsp
      rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at this
        exact this hP.2
      · rw [h1, h2] at this
        exact this hP.2.symm
    simp [hP.1, hP.2, this]
  · intro hP
    simp only [Bool.and_eq_true, beq_iff_eq] at hP ⊢
    exact ⟨hP.2.1, hP.1⟩

private theorem convS_sub_unpart {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n} (hm : (g.dotChoice g.splitPairs A).mergeT = some t) :
    List.Sublist (convS g (g.dotChoice g.splitPairs A)) (unpartL g) := by
  rw [convS_eq_filter_unpart hm]
  exact List.filter_sublist

private theorem two_le_length_of_ne {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 2 ≤ l.length := by
  classical
  have : ({a, b} : Finset α) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [*]
  have h2 := Finset.card_le_card this
  rw [Finset.card_pair hab] at h2
  exact h2.trans (List.toFinset_card_le l)

private theorem dot_in_filter {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t)
    {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) (hpA : p ∈ A)
    (hext : p.1.isRight = false ∨ p.2.1.isRight = false) :
    mkC .dot p.1 p.2.1 ∈ (addedComps g.splitPairs A).filter
      (fun c => c.kind == .dot && t.f c.x != t.f c.y) := by
  have hs := mergeT_spec hm
  have hne := sp_ne hp
  have hf : t.f p.1 ≠ t.f p.2.1 := hs.old_dot_ne (c := mkC .dot p.1 p.2.1) hne hext
  rw [List.mem_filter]
  refine ⟨mem_addedComps.2 ⟨p, hp, Or.inl ⟨hpA, rfl⟩⟩, ?_⟩
  simp [mkC, hf]

private theorem internal_pair {g : Graph k n} {A : List (Atom k n × Atom k n × Bool)}
    {t : Tracked k n}
    (_hm : (g.dotChoice g.splitPairs A).mergeT = some t)
    {p : Atom k n × Atom k n × Bool} (hp : p ∈ g.splitPairs) (hpA : p ∈ A)
    (hint : p.1.isRight = true ∧ p.2.1.isRight = true) :
    ∃ i j : Fin n, i ≠ j ∧ p.1 = .inr i ∧ p.2.1 = .inr j ∧
      (g.dotChoice g.splitPairs A).mrep (.inr i) = (g.dotChoice g.splitPairs A).mrep (.inr j) := by
  have hne := sp_ne hp
  have hr := pair_rep hp hpA
  rcases h1 : p.1 with a | i <;> rcases h2 : p.2.1 with b | j
  · rw [h1] at hint; simp at hint
  · rw [h1] at hint; simp at hint
  · rw [h2] at hint; simp at hint
  · rw [h1, h2] at hne hr
    exact ⟨i, j, fun h => hne (by rw [h]), rfl, rfl, hr⟩

private theorem r_two_pairs {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (h1 : h.mrep (.inr a) = h.mrep (.inr b))
    (h2 : h.mrep (.inr c) = h.mrep (.inr d))
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) : t.nOut + 2 ≤ n := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have g1 := hs.g_eq hg h1
  have g2 := hs.g_eq hg h2
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun hbd => hne (Or.inl ⟨rfl, hbd⟩)
    have := card_le_of_twins g hgs {b, d} (fun v hv => by
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hcd⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1
        · exact g2)
    simpa [Finset.card_pair hbd] using this
  by_cases had : a = d
  · subst had
    have hbc : b ≠ c := fun hbc => hne (Or.inr ⟨rfl, hbc⟩)
    have := card_le_of_twins g hgs {b, c} (fun v hv => by
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, fun h => hcd h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1
        · exact g2.symm)
    simpa [Finset.card_pair hbc] using this
  by_cases hbc : b = c
  · subst hbc
    have had : a ≠ d := had
    have := card_le_of_twins g hgs {a, d} (fun v hv => by
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hab h.symm, hcd⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1.symm
        · exact g2)
    simpa [Finset.card_pair had] using this
  by_cases hbd : b = d
  · subst hbd
    have hac' : a ≠ c := hac
    have := card_le_of_twins g hgs {a, c} (fun v hv => by
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hab h.symm, fun h => hcd h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1.symm
        · exact g2.symm)
    simpa [Finset.card_pair hac'] using this
  · have had' : a ≠ d := had
    have hbd' : b ≠ d := hbd
    have := card_le_of_twins g hgs {b, d} (fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · refine ⟨a, ?_, g1⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, had'⟩
      · refine ⟨c, ?_, g2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hbc h.symm, hcd⟩)
    simpa [Finset.card_pair hbd'] using this

private theorem samePair_of_pairs {c₁ c₂ : Comp (Atom k n)} {p₁ p₂ : Atom k n × Atom k n × Bool}
    (hm₁ : p₁.1 = c₁.x ∧ p₁.2.1 = c₁.y ∨ p₁.1 = c₁.y ∧ p₁.2.1 = c₁.x)
    (hm₂ : p₂.1 = c₂.x ∧ p₂.2.1 = c₂.y ∨ p₂.1 = c₂.y ∧ p₂.2.1 = c₂.x)
    (h : (p₁.1 = p₂.1 ∧ p₁.2.1 = p₂.2.1) ∨ (p₁.1 = p₂.2.1 ∧ p₁.2.1 = p₂.1)) :
    SamePair c₁ c₂ := by
  unfold SamePair
  rcases hm₁ with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hm₂ with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

private theorem two_pairs {g : Graph k n} (hsl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {A : List (Atom k n × Atom k n × Bool)} {t : Tracked k n}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) {c₁ c₂ : Comp (Atom k n)}
    (h₁ : c₁ ∈ convS g (g.dotChoice g.splitPairs A))
    (h₂ : c₂ ∈ convS g (g.dotChoice g.splitPairs A)) (hne : ¬ SamePair c₁ c₂) :
    2 ≤ odK g A t + (n - t.nOut) := by
  have hs := mergeT_spec hm
  have hle := hs.nOut_le
  unfold convS at h₁ h₂
  rw [List.mem_filter] at h₁ h₂
  simp only [Bool.and_eq_true, beq_iff_eq] at h₁ h₂
  obtain ⟨hc₁, hs₁, hr₁⟩ := h₁
  obtain ⟨hc₂, hs₂, hr₂⟩ := h₂
  obtain ⟨p₁, hp₁, hpA₁, -, hm₁⟩ := solid_conv_pair hm hc₁ hs₁ (hsl c₁ hc₁ hs₁) hr₁
  obtain ⟨p₂, hp₂, hpA₂, -, hm₂⟩ := solid_conv_pair hm hc₂ hs₂ (hsl c₂ hc₂ hs₂) hr₂
  have hdne : ¬ ((p₁.1 = p₂.1 ∧ p₁.2.1 = p₂.2.1) ∨ (p₁.1 = p₂.2.1 ∧ p₁.2.1 = p₂.1)) :=
    fun h => hne (samePair_of_pairs hm₁ hm₂ h)
  by_cases e₁ : p₁.1.isRight = false ∨ p₁.2.1.isRight = false <;>
    by_cases e₂ : p₂.1.isRight = false ∨ p₂.2.1.isRight = false
  · have d₁ := dot_in_filter hm hp₁ hpA₁ e₁
    have d₂ := dot_in_filter hm hp₂ hpA₂ e₂
    have hdd : mkC .dot p₁.1 p₁.2.1 ≠ (mkC .dot p₂.1 p₂.2.1 : Comp (Atom k n)) := by
      intro h
      simp only [mkC, Comp.mk.injEq, true_and, and_true] at h
      exact hdne (Or.inl h)
    have := two_le_length_of_ne d₁ d₂ hdd
    unfold odK
    omega
  · have d₁ := dot_in_filter hm hp₁ hpA₁ e₁
    have hint : p₂.1.isRight = true ∧ p₂.2.1.isRight = true := by
      push Not at e₂
      simpa using e₂
    obtain ⟨i, j, hij, -, -, hr⟩ := internal_pair hm hp₂ hpA₂ hint
    have h1 := hs.r_one hij hr
    have h2 : 1 ≤ odK g A t := List.length_pos_of_mem d₁
    omega
  · have d₂ := dot_in_filter hm hp₂ hpA₂ e₂
    have hint : p₁.1.isRight = true ∧ p₁.2.1.isRight = true := by
      push Not at e₁
      simpa using e₁
    obtain ⟨i, j, hij, -, -, hr⟩ := internal_pair hm hp₁ hpA₁ hint
    have h1 := hs.r_one hij hr
    have h2 : 1 ≤ odK g A t := List.length_pos_of_mem d₂
    omega
  · have hint₁ : p₁.1.isRight = true ∧ p₁.2.1.isRight = true := by
      push Not at e₁
      simpa using e₁
    have hint₂ : p₂.1.isRight = true ∧ p₂.2.1.isRight = true := by
      push Not at e₂
      simpa using e₂
    obtain ⟨i, j, hij, hi, hj, hr⟩ := internal_pair hm hp₁ hpA₁ hint₁
    obtain ⟨i', j', hij', hi', hj', hr'⟩ := internal_pair hm hp₂ hpA₂ hint₂
    have h := r_two_pairs hs hij hij' hr hr' (by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hdne (Or.inl ⟨by rw [hi, hi', h1], by rw [hj, hj', h2]⟩)
      · exact hdne (Or.inr ⟨by rw [hi, hj', h1], by rw [hj, hi', h2]⟩))
    omega

/-- The order of `O_dot` on a graph with at most three solid edges without `×`-dotted partner,
not all on one pair of atoms when there are three. -/
private theorem dot_order {g : Graph k n} (hd : DotOK g)
    (hsl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hU : (unpartL g).length ≤ 4)
    (hU3 : ∀ L : List (Comp (Atom k n)), L.Sublist (unpartL g) → 3 ≤ L.length →
      ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂)
    {A : List (Atom k n × Atom k n × Bool)} (hA : List.Sublist A g.splitPairs) {t : Tracked k n}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) :
    ∃ K r e : ℕ, t.g.ord = g.ord + 2 * ((K : ℤ) + r) - e ∧ K = odK g A t ∧ r = n - t.nOut ∧
      e = (convS g (g.dotChoice g.splitPairs A)).length ∧ e ≤ 2 * (K + r) ∧ (1 ≤ e → 1 ≤ K + r) ∧
      (K + r = 0 → A = []) := by
  have hs := mergeT_spec hm
  have hle := hs.nOut_le
  have hsub := convS_sub_unpart hm
  have hordeq := merge_ord_eq hd hm
  rw [odConv_dotChoice] at hordeq
  have he_le : (convS g (g.dotChoice g.splitPairs A)).length ≤ (unpartL g).length :=
    hsub.length_le
  have hpos : 1 ≤ (convS g (g.dotChoice g.splitPairs A)).length → 1 ≤ odK g A t + (n - t.nOut) := by
    intro he
    obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos he
    have hc' := hc
    unfold convS at hc'
    rw [List.mem_filter] at hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨hcg, hsc, hrc⟩ := hc'
    obtain ⟨p, hp, hpA, -, -⟩ := solid_conv_pair hm hcg hsc (hsl c hcg hsc) hrc
    exact Kr_pos hm hp hpA
  refine ⟨odK g A t, n - t.nOut, (convS g (g.dotChoice g.splitPairs A)).length, ?_, rfl, rfl,
    rfl, ?_, hpos, ?_⟩
  · rw [hordeq]
    push_cast [Nat.cast_sub hle]
    ring
  · set e := (convS g (g.dotChoice g.splitPairs A)).length with he
    by_cases h0 : e = 0
    · omega
    · have h1 := hpos (by omega)
      by_cases h3 : 3 ≤ e
      · obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := hU3 _ hsub h3
        have := two_pairs hsl hm hc₁ hc₂ hne
        omega
      · omega
  · intro h0
    by_contra hne
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    have := Kr_pos hm (hA.subset hp) hp
    omega

/-- The graphs of `O_dot` of order at most that of the input, when at most two solid edges have no
`×`-dotted partner: either no dotted edge is added and no internal atoms are identified, or the
two solid edges lie on one pair of atoms and are both inside a dot block. -/
private theorem dot_eq {g : Graph k n} (hd : DotOK g)
    (hsl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hU2 : (unpartL g).length ≤ 2)
    {A : List (Atom k n × Atom k n × Bool)} (hA : List.Sublist A g.splitPairs) {t : Tracked k n}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) (hle : t.g.ord ≤ g.ord) :
    (A = [] ∧ t.nOut = n ∧ convS g (g.dotChoice g.splitPairs A) = []) ∨
    (∃ c₁ c₂, unpartL g = [c₁, c₂] ∧ SamePair c₁ c₂ ∧
      convS g (g.dotChoice g.splitPairs A) = [c₁, c₂] ∧ odK g A t + (n - t.nOut) = 1 ∧
      ∃ p ∈ g.splitPairs, p ∈ A ∧ (p.1 = c₁.x ∧ p.2.1 = c₁.y ∨ p.1 = c₁.y ∧ p.2.1 = c₁.x)) := by
  have hs := mergeT_spec hm
  have hnle := hs.nOut_le
  obtain ⟨K, r, e, hord, hK, hr, he, hle2, hpos, hz⟩ :=
    dot_order hd hsl (by omega) (fun L hL h3 => by have := hL.length_le; omega) hA hm
  have hsub := convS_sub_unpart hm
  have he_le : e ≤ (unpartL g).length := by rw [he]; exact hsub.length_le
  have heq : (e : ℤ) = 2 * ((K : ℤ) + r) := by
    have : (e : ℤ) ≤ 2 * ((K : ℤ) + r) := by exact_mod_cast hle2
    linarith
  have heq' : e = 2 * (K + r) := by exact_mod_cast heq
  by_cases h0 : K + r = 0
  · left
    refine ⟨hz h0, by omega, ?_⟩
    rw [← List.length_eq_zero_iff, ← he]
    omega
  · right
    have he2 : e = 2 := by omega
    have hKr : K + r = 1 := by omega
    have hU : (unpartL g).length = 2 := by omega
    obtain ⟨c₁, c₂, hUc⟩ := List.length_eq_two.1 hU
    have hEq : convS g (g.dotChoice g.splitPairs A) = unpartL g :=
      hsub.eq_of_length (by omega)
    have hm₁ : c₁ ∈ convS g (g.dotChoice g.splitPairs A) := by rw [hEq, hUc]; simp
    have hm₂ : c₂ ∈ convS g (g.dotChoice g.splitPairs A) := by rw [hEq, hUc]; simp
    have hsp : SamePair c₁ c₂ := by
      by_contra hne
      have := two_pairs hsl hm hm₁ hm₂ hne
      omega
    refine ⟨c₁, c₂, hUc, hsp, by rw [hEq, hUc], by rw [← hK, ← hr]; exact hKr, ?_⟩
    have hc' := hm₁
    unfold convS at hc'
    rw [List.mem_filter] at hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨hcg, hsc, hrc⟩ := hc'
    obtain ⟨p, hp, hpA, -, hmm⟩ := solid_conv_pair hm hcg hsc (hsl c₁ hcg hsc) hrc
    exact ⟨p, hp, hpA, hmm⟩

end OC

/-! ## Complex conjugation of graphs: invariant properties -/

section ConjInv

variable {k n : ℕ}

/-- The complex conjugate of one component. -/
private def Comp.conj {V : Type*} (c : Comp V) : Comp V := { c with kind := c.kind.conj }

private theorem Graph.conj_comps (Γ : Graph k n) : Γ.conj.comps = Γ.comps.map Comp.conj := rfl

private theorem Kind.conj_isSolid (κ : Kind) : κ.conj.isSolid = κ.isSolid := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isSolid]

private theorem Kind.conj_isRandom (κ : Kind) : κ.conj.isRandom = κ.isRandom := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isRandom]

private theorem Kind.conj_isWeight (κ : Kind) : κ.conj.isWeight = κ.isWeight := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isWeight]

private theorem Kind.conj_joinsMol (κ : Kind) : κ.conj.joinsMol = κ.joinsMol := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.joinsMol]

private theorem Kind.conj_isDiffusive (κ : Kind) : κ.conj.isDiffusive = κ.isDiffusive := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.isDiffusive]

private theorem Kind.conj_ord (κ : Kind) : κ.conj.ord = κ.ord := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj, Kind.ord]

private theorem Kind.conj_eq_dot (κ : Kind) : κ.conj = .dot ↔ κ = .dot := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

private theorem Kind.conj_eq_xdot (κ : Kind) : κ.conj = .xdot ↔ κ = .xdot := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

private theorem Kind.conj_waved (κ : Kind) : (∃ w, κ.conj = .waved w) ↔ ∃ w, κ = .waved w := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

private theorem Kind.conj_inv (κ : Kind) : (∃ ch, κ.conj = .inv ch) ↔ ∃ ch, κ = .inv ch := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

private theorem Kind.conj_wD (κ : Kind) : (∃ ch d, κ.conj = .wD ch d) ↔ ∃ ch d, κ = .wD ch d := by
  cases κ <;> (try cases ‹Wave›) <;> simp [Kind.conj]

@[simp] private theorem Comp.conj_x {V : Type*} (c : Comp V) : c.conj.x = c.x := rfl

@[simp] private theorem Comp.conj_y {V : Type*} (c : Comp V) : c.conj.y = c.y := rfl

@[simp] private theorem Comp.conj_label {V : Type*} (c : Comp V) : c.conj.label = c.label := rfl

@[simp] private theorem Comp.conj_kind {V : Type*} (c : Comp V) : c.conj.kind = c.kind.conj := rfl

private theorem Graph.mem_conj_comps {Γ : Graph k n} {c' : Comp (Atom k n)} :
    c' ∈ Γ.conj.comps ↔ ∃ c ∈ Γ.comps, c' = c.conj := by
  rw [Graph.conj_comps, List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

private theorem Graph.conj_ord (Γ : Graph k n) : Γ.conj.ord = Γ.ord := by
  unfold Graph.ord
  simp only [Graph.conj_comps, List.map_map, Function.comp_def, Comp.conj_kind, Kind.conj_ord]

private theorem Graph.conj_length (Γ : Graph k n) : Γ.conj.comps.length = Γ.comps.length := by
  simp [Graph.conj_comps]

private theorem Graph.conj_labels (Γ : Graph k n) : Γ.conj.labels = Γ.labels := by
  unfold Graph.labels
  simp only [Graph.conj_comps]
  congr 1
  induction Γ.comps with
  | nil => rfl
  | cons c cs ih => simp [List.filterMap_cons, ih]

private theorem Graph.conj_wt (Γ : Graph k n) (u : Atom k n) : Γ.conj.wt u = Γ.wt u := by
  unfold Graph.wt
  simp only [Graph.conj_comps, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro c _
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Wave›) <;> simp [Comp.conj, Kind.conj]

private theorem Graph.conj_edgeGraph (Γ : Graph k n) : Γ.conj.edgeGraph = Γ.edgeGraph := by
  unfold Graph.edgeGraph
  congr 1
  funext u v
  apply propext
  simp only [Graph.mem_conj_comps]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h1, h2⟩; exact ⟨c, hc, h1, h2⟩
  · rintro ⟨c, hc, h1, h2⟩; exact ⟨c.conj, ⟨c, hc, rfl⟩, h1, h2⟩

private theorem Graph.conj_edgeGraphNoX (Γ : Graph k n) : Γ.conj.edgeGraphNoX = Γ.edgeGraphNoX := by
  unfold Graph.edgeGraphNoX
  congr 1
  funext u v
  apply propext
  simp only [Graph.mem_conj_comps]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h0, h1, h2⟩
    refine ⟨c, hc, fun h => h0 ?_, h1, h2⟩
    simp [h, Kind.conj]
  · rintro ⟨c, hc, h0, h1, h2⟩
    refine ⟨c.conj, ⟨c, hc, rfl⟩, fun h => h0 ?_, h1, h2⟩
    simpa [Kind.conj_eq_xdot] using h

private theorem Graph.conj_wavedThetaGraph (Γ : Graph k n) :
    Γ.conj.wavedThetaGraph = Γ.wavedThetaGraph := by
  unfold Graph.wavedThetaGraph
  congr 1
  funext u v
  apply propext
  simp only [Graph.mem_conj_comps]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h0, h1, h2⟩
    refine ⟨c, hc, ?_, h1, h2⟩
    simpa [Kind.conj_joinsMol, Kind.conj_eq_dot, Kind.conj_isDiffusive] using h0
  · rintro ⟨c, hc, h0, h1, h2⟩
    refine ⟨c.conj, ⟨c, hc, rfl⟩, ?_, h1, h2⟩
    simpa [Kind.conj_joinsMol, Kind.conj_eq_dot, Kind.conj_isDiffusive] using h0

private theorem Graph.conj_wavedGraph (Γ : Graph k n) : Γ.conj.wavedGraph = Γ.wavedGraph := by
  unfold Graph.wavedGraph
  congr 1
  funext u v
  apply propext
  simp only [Graph.mem_conj_comps]
  constructor
  · rintro ⟨c', ⟨c, hc, rfl⟩, h0, h1, h2⟩
    refine ⟨c, hc, ?_, h1, h2⟩
    simpa [Kind.conj_waved] using h0
  · rintro ⟨c, hc, h0, h1, h2⟩
    refine ⟨c.conj, ⟨c, hc, rfl⟩, ?_, h1, h2⟩
    simpa [Kind.conj_waved] using h0

private theorem Graph.conj_Regular {C : ℕ} {Γ : Graph k n} (h : Γ.Regular C)
    : Γ.conj.Regular C := by
  refine ⟨by rw [Graph.conj_length]; exact h.size, ?_, ?_, ?_⟩
  · rw [Graph.conj_edgeGraph]; exact h.connected
  · intro a b; rw [Graph.conj_wavedThetaGraph]; exact h.internal a b
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.noIntDot c hc ((Kind.conj_eq_dot _).1 hk)

private theorem Graph.conj_Normal {C : ℕ} {Γ : Graph k n} (h : Γ.Normal C) : Γ.conj.Normal C := by
  obtain ⟨hr, hs, hx⟩ := h
  refine ⟨Graph.conj_Regular hr, ?_, ?_⟩
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact hs c hc (by simpa [Kind.conj_isSolid] using hk)
  · intro u v huv
    have h := hx u v huv
    simp only [Graph.mem_conj_comps]
    constructor
    · rintro ⟨c', ⟨c, hc, rfl⟩, hk, hm⟩
      obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := h.1 ⟨c, hc, by simpa [Kind.conj_eq_xdot] using hk, hm⟩
      exact ⟨c₂.conj, ⟨c₂, hc₂, rfl⟩, by simpa [Kind.conj_isSolid] using hk₂, hm₂⟩
    · rintro ⟨c', ⟨c, hc, rfl⟩, hk, hm⟩
      obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := h.2 ⟨c, hc, by simpa [Kind.conj_isSolid] using hk, hm⟩
      exact ⟨c₂.conj, ⟨c₂, hc₂, rfl⟩, by simpa [Kind.conj_eq_xdot] using hk₂, hm₂⟩

private theorem Graph.conj_Plain {Γ : Graph k n} (h : Γ.Plain) : Γ.conj.Plain := by
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h c hc
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch hk
    have : ∃ ch', c.conj.kind = .inv ch' := ⟨ch, hk⟩
    obtain ⟨ch', hch'⟩ := (Kind.conj_inv c.kind).1 this
    exact h2 ch' hch'
  · intro ch d hk
    have : ∃ ch' d', c.conj.kind = .wD ch' d' := ⟨ch, d, hk⟩
    obtain ⟨ch', d', hch'⟩ := (Kind.conj_wD c.kind).1 this
    exact h3 ch' d' hch'
  · intro hk
    exact h4 ((Kind.conj_eq_dot _).1 hk)
  · intro hw
    rw [Comp.conj_kind, Kind.conj_isWeight] at hw
    exact h5 hw
  · intro hl
    rw [Comp.conj_kind, Kind.conj_isRandom]
    exact h6 hl

end ConjInv

/-! ## Lists of components: erasing, lifting, labelling, derivatives -/

section Lists2

variable {V : Type*}

private theorem eraseIdx_map {W : Type*} (f : Comp V → Comp W) (l : List (Comp V)) (j : ℕ) :
    (l.map f).eraseIdx j = (l.eraseIdx j).map f := by
  induction l generalizing j with
  | nil => simp
  | cons c l ih =>
    cases j with
    | zero => simp
    | succ j => simp [ih]

end Lists2

section LiftLabel

variable {k n : ℕ}

private theorem liftCs_length (j : ℕ) (cs : List (Comp (Atom k n))) :
    (liftCs j cs).length = cs.length := by
  simp [liftCs]

private theorem ordL_liftCs (j : ℕ) (cs : List (Comp (Atom k n))) : ordL
    (liftCs j cs) = ordL cs := by
  simp [liftCs, ordL, Comp.map, List.map_map, Function.comp_def]

private theorem liftA_injective (j : ℕ) : Function.Injective (liftA (k := k) (n := n) j) := by
  intro u v h
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [liftA, Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, Sum.inr.injEq,
      Fin.castAdd_inj, reduceCtorEq] at h ⊢ <;> exact h

private theorem liftA_isLeft (j : ℕ) (u : Atom k n) : (liftA j u).isLeft = u.isLeft := by
  rcases u with a | a <;> simp [liftA]

private theorem liftA_ne_newA (j : ℕ) (u : Atom k n) (i : Fin j) : liftA j u ≠ newA i := by
  rcases u with a | a
  · simp [liftA, newA]
  · intro h
    have := congrArg Fin.val (Sum.inr.inj h)
    simp at this
    have := a.isLt
    omega

private theorem mem_liftCs {j : ℕ} {cs : List (Comp (Atom k n))} {c' : Comp (Atom k (n + j))} :
    c' ∈ liftCs j cs ↔ ∃ c ∈ cs, c' = c.map (liftA j) := by
  unfold liftCs
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

private theorem ordL_labelQs {V : Type*} (u : V) (cs : List (Comp V)) : ordL
    (labelQs u cs) = ordL cs := by
  unfold labelQs ordL
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, Comp.labelQ]
  split_ifs <;> rfl

private theorem labelQs_length {V : Type*} (u : V) (cs : List (Comp V)) :
    (labelQs u cs).length = cs.length := by simp [labelQs]

private theorem mem_labelQs {V : Type*} {u : V} {cs : List (Comp V)} {c' : Comp V} :
    c' ∈ labelQs u cs ↔ ∃ c ∈ cs, c' = c.labelQ u := by
  unfold labelQs
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩

end LiftLabel

section DTermsFacts

variable {V : Type*} [DecidableEq V]

private theorem mem_dTerms {p q : V} {cs : List (Comp V)} {d : List (Comp V)} :
    d ∈ dTerms p q cs ↔ ∃ j, ∃ (hj : j < cs.length), ∃ ps, (cs[j]).dPieces p q = some ps ∧
      d = cs.eraseIdx j ++ ps := by
  unfold dTerms
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hi
    exact ⟨i.1, i.2, ps, hps, rfl⟩
  · rintro ⟨j, hj, ps, hps, rfl⟩
    refine ⟨⟨j, hj⟩, List.mem_finRange _, ?_⟩
    simp [hps]

private theorem dPieces_random {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps) :
    (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) := by
  unfold Comp.dPieces at h
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp_all

private theorem dPieces_length {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps) :
    ps.length = 2 := by
  unfold Comp.dPieces at h
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Charge›) <;> simp_all <;> subst h <;> rfl

end DTermsFacts

/-! ## Reachability in the graphs of a list of components -/

section Reach

variable {k n : ℕ}

private theorem reach_map {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} (φ : α → β)
    (h : ∀ a b, G.Adj a b → H.Reachable (φ a) (φ b)) {u v : α} (huv : G.Reachable u v) :
    H.Reachable (φ u) (φ v) := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

private theorem atom_cases {j : ℕ} (u : Atom k (n + j)) :
    (∃ v : Atom k n, u = liftA j v) ∨ ∃ i : Fin j, u = newA i := by
  rcases u with a | i
  · exact Or.inl ⟨.inl a, rfl⟩
  · by_cases h : i.val < n
    · left
      exact ⟨.inr ⟨i.val, h⟩, by simp [liftA]⟩
    · right
      refine ⟨⟨i.val - n, by omega⟩, ?_⟩
      simp only [newA, Fin.natAdd_mk, Sum.inr.injEq]
      ext
      simp only []
      omega

private theorem wavedGraph_le_wavedTheta (g : Graph k n) : g.wavedGraph ≤ g.wavedThetaGraph := by
  intro u v h
  rw [Graph.wavedGraph, SimpleGraph.fromRel_adj] at h
  rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
  refine ⟨h.1, ?_⟩
  have key : ∀ a b, (∃ c ∈ g.comps, (∃ w, c.kind = .waved w) ∧ c.x = a ∧ c.y = b) →
      ∃ c ∈ g.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = a ∧ c.y = b := by
    rintro a b ⟨c, hc, ⟨w, hw⟩, h1, h2⟩
    exact ⟨c, hc, Or.inl ⟨by simp [hw, Kind.joinsMol], by simp [hw]⟩, h1, h2⟩
  rcases h.2 with h | h
  · exact Or.inl (key _ _ h)
  · exact Or.inr (key _ _ h)

private theorem wavedGraph_le_edgeGraphNoX (g : Graph k n) : g.wavedGraph ≤ g.edgeGraphNoX := by
  intro u v h
  rw [Graph.wavedGraph, SimpleGraph.fromRel_adj] at h
  rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
  refine ⟨h.1, ?_⟩
  have key : ∀ a b, (∃ c ∈ g.comps, (∃ w, c.kind = .waved w) ∧ c.x = a ∧ c.y = b) →
      ∃ c ∈ g.comps, c.kind ≠ .xdot ∧ c.x = a ∧ c.y = b := by
    rintro a b ⟨c, hc, ⟨w, hw⟩, h1, h2⟩
    exact ⟨c, hc, by simp [hw], h1, h2⟩
  rcases h.2 with h | h
  · exact Or.inl (key _ _ h)
  · exact Or.inr (key _ _ h)

private theorem edgeGraphNoX_le_edgeGraph (g : Graph k n) : g.edgeGraphNoX ≤ g.edgeGraph := by
  intro u v h
  rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at h
  rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩
  · exact Or.inl ⟨c, hc, h1, h2⟩
  · exact Or.inr ⟨c, hc, h1, h2⟩

private theorem reach_of_comp_noX (g : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ g.comps)
    (hk : c.kind ≠ .xdot) : g.edgeGraphNoX.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩ |>.reachable

private theorem Graph.normal_connNoX {C : ℕ} {g : Graph k n} (h : g.Normal C) : g.ConnNoX := by
  obtain ⟨hr, hs, hx⟩ := h
  intro u v
  refine reach_map (G := g.edgeGraph) (H := g.edgeGraphNoX) id (fun a b hab => ?_)
    (hr.connected u v)
  rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hab
  obtain ⟨hne, hrel⟩ := hab
  have key : ∀ c ∈ g.comps, c.kind ≠ .xdot → (c.x = a ∧ c.y = b ∨ c.x = b ∧ c.y = a) →
      g.edgeGraphNoX.Reachable a b := by
    intro c hc hk hm
    have := reach_of_comp_noX g hc hk
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this; exact this
    · rw [h1, h2] at this; exact this.symm
  rcases hrel with ⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩
  · by_cases hk : c.kind = .xdot
    · obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hx a b hne).1 ⟨c, hc, hk, Or.inl ⟨h1, h2⟩⟩
      exact key c₂ hc₂ (by intro h; rw [h] at hk₂; simp [Kind.isSolid] at hk₂) hm₂
    · exact key c hc hk (Or.inl ⟨h1, h2⟩)
  · by_cases hk : c.kind = .xdot
    · obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hx a b hne).1 ⟨c, hc, hk, Or.inr ⟨h1, h2⟩⟩
      exact key c₂ hc₂ (by intro h; rw [h] at hk₂; simp [Kind.isSolid] at hk₂) hm₂
    · exact key c hc hk (Or.inr ⟨h1, h2⟩)

end Reach

/-! ## Graphs extending a graph by new atoms -/

section Ext

variable {k n : ℕ}

/-- A component that may be added to a graph: a solid edge, a weight, a light weight or a
waved edge, without minor; a weight sits on its atom, a solid edge joins two distinct atoms, only
random components are labelled. -/
private def NewOK {V : Type*} (c : Comp V) : Prop :=
  c.minor = [] ∧
  ((∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) ∨
    ∃ w, c.kind = .waved w) ∧
  (c.kind.isWeight = true → c.y = c.x) ∧ (c.kind.isSolid = true → c.x ≠ c.y) ∧
  (c.label.isSome = true → c.kind.isRandom = true)

/-- `g'` extends `g₁` along an injective map `φ` of the atoms: the non-random components of `g₁`
are kept, every component of `g'` comes from `g₁` or is new, the images of the ends of every
edge of `g₁` between distinct atoms are joined by a path (not using `×`-dotted edges), and every
atom outside the image of `φ` is joined to the image of `x` by waved edges. -/
private structure ExtData {m : ℕ} (φ : Atom k n → Atom k m) (g₁ : Graph k n) (x : Atom k n)
    (g' : Graph k m) : Prop where
  old : ∀ c ∈ g₁.comps, c.kind.isRandom = false → c.map φ ∈ g'.comps
  src : ∀ c' ∈ g'.comps, (∃ c ∈ g₁.comps, c' = c.map φ) ∨ NewOK c'
  cover : ∀ c ∈ g₁.comps, c.kind ≠ .xdot → c.x ≠ c.y →
    g'.edgeGraphNoX.Reachable (φ c.x) (φ c.y)
  attach : ∀ u : Atom k m, (∀ v, φ v ≠ u) → g'.wavedGraph.Reachable (φ x) u

private theorem kind_nonrandom_of_mol {κ : Kind}
    (h : κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) : κ.isRandom = false := by
  cases κ <;> simp_all [Kind.joinsMol, Kind.isDiffusive, Kind.isRandom]

private theorem isLeft_iff_isRight_false {V W : Type*} (u : V ⊕ W)
    : u.isLeft = true ↔ u.isRight = false := by
  cases u <;> simp

private theorem Comp.map_minor_nil {V W : Type*} (f : V → W) {c : Comp V} (h : c.minor = []) :
    (c.map f).minor = [] := by simp [Comp.map, h]

private theorem ExtData.props {C m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n} {x : Atom k n}
    {g' : Graph k m} (hφ : Function.Injective φ) (hφL : ∀ v, (φ v).isLeft = v.isLeft)
    (hN : g₁.Normal C) (hP : g₁.Plain) (hx : x.isRight = true) (E : ExtData φ g₁ x g') :
    g'.ConnNoX ∧ (∀ a b : Fin m, g'.wavedThetaGraph.Reachable (.inr a) (.inr b)) ∧
    (∀ c ∈ g'.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true) ∧
    DotOK g' ∧ (∀ c ∈ g'.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧ g'.Plain := by
  have hconn₁ := Graph.normal_connNoX hN
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : Fin n, x = .inr x₀ := by
    rcases x with a | a
    · simp at hx
    · exact ⟨a, rfl⟩
  have hint₁ := hN.1.internal
  have hnoint₁ := hN.1.noIntDot
  have hsolid₁ := hN.2.1
  have hφR : ∀ u : Atom k n, (φ u).isRight = u.isRight := by
    intro u
    have h := hφL u
    cases hφu : φ u <;> cases u <;> simp [hφu] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- connectedness without `×`-dotted edges
    have hold : ∀ v : Atom k n, g'.edgeGraphNoX.Reachable (φ (.inr x₀)) (φ v) := by
      intro v
      refine reach_map (G := g₁.edgeGraphNoX) (H := g'.edgeGraphNoX) φ (fun a b hab => ?_)
        (hconn₁ (.inr x₀) v)
      rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hab
      obtain ⟨hne, hrel⟩ := hab
      rcases hrel with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
      · have := E.cover c hc hk (by rw [h1, h2]; exact hne)
        rw [h1, h2] at this; exact this
      · have := E.cover c hc hk (by rw [h1, h2]; exact hne.symm)
        rw [h1, h2] at this; exact this.symm
    have hall : ∀ u : Atom k m, g'.edgeGraphNoX.Reachable (φ (.inr x₀)) u := by
      intro u
      by_cases hu : ∃ v, φ v = u
      · obtain ⟨v, rfl⟩ := hu
        exact hold v
      · push Not at hu
        exact (E.attach u hu).mono (wavedGraph_le_edgeGraphNoX g')
    exact fun u v => (hall u).symm.trans (hall v)
  · -- internal atoms are joined by waved and `Θ` edges
    have hold : ∀ a' : Fin n, g'.wavedThetaGraph.Reachable (φ (.inr x₀)) (φ (.inr a')) := by
      intro a'
      refine reach_map (G := g₁.wavedThetaGraph) (H := g'.wavedThetaGraph) φ
        (fun a b hab => ?_) (hint₁ x₀ a')
      rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨hne, hrel⟩ := hab
      have hne' : φ a ≠ φ b := fun h => hne (hφ h)
      rcases hrel with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
      · have hm := E.old c hc (kind_nonrandom_of_mol hk)
        refine SimpleGraph.Adj.reachable ?_
        rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne', Or.inl ⟨c.map φ, hm, ?_, by simp [Comp.map, h1], by simp [Comp.map, h2]⟩⟩
        simpa [Comp.map] using hk
      · have hm := E.old c hc (kind_nonrandom_of_mol hk)
        refine SimpleGraph.Adj.reachable ?_
        rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
        refine ⟨hne', Or.inr ⟨c.map φ, hm, ?_, by simp [Comp.map, h1], by simp [Comp.map, h2]⟩⟩
        simpa [Comp.map] using hk
    have hall : ∀ a : Fin m, g'.wavedThetaGraph.Reachable (φ (.inr x₀)) (.inr a) := by
      intro a
      by_cases hu : ∃ v, φ v = .inr a
      · obtain ⟨v, hv⟩ := hu
        rcases v with b | b
        · have := hφL (.inl b)
          rw [hv] at this
          simp at this
        · rw [← hv]; exact hold b
      · push Not at hu
        exact (E.attach _ hu).mono (wavedGraph_le_wavedTheta g')
    exact fun a b => (hall a).symm.trans (hall b)
  · intro c' hc' hk
    rcases E.src c' hc' with ⟨c, hc, rfl⟩ | hnew
    · have hkc : c.kind = .dot := by simpa [Comp.map] using hk
      rcases hnoint₁ c hc hkc with h | h
      · left; simpa [Comp.map, hφL] using h
      · right; simpa [Comp.map, hφL] using h
    · exfalso
      obtain ⟨-, hkinds, -⟩ := hnew
      rcases hkinds with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨w, h⟩ <;> rw [h] at hk <;> cases hk
  · intro c' hc' hk
    rcases E.src c' hc' with ⟨c, hc, rfl⟩ | hnew
    · have hkc : c.kind = .dot := by simpa [Comp.map] using hk
      have hne : c.x ≠ c.y := (hP c hc).2.2.2.1 hkc
      refine ⟨fun h => hne (hφ h), ?_⟩
      rcases hnoint₁ c hc hkc with h | h
      · left
        simp only [Comp.map]
        rw [hφR]
        exact (isLeft_iff_isRight_false _).1 h
      · right
        simp only [Comp.map]
        rw [hφR]
        exact (isLeft_iff_isRight_false _).1 h
    · exfalso
      obtain ⟨-, hkinds, -⟩ := hnew
      rcases hkinds with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨w, h⟩ <;> rw [h] at hk <;> cases hk
  · intro c' hc' hk
    rcases E.src c' hc' with ⟨c, hc, rfl⟩ | hnew
    · have hkc : c.kind.isSolid = true := by simpa [Comp.map] using hk
      exact fun h => hsolid₁ c hc hkc (hφ h)
    · exact hnew.2.2.2.1 hk
  · intro c' hc'
    rcases E.src c' hc' with ⟨c, hc, rfl⟩ | hnew
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP c hc
      refine ⟨Comp.map_minor_nil _ h1, ?_, ?_, ?_, ?_, ?_⟩
      · intro ch h; exact h2 ch (by simpa [Comp.map] using h)
      · intro ch d h; exact h3 ch d (by simpa [Comp.map] using h)
      · intro h
        exact fun h' => h4 (by simpa [Comp.map] using h) (hφ h')
      · intro h
        have := h5 (by simpa [Comp.map] using h)
        simp [Comp.map, this]
      · intro h
        have : c.label.isSome = true := by simpa [Comp.map] using h
        simpa [Comp.map] using h6 this
    · obtain ⟨hmi, hkinds, hw, -, hl⟩ := hnew
      refine ⟨hmi, ?_, ?_, ?_, hw, hl⟩
      · intro ch h; rcases hkinds with ⟨ch', h'⟩ | ⟨ch', h'⟩ | ⟨ch', h'⟩ | ⟨w, h'⟩ <;>
          rw [h'] at h <;> cases h
      · intro ch d h; rcases hkinds with ⟨ch', h'⟩ | ⟨ch', h'⟩ | ⟨ch', h'⟩ | ⟨w, h'⟩ <;>
          rw [h'] at h <;> cases h
      · intro h; rcases hkinds with ⟨ch', h'⟩ | ⟨ch', h'⟩ | ⟨ch', h'⟩ | ⟨w, h'⟩ <;>
          rw [h'] at h <;> cases h

end Ext

/-! ## New components, and the graphs extending a graph -/

section NewComps

variable {k n : ℕ}

/-- The optional `Q`-labelling of all random components of a list. -/
private def labW {V : Type*} : Option V → List (Comp V) → List (Comp V)
  | none, L => L
  | some u, L => labelQs u L

private theorem labW_exists {V : Type*} {o : Option V} {L : List (Comp V)} {c : Comp V}
    (hc : c ∈ L) :
    ∃ c'' ∈ labW o L, c''.x = c.x ∧ c''.y = c.y ∧ c''.kind = c.kind := by
  cases o with
  | none => exact ⟨c, hc, rfl, rfl, rfl⟩
  | some u =>
    refine ⟨c.labelQ u, mem_labelQs.2 ⟨c, hc, rfl⟩, ?_⟩
    unfold Comp.labelQ
    split_ifs <;> simp

private theorem labW_nonrandom {V : Type*} {o : Option V} {L : List (Comp V)} {c : Comp V}
    (hc : c ∈ L)
    (hr : c.kind.isRandom = false) : c ∈ labW o L := by
  cases o with
  | none => exact hc
  | some u =>
    have : c.labelQ u = c := by
      unfold Comp.labelQ
      simp [hr]
    exact mem_labelQs.2 ⟨c, hc, this.symm⟩

private theorem labW_cases {V : Type*} {o : Option V} {L : List (Comp V)} {c' : Comp V}
    (h : c' ∈ labW o L) : ∃ c ∈ L, c' = c ∨ ∃ u, c' = c.labelQ u := by
  cases o with
  | none => exact ⟨c', h, Or.inl rfl⟩
  | some u =>
    obtain ⟨c, hc, rfl⟩ := mem_labelQs.1 h
    exact ⟨c, hc, Or.inr ⟨u, rfl⟩⟩

private theorem ordL_labW {V : Type*} (o : Option V) (L : List (Comp V)) : ordL
    (labW o L) = ordL L := by
  cases o with
  | none => rfl
  | some u => exact ordL_labelQs u L

private theorem length_labW {V : Type*} (o : Option V) (L : List (Comp V)) :
    (labW o L).length = L.length := by
  cases o with
  | none => rfl
  | some u => exact labelQs_length u L

private theorem NewOK.labelQ {V : Type*} {c : Comp V} (h : NewOK c) (u : V) : NewOK
    (c.labelQ u) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold Comp.labelQ
  split_ifs with hr
  · exact ⟨h1, h2, h3, h4, fun _ => hr⟩
  · exact ⟨h1, h2, h3, h4, h5⟩

private theorem NewOK_solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    NewOK (solidC ch u v) := by
  unfold solidC
  split_ifs with h
  · exact ⟨rfl, Or.inr (Or.inl ⟨ch, rfl⟩), fun _ => rfl,
      fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩
  · exact ⟨rfl, Or.inl ⟨ch, rfl⟩, fun hw => by simp [mkC, Kind.isWeight] at hw, fun _ => h,
      fun hl => by simp [mkC] at hl⟩

private theorem NewOK_waved {V : Type*} (w : Wave) (u v : V) : NewOK (mkC (.waved w) u v) :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨w, rfl⟩)), fun hw => by simp [mkC, Kind.isWeight] at hw,
    fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩

private theorem NewOK_light {V : Type*} (ch : Charge) (u : V) : NewOK (mkC (.light ch) u u) :=
  ⟨rfl, Or.inr (Or.inr (Or.inl ⟨ch, rfl⟩)), fun _ => rfl,
    fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩

private theorem NewOK_weight {V : Type*} (ch : Charge) (u : V) : NewOK (mkC (.weight ch) u u) :=
  ⟨rfl, Or.inr (Or.inl ⟨ch, rfl⟩), fun _ => rfl,
    fun hs => by simp [mkC, Kind.isSolid] at hs, fun hl => by simp [mkC] at hl⟩

private theorem NewOK_G {V : Type*} (ch : Charge) {u v : V} (h : u ≠ v) : NewOK (mkC (.G ch) u v) :=
  ⟨rfl, Or.inl ⟨ch, rfl⟩, fun hw => by simp [mkC, Kind.isWeight] at hw, fun _ => h,
    fun hl => by simp [mkC] at hl⟩

private theorem dPieces_newOK {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)}
    (h : c.dPieces p q = some ps) : ∀ c' ∈ ps, NewOK c' := by
  unfold Comp.dPieces at h
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Charge›) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    (intro c' hc'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
     rcases hc' with rfl | rfl <;> exact NewOK_solidC _ _ _)

private theorem NewOK_map_of_old {C m : ℕ} {φ : Atom k n → Atom k m} (hφ : Function.Injective φ)
    {g₁ : Graph k n} (hN : g₁.Normal C) (hP : g₁.Plain) {c : Comp (Atom k n)}
    (hc : c ∈ g₁.comps) (hr : c.kind.isRandom = true) : NewOK (c.map φ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP c hc
  have hsol := hN.2.1 c hc
  refine ⟨Comp.map_minor_nil _ h1, ?_, ?_, ?_, ?_⟩
  · rcases c with ⟨κ, a, b, mi, l⟩
    cases κ <;> simp_all [Kind.isRandom, Comp.map]
  · intro hw
    have := h5 (by simpa [Comp.map] using hw)
    simp [Comp.map, this]
  · intro hs
    exact fun h => hsol (by simpa [Comp.map] using hs) (hφ h)
  · intro _
    simpa [Comp.map] using hr

end NewComps

section Paths

variable {V : Type*} [DecidableEq V]

private theorem solidC_x (ch : Charge) (u v : V) : (solidC ch u v).x = u := by
  unfold solidC; split_ifs <;> simp [mkC]

private theorem solidC_y (ch : Charge) (u v : V) : (solidC ch u v).y = v := by
  unfold solidC; split_ifs with h <;> simp [mkC, h]

/-- The two factors of the derivative of a solid edge, together with `G_{pq}`, join the ends of the
edge. -/
private theorem dPieces_path {G : SimpleGraph V} {p q : V} {c : Comp V} {ps : List (Comp V)}
    (hps : c.dPieces p q = some ps) (hG : ∃ ch, c.kind = .G ch)
    (hpieces : ∀ c' ∈ ps, G.Reachable c'.x c'.y) (hE : G.Reachable p q) :
    G.Reachable c.x c.y := by
  obtain ⟨ch, hch⟩ := hG
  unfold Comp.dPieces at hps
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at hch
  subst hch
  cases ch
  · simp only [Kind.isWeight, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hps
    subst hps
    have h1 := hpieces _ (List.mem_cons_self ..)
    have h2 := hpieces _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [solidC_x, solidC_y] at h1 h2
    exact h1.trans (hE.trans h2)
  · simp only [Kind.isWeight, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hps
    subst hps
    have h1 := hpieces _ (List.mem_cons_self ..)
    have h2 := hpieces _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [solidC_x, solidC_y] at h1 h2
    exact h1.trans (hE.symm.trans h2)

end Paths

section ExtLemmas

variable {k n : ℕ}

private theorem attach_of_new {j : ℕ} {g' : Graph k (n + j)} {x : Atom k n}
    (hatt : ∀ i : Fin j, g'.wavedGraph.Reachable (liftA j x) (newA i)) :
    ∀ u : Atom k (n + j), (∀ v, liftA j v ≠ u) → g'.wavedGraph.Reachable (liftA j x) u := by
  intro u hu
  rcases atom_cases (j := j) u with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · exact absurd rfl (hu v)
  · exact hatt i

private theorem reach_of_waved (g : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ g.comps)
    (hw : ∃ w, c.kind = .waved w) : g.wavedGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, hw, rfl, rfl⟩⟩ |>.reachable

end ExtLemmas

/-! ## Solid edges without `×`-dotted partner in extended graphs -/

section Unpart

variable {k n : ℕ}

/-- The number of solid edges of the list `L` without `×`-dotted partner in `g`. -/
def unpartCount (g : Graph k n) (L : List (Comp (Atom k n))) : ℕ :=
  (L.filter fun c => c.kind.isSolid && !partnered g c).length

private theorem unpartL_length (g : Graph k n) : (unpartL g).length = unpartCount g g.comps := rfl

private theorem unpartCount_append (g : Graph k n) (L M : List (Comp (Atom k n))) :
    unpartCount g (L ++ M) = unpartCount g L + unpartCount g M := by
  simp [unpartCount, List.filter_append]

private theorem partnered_congr (g : Graph k n) {c c' : Comp (Atom k n)} (hx : c.x = c'.x)
    (hy : c.y = c'.y) : partnered g c = partnered g c' := by
  unfold partnered
  rw [hx, hy]

private theorem unpartCount_labW (g : Graph k n) (o : Option (Atom k n))
    (L : List (Comp (Atom k n))) :
    unpartCount g (labW o L) = unpartCount g L := by
  cases o with
  | none => rfl
  | some u =>
    unfold unpartCount labW labelQs
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro c _
    have hx : (c.labelQ u).x = c.x := by unfold Comp.labelQ; split_ifs <;> rfl
    have hy : (c.labelQ u).y = c.y := by unfold Comp.labelQ; split_ifs <;> rfl
    have hk : (c.labelQ u).kind = c.kind := by unfold Comp.labelQ; split_ifs <;> rfl
    simp [hk, partnered_congr g hx hy]

private theorem unpartCount_eq_zero (g : Graph k n) {L : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.kind.isSolid = true → partnered g c = true) : unpartCount g L = 0 := by
  unfold unpartCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc
  by_cases hs : c.kind.isSolid = true
  · simp [hs, h c hc hs]
  · simp [Bool.eq_false_iff.2 hs]

private theorem unpartCount_le (g : Graph k n) (L : List (Comp (Atom k n))) :
    unpartCount g L ≤ L.length := List.length_filter_le _ _

private theorem unpartCount_le_solid (g : Graph k n) (L : List (Comp (Atom k n))) :
    unpartCount g L ≤ (L.filter fun c => c.kind.isSolid).length := by
  unfold unpartCount
  refine (List.monotone_filter_right L ?_).length_le
  intro c hc
  simp only [Bool.and_eq_true] at hc
  exact hc.1

end Unpart

section Out2

variable {k n : ℕ}

private theorem labels_le_one {g : Graph k n} {u : Atom k n}
    (h : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.Q, u)) : g.labels.length ≤ 1 := by
  unfold Graph.labels
  have hall : ∀ l ∈ (g.comps.filterMap Comp.label).dedup, l = (PQ.Q, u) := by
    intro l hl
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 (List.mem_dedup.1 hl)
    rcases h c hc with h0 | h0
    · rw [h0] at hcl; simp at hcl
    · rw [h0] at hcl; exact (Option.some.inj hcl).symm
  have hnd := List.nodup_dedup (g.comps.filterMap Comp.label)
  generalize (g.comps.filterMap Comp.label).dedup = L at hall hnd
  rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp
  · simp
  · exfalso
    have ha := hall a (List.mem_cons_self ..)
    have hb := hall b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [List.nodup_cons] at hnd
    exact hnd.1 (by rw [ha, hb]; exact List.mem_cons_self ..)

private theorem unlabelled_dots {m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n} {x : Atom k n}
    {g' : Graph k m} (E : ExtData φ g₁ x g') (hU : ∀ c ∈ g₁.comps, c.label = none) :
    ∀ c ∈ g'.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
  intro c' hc' hk
  rcases E.src c' hc' with ⟨c, hc, rfl⟩ | hnew
  · simp [Comp.map, hU c hc]
  · exfalso
    obtain ⟨-, hkinds, -⟩ := hnew
    rcases hkinds with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨w, h⟩ <;> rcases hk with hk | hk <;>
      rw [h] at hk <;> cases hk

private theorem partnered_old {C m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n} {x : Atom k n}
    {g' : Graph k m} (hN : g₁.Normal C) (E : ExtData φ g₁ x g') {c' : Comp (Atom k m)}
    (hold : ∃ c ∈ g₁.comps, c'.x = φ c.x ∧ c'.y = φ c.y ∧ c'.kind = c.kind)
    (hs : c'.kind.isSolid = true) : partnered g' c' = true := by
  obtain ⟨c, hc, h1, h2, h3⟩ := hold
  have hcs : c.kind.isSolid = true := by rw [← h3]; exact hs
  have hne : c.x ≠ c.y := hN.2.1 c hc hcs
  have hx := (hN.2.2 c.x c.y hne).2 ⟨c, hc, hcs, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨c₃, hc₃, hk₃, hm₃⟩ := hx
  rw [partnered_iff]
  refine ⟨c₃.map φ, E.old c₃ hc₃ (by rw [hk₃]; rfl), by simpa [Comp.map] using hk₃, ?_⟩
  unfold SamePair
  simp only [Comp.map]
  rcases hm₃ with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · left; rw [h1, h2, a1, a2]; exact ⟨rfl, rfl⟩
  · right; rw [h1, h2, a1, a2]; exact ⟨rfl, rfl⟩

end Out2

section Assembly

variable {k n : ℕ}

private theorem label_labelQs {V : Type*} (u : V) {cs : List (Comp V)}
    (h : ∀ c ∈ cs, c.label = none) :
    ∀ c ∈ labelQs u cs, c.label = none ∨ c.label = some (.Q, u) := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := mem_labelQs.1 hc
  unfold Comp.labelQ
  split_ifs
  · right; rfl
  · left; exact h c₀ hc₀

private theorem solidC_label {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).label = none := by
  unfold solidC; split_ifs <;> rfl

private theorem dPieces_label {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)}
    (h : c.dPieces p q = some ps) : ∀ c' ∈ ps, c'.label = none := by
  unfold Comp.dPieces at h
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Charge›) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    (intro c' hc'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
     rcases hc' with rfl | rfl <;> exact solidC_label _ _ _)

end Assembly

/-! ## The factors of the derivative: orders and pairs -/

section DPieces

variable {V : Type*} [DecidableEq V]

private theorem ord_solidC (ch : Charge) (u v : V) :
    (solidC ch u v).kind.ord = if u = v then 0 else 1 := by
  unfold solidC; split_ifs <;> simp [mkC, Kind.ord]

/-- The endpoint of a random component other than the one it sits on (itself, for a weight). -/
private def Comp.endB (c : Comp V) : V := if c.kind.isWeight then c.x else c.y

private theorem dPieces_eq_plus {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps)
    (hk : (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) :
    (c.kind = .G .plus ∨ c.kind = .weight .plus ∨ c.kind = .light .plus) ∧
      ps = [solidC .plus c.x p, solidC .plus q c.endB] ∨
    (c.kind = .G .minus ∨ c.kind = .weight .minus ∨ c.kind = .light .minus) ∧
      ps = [solidC .minus c.x q, solidC .minus p c.endB] := by
  unfold Comp.dPieces at h
  unfold Comp.endB
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> (try cases ‹Charge›) <;> simp_all [Kind.isWeight]

omit [DecidableEq V] in
private theorem ordL_two {a b : Comp V} : ordL [a, b] = a.kind.ord + b.kind.ord := by
  simp [ordL]

omit [DecidableEq V] in
private theorem kind_ord_le_one {c : Comp V}
    (hk : (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) :
    c.kind.ord ≤ 1 := by
  rcases hk with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [h, Kind.ord]

private theorem dPieces_ord_ge {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps)
    (hx : c.x ≠ p) (hb : c.endB ≠ p) : 1 ≤ ordL ps ∧ c.kind.ord ≤ 1 := by
  have hk := dPieces_random h
  refine ⟨?_, kind_ord_le_one hk⟩
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [ordL_two, ord_solidC, ord_solidC, ite_eq_right hx]
    split_ifs <;> simp
  · rw [ordL_two, ord_solidC, ord_solidC, ite_eq_right (Ne.symm hb)]
    split_ifs <;> simp

private theorem dPieces_ord_two {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps)
    (hx : c.x ≠ p) (hb : c.endB ≠ p) (hxq : c.x ≠ q) (hbq : c.endB ≠ q) : ordL ps = 2 := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [ordL_two, ord_solidC, ord_solidC, ite_eq_right hx, ite_eq_right (Ne.symm hbq)]
    norm_num
  · rw [ordL_two, ord_solidC, ord_solidC, ite_eq_right hxq, ite_eq_right (Ne.symm hb)]
    norm_num

end DPieces

/-! ## Lemmas for the remaining terms -/

section Helpers

variable {k n : ℕ}

@[simp] private theorem labelQ_x {V : Type*} (u : V) (c : Comp V) : (c.labelQ u).x = c.x := by
  unfold Comp.labelQ; split_ifs <;> rfl

@[simp] private theorem labelQ_y {V : Type*} (u : V) (c : Comp V) : (c.labelQ u).y = c.y := by
  unfold Comp.labelQ; split_ifs <;> rfl

@[simp] private theorem labelQ_kind {V : Type*} (u : V) (c : Comp V) :
    (c.labelQ u).kind = c.kind := by
  unfold Comp.labelQ; split_ifs <;> rfl

end Helpers

/-! ## The dotted edge partition after a pre-dot step -/

section DotOp

variable {k n : ℕ}

private theorem mem_oDotT_cases' {g : Graph k n} {t : Tracked k n} (ht : t ∈ oDotT g) :
    t = Tracked.self g ∨ ∃ A, List.Sublist A g.splitPairs ∧
      (g.dotChoice g.splitPairs A).mergeT = some t := by
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht with h1 h2
  · exact Or.inl (List.mem_singleton.1 ht)
  · exact Or.inl (List.mem_singleton.1 ht)
  · obtain ⟨A, hA, hA'⟩ := List.mem_filterMap.1 ht
    exact Or.inr ⟨A, List.mem_sublists.1 hA, hA'⟩

private theorem plain_dotChoice {g : Graph k n} (hP : g.Plain)
    (A : List (Atom k n × Atom k n × Bool)) : (g.dotChoice g.splitPairs A).Plain := by
  intro c hc
  have hc' : c ∈ keptComps g g.splitPairs ++ addedComps g.splitPairs A := hc
  rcases List.mem_append.1 hc' with h | h
  · exact hP c ((mem_keptComps g _ c).1 h).1
  · obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 h
    · refine ⟨rfl, fun ch => by simp [mkC], fun ch d => by simp [mkC], fun _ => sp_ne hp, ?_, ?_⟩
      · intro hw; simp [mkC, Kind.isWeight] at hw
      · intro hl; simp [mkC] at hl
    · refine ⟨rfl, fun ch => by simp [mkC], fun ch d => by simp [mkC],
        fun hk => by simp [mkC] at hk, ?_, ?_⟩
      · intro hw; simp [mkC, Kind.isWeight] at hw
      · intro hl; simp [mkC] at hl

private theorem MergeSpec.plain {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    (hP : h.Plain) :
    t.g.Plain := by
  intro c' hc'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP c hc
  unfold mergeComp at hm
  split_ifs at hm with hd hsol
  · obtain rfl := Option.some.inj hm
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hsol
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Comp.map, h1]
    · intro ch' h; simp [hch, Kind.toWeight] at h
    · intro ch' d' h; simp [hch, Kind.toWeight] at h
    · intro h; simp [hch, Kind.toWeight] at h
    · intro _; rfl
    · intro hl
      simp [hch, Kind.toWeight, Kind.isRandom]
  · obtain rfl := Option.some.inj hm
    refine ⟨Comp.map_minor_nil _ h1, ?_, ?_, ?_, ?_, ?_⟩
    · intro ch' h; exact h2 ch' (by simpa [Comp.map] using h)
    · intro ch' d' h; exact h3 ch' d' (by simpa [Comp.map] using h)
    · intro hk
      have hkc : c.kind = .dot := by simpa [Comp.map] using hk
      simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hd
      have := hd hkc
      simpa [Comp.map] using this
    · intro hw
      have := h5 (by simpa [Comp.map] using hw)
      simp [Comp.map, this]
    · intro hl
      have : c.label.isSome = true := by simpa [Comp.map] using hl
      simpa [Comp.map] using h6 this

private theorem oDotT_plain {g : Graph k n} (hP : g.Plain) : ∀ t ∈ oDotT g, t.g.Plain := by
  intro t ht
  rcases mem_oDotT_cases' ht with rfl | ⟨A, -, hm⟩
  · exact hP
  · exact (mergeT_spec hm).plain (plain_dotChoice hP A)

private theorem MergeSpec.waved_reach {g h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    (hsub : ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) → c ∈ h.comps) {u v : Atom k n}
    (huv : g.wavedGraph.Reachable u v) : t.g.wavedGraph.Reachable (t.f u) (t.f v) := by
  refine reach_map (G := g.wavedGraph) (H := t.g.wavedGraph) t.f (fun a b hab => ?_) huv
  rw [Graph.wavedGraph, SimpleGraph.fromRel_adj] at hab
  obtain ⟨-, hrel⟩ := hab
  have key : ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) →
      t.g.wavedGraph.Reachable (t.f c.x) (t.f c.y) := by
    intro c hc hw
    obtain ⟨w, hw⟩ := hw
    have hcm := hsub c hc ⟨w, hw⟩
    have hmem := hs.mem_of_other hcm (by rw [hw]; exact fun h => by cases h)
      (by simp [hw, Kind.isSolid])
    exact reach_of_waved t.g hmem ⟨w, by simp [Comp.map, hw]⟩
  rcases hrel with ⟨c, hc, hw, h1, h2⟩ | ⟨c, hc, hw, h1, h2⟩
  · have := key c hc hw
    rwa [h1, h2] at this
  · have := key c hc hw
    rw [h1, h2] at this
    exact this.symm

private theorem NR_dot {m : ℕ} {g₂ : Graph k m} {F : Atom k n → Atom k m} {x : Atom k n}
    (hNR : ∀ u, (∀ v, F v ≠ u) → g₂.wavedGraph.Reachable (F x) u)
    {t₃ : Tracked k m} (ht : t₃ ∈ oDotT g₂) :
    ∀ u, (∀ v, t₃.f (F v) ≠ u) → t₃.g.wavedGraph.Reachable (t₃.f (F x)) u := by
  intro u hu
  rcases mem_oDotT_cases' ht with rfl | ⟨A, -, hm⟩
  · exact hNR u hu
  · have hs := mergeT_spec hm
    obtain ⟨w, rfl⟩ := hs.f_surj u
    have hw : ∀ v, F v ≠ w := fun v h => hu v (by rw [h])
    have := hs.waved_reach (g := g₂) (fun c hc _ => mem_dotChoice_of_ne_xdot g₂ _ A hc
      (by rintro hk; obtain ⟨w', hw'⟩ := ‹∃ w, c.kind = .waved w›; rw [hw'] at hk; cases hk))
      (hNR w hw)
    exact this

end DotOp

section DotOp2

variable {k n : ℕ}

theorem dot_ord_ge {g : Graph k n} (hd : DotOK g)
    (hsl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hunp : (unpartL g).length ≤ 4 ∧ ∀ L : List (Comp (Atom k n)), L.Sublist (unpartL g) →
      3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂) :
    ∀ t ∈ oDotT g, g.ord ≤ t.g.ord := by
  intro t ht
  rcases mem_oDotT_cases' ht with rfl | ⟨A, hA, hm⟩
  · exact le_rfl
  · obtain ⟨K, r, e, hord, -, -, -, hle, -, -⟩ := dot_order hd hsl hunp.1 hunp.2 hA hm
    have : (e : ℤ) ≤ 2 * ((K : ℤ) + r) := by exact_mod_cast hle
    rw [hord]
    linarith

end DotOp2

/-! ## Order and reachability after `O_dot` -/

section Canonical

variable {k n : ℕ}

private theorem Graph.Normal.mono {C C' : ℕ} {g : Graph k n} (h : g.Normal C) (hC : C ≤ C') :
    g.Normal C' :=
  ⟨⟨by have := h.1.size; omega, h.1.connected, h.1.internal, h.1.noIntDot⟩, h.2.1, h.2.2⟩

private theorem splitPairs_nil_of_normal {C : ℕ} {g : Graph k n} (h : g.Normal C) : g.splitPairs =
    [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  have hne := sp_ne hp
  obtain ⟨-, hdiff, -⟩ := mem_splitPairs.1 hp
  have hiff := h.2.2 p.1 p.2.1 hne
  simp only [bne_iff_ne, ne_eq] at hdiff
  apply hdiff
  rw [Bool.eq_iff_iff]
  rw [spJoined_iff, spJoined_iff]
  constructor
  · rintro ⟨c, hc, hk, hm⟩
    obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := hiff.2 ⟨c, hc, hk, hm⟩
    exact ⟨c₂, hc₂, by simp [hk₂], hm₂⟩
  · rintro ⟨c, hc, hk, hm⟩
    obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := hiff.1 ⟨c, hc, by simpa using hk, hm⟩
    exact ⟨c₂, hc₂, hk₂, hm₂⟩

private theorem oDotT_normal_self {C : ℕ} {g : Graph k n} (h : g.Normal C) : oDotT g =
    [Tracked.self g] := by
  by_cases hb1 : (2 ≤ g.labels.length ∨
      (g.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true)
  · exact oDotT_branch1 hb1
  · refine oDotT_branch2 hb1 ?_
    rw [splitPairs_nil_of_normal h]
    simp only [List.isEmpty_nil, Bool.true_and, Bool.not_eq_true', List.any_eq_false]
    intro c hc hcon
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcon
    rcases hcon with ⟨⟨hk, h1⟩, h2⟩ | ⟨hs, hxy⟩
    · rcases h.1.noIntDot c hc hk with h3 | h3
      · rw [Sum.isLeft_iff] at h3
        obtain ⟨a, ha⟩ := h3
        rw [ha] at h1
        simp at h1
      · rw [Sum.isLeft_iff] at h3
        obtain ⟨a, ha⟩ := h3
        rw [ha] at h2
        simp at h2
    · exact h.2.1 c hc hs hxy

end Canonical

/-! ## Weights after `O_merge` -/

section MergeWt

variable {k n : ℕ}

private theorem r_two_pairs_g {m : ℕ} (g : Fin n → Fin m) (hgs : Function.Surjective g)
    {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (g1 : g a = g b) (g2 : g c = g d)
    (hne : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) : m + 2 ≤ n := by
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun hbd => hne (Or.inl ⟨rfl, hbd⟩)
    have := card_le_of_twins g hgs {b, d} (fun v hv => by
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hcd⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1
        · exact g2)
    simpa [Finset.card_pair hbd] using this
  by_cases had : a = d
  · subst had
    have hbc : b ≠ c := fun hbc => hne (Or.inr ⟨rfl, hbc⟩)
    have := card_le_of_twins g hgs {b, c} (fun v hv => by
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, fun h => hcd h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1
        · exact g2.symm)
    simpa [Finset.card_pair hbc] using this
  by_cases hbc : b = c
  · subst hbc
    have had : a ≠ d := had
    have := card_le_of_twins g hgs {a, d} (fun v hv => by
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hab h.symm, hcd⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1.symm
        · exact g2)
    simpa [Finset.card_pair had] using this
  by_cases hbd : b = d
  · subst hbd
    have hac' : a ≠ c := hac
    have := card_le_of_twins g hgs {a, c} (fun v hv => by
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hab h.symm, fun h => hcd h.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact g1.symm
        · exact g2.symm)
    simpa [Finset.card_pair hac'] using this
  · have had' : a ≠ d := had
    have hbd' : b ≠ d := hbd
    have := card_le_of_twins g hgs {b, d} (fun v hv => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · refine ⟨a, ?_, g1⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, had'⟩
      · refine ⟨c, ?_, g2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hbc h.symm, hcd⟩)
    simpa [Finset.card_pair hbd'] using this

/-- If exactly one internal atom disappears and `X`, `α` are identified, no other two atoms are
identified. -/
private theorem fiber_r1 {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    (hr : t.nOut + 1 = n)
    {X α : Fin n} (hXα : X ≠ α) (hf : t.f (.inr X) = t.f (.inr α)) :
    ∀ u v : Atom k n, t.f u = t.f v → u = v ∨ (u = .inr X ∧ v = .inr α) ∨
      (u = .inr α ∧ v = .inr X) := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  intro u v huv
  rcases u with a | i <;> rcases v with b | j
  · rw [hs.f_inl, hs.f_inl] at huv
    left
    simp only [Sum.inl.injEq] at huv ⊢
    exact huv
  · rw [hs.f_inl, hg] at huv; simp at huv
  · rw [hs.f_inl, hg] at huv; simp at huv
  · rw [hg, hg] at huv hf
    have hgij : g i = g j := Sum.inr.inj huv
    have hgXα : g X = g α := Sum.inr.inj hf
    by_cases hij : i = j
    · left; rw [hij]
    · by_cases hc : (i = X ∧ j = α) ∨ (i = α ∧ j = X)
      · right
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
        · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
      · exfalso
        have := r_two_pairs_g g hgs hij hXα hgij hgXα hc
        omega

end MergeWt

section MergeFormula

variable {k n : ℕ}

private theorem countP_dotChoice (g : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
    (Q : Comp (Atom k n) → Bool) (hQ : ∀ c, (c.kind = .xdot ∨ c.kind = .dot) → Q c = false) :
    (g.dotChoice SP A).comps.countP Q = g.comps.countP Q := by
  have hcomps : (g.dotChoice SP A).comps = keptComps g SP ++ addedComps SP A := rfl
  rw [hcomps, List.countP_append]
  have h1 : (addedComps SP A).countP Q = 0 := by
    rw [List.countP_eq_zero]
    intro c hc
    have := (addedComps_label hc).2
    simp [hQ c this.symm]
  rw [h1, add_zero]
  unfold keptComps
  rw [List.countP_filter]
  apply List.countP_congr
  intro c _
  by_cases hk : c.kind = .xdot
  · simp [hQ c (Or.inl hk)]
  · simp [hk]

end MergeFormula

section MergeE1

variable {k n : ℕ}

private theorem MergeSpec.injective_of_nOut {h : Graph k n} {t : Tracked k n} (hs : MergeSpec h t)
    (hn : t.nOut = n) : Function.Injective t.f := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hginj : ∀ i j : Fin n, g i = g j → i = j := by
    intro i j hij
    by_contra hne
    have := card_le_of_twins g hgs {j} (fun v hv => ⟨i, by
      simpa [Finset.mem_singleton.1 hv] using hne, by
      rw [Finset.mem_singleton.1 hv]; exact hij⟩)
    simp at this
    omega
  intro u v huv
  rcases u with a | i <;> rcases v with b | j
  · rw [hs.f_inl, hs.f_inl] at huv; rw [Sum.inl.inj huv]
  · rw [hs.f_inl, hg] at huv; simp at huv
  · rw [hs.f_inl, hg] at huv; simp at huv
  · rw [hg, hg] at huv
    rw [hginj i j (Sum.inr.inj huv)]

end MergeE1

section IdxLemmas

variable {α : Type*}

private theorem pickIdxs_eq (is : List ℕ) (l : List α) :
    pickIdxs is l = (l.zipIdx.filter fun p => is.contains p.2).map Prod.fst := rfl

private theorem eraseIdxs_eq (is : List ℕ) (l : List α) :
    eraseIdxs is l = (l.zipIdx.filter fun p => !is.contains p.2).map Prod.fst := rfl

private theorem eraseIdxs_pick_perm (is : List ℕ) (l : List α) :
    (eraseIdxs is l ++ pickIdxs is l).Perm l := by
  rw [eraseIdxs_eq, pickIdxs_eq]
  have h := List.filter_append_perm (fun p : α × ℕ => is.contains p.2) l.zipIdx
  have h2 := (h.map Prod.fst)
  rw [List.map_append, List.zipIdx_map_fst] at h2
  exact List.perm_append_comm.trans h2

private theorem mem_eraseIdxs_of_mem {is : List ℕ} {l : List α} {a : α} (h : a ∈ eraseIdxs is l) :
    a ∈ l := (eraseIdxs_pick_perm is l).subset (List.mem_append_left _ h)

private theorem zipIdx_nodup (l : List α) : l.zipIdx.Nodup := by
  have : (l.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' ..
  exact List.Nodup.of_map _ this

private theorem pickIdxs_perm (is : List ℕ) (hnd : is.Nodup) (l : List α) :
    (pickIdxs is l).Perm (is.filterMap fun i => l[i]?) := by
  classical
  rw [pickIdxs_eq]
  have key : (l.zipIdx.filter fun p => is.contains p.2).Perm
      (is.filterMap fun i => (l[i]?).map fun a => (a, i)) := by
    refine List.perm_of_nodup_nodup_toFinset_eq ?_ ?_ ?_
    · exact (zipIdx_nodup l).filter _
    · refine List.Nodup.filterMap ?_ hnd
      intro i i' p hp hp'
      simp only [Option.mem_def, Option.map_eq_some_iff] at hp hp'
      obtain ⟨a, -, rfl⟩ := hp
      obtain ⟨a', -, h⟩ := hp'
      exact (Prod.mk.inj h).2.symm
    · ext p
      simp only [List.mem_toFinset, List.mem_filter, List.mem_zipIdx_iff_getElem?,
        List.contains_iff_mem, List.mem_filterMap, Option.map_eq_some_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨p.2, h2, p.1, h1, rfl⟩
      · rintro ⟨i, hi, a, ha, rfl⟩
        exact ⟨ha, hi⟩
  have h2 := key.map Prod.fst
  rw [List.map_filterMap] at h2
  have h3 : (is.filterMap fun x => Option.map Prod.fst (Option.map (fun a => (a, x)) l[x]?)) =
      is.filterMap fun i => l[i]? := by
    apply List.filterMap_congr
    intro i _
    cases l[i]? <;> rfl
  rw [h3] at h2
  exact h2

end IdxLemmas

section EdgeIdx

variable {k n : ℕ}

private theorem mem_edgeIdx {Γ : Graph k n} {x : Atom k n} {ch : Charge} {out : Bool} {j : ℕ} :
    j ∈ Γ.edgeIdx x ch out ↔ ∃ c, Γ.comps[j]? = some c ∧ c.kind = .G ch ∧
      (if out = true then c.x = x ∧ c.y ≠ x else c.y = x ∧ c.x ≠ x) := by
  unfold Graph.edgeIdx
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?] at hp
    obtain ⟨hz, hf⟩ := hp
    refine ⟨p.1, hz, ?_⟩
    cases out <;> simp_all
  · rintro ⟨c, hc, hk, ho⟩
    refine ⟨(c, j), ?_, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?]
    refine ⟨hc, ?_⟩
    cases out <;> simp_all

private theorem edgeIdx_nodup (Γ : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    (Γ.edgeIdx x ch out).Nodup := by
  unfold Graph.edgeIdx
  have : (Γ.comps.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' ..
  have h2 := (List.Nodup.sublist (List.filter_sublist (p := fun p : Comp (Atom k n) × ℕ =>
    p.1.kind == .G ch && (if out then p.1.x == x && p.1.y != x else p.1.y == x && p.1.x != x))
    (l := Γ.comps.zipIdx)) (zipIdx_nodup Γ.comps))
  refine List.Nodup.map_on ?_ h2
  intro p hp q hq h
  rw [List.mem_filter, List.mem_zipIdx_iff_getElem?] at hp hq
  have h1 := hp.1
  have h2' := hq.1
  rw [h] at h1
  rw [h1] at h2'
  exact Prod.ext (Option.some.inj h2') h

private theorem edgeIdx_disjoint {Γ : Graph k n} {x : Atom k n} {ch ch' : Charge} {out out' : Bool}
    (h : ch ≠ ch' ∨ out ≠ out') {j : ℕ} (h1 : j ∈ Γ.edgeIdx x ch out)
    (h2 : j ∈ Γ.edgeIdx x ch' out') : False := by
  rw [mem_edgeIdx] at h1 h2
  obtain ⟨c, hc, hk, ho⟩ := h1
  obtain ⟨c', hc', hk', ho'⟩ := h2
  rw [hc] at hc'
  obtain rfl := Option.some.inj hc'
  rw [hk] at hk'
  have hch : ch = ch' := by injection hk'
  subst hch
  rcases h with h | h
  · exact h rfl
  · cases out <;> cases out' <;> simp_all

end EdgeIdx

section Perms

variable {α : Type*}

private theorem eraseIdx_perm {l : List α} {i : ℕ} {a : α} (h : l[i]? = some a) :
    (l.eraseIdx i ++ [a]).Perm l := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.eraseIdx_cons_succ, List.cons_append]
      exact (ih h).cons b

private theorem eraseIdxs_two_perm {l : List α} {i j : ℕ} {a b : α} (hij : i ≠ j) (ha : l[i]? =
    some a)
    (hb : l[j]? = some b) : (eraseIdxs [i, j] l ++ [a, b]).Perm l := by
  have h1 := eraseIdxs_pick_perm [i, j] l
  have h2 := pickIdxs_perm [i, j] (by simpa using hij) l
  simp only [List.filterMap_cons, ha, hb, List.filterMap_nil] at h2
  exact ((List.Perm.refl _).append h2.symm).trans h1

end Perms

section PreT

variable {k n : ℕ}

/-- The properties of a graph produced from `Γ` by one of the edge expansions before `O_dot`. -/
structure PreT (C : ℕ) (o : ℤ) (x : Atom k n) (T : Tracked k n) : Prop where
  size : k + T.nOut + T.g.comps.length ≤ C + 8
  conn : T.g.ConnNoX
  int : ∀ a b : Fin T.nOut, T.g.wavedThetaGraph.Reachable (.inr a) (.inr b)
  noIntDot : ∀ c ∈ T.g.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true
  dotOK : DotOK T.g
  sl : ∀ c ∈ T.g.comps, c.kind.isSolid = true → c.x ≠ c.y
  unp : (unpartL T.g).length ≤ 4 ∧ ∀ L : List (Comp (Atom k T.nOut)), L.Sublist (unpartL T.g) →
    3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂
  plain : T.g.Plain
  lab : T.g.labels.length ≤ 1 ∧ ∀ c ∈ T.g.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none
  ord : o ≤ T.g.ord
  new : ∀ u, (∀ v, T.f v ≠ u) → T.g.wavedGraph.Reachable (T.f x) u

/-- A component of an output graph comes from the input graph or is a new component. -/
private def SrcOK {m : ℕ} (φ : Atom k n → Atom k m) (g₁ : Graph k n) (c' : Comp (Atom k
    m)) : Prop :=
  (∃ c ∈ g₁.comps, c' = c.map φ) ∨ NewOK c'

private theorem SrcOK.labelQ {C m : ℕ} {φ : Atom k n → Atom k m} (hφ : Function.Injective φ)
    {g₁ : Graph k n} (hN : g₁.Normal C) (hP : g₁.Plain) {c' : Comp (Atom k m)}
    (h : SrcOK φ g₁ c') (u : Atom k m) : SrcOK φ g₁ (c'.labelQ u) := by
  rcases h with ⟨c, hc, rfl⟩ | hnew
  · by_cases hr : c.kind.isRandom = true
    · exact Or.inr ((NewOK_map_of_old hφ hN hP hc hr).labelQ u)
    · have hr' : (c.map φ).kind.isRandom = false := by simpa [Comp.map] using hr
      left
      refine ⟨c, hc, ?_⟩
      unfold Comp.labelQ
      simp [hr']
  · exact Or.inr (hnew.labelQ u)

private theorem srcOK_labW {C m : ℕ} {φ : Atom k n → Atom k m} (hφ : Function.Injective φ)
    {g₁ : Graph k n} (hN : g₁.Normal C) (hP : g₁.Plain) (o : Option (Atom k m))
    {L : List (Comp (Atom k m))} (h : ∀ c ∈ L, SrcOK φ g₁ c) :
    ∀ c' ∈ labW o L, SrcOK φ g₁ c' := by
  intro c' hc'
  obtain ⟨c, hc, h'⟩ := labW_cases hc'
  rcases h' with h' | ⟨u, h'⟩
  · rw [h']; exact h c hc
  · rw [h']; exact (h c hc).labelQ hφ hN hP u

private theorem srcOK_new {m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n} {c : Comp (Atom k m)}
    (h : NewOK c) : SrcOK φ g₁ c := Or.inr h

private theorem srcOK_lift {m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n} {c : Comp (Atom k n)}
    (h : c ∈ g₁.comps) : SrcOK φ g₁ (c.map φ) := Or.inl ⟨c, h, rfl⟩

private theorem unp_conv {m : ℕ} {g : Graph k m}
    (h : (unpartL g).length ≤ 3 ∧ ((unpartL g).length = 3 →
      ∃ c₁ ∈ unpartL g, ∃ c₂ ∈ unpartL g, ¬ SamePair c₁ c₂)) :
    (unpartL g).length ≤ 4 ∧ ∀ L : List (Comp (Atom k m)), L.Sublist (unpartL g) →
      3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂ := by
  refine ⟨by omega, fun L hL h3 => ?_⟩
  have hlen : L.length = (unpartL g).length := by
    have := hL.length_le
    omega
  have hEq : L = unpartL g := hL.eq_of_length hlen
  rw [hEq]
  exact h.2 (by omega)

end PreT

section MasterA

variable {k n : ℕ}

private theorem ordL_perm {V : Type*} {l₁ l₂ : List (Comp V)} (h : l₁.Perm
    l₂) : ordL l₁ = ordL l₂ := by
  unfold ordL
  exact (h.map _).sum_eq

private theorem ord_eq_of_comps {j : ℕ} {Γ : Graph k n} (o : Option (Atom k (n + j)))
    (B R : List (Comp (Atom k n))) (N₁ N₂ : List (Comp (Atom k (n + j)))) (d : Coeff)
    (hBR : (B ++ R).Perm Γ.comps) :
    (⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ : Graph k (n + j)).ord =
      Γ.ord + ordL (N₁ ++ N₂) - ordL R - 2 * j := by
  have h1 := ordL_perm hBR
  rw [ordL_append] at h1
  simp only [Graph.ord_eq, ordL_append, ordL_labW, ordL_liftCs]
  push_cast
  linarith

private theorem preT_A' {C j : ℕ} {Γ : Graph k n} {x : Atom k n}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (o : Option (Atom k (n + j))) (B R : List (Comp (Atom k n)))
    (N₁ N₂ M : List (Comp (Atom k (n + j)))) (d : Coeff)
    (hM : M = labW o (liftCs j B ++ N₁) ++ N₂)
    (hBR : (B ++ R).Perm Γ.comps)
    (hrand : ∀ r ∈ R, r.kind.isRandom = true)
    (hN₁ : ∀ c ∈ N₁, NewOK c) (hN₂ : ∀ c ∈ N₂, NewOK c)
    (hNl : ∀ c ∈ N₁ ++ N₂, c.label = none)
    (hcover : ∀ r ∈ R, r.kind ≠ .xdot → r.x ≠ r.y →
      (⟨M, d⟩ : Graph k (n + j)).edgeGraphNoX.Reachable (liftA j r.x) (liftA j r.y))
    (hatt : ∀ i : Fin j, (⟨M, d⟩ : Graph k (n + j)).wavedGraph.Reachable
      (liftA j x) (newA i))
    (hunp : ExtData (liftA j) Γ x (⟨M, d⟩ : Graph k (n + j)) →
      (unpartL (⟨M, d⟩ : Graph k (n + j))).length ≤ 4 ∧
        ∀ L : List (Comp (Atom k (n + j))), L.Sublist (unpartL (⟨M, d⟩ : Graph k (n + j))) →
          3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂)
    (hlen : j + (N₁ ++ N₂).length ≤ R.length + 8)
    (hord : ordL R + 2 * j ≤ ordL (N₁ ++ N₂)) :
    PreT C Γ.ord x ⟨n + j, ⟨M, d⟩, liftA j⟩ ∧
      (⟨M, d⟩ : Graph k (n + j)).ord = Γ.ord + ordL (N₁ ++ N₂) - ordL R - 2 * j := by
  subst hM
  set g' : Graph k (n + j) := ⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ with hg'
  have hcomps : g'.comps = labW o (liftCs j B ++ N₁) ++ N₂ := rfl
  have hBsub : ∀ c ∈ B, c ∈ Γ.comps := fun c hc => hBR.subset (List.mem_append_left _ hc)
  have hcov : ∀ c ∈ Γ.comps, c ∈ B ∨ c ∈ R := fun c hc =>
    List.mem_append.1 (hBR.symm.subset hc)
  have hinj := liftA_injective (k := k) (n := n) j
  have E : ExtData (liftA j) Γ x g' := by
    refine ⟨?_, ?_, ?_, attach_of_new hatt⟩
    · intro c hc hr
      have hcB : c ∈ B := by
        rcases hcov c hc with h | h
        · exact h
        · rw [hrand c h] at hr; cases hr
      rw [hcomps]
      apply List.mem_append_left
      apply labW_nonrandom
      · exact List.mem_append_left _ (mem_liftCs.2 ⟨c, hcB, rfl⟩)
      · simpa [Comp.map] using hr
    · intro c' hc'
      rw [hcomps, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · refine srcOK_labW hinj hN hP o ?_ c' hc'
        intro c₁ hc₁
        rcases List.mem_append.1 hc₁ with h | h
        · obtain ⟨c, hcB, rfl⟩ := mem_liftCs.1 h
          exact srcOK_lift (hBsub c hcB)
        · exact srcOK_new (hN₁ c₁ h)
      · exact srcOK_new (hN₂ c' hc')
    · intro c hc hk hne
      rcases hcov c hc with hcB | hcR
      · obtain ⟨c'', hc'', h1, h2, h3⟩ := labW_exists (o := o) (L := liftCs j B ++ N₁)
          (List.mem_append_left _ (mem_liftCs.2 ⟨c, hcB, rfl⟩))
        have := reach_of_comp_noX g' (c := c'') (by rw [hcomps]; exact List.mem_append_left _ hc'')
          (by rw [h3]; simpa [Comp.map] using hk)
        simpa [h1, h2, Comp.map] using this
      · exact hcover c hcR hk hne
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ExtData.props hinj (liftA_isLeft j) hN hP hx E
  have hlength : g'.comps.length + R.length = Γ.comps.length + (N₁ ++ N₂).length := by
    have := hBR.length_eq
    rw [List.length_append] at this
    simp only [hcomps, List.length_append, length_labW, liftCs_length]
    simp only [List.length_append] at hlen ⊢
    omega
  have hunp' := hunp E
  refine ⟨⟨?_, h1, h2, h3, h4, h5, hunp', h6, ⟨?_, unlabelled_dots E hU⟩, ?_, E.attach⟩,
    ord_eq_of_comps o B R N₁ N₂ d hBR⟩
  · have := hN.1.size
    simp only [List.length_append] at hlength hlen ⊢
    omega
  · cases o with
    | none =>
      refine labels_le_one (u := liftA j x) fun c hc => Or.inl ?_
      simp only [hcomps, labW, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · obtain ⟨c0, hc0, rfl⟩ := mem_liftCs.1 hc
        simp [Comp.map, hU c0 (hBsub c0 hc0)]
      · exact hNl c (List.mem_append_left _ hc)
      · exact hNl c (List.mem_append_right _ hc)
    | some u =>
      refine labels_le_one (u := u) fun c hc => ?_
      rw [hcomps, List.mem_append] at hc
      rcases hc with hc | hc
      · refine label_labelQs u (cs := liftCs j B ++ N₁) ?_ c hc
        intro c₁ hc₁
        rcases List.mem_append.1 hc₁ with h | h
        · obtain ⟨c0, hc0, rfl⟩ := mem_liftCs.1 h
          simp [Comp.map, hU c0 (hBsub c0 hc0)]
        · exact hNl c₁ (List.mem_append_left _ h)
      · exact Or.inl (hNl c (List.mem_append_right _ hc))
  · have := ord_eq_of_comps o B R N₁ N₂ d hBR
    rw [this]
    linarith

private theorem preT_A {C j : ℕ} {Γ : Graph k n} {x : Atom k n}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (o : Option (Atom k (n + j))) (B R : List (Comp (Atom k n)))
    (N₁ N₂ M : List (Comp (Atom k (n + j)))) (d : Coeff)
    (hM : M = labW o (liftCs j B ++ N₁) ++ N₂)
    (hBR : (B ++ R).Perm Γ.comps)
    (hrand : ∀ r ∈ R, r.kind.isRandom = true)
    (hN₁ : ∀ c ∈ N₁, NewOK c) (hN₂ : ∀ c ∈ N₂, NewOK c)
    (hNl : ∀ c ∈ N₁ ++ N₂, c.label = none)
    (hcover : ∀ r ∈ R, r.kind ≠ .xdot → r.x ≠ r.y →
      (⟨M, d⟩ : Graph k (n + j)).edgeGraphNoX.Reachable (liftA j r.x) (liftA j r.y))
    (hatt : ∀ i : Fin j, (⟨M, d⟩ : Graph k (n + j)).wavedGraph.Reachable
      (liftA j x) (newA i))
    (hsol : ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 2)
    (hlen : j + (N₁ ++ N₂).length ≤ R.length + 8)
    (hord : ordL R + 2 * j ≤ ordL (N₁ ++ N₂)) :
    PreT C Γ.ord x ⟨n + j, ⟨M, d⟩, liftA j⟩ ∧
      (⟨M, d⟩ : Graph k (n + j)).ord = Γ.ord + ordL (N₁ ++ N₂) - ordL R - 2 * j := by
  refine preT_A' hN hP hx hU o B R N₁ N₂ M d hM hBR hrand hN₁ hN₂ hNl hcover hatt ?_ hlen hord
  intro E
  subst hM
  set g' : Graph k (n + j) := ⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ with hg'
  have hcomps : g'.comps = labW o (liftCs j B ++ N₁) ++ N₂ := rfl
  have hBsub : ∀ c ∈ B, c ∈ Γ.comps := fun c hc => hBR.subset (List.mem_append_left _ hc)
  have hunp0 : unpartCount g' (liftCs j B) = 0 := by
    refine unpartCount_eq_zero g' fun c' hc' hs => ?_
    obtain ⟨c, hcB, rfl⟩ := mem_liftCs.1 hc'
    exact partnered_old hN E ⟨c, hBsub c hcB, rfl, rfl, rfl⟩ hs
  have hunpN : (unpartL g').length ≤ 2 := by
    rw [unpartL_length, hcomps, unpartCount_append, unpartCount_labW, unpartCount_append, hunp0,
      zero_add, ← unpartCount_append]
    exact (unpartCount_le_solid g' _).trans hsol
  exact unp_conv ⟨by omega, fun h => by omega⟩

end MasterA

section ReachIn

variable {k n : ℕ}

private theorem reach_in {j : ℕ} (o : Option (Atom k (n + j))) {P N₂ : List (Comp (Atom k (n + j)))}
    (d : Coeff) {c : Comp (Atom k (n + j))} (hc : c ∈ P ∨ c ∈ N₂) (hk : c.kind ≠ .xdot) :
    (⟨labW o P ++ N₂, d⟩ : Graph k (n + j)).edgeGraphNoX.Reachable c.x c.y := by
  rcases hc with hc | hc
  · obtain ⟨c'', hc'', h1, h2, h3⟩ := labW_exists (o := o) hc
    have := reach_of_comp_noX (⟨labW o P ++ N₂, d⟩ : Graph k (n + j)) (c := c'')
      (List.mem_append_left _ hc'') (by rw [h3]; exact hk)
    rwa [h1, h2] at this
  · exact reach_of_comp_noX (⟨labW o P ++ N₂, d⟩ : Graph k (n + j)) (c := c)
      (List.mem_append_right _ hc) hk

private theorem reachW_in {j : ℕ} (o : Option (Atom k (n + j))) {P N₂ : List (Comp (Atom k (n +
    j)))}
    (d : Coeff) {c : Comp (Atom k (n + j))} (hc : c ∈ P ∨ c ∈ N₂) (hw : ∃ w, c.kind = .waved w) :
    (⟨labW o P ++ N₂, d⟩ : Graph k (n + j)).wavedGraph.Reachable c.x c.y := by
  have hr : c.kind.isRandom = false := by
    obtain ⟨w, hw⟩ := hw
    rw [hw]; rfl
  rcases hc with hc | hc
  · exact reach_of_waved (⟨labW o P ++ N₂, d⟩ : Graph k (n + j)) (c := c)
      (List.mem_append_left _ (labW_nonrandom hc hr)) hw
  · exact reach_of_waved (⟨labW o P ++ N₂, d⟩ : Graph k (n + j)) (c := c)
      (List.mem_append_right _ hc) hw

private theorem NewOK.ne_xdot {V : Type*} {c : Comp V} (h : NewOK c) : c.kind ≠ .xdot := by
  rcases h.2.1 with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨w, h⟩ <;> rw [h] <;> simp

private theorem newOK_cons {V : Type*} {c : Comp V} {cs : List (Comp V)} (h : NewOK c)
    (hs : ∀ c' ∈ cs, NewOK c') : ∀ c' ∈ c :: cs, NewOK c' := by
  intro c' hc'
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact h
  · exact hs c' hc'

private theorem newOK_append {V : Type*} {cs ds : List (Comp V)} (h : ∀ c' ∈ cs, NewOK c')
    (hs : ∀ c' ∈ ds, NewOK c') : ∀ c' ∈ cs ++ ds, NewOK c' := by
  intro c' hc'
  rcases List.mem_append.1 hc' with h' | h'
  · exact h c' h'
  · exact hs c' h'

private theorem newOK_nil {V : Type*} : ∀ c' ∈ ([] : List (Comp V)), NewOK c' := by simp

private theorem reach_in' {j : ℕ} (o : Option (Atom k (n + j))) {P N₂ M : List (Comp (Atom k (n +
    j)))}
    (d : Coeff) (hM : M = labW o P ++ N₂) {c : Comp (Atom k (n + j))}
    (hc : c ∈ P ∨ c ∈ N₂) (hk : c.kind ≠ .xdot) :
    (⟨M, d⟩ : Graph k (n + j)).edgeGraphNoX.Reachable c.x c.y := by
  subst hM
  exact reach_in o d hc hk

private theorem reachW_in' {j : ℕ} (o : Option (Atom k (n + j))) {P N₂ M : List (Comp (Atom k (n +
    j)))}
    (d : Coeff) (hM : M = labW o P ++ N₂) {c : Comp (Atom k (n + j))}
    (hc : c ∈ P ∨ c ∈ N₂) (hw : ∃ w, c.kind = .waved w) :
    (⟨M, d⟩ : Graph k (n + j)).wavedGraph.Reachable c.x c.y := by
  subst hM
  exact reachW_in o d hc hw

private theorem lab_cons {V : Type*} {c : Comp V} {cs : List (Comp V)} (h : c.label = none)
    (hs : ∀ c' ∈ cs, c'.label = none) : ∀ c' ∈ c :: cs, c'.label = none := by
  intro c' hc'
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact h
  · exact hs c' hc'

private theorem lab_append {V : Type*} {cs ds : List (Comp V)} (h : ∀ c' ∈ cs, c'.label = none)
    (hs : ∀ c' ∈ ds, c'.label = none) : ∀ c' ∈ cs ++ ds, c'.label = none := by
  intro c' hc'
  rcases List.mem_append.1 hc' with h' | h'
  · exact h c' h'
  · exact hs c' h'

private theorem lab_nil {V : Type*} : ∀ c' ∈ ([] : List (Comp V)), c'.label = none := by simp

private theorem filter_solid_nil {V : Type*} {L : List (Comp V)} (h : ∀ c ∈ L,
    c.kind.isSolid = false) :
    (L.filter fun c => c.kind.isSolid) = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  simp [h c hc]

end ReachIn

section OutDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- Auxiliary: the graph with `n + 1` internal atoms. -/
def EO_t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n := ⟨n + 1, ⟨cs, d⟩,
    liftA 1⟩

/-- The indices of the solid edges attached to `x`: those of charge `plus` leaving `x`, then those
of charge `minus` leaving `x`, then those of charge `plus` entering `x`, then those of charge
`minus` entering `x` ([I, Def 3.11]). -/
def EO_oXIdx : List ℕ :=
  Γ.edgeIdx x .plus true ++ Γ.edgeIdx x .minus true ++ Γ.edgeIdx x .plus false ++
    Γ.edgeIdx x .minus false

/-- The waved edge `s_{xα}` from the image of `x` to the new atom `α` ([I, (3.13)]). -/
def EO_oSx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0)

/-- The solid edge `G_{α y₁}` taking the place of the first edge `G_{x y₁}` of charge `plus`
leaving `x` ([I, (3.13)]). -/
def EO_oGy : Comp (Atom k (n + 1)) := mkC (.G .plus) (newA 0) (liftA 1 e₁.y)

/-- The components of a main term of [I, (3.13)] in case (i): the edges `G_{x y₁}` and `Ḡ_{x y_j}`
are exchanged for `s_{xα} G_{α y₁} Ḡ_{α y_j}`. -/
def EO_oBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ((Γ.comps.getD j e₁).y))]

/-- The components of a main term of [I, (3.13)] in case (i): the edges `G_{x y₁}` and `G_{w_j x}`
are exchanged for `s_{xα} G_{α y₁} G_{w_j α}`. -/
def EO_oBaseP (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The components of the term of [I, (3.13)] in case (i) in which `G_{x y₁}` is exchanged for
`s_{xα} G_{xα} G_{α y₁}`. -/
def EO_oE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mkC (.G .plus) (liftA 1 x) (newA 0), EO_oGy e₁]

/-- The components of the term of [I, (3.13)] in case (i) in which `G_{x y₁}` is exchanged for
`s_{xα} Ḡ_{αx} G_{α y₁}`. -/
def EO_oE2 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mkC (.G .minus) (newA 0) (liftA 1 x), EO_oGy e₁]

/-- The components of the term `m ∑_α s_{xα} (G_{αα} - m) 𝒢` of [I, (3.13)] in case (i). -/
def EO_oL3 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 Γ.comps ++ [EO_oSx x, mkC (.light .plus) (newA 0) (newA 0)]

/-- The components of the derivative terms of [I, (3.13)] in case (i). -/
def EO_oDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (EO_oXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((EO_oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [EO_oSx x, EO_oGy e₁]

/-- The terms of `Ô^{(x)}_multi-e` in case (i) of [I, Def 3.11], for the first edge `G_{x y₁}` of
charge `plus` leaving `x` (at the index `i₁`, the further such edges being at the indices
`is₂`). -/
def EO_oOut : TExpansion k n :=
  (Γ.edgeIdx x .minus true).map (fun j => EO_t1 (EO_oBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => EO_t1 (EO_oBaseP x Γ i₁ e₁ j) (cm * cm * Γ.coeff)) ++
    (Γ.edgeIdx x .minus true).map (fun j => EO_t1 (EO_oBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => EO_t1 (EO_oBaseP x Γ i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [EO_t1 (EO_oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [EO_t1 (EO_oE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (if (Γ.edgeIdx x .minus false).length = 0 then [] else
      [EO_t1 (EO_oE2 x Γ i₁ e₁) (((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)]) ++
    (EO_oDs x Γ i₁ e₁).map (fun d => EO_t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus true).map (fun j => EO_t1 (labelQs (liftA 1 x) (EO_oBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => EO_t1 (labelQs (liftA 1 x) (EO_oBaseP x Γ i₁ e₁ j ++
      [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [EO_t1 (labelQs (liftA 1 x) (EO_oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [EO_t1 (labelQs (liftA 1 x) (EO_oE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (if (Γ.edgeIdx x .minus false).length = 0 then [] else
      [EO_t1 (labelQs (liftA 1 x) (EO_oE2 x Γ i₁ e₁))
        (-((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)]) ++
    (EO_oDs x Γ i₁ e₁).map (fun d => EO_t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

end OutDefs

section OutTerms

variable {k n : ℕ}

/-- The data of case (i) of [I, Def 3.11]: `Γ` is plain and normal regular with bound `C`, label-
free, `x` is internal, and the edges of charge `plus` leaving `x` are at the indices `i₁ ::
is₂`, the first being `e₁`. -/
structure OutCtx (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  hOP : Γ.edgeIdx x .plus true = i₁ :: is₂
  hL : Γ.comps[i₁]? = some e₁

private theorem OutCtx.e₁spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) :
    e₁.kind = .G .plus ∧ e₁.x = x ∧ e₁.y ≠ x := by
  have h : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hL] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem OutCtx.e₁mem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) : e₁ ∈ Γ.comps :=
  List.mem_of_getElem? Ctx.hL

private theorem newOK_oSx (x : Atom k n) : NewOK (EO_oSx x) := NewOK_waved _ _ _

private theorem newOK_oGy (e₁ : Comp (Atom k n)) : NewOK (EO_oGy e₁) :=
  NewOK_G _ (liftA_ne_newA 1 e₁.y 0).symm

/-- The terms `baseM` of `Ô_multi-e`, case (i), with an extra list of non-solid components. -/
private theorem preT_baseM {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) {j : ℕ}
    (hj : j ∈ Γ.edgeIdx x .minus true) (o : Option (Atom k (n + 1)))
    (extra : List (Comp (Atom k (n + 1)))) (hex : ∀ c ∈ extra, NewOK c)
    (hexs : ∀ c ∈ extra, c.kind.isSolid = false) (hexl : ∀ c ∈ extra, c.label = none)
    (hexo : 0 ≤ ordL extra) (hexn : extra.length ≤ 1) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (EO_oBaseM x Γ i₁ e₁ j ++ extra), d⟩, liftA 1⟩ ∧
      (⟨labW o (EO_oBaseM x Γ i₁ e₁ j ++ extra), d⟩ : Graph k (n + 1)).ord = Γ.ord + ordL extra ∧
      ∃ c ∈ EO_oBaseM x Γ i₁ e₁ j ++ extra, c.kind.isRandom = true := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  obtain ⟨ej, hej, hkj, hxj, hyj⟩ := mem_edgeIdx.1 hj
  have hne : i₁ ≠ j := by
    rintro rfl
    rw [Ctx.hL] at hej
    obtain rfl := Option.some.inj hej
    rw [hk₁] at hkj
    cases hkj
  have hperm := eraseIdxs_two_perm hne Ctx.hL hej
  have hgetD : Γ.comps.getD j e₁ = ej := by simp [List.getD_eq_getElem?_getD, hej]
  have hS : NewOK (mkC (.G .minus) (newA 0) (liftA 1 ej.y) : Comp (Atom k (n + 1))) :=
    NewOK_G _ (liftA_ne_newA 1 ej.y 0).symm
  have hbase : EO_oBaseM x Γ i₁ e₁ j = liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] := by
    unfold EO_oBaseM; rw [hgetD]
  rw [hbase]
  have hM2 : labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra) =
      labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra) ++ [] :=
    (List.append_nil _).symm
  have hsx : EO_oSx x ∈ liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra := by simp
  have hgy : EO_oGy e₁ ∈ liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra := by simp
  have hgj : (mkC (.G .minus) (newA 0) (liftA 1 ej.y) : Comp (Atom k (n + 1))) ∈
      liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra := by simp
  have h1 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hsx) (by simp [EO_oSx, mkC])
  have h2 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgy) (by simp [EO_oGy, mkC])
  have h3 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgj) (by simp [mkC])
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have e2 : ej.kind.ord = 1 := by rw [hkj]; rfl
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (eraseIdxs [i₁, j] Γ.comps)
    [e₁, ej] ([EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra) []
    (labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra)) d
    (by simp [List.append_assoc]) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_append (newOK_cons (newOK_oSx x) (newOK_cons (newOK_oGy e₁) (newOK_cons hS newOK_nil)))
        hex)
    newOK_nil
    (by
      simp only [List.append_nil, List.forall_mem_append]
      exact ⟨by simp [EO_oSx, EO_oGy, mkC], hexl⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx₁]
        exact h1.trans h2
      · rw [hxj]
        exact h1.trans h3)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o d hM2 (Or.inl hsx) ⟨.s, rfl⟩)
    (by
      simp only [List.append_nil, List.filter_append, filter_solid_nil hexs]
      simp [EO_oSx, EO_oGy, mkC, Kind.isSolid])
    (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
    (by
      have h4 : ordL ([EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra ++ []) =
          4 + ordL extra := by
        simp [EO_oSx, EO_oGy, mkC, Kind.ord]
        ring
      have h5 : ordL [e₁, ej] = 2 := by simp [ordL_cons, e1, e2]
      rw [h4, h5]
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨EO_oGy e₁, by simp, by simp [EO_oGy, mkC, Kind.isRandom]⟩⟩
  rw [key.2]
  have h4 : ordL ([EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] ++ extra ++ []) =
      4 + ordL extra := by
    simp [EO_oSx, EO_oGy, mkC, Kind.ord]
    ring
  have h5 : ordL [e₁, ej] = 2 := by simp [ordL_cons, e1, e2]
  rw [h4, h5]
  push_cast
  ring

end OutTerms

section OutTerms2

variable {k n : ℕ}

/-- The terms `baseP` of `Ô_multi-e`, case (i), with an extra list of non-solid components. -/
private theorem preT_baseP {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) {j : ℕ}
    (hj : j ∈ Γ.edgeIdx x .plus false) (o : Option (Atom k (n + 1)))
    (extra : List (Comp (Atom k (n + 1)))) (hex : ∀ c ∈ extra, NewOK c)
    (hexs : ∀ c ∈ extra, c.kind.isSolid = false) (hexl : ∀ c ∈ extra, c.label = none)
    (hexo : 0 ≤ ordL extra) (hexn : extra.length ≤ 1) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (EO_oBaseP x Γ i₁ e₁ j ++ extra), d⟩, liftA 1⟩ ∧
      (⟨labW o (EO_oBaseP x Γ i₁ e₁ j ++ extra), d⟩ : Graph k (n + 1)).ord = Γ.ord + ordL extra ∧
      ∃ c ∈ EO_oBaseP x Γ i₁ e₁ j ++ extra, c.kind.isRandom = true := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  obtain ⟨ej, hej, hkj, hyj, hxj⟩ := mem_edgeIdx.1 hj
  have hne : i₁ ≠ j := by
    rintro rfl
    rw [Ctx.hL] at hej
    obtain rfl := Option.some.inj hej
    exact hy₁ hyj
  have hperm := eraseIdxs_two_perm hne Ctx.hL hej
  have hgetD : Γ.comps.getD j e₁ = ej := by simp [List.getD_eq_getElem?_getD, hej]
  have hS : NewOK (mkC (.G .plus) (liftA 1 ej.x) (newA 0) : Comp (Atom k (n + 1))) :=
    NewOK_G _ (liftA_ne_newA 1 ej.x 0)
  have hbase : EO_oBaseP x Γ i₁ e₁ j = liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] := by
    unfold EO_oBaseP; rw [hgetD]
  rw [hbase]
  have hM2 : labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra) =
      labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra) ++ [] :=
    (List.append_nil _).symm
  have hsx : EO_oSx x ∈ liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra := by simp
  have hgy : EO_oGy e₁ ∈ liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra := by simp
  have hgj : (mkC (.G .plus) (liftA 1 ej.x) (newA 0) : Comp (Atom k (n + 1))) ∈
      liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra := by simp
  have h1 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hsx) (by simp [EO_oSx, mkC])
  have h2 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgy) (by simp [EO_oGy, mkC])
  have h3 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgj) (by simp [mkC])
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have e2 : ej.kind.ord = 1 := by rw [hkj]; rfl
  have h4 : ordL ([EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra ++ []) =
      4 + ordL extra := by
    simp [EO_oSx, EO_oGy, mkC, Kind.ord]
    ring
  have h5 : ordL [e₁, ej] = 2 := by simp [ordL_cons, e1, e2]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (eraseIdxs [i₁, j] Γ.comps)
    [e₁, ej] ([EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra) []
    (labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] ++ extra)) d
    (by simp [List.append_assoc]) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_append (newOK_cons (newOK_oSx x) (newOK_cons (newOK_oGy e₁) (newOK_cons hS newOK_nil)))
        hex)
    newOK_nil
    (by
      simp only [List.append_nil, List.forall_mem_append]
      exact ⟨by simp [EO_oSx, EO_oGy, mkC], hexl⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx₁]
        exact h1.trans h2
      · rw [hyj]
        exact h3.trans h1.symm)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o d hM2 (Or.inl hsx) ⟨.s, rfl⟩)
    (by
      simp only [List.append_nil, List.filter_append, filter_solid_nil hexs]
      simp [EO_oSx, EO_oGy, mkC, Kind.isSolid])
    (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
    (by
      rw [h4, h5]
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨EO_oGy e₁, by simp, by simp [EO_oGy, mkC, Kind.isRandom]⟩⟩
  rw [key.2, h4, h5]
  push_cast
  ring

/-- The term `l3` of `Ô_multi-e`, cases (i) and (iii). -/
private theorem preT_l3 {C : ℕ} {x : Atom k n} {Γ : Graph k n}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (EO_oL3 x Γ), d⟩, liftA 1⟩ ∧
      (⟨labW o (EO_oL3 x Γ), d⟩ : Graph k (n + 1)).ord = Γ.ord + 1 ∧
      ∃ c ∈ EO_oL3 x Γ, c.kind.isRandom = true := by
  have hM2 : labW o (EO_oL3 x Γ) = labW o (EO_oL3 x Γ) ++ [] := (List.append_nil _).symm
  have hsx : EO_oSx x ∈ EO_oL3 x Γ := by simp [EO_oL3]
  have h4 : ordL ([EO_oSx x, mkC (.light .plus) (newA 0) (newA 0)] ++ []) = (3 : ℤ) := by
    simp [EO_oSx, mkC, Kind.ord]
  have key := preT_A (j := 1) hN hP hx hU o Γ.comps [] [EO_oSx x,
      mkC (.light .plus) (newA 0) (newA 0)] []
    (labW o (EO_oL3 x Γ)) d (by simp [EO_oL3]) (by simp)
    (by simp)
    (newOK_cons (newOK_oSx x) (newOK_cons (NewOK_light _ _) newOK_nil)) newOK_nil
    (by simp [EO_oSx, mkC])
    (by simp)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o d hM2 (Or.inl hsx) ⟨.s, rfl⟩)
    (by simp [EO_oSx, mkC, Kind.isSolid])
    (by simp)
    (by rw [h4]; simp)
  refine ⟨key.1, ?_, ⟨mkC (.light .plus) (newA 0) (newA 0),
      by simp [EO_oL3], by simp [mkC, Kind.isRandom]⟩⟩
  rw [key.2, h4]
  simp
  ring

/-- The terms `e1` and `e2` of `Ô_multi-e`, case (i): the first edge `G_{x y₁}` becomes the path
`x – α – y₁` with a further solid edge at `α`. -/
private theorem preT_e12 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) (mid : Comp (Atom k (n + 1)))
    (hmid : NewOK mid) (hmids : mid.kind.isSolid = true) (hmidl : mid.label = none)
    (hmidk : mid.kind ≠ .xdot) (hmidx : (mid.x = liftA 1 x ∧ mid.y = newA 0) ∨
      (mid.x = newA 0 ∧ mid.y = liftA 1 x)) (hmido : mid.kind.ord = 1)
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁]), d⟩,
      liftA 1⟩ ∧
      (⟨labW o (liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁]), d⟩ :
        Graph k (n + 1)).ord = Γ.ord + 1 ∧
      ∃ c ∈ liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁], c.kind.isRandom = true := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  have hperm := eraseIdx_perm Ctx.hL
  have hM2 : labW o (liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁]) =
      labW o (liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁]) ++ [] :=
    (List.append_nil _).symm
  have hsx : EO_oSx x ∈ liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁] := by simp
  have hmm : mid ∈ liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁] := by simp
  have hgy : EO_oGy e₁ ∈ liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁] := by simp
  have h1 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hmm) hmidk
  have h2 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgy) (by simp [EO_oGy, mkC])
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have h4 : ordL ([EO_oSx x, mid, EO_oGy e₁] ++ []) = 4 := by
    simp only [List.append_nil, ordL_cons, ordL_nil, hmido]
    simp [EO_oSx, EO_oGy, mkC, Kind.ord]
  have h5 : ordL [e₁] = 1 := by simp [ordL_cons, e1]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (Γ.comps.eraseIdx i₁)
    [e₁] [EO_oSx x, mid, EO_oGy e₁] []
    (labW o (liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, mid, EO_oGy e₁])) d
    (by simp) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl; simp [Kind.isRandom, *])
    (newOK_cons (newOK_oSx x) (newOK_cons hmid (newOK_cons (newOK_oGy e₁) newOK_nil)))
    newOK_nil
    (by
      simp only [List.append_nil]
      exact lab_cons (by simp [EO_oSx, mkC]) (lab_cons hmidl (lab_cons (by simp [EO_oGy, mkC]) lab_nil)))
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      rw [hx₁]
      rcases hmidx with ⟨a, b⟩ | ⟨a, b⟩
      · have := h1
        rw [a, b] at this
        exact this.trans h2
      · have := h1
        rw [a, b] at this
        exact this.symm.trans h2)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o d hM2 (Or.inl hsx) ⟨.s, rfl⟩)
    (by
      have hsxs : (EO_oSx x).kind.isSolid = false := rfl
      have hgys : (EO_oGy e₁).kind.isSolid = true := rfl
      simp [hsxs, hmids, hgys])
    (by simp)
    (by
      rw [h4, h5]
      push_cast)
  refine ⟨key.1, ?_, ⟨EO_oGy e₁, by simp, by simp [EO_oGy, mkC, Kind.isRandom]⟩⟩
  rw [key.2, h4, h5]
  push_cast
  try ring

end OutTerms2

section XIdx

private theorem perm_aux {α : Type*} (xe fL : List α) (e : α) :
    (xe ++ fL ++ [e]).Perm (fL ++ (e :: xe)) := by
  have h : (fL ++ (e :: xe)).Perm (xe ++ fL ++ [e]) := by
    rw [← Multiset.coe_eq_coe]
    have : (e :: xe) = [e] ++ xe := rfl
    rw [this]
    simp only [← Multiset.coe_add]
    abel
  exact h.symm

variable {k n : ℕ}

private theorem mem_eraseIdxs_iff {α : Type*} {is : List ℕ} {l : List α} {c : α} :
    c ∈ eraseIdxs is l ↔ ∃ i, l[i]? = some c ∧ i ∉ is := by
  rw [eraseIdxs_eq, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?] at hp
    refine ⟨p.2, hp.1, ?_⟩
    simpa using hp.2
  · rintro ⟨i, hi, hn⟩
    refine ⟨(c, i), ?_, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?]
    exact ⟨hi, by simpa using hn⟩

private theorem mem_oXIdx {Γ : Graph k n} {x : Atom k n} {j : ℕ} :
    j ∈ EO_oXIdx x Γ ↔ ∃ c, Γ.comps[j]? = some c ∧ ∃ ch, c.kind = .G ch ∧
      ((c.x = x ∧ c.y ≠ x) ∨ (c.y = x ∧ c.x ≠ x)) := by
  unfold EO_oXIdx
  simp only [List.mem_append, mem_edgeIdx]
  constructor
  · rintro (((⟨c, h1, h2, h3⟩ | ⟨c, h1, h2, h3⟩) | ⟨c, h1, h2, h3⟩) | ⟨c, h1, h2, h3⟩)
    · exact ⟨c, h1, _, h2, Or.inl h3⟩
    · exact ⟨c, h1, _, h2, Or.inl h3⟩
    · exact ⟨c, h1, _, h2, Or.inr h3⟩
    · exact ⟨c, h1, _, h2, Or.inr h3⟩
  · rintro ⟨c, h1, ch, h2, h3 | h3⟩
    · cases ch
      · exact Or.inl (Or.inl (Or.inl ⟨c, h1, h2, h3⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨c, h1, h2, h3⟩))
    · cases ch
      · exact Or.inl (Or.inr ⟨c, h1, h2, h3⟩)
      · exact Or.inr ⟨c, h1, h2, h3⟩

private theorem oXIdx_nodup (x : Atom k n) (Γ : Graph k n) : (EO_oXIdx x Γ).Nodup := by
  unfold EO_oXIdx
  have n1 := edgeIdx_nodup Γ x .plus true
  have n2 := edgeIdx_nodup Γ x .minus true
  have n3 := edgeIdx_nodup Γ x .plus false
  have n4 := edgeIdx_nodup Γ x .minus false
  simp only [List.nodup_append]
  refine ⟨⟨⟨n1, n2, ?_⟩, n3, ?_⟩, n4, ?_⟩
  · intro a ha b hb hab
    subst hab
    exact edgeIdx_disjoint (Or.inl (by simp)) ha hb
  · intro a ha b hb hab
    subst hab
    rcases List.mem_append.1 ha with ha | ha
    · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
    · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
  · intro a ha b hb hab
    subst hab
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
      · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
    · exact edgeIdx_disjoint (Or.inl (by simp)) ha hb

private theorem oXIdx_mem_i₁ {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) : i₁ ∈ EO_oXIdx x Γ := by
  have : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
  unfold EO_oXIdx
  simp [this]

private theorem xe_fL_perm {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) :
    (pickIdxs ((EO_oXIdx x Γ).filter (· != i₁)) Γ.comps ++ eraseIdxs (EO_oXIdx x Γ) Γ.comps ++
      [e₁]).Perm Γ.comps := by
  have hnd := oXIdx_nodup x Γ
  have hmem := oXIdx_mem_i₁ Ctx
  have hP1 := pickIdxs_perm ((EO_oXIdx x Γ).filter (· != i₁))
    (hnd.sublist (List.filter_sublist)) Γ.comps
  have hP2 := pickIdxs_perm (EO_oXIdx x Γ) hnd Γ.comps
  have hxI : (EO_oXIdx x Γ).Perm (i₁ :: (EO_oXIdx x Γ).filter (· != i₁)) := by
    have := List.perm_cons_erase hmem
    rwa [hnd.erase_eq_filter] at this
  have hP3 := hxI.filterMap (fun i => Γ.comps[i]?)
  simp only [List.filterMap_cons, Ctx.hL] at hP3
  have hall : (pickIdxs (EO_oXIdx x Γ) Γ.comps).Perm
      (e₁ :: pickIdxs ((EO_oXIdx x Γ).filter (· != i₁)) Γ.comps) :=
    hP2.trans (hP3.trans (hP1.symm.cons e₁))
  have h1 := eraseIdxs_pick_perm (EO_oXIdx x Γ) Γ.comps
  refine List.Perm.trans ?_ ((hall.symm.append_left _).trans h1)
  exact perm_aux _ _ _

end XIdx

section DsTerm

variable {k n : ℕ}

private theorem dPieces_has_q {V : Type*} [DecidableEq V] {p q : V} {c : Comp V} {ps : List (Comp
    V)}
    (h : c.dPieces p q = some ps) : ∃ c₂ ∈ ps, c₂.x = q ∨ c₂.y = q := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨solidC .plus q c.endB, by simp, Or.inl (solidC_x _ _ _)⟩
  · exact ⟨solidC .minus c.x q, by simp, Or.inr (solidC_y _ _ _)⟩

private theorem wt_zero_imp {Γ : Graph k n} {x : Atom k n} (h : Γ.wt x = 0) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) :
    c.x ≠ x := by
  intro hcx
  unfold Graph.wt at h
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  have := h c hc
  rcases hk with ⟨ch, hch⟩ | ⟨ch, hch⟩ <;> simp [hch, hcx] at this

private theorem fL_untouched {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    {c : Comp (Atom k n)} (hc : c ∈ eraseIdxs (EO_oXIdx x Γ) Γ.comps) {ch : Charge}
    (hk : c.kind = .G ch) : c.x ≠ x ∧ c.y ≠ x := by
  obtain ⟨i, hi, hn⟩ := mem_eraseIdxs_iff.1 hc
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  have hsl := hN.2.1 c hcm (by simp [hk, Kind.isSolid])
  constructor
  · intro hcx
    exact hn (mem_oXIdx.2 ⟨c, hi, ch, hk, Or.inl ⟨hcx, by rw [← hcx]; exact fun h => hsl h.symm⟩⟩)
  · intro hcy
    exact hn (mem_oXIdx.2 ⟨c, hi, ch, hk, Or.inr ⟨hcy, by rw [← hcy]; exact hsl⟩⟩)

set_option linter.flexible false in
/-- The derivative terms `ds` of `Ô_multi-e`, case (i). -/
private theorem preT_ds {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) (o : Option (Atom k (n + 1)))
    {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x)
      (liftCs 1 (eraseIdxs (EO_oXIdx x Γ) Γ.comps))) (c0 : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (liftCs 1 (pickIdxs ((EO_oXIdx x Γ).filter (· != i₁)) Γ.comps) ++
      d ++ [EO_oSx x, EO_oGy e₁]), c0⟩, liftA 1⟩ ∧
    (Γ.wt x = 0 → Γ.ord + 1 ≤ (⟨labW o (liftCs 1 (pickIdxs ((EO_oXIdx x Γ).filter (· != i₁))
      Γ.comps) ++ d ++ [EO_oSx x, EO_oGy e₁]), c0⟩ : Graph k (n + 1)).ord) ∧
    ∃ c ∈ liftCs 1 (pickIdxs ((EO_oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [EO_oSx x, EO_oGy e₁],
      c.kind.isRandom = true := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  set fL := eraseIdxs (EO_oXIdx x Γ) Γ.comps with hfL
  set xe := pickIdxs ((EO_oXIdx x Γ).filter (· != i₁)) Γ.comps with hxe
  obtain ⟨jj, hjj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hjj' : jj < fL.length := by simpa [liftCs_length] using hjj
  set cj := fL[jj] with hcj
  have hfj : fL[jj]? = some cj := by simp [hcj]
  have hcjmem : cj ∈ fL := List.getElem_mem hjj'
  have hcjΓ : cj ∈ Γ.comps := mem_eraseIdxs_of_mem hcjmem
  have hlift : (liftCs 1 fL)[jj] = cj.map (liftA 1) := by simp [liftCs, hcj]
  have hps' : (cj.map (liftA 1)).dPieces (newA 0) (liftA 1 x) = some ps := by
    rw [← hlift]; exact hps
  have hE : (liftCs 1 fL).eraseIdx jj = liftCs 1 (fL.eraseIdx jj) := by
    unfold liftCs; exact eraseIdx_map _ _ _
  have hperm : (xe ++ fL.eraseIdx jj ++ [cj, e₁]).Perm Γ.comps := by
    have h1 := xe_fL_perm Ctx
    have h2 := eraseIdx_perm hfj
    have h3 : (xe ++ (fL.eraseIdx jj ++ [cj]) ++ [e₁]).Perm Γ.comps :=
      (((h2.append_left xe).append_right [e₁])).trans h1
    simpa [List.append_assoc] using h3
  rw [hE]
  have hP : liftCs 1 xe ++ (liftCs 1 (fL.eraseIdx jj) ++ ps) ++ [EO_oSx x, EO_oGy e₁] =
      liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁]) := by
    simp [liftCs, List.append_assoc]
  rw [hP]
  have hM2 : labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁])) =
      labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁])) ++ [] :=
    (List.append_nil _).symm
  have hpsNew := dPieces_newOK hps'
  have hpsLab := dPieces_label hps'
  have hsxm : EO_oSx x ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁]) := by simp
  have hgym : EO_oGy e₁ ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁]) := by simp
  have h1 := reach_in' (k := k) (n := n) o c0 hM2 (Or.inl hsxm) (by simp [EO_oSx, mkC])
  have h2 := reach_in' (k := k) (n := n) o c0 hM2 (Or.inl hgym) (by simp [EO_oGy, mkC])
  have hcjrand := dPieces_random hps'
  have hcjrand' : cj.kind.isRandom = true := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch,
        h⟩ <;> simp [Comp.map] at h <;> simp [h, Kind.isRandom]
  have hord1 := dPieces_ord_ge hps' (by simp [Comp.map, liftA_ne_newA]) (by
    unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA])
  have hordcj : (cj.map (liftA 1)).kind.ord = cj.kind.ord := rfl
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have hR : ordL [cj, e₁] = cj.kind.ord + 1 := by simp [ordL_cons, e1]
  have hN : ordL (ps ++ [EO_oSx x, EO_oGy e₁]) = ordL ps + 3 := by
    simp [ordL_append, EO_oSx, EO_oGy, mkC, Kind.ord]
  have key := preT_A' (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (xe ++ fL.eraseIdx jj)
    [cj, e₁] (ps ++ [EO_oSx x, EO_oGy e₁]) []
    (labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁]))) c0
    (by simp) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hcjrand'
      · simp [hk₁, Kind.isRandom])
    (newOK_append hpsNew (newOK_cons (newOK_oSx x) (newOK_cons (newOK_oGy e₁) newOK_nil)))
    newOK_nil
    (by
      simp only [List.append_nil]
      exact lab_append hpsLab (lab_cons (by simp [EO_oSx, mkC]) (lab_cons (by simp [EO_oGy, mkC])
          lab_nil)))
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
        · have := dPieces_path (G := (⟨labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++
            (ps ++ [EO_oSx x, EO_oGy e₁])), c0⟩ : Graph k (n + 1)).edgeGraphNoX) hps' ⟨ch, h⟩
            (fun c' hc' => by
              have hmem : c' ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁]) :=
                List.mem_append_right _ (List.mem_append_left _ hc')
              exact reach_in' (k := k) (n := n) o c0 hM2 (Or.inl hmem) (hpsNew c' hc').ne_xdot)
            h1.symm
          simpa [Comp.map] using this
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
      · rw [hx₁]
        exact h1.trans h2)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o c0 hM2 (Or.inl hsxm) ⟨.s, rfl⟩)
    (fun E => unp_conv (by
      set g' : Graph k (n + 1) := ⟨labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++
        (ps ++ [EO_oSx x, EO_oGy e₁])), c0⟩ with hg'
      have hcomps : g'.comps = labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++
        (ps ++ [EO_oSx x, EO_oGy e₁])) := rfl
      have hBsub : ∀ c ∈ xe ++ fL.eraseIdx jj, c ∈ Γ.comps := fun c hc =>
        hperm.subset (List.mem_append_left _ hc)
      have hunp0 : unpartCount g' (liftCs 1 (xe ++ fL.eraseIdx jj)) = 0 := by
        refine unpartCount_eq_zero g' fun c' hc' hs => ?_
        obtain ⟨c, hcB, rfl⟩ := mem_liftCs.1 hc'
        exact partnered_old Ctx.normal E ⟨c, hBsub c hcB, rfl, rfl, rfl⟩ hs
      have hlen : (unpartL g').length =
          unpartCount g' ps + unpartCount g' [EO_oSx x, EO_oGy e₁] := by
        rw [unpartL_length, hcomps, unpartCount_labW, unpartCount_append, hunp0, zero_add,
          unpartCount_append]
      have hps2 : unpartCount g' ps ≤ 2 := by
        have := unpartCount_le g' ps
        rw [dPieces_length hps'] at this
        exact this
      have hsx1 : unpartCount g' [EO_oSx x, EO_oGy e₁] ≤ 1 := by
        refine (unpartCount_le_solid g' _).trans ?_
        simp [EO_oSx, EO_oGy, mkC, Kind.isSolid]
      refine ⟨by omega, fun h3 => ?_⟩
      have h2 : unpartCount g' ps = 2 := by omega
      have h1' : unpartCount g' [EO_oSx x, EO_oGy e₁] = 1 := by omega
      have hGy : partnered g' (EO_oGy e₁) = false := by
        by_contra hcon
        have hcon' : partnered g' (EO_oGy e₁) = true := by simpa using hcon
        unfold unpartCount at h1'
        simp [EO_oSx, EO_oGy, mkC, Kind.isSolid, List.filter_cons] at h1' hcon'
        simp [hcon'] at h1'
      have hall : ∀ c ∈ ps, (c.kind.isSolid && !partnered g' c) = true := by
        have := h2
        unfold unpartCount at this
        rw [← dPieces_length hps'] at this
        exact List.length_filter_eq_length_iff.1 this
      obtain ⟨c₂, hc₂ps, hc₂q⟩ := dPieces_has_q hps'
      have hc₂m : c₂ ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_oGy e₁]) :=
        List.mem_append_right _ (List.mem_append_left _ hc₂ps)
      obtain ⟨c₁'', hc₁'', a1, a2, a3⟩ := labW_exists (o := o) hgym
      obtain ⟨c₂'', hc₂'', b1, b2, b3⟩ := labW_exists (o := o) hc₂m
      refine ⟨c₁'', ?_, c₂'', ?_, ?_⟩
      · refine List.mem_filter.2 ⟨by rw [hcomps]; exact hc₁'', ?_⟩
        have : partnered g' c₁'' = false := by
          rw [partnered_congr g' (c' := EO_oGy e₁) a1 a2]; exact hGy
        simp [a3, EO_oGy, mkC, Kind.isSolid, this]
      · refine List.mem_filter.2 ⟨by rw [hcomps]; exact hc₂'', ?_⟩
        have hh := hall c₂ hc₂ps
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh ⊢
        refine ⟨by rw [b3]; exact hh.1, ?_⟩
        rw [partnered_congr g' (c' := c₂) b1 b2]; exact hh.2
      · unfold SamePair
        rw [a1, a2, b1, b2]
        simp only [EO_oGy, mkC]
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases hc₂q with hq | hq
          · exact liftA_ne_newA 1 x 0 (hq.symm.trans h1)
          · exact hy₁ (liftA_injective 1 (h2.symm.trans hq))
        · rcases hc₂q with hq | hq
          · exact hy₁ (liftA_injective 1 (h1.symm.trans hq))
          · exact liftA_ne_newA 1 x 0 (hq.symm.trans h2)))
    (by
      have := dPieces_length hps'
      simp only [List.length_append, List.length_cons, List.length_nil, this]
      omega)
    (by
      rw [List.append_nil, hR, hN]
      obtain ⟨h5, h6⟩ := hord1
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨EO_oGy e₁, by simp, by simp [EO_oGy, mkC, Kind.isRandom]⟩⟩
  intro hwt
  rw [key.2, List.append_nil, hR, hN]
  have hnt : cj.x ≠ x ∧ (cj.map (liftA 1)).endB ≠ liftA 1 x := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
    · have hch : cj.kind = .G ch := by simpa [Comp.map] using h
      obtain ⟨a, b⟩ := fL_untouched Ctx.normal hcjmem hch
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => b (liftA_injective 1 hh)
    · have hch : cj.kind = .weight ch := by simpa [Comp.map] using h
      have a := wt_zero_imp hwt hcjΓ (Or.inl ⟨ch, hch⟩)
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => a (liftA_injective 1 hh)
    · have hch : cj.kind = .light ch := by simpa [Comp.map] using h
      have a := wt_zero_imp hwt hcjΓ (Or.inr ⟨ch, hch⟩)
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => a (liftA_injective 1 hh)
  have h2 := dPieces_ord_two hps' (by simp [Comp.map, liftA_ne_newA])
    (by unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA])
    (by simpa [Comp.map] using fun hh => hnt.1 (liftA_injective 1 hh)) hnt.2
  obtain ⟨-, h6⟩ := hord1
  rw [h2]
  push_cast
  linarith

end DsTerm

section OutSpec

variable {k n : ℕ}

private theorem labW_some_not_lf {j : ℕ} (u : Atom k (n + j)) (P N₂ : List (Comp (Atom k (n + j))))
    (d : Coeff) (h : ∃ c ∈ P, c.kind.isRandom = true) :
    ¬ (⟨labW (some u) P ++ N₂, d⟩ : Graph k (n + j)).LabelFree := by
  obtain ⟨c, hc, hr⟩ := h
  intro hlf
  have hm : c.labelQ u ∈ (⟨labW (some u) P ++ N₂, d⟩ : Graph k (n + j)).comps :=
    List.mem_append_left _ (mem_labelQs.2 ⟨c, hc, rfl⟩)
  have := hlf _ hm
  unfold Comp.labelQ at this
  simp [hr] at this

private theorem labelQs_not_lf {m : ℕ} (u : Atom k m) (L : List (Comp (Atom k m))) (d : Coeff)
    (h : ∃ c ∈ L, c.kind.isRandom = true) :
    ¬ (⟨labelQs u L, d⟩ : Graph k m).LabelFree := by
  obtain ⟨c, hc, hr⟩ := h
  intro hlf
  have hm : c.labelQ u ∈ (⟨labelQs u L, d⟩ : Graph k m).comps := mem_labelQs.2 ⟨c, hc, rfl⟩
  have := hlf _ hm
  unfold Comp.labelQ at this
  simp [hr] at this

/-- The bare main terms of `Ô_multi-e`, case (i). -/
def BaseOut (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n))
    (t : Tracked k n) : Prop :=
  ∃ j d, (j ∈ Γ.edgeIdx x .minus true ∧ t = EO_t1 (EO_oBaseM x Γ i₁ e₁ j) d) ∨
    (j ∈ Γ.edgeIdx x .plus false ∧ t = EO_t1 (EO_oBaseP x Γ i₁ e₁ j) d)

private theorem comp_map_id' {V : Type*} (c : Comp V) : c.map id = c := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp [Comp.map]

private theorem preT_self {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none) (c0 : Coeff) :
    PreT C Γ.ord x ⟨n, ⟨labelQs x Γ.comps, c0⟩, id⟩ ∧
      (⟨labelQs x Γ.comps, c0⟩ : Graph k n).ord = Γ.ord := by
  set g' : Graph k n := ⟨labelQs x Γ.comps, c0⟩ with hg'
  have hcomps : g'.comps = labelQs x Γ.comps := rfl
  have hinj : Function.Injective (id : Atom k n → Atom k n) := Function.injective_id
  have E : ExtData (id : Atom k n → Atom k n) Γ x g' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc hr
      rw [hcomps, comp_map_id']
      refine mem_labelQs.2 ⟨c, hc, ?_⟩
      unfold Comp.labelQ; simp [hr]
    · intro c' hc'
      rw [hcomps] at hc'
      obtain ⟨c, hc, rfl⟩ := mem_labelQs.1 hc'
      have := (srcOK_lift (φ := (id : Atom k n → Atom k n)) hc).labelQ hinj hN hP x
      rwa [comp_map_id'] at this
    · intro c hc hk hne
      have hm : c.labelQ x ∈ g'.comps := by
        rw [hcomps]; exact mem_labelQs.2 ⟨c, hc, rfl⟩
      have := reach_of_comp_noX g' hm (by simpa using hk)
      simpa using this
    · intro u hu
      exact absurd rfl (hu u)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ExtData.props hinj (fun v => rfl) hN hP hx E
  have hunp : (unpartL g').length = 0 := by
    rw [unpartL_length]
    refine unpartCount_eq_zero g' fun c' hc' hs => ?_
    rw [hcomps] at hc'
    obtain ⟨c, hc, rfl⟩ := mem_labelQs.1 hc'
    exact partnered_old hN E ⟨c, hc, by simp, by simp, by simp⟩ hs
  have hord : g'.ord = Γ.ord := by
    simp only [Graph.ord_eq, hg', ordL_labelQs]
  have hunp' : (unpartL g').length ≤ 3 ∧ ((unpartL g').length = 3 →
      ∃ c₁ ∈ unpartL g', ∃ c₂ ∈ unpartL g', ¬ SamePair c₁ c₂) :=
    ⟨by omega, fun h => by omega⟩
  refine ⟨⟨?_, h1, h2, h3, h4, h5, unp_conv hunp', h6, ⟨?_, unlabelled_dots E hU⟩, ?_,
    fun u hu => absurd rfl (hu u)⟩, hord⟩
  · have := hN.1.size
    simp only [hcomps, labelQs_length]
    omega
  · exact labels_le_one (u := x) (label_labelQs x hU)
  · rw [hord]

theorem oOut_spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) :
    ∀ t ∈ EO_oOut x Γ i₁ is₂ e₁, PreT C Γ.ord x t ∧
      (¬ t.g.LabelFree ∨ (Γ.wt x = 0 → Γ.ord + 1 ≤ t.g.ord) ∨ BaseOut x Γ i₁ e₁ t) := by
  intro t ht
  have light_ord : ∀ ch : Charge, ordL ([mkC (.light ch) (liftA 1 x) (liftA 1 x)] :
      List (Comp (Atom k (n + 1)))) = 1 := by
    intro ch; simp [ordL, mkC, Kind.ord]
  simp only [EO_oOut, List.mem_append, List.mem_map, List.mem_singleton, List.mem_ite_nil_left] at ht
  rcases ht with
    ((((((((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) |
      ⟨hne, rfl⟩) | ⟨hne, rfl⟩) | ⟨d, hd, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) |
      ⟨hne, rfl⟩) | ⟨hne, rfl⟩) | ⟨d, hd, rfl⟩)
  · -- baseM
    have h := preT_baseM Ctx hj none [] newOK_nil (by simp) (by simp) (by simp) (by simp) (cm * cmb
        * Γ.coeff)
    refine ⟨?_, Or.inr (Or.inr ⟨j, _, Or.inl ⟨hj, rfl⟩⟩)⟩
    simpa [labW, EO_t1] using h.1
  · -- baseP
    have h := preT_baseP Ctx hj none [] newOK_nil (by simp) (by simp) (by simp) (by simp) (cm * cm
        * Γ.coeff)
    refine ⟨?_, Or.inr (Or.inr ⟨j, _, Or.inr ⟨hj, rfl⟩⟩)⟩
    simpa [labW, EO_t1] using h.1
  · -- baseM with a light weight
    have h := preT_baseM Ctx hj none [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]
      (newOK_cons (NewOK_light _ _) newOK_nil) (by simp [mkC, Kind.isSolid]) (by simp [mkC])
      (by simp [ordL, mkC, Kind.ord]) (by simp) (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1]
    rw [light_ord _] at this
    linarith
  · -- baseP with a light weight
    have h := preT_baseP Ctx hj none [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]
      (newOK_cons (NewOK_light _ _) newOK_nil) (by simp [mkC, Kind.isSolid]) (by simp [mkC])
      (by simp [ordL, mkC, Kind.ord]) (by simp) (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1]
    rw [light_ord _] at this
    linarith
  · -- l3
    have h := preT_l3 Ctx.normal Ctx.plain Ctx.right Ctx.unl none (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1]
    linarith
  · -- e1
    have h := preT_e12 Ctx (mkC (.G .plus) (liftA 1 x) (newA 0)) (NewOK_G _ (liftA_ne_newA 1 x 0))
      (by simp [mkC, Kind.isSolid]) rfl (by simp [mkC]) (Or.inl ⟨rfl,
          rfl⟩) (by simp [mkC, Kind.ord])
      none (((is₂.length : Coeff)) * cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1, EO_oE1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1, EO_oE1]
    linarith
  · -- e2
    have h := preT_e12 Ctx (mkC (.G .minus) (newA 0) (liftA 1 x)) (NewOK_G _ (liftA_ne_newA 1 x
        0).symm)
      (by simp [mkC, Kind.isSolid]) rfl (by simp [mkC]) (Or.inr ⟨rfl,
          rfl⟩) (by simp [mkC, Kind.ord])
      none ((((Γ.edgeIdx x .minus false).length : Coeff)) * cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1, EO_oE2] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1, EO_oE2]
    linarith
  · -- ds
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h := preT_ds Ctx none hd' (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1, EO_oDs] using h.1, Or.inr (Or.inl fun hw => ?_)⟩
    have := h.2.1 hw
    simp only [labW] at this
    simpa [EO_t1] using this
  · -- the term with the labels `Q_x`
    refine ⟨(preT_self Ctx.normal Ctx.plain Ctx.right Ctx.unl _).1, Or.inl ?_⟩
    refine labelQs_not_lf _ _ _ ⟨e₁, Ctx.e₁mem, ?_⟩
    simp [Ctx.e₁spec.1, Kind.isRandom]
  · -- baseM, labelled
    have h := preT_baseM Ctx hj (some (liftA 1 x)) [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]
      (newOK_cons (NewOK_weight _ _) newOK_nil) (by simp [mkC, Kind.isSolid]) (by simp [mkC])
      (by simp [ordL, mkC, Kind.ord]) (by simp) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · -- baseP, labelled
    have h := preT_baseP Ctx hj (some (liftA 1 x)) [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]
      (newOK_cons (NewOK_weight _ _) newOK_nil) (by simp [mkC, Kind.isSolid]) (by simp [mkC])
      (by simp [ordL, mkC, Kind.ord]) (by simp) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · -- l3, labelled
    have h := preT_l3 Ctx.normal Ctx.plain Ctx.right Ctx.unl (some (liftA 1 x)) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · -- e1, labelled
    have h := preT_e12 Ctx (mkC (.G .plus) (liftA 1 x) (newA 0)) (NewOK_G _ (liftA_ne_newA 1 x 0))
      (by simp [mkC, Kind.isSolid]) rfl (by simp [mkC]) (Or.inl ⟨rfl,
          rfl⟩) (by simp [mkC, Kind.ord])
      (some (liftA 1 x)) (-(is₂.length : Coeff) * cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1, EO_oE1] using h.1,
      Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · -- e2, labelled
    have h := preT_e12 Ctx (mkC (.G .minus) (newA 0) (liftA 1 x)) (NewOK_G _ (liftA_ne_newA 1 x
        0).symm)
      (by simp [mkC, Kind.isSolid]) rfl (by simp [mkC]) (Or.inr ⟨rfl,
          rfl⟩) (by simp [mkC, Kind.ord])
      (some (liftA 1 x)) (-((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1, EO_oE2] using h.1,
      Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · -- ds, labelled
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h := preT_ds Ctx (some (liftA 1 x)) hd' (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1, EO_oDs] using h.1,
      Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩

end OutSpec

section InDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges of charge `plus` or `minus` entering `x` ([I, Def 3.11]). -/
def EO_iXIdx : List ℕ := Γ.edgeIdx x .plus false ++ Γ.edgeIdx x .minus false

/-- The solid edge `G_{w₁ α}` taking the place of the first edge `G_{w₁ x}` of charge `plus`
entering `x` ([I, (3.13)]). -/
def EO_iGw : Comp (Atom k (n + 1)) := mkC (.G .plus) (liftA 1 e₁.x) (newA 0)

/-- The components of a main term of [I, (3.13)] in case (iii): the edges `G_{w₁ x}` and `Ḡ_{w_j
x}` are exchanged for `s_{xα} G_{w₁ α} Ḡ_{w_j α}`. -/
def EO_iBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The components of the term of [I, (3.13)] in case (iii) in which `G_{w₁ x}` is exchanged for
`s_{xα} G_{w₁ α} G_{αx}`. -/
def EO_iE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [EO_oSx x, EO_iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)]

/-- The components of the derivative terms of [I, (3.13)] in case (iii). -/
def EO_iDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (EO_iXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((EO_iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [EO_oSx x, EO_iGw e₁]

/-- The terms of `Ô^{(x)}_multi-e` in case (iii) of [I, Def 3.11], for the first edge `G_{w₁ x}`
of charge `plus` entering `x` (at the index `i₁`, the further such edges being at the indices
`is₂`). -/
def EO_iOut : TExpansion k n :=
  (Γ.edgeIdx x .minus false).map (fun j => EO_t1 (EO_iBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .minus false).map (fun j => EO_t1 (EO_iBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [EO_t1 (EO_oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [EO_t1 (EO_iE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (EO_iDs x Γ i₁ e₁).map (fun d => EO_t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus false).map (fun j => EO_t1 (labelQs (liftA 1 x) (EO_iBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [EO_t1 (labelQs (liftA 1 x) (EO_oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [EO_t1 (labelQs (liftA 1 x) (EO_iE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (EO_iDs x Γ i₁ e₁).map (fun d => EO_t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

end InDefs

section InTerms

variable {k n : ℕ}

private theorem dPieces_ord_ge_q {V : Type*} [DecidableEq V] {p q : V} {c : Comp V} {ps : List
    (Comp V)}
    (h : c.dPieces p q = some ps) (hx : c.x ≠ q) (hb : c.endB ≠ q) : 1 ≤ ordL ps := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [ordL_two, ord_solidC, ord_solidC, ite_eq_right (Ne.symm hb)]
    split_ifs <;> simp
  · rw [ordL_two, ord_solidC, ord_solidC, ite_eq_right hx]
    split_ifs <;> simp

private theorem dPieces_has_p {V : Type*} [DecidableEq V] {p q : V} {c : Comp V} {ps : List (Comp
    V)}
    (h : c.dPieces p q = some ps) : ∃ c₂ ∈ ps, c₂.x = p ∨ c₂.y = p := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨solidC .plus c.x p, by simp, Or.inr (solidC_y _ _ _)⟩
  · exact ⟨solidC .minus p c.endB, by simp, Or.inl (solidC_x _ _ _)⟩

/-- The data of case (iii) of [I, Def 3.11]: `Γ` is plain and normal regular with bound `C`,
label-free, `x` is internal, no solid edge leaves `x`, and the edges of charge `plus` entering
`x` are at the indices `i₁ :: is₂`, the first being `e₁`. -/
structure InCtx (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  hIP : Γ.edgeIdx x .plus false = i₁ :: is₂
  hL : Γ.comps[i₁]? = some e₁
  hOP0 : Γ.edgeIdx x .plus true = []
  hOM0 : Γ.edgeIdx x .minus true = []

private theorem InCtx.e₁spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) :
    e₁.kind = .G .plus ∧ e₁.y = x ∧ e₁.x ≠ x := by
  have h : i₁ ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hIP]; exact List.mem_cons_self ..
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hL] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem InCtx.e₁mem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) : e₁ ∈ Γ.comps :=
  List.mem_of_getElem? Ctx.hL

private theorem newOK_iGw (e₁ : Comp (Atom k n)) : NewOK (EO_iGw e₁) :=
  NewOK_G _ (liftA_ne_newA 1 e₁.x 0)

private theorem mem_iXIdx {Γ : Graph k n} {x : Atom k n} {j : ℕ} :
    j ∈ EO_iXIdx x Γ ↔ ∃ c, Γ.comps[j]? = some c ∧ ∃ ch, c.kind = .G ch ∧ (c.y = x ∧ c.x ≠ x) := by
  unfold EO_iXIdx
  simp only [List.mem_append, mem_edgeIdx]
  constructor
  · rintro (⟨c, h1, h2, h3⟩ | ⟨c, h1, h2, h3⟩)
    · exact ⟨c, h1, _, h2, h3⟩
    · exact ⟨c, h1, _, h2, h3⟩
  · rintro ⟨c, h1, ch, h2, h3⟩
    cases ch
    · exact Or.inl ⟨c, h1, h2, h3⟩
    · exact Or.inr ⟨c, h1, h2, h3⟩

private theorem iXIdx_nodup (x : Atom k n) (Γ : Graph k n) : (EO_iXIdx x Γ).Nodup := by
  unfold EO_iXIdx
  have n3 := edgeIdx_nodup Γ x .plus false
  have n4 := edgeIdx_nodup Γ x .minus false
  simp only [List.nodup_append]
  refine ⟨n3, n4, ?_⟩
  intro a ha b hb hab
  subst hab
  exact edgeIdx_disjoint (Or.inl (by simp)) ha hb

private theorem iXIdx_mem_i₁ {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) : i₁ ∈ EO_iXIdx x Γ := by
  have : i₁ ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hIP]; exact List.mem_cons_self ..
  unfold EO_iXIdx
  simp [this]

private theorem ixe_fL_perm {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) :
    (pickIdxs ((EO_iXIdx x Γ).filter (· != i₁)) Γ.comps ++ eraseIdxs (EO_iXIdx x Γ) Γ.comps ++
      [e₁]).Perm Γ.comps := by
  have hnd := iXIdx_nodup x Γ
  have hmem := iXIdx_mem_i₁ Ctx
  have hP1 := pickIdxs_perm ((EO_iXIdx x Γ).filter (· != i₁))
    (hnd.sublist (List.filter_sublist)) Γ.comps
  have hP2 := pickIdxs_perm (EO_iXIdx x Γ) hnd Γ.comps
  have hxI : (EO_iXIdx x Γ).Perm (i₁ :: (EO_iXIdx x Γ).filter (· != i₁)) := by
    have := List.perm_cons_erase hmem
    rwa [hnd.erase_eq_filter] at this
  have hP3 := hxI.filterMap (fun i => Γ.comps[i]?)
  simp only [List.filterMap_cons, Ctx.hL] at hP3
  have hall : (pickIdxs (EO_iXIdx x Γ) Γ.comps).Perm
      (e₁ :: pickIdxs ((EO_iXIdx x Γ).filter (· != i₁)) Γ.comps) :=
    hP2.trans (hP3.trans (hP1.symm.cons e₁))
  have h1 := eraseIdxs_pick_perm (EO_iXIdx x Γ) Γ.comps
  refine List.Perm.trans ?_ ((hall.symm.append_left _).trans h1)
  exact perm_aux _ _ _

private theorem fL_untouched_in {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁)
    {c : Comp (Atom k n)} (hc : c ∈ eraseIdxs (EO_iXIdx x Γ) Γ.comps) {ch : Charge}
    (hk : c.kind = .G ch) : c.x ≠ x ∧ c.y ≠ x := by
  obtain ⟨i, hi, hn⟩ := mem_eraseIdxs_iff.1 hc
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  have hsl := Ctx.normal.2.1 c hcm (by simp [hk, Kind.isSolid])
  constructor
  · intro hcx
    have hy : c.y ≠ x := by rw [← hcx]; exact fun h => hsl h.symm
    have : i ∈ Γ.edgeIdx x ch true := mem_edgeIdx.2 ⟨c, hi, hk, hcx, hy⟩
    cases ch
    · rw [Ctx.hOP0] at this; simp at this
    · rw [Ctx.hOM0] at this; simp at this
  · intro hcy
    exact hn (mem_iXIdx.2 ⟨c, hi, ch, hk, hcy, by rw [← hcy]; exact hsl⟩)

end InTerms

section InTerms2

variable {k n : ℕ}

/-- The terms `baseM` of `Ô_multi-e`, case (iii), with an extra list of non-solid components. -/
private theorem preT_iBaseM {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) {j : ℕ}
    (hj : j ∈ Γ.edgeIdx x .minus false) (o : Option (Atom k (n + 1)))
    (extra : List (Comp (Atom k (n + 1)))) (hex : ∀ c ∈ extra, NewOK c)
    (hexs : ∀ c ∈ extra, c.kind.isSolid = false) (hexl : ∀ c ∈ extra, c.label = none)
    (hexo : 0 ≤ ordL extra) (hexn : extra.length ≤ 1) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (EO_iBaseM x Γ i₁ e₁ j ++ extra), d⟩, liftA 1⟩ ∧
      (⟨labW o (EO_iBaseM x Γ i₁ e₁ j ++ extra), d⟩ : Graph k (n + 1)).ord = Γ.ord + ordL extra ∧
      ∃ c ∈ EO_iBaseM x Γ i₁ e₁ j ++ extra, c.kind.isRandom = true := by
  obtain ⟨hk₁, hy₁, hx₁⟩ := Ctx.e₁spec
  obtain ⟨ej, hej, hkj, hyj, hxj⟩ := mem_edgeIdx.1 hj
  have hne : i₁ ≠ j := by
    rintro rfl
    rw [Ctx.hL] at hej
    obtain rfl := Option.some.inj hej
    rw [hk₁] at hkj
    cases hkj
  have hperm := eraseIdxs_two_perm hne Ctx.hL hej
  have hgetD : Γ.comps.getD j e₁ = ej := by simp [List.getD_eq_getElem?_getD, hej]
  have hS : NewOK (mkC (.G .minus) (liftA 1 ej.x) (newA 0) : Comp (Atom k (n + 1))) :=
    NewOK_G _ (liftA_ne_newA 1 ej.x 0)
  have hbase : EO_iBaseM x Γ i₁ e₁ j = liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] := by
    unfold EO_iBaseM; rw [hgetD]
  rw [hbase]
  have hM2 : labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra) =
      labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra) ++ [] :=
    (List.append_nil _).symm
  have hsx : EO_oSx x ∈ liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra := by simp
  have hgy : EO_iGw e₁ ∈ liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra := by simp
  have hgj : (mkC (.G .minus) (liftA 1 ej.x) (newA 0) : Comp (Atom k (n + 1))) ∈
      liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra := by simp
  have h1 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hsx) (by simp [EO_oSx, mkC])
  have h2 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgy) (by simp [EO_iGw, mkC])
  have h3 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgj) (by simp [mkC])
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have e2 : ej.kind.ord = 1 := by rw [hkj]; rfl
  have h4 : ordL ([EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra ++ []) =
      4 + ordL extra := by
    simp [EO_oSx, EO_iGw, mkC, Kind.ord]
    ring
  have h5 : ordL [e₁, ej] = 2 := by simp [ordL_cons, e1, e2]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (eraseIdxs [i₁, j] Γ.comps)
    [e₁, ej] ([EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra) []
    (labW o (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] ++ extra)) d
    (by simp [List.append_assoc]) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_append (newOK_cons (newOK_oSx x) (newOK_cons (newOK_iGw e₁) (newOK_cons hS newOK_nil)))
        hex)
    newOK_nil
    (by
      simp only [List.append_nil, List.forall_mem_append]
      exact ⟨by simp [EO_oSx, EO_iGw, mkC], hexl⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hy₁]
        exact h2.trans h1.symm
      · rw [hyj]
        exact h3.trans h1.symm)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o d hM2 (Or.inl hsx) ⟨.s, rfl⟩)
    (by
      simp only [List.append_nil, List.filter_append, filter_solid_nil hexs]
      simp [EO_oSx, EO_iGw, mkC, Kind.isSolid])
    (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
    (by
      rw [h4, h5]
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨EO_iGw e₁, by simp, by simp [EO_iGw, mkC, Kind.isRandom]⟩⟩
  rw [key.2, h4, h5]
  push_cast
  ring

/-- The term `e1` of `Ô_multi-e`, case (iii). -/
private theorem preT_ie1 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁)
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (EO_iE1 x Γ i₁ e₁), d⟩, liftA 1⟩ ∧
      (⟨labW o (EO_iE1 x Γ i₁ e₁), d⟩ : Graph k (n + 1)).ord = Γ.ord + 1 ∧
      ∃ c ∈ EO_iE1 x Γ i₁ e₁, c.kind.isRandom = true := by
  obtain ⟨hk₁, hy₁, hx₁⟩ := Ctx.e₁spec
  have hperm := eraseIdx_perm Ctx.hL
  have hM2 : labW o (EO_iE1 x Γ i₁ e₁) = labW o (EO_iE1 x Γ i₁ e₁) ++ [] := (List.append_nil _).symm
  have hsx : EO_oSx x ∈ EO_iE1 x Γ i₁ e₁ := by simp [EO_iE1]
  have hmm : (mkC (.G .plus) (newA 0) (liftA 1 x) : Comp (Atom k (n + 1))) ∈ EO_iE1 x Γ i₁ e₁ := by
    simp [EO_iE1]
  have hgy : EO_iGw e₁ ∈ EO_iE1 x Γ i₁ e₁ := by simp [EO_iE1]
  have h1 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hmm) (by simp [mkC])
  have h2 := reach_in' (k := k) (n := n) o d hM2 (Or.inl hgy) (by simp [EO_iGw, mkC])
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have h4 : ordL ([EO_oSx x, EO_iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)] ++ []) = 4 := by
    simp [EO_oSx, EO_iGw, mkC, Kind.ord]
  have h5 : ordL [e₁] = 1 := by simp [ordL_cons, e1]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (Γ.comps.eraseIdx i₁)
    [e₁] [EO_oSx x, EO_iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)] []
    (labW o (EO_iE1 x Γ i₁ e₁)) d
    (by simp [EO_iE1]) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl; simp [Kind.isRandom, *])
    (newOK_cons (newOK_oSx x) (newOK_cons (newOK_iGw e₁)
      (newOK_cons (NewOK_G _ (liftA_ne_newA 1 x 0).symm) newOK_nil)))
    newOK_nil
    (by
      simp only [List.append_nil]
      exact lab_cons (by simp [EO_oSx, mkC]) (lab_cons (by simp [EO_iGw, mkC]) (lab_cons (by simp [mkC])
          lab_nil)))
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      rw [hy₁]
      exact h2.trans h1)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o d hM2 (Or.inl hsx) ⟨.s, rfl⟩)
    (by
      simp [EO_oSx, EO_iGw, mkC, Kind.isSolid])
    (by simp)
    (by
      rw [h4, h5]
      push_cast)
  refine ⟨key.1, ?_, ⟨EO_iGw e₁, by simp [EO_iE1], by simp [EO_iGw, mkC, Kind.isRandom]⟩⟩
  rw [key.2, h4, h5]
  push_cast
  try ring

end InTerms2

section InTerms3

variable {k n : ℕ}

set_option linter.flexible false in
/-- The derivative terms `ds` of `Ô_multi-e`, case (iii). -/
private theorem preT_ids {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) (o : Option (Atom k (n + 1)))
    {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ dTerms (liftA 1 x : Atom k (n + 1)) (newA 0)
      (liftCs 1 (eraseIdxs (EO_iXIdx x Γ) Γ.comps))) (c0 : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (liftCs 1 (pickIdxs ((EO_iXIdx x Γ).filter (· != i₁)) Γ.comps) ++
      d ++ [EO_oSx x, EO_iGw e₁]), c0⟩, liftA 1⟩ ∧
    (Γ.wt x = 0 → Γ.ord + 1 ≤ (⟨labW o (liftCs 1 (pickIdxs ((EO_iXIdx x Γ).filter (· != i₁))
      Γ.comps) ++ d ++ [EO_oSx x, EO_iGw e₁]), c0⟩ : Graph k (n + 1)).ord) ∧
    ∃ c ∈ liftCs 1 (pickIdxs ((EO_iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [EO_oSx x, EO_iGw e₁],
      c.kind.isRandom = true := by
  obtain ⟨hk₁, hy₁, hx₁⟩ := Ctx.e₁spec
  set fL := eraseIdxs (EO_iXIdx x Γ) Γ.comps with hfL
  set xe := pickIdxs ((EO_iXIdx x Γ).filter (· != i₁)) Γ.comps with hxe
  obtain ⟨jj, hjj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hjj' : jj < fL.length := by simpa [liftCs_length] using hjj
  set cj := fL[jj] with hcj
  have hfj : fL[jj]? = some cj := by simp [hcj]
  have hcjmem : cj ∈ fL := List.getElem_mem hjj'
  have hcjΓ : cj ∈ Γ.comps := mem_eraseIdxs_of_mem hcjmem
  have hlift : (liftCs 1 fL)[jj] = cj.map (liftA 1) := by simp [liftCs, hcj]
  have hps' : (cj.map (liftA 1)).dPieces (liftA 1 x) (newA 0) = some ps := by
    rw [← hlift]; exact hps
  have hE : (liftCs 1 fL).eraseIdx jj = liftCs 1 (fL.eraseIdx jj) := by
    unfold liftCs; exact eraseIdx_map _ _ _
  have hperm : (xe ++ fL.eraseIdx jj ++ [cj, e₁]).Perm Γ.comps := by
    have h1 := ixe_fL_perm Ctx
    have h2 := eraseIdx_perm hfj
    have h3 : (xe ++ (fL.eraseIdx jj ++ [cj]) ++ [e₁]).Perm Γ.comps :=
      (((h2.append_left xe).append_right [e₁])).trans h1
    simpa [List.append_assoc] using h3
  rw [hE]
  have hP : liftCs 1 xe ++ (liftCs 1 (fL.eraseIdx jj) ++ ps) ++ [EO_oSx x, EO_iGw e₁] =
      liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁]) := by
    simp [liftCs, List.append_assoc]
  rw [hP]
  have hM2 : labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁])) =
      labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁])) ++ [] :=
    (List.append_nil _).symm
  have hpsNew := dPieces_newOK hps'
  have hpsLab := dPieces_label hps'
  have hsxm : EO_oSx x ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁]) := by simp
  have hgym : EO_iGw e₁ ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁]) := by simp
  have h1 := reach_in' (k := k) (n := n) o c0 hM2 (Or.inl hsxm) (by simp [EO_oSx, mkC])
  have h2 := reach_in' (k := k) (n := n) o c0 hM2 (Or.inl hgym) (by simp [EO_iGw, mkC])
  have hcjrand := dPieces_random hps'
  have hcjrand' : cj.kind.isRandom = true := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch,
        h⟩ <;> simp [Comp.map] at h <;> simp [h, Kind.isRandom]
  have hordge := dPieces_ord_ge_q hps' (by simp [Comp.map, liftA_ne_newA]) (by
    unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA])
  have hordle : cj.kind.ord ≤ 1 := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [Comp.map] at h <;>
      simp [h, Kind.ord]
  have hordcj : (cj.map (liftA 1)).kind.ord = cj.kind.ord := rfl
  have e1 : e₁.kind.ord = 1 := by rw [hk₁]; rfl
  have hR : ordL [cj, e₁] = cj.kind.ord + 1 := by simp [ordL_cons, e1]
  have hN : ordL (ps ++ [EO_oSx x, EO_iGw e₁]) = ordL ps + 3 := by
    simp [ordL_append, EO_oSx, EO_iGw, mkC, Kind.ord]
  have key := preT_A' (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (xe ++ fL.eraseIdx jj)
    [cj, e₁] (ps ++ [EO_oSx x, EO_iGw e₁]) []
    (labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁]))) c0
    (by simp) hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hcjrand'
      · simp [hk₁, Kind.isRandom])
    (newOK_append hpsNew (newOK_cons (newOK_oSx x) (newOK_cons (newOK_iGw e₁) newOK_nil)))
    newOK_nil
    (by
      simp only [List.append_nil]
      exact lab_append hpsLab (lab_cons (by simp [EO_oSx, mkC]) (lab_cons (by simp [EO_iGw, mkC])
          lab_nil)))
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
        · have := dPieces_path (G := (⟨labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++
            (ps ++ [EO_oSx x, EO_iGw e₁])), c0⟩ : Graph k (n + 1)).edgeGraphNoX) hps' ⟨ch, h⟩
            (fun c' hc' => by
              have hmem : c' ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁]) :=
                List.mem_append_right _ (List.mem_append_left _ hc')
              exact reach_in' (k := k) (n := n) o c0 hM2 (Or.inl hmem) (hpsNew c' hc').ne_xdot)
            h1
          simpa [Comp.map] using this
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
      · rw [hy₁]
        exact h2.trans h1.symm)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' o c0 hM2 (Or.inl hsxm) ⟨.s, rfl⟩)
    (fun E => unp_conv (by
      set g' : Graph k (n + 1) := ⟨labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++
        (ps ++ [EO_oSx x, EO_iGw e₁])), c0⟩ with hg'
      have hcomps : g'.comps = labW o (liftCs 1 (xe ++ fL.eraseIdx jj) ++
        (ps ++ [EO_oSx x, EO_iGw e₁])) := rfl
      have hBsub : ∀ c ∈ xe ++ fL.eraseIdx jj, c ∈ Γ.comps := fun c hc =>
        hperm.subset (List.mem_append_left _ hc)
      have hunp0 : unpartCount g' (liftCs 1 (xe ++ fL.eraseIdx jj)) = 0 := by
        refine unpartCount_eq_zero g' fun c' hc' hs => ?_
        obtain ⟨c, hcB, rfl⟩ := mem_liftCs.1 hc'
        exact partnered_old Ctx.normal E ⟨c, hBsub c hcB, rfl, rfl, rfl⟩ hs
      have hlen : (unpartL g').length =
          unpartCount g' ps + unpartCount g' [EO_oSx x, EO_iGw e₁] := by
        rw [unpartL_length, hcomps, unpartCount_labW, unpartCount_append, hunp0, zero_add,
          unpartCount_append]
      have hps2 : unpartCount g' ps ≤ 2 := by
        have := unpartCount_le g' ps
        rw [dPieces_length hps'] at this
        exact this
      have hsx1 : unpartCount g' [EO_oSx x, EO_iGw e₁] ≤ 1 := by
        refine (unpartCount_le_solid g' _).trans ?_
        simp [EO_oSx, EO_iGw, mkC, Kind.isSolid]
      refine ⟨by omega, fun h3 => ?_⟩
      have h2 : unpartCount g' ps = 2 := by omega
      have h1' : unpartCount g' [EO_oSx x, EO_iGw e₁] = 1 := by omega
      have hGy : partnered g' (EO_iGw e₁) = false := by
        by_contra hcon
        have hcon' : partnered g' (EO_iGw e₁) = true := by simpa using hcon
        unfold unpartCount at h1'
        simp [EO_oSx, EO_iGw, mkC, Kind.isSolid, List.filter_cons] at h1' hcon'
        simp [hcon'] at h1'
      have hall : ∀ c ∈ ps, (c.kind.isSolid && !partnered g' c) = true := by
        have := h2
        unfold unpartCount at this
        rw [← dPieces_length hps'] at this
        exact List.length_filter_eq_length_iff.1 this
      obtain ⟨c₂, hc₂ps, hc₂q⟩ := dPieces_has_p hps'
      have hc₂m : c₂ ∈ liftCs 1 (xe ++ fL.eraseIdx jj) ++ (ps ++ [EO_oSx x, EO_iGw e₁]) :=
        List.mem_append_right _ (List.mem_append_left _ hc₂ps)
      obtain ⟨c₁'', hc₁'', a1, a2, a3⟩ := labW_exists (o := o) hgym
      obtain ⟨c₂'', hc₂'', b1, b2, b3⟩ := labW_exists (o := o) hc₂m
      refine ⟨c₁'', ?_, c₂'', ?_, ?_⟩
      · refine List.mem_filter.2 ⟨by rw [hcomps]; exact hc₁'', ?_⟩
        have : partnered g' c₁'' = false := by
          rw [partnered_congr g' (c' := EO_iGw e₁) a1 a2]; exact hGy
        simp [a3, EO_iGw, mkC, Kind.isSolid, this]
      · refine List.mem_filter.2 ⟨by rw [hcomps]; exact hc₂'', ?_⟩
        have hh := hall c₂ hc₂ps
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh ⊢
        refine ⟨by rw [b3]; exact hh.1, ?_⟩
        rw [partnered_congr g' (c' := c₂) b1 b2]; exact hh.2
      · unfold SamePair
        rw [a1, a2, b1, b2]
        simp only [EO_iGw, mkC]
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases hc₂q with hq | hq
          · exact hx₁ (liftA_injective 1 (h1.symm.trans hq))
          · exact liftA_ne_newA 1 x 0 (hq.symm.trans h2)
        · rcases hc₂q with hq | hq
          · exact liftA_ne_newA 1 x 0 (hq.symm.trans h1)
          · exact hx₁ (liftA_injective 1 (h2.symm.trans hq))))
    (by
      have := dPieces_length hps'
      simp only [List.length_append, List.length_cons, List.length_nil, this]
      omega)
    (by
      rw [List.append_nil, hR, hN]
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨EO_iGw e₁, by simp, by simp [EO_iGw, mkC, Kind.isRandom]⟩⟩
  intro hwt
  rw [key.2, List.append_nil, hR, hN]
  have hnt : cj.x ≠ x ∧ (cj.map (liftA 1)).endB ≠ liftA 1 x := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
    · have hch : cj.kind = .G ch := by simpa [Comp.map] using h
      obtain ⟨a, b⟩ := fL_untouched_in Ctx hcjmem hch
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => b (liftA_injective 1 hh)
    · have hch : cj.kind = .weight ch := by simpa [Comp.map] using h
      have a := wt_zero_imp hwt hcjΓ (Or.inl ⟨ch, hch⟩)
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => a (liftA_injective 1 hh)
    · have hch : cj.kind = .light ch := by simpa [Comp.map] using h
      have a := wt_zero_imp hwt hcjΓ (Or.inr ⟨ch, hch⟩)
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => a (liftA_injective 1 hh)
  have h2 := dPieces_ord_two hps' (by simpa [Comp.map] using fun hh => hnt.1 (liftA_injective 1 hh))
    hnt.2 (by simp [Comp.map, liftA_ne_newA])
    (by unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA])
  rw [h2]
  push_cast
  linarith

end InTerms3

section InSpec

variable {k n : ℕ}

/-- The bare main terms of `Ô_multi-e`, case (iii). -/
def BaseIn (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n))
    (t : Tracked k n) : Prop :=
  ∃ j d, j ∈ Γ.edgeIdx x .minus false ∧ t = EO_t1 (EO_iBaseM x Γ i₁ e₁ j) d

theorem iOut_spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) :
    ∀ t ∈ EO_iOut x Γ i₁ is₂ e₁, PreT C Γ.ord x t ∧
      (¬ t.g.LabelFree ∨ (Γ.wt x = 0 → Γ.ord + 1 ≤ t.g.ord) ∨ BaseIn x Γ i₁ e₁ t) := by
  intro t ht
  have light_ord : ∀ ch : Charge, ordL ([mkC (.light ch) (liftA 1 x) (liftA 1 x)] :
      List (Comp (Atom k (n + 1)))) = 1 := by
    intro ch; simp [ordL, mkC, Kind.ord]
  simp only [EO_iOut, List.mem_append, List.mem_map, List.mem_singleton, List.mem_ite_nil_left] at ht
  rcases ht with
    (((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | rfl) | ⟨hne, rfl⟩) | ⟨d, hd, rfl⟩) | rfl) |
      ⟨j, hj, rfl⟩) | rfl) | ⟨hne, rfl⟩) | ⟨d, hd, rfl⟩)
  · have h := preT_iBaseM Ctx hj none [] newOK_nil (by simp) (by simp) (by simp) (by simp)
      (cm * cmb * Γ.coeff)
    refine ⟨?_, Or.inr (Or.inr ⟨j, _, hj, rfl⟩)⟩
    simpa [labW, EO_t1] using h.1
  · have h := preT_iBaseM Ctx hj none [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]
      (newOK_cons (NewOK_light _ _) newOK_nil) (by simp [mkC, Kind.isSolid]) (by simp [mkC])
      (by simp [ordL, mkC, Kind.ord]) (by simp) (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1]
    rw [light_ord] at this
    linarith
  · have h := preT_l3 Ctx.normal Ctx.plain Ctx.right Ctx.unl none (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1]
    linarith
  · have h := preT_ie1 Ctx none ((is₂.length : Coeff) * cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1, EO_iE1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have := h.2.1
    simp only [labW] at this
    simp only [EO_t1]
    linarith
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h := preT_ids Ctx none hd' (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1, EO_iDs] using h.1, Or.inr (Or.inl fun hw => ?_)⟩
    have := h.2.1 hw
    simp only [labW] at this
    simpa [EO_t1] using this
  · refine ⟨(preT_self Ctx.normal Ctx.plain Ctx.right Ctx.unl _).1, Or.inl ?_⟩
    refine labelQs_not_lf _ _ _ ⟨e₁, Ctx.e₁mem, ?_⟩
    simp [Ctx.e₁spec.1, Kind.isRandom]
  · have h := preT_iBaseM Ctx hj (some (liftA 1 x)) [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]
      (newOK_cons (NewOK_weight _ _) newOK_nil) (by simp [mkC, Kind.isSolid]) (by simp [mkC])
      (by simp [ordL, mkC, Kind.ord]) (by simp) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · have h := preT_l3 Ctx.normal Ctx.plain Ctx.right Ctx.unl (some (liftA 1 x)) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · have h := preT_ie1 Ctx (some (liftA 1 x)) (-(is₂.length : Coeff) * cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1, EO_iE1] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h := preT_ids Ctx (some (liftA 1 x)) hd' (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1, EO_iDs] using h.1, Or.inl (labelQs_not_lf _ _ _ h.2.2)⟩

end InSpec

section ZeroLift

variable {k n : ℕ}

private theorem liftA_zero (u : Atom k n) : (liftA 0 u : Atom k (n + 0)) = u := by
  rcases u with a | a <;> simp [liftA]

private theorem liftA_zero_eq : (liftA 0 : Atom k n → Atom k (n + 0)) = id := funext liftA_zero

private theorem liftCs_zero (cs : List (Comp (Atom k n))) :
    (liftCs 0 cs : List (Comp (Atom k (n + 0)))) = cs := by
  unfold liftCs
  simp only [liftA_zero_eq]
  rw [show Comp.map (id : Atom k n → Atom k n) = id from funext comp_map_id', List.map_id]

/-- The master lemma without new atoms: the tracked map is the identity. -/
private theorem preT_A0 {C : ℕ} {Γ : Graph k n} {x : Atom k n}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (o : Option (Atom k n)) (B R : List (Comp (Atom k n)))
    (N₁ N₂ M : List (Comp (Atom k n))) (d : Coeff)
    (hM : M = labW o (B ++ N₁) ++ N₂)
    (hBR : (B ++ R).Perm Γ.comps)
    (hrand : ∀ r ∈ R, r.kind.isRandom = true)
    (hN₁ : ∀ c ∈ N₁, NewOK c) (hN₂ : ∀ c ∈ N₂, NewOK c)
    (hNl : ∀ c ∈ N₁ ++ N₂, c.label = none)
    (hcover : ∀ r ∈ R, r.kind ≠ .xdot → r.x ≠ r.y →
      (⟨M, d⟩ : Graph k n).edgeGraphNoX.Reachable r.x r.y)
    (hsol : ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 2)
    (hlen : (N₁ ++ N₂).length ≤ R.length + 8)
    (hord : ordL R ≤ ordL (N₁ ++ N₂)) :
    PreT C Γ.ord x ⟨n, ⟨M, d⟩, id⟩ ∧
      (⟨M, d⟩ : Graph k n).ord = Γ.ord + ordL (N₁ ++ N₂) - ordL R := by
  have key := preT_A (j := 0) hN hP hx hU o B R N₁ N₂ M d
    (by rw [hM, liftCs_zero]) hBR hrand hN₁ hN₂ hNl
    (fun r hr hk hne => by
      have := hcover r hr hk hne
      rwa [liftA_zero, liftA_zero])
    (fun i => i.elim0) hsol (by simpa using hlen) (by simpa using hord)
  refine ⟨⟨key.1.size, key.1.conn, key.1.int, key.1.noIntDot, key.1.dotOK, key.1.sl, key.1.unp,
    key.1.plain, key.1.lab, key.1.ord, fun u hu => absurd rfl (hu u)⟩, ?_⟩
  have := key.2
  simpa using this

end ZeroLift

section GGDefs2

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n))

/-- Auxiliary: the graph with `n + 2` internal atoms. -/
def EO_t2 (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) : Tracked k n := ⟨n + 2, ⟨cs, d⟩,
    liftA 2⟩

/-- The components of `Γ` other than the two solid edges at the indices `i` and `j`. -/
def EO_ggF : List (Comp (Atom k n)) := eraseIdxs [i, j] Γ.comps

/-- The components `f G_{y'y}` (with the weight `G_{yy}` when `y = y'`) of the main term of
`Ô^{(x)}_GG` ([I, (3.17)]). -/
def EO_ggMain : List (Comp (Atom k n)) := EO_ggF Γ i j ++ [solidC .plus e'.x e.y]

/-- The derivative terms of `f` at `α` in `Ô^{(x)}_GG` ([I, (3.17)]), with one new atom. -/
def EO_ggD1 : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (EO_ggF Γ i j))).map fun d =>
    d ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]

/-- The derivative terms of `f` at `β` in `Ô^{(x)}_GG` ([I, (3.17)]), with two new atoms. -/
def EO_ggD2 : List (List (Comp (Atom k (n + 2)))) :=
  (dTerms (newA 1) (newA 0) (liftCs 2 (EO_ggF Γ i j))).map fun d =>
    d ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]

/-- The terms of `Ô^{(x)}_GG` ([I, (3.17)]) for the edges `e = G_{xy}` at the index `i` and `e' =
G_{y'x}` at the index `j`. -/
def EO_ggOut : TExpansion k n :=
  let a₁ : Atom k (n + 1) := newA 0
  let a₂ : Atom k (n + 2) := newA 0
  let b₂ : Atom k (n + 2) := newA 1
  [⟨n, ⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], cm * Γ.coeff⟩, id⟩,
    EO_t1 (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) a₁, mkC (.light .plus) a₁ a₁])
      (cm * Γ.coeff),
    EO_t2 (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂,
      mkC (.light .plus) b₂ b₂, mkC (.G .plus) a₂ (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) a₂]) (cm * Γ.coeff),
    EO_t1 (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
      mkC (.waved .s) (liftA 1 x) a₁, mkC (.G .plus) a₁ (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) a₁]) (cm * Γ.coeff),
    EO_t2 (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂,
      mkC (.light .plus) a₂ a₂, mkC (.G .plus) b₂ (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) b₂]) (cm * Γ.coeff)] ++
    (EO_ggD1 x Γ i j e e').map (fun d => EO_t1 (d ++ [mkC (.waved .s) (liftA 1 x) a₁]) (cm * Γ.coeff)) ++
    (EO_ggD2 Γ i j e e').map (fun d => EO_t2 (d ++ [mkC (.waved .plus) (liftA 2 x) a₂,
      mkC (.waved .s) a₂ b₂]) (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩,
      EO_t1 (labelQs a₁ (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) a₁ (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) a₁]) ++ [mkC (.waved .plus) (liftA 1 x) a₁]) Γ.coeff,
      ⟨n, ⟨labelQs e.y (EO_ggMain Γ i j e e') ++ [mkC (.waved .plus) x e.y], -cm * Γ.coeff⟩, id⟩,
      EO_t1 (labelQs (liftA 1 x) (liftCs 1 Γ.comps ++ [mkC (.light .plus) a₁ a₁]) ++
        [mkC (.waved .s) (liftA 1 x) a₁]) (-cm * Γ.coeff),
      EO_t2 (labelQs a₂ (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus) b₂ b₂,
        mkC (.G .plus) a₂ (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) a₂]) ++
        [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂]) (-cm * Γ.coeff),
      EO_t1 (labelQs (liftA 1 x) (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
        mkC (.G .plus) a₁ (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) a₁]) ++
        [mkC (.waved .s) (liftA 1 x) a₁]) (-cm * Γ.coeff),
      EO_t2 (labelQs a₂ (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus) a₂ a₂,
        mkC (.G .plus) b₂ (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) b₂]) ++
        [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂]) (-cm * Γ.coeff)] ++
    (EO_ggD1 x Γ i j e e').map (fun d => EO_t1 (labelQs (liftA 1 x) d ++
      [mkC (.waved .s) (liftA 1 x) a₁]) (-cm * Γ.coeff)) ++
    (EO_ggD2 Γ i j e e').map (fun d => EO_t2 (labelQs a₂ d ++ [mkC (.waved .plus) (liftA 2 x) a₂,
      mkC (.waved .s) a₂ b₂]) (-cm * Γ.coeff))

private theorem ggPos_some' {E : TExpansion k n} (h : ggPos x Γ = some E) :
    ∃ i j e e', Γ.edgeIdx x .plus true = [i] ∧ Γ.edgeIdx x .plus false = [j] ∧
      Γ.comps[i]? = some e ∧ Γ.comps[j]? = some e' ∧ Γ.xdotsAt x [i, j] = true ∧
      E = EO_ggOut x Γ i j e e' := by
  unfold ggPos at h
  split_ifs at h
  split at h
  · rename_i i j hi hj
    split at h
    · rename_i e e' he he'
      dsimp only at h
      rw [ite_eq_iff] at h
      rcases h with ⟨_, h⟩ | ⟨hX, h⟩
      · exact absurd h (by simp)
      refine ⟨i, j, e, e', hi, hj, he, he', by simpa using hX, ?_⟩
      exact (Option.some.inj h).symm
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end GGDefs2

section GGCtx

variable {k n : ℕ}

/-- The data of the `GG` expansion: `Γ` is plain and normal regular with bound `C`, label-free,
`x` is internal, and the solid edges attached to `x` are the edge `e` of charge `plus` leaving
`x` (index `i`) and the edge `e'` of charge `plus` entering `x` (index `j`). -/
structure GGCtx (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n)) :
    Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  hPO : Γ.edgeIdx x .plus true = [i]
  hPI : Γ.edgeIdx x .plus false = [j]
  hMO : Γ.edgeIdx x .minus true = []
  hMI : Γ.edgeIdx x .minus false = []
  hi : Γ.comps[i]? = some e
  hj : Γ.comps[j]? = some e'

private theorem GGCtx.espec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k
    n)}
    (Ctx : GGCtx C x Γ i j e e') : e.kind = .G .plus ∧ e.x = x ∧ e.y ≠ x := by
  have h : i ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hPO]; exact List.mem_singleton_self _
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hi] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem GGCtx.e'spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k
    n)}
    (Ctx : GGCtx C x Γ i j e e') : e'.kind = .G .plus ∧ e'.y = x ∧ e'.x ≠ x := by
  have h : j ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hPI]; exact List.mem_singleton_self _
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hj] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem GGCtx.hij {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtx C x Γ i j e e') : i ≠ j := by
  intro hij
  have hj := Ctx.hj
  rw [← hij, Ctx.hi] at hj
  obtain rfl := Option.some.inj hj
  exact Ctx.e'spec.2.2 Ctx.espec.2.1

private theorem GGCtx.perm {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtx C x Γ i j e e') : (EO_ggF Γ i j ++ [e, e']).Perm Γ.comps :=
  eraseIdxs_two_perm Ctx.hij Ctx.hi Ctx.hj

set_option linter.flexible false in
private theorem GGCtx.f_untouched {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e') {c : Comp (Atom k n)}
    (hc : c ∈ EO_ggF Γ i j) {ch : Charge} (hk : c.kind = .G ch) : c.x ≠ x ∧ c.y ≠ x := by
  obtain ⟨m, hm, hn⟩ := mem_eraseIdxs_iff.1 hc
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  have hsl := Ctx.normal.2.1 c hcm (by simp [hk, Kind.isSolid])
  have hmi : m ≠ i := fun h => hn (by simp [h])
  have hmj : m ≠ j := fun h => hn (by simp [h])
  constructor
  · intro hcx
    have hy : c.y ≠ x := by rw [← hcx]; exact fun h => hsl h.symm
    have : m ∈ Γ.edgeIdx x ch true := mem_edgeIdx.2 ⟨c, hm, hk, hcx, hy⟩
    cases ch
    · rw [Ctx.hPO] at this; simp at this; exact hmi this
    · rw [Ctx.hMO] at this; simp at this
  · intro hcy
    have hxx : c.x ≠ x := by rw [← hcy]; exact hsl
    have : m ∈ Γ.edgeIdx x ch false := mem_edgeIdx.2 ⟨c, hm, hk, hcy, hxx⟩
    cases ch
    · rw [Ctx.hPI] at this; simp at this; exact hmj this
    · rw [Ctx.hMI] at this; simp at this

private theorem GGCtx.e'mem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k
    n)}
    (Ctx : GGCtx C x Γ i j e e') : e' ∈ Γ.comps := List.mem_of_getElem? Ctx.hj

private theorem GGCtx.emem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtx C x Γ i j e e') : e ∈ Γ.comps := List.mem_of_getElem? Ctx.hi

end GGCtx

section GGTerms

variable {k n : ℕ}

private theorem preT_gg_T2 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 2))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 2,
        ⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1),
        mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [], d⟩,
        liftA 2⟩ ∧
      (⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1),
          mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [],
          d⟩ : Graph k (n + 2)).ord = Γ.ord + 1 ∧
      ∃ c ∈ liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1),
          mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)],
          c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1),
      mkC (.G .plus) (newA 0) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ []) = labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC
      (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [] := rfl
  have h_Ga := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 0) (liftA 2
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gp := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 2 e'.x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_S := reach_in' (k := k) (n := n) (c := mkC (.waved .plus) (liftA 2 x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inl
      (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)] ++ []) = 7 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 2) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
        mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 0)] [] (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved
        .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
        mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ []) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_waved _ _ _) (newOK_cons (NewOK_waved _ _ _) (newOK_cons (NewOK_light _ _)
        (newOK_cons (NewOK_G _ (liftA_ne_newA 2 e.y 0).symm) (newOK_cons (NewOK_G _ (liftA_ne_newA
        2 e'.x 0)) newOK_nil))))) newOK_nil
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl (lab_cons rfl (lab_cons rfl (lab_cons rfl lab_nil))))),
          lab_nil⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_S.trans (h_Ga)
      · rw [he'_y]
        exact h_Gp.trans (h_S.symm))
    (by
      intro i
      fin_cases i
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inl (by simp))
          ⟨_, rfl⟩)
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inl (by simp))
          ⟨_, rfl⟩).trans ((reachW_in' (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inl
          (by simp)) ⟨_, rfl⟩))
      )
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.light .plus) (newA 1) (newA 1), by simp, by simp [mkC, Kind.isRandom]⟩

private theorem preT_gg_Q5 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 2))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 2, ⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.G .plus) (newA 0) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], d⟩, liftA 2⟩ ∧
      (⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
          mkC (.G .plus) (newA 0) (liftA 2 e.y),
          mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1)], d⟩ : Graph k (n + 2)).ord = Γ.ord + 1 ∧
      ∃ c ∈ liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
          mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)],
          c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.G .plus) (newA 0) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) = labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus)
      (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] := rfl
  have h_Ga := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 0) (liftA 2
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gp := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 2 e'.x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_S := reach_in' (k := k) (n := n) (c := mkC (.waved .plus) (liftA 2 x) (newA
      0)) o d hM2 (Or.inr (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inr
      (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)] ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) = 7 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 2) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 0)] [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)] (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.light .plus)
        (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)]) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_light _ _) (newOK_cons (NewOK_G _ (liftA_ne_newA 2 e.y 0).symm) (newOK_cons
        (NewOK_G _ (liftA_ne_newA 2 e'.x 0)) newOK_nil))) (newOK_cons (NewOK_waved _ _ _)
        (newOK_cons (NewOK_waved _ _ _) newOK_nil))
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl (lab_cons rfl lab_nil))),
          (lab_cons rfl (lab_cons rfl lab_nil))⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_S.trans (h_Ga)
      · rw [he'_y]
        exact h_Gp.trans (h_S.symm))
    (by
      intro i
      fin_cases i
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inr (by simp))
          ⟨_, rfl⟩)
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inr (by simp))
          ⟨_, rfl⟩).trans ((reachW_in' (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inr
          (by simp)) ⟨_, rfl⟩))
      )
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.light .plus) (newA 1) (newA 1), by simp, by simp [mkC, Kind.isRandom]⟩

private theorem preT_gg_T4 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 2))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 2,
        ⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
        mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [], d⟩,
        liftA 2⟩ ∧
      (⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
          mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [],
          d⟩ : Graph k (n + 2)).ord = Γ.ord + 1 ∧
      ∃ c ∈ liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
          mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)],
          c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ []) = labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC
      (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.light .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [] := rfl
  have h_Gb := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 1) (liftA 2
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gpb := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 2 e'.x) (newA
      1)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_S := reach_in' (k := k) (n := n) (c := mkC (.waved .plus) (liftA 2 x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inl
      (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.light .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 1)] ++ []) = 7 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 2) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
        mkC (.light .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 1)] [] (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.waved
        .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
        mkC (.light .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ []) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_waved _ _ _) (newOK_cons (NewOK_waved _ _ _) (newOK_cons (NewOK_light _ _)
        (newOK_cons (NewOK_G _ (liftA_ne_newA 2 e.y 1).symm) (newOK_cons (NewOK_G _ (liftA_ne_newA
        2 e'.x 1)) newOK_nil))))) newOK_nil
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl (lab_cons rfl (lab_cons rfl (lab_cons rfl lab_nil))))),
          lab_nil⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_S.trans (h_s.trans (h_Gb))
      · rw [he'_y]
        exact h_Gpb.trans (h_s.symm.trans (h_S.symm)))
    (by
      intro i
      fin_cases i
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inl (by simp))
          ⟨_, rfl⟩)
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inl (by simp))
          ⟨_, rfl⟩).trans ((reachW_in' (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inl
          (by simp)) ⟨_, rfl⟩))
      )
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.light .plus) (newA 0) (newA 0), by simp, by simp [mkC, Kind.isRandom]⟩

private theorem preT_gg_Q7 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 2))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 2, ⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
        mkC (.G .plus) (newA 1) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], d⟩, liftA 2⟩ ∧
      (⟨labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
          mkC (.G .plus) (newA 1) (liftA 2 e.y),
          mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1)], d⟩ : Graph k (n + 2)).ord = Γ.ord + 0 ∧
      ∃ c ∈ liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
          mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)],
          c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
      mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) = labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus)
      (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] := rfl
  have h_Gb := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 1) (liftA 2
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gpb := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 2 e'.x) (newA
      1)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_S := reach_in' (k := k) (n := n) (c := mkC (.waved .plus) (liftA 2 x) (newA
      0)) o d hM2 (Or.inr (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inr
      (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.weight .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 1)] ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) = 6 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 2) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.weight .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 1)] [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)] (labW o (liftCs 2 (EO_ggF Γ i j) ++ [mkC (.weight .plus)
        (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)]) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_weight _ _) (newOK_cons (NewOK_G _ (liftA_ne_newA 2 e.y 1).symm) (newOK_cons
        (NewOK_G _ (liftA_ne_newA 2 e'.x 1)) newOK_nil))) (newOK_cons (NewOK_waved _ _ _)
        (newOK_cons (NewOK_waved _ _ _) newOK_nil))
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl (lab_cons rfl lab_nil))),
          (lab_cons rfl (lab_cons rfl lab_nil))⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_S.trans (h_s.trans (h_Gb))
      · rw [he'_y]
        exact h_Gpb.trans (h_s.symm.trans (h_S.symm)))
    (by
      intro i
      fin_cases i
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inr (by simp))
          ⟨_, rfl⟩)
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o d hM2 (Or.inr (by simp))
          ⟨_, rfl⟩).trans ((reachW_in' (c := mkC (.waved .s) (newA 0) (newA 1)) o d hM2 (Or.inr
          (by simp)) ⟨_, rfl⟩))
      )
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.weight .plus) (newA 0) (newA 0), by simp, by simp [mkC, Kind.isRandom]⟩

private theorem preT_gg_T3 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1,
        ⟨labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
        mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [], d⟩, liftA 1⟩ ∧
      (⟨labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
          mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e.y),
          mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [], d⟩ : Graph k (n + 1)).ord = Γ.ord + 1 ∧
      ∃ c ∈ liftCs 1 (EO_ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
          mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e.y),
          mkC (.G .plus) (liftA 1 e'.x) (newA 0)], c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
      mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ []) = labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC
      (.light .plus) (liftA 1 x) (liftA 1 x), mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [] := rfl
  have h_Ga := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 0) (liftA 1
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gp := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 1 e'.x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (liftA 1 x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.light .plus) (liftA 1 x) (liftA 1 x),
      mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)] ++ []) = 5 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.light .plus) (liftA 1 x) (liftA 1 x), mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)] [] (labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.light
        .plus) (liftA 1 x) (liftA 1 x), mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ []) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_light _ _) (newOK_cons (NewOK_waved _ _ _) (newOK_cons (NewOK_G _
        (liftA_ne_newA 1 e.y 0).symm) (newOK_cons (NewOK_G _ (liftA_ne_newA 1 e'.x 0))
        newOK_nil)))) newOK_nil
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl (lab_cons rfl (lab_cons rfl lab_nil)))), lab_nil⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_s.trans (h_Ga)
      · rw [he'_y]
        exact h_Gp.trans (h_s.symm))
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact (reachW_in' (c := mkC (.waved .s) (liftA 1 x) (newA 0)) o d hM2 (Or.inl (by simp)) ⟨_,
          rfl⟩))
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.light .plus) (liftA 1 x) (liftA 1 x), by simp, by simp [mkC, Kind.isRandom]⟩

private theorem preT_gg_Q6 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1,
        ⟨labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
        mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)], d⟩,
        liftA 1⟩ ∧
      (⟨labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
          mkC (.G .plus) (newA 0) (liftA 1 e.y),
          mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
          d⟩ : Graph k (n + 1)).ord = Γ.ord + 0 ∧
      ∃ c ∈ liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
          mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (newA 0)],
          c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
      mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA
      0)]) = labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
      mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)] := rfl
  have h_Ga := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 0) (liftA 1
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gp := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 1 e'.x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (liftA 1 x) (newA
      0)) o d hM2 (Or.inr (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
      mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)] ++ [mkC (.waved .s) (liftA 1 x) (newA 0)]) = 4 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.weight .plus) (liftA 1 x) (liftA 1 x), mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)] [mkC (.waved .s) (liftA 1 x) (newA 0)] (labW o
        (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
        mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA
        0)]) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_weight _ _) (newOK_cons (NewOK_G _ (liftA_ne_newA 1 e.y 0).symm) (newOK_cons
        (NewOK_G _ (liftA_ne_newA 1 e'.x 0)) newOK_nil))) (newOK_cons (NewOK_waved _ _ _) newOK_nil)
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl (lab_cons rfl lab_nil))), (lab_cons rfl lab_nil)⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_s.trans (h_Ga)
      · rw [he'_y]
        exact h_Gp.trans (h_s.symm))
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact (reachW_in' (c := mkC (.waved .s) (liftA 1 x) (newA 0)) o d hM2 (Or.inr (by simp)) ⟨_,
          rfl⟩))
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.weight .plus) (liftA 1 x) (liftA 1 x), by simp, by simp [mkC, Kind.isRandom]⟩

private theorem preT_gg_Q2 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e')
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 1 x) (newA 0)], d⟩,
        liftA 1⟩ ∧
      (⟨labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
          mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 1 x) (newA 0)],
          d⟩ : Graph k (n + 1)).ord = Γ.ord + 0 ∧
      ∃ c ∈ liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
          mkC (.G .plus) (liftA 1 e'.x) (newA 0)], c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : (labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 1 x) (newA
      0)]) = labW o (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 1 x) (newA 0)] := rfl
  have h_Ga := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 0) (liftA 1
      e.y)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_Gp := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 1 e'.x) (newA
      0)) o d hM2 (Or.inl (by simp)) (by simp [mkC])
  have h_S := reach_in' (k := k) (n := n) (c := mkC (.waved .plus) (liftA 1 x) (newA
      0)) o d hM2 (Or.inr (by simp)) (by simp [mkC])
  have hN : ordL ([mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)] ++ [mkC (.waved .plus) (liftA 1 x) (newA
      0)]) = 4 := by
    simp [ordL, mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by
    simp [ordL_cons, e1, e2]
  have key := preT_A (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j)
    [e, e'] [mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)] [mkC (.waved .plus) (liftA 1 x) (newA 0)] (labW o
        (liftCs 1 (EO_ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 1 x) (newA
        0)]) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_G _ (liftA_ne_newA 1 e.y 0).symm) (newOK_cons (NewOK_G _ (liftA_ne_newA 1
        e'.x 0)) newOK_nil)) (newOK_cons (NewOK_waved _ _ _) newOK_nil)
    (by
      simp only [List.forall_mem_append]
      exact ⟨(lab_cons rfl (lab_cons rfl lab_nil)), (lab_cons rfl lab_nil)⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_S.trans (h_Ga)
      · rw [he'_y]
        exact h_Gp.trans (h_S.symm))
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact (reachW_in' (c := mkC (.waved .plus) (liftA 1 x) (newA 0)) o d hM2 (Or.inr (by simp))
          ⟨_, rfl⟩))
    (by simp [mkC, Kind.isSolid])
    (by simp [mkC])
    (by rw [hN, hR]; norm_num)
  refine ⟨key.1, ?_, ?_⟩
  · rw [key.2, hN, hR]; push_cast; ring
  · exact ⟨mkC (.G .plus) (newA 0) (liftA 1 e.y), by simp, by simp [mkC, Kind.isRandom]⟩

end GGTerms

section GGMain

variable {k n : ℕ}

private theorem solidC_ne_xdot {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).kind ≠ .xdot := by
  unfold solidC; split_ifs <;> simp [mkC]

private theorem solidC_random {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).kind.isRandom = true := by
  unfold solidC; split_ifs <;> simp [mkC, Kind.isRandom]

private theorem ord_solidC_nonneg {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    0 ≤ (solidC ch u v).kind.ord := by
  rw [ord_solidC]; split_ifs <;> simp

/-- The main term `m S⁺_{xy} G_{y'y} f` of `Ô_GG`, with an optional label. -/
private theorem preT_gg_main {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e') (o : Option (Atom k n)) (d : Coeff) :
    PreT C Γ.ord x ⟨n, ⟨labW o (EO_ggMain Γ i j e e') ++ [mkC (.waved .plus) x e.y], d⟩, id⟩ ∧
      (⟨labW o (EO_ggMain Γ i j e e') ++ [mkC (.waved .plus) x e.y], d⟩ : Graph k n).ord =
        Γ.ord + (solidC .plus e'.x e.y).kind.ord ∧
      ∃ c ∈ EO_ggMain Γ i j e e', c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hM2 : labW o (EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) ++ [mkC (.waved .plus) x e.y] =
      labW o (EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) ++ [mkC (.waved .plus) x e.y] := rfl
  have h_S := reach_in' (k := k) (n := n) (j := 0) (c := mkC (.waved .plus) x e.y) o d
    (M := labW o (EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) ++ [mkC (.waved .plus) x e.y])
    (P := EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) (N₂ := [mkC (.waved .plus) x e.y]) rfl
    (Or.inr (by simp)) (by simp [mkC])
  have h_G := reach_in' (k := k) (n := n) (j := 0) (c := solidC .plus e'.x e.y) o d
    (M := labW o (EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) ++ [mkC (.waved .plus) x e.y])
    (P := EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) (N₂ := [mkC (.waved .plus) x e.y]) rfl
    (Or.inl (by simp)) (solidC_ne_xdot _ _ _)
  rw [solidC_x, solidC_y] at h_G
  have hN : ordL ([solidC .plus e'.x e.y] ++ [mkC (.waved .plus) x e.y]) =
      (solidC .plus e'.x e.y).kind.ord + 2 := by
    simp [mkC, Kind.ord]
  have hR : ordL [e, e'] = 2 := by simp [ordL_cons, e1, e2]
  have key := preT_A0 Ctx.normal Ctx.plain Ctx.right Ctx.unl o (EO_ggF Γ i j) [e, e']
    [solidC .plus e'.x e.y] [mkC (.waved .plus) x e.y]
    (labW o (EO_ggF Γ i j ++ [solidC .plus e'.x e.y]) ++ [mkC (.waved .plus) x e.y]) d rfl Ctx.perm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Kind.isRandom, *])
    (newOK_cons (NewOK_solidC _ _ _) newOK_nil) (newOK_cons (NewOK_waved _ _ _) newOK_nil)
    (by
      simp only [List.forall_mem_append]
      exact ⟨lab_cons (solidC_label _ _ _) lab_nil, lab_cons rfl lab_nil⟩)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [he_x]
        exact h_S
      · rw [he'_y]
        exact h_G.trans h_S.symm)
    (by
      refine (List.length_filter_le _ _).trans ?_
      simp)
    (by simp)
    (by
      rw [hN, hR]
      have := ord_solidC_nonneg (V := Atom k n) .plus e'.x e.y
      linarith)
  refine ⟨key.1, ?_, ⟨solidC .plus e'.x e.y, by simp [EO_ggMain], solidC_random _ _ _⟩⟩
  have h2 := key.2
  rw [hN, hR] at h2
  simp only [EO_ggMain]
  rw [h2]
  ring

/-- The term of `Ô_GG` with the light weight `G_{αα} - m` and the label `Q_{x}`. -/
private theorem preT_gg_Q4 {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (o : Option (Atom k (n + 1))) (d : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)], d⟩, liftA 1⟩ ∧
    (⟨labW o (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)], d⟩ : Graph k (n + 1)).ord = Γ.ord + 1 ∧
    ∃ c ∈ liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)], c.kind.isRandom = true := by
  have h_s := reachW_in' (k := k) (n := n) (j := 1) (c := mkC (.waved .s) (liftA 1 x) (newA 0)) o d
    (M := labW o (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) (P := liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA
          0) (newA 0)])
    (N₂ := [mkC (.waved .s) (liftA 1 x) (newA 0)]) rfl (Or.inr (by simp)) ⟨_, rfl⟩
  have hNo : ordL ([mkC (.light .plus) (newA 0) (newA 0)] ++ [mkC (.waved .s) (liftA 1 x) (newA 0)]
      :
      List (Comp (Atom k (n + 1)))) = 3 := by
    simp [mkC, Kind.ord]
  have key := preT_A (j := 1) hN hP hx hU o Γ.comps [] [mkC (.light .plus) (newA 0) (newA 0)]
    [mkC (.waved .s) (liftA 1 x) (newA 0)]
    (labW o (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) d rfl (by simp) (by simp)
    (newOK_cons (NewOK_light _ _) newOK_nil) (newOK_cons (NewOK_waved _ _ _) newOK_nil)
    (by simp [mkC]) (by simp)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact h_s)
    (by simp [mkC, Kind.isSolid]) (by simp)
    (by rw [hNo]; simp)
  refine ⟨key.1, ?_, ⟨mkC (.light .plus) (newA 0) (newA 0), by simp, by simp [mkC, Kind.isRandom]⟩⟩
  rw [key.2, hNo]
  simp
  ring

end GGMain

section GGD1

variable {k n : ℕ}

set_option linter.flexible false in
/-- The derivative terms of `Ô_GG` at `α = x`, with an optional label. -/
private theorem preT_gg_D1 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e') (o : Option (Atom k (n + 1)))
    {d₀ : List (Comp (Atom k (n + 1)))}
    (hd : d₀ ∈ dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (EO_ggF Γ i j)))
    (c0 : Coeff) :
    PreT C Γ.ord x ⟨n + 1, ⟨labW o (d₀ ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)], c0⟩,
      liftA 1⟩ ∧
    (Γ.wt x = 0 → Γ.ord + 1 ≤ (⟨labW o (d₀ ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
      c0⟩ : Graph k (n + 1)).ord) ∧
    ∃ c ∈ d₀ ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)],
      c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  set fL := EO_ggF Γ i j with hfL
  obtain ⟨jj, hjj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hjj' : jj < fL.length := by simpa [liftCs_length] using hjj
  set cj := fL[jj] with hcj
  have hfj : fL[jj]? = some cj := by simp [hcj]
  have hcjmem : cj ∈ fL := List.getElem_mem hjj'
  have hcjΓ : cj ∈ Γ.comps := mem_eraseIdxs_of_mem hcjmem
  have hlift : (liftCs 1 fL)[jj] = cj.map (liftA 1) := by simp [liftCs, hcj]
  have hps' : (cj.map (liftA 1)).dPieces (newA 0) (liftA 1 x) = some ps := by
    rw [← hlift]; exact hps
  have hE : (liftCs 1 fL).eraseIdx jj = liftCs 1 (fL.eraseIdx jj) := by
    unfold liftCs; exact eraseIdx_map _ _ _
  have hperm : (fL.eraseIdx jj ++ [cj, e, e']).Perm Γ.comps := by
    have h2 := eraseIdx_perm hfj
    have h3 : (fL.eraseIdx jj ++ [cj] ++ [e, e']).Perm Γ.comps :=
      (h2.append_right [e, e']).trans Ctx.perm
    simpa [List.append_assoc] using h3
  rw [hE]
  have hP : (liftCs 1 (fL.eraseIdx jj) ++ ps) ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)] = liftCs 1 (fL.eraseIdx jj) ++
      (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
          mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) := by
    simp [List.append_assoc]
  rw [hP]
  have hM2 : labW o (liftCs 1 (fL.eraseIdx jj) ++ (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)] =
      labW o (liftCs 1 (fL.eraseIdx jj) ++ (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)] := rfl
  have hpsNew := dPieces_newOK hps'
  have hpsLab := dPieces_label hps'
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (liftA 1 x) (newA 0)) o c0 hM2
    (Or.inr (by simp)) (by simp [mkC])
  have h_Ga := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 0) (liftA 1 e.y)) o c0 hM2
    (Or.inl (by simp)) (by simp [mkC])
  have h_Gp := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)) o c0 hM2
    (Or.inl (by simp)) (by simp [mkC])
  have hcjrand := dPieces_random hps'
  have hcjrand' : cj.kind.isRandom = true := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch,
        h⟩ <;> simp [Comp.map] at h <;> simp [h, Kind.isRandom]
  have hord1 := dPieces_ord_ge hps' (by simp [Comp.map, liftA_ne_newA]) (by
    unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA])
  have hordcj : (cj.map (liftA 1)).kind.ord = cj.kind.ord := rfl
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hR : ordL [cj, e, e'] = cj.kind.ord + 2 := by
    simp [ordL_cons, e1, e2]
  have hN : ordL ((ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)]) =
      ordL ps + 4 := by
    simp [ordL_append, mkC, Kind.ord]
  have key := preT_A' (j := 1) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (fL.eraseIdx jj)
    [cj, e, e'] (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) [mkC (.waved .s) (liftA 1 x) (newA 0)]
    (labW o (liftCs 1 (fL.eraseIdx jj) ++ (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)]) c0
    rfl hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hcjrand'
      · simp [he_k, Kind.isRandom]
      · simp [he'_k, Kind.isRandom])
    (newOK_append hpsNew (newOK_cons (NewOK_G _ (liftA_ne_newA 1 e.y 0).symm)
      (newOK_cons (NewOK_G _ (fun h => he'_x (liftA_injective 1 h))) newOK_nil)))
    (newOK_cons (NewOK_waved _ _ _) newOK_nil)
    (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (hc | rfl | rfl) | rfl
      · exact hpsLab c hc
      · rfl
      · rfl
      · rfl)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
        · have := dPieces_path (G := (⟨labW o (liftCs 1 (fL.eraseIdx jj) ++ (ps ++
            [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])) ++
            [mkC (.waved .s) (liftA 1 x) (newA 0)], c0⟩ : Graph k (n + 1)).edgeGraphNoX) hps'
            ⟨ch, h⟩
            (fun c' hc' => by
              exact reach_in' (k := k) (n := n) o c0 hM2
                (Or.inl (List.mem_append_right _ (List.mem_append_left _ hc')))
                (hpsNew c' hc').ne_xdot)
            h_s.symm
          simpa [Comp.map] using this
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
      · rw [he_x]
        exact h_s.trans h_Ga
      · rw [he'_y]
        exact h_Gp)
    (by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact reachW_in' (c := mkC (.waved .s) (liftA 1 x) (newA 0)) o c0 hM2 (Or.inr (by simp)) ⟨.s,
          rfl⟩)
    (fun E => unp_conv (by
      set g' : Graph k (n + 1) := ⟨labW o (liftCs 1 (fL.eraseIdx jj) ++ (ps ++
        [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)], c0⟩ with hg'
      have hcomps : g'.comps = labW o (liftCs 1 (fL.eraseIdx jj) ++ (ps ++
        [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)] := rfl
      have hBsub : ∀ c ∈ fL.eraseIdx jj, c ∈ Γ.comps := fun c hc =>
        hperm.subset (List.mem_append_left _ hc)
      have hunp0 : unpartCount g' (liftCs 1 (fL.eraseIdx jj)) = 0 := by
        refine unpartCount_eq_zero g' fun c' hc' hs => ?_
        obtain ⟨c, hcB, rfl⟩ := mem_liftCs.1 hc'
        exact partnered_old Ctx.normal E ⟨c, hBsub c hcB, rfl, rfl, rfl⟩ hs
      have hGp0 : unpartCount g' [mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)] = 0 := by
        refine unpartCount_eq_zero g' fun c' hc' hs => ?_
        rcases List.mem_singleton.1 hc' with rfl
        exact partnered_old Ctx.normal E ⟨e', Ctx.e'mem, rfl, by rw [he'_y]; rfl,
          by simp [mkC, he'_k]⟩ hs
      have hs0 : unpartCount g' [mkC (.waved .s) (liftA 1 x) (newA 0)] = 0 := by
        refine unpartCount_eq_zero g' fun c' hc' hs => ?_
        rcases List.mem_singleton.1 hc' with rfl
        simp [mkC, Kind.isSolid] at hs
      have hsplit : [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x)
          (liftA 1 x)] = [mkC (.G .plus) (newA 0) (liftA 1 e.y)] ++
          [mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)] := rfl
      have hlen : (unpartL g').length =
          unpartCount g' ps + unpartCount g' [mkC (.G .plus) (newA 0) (liftA 1 e.y)] := by
        rw [unpartL_length, hcomps, unpartCount_append, unpartCount_labW, unpartCount_append,
          unpartCount_append, hunp0, hs0, hsplit, unpartCount_append, hGp0]
        ring
      have hps2 : unpartCount g' ps ≤ 2 := by
        have := unpartCount_le g' ps
        rw [dPieces_length hps'] at this
        exact this
      have hga1 : unpartCount g' [mkC (.G .plus) (newA 0) (liftA 1 e.y)] ≤ 1 :=
        unpartCount_le g' _
      refine ⟨by omega, fun h3 => ?_⟩
      have h2 : unpartCount g' ps = 2 := by omega
      have h1' : unpartCount g' [mkC (.G .plus) (newA 0) (liftA 1 e.y)] = 1 := by omega
      have hGy : partnered g' (mkC (.G .plus) (newA 0) (liftA 1 e.y)) = false := by
        by_contra hcon
        have hcon' : partnered g' (mkC (.G .plus) (newA 0) (liftA 1 e.y)) = true := by
          simpa using hcon
        unfold unpartCount at h1'
        simp [mkC, Kind.isSolid, List.filter_cons] at h1' hcon'
        simp [hcon'] at h1'
      have hall : ∀ c ∈ ps, (c.kind.isSolid && !partnered g' c) = true := by
        have := h2
        unfold unpartCount at this
        rw [← dPieces_length hps'] at this
        exact List.length_filter_eq_length_iff.1 this
      obtain ⟨c₂, hc₂ps, hc₂q⟩ := dPieces_has_q hps'
      have hc₂m : c₂ ∈ liftCs 1 (fL.eraseIdx jj) ++ (ps ++
          [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) :=
        List.mem_append_right _ (List.mem_append_left _ hc₂ps)
      have hgam : mkC (.G .plus) (newA 0) (liftA 1 e.y) ∈ liftCs 1 (fL.eraseIdx jj) ++ (ps ++
          [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]) := by
        simp
      obtain ⟨c₁'', hc₁'', a1, a2, a3⟩ := labW_exists (o := o) hgam
      obtain ⟨c₂'', hc₂'', b1, b2, b3⟩ := labW_exists (o := o) hc₂m
      refine ⟨c₁'', ?_, c₂'', ?_, ?_⟩
      · refine List.mem_filter.2 ⟨by rw [hcomps]; exact List.mem_append_left _ hc₁'', ?_⟩
        have : partnered g' c₁'' = false := by
          rw [partnered_congr g' (c' := mkC (.G .plus) (newA 0) (liftA 1 e.y)) a1 a2]; exact hGy
        simp [a3, mkC, Kind.isSolid, this]
      · refine List.mem_filter.2 ⟨by rw [hcomps]; exact List.mem_append_left _ hc₂'', ?_⟩
        have hh := hall c₂ hc₂ps
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hh ⊢
        refine ⟨by rw [b3]; exact hh.1, ?_⟩
        rw [partnered_congr g' (c' := c₂) b1 b2]; exact hh.2
      · unfold SamePair
        rw [a1, a2, b1, b2]
        simp only [mkC]
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rcases hc₂q with hq | hq
          · exact liftA_ne_newA 1 x 0 (hq.symm.trans h1)
          · exact he_y (liftA_injective 1 (h2.symm.trans hq))
        · rcases hc₂q with hq | hq
          · exact he_y (liftA_injective 1 (h1.symm.trans hq))
          · exact liftA_ne_newA 1 x 0 (hq.symm.trans h2)))
    (by
      have := dPieces_length hps'
      simp only [List.length_append, List.length_cons, List.length_nil, this]
      omega)
    (by
      rw [hR, hN]
      obtain ⟨h5, h6⟩ := hord1
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨mkC (.G .plus) (newA 0) (liftA 1 e.y), by simp, by simp [mkC, Kind.isRandom]⟩⟩
  intro hwt
  rw [key.2, hR, hN]
  have hnt : cj.x ≠ x ∧ (cj.map (liftA 1)).endB ≠ liftA 1 x := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
    · have hch : cj.kind = .G ch := by simpa [Comp.map] using h
      obtain ⟨a, b⟩ := Ctx.f_untouched hcjmem hch
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => b (liftA_injective 1 hh)
    · have hch : cj.kind = .weight ch := by simpa [Comp.map] using h
      have a := wt_zero_imp hwt hcjΓ (Or.inl ⟨ch, hch⟩)
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => a (liftA_injective 1 hh)
    · have hch : cj.kind = .light ch := by simpa [Comp.map] using h
      have a := wt_zero_imp hwt hcjΓ (Or.inr ⟨ch, hch⟩)
      refine ⟨a, ?_⟩
      unfold Comp.endB
      simp [Comp.map, hch, Kind.isWeight]
      exact fun hh => a (liftA_injective 1 hh)
  have h2 := dPieces_ord_two hps' (by simp [Comp.map, liftA_ne_newA])
    (by unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA])
    (by simpa [Comp.map] using fun hh => hnt.1 (liftA_injective 1 hh)) hnt.2
  obtain ⟨-, h6⟩ := hord1
  rw [h2]
  push_cast
  linarith

end GGD1

section TwoClass

variable {k n : ℕ}

private theorem two_class {α : Type*} {W L : List α} (Q : α → Bool) (hL : L.Sublist W)
    (hQ : (W.filter Q).length ≤ 2) (hnQ : (W.filter fun a => !Q a).length ≤ 2)
    (h3 : 3 ≤ L.length) : (∃ a ∈ L, Q a = true) ∧ ∃ b ∈ L, Q b = false := by
  have h1 := (hL.filter Q).length_le
  have h2 := (hL.filter fun a => !Q a).length_le
  have hl := List.length_eq_length_filter_add (l := L) Q
  constructor
  · by_contra hcon
    push Not at hcon
    have : (L.filter Q).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro a ha
      simp [hcon a ha]
    omega
  · by_contra hcon
    push Not at hcon
    have : (L.filter fun a => !Q a).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro a ha
      have := hcon a ha
      simp at this
      simp [this]
    omega

private theorem countP_labW {V : Type*} (P : Comp V → Bool) (hP : ∀ u c, P (c.labelQ u) = P c)
    (o : Option V) (L : List (Comp V)) : (labW o L).countP P = L.countP P := by
  cases o with
  | none => rfl
  | some u =>
    unfold labW labelQs
    rw [List.countP_map]
    apply List.countP_congr
    intro c _
    simp [hP u c]

/-- Two classes of unpartnered solid edges, each with at most two members among the new
components, give at most four unpartnered solid edges, no three on one pair. -/
private theorem unp_two_classes {C j : ℕ} {Γ : Graph k n} {x : Atom k n} (hN : Γ.Normal C)
    (o : Option (Atom k (n + j))) (B : List (Comp (Atom k n)))
    (N₁ N₂ M : List (Comp (Atom k (n + j)))) (d : Coeff)
    (hM : M = labW o (liftCs j B ++ N₁) ++ N₂)
    (hBsub : ∀ c ∈ B, c ∈ Γ.comps)
    (E : ExtData (liftA j) Γ x (⟨M, d⟩ : Graph k (n + j)))
    (Q : Comp (Atom k (n + j)) → Bool) (hQ : ∀ u c, Q (c.labelQ u) = Q c)
    (hSame : ∀ c₁ c₂, Q c₁ ≠ Q c₂ → ¬ SamePair c₁ c₂)
    (hcnt : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && Q c).length ≤ 2)
    (hcnt' : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && !Q c).length ≤ 2) :
    (unpartL (⟨M, d⟩ : Graph k (n + j))).length ≤ 4 ∧
      ∀ L : List (Comp (Atom k (n + j))), L.Sublist (unpartL (⟨M, d⟩ : Graph k (n + j))) →
        3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂ := by
  subst hM
  set g' : Graph k (n + j) := ⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ with hg'
  have hcomps : g'.comps = labW o (liftCs j B ++ N₁) ++ N₂ := rfl
  -- counting lemma
  have hcount : ∀ R : Comp (Atom k (n + j)) → Bool, (∀ u c, R (c.labelQ u) = R c) →
      ((unpartL g').filter R).length ≤ ((N₁ ++ N₂).filter fun c => c.kind.isSolid && R
          c).length := by
    intro R hR
    have e1 : ((unpartL g').filter R).length =
        g'.comps.countP (fun c => R c && (c.kind.isSolid && !partnered g' c)) := by
      rw [← List.countP_eq_length_filter, unpartL, List.countP_filter]
    rw [e1, hcomps, List.countP_append]
    have hinv : ∀ u c, (fun c : Comp (Atom k (n + j)) => R c && (c.kind.isSolid && !partnered g' c))
        (c.labelQ u) = (fun c => R c && (c.kind.isSolid && !partnered g' c)) c := by
      intro u c
      have hx : (c.labelQ u).x = c.x := labelQ_x u c
      have hy : (c.labelQ u).y = c.y := labelQ_y u c
      have hk : (c.labelQ u).kind = c.kind := labelQ_kind u c
      simp only [hR u c, hk, partnered_congr g' hx hy]
    rw [countP_labW _ hinv, List.countP_append]
    have h0 : (liftCs j B).countP (fun c => R c && (c.kind.isSolid && !partnered g' c)) = 0 := by
      rw [List.countP_eq_zero]
      intro c hc
      obtain ⟨c0, hc0, rfl⟩ := mem_liftCs.1 hc
      by_cases hs : (c0.map (liftA j)).kind.isSolid = true
      · have := partnered_old hN E ⟨c0, hBsub c0 hc0, rfl, rfl, rfl⟩ hs
        simp [this]
      · simp [hs]
    rw [h0, zero_add, ← List.countP_eq_length_filter, List.countP_append]
    have hle : ∀ L : List (Comp (Atom k (n + j))),
        L.countP (fun c => R c && (c.kind.isSolid && !partnered g' c)) ≤
          L.countP (fun c => c.kind.isSolid && R c) := by
      intro L
      apply List.countP_mono_left
      intro c _ h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
      exact ⟨h.2.1, h.1⟩
    exact add_le_add (hle N₁) (hle N₂)
  have c1 := hcount Q hQ
  have c2 := hcount (fun c => !Q c) (fun u c => by simp [hQ u c])
  have hU : (unpartL g').length =
      ((unpartL g').filter Q).length + ((unpartL g').filter fun c => !Q c).length :=
    List.length_eq_length_filter_add Q
  refine ⟨by omega, fun L hL h3 => ?_⟩
  obtain ⟨⟨c₁, hc₁, hq₁⟩, ⟨c₂, hc₂, hq₂⟩⟩ := two_class Q hL (by omega) (by omega) h3
  exact ⟨c₁, hc₁, c₂, hc₂, hSame c₁ c₂ (by rw [hq₁, hq₂]; simp)⟩

end TwoClass

section D2Aux

variable {k n : ℕ}

private theorem dPieces_classes {V : Type*} [DecidableEq V] {p q : V} {c : Comp V} {ps : List (Comp
    V)}
    (h : c.dPieces p q = some ps) (hpq : p ≠ q) (hxp : c.x ≠ p) (hxq : c.x ≠ q)
    (hbp : c.endB ≠ p) (hbq : c.endB ≠ q) :
    (ps.filter fun c' => c'.kind.isSolid && (decide (c'.x = p) || decide (c'.y = p))).length ≤ 1 ∧
    (ps.filter fun c' => c'.kind.isSolid && !(decide (c'.x = p) || decide (c'.y = p))).length ≤
      1 := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simp [solidC, hxp, Ne.symm hbq, mkC, Kind.isSolid, hbp, Ne.symm hpq]
  · simp [solidC, hbp, Ne.symm hbp, mkC, Kind.isSolid, hxp, Ne.symm hpq,
      hxq]

end D2Aux

section D2

variable {k n : ℕ}

/-- The derivative terms of `Ô_GG` at a new atom `α`, with an optional label. -/
private theorem preT_gg_D2 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtx C x Γ i j e e') (o : Option (Atom k (n + 2)))
    {d₀ : List (Comp (Atom k (n + 2)))}
    (hd : d₀ ∈ dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (EO_ggF Γ i j)))
    (c0 : Coeff) :
    PreT C Γ.ord x ⟨n + 2, ⟨labW o (d₀ ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)], c0⟩, liftA 2⟩ ∧
    Γ.ord + 1 ≤ (⟨labW o (d₀ ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)], c0⟩ : Graph k (n + 2)).ord ∧
    ∃ c ∈ d₀ ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)],
      c.kind.isRandom = true := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  set fL := EO_ggF Γ i j with hfL
  obtain ⟨jj, hjj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hjj' : jj < fL.length := by simpa [liftCs_length] using hjj
  set cj := fL[jj] with hcj
  have hfj : fL[jj]? = some cj := by simp [hcj]
  have hcjmem : cj ∈ fL := List.getElem_mem hjj'
  have hcjΓ : cj ∈ Γ.comps := mem_eraseIdxs_of_mem hcjmem
  have hlift : (liftCs 2 fL)[jj] = cj.map (liftA 2) := by simp [liftCs, hcj]
  have hps' : (cj.map (liftA 2)).dPieces (newA 1) (newA 0) = some ps := by
    rw [← hlift]; exact hps
  have hE : (liftCs 2 fL).eraseIdx jj = liftCs 2 (fL.eraseIdx jj) := by
    unfold liftCs; exact eraseIdx_map _ _ _
  have hperm : (fL.eraseIdx jj ++ [cj, e, e']).Perm Γ.comps := by
    have h2 := eraseIdx_perm hfj
    have h3 : (fL.eraseIdx jj ++ [cj] ++ [e, e']).Perm Γ.comps :=
      (h2.append_right [e, e']).trans Ctx.perm
    simpa [List.append_assoc] using h3
  rw [hE]
  have hP : (liftCs 2 (fL.eraseIdx jj) ++ ps) ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)] = liftCs 2 (fL.eraseIdx jj) ++
      (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) := by
    simp [List.append_assoc]
  rw [hP]
  have hM2 : labW o (liftCs 2 (fL.eraseIdx jj) ++ (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)])) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] =
      labW o (liftCs 2 (fL.eraseIdx jj) ++ (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)])) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] := rfl
  have hpsNew := dPieces_newOK hps'
  have hpsLab := dPieces_label hps'
  have h_S := reach_in' (k := k) (n := n) (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o c0 hM2
    (Or.inr (by simp)) (by simp [mkC])
  have h_s := reach_in' (k := k) (n := n) (c := mkC (.waved .s) (newA 0) (newA 1)) o c0 hM2
    (Or.inr (by simp)) (by simp [mkC])
  have h_Gb := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (newA 1) (liftA 2 e.y)) o c0 hM2
    (Or.inl (by simp)) (by simp [mkC])
  have h_Gpa := reach_in' (k := k) (n := n) (c := mkC (.G .plus) (liftA 2 e'.x) (newA 0)) o c0 hM2
    (Or.inl (by simp)) (by simp [mkC])
  have hcjrand := dPieces_random hps'
  have hcjrand' : cj.kind.isRandom = true := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch,
        h⟩ <;> simp [Comp.map] at h <;> simp [h, Kind.isRandom]
  have hxp : (cj.map (liftA 2)).x ≠ newA 1 := by simp [Comp.map, liftA_ne_newA]
  have hxq : (cj.map (liftA 2)).x ≠ newA 0 := by simp [Comp.map, liftA_ne_newA]
  have hbp : (cj.map (liftA 2)).endB ≠ newA 1 := by
    unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA]
  have hbq : (cj.map (liftA 2)).endB ≠ newA 0 := by
    unfold Comp.endB; split_ifs <;> simp [Comp.map, liftA_ne_newA]
  have hord2 := dPieces_ord_two hps' hxp hbp hxq hbq
  have hordle : cj.kind.ord ≤ 1 := by
    rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [Comp.map] at h <;>
      simp [h, Kind.ord]
  have e1 : e.kind.ord = 1 := by rw [he_k]; rfl
  have e2 : e'.kind.ord = 1 := by rw [he'_k]; rfl
  have hR : ordL [cj, e, e'] = cj.kind.ord + 2 := by
    simp [ordL_cons, e1, e2]
  have hN : ordL ((ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) = ordL ps + 6 := by
    simp [ordL_append, mkC, Kind.ord]
  have key := preT_A' (j := 2) Ctx.normal Ctx.plain Ctx.right Ctx.unl o (fL.eraseIdx jj)
    [cj, e, e'] (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]
    (labW o (liftCs 2 (fL.eraseIdx jj) ++ (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) (newA 0)])) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) c0
    rfl hperm
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hcjrand'
      · simp [he_k, Kind.isRandom]
      · simp [he'_k, Kind.isRandom])
    (newOK_append hpsNew (newOK_cons (NewOK_G _ (liftA_ne_newA 2 e.y 1).symm)
      (newOK_cons (NewOK_G _ (liftA_ne_newA 2 e'.x 0)) newOK_nil)))
    (newOK_cons (NewOK_waved _ _ _) (newOK_cons (NewOK_waved _ _ _) newOK_nil))
    (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (hc | rfl | rfl) | rfl | rfl
      · exact hpsLab c hc
      · rfl
      · rfl
      · rfl
      · rfl)
    (by
      intro r hr hk hne'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rcases hcjrand with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩
        · have := dPieces_path (G := (⟨labW o (liftCs 2 (fL.eraseIdx jj) ++ (ps ++
            [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)])) ++
            [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)], c0⟩ :
              Graph k (n + 2)).edgeGraphNoX) hps' ⟨ch, h⟩
            (fun c' hc' => by
              exact reach_in' (k := k) (n := n) o c0 hM2
                (Or.inl (List.mem_append_right _ (List.mem_append_left _ hc')))
                (hpsNew c' hc').ne_xdot)
            h_s.symm
          simpa [Comp.map] using this
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
        · exfalso
          have := (Ctx.plain cj hcjΓ).2.2.2.2.1 (by simp [Comp.map] at h; simp [h, Kind.isWeight])
          exact hne' this.symm
      · rw [he_x]
        exact h_S.trans (h_s.trans h_Gb)
      · rw [he'_y]
        exact h_Gpa.trans h_S.symm)
    (by
      intro i
      fin_cases i
      · exact reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o c0 hM2
          (Or.inr (by simp)) ⟨.plus, rfl⟩
      · exact (reachW_in' (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) o c0 hM2
          (Or.inr (by simp)) ⟨.plus, rfl⟩).trans
          (reachW_in' (c := mkC (.waved .s) (newA 0) (newA 1)) o c0 hM2
            (Or.inr (by simp)) ⟨.s, rfl⟩))
    (fun E => by
      refine unp_two_classes Ctx.normal o (fL.eraseIdx jj) _ _ _ c0 rfl
        (fun c hc => hperm.subset (List.mem_append_left _ hc)) E
        (fun c => decide (c.x = newA 1) || decide (c.y = newA 1)) (fun u c => by simp) ?_ ?_ ?_
      · intro c₁ c₂ hne hsp
        apply hne
        rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, Bool.or_comm]
      · have := (dPieces_classes hps' (by simp [newA, Fin.ext_iff]) hxp hxq hbp hbq).1
        simp only [List.filter_append, List.length_append]
        have a1 : decide ((liftA 2 e'.x : Atom k (n + 2)) = newA 1) = false := by
          simp [liftA_ne_newA]
        have a2 : decide ((newA 0 : Atom k (n + 2)) = newA 1) = false := by
          simp [newA, Fin.ext_iff]
        simp [mkC, Kind.isSolid, a1, a2] at this ⊢
        omega
      · have := (dPieces_classes hps' (by simp [newA, Fin.ext_iff]) hxp hxq hbp hbq).2
        simp only [List.filter_append, List.length_append]
        have a1 : decide ((liftA 2 e'.x : Atom k (n + 2)) = newA 1) = false := by
          simp [liftA_ne_newA]
        have a2 : decide ((newA 0 : Atom k (n + 2)) = newA 1) = false := by
          simp [newA, Fin.ext_iff]
        simp [mkC, Kind.isSolid, a1, a2] at this ⊢
        omega)
    (by
      have := dPieces_length hps'
      simp only [List.length_append, List.length_cons, List.length_nil, this]
      omega)
    (by
      rw [hR, hN, hord2]
      push_cast
      linarith)
  refine ⟨key.1, ?_, ⟨mkC (.G .plus) (newA 1) (liftA 2 e.y), by simp, by simp [mkC, Kind.isRandom]⟩⟩
  rw [key.2, hR, hN, hord2]
  push_cast
  linarith

end D2

section GGSpec

variable {k n : ℕ}

private theorem labW_some_not_lf' {m : ℕ} (u : Atom k m) (P N₂ : List (Comp (Atom k m))) (d : Coeff)
    (h : ∃ c ∈ P, c.kind.isRandom = true) :
    ¬ (⟨labW (some u) P ++ N₂, d⟩ : Graph k m).LabelFree := by
  obtain ⟨c, hc, hr⟩ := h
  intro hlf
  have hm : c.labelQ u ∈ (⟨labW (some u) P ++ N₂, d⟩ : Graph k m).comps :=
    List.mem_append_left _ (mem_labelQs.2 ⟨c, hc, rfl⟩)
  have := hlf _ hm
  unfold Comp.labelQ at this
  simp [hr] at this

/-- The main term of `Ô_GG` when `y = y'`. -/
def GGMainShape (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n))
    (t : Tracked k n) : Prop :=
  e'.x = e.y ∧ ∃ d, t = ⟨n, ⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩, id⟩

theorem ggOut_spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtx C x Γ i j e e') :
    ∀ t ∈ EO_ggOut x Γ i j e e', PreT C Γ.ord x t ∧
      (¬ t.g.LabelFree ∨ (Γ.wt x = 0 → Γ.ord + 1 ≤ t.g.ord) ∨ GGMainShape x Γ i j e e' t) := by
  intro t ht
  simp only [EO_ggOut, List.mem_append, List.mem_map, List.mem_cons, 
    List.not_mem_nil, or_false] at ht
  rcases ht with
    ((((((rfl | rfl | rfl | rfl | rfl) | ⟨d₀, hd₀, rfl⟩) | ⟨d₀, hd₀, rfl⟩) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | ⟨d₀, hd₀, rfl⟩) | ⟨d₀, hd₀, rfl⟩)
  · -- the main term
    have h := preT_gg_main Ctx none (cm * Γ.coeff)
    refine ⟨by simpa [labW] using h.1, ?_⟩
    by_cases hxy : e'.x = e.y
    · exact Or.inr (Or.inr ⟨hxy, _, rfl⟩)
    · refine Or.inr (Or.inl fun _ => ?_)
      have h2 := h.2.1
      simp only [labW] at h2
      rw [ord_solidC, ite_eq_right hxy] at h2
      linarith
  · -- the light weight term
    have h := preT_l3 Ctx.normal Ctx.plain Ctx.right Ctx.unl none (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1, EO_oL3, EO_oSx] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have h2 := h.2.1
    simp only [labW] at h2
    exact h2.symm.le
  · have h := preT_gg_T2 Ctx none (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t2] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have h2 := h.2.1
    simp only [labW, List.append_nil, EO_t2] at h2 ⊢
    linarith
  · have h := preT_gg_T3 Ctx none (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have h2 := h.2.1
    simp only [labW, List.append_nil, EO_t1] at h2 ⊢
    linarith
  · have h := preT_gg_T4 Ctx none (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t2] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have h2 := h.2.1
    simp only [labW, List.append_nil, EO_t2] at h2 ⊢
    linarith
  · -- the derivative terms at `x`
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd₀
    have h := preT_gg_D1 Ctx none hd' (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t1] using h.1, Or.inr (Or.inl fun hw => ?_)⟩
    have h2 := h.2.1 hw
    simp only [labW] at h2
    simpa [EO_t1] using h2
  · -- the derivative terms at the new atom
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd₀
    have h := preT_gg_D2 Ctx none hd' (cm * Γ.coeff)
    refine ⟨by simpa [labW, EO_t2] using h.1, Or.inr (Or.inl fun _ => ?_)⟩
    have h2 := h.2.1
    simp only [labW] at h2
    simpa [EO_t2] using h2
  · -- labelled: the graph itself
    refine ⟨(preT_self Ctx.normal Ctx.plain Ctx.right Ctx.unl _).1, Or.inl ?_⟩
    refine labelQs_not_lf _ _ _ ⟨e, Ctx.emem, ?_⟩
    simp [Ctx.espec.1, Kind.isRandom]
  · have h := preT_gg_Q2 Ctx (some (newA 0)) Γ.coeff
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩
  · have h := preT_gg_main Ctx (some e.y) (-cm * Γ.coeff)
    exact ⟨by simpa [labW] using h.1, Or.inl (labW_some_not_lf' _ _ _ _ h.2.2)⟩
  · have h := preT_gg_Q4 Ctx.normal Ctx.plain Ctx.right Ctx.unl (some (liftA 1 x)) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩
  · have h := preT_gg_Q5 Ctx (some (newA 0)) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t2] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩
  · have h := preT_gg_Q6 Ctx (some (liftA 1 x)) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩
  · have h := preT_gg_Q7 Ctx (some (newA 0)) (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t2] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd₀
    have h := preT_gg_D1 Ctx (some (liftA 1 x)) hd' (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t1] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd₀
    have h := preT_gg_D2 Ctx (some (newA 0)) hd' (-cm * Γ.coeff)
    exact ⟨by simpa [labW, EO_t2] using h.1, Or.inl (labW_some_not_lf _ _ _ _ h.2.2)⟩

end GGSpec

section DegMerge

variable {k N : ℕ}

private theorem mergeDegTerm {m : ℕ} (rep : Atom k N → Atom k N) (f : Atom k N → Atom k m) (w :
    Atom k m)
    (c : Comp (Atom k N)) :
    (Option.map (fun c' => c'.kind.isSolid && (c'.x == w || c'.y == w))
      (mergeComp rep f c)).getD false =
      (c.kind.isSolid && !(rep c.x == rep c.y) && (f c.x == w || f c.y == w)) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  unfold mergeComp
  cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;>
    by_cases hr : rep a = rep b <;> by_cases hf : f a = f b <;>
    simp [Comp.map, Kind.isSolid, Kind.toWeight, hr, hf]

private theorem deg_merge {g : Graph k N} {A : List (Atom k N × Atom k N × Bool)} {t : Tracked k N}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) (w : Atom k t.nOut) :
    t.g.deg w = g.comps.countP (fun c => c.kind.isSolid &&
      !((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
      (t.f c.x == w || t.f c.y == w)) := by
  have hs := mergeT_spec hm
  rw [← countP_dotChoice g g.splitPairs A]
  · unfold Graph.deg
    rw [← List.countP_eq_length_filter, hs.comps_eq, List.countP_filterMap]
    apply List.countP_congr
    intro c _
    exact Iff.of_eq (congrArg (· = true) (mergeDegTerm _ _ _ _))
  · intro c hc
    rcases hc with hc | hc <;> simp [hc, Kind.isSolid]

private theorem countP_or_disj {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ a ∈ l, p a = true → q a = false) :
    l.countP (fun a => p a || q a) = l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.countP_cons]
    by_cases hp : p a = true
    · have hq := h a (List.mem_cons_self ..) hp
      simp [hp, hq, ih']
      omega
    · by_cases hq : q a = true <;> simp [hp, hq, ih']; omega

private theorem deg_eq_countP (g : Graph k N) (u : Atom k N) :
    g.deg u = g.comps.countP (fun c => c.kind.isSolid && (c.x == u || c.y == u)) := by
  unfold Graph.deg
  rw [List.countP_eq_length_filter]

private theorem convS_countP {g : Graph k N} {A : List (Atom k N × Atom k N × Bool)} (u : Atom k
    N) :
    (convS g (g.dotChoice g.splitPairs A)).countP (fun c => c.x == u || c.y == u) =
      g.comps.countP (fun c => c.kind.isSolid &&
        ((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
        (c.x == u || c.y == u)) := by
  unfold convS
  rw [List.countP_filter]
  apply List.countP_congr
  intro c _
  simp [Bool.and_comm]

private theorem deg_Z {g : Graph k N} {A : List (Atom k N × Atom k N × Bool)} {t : Tracked k N}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) (hinj : Function.Injective t.f)
    (hconv : convS g (g.dotChoice g.splitPairs A) = []) (u : Atom k N) :
    t.g.deg (t.f u) = g.deg u := by
  rw [deg_merge hm, deg_eq_countP]
  apply List.countP_congr
  intro c hc
  have hnc : (c.kind.isSolid &&
      (g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) = false := by
    by_contra hcon
    have hcon' : (c.kind.isSolid &&
        (g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) = true := by
      simpa using hcon
    have : c ∈ convS g (g.dotChoice g.splitPairs A) := List.mem_filter.2 ⟨hc, hcon'⟩
    rw [hconv] at this
    cases this
  have hnc' : c.kind.isSolid = true → ¬ ((g.dotChoice g.splitPairs A).mrep c.x =
      (g.dotChoice g.splitPairs A).mrep c.y) := by
    intro hs hr
    simp [hs, hr] at hnc
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨⟨hs, -⟩, hx⟩ := h
    refine ⟨hs, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl (hinj hx)
    · exact Or.inr (hinj hx)
  · intro h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨hs, hx⟩ := h
    refine ⟨⟨hs, ?_⟩, ?_⟩
    · simpa using hnc' hs
    · rcases hx with hx | hx
      · exact Or.inl (by rw [hx])
      · exact Or.inr (by rw [hx])

private theorem deg_E2 {g : Graph k N} {A : List (Atom k N × Atom k N × Bool)} {t : Tracked k N}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) (hinj : Function.Injective t.f)
    {c₁ c₂ : Comp (Atom k N)} (hconv : convS g (g.dotChoice g.splitPairs A) = [c₁, c₂])
    (u : Atom k N) :
    t.g.deg (t.f u) + ([c₁, c₂].countP fun c => c.x == u || c.y == u) = g.deg u := by
  rw [deg_merge hm, deg_eq_countP, ← hconv, convS_countP, ← countP_or_disj]
  · apply List.countP_congr
    intro c _
    by_cases hs : c.kind.isSolid = true <;>
      by_cases hr : ((g.dotChoice g.splitPairs A).mrep c.x ==
        (g.dotChoice g.splitPairs A).mrep c.y) = true <;>
      simp [hs, hr, hinj.eq_iff]
  · intro c _ hp
    by_cases hr : ((g.dotChoice g.splitPairs A).mrep c.x ==
        (g.dotChoice g.splitPairs A).mrep c.y) = true
    · simp [hr] at hp
    · simp [hr]

private theorem deg_split (g : Graph k N) (A : List (Atom k N × Atom k N × Bool)) (u : Atom k N) :
    g.deg u = g.comps.countP (fun c => c.kind.isSolid &&
      !((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
      (c.x == u || c.y == u)) +
      (convS g (g.dotChoice g.splitPairs A)).countP (fun c => c.x == u || c.y == u) := by
  rw [deg_eq_countP, convS_countP, ← countP_or_disj]
  · apply List.countP_congr
    intro c _
    by_cases hs : c.kind.isSolid = true <;>
      by_cases hr : ((g.dotChoice g.splitPairs A).mrep c.x ==
        (g.dotChoice g.splitPairs A).mrep c.y) = true <;> simp [hs, hr]
  · intro c _ hp
    by_cases hr : ((g.dotChoice g.splitPairs A).mrep c.x ==
        (g.dotChoice g.splitPairs A).mrep c.y) = true
    · simp [hr] at hp
    · simp [hr]

private theorem deg_E1 {g : Graph k N} {A : List (Atom k N × Atom k N × Bool)} {t : Tracked k N}
    (hm : (g.dotChoice g.splitPairs A).mergeT = some t) {a b : Atom k N}
    (hfib : ∀ u v, t.f u = t.f v → u = v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (hfab : t.f a = t.f b) {c₁ c₂ : Comp (Atom k N)}
    (hconv : convS g (g.dotChoice g.splitPairs A) = [c₁, c₂])
    (hc₁ : (c₁.x = a ∧ c₁.y = b) ∨ (c₁.x = b ∧ c₁.y = a))
    (hc₂ : (c₂.x = a ∧ c₂.y = b) ∨ (c₂.x = b ∧ c₂.y = a)) (hda : g.deg a = 2) :
    (∀ u, u ≠ a → u ≠ b → t.g.deg (t.f u) = g.deg u) ∧ t.g.deg (t.f b) + 2 = g.deg b := by
  have hca : [c₁, c₂].countP (fun c => c.x == a || c.y == a) = 2 := by
    rcases hc₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc₂ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp [h1, h2, h3, h4]
  have hcb : [c₁, c₂].countP (fun c => c.x == b || c.y == b) = 2 := by
    rcases hc₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc₂ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp [h1, h2, h3, h4]
  have hnoa : ∀ c ∈ g.comps, (c.kind.isSolid &&
      !((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
      (c.x == a || c.y == a)) = false := by
    have h := deg_split g A a
    rw [hconv, hca, hda] at h
    have h0 : g.comps.countP (fun c => c.kind.isSolid &&
        !((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
        (c.x == a || c.y == a)) = 0 := by omega
    rw [List.countP_eq_zero] at h0
    intro c hc
    simpa using h0 c hc
  constructor
  · intro u hua hub
    rw [deg_merge hm]
    have h := deg_split g A u
    have hcu : [c₁, c₂].countP (fun c => c.x == u || c.y == u) = 0 := by
      rcases hc₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hc₂ with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        simp [h1, h2, h3, h4, Ne.symm hua, Ne.symm hub]
    rw [hconv, hcu] at h
    rw [h]
    simp only [add_zero]
    apply List.countP_congr
    intro c _
    have key : ∀ w, (t.f w = t.f u) ↔ w = u := by
      intro w
      constructor
      · intro hw
        rcases hfib w u hw with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h2 hub
        · exact absurd h2 hua
      · rintro rfl; rfl
    simp [key]
  · rw [deg_merge hm]
    have h := deg_split g A b
    rw [hconv, hcb] at h
    have key : ∀ w, (t.f w = t.f b) ↔ (w = a ∨ w = b) := by
      intro w
      constructor
      · intro hw
        rcases hfib w b hw with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr h1
        · exact Or.inl h1
        · exact Or.inr h1
      · rintro (rfl | rfl)
        · exact hfab
        · rfl
    have : g.comps.countP (fun c => c.kind.isSolid &&
        !((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
        (t.f c.x == t.f b || t.f c.y == t.f b)) =
        g.comps.countP (fun c => c.kind.isSolid &&
        !((g.dotChoice g.splitPairs A).mrep c.x == (g.dotChoice g.splitPairs A).mrep c.y) &&
        (c.x == b || c.y == b)) := by
      apply List.countP_congr
      intro c hc
      constructor
      · intro hh
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, key] at hh ⊢
        obtain ⟨hh1, hh2⟩ := hh
        refine ⟨hh1, ?_⟩
        rcases hh2 with (h1 | h1) | (h1 | h1)
        · exfalso
          have := hnoa c hc
          simp only [Bool.not_eq_true'] at hh1
          rw [hh1.1] at this
          have hconv0 := hh1.2
          simp only [hconv0] at this
          simp [h1] at this
        · exact Or.inl h1
        · exfalso
          have := hnoa c hc
          simp only [Bool.not_eq_true'] at hh1
          rw [hh1.1] at this
          have hconv0 := hh1.2
          simp only [hconv0] at this
          simp [h1] at this
        · exact Or.inr h1
      · intro hh
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, key] at hh ⊢
        obtain ⟨hh1, hh2⟩ := hh
        refine ⟨hh1, ?_⟩
        rcases hh2 with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inr h1)
    rw [this]
    omega

end DegMerge

section Ends0

variable {k n : ℕ}

/-- The end at `x` of a solid edge (nothing for the other components and for loops). -/
private def endFn (x : Atom k n) (c : Comp (Atom k n)) : Option (Bool × Charge) :=
  match c.kind with
  | .G ch => if c.x = x ∧ c.y ≠ x then some (true, ch)
      else if c.y = x ∧ c.x ≠ x then some (false, ch) else none
  | _ => none

private theorem ends_eq (Γ : Graph k n) (x : Atom k n) : Γ.ends x = Γ.comps.filterMap (endFn
    x) := rfl

end Ends0

section StdZ

variable {k N : ℕ}

private theorem hcomps_Z {g : Graph k N} {t : Tracked k N}
    (hm : (g.dotChoice g.splitPairs []).mergeT = some t) (hd : DotOK g)
    (hconv : convS g (g.dotChoice g.splitPairs []) = []) :
    t.g.comps = (g.dotChoice g.splitPairs []).comps.map (Comp.map t.f) := by
  have hs := mergeT_spec hm
  have hcomps : (g.dotChoice g.splitPairs []).comps = keptComps g g.splitPairs ++
      addedComps g.splitPairs [] := rfl
  have hall : ∀ c ∈ (g.dotChoice g.splitPairs []).comps,
      mergeComp (g.dotChoice g.splitPairs []).mrep t.f c = some (c.map t.f) := by
    intro c hc
    rw [hcomps] at hc
    rcases List.mem_append.1 hc with hk | ha
    · have hcg := ((mem_keptComps g _ c).1 hk).1
      by_cases hdot : c.kind = .dot
      · rw [mergeComp_dot hdot, ite_eq_right]
        exact hs.old_dot_ne (hd c hcg hdot).1 (hd c hcg hdot).2
      · by_cases hsol : c.kind.isSolid = true
        · rw [mergeComp_solid hsol, ite_eq_right]
          intro hr
          have : c ∈ convS g (g.dotChoice g.splitPairs []) := by
            unfold convS
            exact List.mem_filter.2 ⟨hcg, by simp [hsol, hr]⟩
          rw [hconv] at this
          cases this
        · exact mergeComp_other hdot (by simpa using hsol)
    · obtain ⟨p, hp, h | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 ha
      · simp at h
      · exact mergeComp_other (by simp [mkC]) (by simp [mkC, Kind.isSolid])
  rw [hs.comps_eq, List.filterMap_congr hall]
  generalize (g.dotChoice g.splitPairs []).comps = l
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem endFn_map_inj {m : ℕ} {f : Atom k N → Atom k m} (hinj : Function.Injective f)
    (u : Atom k N) (c : Comp (Atom k N)) : endFn (f u) (c.map f) = endFn u c := by
  unfold endFn
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp [Comp.map, hinj.eq_iff]

private theorem filter_hcomps_Z {g : Graph k N} (q : Comp (Atom k N) → Bool)
    (hq : ∀ c, q c = true → c.kind ≠ .xdot) :
    ((g.dotChoice g.splitPairs []).comps.filter q) = g.comps.filter q := by
  have hcomps : (g.dotChoice g.splitPairs []).comps = keptComps g g.splitPairs ++
      addedComps g.splitPairs [] := rfl
  rw [hcomps, List.filter_append]
  have h1 : (addedComps g.splitPairs []).filter q = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨p, hp, h | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
    · simp at h
    · intro hqc
      exact hq _ hqc (by simp [mkC])
  rw [h1, List.append_nil]
  unfold keptComps
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  by_cases hqc : q c = true
  · have := hq c hqc
    simp [hqc, this]
  · simp [hqc]

private theorem filterMap_hcomps_Z {g : Graph k N} (e : Comp (Atom k N) → Option (Bool × Charge))
    (he : ∀ c, c.kind = .xdot → e c = none) :
    ((g.dotChoice g.splitPairs []).comps.filterMap e) = g.comps.filterMap e := by
  have hcomps : (g.dotChoice g.splitPairs []).comps = keptComps g g.splitPairs ++
      addedComps g.splitPairs [] := rfl
  rw [hcomps, List.filterMap_append]
  have h1 : (addedComps g.splitPairs []).filterMap e = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    obtain ⟨p, hp, h | ⟨-, -, rfl⟩⟩ := mem_addedComps.1 hc
    · simp at h
    · exact he _ (by simp [mkC])
  rw [h1, List.append_nil]
  unfold keptComps
  rw [List.filterMap_filter]
  apply List.filterMap_congr
  intro c _
  by_cases hk : c.kind = .xdot
  · simp [he c hk]
  · have : (!(c.kind == Kind.xdot && xonlyB g.splitPairs c.x c.y)) = true := by simp [hk]
    simp [this]

private theorem std_Z {g : Graph k N} {t : Tracked k N}
    (hm : (g.dotChoice g.splitPairs []).mergeT = some t) (hd : DotOK g)
    (hconv : convS g (g.dotChoice g.splitPairs []) = []) (hinj : Function.Injective t.f)
    (u : Atom k N) : t.g.stdNeutralAt (t.f u) = g.stdNeutralAt u := by
  have hc := hcomps_Z hm hd hconv
  have hcs : t.g.comps.filter (fun c => c.kind != .xdot && (c.x == t.f u || c.y == t.f u)) =
      (g.comps.filter (fun c => c.kind != .xdot && (c.x == u || c.y == u))).map (Comp.map t.f) := by
    rw [hc, List.filter_map,
        ← filter_hcomps_Z (g := g) (fun c => c.kind != .xdot && (c.x == u || c.y == u))
      (fun c hc' => by
        simp only [Bool.and_eq_true] at hc'
        simpa using hc'.1)]
    congr 1
    apply List.filter_congr
    intro c _
    have hbeq : ∀ a b : Atom k N, (t.f a == t.f b) = (a == b) := fun a b => by
      rw [Bool.eq_iff_iff]; simp [hinj.eq_iff]
    simp [Comp.map, hbeq]
  have hends : t.g.ends (t.f u) = g.ends u := by
    rw [ends_eq, ends_eq, hc, List.filterMap_map]
    have : (endFn (t.f u) ∘ Comp.map t.f) = endFn u := by
      funext c; exact endFn_map_inj hinj u c
    rw [this]
    exact filterMap_hcomps_Z (endFn u) (fun c hk => by simp [endFn, hk])
  unfold Graph.stdNeutralAt
  simp only [hcs, hends, List.length_map, List.filter_map]
  congr 3

end StdZ

section Shape2

variable {k n : ℕ}

/-- Two different solid edges of `Γ` join `x` and `y`. -/
private def TwoEdgesAt (Γ : Graph k n) (x y : Atom k n) : Prop :=
  ∃ i j : ℕ, i ≠ j ∧
    (∃ ca, Γ.comps[i]? = some ca ∧ ca.kind.isSolid = true ∧
      ((ca.x = x ∧ ca.y = y) ∨ (ca.x = y ∧ ca.y = x))) ∧
    (∃ cb, Γ.comps[j]? = some cb ∧ cb.kind.isSolid = true ∧
      ((cb.x = x ∧ cb.y = y) ∨ (cb.x = y ∧ cb.y = x)))

/-- The pre-dot graph of a main term of the multi-edge expansion: two unpartnered solid edges at
the new atom `α` and the degrees of `Ô`. -/
private structure Base2Data (Γ : Graph k n) (x : Atom k n) (g : Graph k (n + 1)) : Prop where
  dotOK : DotOK g
  sl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y
  unp2 : (unpartL g).length ≤ 2
  pair : ∀ c₁ c₂, unpartL g = [c₁, c₂] → SamePair c₁ c₂ →
    ∃ y : Atom k n, y ≠ x ∧ TwoEdgesAt Γ x y ∧
      ((c₁.x = newA 0 ∧ c₁.y = liftA 1 y) ∨ (c₁.x = liftA 1 y ∧ c₁.y = newA 0)) ∧
      ((c₂.x = newA 0 ∧ c₂.y = liftA 1 y) ∨ (c₂.x = liftA 1 y ∧ c₂.y = newA 0))
  degα : g.deg (newA 0) = 2
  deg : ∀ v : Atom k n, g.deg (liftA 1 v) + (if v = x then 2 else 0) = Γ.deg v

private theorem new_unique {s : Tracked k (n + 1)} (hsurj : Function.Surjective s.f)
    {w : Atom k s.nOut} (hw : ∀ v, s.f (liftA 1 v) ≠ w) : w = s.f (newA 0) := by
  obtain ⟨z, rfl⟩ := hsurj w
  rcases atom_cases (j := 1) z with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · exact absurd rfl (hw v)
  · have : i = 0 := Subsingleton.elim _ _
    rw [this]

private theorem a0_of_inj {Γ : Graph k n} {x : Atom k n} {g : Graph k (n + 1)}
    (D : Base2Data Γ x g) {s : Tracked k (n + 1)} (hinj : Function.Injective s.f)
    (hsurj : Function.Surjective s.f) (hdeg : ∀ u, s.g.deg (s.f u) = g.deg u)
    (hstd : ∀ u, s.g.stdNeutralAt (s.f u) = g.stdNeutralAt u) :
    (∃ u, (∀ v, s.f (liftA 1 v) ≠ u) ∧ s.g.deg u = 2 ∧
        ∀ w, (∀ v, s.f (liftA 1 v) ≠ w) → w = u) ∧
      s.g.deg (s.f (liftA 1 x)) + 2 = Γ.deg x ∧
      (∀ v, v ≠ x → s.g.deg (s.f (liftA 1 v)) = Γ.deg v) ∧
      (g.stdNeutralAt (newA 0) = true → ∃ u, (∀ v, s.f (liftA 1 v) ≠ u) ∧
        s.g.stdNeutralAt u = true) := by
  refine ⟨⟨s.f (newA 0), fun v h => ?_, ?_, fun w hw => new_unique hsurj hw⟩, ?_, fun v hv => ?_,
      ?_⟩
  · exact liftA_ne_newA 1 v 0 (hinj h)
  · rw [hdeg, D.degα]
  · rw [hdeg]
    have := D.deg x
    simpa using this
  · rw [hdeg]
    have := D.deg v
    simpa [hv] using this
  · intro h
    exact ⟨s.f (newA 0), fun v hv => liftA_ne_newA 1 v 0 (hinj hv), by rw [hstd]; exact h⟩

private theorem shape2 {Γ : Graph k n} {x : Atom k n} {g : Graph k (n + 1)}
    (D : Base2Data Γ x g) {s : Tracked k (n + 1)} (hs : s ∈ oDotT g) (hle : s.g.ord ≤ g.ord) :
    ((∃ u, (∀ v, s.f (liftA 1 v) ≠ u) ∧ s.g.deg u = 2 ∧
        ∀ w, (∀ v, s.f (liftA 1 v) ≠ w) → w = u) ∧
      s.g.deg (s.f (liftA 1 x)) + 2 = Γ.deg x ∧
      (∀ v, v ≠ x → s.g.deg (s.f (liftA 1 v)) = Γ.deg v) ∧
      (g.stdNeutralAt (newA 0) = true → ∃ u, (∀ v, s.f (liftA 1 v) ≠ u) ∧
        s.g.stdNeutralAt u = true)) ∨
    (∃ y, y ≠ x ∧ s.g.deg (s.f (liftA 1 x)) + 2 = Γ.deg x ∧ s.g.deg (s.f (liftA 1 y)) + 2 = Γ.deg y
        ∧
      (∀ v, v ≠ x → v ≠ y → s.g.deg (s.f (liftA 1 v)) = Γ.deg v) ∧
      (∀ u, (∀ v, s.f (liftA 1 v) ≠ u) → s.g.deg u = 0) ∧
      TwoEdgesAt Γ x y ∧ ∃ c₁ c₂, unpartL g = [c₁, c₂] ∧
        ((c₁.x = newA 0 ∧ c₁.y = liftA 1 y) ∨ (c₁.x = liftA 1 y ∧ c₁.y = newA 0)) ∧
        ((c₂.x = newA 0 ∧ c₂.y = liftA 1 y) ∨ (c₂.x = liftA 1 y ∧ c₂.y = newA 0))) := by
  rcases mem_oDotT_cases' hs with rfl | ⟨A, hA, hm⟩
  · left
    exact a0_of_inj D (fun a b h => h) (fun a => ⟨a, rfl⟩) (fun u => rfl) (fun u => rfl)
  have hms := mergeT_spec hm
  rcases dot_eq D.dotOK D.sl D.unp2 hA hm hle with
    ⟨hA0, hn, hconv⟩ | ⟨c₁, c₂, hU, hsp, hconv, hKr, p, hp, hpA, hpm⟩
  · left
    have hinj := hms.injective_of_nOut hn
    subst hA0
    exact a0_of_inj D hinj hms.f_surj (deg_Z hm hinj hconv) (std_Z hm D.dotOK hconv hinj)
  right
  obtain ⟨y, hyx, hTE, h1, h2⟩ := D.pair c₁ c₂ hU hsp
  have hyα : liftA 1 y ≠ newA 0 := liftA_ne_newA 1 y 0
  have hF1 : (p.1 = newA 0 ∧ p.2.1 = liftA 1 y) ∨ (p.1 = liftA 1 y ∧ p.2.1 = newA 0) := by
    rcases hpm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨e1.trans a1, e2.trans a2⟩
    · exact Or.inr ⟨e1.trans a1, e2.trans a2⟩
    · exact Or.inr ⟨e1.trans a2, e2.trans a1⟩
    · exact Or.inl ⟨e1.trans a2, e2.trans a1⟩
  have hrep := pair_rep hp hpA
  have hcnt : ∀ u : Atom k (n + 1), ([c₁, c₂].countP fun c => c.x == u || c.y == u) =
      (if u = newA 0 then 2 else 0) + (if u = liftA 1 y then 2 else 0) := by
    intro u
    by_cases hua : u = newA 0
    · have hub : u ≠ liftA 1 y := fun h => hyα (h.symm.trans hua)
      subst hua
      rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
        simp [a1, a2, b1, b2, hub]
    · by_cases hub : u = liftA 1 y
      · subst hub
        rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
          simp [a1, a2, b1, b2, hyα]
      · rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
          simp [a1, a2, b1, b2, hua, hub, Ne.symm hua, Ne.symm hub]
  refine ⟨y, hyx, ?_⟩
  by_cases hyR : y.isRight = true
  · -- `y` internal: `α` is identified with `y`
    obtain ⟨j, rfl⟩ : ∃ j, y = Sum.inr j := by
      rcases y with a | j
      · simp at hyR
      · exact ⟨j, rfl⟩
    have hne : (Fin.castAdd 1 j : Fin (n + 1)) ≠ Fin.natAdd n (0 : Fin 1) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      have := j.isLt
      omega
    have hrepI : (g.dotChoice g.splitPairs A).mrep (Sum.inr (Fin.castAdd 1 j)) =
        (g.dotChoice g.splitPairs A).mrep (Sum.inr (Fin.natAdd n (0 : Fin 1))) := by
      rcases hF1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at hrep
        exact hrep.symm
      · rw [e1, e2] at hrep
        exact hrep
    have hr1 := hms.r_one hne hrepI
    have hr : s.nOut + 1 = n + 1 := by
      have := hms.nOut_le
      omega
    have hf : s.f (Sum.inr (Fin.castAdd 1 j)) = s.f (Sum.inr (Fin.natAdd n (0 : Fin 1))) :=
      hms.f_eq _ _ hrepI rfl rfl
    have hfib := fiber_r1 hms hr hne hf
    obtain ⟨hE1a, hE1b⟩ := deg_E1 (a := newA 0) (b := liftA 1 (Sum.inr j)) hm
      (fun u v huv => by
        rcases hfib u v huv with h | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨h1', h2'⟩)
        · exact Or.inr (Or.inl ⟨h1', h2'⟩))
      hf.symm hconv h1 h2 D.degα
    have hxne : liftA 1 x ≠ liftA 1 (Sum.inr j) := fun h => hyx (liftA_injective 1 h).symm
    refine ⟨?_, ?_, ?_, ?_, hTE, c₁, c₂, hU, h1, h2⟩
    · have := hE1a (liftA 1 x) (liftA_ne_newA 1 x 0) hxne
      have h3 := D.deg x
      simp at h3
      omega
    · have h3 := D.deg (Sum.inr j)
      rw [ite_eq_right hyx] at h3
      omega
    · intro v hvx hvy
      have hv1 : liftA 1 v ≠ liftA 1 (Sum.inr j) := fun h => hvy (liftA_injective 1 h)
      have := hE1a (liftA 1 v) (liftA_ne_newA 1 v 0) hv1
      have h3 := D.deg v
      rw [ite_eq_right hvx] at h3
      omega
    · intro u hu
      exfalso
      have := new_unique hms.f_surj hu
      exact hu (Sum.inr j) (hf.trans this.symm)
  · -- `y` external: a dotted edge to `y` stays
    obtain ⟨a₀, rfl⟩ : ∃ a₀, y = Sum.inl a₀ := by
      rcases y with a | j
      · exact ⟨a, rfl⟩
      · simp at hyR
    have hf0 : s.f (newA 0) ≠ s.f (liftA 1 (Sum.inl a₀)) := by
      obtain ⟨gg, hg, -⟩ := hms.f_inr
      have h1' : s.f (newA 0) = Sum.inr (gg (Fin.natAdd n (0 : Fin 1))) := hg _
      have h2' : s.f (liftA 1 (Sum.inl a₀)) = Sum.inl a₀ := hms.f_inl a₀
      rw [h1', h2']
      exact Sum.inr_ne_inl
    have hodk : 1 ≤ odK g A s := by
      apply odK_pos hp hpA
      rcases hF1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact hf0
      · rw [e1, e2]; exact hf0.symm
    have hn : s.nOut = n + 1 := by
      have := hms.nOut_le
      omega
    have hinj := hms.injective_of_nOut hn
    have hd := fun u => deg_E2 hm hinj hconv u
    have hdα := hd (newA 0)
    rw [hcnt, ite_eq_left rfl, ite_eq_right (Ne.symm hyα)] at hdα
    have hdy := hd (liftA 1 (Sum.inl a₀))
    rw [hcnt, ite_eq_right hyα, ite_eq_left rfl] at hdy
    have hxne : liftA 1 x ≠ liftA 1 (Sum.inl a₀) := fun h => hyx (liftA_injective 1 h).symm
    refine ⟨?_, ?_, ?_, ?_, hTE, c₁, c₂, hU, h1, h2⟩
    · have := hd (liftA 1 x)
      rw [hcnt, ite_eq_right (liftA_ne_newA 1 x 0), ite_eq_right hxne] at this
      have h3 := D.deg x
      simp at h3
      omega
    · have h3 := D.deg (Sum.inl a₀)
      rw [ite_eq_right hyx] at h3
      omega
    · intro v hvx hvy
      have hv1 : liftA 1 v ≠ liftA 1 (Sum.inl a₀) := fun h => hvy (liftA_injective 1 h)
      have := hd (liftA 1 v)
      rw [hcnt, ite_eq_right (liftA_ne_newA 1 v 0), ite_eq_right hv1] at this
      have h3 := D.deg v
      rw [ite_eq_right hvx] at h3
      omega
    · intro u hu
      rw [new_unique hms.f_surj hu]
      have := D.degα
      omega

end Shape2

section Shape0

variable {k n : ℕ}

/-- The pre-dot graph of the main term of `Ô_GG` when `y = y'`: no unpartnered solid edge, and the
degrees of the pair-removed pattern. -/
private structure Main0Data (dΓ : Atom k n → ℕ) (x y : Atom k n) (g : Graph k n) : Prop where
  dotOK : DotOK g
  sl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y
  unp0 : (unpartL g).length = 0
  degx : g.deg x = 0
  degy : g.deg y + 2 = dΓ y
  dego : ∀ v, v ≠ x → v ≠ y → g.deg v = dΓ v

private theorem shape0 {dΓ : Atom k n → ℕ} {x y : Atom k n} {g : Graph k n}
    (D : Main0Data dΓ x y g) {s : Tracked k n} (hs : s ∈ oDotT g) (hle : s.g.ord ≤ g.ord) :
    s.g.deg (s.f x) = 0 ∧ s.g.deg (s.f y) + 2 = dΓ y ∧
      (∀ v, v ≠ x → v ≠ y → s.g.deg (s.f v) = dΓ v) ∧
      (∀ u, (∀ v, s.f v ≠ u) → s.g.deg u = 0) := by
  have key : (Function.Injective s.f ∧ Function.Surjective s.f ∧ ∀ u,
      s.g.deg (s.f u) = g.deg u) := by
    rcases mem_oDotT_cases' hs with rfl | ⟨A, hA, hm⟩
    · exact ⟨fun a b h => h, fun a => ⟨a, rfl⟩, fun u => rfl⟩
    · have hms := mergeT_spec hm
      rcases dot_eq D.dotOK D.sl (by rw [D.unp0]; omega) hA hm hle with
        ⟨hA0, hn, hconv⟩ | ⟨c₁, c₂, hU, -⟩
      · have hinj := hms.injective_of_nOut hn
        exact ⟨hinj, hms.f_surj, deg_Z hm hinj hconv⟩
      · have := D.unp0
        rw [hU] at this
        simp at this
  obtain ⟨hinj, hsurj, hdeg⟩ := key
  refine ⟨?_, ?_, fun v hvx hvy => ?_, fun u hu => ?_⟩
  · rw [hdeg]; exact D.degx
  · rw [hdeg]; exact D.degy
  · rw [hdeg]; exact D.dego v hvx hvy
  · obtain ⟨z, rfl⟩ := hsurj u
    exact absurd rfl (hu z)

end Shape0

section Base2

variable {k n : ℕ}

private theorem partnered_old' {C m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n}
    {g' : Graph k m} (hN : g₁.Normal C)
    (hold : ∀ c ∈ g₁.comps, c.kind.isRandom = false → c.map φ ∈ g'.comps)
    {c' : Comp (Atom k m)}
    (hold' : ∃ c ∈ g₁.comps, c'.x = φ c.x ∧ c'.y = φ c.y ∧ c'.kind = c.kind)
    (hs : c'.kind.isSolid = true) : partnered g' c' = true := by
  obtain ⟨c, hc, h1, h2, h3⟩ := hold'
  have hcs : c.kind.isSolid = true := by rw [← h3]; exact hs
  have hne : c.x ≠ c.y := hN.2.1 c hc hcs
  have hx := (hN.2.2 c.x c.y hne).2 ⟨c, hc, hcs, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨c₃, hc₃, hk₃, hm₃⟩ := hx
  rw [partnered_iff]
  refine ⟨c₃.map φ, hold c₃ hc₃ (by rw [hk₃]; rfl), by simpa [Comp.map] using hk₃, ?_⟩
  unfold SamePair
  simp only [Comp.map]
  rcases hm₃ with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · left; rw [h1, h2, a1, a2]; exact ⟨rfl, rfl⟩
  · right; rw [h1, h2, a1, a2]; exact ⟨rfl, rfl⟩

private theorem countP_liftCs {j : ℕ} (B : List (Comp (Atom k n))) (v : Atom k n) :
    (liftCs j B).countP (fun c => c.kind.isSolid && (c.x == liftA j v || c.y == liftA j v)) =
      B.countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) := by
  unfold liftCs
  rw [List.countP_map]
  apply List.countP_congr
  intro c _
  simp [Comp.map, (liftA_injective (k := k) (n := n) j).eq_iff]

private theorem countP_liftCs_new {j : ℕ} (B : List (Comp (Atom k n))) (i : Fin j) :
    (liftCs j B).countP (fun c => c.kind.isSolid && (c.x == newA i || c.y == newA i)) = 0 := by
  rw [List.countP_eq_zero]
  intro c hc
  obtain ⟨c0, -, rfl⟩ := mem_liftCs.1 hc
  simp [Comp.map, liftA_ne_newA]

set_option linter.flexible false in
/-- A graph obtained from `Γ` by replacing two solid edges at `x` by the waved edge `s_{xα}` and
two solid edges at the new atom `α` satisfies the data of the main terms of the multi-edge
expansion. -/
private theorem base2_of_shape {C : ℕ} {Γ : Graph k n} {x : Atom k n} (hN : Γ.Normal C)
    (B : List (Comp (Atom k n))) (ea eb : Comp (Atom k n))
    (hBR : (B ++ [ea, eb]).Perm Γ.comps) (ia ib : ℕ) (hia : Γ.comps[ia]? = some ea)
    (hib : Γ.comps[ib]? = some eb) (hiab : ia ≠ ib)
    (ya yb : Atom k n) (hya : ya ≠ x) (hyb : yb ≠ x)
    (hea_s : ea.kind.isSolid = true) (heb_s : eb.kind.isSolid = true)
    (hea : (ea.x = x ∧ ea.y = ya) ∨ (ea.y = x ∧ ea.x = ya))
    (heb : (eb.x = x ∧ eb.y = yb) ∨ (eb.y = x ∧ eb.x = yb))
    (sx Ga Gb : Comp (Atom k (n + 1))) (g : Graph k (n + 1))
    (hg : g.comps = liftCs 1 B ++ [sx, Ga, Gb])
    (hsx : sx.kind.isSolid = false) (hGa_s : Ga.kind.isSolid = true) (hGb_s : Gb.kind.isSolid =
        true)
    (hGa : (Ga.x = newA 0 ∧ Ga.y = liftA 1 ya) ∨ (Ga.x = liftA 1 ya ∧ Ga.y = newA 0))
    (hGb : (Gb.x = newA 0 ∧ Gb.y = liftA 1 yb) ∨ (Gb.x = liftA 1 yb ∧ Gb.y = newA 0))
    (hdot : DotOK g) (hsl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y) :
    Base2Data Γ x g := by
  have hBsub : ∀ c ∈ B, c ∈ Γ.comps := fun c hc => hBR.subset (List.mem_append_left _ hc)
  have hold : ∀ c ∈ Γ.comps, c.kind.isRandom = false → c.map (liftA 1) ∈ g.comps := by
    intro c hc hr
    have hcB : c ∈ B := by
      rcases List.mem_append.1 (hBR.symm.subset hc) with h | h
      · exact h
      · exfalso
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · simp [Kind.isSolid] at hr hea_s
          cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isRandom]
        · cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isRandom]
    rw [hg]
    exact List.mem_append_left _ (mem_liftCs.2 ⟨c, hcB, rfl⟩)
  have hpart : ∀ c ∈ liftCs 1 B, c.kind.isSolid = true → partnered g c = true := by
    intro c hc hs
    obtain ⟨c0, hc0, rfl⟩ := mem_liftCs.1 hc
    exact partnered_old' hN hold ⟨c0, hBsub c0 hc0, rfl, rfl, rfl⟩ hs
  have hU : unpartL g = [Ga, Gb].filter (fun c => c.kind.isSolid && !partnered g c) := by
    unfold unpartL
    rw [hg, List.filter_append]
    have h0 : (liftCs 1 B).filter (fun c => c.kind.isSolid && !partnered g c) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc
      by_cases hs : c.kind.isSolid = true
      · simp [hs, hpart c hc hs]
      · simp [Bool.eq_false_iff.2 hs]
    rw [h0, List.nil_append, List.filter_cons_of_neg (by simp [hsx])]
  have hAlpha : ∀ (y : Atom k n) (c : Comp (Atom k (n + 1))), ((c.x = newA 0 ∧ c.y = liftA 1 y) ∨
      (c.x = liftA 1 y ∧ c.y = newA 0)) → (c.x == newA 0 || c.y == newA 0) = true := by
    intro y c hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  refine ⟨hdot, hsl, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    exact (List.length_filter_le _ _).trans (by simp)
  · intro c₁ c₂ hU2 hsp
    rw [hU] at hU2
    have hEq : [Ga, Gb].filter (fun c => c.kind.isSolid && !partnered g c) = [Ga, Gb] :=
      (List.filter_sublist).eq_of_length (by rw [hU2]; rfl)
    rw [hEq] at hU2
    obtain ⟨rfl, rfl⟩ : Ga = c₁ ∧ Gb = c₂ := by simpa using hU2
    have hyy : yb = ya := by
      unfold SamePair at hsp
      rcases hGa with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hGb with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
        rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [a1, a2, b1, b2] at h1 h2 <;>
        first
        | exact liftA_injective 1 h1
        | exact liftA_injective 1 h2
        | exact (liftA_ne_newA 1 _ 0 h1.symm).elim
        | exact (liftA_ne_newA 1 _ 0 h1).elim
    subst hyy
    refine ⟨yb, hya, ⟨ia, ib, hiab, ⟨ea, hia, hea_s, ?_⟩, ⟨eb, hib, heb_s, ?_⟩⟩, hGa, hGb⟩
    · rcases hea with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact Or.inl ⟨a1, a2⟩
      · exact Or.inr ⟨a2, a1⟩
    · rcases heb with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · exact Or.inl ⟨a1, a2⟩
      · exact Or.inr ⟨a2, a1⟩
  · rw [deg_eq_countP, hg, List.countP_append, countP_liftCs_new]
    simp [hsx, hGa_s, hGb_s, hAlpha _ _ hGa, hAlpha _ _ hGb]
  · intro v
    have hΓ : Γ.deg v = B.countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) +
        [ea, eb].countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) := by
      rw [deg_eq_countP, ← hBR.countP_eq, List.countP_append]
    have hg' : g.deg (liftA 1 v) = B.countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) +
        [Ga, Gb].countP (fun c => c.kind.isSolid &&
          (c.x == liftA 1 v || c.y == liftA 1 v)) := by
      rw [deg_eq_countP, hg, List.countP_append, countP_liftCs]
      simp [hsx]
    have hpa : (ea.kind.isSolid && (ea.x == v || ea.y == v)) = (x == v || ya == v) := by
      rcases hea with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [hea_s, e1, e2, Bool.or_comm]
    have hpb : (eb.kind.isSolid && (eb.x == v || eb.y == v)) = (x == v || yb == v) := by
      rcases heb with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [heb_s, e1, e2, Bool.or_comm]
    have hna : (newA 0 == liftA 1 v) = false := by
      simp [Ne.symm (liftA_ne_newA 1 v 0)]
    have hli : ∀ y : Atom k n, (liftA 1 y == liftA 1 v) = (y == v) := by
      intro y
      rw [Bool.eq_iff_iff]
      simp [(liftA_injective (k := k) (n := n) 1).eq_iff]
    have hqa : (Ga.kind.isSolid && (Ga.x == liftA 1 v || Ga.y == liftA 1 v)) = (ya == v) := by
      rcases hGa with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [hGa_s, e1, e2, hna, hli]
    have hqb : (Gb.kind.isSolid && (Gb.x == liftA 1 v || Gb.y == liftA 1 v)) = (yb == v) := by
      rcases hGb with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp [hGb_s, e1, e2, hna, hli]
    rw [hΓ, hg']
    simp only [List.countP_cons, List.countP_nil, hpa, hpb, hqa, hqb]
    simp only [beq_iff_eq, Bool.or_eq_true]
    by_cases hvx : x = v <;> by_cases hva : ya = v <;> by_cases hvb : yb = v <;>
      simp [hvx, hva, hvb]
    all_goals first
      | exact absurd (hva.trans hvx.symm) hya
      | exact absurd (hvb.trans hvx.symm) hyb
      | exact fun h => hvx h.symm

end Base2

section Base2Fam

variable {k n : ℕ}

private theorem base2_baseM {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) {j : ℕ}
    (hj : j ∈ Γ.edgeIdx x .minus true) (d : Coeff) :
    Base2Data Γ x (⟨EO_oBaseM x Γ i₁ e₁ j, d⟩ : Graph k (n + 1)) ∧
      (⟨EO_oBaseM x Γ i₁ e₁ j, d⟩ : Graph k (n + 1)).ord = Γ.ord := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  obtain ⟨ej, hej, hkj, hxj, hyj⟩ := mem_edgeIdx.1 hj
  have hne : i₁ ≠ j := by
    rintro rfl
    rw [Ctx.hL] at hej
    obtain rfl := Option.some.inj hej
    rw [hk₁] at hkj
    cases hkj
  have hperm := eraseIdxs_two_perm hne Ctx.hL hej
  have hgetD : Γ.comps.getD j e₁ = ej := by simp [List.getD_eq_getElem?_getD, hej]
  have hbase : EO_oBaseM x Γ i₁ e₁ j = liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ej.y)] := by
    unfold EO_oBaseM; rw [hgetD]
  have h := preT_baseM Ctx hj none [] newOK_nil (by simp) (by simp) (by simp) (by simp) d
  have hP := h.1
  simp only [labW, List.append_nil] at hP h
  refine ⟨?_, by simpa [ordL] using h.2.1⟩
  exact base2_of_shape Ctx.normal (eraseIdxs [i₁,
      j] Γ.comps) e₁ ej hperm i₁ j Ctx.hL hej hne e₁.y ej.y hy₁ hyj
    (by simp [hk₁, Kind.isSolid]) (by simp [hkj, Kind.isSolid]) (Or.inl ⟨hx₁, rfl⟩)
    (Or.inl ⟨hxj, rfl⟩) (EO_oSx x) (EO_oGy e₁) (mkC (.G .minus) (newA 0) (liftA 1 ej.y))
    ⟨EO_oBaseM x Γ i₁ e₁ j, d⟩ hbase (by simp [EO_oSx, mkC, Kind.isSolid])
    (by simp [EO_oGy, mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid])
    (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) hP.dotOK hP.sl

private theorem base2_baseP {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) {j : ℕ}
    (hj : j ∈ Γ.edgeIdx x .plus false) (d : Coeff) :
    Base2Data Γ x (⟨EO_oBaseP x Γ i₁ e₁ j, d⟩ : Graph k (n + 1)) ∧
      (⟨EO_oBaseP x Γ i₁ e₁ j, d⟩ : Graph k (n + 1)).ord = Γ.ord := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  obtain ⟨ej, hej, hkj, hyj, hxj⟩ := mem_edgeIdx.1 hj
  have hne : i₁ ≠ j := by
    rintro rfl
    rw [Ctx.hL] at hej
    obtain rfl := Option.some.inj hej
    exact hy₁ hyj
  have hperm := eraseIdxs_two_perm hne Ctx.hL hej
  have hgetD : Γ.comps.getD j e₁ = ej := by simp [List.getD_eq_getElem?_getD, hej]
  have hbase : EO_oBaseP x Γ i₁ e₁ j = liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_oGy e₁, mkC (.G .plus) (liftA 1 ej.x) (newA 0)] := by
    unfold EO_oBaseP; rw [hgetD]
  have h := preT_baseP Ctx hj none [] newOK_nil (by simp) (by simp) (by simp) (by simp) d
  have hP := h.1
  simp only [labW, List.append_nil] at hP h
  refine ⟨?_, by simpa [ordL] using h.2.1⟩
  exact base2_of_shape Ctx.normal (eraseIdxs [i₁,
      j] Γ.comps) e₁ ej hperm i₁ j Ctx.hL hej hne e₁.y ej.x hy₁ hxj
    (by simp [hk₁, Kind.isSolid]) (by simp [hkj, Kind.isSolid]) (Or.inl ⟨hx₁, rfl⟩)
    (Or.inr ⟨hyj, rfl⟩) (EO_oSx x) (EO_oGy e₁) (mkC (.G .plus) (liftA 1 ej.x) (newA 0))
    ⟨EO_oBaseP x Γ i₁ e₁ j, d⟩ hbase (by simp [EO_oSx, mkC, Kind.isSolid])
    (by simp [EO_oGy, mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid])
    (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hP.dotOK hP.sl

private theorem base2_iBaseM {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) {j : ℕ}
    (hj : j ∈ Γ.edgeIdx x .minus false) (d : Coeff) :
    Base2Data Γ x (⟨EO_iBaseM x Γ i₁ e₁ j, d⟩ : Graph k (n + 1)) ∧
      (⟨EO_iBaseM x Γ i₁ e₁ j, d⟩ : Graph k (n + 1)).ord = Γ.ord := by
  obtain ⟨hk₁, hy₁, hx₁⟩ := Ctx.e₁spec
  obtain ⟨ej, hej, hkj, hyj, hxj⟩ := mem_edgeIdx.1 hj
  have hne : i₁ ≠ j := by
    rintro rfl
    rw [Ctx.hL] at hej
    obtain rfl := Option.some.inj hej
    rw [hk₁] at hkj
    cases hkj
  have hperm := eraseIdxs_two_perm hne Ctx.hL hej
  have hgetD : Γ.comps.getD j e₁ = ej := by simp [List.getD_eq_getElem?_getD, hej]
  have hbase : EO_iBaseM x Γ i₁ e₁ j = liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
      [EO_oSx x, EO_iGw e₁, mkC (.G .minus) (liftA 1 ej.x) (newA 0)] := by
    unfold EO_iBaseM; rw [hgetD]
  have h := preT_iBaseM Ctx hj none [] newOK_nil (by simp) (by simp) (by simp) (by simp) d
  have hP := h.1
  simp only [labW, List.append_nil] at hP h
  refine ⟨?_, by simpa [ordL] using h.2.1⟩
  exact base2_of_shape Ctx.normal (eraseIdxs [i₁,
      j] Γ.comps) e₁ ej hperm i₁ j Ctx.hL hej hne e₁.x ej.x hx₁ hxj
    (by simp [hk₁, Kind.isSolid]) (by simp [hkj, Kind.isSolid]) (Or.inr ⟨hy₁, rfl⟩)
    (Or.inr ⟨hyj, rfl⟩) (EO_oSx x) (EO_iGw e₁) (mkC (.G .minus) (liftA 1 ej.x) (newA 0))
    ⟨EO_iBaseM x Γ i₁ e₁ j, d⟩ hbase (by simp [EO_oSx, mkC, Kind.isSolid])
    (by simp [EO_iGw, mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid])
    (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hP.dotOK hP.sl

end Base2Fam

section ConjPre

variable {k n : ℕ}

private theorem Graph.conj_deg (Γ : Graph k n) : Γ.conj.deg = Γ.deg := by
  funext u
  unfold Graph.deg
  simp only [Graph.conj_comps, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp [Comp.conj, Kind.conj_isSolid]

private theorem Graph.conj_labelFree (Γ : Graph k n) : Γ.conj.LabelFree ↔ Γ.LabelFree := by
  unfold Graph.LabelFree
  constructor
  · intro h c hc
    exact h c.conj (Graph.mem_conj_comps.2 ⟨c, hc, rfl⟩)
  · intro h c' hc'
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h c hc

private theorem partnered_conj (g : Graph k n) (c : Comp (Atom k n)) :
    partnered g.conj c = partnered g c := by
  unfold partnered
  rw [Graph.conj_comps, List.any_map]
  refine List.any_congr rfl ?_
  intro c₂
  simp only [Function.comp, Comp.conj_kind, Comp.conj_x, Comp.conj_y]
  have : (c₂.kind.conj == Kind.xdot) = (c₂.kind == Kind.xdot) := by
    rw [Bool.eq_iff_iff]
    simpa using Kind.conj_eq_xdot c₂.kind
  rw [this]

private theorem conj_unpartL (g : Graph k n) : unpartL g.conj = (unpartL g).map Comp.conj := by
  unfold unpartL
  rw [Graph.conj_comps, List.filter_map]
  congr 1
  apply List.filter_congr
  intro c _
  have h2 : partnered g c.conj = partnered g c := partnered_congr g rfl rfl
  simp [Comp.conj_kind, Kind.conj_isSolid, partnered_conj, h2]

private theorem Graph.conj_dotOK {g : Graph k n} (h : DotOK g) : DotOK g.conj := by
  intro c' hc' hk
  obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
  exact h c hc ((Kind.conj_eq_dot _).1 hk)

private theorem Graph.conj_sl {g : Graph k n} (h : ∀ c ∈ g.comps,
    c.kind.isSolid = true → c.x ≠ c.y) :
    ∀ c ∈ g.conj.comps, c.kind.isSolid = true → c.x ≠ c.y := by
  intro c' hc' hs
  obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
  exact h c hc (by simpa [Kind.conj_isSolid] using hs)

private theorem conj_unp {g : Graph k n}
    (h : (unpartL g).length ≤ 4 ∧ ∀ L : List (Comp (Atom k n)), L.Sublist (unpartL g) →
      3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂) :
    (unpartL g.conj).length ≤ 4 ∧ ∀ L : List (Comp (Atom k n)), L.Sublist (unpartL g.conj) →
      3 ≤ L.length → ∃ c₁ ∈ L, ∃ c₂ ∈ L, ¬ SamePair c₁ c₂ := by
  rw [conj_unpartL]
  refine ⟨by simpa using h.1, fun L hL h3 => ?_⟩
  obtain ⟨L', hL', rfl⟩ := List.sublist_map_iff.1 hL
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := h.2 L' hL' (by simpa using h3)
  exact ⟨c₁.conj, List.mem_map_of_mem hc₁, c₂.conj, List.mem_map_of_mem hc₂, hne⟩

theorem PreT.conj {C : ℕ} {o : ℤ} {x : Atom k n} {T : Tracked k n} (h : PreT C o x T) :
    PreT C o x ⟨T.nOut, T.g.conj, T.f⟩ := by
  refine ⟨?_, ?_, ?_, ?_, Graph.conj_dotOK h.dotOK, Graph.conj_sl h.sl, conj_unp h.unp,
    Graph.conj_Plain h.plain, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [Graph.conj_length] using h.size
  · intro u v
    change T.g.conj.edgeGraphNoX.Reachable u v
    rw [Graph.conj_edgeGraphNoX]; exact h.conn u v
  · intro a b
    change T.g.conj.wavedThetaGraph.Reachable (.inr a) (.inr b)
    rw [Graph.conj_wavedThetaGraph]; exact h.int a b
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.noIntDot c hc ((Kind.conj_eq_dot _).1 hk)
  · change T.g.conj.labels.length ≤ 1
    rw [Graph.conj_labels]; exact h.lab.1
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    simp only [Comp.conj_label]
    refine h.lab.2 c hc ?_
    rcases hk with hk | hk
    · exact Or.inl ((Kind.conj_eq_dot _).1 hk)
    · exact Or.inr ((Kind.conj_eq_xdot _).1 hk)
  · change o ≤ T.g.conj.ord
    rw [Graph.conj_ord]; exact h.ord
  · intro u hu
    change T.g.conj.wavedGraph.Reachable (T.f x) u
    rw [Graph.conj_wavedGraph]; exact h.new u hu

private theorem TwoEdgesAt.conj_of {Γ : Graph k n} {x y : Atom k n} (h : TwoEdgesAt Γ.conj x y) :
    TwoEdgesAt Γ x y := by
  obtain ⟨i, j, hij, ⟨ca, hca, hs, he⟩, ⟨cb, hcb, hs', he'⟩⟩ := h
  simp only [Graph.conj_comps, List.getElem?_map, Option.map_eq_some_iff] at hca hcb
  obtain ⟨ca0, hca0, rfl⟩ := hca
  obtain ⟨cb0, hcb0, rfl⟩ := hcb
  exact ⟨i, j, hij, ⟨ca0, hca0, by simpa [Kind.conj_isSolid] using hs, he⟩,
    ⟨cb0, hcb0, by simpa [Kind.conj_isSolid] using hs', he'⟩⟩

private theorem Base2Data.conj {Γ : Graph k n} {x : Atom k n} {g : Graph k (n + 1)}
    (D : Base2Data Γ.conj x g) : Base2Data Γ x g.conj where
  dotOK := Graph.conj_dotOK D.dotOK
  sl := Graph.conj_sl D.sl
  unp2 := by rw [conj_unpartL]; simpa using D.unp2
  pair := by
    intro c₁ c₂ hU hsp
    rw [conj_unpartL] at hU
    obtain ⟨d₁, d₂, hd, rfl, rfl⟩ : ∃ d₁ d₂, unpartL g = [d₁,
        d₂] ∧ c₁ = d₁.conj ∧ c₂ = d₂.conj := by
      rcases hl : unpartL g with _ | ⟨d₁, _ | ⟨d₂, _ | ⟨d₃, rest⟩⟩⟩
      · rw [hl] at hU; simp at hU
      · rw [hl] at hU; simp at hU
      · rw [hl] at hU
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hU
        exact ⟨d₁, d₂, rfl, hU.1.symm, hU.2.symm⟩
      · rw [hl] at hU; simp at hU
    obtain ⟨y, hy, hTE, h1, h2⟩ := D.pair d₁ d₂ hd hsp
    exact ⟨y, hy, hTE.conj_of, h1, h2⟩
  degα := by rw [Graph.conj_deg]; exact D.degα
  deg := by
    intro v
    have := D.deg v
    rw [Graph.conj_deg] at this ⊢
    exact this

private theorem Main0Data.conj {dΓ : Atom k n → ℕ} {x y : Atom k n} {g : Graph k n}
    (D : Main0Data dΓ x y g) : Main0Data dΓ x y g.conj where
  dotOK := Graph.conj_dotOK D.dotOK
  sl := Graph.conj_sl D.sl
  unp0 := by rw [conj_unpartL]; simpa using D.unp0
  degx := by rw [Graph.conj_deg]; exact D.degx
  degy := by rw [Graph.conj_deg]; exact D.degy
  dego := by
    intro v hvx hvy
    rw [Graph.conj_deg]; exact D.dego v hvx hvy

end ConjPre

section EdgeIdxConj

variable {k n : ℕ}

private theorem zipIdx_map' {α β : Type*} (f : α → β) (l : List α) (m : ℕ) :
    (l.map f).zipIdx m = (l.zipIdx m).map (fun p => (f p.1, p.2)) := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx_cons, ih]

private theorem edgeIdx_conj (Γ : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    Γ.conj.edgeIdx x ch out = Γ.edgeIdx x ch.flip out := by
  unfold Graph.edgeIdx
  rw [Graph.conj_comps, zipIdx_map', List.filter_map, List.map_map]
  congr 1
  · apply List.filter_congr
    intro p _
    rw [Bool.eq_iff_iff]
    cases ch <;> rcases p with ⟨⟨κ, a, b, mi, l⟩, i⟩ <;>
      cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;>
      simp [Comp.conj, Kind.conj, Charge.flip]

private theorem OutCtx.conj_of {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true)
    (hU : ∀ c ∈ Γ.comps, c.label = none) (hOP : Γ.edgeIdx x .minus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) : OutCtx C x Γ.conj i₁ is₂ e₁.conj where
  normal := Graph.conj_Normal hN
  plain := Graph.conj_Plain hP
  right := hx
  unl := fun c' hc' => by
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    simpa using hU c hc
  hOP := by rw [edgeIdx_conj]; exact hOP
  hL := by simp [Graph.conj_comps, hL]

private theorem InCtx.conj_of {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true)
    (hU : ∀ c ∈ Γ.comps, c.label = none) (hIP : Γ.edgeIdx x .minus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hOP0 : Γ.edgeIdx x .plus true = [])
    (hOM0 : Γ.edgeIdx x .minus true = []) : InCtx C x Γ.conj i₁ is₂ e₁.conj where
  normal := Graph.conj_Normal hN
  plain := Graph.conj_Plain hP
  right := hx
  unl := fun c' hc' => by
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    simpa using hU c hc
  hIP := by rw [edgeIdx_conj]; exact hIP
  hL := by simp [Graph.conj_comps, hL]
  hOP0 := by rw [edgeIdx_conj]; exact hOM0
  hOM0 := by rw [edgeIdx_conj]; exact hOP0

private theorem xdotsAt_of_normal {C : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) (x : Atom k n)
    (is : List ℕ) (h : ∀ j ∈ is, ∃ c, Γ.comps[j]? = some c ∧ c.kind.isSolid = true ∧
      (c.x = x ∨ c.y = x)) : Γ.xdotsAt x is = true := by
  unfold Graph.xdotsAt
  rw [List.all_eq_true]
  intro j hj
  obtain ⟨c, hc, hs, hxy⟩ := h j hj
  rw [hc]
  simp only
  have hcm : c ∈ Γ.comps := List.mem_of_getElem? hc
  have hne : c.x ≠ c.y := hN.2.1 c hcm hs
  unfold Graph.hasXdot
  rw [List.any_eq_true]
  by_cases hcx : c.x = x
  · have hzx : c.y ≠ x := fun h' => hne (hcx.trans h'.symm)
    obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hN.2.2 x c.y (Ne.symm hzx)).2 ⟨c, hcm, hs, Or.inl ⟨hcx, rfl⟩⟩
    refine ⟨c₂, hc₂, ?_⟩
    simp only [hcx, beq_self_eq_true, ite_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨by simpa using hk₂, ?_⟩
    rcases hm₂ with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨a1, a2⟩
    · exact Or.inr ⟨a1, a2⟩
  · have hcy : c.y = x := hxy.resolve_left hcx
    have hzx : c.x ≠ x := hcx
    obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hN.2.2 x c.x (Ne.symm hzx)).2 ⟨c, hcm, hs, Or.inr ⟨rfl, hcy⟩⟩
    refine ⟨c₂, hc₂, ?_⟩
    have : (c.x == x) = false := by simpa using hcx
    simp only [this, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨by simpa using hk₂, ?_⟩
    rcases hm₂ with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨a1, a2⟩
    · exact Or.inr ⟨a1, a2⟩

private theorem length_filterMap_of_some {α β : Type*} (f : α → Option β) (l : List α)
    (h : ∀ i ∈ l, ∃ c, f i = some c) : (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨c, hc⟩ := h a (List.mem_cons_self ..)
    simp [hc, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

private theorem deg_eq_sum {C : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) (x : Atom k n) :
    Γ.deg x = (Γ.edgeIdx x .plus true).length + (Γ.edgeIdx x .minus true).length +
      (Γ.edgeIdx x .plus false).length + (Γ.edgeIdx x .minus false).length := by
  have hperm := eraseIdxs_pick_perm (EO_oXIdx x Γ) Γ.comps
  have hnd := oXIdx_nodup x Γ
  have hpp := pickIdxs_perm (EO_oXIdx x Γ) hnd Γ.comps
  rw [deg_eq_countP, ← hperm.countP_eq, List.countP_append]
  have h0 : (eraseIdxs (EO_oXIdx x Γ) Γ.comps).countP
      (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = 0 := by
    rw [List.countP_eq_zero]
    intro c hc hcon
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcon
    obtain ⟨hs, hxy⟩ := hcon
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    obtain ⟨a, b⟩ := fL_untouched hN hc hch
    rcases hxy with h | h
    · exact a h
    · exact b h
  have hlen : (pickIdxs (EO_oXIdx x Γ) Γ.comps).length = (EO_oXIdx x Γ).length := by
    rw [hpp.length_eq]
    apply length_filterMap_of_some
    intro i hi
    obtain ⟨c, hc, -⟩ := mem_oXIdx.1 hi
    exact ⟨c, hc⟩
  have h1 : (pickIdxs (EO_oXIdx x Γ) Γ.comps).countP
      (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = (EO_oXIdx x Γ).length := by
    rw [← hlen, List.countP_eq_length]
    intro c hc
    obtain ⟨i, hi, hic⟩ := List.mem_filterMap.1 (hpp.subset hc)
    obtain ⟨c', hc', ch, hk, hxy⟩ := mem_oXIdx.1 hi
    have : c = c' := by
      rw [hc'] at hic
      exact (Option.some.inj hic).symm
    rw [this]
    rcases hxy with ⟨h1', -⟩ | ⟨h1', -⟩ <;> simp [hk, Kind.isSolid, h1']
  rw [h0, h1]
  simp only [EO_oXIdx, List.length_append]
  omega

end EdgeIdxConj

section Ends

variable {k n : ℕ}

private theorem matchedEnds_comm (e₁ e₂ : Bool ×
    Charge) : matchedEnds e₁ e₂ = matchedEnds e₂ e₁ := by
  rcases e₁ with ⟨a, ch⟩; rcases e₂ with ⟨b, ch'⟩
  cases a <;> cases b <;> cases ch <;> cases ch' <;> rfl

private theorem matchedEnds_flip (e₁ e₂ : Bool × Charge) :
    matchedEnds (e₁.1, e₁.2.flip) (e₂.1, e₂.2.flip) = matchedEnds e₁ e₂ := by
  rcases e₁ with ⟨a, ch⟩; rcases e₂ with ⟨b, ch'⟩
  cases a <;> cases b <;> cases ch <;> cases ch' <;> rfl

private theorem endFn_conj (x : Atom k n) (c : Comp (Atom k n)) :
    endFn x c.conj = (endFn x c).map (fun e => (e.1, e.2.flip)) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  unfold endFn Comp.conj
  cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;>
    by_cases h1 : a = x <;> by_cases h2 : b = x <;> simp [Kind.conj, Charge.flip, h1, h2]

private theorem ends_conj (Γ : Graph k n) (x : Atom k n) :
    Γ.conj.ends x = (Γ.ends x).map (fun e => (e.1, e.2.flip)) := by
  rw [ends_eq, ends_eq, Graph.conj_comps, List.filterMap_map]
  have : (endFn x ∘ Comp.conj) = fun c => (endFn x c).map (fun e => (e.1, e.2.flip)) := by
    funext c; exact endFn_conj x c
  rw [this]
  induction Γ.comps with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.filterMap_cons]
    cases hc : endFn x c <;> simp [ih]

private theorem conj_mismatchedAt (Γ : Graph k n) (x : Atom k n) :
    Γ.conj.mismatchedAt x = Γ.mismatchedAt x := by
  unfold Graph.mismatchedAt
  rw [Graph.conj_deg, ends_conj]
  rcases hE : Γ.ends x with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, rest⟩⟩⟩
  · simp
  · simp
  · simp [matchedEnds_flip]
  · simp

private theorem mismatched_false_of_pair {C : ℕ} {Γ : Graph k n} {x : Atom k n} (_hN : Γ.Normal C)
    (B : List (Comp (Atom k n))) (ea eb : Comp (Atom k n)) (hBR : (B ++ [ea, eb]).Perm Γ.comps)
    (a b : Bool × Charge) (hea : endFn x ea = some a) (heb : endFn x eb = some b)
    (hm : matchedEnds a b = true) (hdeg : Γ.deg x = 2) : Γ.mismatchedAt x = false := by
  have hB : ∀ c ∈ B, endFn x c = none := by
    intro c hc
    have hcnt : B.countP (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = 0 := by
      have h1 := deg_eq_countP Γ x
      rw [← hBR.countP_eq, List.countP_append] at h1
      have h2 : [ea, eb].countP (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = 2 := by
        have ha : ea.kind.isSolid = true ∧ (ea.x = x ∨ ea.y = x) := by
          unfold endFn at hea
          rcases hk : ea.kind with ch | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
            simp_all [Kind.isSolid]
          all_goals split_ifs at hea <;> simp_all
        have hb : eb.kind.isSolid = true ∧ (eb.x = x ∨ eb.y = x) := by
          unfold endFn at heb
          rcases hk : eb.kind with ch | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
            simp_all [Kind.isSolid]
          all_goals split_ifs at heb <;> simp_all
        simp [ha.1, hb.1, ha.2, hb.2]
      omega
    rw [List.countP_eq_zero] at hcnt
    have := hcnt c hc
    unfold endFn
    rcases hk : c.kind with ch | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
        <;> simp_all [Kind.isSolid]
  have hends : (Γ.ends x).Perm [a, b] := by
    rw [ends_eq]
    have := hBR.symm.filterMap (endFn x)
    rw [List.filterMap_append] at this
    have hB0 : B.filterMap (endFn x) = [] := List.filterMap_eq_nil_iff.2 hB
    simpa [hB0, hea, heb] using this
  unfold Graph.mismatchedAt
  rcases List.perm_pair.1 hends with h | h
  · rw [h]; simp [hdeg, hm]
  · rw [h]
    have hm' := hm
    rw [matchedEnds_comm] at hm'
    simp [hdeg, hm']

/-- The atom `x` has two matched solid edges, or more than two solid edges. -/
def BaseMatch (Γ : Graph k n) (x : Atom k n) : Prop :=
  2 ≤ Γ.deg x ∧ (Γ.deg x = 2 → Γ.mismatchedAt x = false)

private theorem BaseMatch.conj {Γ : Graph k n} {x : Atom k n} (h : BaseMatch Γ.conj x) :
    BaseMatch Γ x := by
  unfold BaseMatch at h ⊢
  rw [Graph.conj_deg, conj_mismatchedAt] at h
  exact h

private theorem endFn_out {x : Atom k n} {e : Comp (Atom k n)} {ch : Charge} (hk : e.kind = .G ch)
    (hx : e.x = x) (hy : e.y ≠ x) : endFn x e = some (true, ch) := by
  simp [endFn, hk, hx, hy]

private theorem endFn_in {x : Atom k n} {e : Comp (Atom k n)} {ch : Charge} (hk : e.kind = .G ch)
    (hy : e.y = x) (hx : e.x ≠ x) : endFn x e = some (false, ch) := by
  simp [endFn, hk, hx, hy]

private theorem baseMatch_of_pair {C : ℕ} {Γ : Graph k n} {x : Atom k n} (hN : Γ.Normal C)
    {i j : ℕ} {chi chj : Charge} {outi outj : Bool}
    (hi : i ∈ Γ.edgeIdx x chi outi) (hj : j ∈ Γ.edgeIdx x chj outj) (hij : i ≠ j)
    {ea eb : Comp (Atom k n)} (hea : Γ.comps[i]? = some ea) (heb : Γ.comps[j]? = some eb)
    (hm : matchedEnds (outi, chi) (outj, chj) = true) : BaseMatch Γ x := by
  have hperm := eraseIdxs_two_perm hij hea heb
  have hsum := deg_eq_sum hN x
  have p1 := List.length_pos_of_mem hi
  have p2 := List.length_pos_of_mem hj
  refine ⟨?_, fun hdeg => ?_⟩
  · by_cases hsame : chi = chj ∧ outi = outj
    · obtain ⟨rfl, rfl⟩ := hsame
      have : 2 ≤ (Γ.edgeIdx x chi outi).length := by
        have hnd := edgeIdx_nodup Γ x chi outi
        have : ({i, j} : Finset ℕ) ⊆ (Γ.edgeIdx x chi outi).toFinset := by
          intro m hm'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
          rcases hm' with rfl | rfl <;> simp [*]
        have h2 := Finset.card_le_card this
        rw [Finset.card_pair hij] at h2
        exact h2.trans (List.toFinset_card_le _)
      cases chi <;> cases outi <;> omega
    · cases chi <;> cases outi <;> cases chj <;> cases outj <;>
        first | omega | (exfalso; simp at hsame)
  · obtain ⟨c1, hc1, hk1, ho1⟩ := mem_edgeIdx.1 hi
    obtain ⟨c2, hc2, hk2, ho2⟩ := mem_edgeIdx.1 hj
    rw [hea] at hc1
    rw [heb] at hc2
    obtain rfl := Option.some.inj hc1
    obtain rfl := Option.some.inj hc2
    refine mismatched_false_of_pair hN _ ea eb hperm (outi, chi) (outj, chj) ?_ ?_ hm hdeg
    · cases outi
      · exact endFn_in hk1 ho1.1 ho1.2
      · exact endFn_out hk1 ho1.1 ho1.2
    · cases outj
      · exact endFn_in hk2 ho2.1 ho2.2
      · exact endFn_out hk2 ho2.1 ho2.2

end Ends

section Classify

variable {k n : ℕ}

/-- A term of an edge expansion before `O_dot`: the properties of the pre-dot graph, and either
a label, an order gain of one, or the main term of the multi-edge expansion. -/
private def Classify (C : ℕ) (Γ : Graph k n) (x : Atom k n) (T : Tracked k n) : Prop :=
  PreT C Γ.ord x T ∧ (¬ T.g.LabelFree ∨ (Γ.wt x = 0 → Γ.ord + 1 ≤ T.g.ord) ∨
    ∃ g : Graph k (n + 1), T = ⟨n + 1, g, liftA 1⟩ ∧ g.ord = Γ.ord ∧ Base2Data Γ x g ∧
      BaseMatch Γ x)

private theorem Classify.conj {C : ℕ} {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (h : Classify C Γ.conj x T) : Classify C Γ x ⟨T.nOut, T.g.conj, T.f⟩ := by
  obtain ⟨hP, hc⟩ := h
  refine ⟨?_, ?_⟩
  · have := hP.conj
    rwa [Graph.conj_ord] at this
  · rcases hc with hc | hc | ⟨g, rfl, hg, hD, hM⟩
    · left
      intro hlf
      exact hc ((Graph.conj_labelFree _).1 hlf)
    · right; left
      intro hw
      have := hc (by rw [Graph.conj_wt]; exact hw)
      rw [Graph.conj_ord] at this
      change Γ.ord + 1 ≤ T.g.conj.ord
      rw [Graph.conj_ord]; exact this
    · right; right
      refine ⟨g.conj, rfl, ?_, ?_, hM.conj⟩
      · rw [Graph.conj_ord] at hg ⊢
        simpa [Graph.conj_ord] using hg
      · exact hD.conj

private theorem classify_oOut {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtx C x Γ i₁ is₂ e₁) :
    ∀ t ∈ EO_oOut x Γ i₁ is₂ e₁, Classify C Γ x t := by
  intro t ht
  obtain ⟨hP, hc⟩ := oOut_spec Ctx t ht
  refine ⟨hP, ?_⟩
  rcases hc with hc | hc | ⟨j, d, ⟨hj, rfl⟩ | ⟨hj, rfl⟩⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · obtain ⟨hD, hord⟩ := base2_baseM Ctx hj d
    obtain ⟨ej, hej, -⟩ := mem_edgeIdx.1 hj
    have hi₁ : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
    have hne : i₁ ≠ j := fun h => edgeIdx_disjoint (Or.inl (by simp)) hi₁ (h ▸ hj)
    exact Or.inr (Or.inr ⟨_, rfl, hord, hD,
      baseMatch_of_pair Ctx.normal hi₁ hj hne Ctx.hL hej (by decide)⟩)
  · obtain ⟨hD, hord⟩ := base2_baseP Ctx hj d
    obtain ⟨ej, hej, -⟩ := mem_edgeIdx.1 hj
    have hi₁ : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
    have hne : i₁ ≠ j := fun h => edgeIdx_disjoint (Or.inr (by simp)) hi₁ (h ▸ hj)
    exact Or.inr (Or.inr ⟨_, rfl, hord, hD,
      baseMatch_of_pair Ctx.normal hi₁ hj hne Ctx.hL hej (by decide)⟩)

private theorem classify_iOut {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtx C x Γ i₁ is₂ e₁) :
    ∀ t ∈ EO_iOut x Γ i₁ is₂ e₁, Classify C Γ x t := by
  intro t ht
  obtain ⟨hP, hc⟩ := iOut_spec Ctx t ht
  refine ⟨hP, ?_⟩
  rcases hc with hc | hc | ⟨j, d, hj, rfl⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · obtain ⟨hD, hord⟩ := base2_iBaseM Ctx hj d
    obtain ⟨ej, hej, -⟩ := mem_edgeIdx.1 hj
    have hi₁ : i₁ ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hIP]; exact List.mem_cons_self ..
    have hne : i₁ ≠ j := fun h => edgeIdx_disjoint (Or.inl (by simp)) hi₁ (h ▸ hj)
    exact Or.inr (Or.inr ⟨_, rfl, hord, hD,
      baseMatch_of_pair Ctx.normal hi₁ hj hne Ctx.hL hej (by decide)⟩)

end Classify

section HatSpec

variable {k n : ℕ}

private theorem multiEOut_eq {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (EO_oXIdx x Γ) = true) :
    multiEOut x Γ = some (EO_oOut x Γ i₁ is₂ e₁) := by
  unfold multiEOut
  split
  · rename_i h
    rw [hOP] at h
    cases h
  · rename_i i₁' is₂' h
    rw [hOP] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    split
    · rename_i h2
      rw [hL] at h2
      cases h2
    · rename_i e₁' h2
      rw [hL] at h2
      obtain rfl := Option.some.inj h2
      dsimp only
      rw [ite_eq_right (by simpa [EO_oXIdx] using hX)]
      rfl

private theorem multiEIn_eq {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (EO_iXIdx x Γ) = true) :
    multiEIn x Γ = some (EO_iOut x Γ i₁ is₂ e₁) := by
  unfold multiEIn
  split
  · rename_i h
    rw [hIP] at h
    cases h
  · rename_i i₁' is₂' h
    rw [hIP] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    split
    · rename_i h2
      rw [hL] at h2
      cases h2
    · rename_i e₁' h2
      rw [hL] at h2
      obtain rfl := Option.some.inj h2
      dsimp only
      rw [ite_eq_right (by simpa [EO_iXIdx] using hX)]
      rfl

private theorem edge_of_idx {Γ : Graph k n} {x : Atom k n} {ch : Charge} {out : Bool} {i : ℕ}
    (h : i ∈ Γ.edgeIdx x ch out) : ∃ e, Γ.comps[i]? = some e := by
  obtain ⟨c, hc, -⟩ := mem_edgeIdx.1 h
  exact ⟨c, hc⟩

private theorem multiEHat_spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain) (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (hdeg : 1 ≤ Γ.deg x) :
    ∃ E, multiEHat x Γ = some E ∧ ∀ T ∈ E, Classify C Γ x T := by
  have hsum := deg_eq_sum hN x
  have hXout : ∀ Γ' : Graph k n, Γ'.Normal C → Γ'.xdotsAt x (EO_oXIdx x Γ') = true := by
    intro Γ' hN'
    refine xdotsAt_of_normal hN' x _ fun j hj => ?_
    obtain ⟨c, hc, ch, hk, hxy⟩ := mem_oXIdx.1 hj
    exact ⟨c, hc, by simp [hk, Kind.isSolid], by rcases hxy with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]⟩
  have hXin : ∀ Γ' : Graph k n, Γ'.Normal C → Γ'.xdotsAt x (EO_iXIdx x Γ') = true := by
    intro Γ' hN'
    refine xdotsAt_of_normal hN' x _ fun j hj => ?_
    obtain ⟨c, hc, ch, hk, hxy, -⟩ := mem_iXIdx.1 hj
    exact ⟨c, hc, by simp [hk, Kind.isSolid], Or.inr hxy⟩
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
        have Ctx := InCtx.conj_of hN hP hx hU hIP hL h1 h2
        have hX' : Γ.conj.xdotsAt x (EO_iXIdx x Γ.conj) = true := hXin _ (Graph.conj_Normal hN)
        have hIP' : Γ.conj.edgeIdx x .plus false = i₁ :: is₂ := by rw [edgeIdx_conj]; exact hIP
        have hL' : Γ.conj.comps[i₁]? = some e₁.conj := by simp [Graph.conj_comps, hL]
        refine ⟨(EO_iOut x Γ.conj i₁ is₂ e₁.conj).map (fun t => ⟨t.nOut, t.g.conj, t.f⟩), ?_, ?_⟩
        · simp [multiEHat, h1, h2, h3, h4, multiEIn_eq hIP' hL' hX', TExpansion.conj]
        · intro T hT
          obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
          exact (classify_iOut Ctx T₀ hT₀).conj
      · obtain ⟨i₁, is₂, hIP⟩ := List.exists_cons_of_ne_nil h3
        obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .plus) (out := false)
          (by rw [hIP]; exact List.mem_cons_self ..)
        have Ctx : InCtx C x Γ i₁ is₂ e₁ := ⟨hN, hP, hx, hU, hIP, hL, h1, h2⟩
        refine ⟨EO_iOut x Γ i₁ is₂ e₁, ?_, classify_iOut Ctx⟩
        simp [multiEHat, h1, h2, h3, multiEIn_eq hIP hL (hXin Γ hN)]
    · obtain ⟨i₁, is₂, hOP⟩ := List.exists_cons_of_ne_nil h2
      obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .minus) (out := true)
        (by rw [hOP]; exact List.mem_cons_self ..)
      have Ctx := OutCtx.conj_of hN hP hx hU hOP hL
      have hX' : Γ.conj.xdotsAt x (EO_oXIdx x Γ.conj) = true := hXout _ (Graph.conj_Normal hN)
      have hOP' : Γ.conj.edgeIdx x .plus true = i₁ :: is₂ := by rw [edgeIdx_conj]; exact hOP
      have hL' : Γ.conj.comps[i₁]? = some e₁.conj := by simp [Graph.conj_comps, hL]
      refine ⟨(EO_oOut x Γ.conj i₁ is₂ e₁.conj).map (fun t => ⟨t.nOut, t.g.conj, t.f⟩), ?_, ?_⟩
      · simp [multiEHat, h1, h2, multiEOut_eq hOP' hL' hX', TExpansion.conj]
      · intro T hT
        obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
        exact (classify_oOut Ctx T₀ hT₀).conj
  · obtain ⟨i₁, is₂, hOP⟩ := List.exists_cons_of_ne_nil h1
    obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .plus) (out := true)
      (by rw [hOP]; exact List.mem_cons_self ..)
    have Ctx : OutCtx C x Γ i₁ is₂ e₁ := ⟨hN, hP, hx, hU, hOP, hL⟩
    refine ⟨EO_oOut x Γ i₁ is₂ e₁, ?_, classify_oOut Ctx⟩
    simp [multiEHat, h1, multiEOut_eq hOP hL (hXout Γ hN)]

end HatSpec

section LfBack

variable {k N : ℕ}

private theorem mergeComp_label_some {m : ℕ} (rep : Atom k N → Atom k N) (f : Atom k N → Atom k m)
    {c : Comp (Atom k N)} (hnd : c.kind ≠ .dot) (hl : c.label.isSome = true) :
    ∃ c', mergeComp rep f c = some c' ∧ c'.label.isSome = true := by
  rcases c with ⟨κ, a, b, mi, l⟩
  unfold mergeComp
  have hκ : (κ == Kind.dot) = false := by simpa using hnd
  simp only [hκ, Bool.false_and, Bool.false_eq_true, ite_false]
  split_ifs
  · exact ⟨_, rfl, by simpa [Comp.map] using hl⟩
  · exact ⟨_, rfl, by simpa [Comp.map] using hl⟩

theorem oDotT_lf_back {g : Graph k N} (hP : g.Plain) {s : Tracked k N} (hs : s ∈ oDotT g)
    (hlf : s.g.LabelFree) : g.LabelFree := by
  intro c hc
  by_contra hl
  have hls : c.label.isSome = true := by simp [Option.isSome_iff_ne_none, hl]
  have hrand : c.kind.isRandom = true := (hP c hc).2.2.2.2.2 hls
  rcases mem_oDotT_cases' hs with rfl | ⟨A, -, hm⟩
  · exact hl (hlf c hc)
  · have hms := mergeT_spec hm
    have hnd : c.kind ≠ .dot := by intro h; rw [h] at hrand; simp [Kind.isRandom] at hrand
    have hnx : c.kind ≠ .xdot := by intro h; rw [h] at hrand; simp [Kind.isRandom] at hrand
    have hcm : c ∈ (g.dotChoice g.splitPairs A).comps := by
      have : (g.dotChoice g.splitPairs A).comps = keptComps g g.splitPairs ++
          addedComps g.splitPairs A := rfl
      rw [this]
      exact List.mem_append_left _ ((mem_keptComps g _ c).2 ⟨hc, fun h => hnx h.1⟩)
    obtain ⟨c', hc', hl'⟩ := mergeComp_label_some (rep := (g.dotChoice g.splitPairs A).mrep)
      (f := s.f) hnd hls
    have hmem : c' ∈ s.g.comps := hms.mem_comps.2 ⟨c, hcm, hc'⟩
    have := hlf c' hmem
    simp [this] at hl'

end LfBack

section MultiECore

variable {k n : ℕ}

private theorem all_isPlainB {Γ : Graph k n} (hlf : Γ.LabelFree) (hP : Γ.Plain) :
    Γ.comps.all Comp.isPlainB = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨h1, h2, h3, -⟩ := hP c hc
  have hl := hlf c hc
  unfold Comp.isPlainB
  rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, d⟩ | w | o | ⟨a, b⟩ | _ | ⟨a, b, c'⟩ | _ | _ <;>
    simp_all

theorem multiE_core {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hx : x.isRight = true) (hlf : Γ.LabelFree) (hwt : Γ.wt x = 0) (hdeg : 1 ≤ Γ.deg x) :
    ∀ t ∈ oMultiET x Γ, t.g.LabelFree →
      Γ.ord + 1 ≤ t.g.ord ∨
      (t.g.ord = Γ.ord ∧ BaseMatch Γ x ∧ t.g.deg (t.f x) + 2 = Γ.deg x ∧
        (((∃ u, t.IsNew u ∧ t.g.deg u = 2 ∧ ∀ v, t.IsNew v → v = u) ∧
            ∀ v, v ≠ x → t.g.deg (t.f v) = Γ.deg v) ∨
          ((∀ u, t.IsNew u → t.g.deg u = 0) ∧
            ∀ v, v ≠ x → t.g.deg (t.f v) = Γ.deg v ∨ t.g.deg (t.f v) + 2 = Γ.deg v))) := by
  obtain ⟨E, hE, hspec⟩ := multiEHat_spec hN hP hx hlf hdeg
  intro t ht htlf
  unfold oMultiET at ht
  rw [ite_eq_right (by simp [all_isPlainB hlf hP]), hE] at ht
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  obtain ⟨hPre, hc⟩ := hspec T hT
  have hge := dot_ord_ge hPre.dotOK hPre.sl hPre.unp s hs
  rcases hc with hc | hc | ⟨g, rfl, hg, hD, hM⟩
  · exact absurd (oDotT_lf_back hPre.plain hs htlf) hc
  · left
    have := hc hwt
    exact this.trans hge
  · have hle : g.ord ≤ s.g.ord := hge
    by_cases h1 : Γ.ord + 1 ≤ s.g.ord
    · exact Or.inl h1
    · right
      have heq : s.g.ord = Γ.ord := by omega
      refine ⟨heq, hM, ?_⟩
      rcases shape2 hD hs (by omega) with ⟨⟨u, hu, hdu, huniq⟩, hdx, hdo, -⟩ |
          ⟨y, hyx, hdx, hdy, hdo, hnew, -⟩
      · exact ⟨hdx, Or.inl ⟨⟨u, hu, hdu, huniq⟩, hdo⟩⟩
      · refine ⟨hdx, Or.inr ⟨hnew, fun v hv => ?_⟩⟩
        by_cases hvy : v = y
        · subst hvy; exact Or.inr hdy
        · exact Or.inl (hdo v hv hvy)

end MultiECore

section StdBase

variable {k n : ℕ}

end StdBase

section GGbarCore

variable {k n : ℕ}

end GGbarCore

section GGbarCases

variable {k n : ℕ}

private theorem idx_of_mem {α : Type*} {l : List α} {a : α} (h : a ∈ l) : ∃ i : ℕ, l[i]? = some a :=
  List.mem_iff_getElem?.1 h

end GGbarCases

section GGClassify

variable {k n : ℕ}

private theorem main0_gg {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtx C x Γ i j e e') (hxy : e'.x = e.y) (d : Coeff)
    (hP : PreT C Γ.ord x
      ⟨n, ⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩, id⟩) :
    Main0Data Γ.deg x e.y ⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩ ∧
      Γ.GGShapeAt x e.y := by
  obtain ⟨he_k, he_x, he_y⟩ := Ctx.espec
  obtain ⟨he'_k, he'_y, he'_x⟩ := Ctx.e'spec
  have hg : (⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩ : Graph k n).comps =
      EO_ggF Γ i j ++ [mkC (.weight .plus) e.y e.y, mkC (.waved .plus) x e.y] := by
    simp [EO_ggMain, hxy, solidC]
  have hΓ : ∀ v, Γ.deg v = (EO_ggF Γ i j).countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) +
      [e, e'].countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) := by
    intro v
    rw [deg_eq_countP, ← Ctx.perm.countP_eq, List.countP_append]
  have hg' : ∀ v, (⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩ : Graph k n).deg v =
      (EO_ggF Γ i j).countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) := by
    intro v
    rw [deg_eq_countP, hg, List.countP_append]
    simp [mkC, Kind.isSolid]
  have hx0 : (EO_ggF Γ i j).countP (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = 0 := by
    rw [List.countP_eq_zero]
    intro c hc
    cases hs : c.kind with
    | G ch =>
      have := Ctx.f_untouched hc hs
      simp [Kind.isSolid, this.1, this.2]
    | _ => simp [Kind.isSolid]
  have hxne : e.y ≠ x := he_y
  have hdeg : Γ.deg x = 2 := by
    rw [hΓ x, hx0]
    simp [he_k, he'_k, Kind.isSolid, he_x, he'_y]
  have hpart : ∀ c ∈ (⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩ : Graph k n).comps,
      c.kind.isSolid = true → c ∈ EO_ggF Γ i j := by
    intro c hc hs
    rw [hg] at hc
    rcases List.mem_append.1 hc with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [mkC, Kind.isSolid] at hs
  refine ⟨⟨hP.dotOK, hP.sl, ?_, ?_, ?_, ?_⟩, hdeg, .plus, ⟨e, Ctx.emem, he_k, he_x, rfl⟩,
    ⟨e', Ctx.e'mem, he'_k, hxy, he'_y⟩⟩
  · -- no unpartnered solid edge
    unfold unpartL
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    by_cases hs : c.kind.isSolid = true
    · have hcF := hpart c hc hs
      have hcΓ : c ∈ Γ.comps := mem_eraseIdxs_of_mem hcF
      have hold : ∀ c ∈ Γ.comps, c.kind.isRandom = false →
          c.map (id : Atom k n → Atom k n) ∈
            (⟨EO_ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], d⟩ : Graph k n).comps := by
        intro c hc hr
        have hcF : c ∈ EO_ggF Γ i j ++ [e, e'] := Ctx.perm.symm.subset hc
        rw [hg]
        rcases List.mem_append.1 hcF with h | h
        · refine List.mem_append_left _ ?_
          simpa [Comp.map] using h
        · exfalso
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp_all [Kind.isRandom]
      have := partnered_old' (φ := (id : Atom k n → Atom k n)) Ctx.normal hold
        ⟨c, hcΓ, rfl, rfl, rfl⟩ hs
      simp [hs, this]
    · simp [Bool.eq_false_iff.2 hs]
  · rw [hg' x]; exact hx0
  · rw [hg' e.y, hΓ e.y]
    have : [e, e'].countP (fun c => c.kind.isSolid && (c.x == e.y || c.y == e.y)) = 2 := by
      simp [he_k, he'_k, Kind.isSolid, hxy, he'_y]
    omega
  · intro v hvx hvy
    rw [hg' v, hΓ v]
    have : [e, e'].countP (fun c => c.kind.isSolid && (c.x == v || c.y == v)) = 0 := by
      simp [he_k, he'_k, Kind.isSolid, hxy, he_x, he'_y, Ne.symm hvx, Ne.symm hvy]
    omega

end GGClassify

section GGClassify2

variable {k n : ℕ}

set_option linter.flexible false in
private theorem kind_of_conj_G {κ : Kind} {ch : Charge} (h : κ.conj = .G ch) : κ = .G ch.flip := by
  cases κ <;> (try cases ‹Wave›) <;> cases ch <;> simp_all [Kind.conj, Charge.flip] <;>
    (try cases ‹Charge›) <;> simp_all

private theorem GGShapeAt.of_conj {Γ : Graph k n} {x y : Atom k n} (h : Γ.conj.GGShapeAt x y) :
    Γ.GGShapeAt x y := by
  obtain ⟨hd, ch, ⟨c, hc, hk, hx, hy⟩, ⟨c', hc', hk', hx', hy'⟩⟩ := h
  obtain ⟨c0, hc0, rfl⟩ := Graph.mem_conj_comps.1 hc
  obtain ⟨c0', hc0', rfl⟩ := Graph.mem_conj_comps.1 hc'
  rw [Graph.conj_deg] at hd
  exact ⟨hd, ch.flip, ⟨c0, hc0, kind_of_conj_G hk, hx, hy⟩,
    ⟨c0', hc0', kind_of_conj_G hk', hx', hy'⟩⟩

/-- A term of the `GG` expansion before `O_dot`: the properties of the pre-dot graph, and either
a label, an order gain of one, or the main term with the pair of solid edges removed. -/
private def ClassifyGG (C : ℕ) (Γ : Graph k n) (x : Atom k n) (T : Tracked k n) : Prop :=
  PreT C Γ.ord x T ∧ (¬ T.g.LabelFree ∨ (Γ.wt x = 0 → Γ.ord + 1 ≤ T.g.ord) ∨
    ∃ (g : Graph k n) (y : Atom k n), T = ⟨n, g, id⟩ ∧ g.ord = Γ.ord ∧
      Main0Data Γ.deg x y g ∧ Γ.GGShapeAt x y)

private theorem ClassifyGG.conj {C : ℕ} {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (h : ClassifyGG C Γ.conj x T) : ClassifyGG C Γ x ⟨T.nOut, T.g.conj, T.f⟩ := by
  obtain ⟨hP, hc⟩ := h
  refine ⟨?_, ?_⟩
  · have := hP.conj
    rwa [Graph.conj_ord] at this
  · rcases hc with hc | hc | ⟨g, y, rfl, hg, hD, hS⟩
    · left
      intro hlf
      exact hc ((Graph.conj_labelFree _).1 hlf)
    · right; left
      intro hw
      have := hc (by rw [Graph.conj_wt]; exact hw)
      rw [Graph.conj_ord] at this
      change Γ.ord + 1 ≤ T.g.conj.ord
      rw [Graph.conj_ord]; exact this
    · right; right
      refine ⟨g.conj, y, rfl, ?_, ?_, GGShapeAt.of_conj hS⟩
      · rw [Graph.conj_ord] at hg ⊢
        simpa [Graph.conj_ord] using hg
      · rw [Graph.conj_deg] at hD
        exact hD.conj

private theorem classify_ggOut {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom
    k n)}
    (Ctx : GGCtx C x Γ i j e e') : ∀ t ∈ EO_ggOut x Γ i j e e', ClassifyGG C Γ x t := by
  intro t ht
  obtain ⟨hP, hc⟩ := ggOut_spec Ctx t ht
  refine ⟨hP, ?_⟩
  rcases hc with hc | hc | ⟨hxy, d, rfl⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · refine Or.inr (Or.inr ⟨_, e.y, rfl, ?_, main0_gg Ctx hxy d hP⟩)
    have h := (preT_gg_main Ctx none d).2.1
    simp only [labW] at h
    rw [ord_solidC, ite_eq_left hxy] at h
    simpa using h

end GGClassify2

section GGLemma

variable {k n : ℕ}

private theorem gg_input {C : ℕ} {Γ : Graph k n} {x y y' : Atom k n} (hN : Γ.Normal C)
    (h : Γ.GGInputAt x y y') :
    ∃ ch : Charge, ∃ i j : ℕ, ∃ e e' : Comp (Atom k n),
      Γ.edgeIdx x ch true = [i] ∧ Γ.edgeIdx x ch false = [j] ∧
      Γ.edgeIdx x ch.flip true = [] ∧ Γ.edgeIdx x ch.flip false = [] ∧
      Γ.comps[i]? = some e ∧ Γ.comps[j]? = some e' := by
  obtain ⟨hdeg, ch, ⟨c, hc, hk, hxc, hyc⟩, ⟨c', hc', hk', hxc', hyc'⟩⟩ := h
  have hsum : ∀ ch : Charge, Γ.deg x = (Γ.edgeIdx x ch true).length +
      (Γ.edgeIdx x ch.flip true).length + (Γ.edgeIdx x ch false).length +
      (Γ.edgeIdx x ch.flip false).length := by
    intro ch
    have := deg_eq_sum hN x
    cases ch <;> simp only [Charge.flip] <;> omega
  obtain ⟨ip, hip⟩ := idx_of_mem hc
  obtain ⟨jp, hjp⟩ := idx_of_mem hc'
  have hs1 := hN.2.1 c hc (by simp [hk, Kind.isSolid])
  have hs2 := hN.2.1 c' hc' (by simp [hk', Kind.isSolid])
  have hmp : ip ∈ Γ.edgeIdx x ch true :=
    mem_edgeIdx.2 ⟨c, hip, hk, hxc, fun h => hs1 (hxc.trans h.symm)⟩
  have hmm : jp ∈ Γ.edgeIdx x ch false :=
    mem_edgeIdx.2 ⟨c', hjp, hk', hyc', fun h => hs2 (h.trans hyc'.symm)⟩
  have p1 := List.length_pos_of_mem hmp
  have p2 := List.length_pos_of_mem hmm
  have hs := hsum ch
  have l1 : (Γ.edgeIdx x ch true).length = 1 := by omega
  have l2 : (Γ.edgeIdx x ch false).length = 1 := by omega
  have l3 : (Γ.edgeIdx x ch.flip true).length = 0 := by omega
  have l4 : (Γ.edgeIdx x ch.flip false).length = 0 := by omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 l1
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 l2
  have hia : ip = a := by rw [ha] at hmp; simpa using hmp
  have hib : jp = b := by rw [hb] at hmm; simpa using hmm
  exact ⟨ch, a, b, c, c', ha, hb, List.length_eq_zero_iff.1 l3, List.length_eq_zero_iff.1 l4,
    by rw [← hia]; exact hip, by rw [← hib]; exact hjp⟩

private theorem ggPos_eq {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (hdeg : Γ.deg x = 2) (hPO : Γ.edgeIdx x .plus true = [i])
    (hPI : Γ.edgeIdx x .plus false = [j]) (hi : Γ.comps[i]? = some e)
    (hj : Γ.comps[j]? = some e') (hX : Γ.xdotsAt x [i, j] = true) :
    ggPos x Γ = some (EO_ggOut x Γ i j e e') := by
  unfold ggPos
  rw [ite_eq_right (by simp [hdeg]), hPO, hPI]
  simp only [hi, hj]
  rw [ite_eq_right (by simp [hX])]
  rfl

private theorem gg_core_of {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hwt : Γ.wt x = 0)
    {E : TExpansion k n} (hE : ∀ T ∈ E, ClassifyGG C Γ x T) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), t.g.LabelFree →
      Γ.ord + 1 ≤ t.g.ord ∨ ∃ y, Γ.GGShapeAt x y ∧ t.PairRemoved Γ x y := by
  intro t ht htlf
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  obtain ⟨hPre, hc⟩ := hE T hT
  have hge := dot_ord_ge hPre.dotOK hPre.sl hPre.unp s hs
  rcases hc with hc | hc | ⟨g, y, rfl, hg, hD, hS⟩
  · exact absurd (oDotT_lf_back hPre.plain hs htlf) hc
  · left
    exact (hc hwt).trans hge
  · have hle : g.ord ≤ s.g.ord := hge
    by_cases h1 : Γ.ord + 1 ≤ s.g.ord
    · exact Or.inl h1
    · right
      have heq : s.g.ord = Γ.ord := by omega
      obtain ⟨h0, h1', h2, h3⟩ := shape0 hD hs (by omega)
      exact ⟨y, hS, heq, h0, h1', h2, h3⟩

end GGLemma

section Canon

variable {k n : ℕ}

private theorem PreT.regular {C : ℕ} {o : ℤ} {x : Atom k n} {T : Tracked k n} (h : PreT C o x T) :
    T.g.Regular (C + 8) :=
  ⟨h.size, fun u v => reach_map (G := T.g.edgeGraphNoX) (H := T.g.edgeGraph) id
    (fun _ _ hab => (edgeGraphNoX_le_edgeGraph T.g hab).reachable) (h.conn u v), h.int,
    h.noIntDot⟩

private theorem all_label_none {Γ : Graph k n} (h : Γ.comps.all Comp.isPlainB = true) :
    ∀ c ∈ Γ.comps, c.label = none := by
  intro c hc
  have := List.all_eq_true.1 h c hc
  simp only [Comp.isPlainB, Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1.2

private theorem canon_bind {C : ℕ} {x : Atom k n} {Γ : Graph k n} {E : TExpansion k n}
    (hE : ∀ T ∈ E, PreT C Γ.ord x T) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), t.g.Normal (2 * C + 16) ∧ t.g.Plain ∧ Γ.ord ≤ t.g.ord ∧
      ∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f x) u := by
  intro t ht
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  have hP := hE T hT
  refine ⟨?_, oDotT_plain hP.plain s hs, hP.ord.trans (dot_ord_ge hP.dotOK hP.sl hP.unp s hs),
    NR_dot hP.new hs⟩
  have := (oDot_normal k T.nOut (C + 8) T.g hP.regular hP.conn hP.lab.1 hP.lab.2 s hs).1
  have h2 : 2 * (C + 8) = 2 * C + 16 := by omega
  rwa [h2] at this

private theorem canon_self {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain) :
    ∀ t ∈ [Tracked.self Γ], t.g.Normal (2 * C + 16) ∧ t.g.Plain ∧ Γ.ord ≤ t.g.ord ∧
      ∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f x) u := by
  intro t ht
  rw [List.mem_singleton] at ht
  subst ht
  exact ⟨hN.mono (by omega), hP, le_rfl, fun u hu => absurd rfl (hu u)⟩

private theorem multiEHat_none_of_deg {x : Atom k n} {Γ : Graph k n} {C : ℕ} (hN : Γ.Normal C)
    (h : Γ.deg x = 0) : multiEHat x Γ = none := by
  have hsum := deg_eq_sum hN x
  have h1 : Γ.edgeIdx x .plus true = [] := List.length_eq_zero_iff.1 (by omega)
  have h2 : Γ.edgeIdx x .minus true = [] := List.length_eq_zero_iff.1 (by omega)
  have h3 : Γ.edgeIdx x .plus false = [] := List.length_eq_zero_iff.1 (by omega)
  have h4 : Γ.edgeIdx x .minus false = [] := List.length_eq_zero_iff.1 (by omega)
  simp [multiEHat, h1, h2, h3, h4]

end Canon

section Canon2

variable {k n : ℕ}

private theorem ggPos_deg {x : Atom k n} {Γ : Graph k n} {E : TExpansion k n}
    (h : ggPos x Γ = some E) : Γ.deg x = 2 := by
  unfold ggPos at h
  by_contra hne
  rw [ite_eq_left (by simpa using hne)] at h
  exact absurd h (by simp)

private theorem ggCtx_of {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true) (hU : ∀ c ∈ Γ.comps, c.label = none)
    (hdeg : Γ.deg x = 2) (hO : Γ.edgeIdx x .plus true = [i]) (hI : Γ.edgeIdx x .plus false = [j])
    (hi : Γ.comps[i]? = some e) (hj : Γ.comps[j]? = some e') : GGCtx C x Γ i j e e' := by
  have hsum := deg_eq_sum hN x
  rw [hO, hI] at hsum
  have h1 : Γ.edgeIdx x .minus true = [] := List.length_eq_zero_iff.1 (by simp at hsum; omega)
  have h2 : Γ.edgeIdx x .minus false = [] := List.length_eq_zero_iff.1 (by simp at hsum; omega)
  exact ⟨hN, hP, hx, hU, hO, hI, h1, h2, hi, hj⟩

private theorem conj_label_none {Γ : Graph k n} (hU : ∀ c ∈ Γ.comps, c.label = none) :
    ∀ c ∈ Γ.conj.comps, c.label = none := by
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
  simpa using hU c hc

end Canon2

/-! ## Statements -/

/-- [I, Def 3.8 (ii)–(iv)] for `O^{(x)}_multi-e` with `C' = 2C + 16`: at an internal atom `x` of a
plain normal regular graph, every output graph is plain and normal regular with bound `2C + 16`,
has scaling order at least that of the input, and every new atom is joined to the image of `x` by
a path of waved edges. -/
theorem oMultiE_canonical :
    CanonicalAt @oMultiET fun C => 2 * C + 16 := by
  intro k n C x Γ hx hN hP t ht
  unfold oMultiET at ht
  by_cases hpl : (Γ.comps.all Comp.isPlainB) = true
  · rw [ite_eq_right (by simp [hpl])] at ht
    have hU : ∀ c ∈ Γ.comps, c.label = none := all_label_none hpl
    rcases hm : multiEHat x Γ with _ | E
    · rw [hm] at ht
      exact canon_self (x := x) hN hP t ht
    · rw [hm] at ht
      have hd : 1 ≤ Γ.deg x := by
        by_contra hd
        have := multiEHat_none_of_deg (x := x) hN (by omega)
        rw [hm] at this
        exact absurd this (by simp)
      obtain ⟨E', hE', hspec⟩ := multiEHat_spec hN hP hx hU hd
      rw [hm] at hE'
      obtain rfl := Option.some.inj hE'
      exact canon_bind (fun T hT => (hspec T hT).1) t ht
  · rw [ite_eq_left (by simpa using hpl)] at ht
    exact canon_self (x := x) hN hP t ht

/-- [I, Def 3.8 (ii)–(iv)] for `O^{(x)}_GG` with `C' = 2C + 16`: at an internal atom `x` of a plain
normal regular graph, every output graph is plain and normal regular with bound `2C + 16`, has
scaling order at least that of the input, and every new atom is joined to the image of `x` by a
path of waved edges. -/
theorem oGG_canonical :
    CanonicalAt @oGGT fun C => 2 * C + 16 := by
  intro k n C x Γ hx hN hP t ht
  unfold oGGT at ht
  by_cases hpl : (Γ.comps.all Comp.isPlainB) = true
  · rw [ite_eq_right (by simp [hpl])] at ht
    have hU : ∀ c ∈ Γ.comps, c.label = none := all_label_none hpl
    rcases hm : ggPos x Γ with _ | E
    · rw [hm] at ht
      simp only at ht
      rcases hm' : ggPos x Γ.conj with _ | E'
      · rw [hm'] at ht
        exact canon_self (x := x) hN hP t ht
      · rw [hm'] at ht
        obtain ⟨i, j, e, e', hO, hI, hi, hj, -, hEq⟩ := ggPos_some' x _ hm'
        subst hEq
        have Ctx := ggCtx_of (Graph.conj_Normal hN) (Graph.conj_Plain hP) hx (conj_label_none hU)
          (ggPos_deg hm') hO hI hi hj
        refine canon_bind (fun T' hT' => ?_) t ht
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
        have := (classify_ggOut Ctx T hT).1.conj
        rwa [Graph.conj_ord] at this
    · rw [hm] at ht
      obtain ⟨i, j, e, e', hO, hI, hi, hj, -, hEq⟩ := ggPos_some' x _ hm
      subst hEq
      have Ctx := ggCtx_of hN hP hx hU (ggPos_deg hm) hO hI hi hj
      exact canon_bind (fun T hT => (classify_ggOut Ctx T hT).1) t ht
  · rw [ite_eq_left (by simpa using hpl)] at ht
    exact canon_self (x := x) hN hP t ht

/-- [I, Def 3.8 (ii)–(iv)] for `O^{(x)}_GḠ` with `C' = 2C + 16`: at an internal atom `x` of a plain
normal regular graph, every output graph is plain and normal regular with bound `2C + 16`, has
scaling order at least that of the input, and every new atom is joined to the image of `x` by a
path of waved edges. -/
theorem oGGbar_canonical :
    CanonicalAt @oGGbarT fun C => 2 * C + 16 := by
  intro k n C x Γ hx hN hP t ht
  unfold oGGbarT at ht
  dsimp only at ht
  split_ifs at ht
  · exact oMultiE_canonical k n C x Γ hx hN hP t ht
  · exact canon_self (x := x) hN hP t ht

/-- [I, Lemma 3.16]: for a plain label-free normal graph without weight on the internal atom `x`
whose solid edges at `x` are `G_{xy} G_{y'x}` or `Ḡ_{xy} Ḡ_{y'x}`, every label-free output graph of
`O^{(x)}_GG` has larger scaling order or is obtained by removing the two solid edges between `x`
and some `y` (case (b)). -/
theorem ggLemma (k n C : ℕ) (x y y' : Atom k n) (Γ : Graph k n) :
    x.isRight = true → Γ.Normal C → Γ.LabelFree → Γ.Plain →
    Γ.wt x = 0 → Γ.GGInputAt x y y' → ∀ t ∈ oGGT x Γ, t.g.LabelFree →
      Γ.ord + 1 ≤ t.g.ord ∨ ∃ y, Γ.GGShapeAt x y ∧ t.PairRemoved Γ x y := by
  intro hx hN hlf hP hwt hin
  have hdeg := hin.1
  have hU : ∀ c ∈ Γ.comps, c.label = none := fun c hc => hlf c hc
  obtain ⟨ch, i, j, e, e', hO, hI, hO', hI', hi, hj⟩ := gg_input hN hin
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB hlf hP]
  cases ch
  · -- charge `plus`
    simp only [Charge.flip] at hO' hI'
    have Ctx : GGCtx C x Γ i j e e' := ⟨hN, hP, hx, hU, hO, hI, hO', hI', hi, hj⟩
    have hX : Γ.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal hN x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e, hi, by simp [Ctx.espec.1, Kind.isSolid], Or.inl Ctx.espec.2.1⟩
      · exact ⟨e', hj, by simp [Ctx.e'spec.1, Kind.isSolid], Or.inr Ctx.e'spec.2.1⟩
    have hE : oGGT x Γ = (EO_ggOut x Γ i j e e').bind (fun _ g => oDotT g) := by
      unfold oGGT
      rw [ite_eq_right (by simp [hpl]), ggPos_eq hdeg hO hI hi hj hX]
    rw [hE]
    exact gg_core_of hwt (classify_ggOut Ctx)
  · -- charge `minus`: the complex conjugate
    simp only [Charge.flip] at hO' hI'
    have hi' : Γ.conj.comps[i]? = some e.conj := by simp [Graph.conj_comps, hi]
    have hj' : Γ.conj.comps[j]? = some e'.conj := by simp [Graph.conj_comps, hj]
    have hO2 : Γ.conj.edgeIdx x .plus true = [i] := by rw [edgeIdx_conj]; exact hO
    have hI2 : Γ.conj.edgeIdx x .plus false = [j] := by rw [edgeIdx_conj]; exact hI
    have hM1 : Γ.conj.edgeIdx x .minus true = [] := by rw [edgeIdx_conj]; exact hO'
    have hM2 : Γ.conj.edgeIdx x .minus false = [] := by rw [edgeIdx_conj]; exact hI'
    have hU' : ∀ c ∈ Γ.conj.comps, c.label = none := by
      intro c' hc'
      obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
      simpa using hU c hc
    have Ctx : GGCtx C x Γ.conj i j e.conj e'.conj :=
      ⟨Graph.conj_Normal hN, Graph.conj_Plain hP, hx, hU', hO2, hI2, hM1, hM2, hi', hj'⟩
    have hX : Γ.conj.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal (Graph.conj_Normal hN) x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e.conj, hi', by rw [Ctx.espec.1]; rfl, Or.inl Ctx.espec.2.1⟩
      · exact ⟨e'.conj, hj', by rw [Ctx.e'spec.1]; rfl, Or.inr Ctx.e'spec.2.1⟩
    have hdeg' : Γ.conj.deg x = 2 := by rw [Graph.conj_deg]; exact hdeg
    have hnone : ggPos x Γ = none := by
      unfold ggPos
      rw [ite_eq_right (by simp [hdeg])]
      have : Γ.edgeIdx x .plus true = [] := hO'
      rw [this]
    have hE : oGGT x Γ = (EO_ggOut x Γ.conj i j e.conj e'.conj).conj.bind (fun _ g => oDotT g) := by
      unfold oGGT
      rw [ite_eq_right (by simp [hpl]), hnone]
      simp only
      rw [ggPos_eq hdeg' hO2 hI2 hi' hj' hX]
    rw [hE]
    refine gg_core_of (C := C) hwt ?_
    intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
    exact (classify_ggOut Ctx T hT).conj

end RBM8D.Graphs
