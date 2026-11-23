module

public import RBM8D.Graph.Local.IBP
public import RBM8D.Graph.Local.Dot

@[expose] public section

/-!
# The weight expansion

`O_weight` ([I, Lemma 3.5, Def 3.6] = [II, Def 4.3]) and [I, Lemma 3.9].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The expansion `G_{xx} = m + (G_{xx} - m)`, `Ḡ_{xx} = m̄ + (Ḡ_{xx} - m̄)` of every unlabelled
regular weight on `x` in the list `cs`: the resulting component lists with their coefficient
factors. A labelled weight is left unsplit. -/
def splitRegular {V : Type*} [DecidableEq V] (x : V) : List (Comp V) → List (List (Comp V) × Coeff)
  | [] => [([], 1)]
  | c :: cs =>
    let r := splitRegular x cs
    match c.kind with
    | .weight ch =>
      if c.x = x ∧ c.label.isNone = true then
        r.map (fun p => (p.1, mOf ch * p.2)) ++
          r.map (fun p => ({ c with kind := .light ch } :: p.1, p.2))
      else r.map fun p => (c :: p.1, p.2)
    | _ => r.map fun p => (c :: p.1, p.2)

/-- The operator `O^{(x),1}_weight` of [I, Def 3.6 (i)]: every unlabelled regular weight on `x`
is written as `m` plus a light weight. -/
def oWeight1T {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  (splitRegular x Γ.comps).map fun p => ⟨n, ⟨p.1, p.2 * Γ.coeff⟩, id⟩

/-- The light weight expansion [I, (3.5)] of `Γ = (G_{xx} - m) f(G)`, for the first light weight
`G_{xx} - m` of positive charge on `x` (`none` if there is none). The new atoms are `α` (and
`β`); the terms are, in order: `m ∑_α s_{xα} (G_{xx} - m)(G_{αα} - m) f`,
`m ∑_{α,β} S⁺_{xα} s_{αβ} (G_{αα} - m)(G_{ββ} - m) f`, `-m ∑_α s_{xα} G_{αx} ∂_{h_{αx}} f`,
`-m ∑_{α,β} S⁺_{xα} s_{αβ} G_{βα} ∂_{h_{βα}} f`, and the six families of `Q`-graphs of `𝒬_w`. -/
def oWeight2Pos {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Option (TExpansion k n) :=
  match Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
  | none => none
  | some i =>
    let c := Γ.coeff
    let f := Γ.comps.eraseIdx i
    let x₁ : Atom k (n + 1) := liftA 1 x
    let x₂ : Atom k (n + 2) := liftA 2 x
    let a₁ : Atom k (n + 1) := newA 0
    let a₂ : Atom k (n + 2) := newA 0
    let b₂ : Atom k (n + 2) := newA 1
    let F₁ := liftCs 1 f
    let F₂ := liftCs 2 f
    let t₁ (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
      ⟨n + 1, ⟨cs, d⟩, liftA 1⟩
    let t₂ (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) : Tracked k n :=
      ⟨n + 2, ⟨cs, d⟩, liftA 2⟩
    some <|
      [t₁ (liftCs 1 Γ.comps ++ [mkC (.waved .s) x₁ a₁, mkC (.light .plus) a₁ a₁]) (cm * c),
        t₂ (F₂ ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂, mkC (.light .plus) a₂ a₂,
          mkC (.light .plus) b₂ b₂]) (cm * c)] ++
      (dTerms a₁ x₁ F₁).map (fun d =>
        t₁ (d ++ [mkC (.waved .s) x₁ a₁, mkC (.G .plus) a₁ x₁]) (cm * c)) ++
      (dTerms b₂ a₂ F₂).map (fun d =>
        t₂ (d ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂, mkC (.G .plus) b₂ a₂])
          (cm * c)) ++
      [⟨n, ⟨labelQs x Γ.comps, c⟩, id⟩,
        t₁ (labelQs a₁ (F₁ ++ [mkC (.light .plus) a₁ a₁]) ++ [mkC (.waved .plus) x₁ a₁]) c,
        t₁ (labelQs x₁ (F₁ ++ [mkC (.light .plus) a₁ a₁, mkC (.weight .plus) x₁ x₁]) ++
          [mkC (.waved .s) x₁ a₁]) (-cm * c),
        t₂ (labelQs a₂ (F₂ ++ [mkC (.light .plus) b₂ b₂, mkC (.weight .plus) a₂ a₂]) ++
          [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂]) (-cm * c)] ++
      (dTerms a₁ x₁ F₁).map (fun d =>
        t₁ (labelQs x₁ (d ++ [mkC (.G .plus) a₁ x₁]) ++ [mkC (.waved .s) x₁ a₁]) (-cm * c)) ++
      (dTerms b₂ a₂ F₂).map (fun d =>
        t₂ (labelQs a₂ (d ++ [mkC (.G .plus) b₂ a₂]) ++
          [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂]) (-cm * c))

/-- The operator `O^{(x),2}_weight` of [I, Def 3.6 (ii)]: [I, (3.5)] on the first positive light
weight on `x`; otherwise [I, (3.6)] (complex conjugation) on the first negative one. It is the
identity on graphs with a `P`/`Q` label, a `G^{(T)}` entry or a `(G_{xx})⁻¹` or `W_D` weight. -/
def oWeight2T {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if !(Γ.comps.all Comp.isPlainB) then [Tracked.self Γ] else
  match oWeight2Pos x Γ with
  | some E => E
  | none =>
    match oWeight2Pos x Γ.conj with
    | some E => E.conj
    | none => [Tracked.self Γ]

/-- The weight expansion `O^{(x)}_weight = O^{(x),1}_weight ∘ O_dot ∘ O^{(x),2}_weight ∘
O^{(x),1}_weight` of [I, (3.7)], tracked; the identity if there is no weight or light weight
on `x`. -/
def oWeightT {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if Γ.comps.any (fun c => (c.kind matches .weight _ | .light _) && c.x == x) then
    (((oWeight1T x Γ).bind fun f g => oWeight2T (f x) g).bind fun _ g => oDotT g).bind
      fun f g => oWeight1T (f x) g
  else [Tracked.self Γ]

/-- The weight expansion `O^{(x)}_weight` ([I, Def 3.6] = [II, Def 4.3]). -/
def oWeight {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Expansion k := (oWeightT x Γ).forget

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
private def SamePair (c c₂ : Comp (Atom k n)) : Prop :=
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
private def DotOK (g : Graph k n) : Prop :=
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
private def partnered (g : Graph k n) (c : Comp (Atom k n)) : Bool :=
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

/-- Weights and light weights. -/
private def Kind.isWL : Kind → Bool
  | .weight _ => true
  | .light _ => true
  | _ => false

/-- Regular weights. -/
private def Kind.isReg : Kind → Bool
  | .weight _ => true
  | _ => false

/-- The sum of the scaling orders of a list of components. -/
private def ordL (cs : List (Comp V)) : ℤ := (cs.map fun c => c.kind.ord).sum

/-- The number of weights and light weights on `u`. -/
private def wtL [DecidableEq V] (u : V) (cs : List (Comp V)) : ℕ :=
  (cs.filter fun c => c.kind.isWL && decide (c.x = u)).length

/-- A component that is a regular weight without label on `x`. -/
private def isRegAt [DecidableEq V] (x : V) (c : Comp V) : Bool :=
  c.kind.isReg && decide (c.x = x) && c.label.isNone

/-- The number of regular weights without label on `x`. -/
private def regL [DecidableEq V] (x : V) (cs : List (Comp V)) : ℕ := (cs.filter (isRegAt x)).length

@[simp] private theorem ordL_nil : ordL ([] : List (Comp V)) = 0 := rfl

@[simp] private theorem ordL_cons (c : Comp V) (cs : List (Comp V)) :
    ordL (c :: cs) = c.kind.ord + ordL cs := by simp [ordL]

@[simp] private theorem ordL_append (cs cs' : List (Comp V)) :
    ordL (cs ++ cs') = ordL cs + ordL cs' := by simp [ordL]

private theorem Graph.ord_eq {k n : ℕ} (Γ : Graph k n) : Γ.ord = ordL Γ.comps - 2 * n := rfl

private theorem wtL_cons [DecidableEq V] (u : V) (c : Comp V) (cs : List (Comp V)) :
    wtL u (c :: cs) =
      (if c.kind.isWL && decide (c.x = u) then 1 else 0) +
      wtL u cs := by
  unfold wtL
  by_cases h : (c.kind.isWL && decide (c.x = u)) = true
  · simp [h]; omega
  · simp [h]

private theorem regL_cons [DecidableEq V] (x : V) (c : Comp V) (cs : List (Comp V)) :
    regL x (c :: cs) = (if isRegAt x c then 1 else 0) + regL x cs := by
  unfold regL
  by_cases h : isRegAt x c = true
  · simp [h]; omega
  · simp [h]

end Lists

/-! ## The first and last weight expansion `O^{(x),1}_weight` -/

section SplitSpec

variable {V : Type*} [DecidableEq V]

/-- A component that is a regular weight without label on `x`, as a proposition. -/
private theorem isRegAt_iff (x : V) (c : Comp V) :
    isRegAt x c = true ↔ (∃ ch, c.kind = .weight ch) ∧ c.x = x ∧ c.label = none := by
  unfold isRegAt
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp [Option.isNone_iff_eq_none, Kind.isReg]

set_option linter.flexible false in
private theorem splitRegular_nonreg (x : V) (c : Comp V) (cs : List (Comp V))
    (h : isRegAt x c = false) :
    splitRegular x (c :: cs) = (splitRegular x cs).map fun p => (c :: p.1, p.2) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp [isRegAt, Kind.isReg] at h <;> simp [splitRegular]
  case weight ch =>
    by_cases ha : a = x
    · have hl : l ≠ none := fun hl => by simp [ha, hl] at h
      simp [ha, hl]
    · simp [ha]

private theorem splitRegular_reg (x : V) (c : Comp V) (cs : List (Comp V)) (h : isRegAt x c = true)
    {ch : Charge} (hk : c.kind = .weight ch) :
    splitRegular x (c :: cs) =
      (splitRegular x cs).map (fun p => (p.1, mOf ch * p.2)) ++
        (splitRegular x cs).map fun p => ({ c with kind := .light ch } :: p.1, p.2) := by
  obtain ⟨-, hx, hl⟩ := (isRegAt_iff x c).1 h
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at hk hx hl
  subst hk hx hl
  simp [splitRegular]

/-- The structure of the output lists of `splitRegular`: `l` weights become light weights, `d`
weights are removed, the other components are unchanged. -/
private theorem splitRegular_spec (x : V) (cs : List (Comp V)) :
    ∀ p ∈ splitRegular x cs, ∃ l d : ℕ, l + d = regL x cs ∧ ordL p.1 = ordL cs + l ∧
      wtL x p.1 + d = wtL x cs ∧ (∀ u, u ≠ x → wtL u p.1 = wtL u cs) ∧ regL x p.1 = 0 ∧
      (∀ c' ∈ p.1, c' ∈ cs ∨ ∃ c ∈ cs, ∃ ch, isRegAt x c = true ∧ c.kind = .weight ch ∧
        c' = { c with kind := .light ch }) ∧
      (∀ c ∈ cs, isRegAt x c = false → c ∈ p.1) ∧ p.1.length ≤ cs.length := by
  induction cs with
  | nil =>
    intro p hp
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨0, 0, rfl, by simp, by simp, fun _ _ => rfl, rfl, by simp, by simp, by simp⟩
  | cons c cs ih =>
    intro p hp
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hk⟩, hx, hl⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hk] at hp
      rcases List.mem_append.1 hp with hp | hp
      · -- the weight is removed
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨l, d, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih q hq
        refine ⟨l, d + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [regL_cons, ite_eq_left hr]; omega
        · simp only [ordL_cons, h2, hk, Kind.ord]; ring
        · rw [wtL_cons, hk, hx]; simp only [h3.symm]; simp [Kind.isWL]; omega
        · intro u hu
          rw [wtL_cons, h4 u hu, hk]
          simp [hx, Ne.symm hu, Kind.isWL]
        · rw [h5]
        · intro c' hc'
          rcases h6 c' hc' with h | ⟨c₀, hc₀, ch₀, h⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr ⟨c₀, List.mem_cons_of_mem _ hc₀, ch₀, h⟩
        · intro c' hc' hc'r
          rcases List.mem_cons.1 hc' with rfl | hc'
          · rw [hr] at hc'r; exact absurd hc'r (by simp)
          · exact h7 c' hc' hc'r
        · simp only [List.length_cons]; omega
      · -- the weight becomes a light weight
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨l, d, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih q hq
        refine ⟨l + 1, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [regL_cons, ite_eq_left hr]; omega
        · simp only [ordL_cons, h2, hk, Kind.ord]; push_cast; ring
        · rw [wtL_cons, wtL_cons, hk, hx]; simp only [← h3]; simp [Kind.isWL]; omega
        · intro u hu
          rw [wtL_cons, wtL_cons, h4 u hu, hk]
          try simp [hx, Ne.symm hu, Kind.isWL]
        · rw [regL_cons, h5, ite_eq_right]
          simp [isRegAt, Kind.isReg]
        · intro c' hc'
          rcases List.mem_cons.1 hc' with rfl | hc'
          · exact Or.inr ⟨c, List.mem_cons_self .., ch, hr, hk, rfl⟩
          · rcases h6 c' hc' with h | ⟨c₀, hc₀, ch₀, h⟩
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr ⟨c₀, List.mem_cons_of_mem _ hc₀, ch₀, h⟩
        · intro c' hc' hc'r
          rcases List.mem_cons.1 hc' with rfl | hc'
          · rw [hr] at hc'r; exact absurd hc'r (by simp)
          · exact List.mem_cons_of_mem _ (h7 c' hc' hc'r)
        · simp only [List.length_cons]; omega
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr'] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨l, d, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih q hq
      refine ⟨l, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [regL_cons, hr']; simpa using h1
      · simp only [ordL_cons, h2]; ring
      · rw [wtL_cons, wtL_cons]; simp only [← h3]; omega
      · intro u hu
        rw [wtL_cons, wtL_cons, h4 u hu]
      · rw [regL_cons, hr', h5]; simp
      · intro c' hc'
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inl (List.mem_cons_self ..)
        · rcases h6 c' hc' with h | ⟨c₀, hc₀, ch₀, h⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr ⟨c₀, List.mem_cons_of_mem _ hc₀, ch₀, h⟩
      · intro c' hc' hc'r
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (h7 c' hc' hc'r)
      · simp only [List.length_cons]; omega

end SplitSpec

/-! ## The order of `O_dot`: the solid edges inside a block -/

section OC

variable {k n : ℕ}

/-- The solid edges without a `×`-dotted partner. -/
private def unpartL (g : Graph k n) : List (Comp (Atom k n)) :=
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
    (hU : (unpartL g).length ≤ 3)
    (hU3 : (unpartL g).length = 3 → ∃ c₁ ∈ unpartL g, ∃ c₂ ∈ unpartL g, ¬ SamePair c₁ c₂)
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
      by_cases h3 : e = 3
      · have hU3' : (unpartL g).length = 3 := by omega
        have hEq : convS g (g.dotChoice g.splitPairs A) = unpartL g :=
          hsub.eq_of_length (by omega)
        obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := hU3 hU3'
        rw [← hEq] at hc₁ hc₂
        have := two_pairs hsl hm hc₁ hc₂ hne
        omega
      · omega
  · intro h0
    by_contra hne
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    have := Kr_pos hm (hA.subset hp) hp
    omega

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

private theorem ordL_eraseIdx (l : List (Comp V)) (j : ℕ) (hj : j < l.length) :
    ordL (l.eraseIdx j) + (l[j]'hj).kind.ord = ordL l := by
  induction l generalizing j with
  | nil => simp at hj
  | cons c l ih =>
    cases j with
    | zero => simp [ordL_cons]; ring
    | succ j =>
      simp only [List.eraseIdx_cons_succ, ordL_cons, List.getElem_cons_succ]
      have := ih j (by simpa using hj)
      linarith

private theorem length_eraseIdx_lt (l : List (Comp V)) (j : ℕ) (hj : j < l.length) :
    (l.eraseIdx j).length + 1 = l.length := by
  rw [List.length_eraseIdx, ite_eq_left hj]
  omega

private theorem mem_eraseIdx_or {l : List (Comp V)} {j : ℕ} {c : Comp V} (hc : c ∈ l) :
    c ∈ l.eraseIdx j ∨ l[j]? = some c := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  by_cases hmj : m = j
  · subst hmj
    right
    simp
  · left
    exact List.mem_eraseIdx_iff_getElem.2 ⟨m, hm, hmj, rfl⟩

private theorem mem_eraseIdx_of_ne {l : List (Comp V)} {j : ℕ} {c : Comp V} (hc : c ∈ l)
    (hne : l[j]? ≠ some c) : c ∈ l.eraseIdx j := by
  rcases mem_eraseIdx_or (j := j) hc with h | h
  · exact h
  · exact absurd h hne

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

private theorem dTerm_length {p q : V} {cs : List (Comp V)} {d : List (Comp V)}
    (h : d ∈ dTerms p q cs) : d.length = cs.length + 1 := by
  obtain ⟨j, hj, ps, hps, rfl⟩ := mem_dTerms.1 h
  rw [List.length_append, dPieces_length hps]
  have := length_eraseIdx_lt cs j hj
  omega

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

private theorem reach_of_comp (g : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ g.comps) :
    g.edgeGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨c, hc, rfl, rfl⟩⟩ |>.reachable

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

/-- A component that the weight expansion may add: a solid edge, a weight, a light weight or a
waved edge, without minor; a weight sits on its atom, a solid edge joins two distinct atoms, only
random components are labelled. -/
private def NewOK {V : Type*} (c : Comp V) : Prop :=
  c.minor = [] ∧
  ((∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) ∨
    ∃ w, c.kind = .waved w) ∧
  (c.kind.isWeight = true → c.y = c.x) ∧ (c.kind.isSolid = true → c.x ≠ c.y) ∧
  (c.label.isSome = true → c.kind.isRandom = true)

/-- `g'` extends `g₁` along an injective map `φ` of the atoms: the non-random components of `g₁`
are kept, every component of `g'` comes from `g₁` or is new, every edge of `g₁` between distinct
atoms is replaced by a path (not using `×`-dotted edges), and every atom outside the image of `φ`
is joined to the image of `x` by waved edges. -/
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

/-! ## The components added by the weight expansion, and the graphs extending a graph -/

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

/-! ## The graphs of the weight expansion extend the input graph -/

section ExtLemmas

variable {k n : ℕ}

private theorem isWeight_random {κ : Kind} (h : κ.isWeight = true) : κ.isRandom = true := by
  cases κ <;> simp_all [Kind.isWeight, Kind.isRandom]

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

private theorem extA {C j : ℕ} {g₁ : Graph k n} {x : Atom k n} (hN : g₁.Normal C) (hP : g₁.Plain)
    (o : Option (Atom k (n + j))) (B : List (Comp (Atom k n)))
    (N₁ N₂ : List (Comp (Atom k (n + j)))) (d : Coeff)
    (hB1 : ∀ c ∈ B, c ∈ g₁.comps) (hB2 : ∀ c ∈ g₁.comps, c ∉ B → c.kind.isWeight = true)
    (hN₁ : ∀ c' ∈ N₁, NewOK c') (hN₂ : ∀ c' ∈ N₂, NewOK c')
    (hatt : ∀ i : Fin j,
      (⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ : Graph k (n + j)).wavedGraph.Reachable
        (liftA j x) (newA i)) :
    ExtData (liftA j) g₁ x ⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ := by
  set g' : Graph k (n + j) := ⟨labW o (liftCs j B ++ N₁) ++ N₂, d⟩ with hg'
  have hcomps : g'.comps = labW o (liftCs j B ++ N₁) ++ N₂ := rfl
  have hold : ∀ c ∈ g₁.comps, c.kind.isRandom = false → c.map (liftA j) ∈ g'.comps := by
    intro c hc hr
    have hcB : c ∈ B := by
      by_contra h
      have := hB2 c hc h
      rw [isWeight_random this] at hr
      simp at hr
    rw [hcomps]
    apply List.mem_append_left
    apply labW_nonrandom
    · exact List.mem_append_left _ (mem_liftCs.2 ⟨c, hcB, rfl⟩)
    · simpa [Comp.map] using hr
  refine ⟨hold, ?_, ?_, attach_of_new hatt⟩
  · -- every component comes from the input graph or is new
    intro c' hc'
    rw [hcomps, List.mem_append] at hc'
    rcases hc' with hc' | hc'
    · obtain ⟨c₁, hc₁, h⟩ := labW_cases hc'
      rcases List.mem_append.1 hc₁ with hc₁ | hc₁
      · obtain ⟨c, hcB, rfl⟩ := mem_liftCs.1 hc₁
        have hcg := hB1 c hcB
        by_cases hr : c.kind.isRandom = true
        · right
          have := NewOK_map_of_old (liftA_injective j) hN hP hcg hr
          rcases h with rfl | ⟨u, rfl⟩
          · exact this
          · exact this.labelQ u
        · left
          have hr' : (c.map (liftA j)).kind.isRandom = false := by simpa [Comp.map] using hr
          rcases h with rfl | ⟨u, rfl⟩
          · exact ⟨c, hcg, rfl⟩
          · refine ⟨c, hcg, ?_⟩
            unfold Comp.labelQ
            simp [hr']
      · right
        rcases h with rfl | ⟨u, rfl⟩
        · exact hN₁ _ hc₁
        · exact (hN₁ _ hc₁).labelQ u
    · right
      exact hN₂ _ hc'
  · -- every edge is kept
    intro c hc hk hne
    by_cases hr : c.kind.isRandom = true
    · have hcB : c ∈ B := by
        by_contra h
        have hw := hB2 c hc h
        exact hne ((hP c hc).2.2.2.2.1 hw).symm
      obtain ⟨c'', hc'', h1, h2, h3⟩ := labW_exists (o := o) (L := liftCs j B ++ N₁)
        (List.mem_append_left _ (mem_liftCs.2 ⟨c, hcB, rfl⟩))
      have := reach_of_comp_noX g' (c := c'') (by rw [hcomps]; exact List.mem_append_left _ hc'')
        (by rw [h3]; simpa [Comp.map] using hk)
      simpa [h1, h2, Comp.map] using this
    · have hr' : c.kind.isRandom = false := by simpa using hr
      have := reach_of_comp_noX g' (hold c hc hr') (by simpa [Comp.map] using hk)
      simpa [Comp.map] using this

private theorem extB {C j : ℕ} {g₁ : Graph k n} {x : Atom k n} (hN : g₁.Normal C) (hP : g₁.Plain)
    (o : Option (Atom k (n + j))) (f : List (Comp (Atom k n)))
    (p q : Atom k (n + j)) (d : List (Comp (Atom k (n + j))))
    (N₁ N₂ : List (Comp (Atom k (n + j)))) (e : Coeff)
    (hf1 : ∀ c ∈ f, c ∈ g₁.comps) (hf2 : ∀ c ∈ g₁.comps, c ∉ f → c.kind.isWeight = true)
    (hd : d ∈ dTerms p q (liftCs j f))
    (hN₁ : ∀ c' ∈ N₁, NewOK c') (hN₂ : ∀ c' ∈ N₂, NewOK c')
    (hE : mkC (.G .plus) p q ∈ N₁ ++ N₂)
    (hatt : ∀ i : Fin j, (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j)).wavedGraph.Reachable
      (liftA j x) (newA i)) :
    ExtData (liftA j) g₁ x ⟨labW o (d ++ N₁) ++ N₂, e⟩ := by
  set g' : Graph k (n + j) := ⟨labW o (d ++ N₁) ++ N₂, e⟩ with hg'
  have hcomps : g'.comps = labW o (d ++ N₁) ++ N₂ := rfl
  obtain ⟨jj, hjj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hjj' : jj < (liftCs j f).length := hjj
  have hFj : (liftCs j f)[jj] ∈ liftCs j f := List.getElem_mem hjj
  have hrandom := dPieces_random hps
  have hFjr : ((liftCs j f)[jj]).kind.isRandom = true := by
    rcases hrandom with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [h, Kind.isRandom]
  have hpsOK := dPieces_newOK hps
  -- the components of the derivative term
  have hdmem : ∀ c₁ ∈ (liftCs j f).eraseIdx jj ++ ps, c₁ ∈ g'.comps → True := fun _ _ _ => trivial
  have hold : ∀ c ∈ g₁.comps, c.kind.isRandom = false → c.map (liftA j) ∈ g'.comps := by
    intro c hc hr
    have hcf : c ∈ f := by
      by_contra h
      have := hf2 c hc h
      rw [isWeight_random this] at hr
      simp at hr
    have hmF : c.map (liftA j) ∈ liftCs j f := mem_liftCs.2 ⟨c, hcf, rfl⟩
    have hne : (liftCs j f)[jj]? ≠ some (c.map (liftA j)) := by
      intro h
      have := List.getElem?_eq_some_iff.1 h
      obtain ⟨hh, h2⟩ := this
      rw [h2] at hFjr
      simp [Comp.map, hr] at hFjr
    have hmd : c.map (liftA j) ∈ (liftCs j f).eraseIdx jj := mem_eraseIdx_of_ne hmF hne
    rw [hcomps]
    apply List.mem_append_left
    apply labW_nonrandom
    · exact List.mem_append_left _ (List.mem_append_left _ hmd)
    · simpa [Comp.map] using hr
  refine ⟨hold, ?_, ?_, attach_of_new hatt⟩
  · intro c' hc'
    rw [hcomps, List.mem_append] at hc'
    rcases hc' with hc' | hc'
    · obtain ⟨c₁, hc₁, h⟩ := labW_cases hc'
      rcases List.mem_append.1 hc₁ with hc₁ | hc₁
      · rcases List.mem_append.1 hc₁ with hc₁ | hc₁
        · obtain ⟨c, hcf, rfl⟩ := mem_liftCs.1 (List.mem_of_mem_eraseIdx hc₁)
          have hcg := hf1 c hcf
          by_cases hr : c.kind.isRandom = true
          · right
            have := NewOK_map_of_old (liftA_injective j) hN hP hcg hr
            rcases h with rfl | ⟨u, rfl⟩
            · exact this
            · exact this.labelQ u
          · left
            have hr' : (c.map (liftA j)).kind.isRandom = false := by simpa [Comp.map] using hr
            rcases h with rfl | ⟨u, rfl⟩
            · exact ⟨c, hcg, rfl⟩
            · refine ⟨c, hcg, ?_⟩
              unfold Comp.labelQ
              simp [hr']
        · right
          rcases h with rfl | ⟨u, rfl⟩
          · exact hpsOK _ hc₁
          · exact (hpsOK _ hc₁).labelQ u
      · right
        rcases h with rfl | ⟨u, rfl⟩
        · exact hN₁ _ hc₁
        · exact (hN₁ _ hc₁).labelQ u
    · right
      exact hN₂ _ hc'
  · -- every edge is kept
    have hin : ∀ c₁ ∈ (liftCs j f).eraseIdx jj ++ ps ++ N₁, c₁.kind ≠ .xdot →
        g'.edgeGraphNoX.Reachable c₁.x c₁.y := by
      intro c₁ hc₁ hk₁
      obtain ⟨c'', hc'', h1, h2, h3⟩ := labW_exists (o := o) hc₁
      have := reach_of_comp_noX g' (c := c'')
        (by rw [hcomps]; exact List.mem_append_left _ hc'') (by rwa [h3])
      rwa [h1, h2] at this
    intro c hc hk hne
    by_cases hr : c.kind.isRandom = true
    · -- `c` is a solid edge
      have hcf : c ∈ f := by
        by_contra h
        have hw := hf2 c hc h
        exact hne ((hP c hc).2.2.2.2.1 hw).symm
      have hmF : c.map (liftA j) ∈ liftCs j f := mem_liftCs.2 ⟨c, hcf, rfl⟩
      have hGch : ∃ ch, c.kind = .G ch := by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP c hc
        rcases c with ⟨κ, a, b, mi, l⟩
        cases κ <;> simp_all [Kind.isRandom, Kind.isWeight]
      have hk' : (c.map (liftA j)).kind ≠ .xdot := by simpa [Comp.map] using hk
      rcases mem_eraseIdx_or (j := jj) hmF with hmd | hmj
      · have := hin _ (List.mem_append_left _ (List.mem_append_left _ hmd)) hk'
        simpa [Comp.map] using this
      · have hFj' : (liftCs j f)[jj] = c.map (liftA j) := by
          have := List.getElem?_eq_some_iff.1 hmj
          exact this.2
        rw [hFj'] at hps
        have hE' : g'.edgeGraphNoX.Reachable p q := by
          rcases List.mem_append.1 hE with h | h
          · have := hin _ (List.mem_append_right _ h) (by simp [mkC])
            simpa [mkC] using this
          · have := reach_of_comp_noX g' (c := mkC (.G .plus) p q)
              (by rw [hcomps]; exact List.mem_append_right _ h) (by simp [mkC])
            simpa [mkC] using this
        have := dPieces_path (G := g'.edgeGraphNoX) hps (by simpa [Comp.map] using hGch)
          (fun c' hc' => by
            have hk'' : c'.kind ≠ .xdot := by
              rcases hpsOK c' hc' with ⟨-, hkinds, -⟩
              rcases hkinds with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨w, h⟩ <;> rw [h] <;> simp
            exact hin c' (List.mem_append_left _ (List.mem_append_right _ hc')) hk'') hE'
        simpa [Comp.map] using this
    · have hr' : c.kind.isRandom = false := by simpa using hr
      have := reach_of_comp_noX g' (hold c hc hr') (by simpa [Comp.map] using hk)
      simpa [Comp.map] using this

end ExtLemmas

/-! ## The terms of the light weight expansion -/

section Terms

variable {k n : ℕ}

/-- The components of `Γ` without the one at index `i`. -/
private def w2f (Γ : Graph k n) (i : ℕ) : List (Comp (Atom k n)) := Γ.comps.eraseIdx i

/-- Term 1. -/
private def w2t1 (x : Atom k n) (Γ : Graph k n) : Tracked k n :=
  ⟨n + 1, ⟨liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
    mkC (.light .plus) (newA 0) (newA 0)], cm * Γ.coeff⟩, liftA 1⟩

/-- Term 2. -/
private def w2t2 (x : Atom k n) (Γ : Graph k n) (i : ℕ) : Tracked k n :=
  ⟨n + 2, ⟨liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
    mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
    mkC (.light .plus) (newA 1) (newA 1)], cm * Γ.coeff⟩, liftA 2⟩

/-- Term 3, for a term `d` of the derivative. -/
private def w2t3 (x : Atom k n) (Γ : Graph k n) (d : List (Comp (Atom k (n + 1)))) : Tracked k n :=
  ⟨n + 1, ⟨d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)],
    cm * Γ.coeff⟩, liftA 1⟩

/-- Term 4, for a term `d` of the derivative. -/
private def w2t4 (x : Atom k n) (Γ : Graph k n) (d : List (Comp (Atom k (n + 2)))) : Tracked k n :=
  ⟨n + 2, ⟨d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
    mkC (.G .plus) (newA 1) (newA 0)], cm * Γ.coeff⟩, liftA 2⟩

/-- Term 5. -/
private def w2t5 (x : Atom k n) (Γ : Graph k n) : Tracked k n :=
  ⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩

/-- Term 6. -/
private def w2t6 (x : Atom k n) (Γ : Graph k n) (i : ℕ) : Tracked k n :=
  ⟨n + 1, ⟨labelQs (newA 0) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
    [mkC (.waved .plus) (liftA 1 x) (newA 0)], Γ.coeff⟩, liftA 1⟩

/-- Term 7. -/
private def w2t7 (x : Atom k n) (Γ : Graph k n) (i : ℕ) : Tracked k n :=
  ⟨n + 1, ⟨labelQs (liftA 1 x) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0),
    mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
    -cm * Γ.coeff⟩, liftA 1⟩

/-- Term 8. -/
private def w2t8 (x : Atom k n) (Γ : Graph k n) (i : ℕ) : Tracked k n :=
  ⟨n + 2, ⟨labelQs (newA 0) (liftCs 2 (w2f Γ i) ++ [mkC (.light .plus) (newA 1) (newA 1),
    mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
    mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩, liftA 2⟩

/-- Term 9, for a term `d` of the derivative. -/
private def w2t9 (x : Atom k n) (Γ : Graph k n) (d : List (Comp (Atom k (n + 1)))) : Tracked k n :=
  ⟨n + 1, ⟨labelQs (liftA 1 x) (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
    [mkC (.waved .s) (liftA 1 x) (newA 0)], -cm * Γ.coeff⟩, liftA 1⟩

/-- Term 10, for a term `d` of the derivative. -/
private def w2t10 (x : Atom k n) (Γ : Graph k n) (d : List (Comp (Atom k (n + 2)))) : Tracked k n :=
  ⟨n + 2, ⟨labelQs (newA 0) (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
    -cm * Γ.coeff⟩, liftA 2⟩

/-- The terms of `oWeight2Pos`, as a list. -/
private def w2E (x : Atom k n) (Γ : Graph k n) (i : ℕ) : TExpansion k n :=
  [w2t1 x Γ, w2t2 x Γ i] ++
    (dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))).map (w2t3 x Γ) ++
    (dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))).map (w2t4 x Γ) ++
    [w2t5 x Γ, w2t6 x Γ i, w2t7 x Γ i, w2t8 x Γ i] ++
    (dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))).map (w2t9 x Γ) ++
    (dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))).map (w2t10 x Γ)

private theorem oWeight2Pos_eq {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    (h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = some i) :
    oWeight2Pos x Γ = some (w2E x Γ i) := by
  unfold oWeight2Pos
  rw [h]
  rfl

private theorem oWeight2Pos_none_iff {x : Atom k n} {Γ : Graph k n} :
    oWeight2Pos x Γ = none ↔
      Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
  unfold oWeight2Pos
  cases h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) <;> simp

end Terms

/-! ## Solid edges without `×`-dotted partner in the graphs of the weight expansion -/

section Unpart

variable {k n : ℕ}

/-- The number of solid edges of the list `L` without `×`-dotted partner in `g`. -/
private def unpartCount (g : Graph k n) (L : List (Comp (Atom k n))) : ℕ :=
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

/-! ## What `O_dot` needs from the output of the light weight expansion -/

section Out2

variable {k n : ℕ}

/-- The properties of a graph produced from `g₁` by the light weight expansion, to which
`O_dot` is applied and to bound the order afterwards. -/
private structure Out2B (C : ℕ) (g₁ : Graph k n) (x : Atom k n) (t : Tracked k n) : Prop where
  size : k + t.nOut + t.g.comps.length ≤ C + 5
  conn : t.g.ConnNoX
  int : ∀ a b : Fin t.nOut, t.g.wavedThetaGraph.Reachable (.inr a) (.inr b)
  noIntDot : ∀ c ∈ t.g.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true
  dotOK : DotOK t.g
  sl : ∀ c ∈ t.g.comps, c.kind.isSolid = true → c.x ≠ c.y
  unp : (unpartL t.g).length ≤ 3 ∧ ((unpartL t.g).length = 3 →
    ∃ c₁ ∈ unpartL t.g, ∃ c₂ ∈ unpartL t.g, ¬ SamePair c₁ c₂)
  plain : t.g.Plain
  lab : t.g.labels.length ≤ 1 ∧ ∀ c ∈ t.g.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none
  ord : g₁.ord ≤ t.g.ord
  new : ∀ u, (∀ v, t.f v ≠ u) → t.g.wavedGraph.Reachable (t.f x) u

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

/-! ## The first positive light weight -/

section Setup

variable {k n : ℕ}

private theorem w2_setup {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    (h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = some i) :
    ∃ hi : i < Γ.comps.length, (Γ.comps[i]).kind = .light .plus ∧ (Γ.comps[i]).x = x := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  refine ⟨hi, ?_⟩
  simpa using hp

private theorem w2f_sub {Γ : Graph k n} {i : ℕ} : ∀ c ∈ w2f Γ i, c ∈ Γ.comps := fun _ h =>
  List.mem_of_mem_eraseIdx h

private theorem w2f_cover {Γ : Graph k n} {i : ℕ} (hi : i < Γ.comps.length)
    (hk : (Γ.comps[i]).kind = .light .plus) :
    ∀ c ∈ Γ.comps, c ∉ w2f Γ i → c.kind.isWeight = true := by
  intro c hc hn
  rcases mem_eraseIdx_or (j := i) hc with h | h
  · exact absurd h hn
  · have := (List.getElem?_eq_some_iff.1 h).2
    rw [← this, hk]
    rfl

private theorem w2f_length {Γ : Graph k n} {i : ℕ} (hi : i < Γ.comps.length) :
    (w2f Γ i).length + 1 = Γ.comps.length := length_eraseIdx_lt _ _ hi

private theorem w2f_ord {Γ : Graph k n} {i : ℕ} (hi : i < Γ.comps.length)
    (hk : (Γ.comps[i]).kind = .light .plus) : ordL (w2f Γ i) + 1 = ordL Γ.comps := by
  have := ordL_eraseIdx Γ.comps i hi
  rw [hk] at this
  unfold w2f
  simpa [Kind.ord] using this

end Setup

/-! ## The outputs of the light weight expansion: assembly -/

section Assembly

variable {k n : ℕ}

private theorem out2B_mk {C : ℕ} {g₁ : Graph k n} {x : Atom k n} {t : Tracked k n}
    (hN : g₁.Normal C) (hP : g₁.Plain) (hx : x.isRight = true)
    (hU : ∀ c ∈ g₁.comps, c.label = none)
    (hinj : Function.Injective t.f) (hL : ∀ v, (t.f v).isLeft = v.isLeft)
    (E : ExtData t.f g₁ x t.g)
    (hsize : k + t.nOut + t.g.comps.length ≤ C + 5)
    (hunp : (unpartL t.g).length ≤ 3 ∧ ((unpartL t.g).length = 3 →
      ∃ c₁ ∈ unpartL t.g, ∃ c₂ ∈ unpartL t.g, ¬ SamePair c₁ c₂))
    (hlab : t.g.labels.length ≤ 1)
    (hord : g₁.ord ≤ t.g.ord) : Out2B C g₁ x t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ExtData.props hinj hL hN hP hx E
  exact ⟨hsize, h1, h2, h3, h4, h5, hunp, h6, ⟨hlab, unlabelled_dots E hU⟩, hord, E.attach⟩

private theorem label_none_lift {j : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.label = none) :
    ∀ c ∈ liftCs j cs, c.label = none := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := mem_liftCs.1 hc
  simp [Comp.map, h c₀ hc₀]

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

private theorem label_dTerms {V : Type*} [DecidableEq V] {p q : V} {F d : List (Comp V)}
    (h : ∀ c ∈ F, c.label = none) (hd : d ∈ dTerms p q F) : ∀ c ∈ d, c.label = none := by
  obtain ⟨j, hj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact h c (List.mem_of_mem_eraseIdx hc)
  · exact dPieces_label hps c hc

end Assembly

/-! ## The terms of the light weight expansion satisfy `Out2B` -/

section Terms2

variable {k n : ℕ}

/-- The hypotheses on the input of the light weight expansion. -/
private structure W2Ctx (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i : ℕ) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  lt : i < Γ.comps.length
  kind : (Γ.comps[i]).kind = .light .plus
  atx : (Γ.comps[i]).x = x

private theorem unpart_zero_of_old {C m : ℕ} {φ : Atom k n → Atom k m} {g₁ : Graph k n}
    {x : Atom k n}
    {g' : Graph k m} (hN : g₁.Normal C) (E : ExtData φ g₁ x g')
    (h : ∀ c' ∈ g'.comps, c'.kind.isSolid = true →
      ∃ c ∈ g₁.comps, c'.x = φ c.x ∧ c'.y = φ c.y ∧ c'.kind = c.kind) :
    (unpartL g').length = 0 := by
  rw [unpartL_length]
  exact unpartCount_eq_zero g' fun c' hc' hs => partnered_old hN E (h c' hc' hs) hs

private theorem out2B_t1 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    Out2B C Γ x (w2t1 x Γ) := by
  unfold w2t1
  have E : ExtData (liftA 1) Γ x
      (⟨liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.light .plus) (newA 0) (newA 0)], cm * Γ.coeff⟩ : Graph k (n + 1)) := by
    have := extA (j := 1) W.normal W.plain none Γ.comps
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)] []
      (cm * Γ.coeff) (fun c hc => hc) (fun c hc hn => absurd hc hn)
      (by
        intro c' hc'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl
        · exact NewOK_waved _ _ _
        · exact NewOK_light _ _)
      (by simp)
      (by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        refine reach_of_waved _ (c := mkC (.waved .s) (liftA 1 x) (newA 0)) ?_ ⟨.s, rfl⟩
        simp [labW])
    simpa [labW] using this
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 1) (liftA_isLeft 1) E ?_ ?_ ?_ ?_
  · have := W.normal.1.size
    simp [liftCs_length] at this ⊢
    omega
  · have h0 := unpart_zero_of_old W.normal E (fun c' hc' hs => by
      rcases List.mem_append.1 hc' with h | h
      · obtain ⟨c, hc, rfl⟩ := mem_liftCs.1 h
        exact ⟨c, hc, by simp [Comp.map]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp [mkC, Kind.isSolid] at hs)
    exact ⟨by rw [h0]; norm_num, fun h => absurd h (by rw [h0]; norm_num)⟩
  · refine labels_le_one (u := liftA 1 x) fun c hc => Or.inl ?_
    rcases List.mem_append.1 hc with h | h
    · exact label_none_lift W.unl c h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> rfl
  · have h2 := w2f_ord W.lt W.kind
    simp [Graph.ord_eq, ordL_liftCs, mkC, Kind.ord]
    linarith

end Terms2

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

/-- A piece of the derivative that does not lie on the pair `{p, q}`. -/
private theorem dPieces_safe {p q : V} {c : Comp V} {ps : List (Comp V)}
    (h : c.dPieces p q = some ps)
    (hpq : p ≠ q) (hx : c.x ≠ p) (hb : c.endB ≠ p) :
    ∃ c₂ ∈ ps, ¬ ((c₂.x = p ∧ c₂.y = q) ∨ (c₂.x = q ∧ c₂.y = p)) := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨solidC .plus q c.endB, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    rw [solidC_x, solidC_y]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hpq h1.symm
    · exact hb h2
  · refine ⟨solidC .minus c.x q, List.mem_cons_self .., ?_⟩
    rw [solidC_x, solidC_y]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hx h1
    · exact hpq h2.symm

end DPieces

/-! ## Family B: the terms with a derivative -/

section FamB

variable {k n : ℕ}

private theorem famB {C j : ℕ} {g₁ : Graph k n} {x : Atom k n} (hN : g₁.Normal C) (hP : g₁.Plain)
    (o : Option (Atom k (n + j))) (f : List (Comp (Atom k n)))
    (p q : Atom k (n + j)) (hpq : p ≠ q) (hp : ∀ c ∈ liftCs j f, c.x ≠ p ∧ c.endB ≠ p)
    (d : List (Comp (Atom k (n + j)))) (N₁ N₂ : List (Comp (Atom k (n + j)))) (e : Coeff)
    (hf1 : ∀ c ∈ f, c ∈ g₁.comps) (hf2 : ∀ c ∈ g₁.comps, c ∉ f → c.kind.isWeight = true)
    (hd : d ∈ dTerms p q (liftCs j f))
    (hN₁ : ∀ c' ∈ N₁, NewOK c') (hN₂ : ∀ c' ∈ N₂, NewOK c')
    (hE : mkC (.G .plus) p q ∈ N₁ ++ N₂)
    (hsol : ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length = 1)
    (hatt : ∀ i : Fin j, (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j)).wavedGraph.Reachable
      (liftA j x) (newA i)) :
    ExtData (liftA j) g₁ x (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j)) ∧
    (unpartL (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j))).length ≤ 3 ∧
    ((unpartL (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j))).length = 3 →
      ∃ c₁ ∈ unpartL (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j)),
      ∃ c₂ ∈ unpartL (⟨labW o (d ++ N₁) ++ N₂, e⟩ : Graph k (n + j)), ¬ SamePair c₁ c₂) := by
  set g' : Graph k (n + j) := ⟨labW o (d ++ N₁) ++ N₂, e⟩ with hg'
  have hcomps : g'.comps = labW o (d ++ N₁) ++ N₂ := rfl
  have E := extB hN hP o f p q d N₁ N₂ e hf1 hf2 hd hN₁ hN₂ hE hatt
  refine ⟨E, ?_⟩
  obtain ⟨jj, hjj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hpsl := dPieces_length hps
  -- the solid edges of the input graph are partnered
  have hold : unpartCount g' ((liftCs j f).eraseIdx jj) = 0 := by
    refine unpartCount_eq_zero g' fun c' hc' hs => ?_
    obtain ⟨c, hcf, rfl⟩ := mem_liftCs.1 (List.mem_of_mem_eraseIdx hc')
    exact partnered_old hN E ⟨c, hf1 c hcf, rfl, rfl, rfl⟩ hs
  have hsplit : (unpartL g').length = unpartCount g' ps + unpartCount g' (N₁ ++ N₂) := by
    rw [unpartL_length, hcomps, unpartCount_append, unpartCount_labW, List.append_assoc,
      unpartCount_append, unpartCount_append, hold]
    simp [unpartCount_append]
    omega
  have hNs : unpartCount g' (N₁ ++ N₂) ≤ 1 :=
    (unpartCount_le_solid g' (N₁ ++ N₂)).trans hsol.le
  have hpsb : unpartCount g' ps ≤ 2 := by
    have := unpartCount_le g' ps
    omega
  refine ⟨by omega, fun h3 => ?_⟩
  have hps2 : unpartCount g' ps = 2 := by omega
  have hN1 : unpartCount g' (N₁ ++ N₂) = 1 := by omega
  -- every piece is a solid edge without partner
  have hall : ∀ c ∈ ps, (c.kind.isSolid && !partnered g' c) = true := by
    have := hps2
    unfold unpartCount at this
    rw [← hpsl] at this
    exact (List.length_filter_eq_length_iff.1 this)
  -- the edge `G_{pq}` has no partner
  have hG : (partnered g' (mkC (.G .plus) p q)) = false := by
    have h1 : List.Sublist ((N₁ ++ N₂).filter fun c => c.kind.isSolid && !partnered g' c)
        ((N₁ ++ N₂).filter fun c => c.kind.isSolid) :=
      List.monotone_filter_right _ (fun c hc => by
        simp only [Bool.and_eq_true] at hc
        exact hc.1)
    have h2 := h1.eq_of_length (by unfold unpartCount at hN1; rw [hN1, hsol])
    have hmem : mkC (.G .plus) p q ∈ (N₁ ++ N₂).filter fun c => c.kind.isSolid :=
      List.mem_filter.2 ⟨hE, by simp [mkC, Kind.isSolid]⟩
    rw [← h2] at hmem
    have := (List.mem_filter.1 hmem).2
    simpa [mkC, Kind.isSolid] using this
  -- representatives in the graph
  have himg : ∀ m, (m ∈ (liftCs j f).eraseIdx jj ++ ps ++ N₁ ∨ m ∈ N₂) →
      ∃ m'' ∈ g'.comps, m''.x = m.x ∧ m''.y = m.y ∧ m''.kind = m.kind := by
    intro m hm
    rcases hm with hm | hm
    · obtain ⟨m'', hm'', h1, h2, h3⟩ := labW_exists (o := o) hm
      exact ⟨m'', by rw [hcomps]; exact List.mem_append_left _ hm'', h1, h2, h3⟩
    · exact ⟨m, by rw [hcomps]; exact List.mem_append_right _ hm, rfl, rfl, rfl⟩
  have hFj : (liftCs j f)[jj] ∈ liftCs j f := List.getElem_mem hjj
  obtain ⟨c₂, hc₂ps, hc₂⟩ := dPieces_safe hps hpq (hp _ hFj).1 (hp _ hFj).2
  obtain ⟨c₁'', hc₁'', e1, e2, e3⟩ := himg (mkC (.G .plus) p q) (by
    rcases List.mem_append.1 hE with h | h
    · exact Or.inl (List.mem_append_right _ h)
    · exact Or.inr h)
  obtain ⟨c₂'', hc₂'', f1, f2, f3⟩ := himg c₂ (Or.inl (List.mem_append_left _
    (List.mem_append_right _ hc₂ps)))
  refine ⟨c₁'', ?_, c₂'', ?_, ?_⟩
  · refine List.mem_filter.2 ⟨hc₁'', ?_⟩
    have : partnered g' c₁'' = false := by
      rw [partnered_congr g' (c' := mkC (.G .plus) p q) e1 e2]
      exact hG
    simp [e3, mkC, Kind.isSolid, this]
  · refine List.mem_filter.2 ⟨hc₂'', ?_⟩
    have := hall c₂ hc₂ps
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this ⊢
    refine ⟨by rw [f3]; exact this.1, ?_⟩
    rw [partnered_congr g' (c' := c₂) f1 f2]
    exact this.2
  · unfold SamePair
    rw [e1, e2, f1, f2]
    simpa [mkC] using hc₂

end FamB

/-! ## Family A: the terms without a derivative -/

section FamA

variable {k n : ℕ}

private theorem out2B_t2 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    Out2B C Γ x (w2t2 x Γ i) := by
  unfold w2t2
  have E : ExtData (liftA 2) Γ x
      (⟨liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
        mkC (.light .plus) (newA 1) (newA 1)], cm * Γ.coeff⟩ : Graph k (n + 2)) := by
    have := extA (j := 2) W.normal W.plain none (w2f Γ i)
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
        mkC (.light .plus) (newA 0) (newA 0), mkC (.light .plus) (newA 1) (newA 1)] []
      (cm * Γ.coeff) w2f_sub (w2f_cover W.lt W.kind)
      (by
        intro c' hc'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl
        · exact NewOK_waved _ _ _
        · exact NewOK_waved _ _ _
        · exact NewOK_light _ _
        · exact NewOK_light _ _)
      (by simp)
      (by
        have h0 : (⟨labW none (liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
            mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
            mkC (.light .plus) (newA 1) (newA 1)]) ++ [], cm * Γ.coeff⟩ :
              Graph k (n + 2)).wavedGraph.Reachable
            (liftA 2 x) (newA 0) := by
          refine reach_of_waved _ (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) ?_ ⟨.plus, rfl⟩
          simp [labW]
        have h1 : (⟨labW none (liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
            mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
            mkC (.light .plus) (newA 1) (newA 1)]) ++ [], cm * Γ.coeff⟩ :
              Graph k (n + 2)).wavedGraph.Reachable
            (newA 0) (newA 1) := by
          refine reach_of_waved _ (c := mkC (.waved .s) (newA 0) (newA 1)) ?_ ⟨.s, rfl⟩
          simp [labW]
        intro i
        fin_cases i
        · exact h0
        · exact h0.trans h1)
    simpa [labW] using this
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 2) (liftA_isLeft 2) E ?_ ?_ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    simp [liftCs_length] at this ⊢
    omega
  · have h0 := unpart_zero_of_old W.normal E (fun c' hc' hs => by
      rcases List.mem_append.1 hc' with h | h
      · obtain ⟨c, hc, rfl⟩ := mem_liftCs.1 h
        exact ⟨c, w2f_sub c hc, by simp [Comp.map]⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> simp [mkC, Kind.isSolid] at hs)
    exact ⟨by rw [h0]; norm_num, fun h => absurd h (by rw [h0]; norm_num)⟩
  · refine labels_le_one (u := liftA 2 x) fun c hc => Or.inl ?_
    rcases List.mem_append.1 hc with h | h
    · exact label_none_lift (fun c hc => W.unl c (w2f_sub c hc)) c h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
  · have h2 := w2f_ord W.lt W.kind
    simp [Graph.ord_eq, ordL_liftCs, mkC, Kind.ord]
    linarith

end FamA

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

private theorem solid_old_famA {j : ℕ} {Γ : Graph k n} (o : Option (Atom k (n + j)))
    {B : List (Comp (Atom k n))} {N₁ N₂ : List (Comp (Atom k (n + j)))}
    (hB : ∀ c ∈ B, c ∈ Γ.comps) (hN : ∀ c ∈ N₁ ++ N₂, c.kind.isSolid = false) :
    ∀ c' ∈ labW o (liftCs j B ++ N₁) ++ N₂, c'.kind.isSolid = true →
      ∃ c ∈ Γ.comps, c'.x = liftA j c.x ∧ c'.y = liftA j c.y ∧ c'.kind = c.kind := by
  intro c' hc' hs
  rcases List.mem_append.1 hc' with h | h
  · obtain ⟨m, hm, hm'⟩ := labW_cases h
    have hshape : c'.x = m.x ∧ c'.y = m.y ∧ c'.kind = m.kind := by
      rcases hm' with rfl | ⟨u, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨labelQ_x _ _, labelQ_y _ _, labelQ_kind _ _⟩
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨c, hc, rfl⟩ := mem_liftCs.1 hm
      exact ⟨c, hB c hc, by simpa [Comp.map] using hshape⟩
    · exfalso
      have := hN m (List.mem_append_left _ hm)
      rw [hshape.2.2] at hs
      rw [hs] at this
      cases this
  · exfalso
    have := hN c' (List.mem_append_right _ h)
    rw [hs] at this
    cases this

private theorem lab_famA {j : ℕ} {Γ : Graph k n} (hU : ∀ c ∈ Γ.comps, c.label = none)
    (u : Atom k (n + j)) {B : List (Comp (Atom k n))} {N₁ N₂ : List (Comp (Atom k (n + j)))}
    (hB : ∀ c ∈ B, c ∈ Γ.comps) (hN : ∀ c ∈ N₁ ++ N₂, c.label = none) :
    ∀ c ∈ labelQs u (liftCs j B ++ N₁) ++ N₂, c.label = none ∨ c.label = some (.Q, u) := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · refine label_labelQs u (fun c hc => ?_) c h
    rcases List.mem_append.1 hc with h | h
    · exact label_none_lift (fun c hc => hU c (hB c hc)) c h
    · exact hN c (List.mem_append_left _ h)
  · exact Or.inl (hN c (List.mem_append_right _ h))

private theorem dTerm_ord_data {V : Type*} [DecidableEq V] {p q : V} {F d : List (Comp V)}
    (hd : d ∈ dTerms p q F) :
    ∃ c ∈ F, ∃ ps, c.dPieces p q = some ps ∧ ordL d + c.kind.ord = ordL F + ordL ps := by
  obtain ⟨j, hj, ps, hps, rfl⟩ := mem_dTerms.1 hd
  refine ⟨F[j], List.getElem_mem hj, ps, hps, ?_⟩
  have := ordL_eraseIdx F j hj
  rw [ordL_append]
  linarith

end Helpers

/-! ## The `Q`-terms without a derivative -/

section QTerms

variable {k n : ℕ}

private theorem comp_map_id {V : Type*} (c : Comp V) : c.map id = c := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp [Comp.map]

private theorem out2B_t5 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    Out2B C Γ x (w2t5 x Γ) := by
  unfold w2t5
  have E : ExtData id Γ x (⟨labelQs x Γ.comps, Γ.coeff⟩ : Graph k n) := by
    have hcomps : (⟨labelQs x Γ.comps, Γ.coeff⟩ : Graph k n).comps = labelQs x Γ.comps := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc hr
      rw [hcomps, comp_map_id]
      exact labW_nonrandom (o := some x) hc hr
    · intro c' hc'
      rw [hcomps] at hc'
      obtain ⟨c, hc, rfl⟩ := mem_labelQs.1 hc'
      by_cases hr : c.kind.isRandom = true
      · right
        have := NewOK_map_of_old (φ := id) Function.injective_id W.normal W.plain hc hr
        rw [comp_map_id] at this
        exact this.labelQ x
      · left
        refine ⟨c, hc, ?_⟩
        rw [comp_map_id]
        unfold Comp.labelQ
        simp [hr]
    · intro c hc hk hne
      obtain ⟨c'', hc'', h1, h2, h3⟩ := labW_exists (o := some x) (L := Γ.comps) hc
      have := reach_of_comp_noX (⟨labelQs x Γ.comps, Γ.coeff⟩ : Graph k n) (c := c'')
        (by rw [hcomps]; exact hc'') (by rw [h3]; exact hk)
      simpa [h1, h2] using this
    · intro u hu
      exact absurd rfl (hu u)
  refine out2B_mk W.normal W.plain W.right W.unl Function.injective_id (fun _ => rfl) E ?_ ?_ ?_ ?_
  · have := W.normal.1.size
    simp [labelQs_length] at this ⊢
    omega
  · have h0 := unpart_zero_of_old W.normal E (fun c' hc' hs => by
      obtain ⟨c, hc, rfl⟩ := mem_labelQs.1 hc'
      exact ⟨c, hc, by simp⟩)
    exact ⟨by rw [h0]; norm_num, fun h => absurd h (by rw [h0]; norm_num)⟩
  · refine labels_le_one (u := x) fun c hc => ?_
    exact label_labelQs x W.unl c hc
  · simp [Graph.ord_eq, ordL_labelQs]

private theorem out2B_t6 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    Out2B C Γ x (w2t6 x Γ i) := by
  unfold w2t6
  have hN₁ : ∀ c' ∈ [mkC (.light .plus) (newA 0 : Atom k (n + 1)) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl
    exact NewOK_light _ _
  have hN₂ : ∀ c' ∈ [mkC (.waved .plus) (liftA 1 x : Atom k (n + 1)) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl
    exact NewOK_waved _ _ _
  have E : ExtData (liftA 1) Γ x
      (⟨labelQs (newA 0) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
        [mkC (.waved .plus) (liftA 1 x) (newA 0)], Γ.coeff⟩ : Graph k (n + 1)) := by
    have := extA (j := 1) W.normal W.plain (some (newA 0)) (w2f Γ i)
      [mkC (.light .plus) (newA 0) (newA 0)] [mkC (.waved .plus) (liftA 1 x) (newA 0)] Γ.coeff
      w2f_sub (w2f_cover W.lt W.kind) hN₁ hN₂
      (by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        refine reach_of_waved _ (c := mkC (.waved .plus) (liftA 1 x) (newA 0)) ?_ ⟨.plus, rfl⟩
        simp [labW])
    simpa [labW] using this
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 1) (liftA_isLeft 1) E ?_ ?_ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    simp [liftCs_length, labelQs_length] at this ⊢
    omega
  · have h0 := unpart_zero_of_old W.normal E
      (solid_old_famA (o := some (newA 0)) (N₁ := [mkC (.light .plus) (newA 0) (newA 0)])
        (N₂ := [mkC (.waved .plus) (liftA 1 x) (newA 0)]) w2f_sub (by
          intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> rfl))
    exact ⟨by rw [h0]; norm_num, fun h => absurd h (by rw [h0]; norm_num)⟩
  · refine labels_le_one (u := newA 0) ?_
    exact lab_famA (N₁ := [mkC (.light .plus) (newA 0) (newA 0)])
      (N₂ := [mkC (.waved .plus) (liftA 1 x) (newA 0)]) W.unl (newA 0) w2f_sub (by
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl)
  · have h2 := w2f_ord W.lt W.kind
    simp [Graph.ord_eq, ordL_liftCs, ordL_labelQs, mkC, Kind.ord]
    linarith

private theorem out2B_t7 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    Out2B C Γ x (w2t7 x Γ i) := by
  unfold w2t7
  have hN₁ : ∀ c' ∈ [mkC (.light .plus) (newA 0 : Atom k (n + 1)) (newA 0),
      mkC (.weight .plus) (liftA 1 x) (liftA 1 x)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact NewOK_light _ _
    · exact NewOK_weight _ _
  have hN₂ : ∀ c' ∈ [mkC (.waved .s) (liftA 1 x : Atom k (n + 1)) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl
    exact NewOK_waved _ _ _
  have E : ExtData (liftA 1) Γ x
      (⟨labelQs (liftA 1 x) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0),
        mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)], -cm * Γ.coeff⟩ : Graph k (n + 1)) := by
    have := extA (j := 1) W.normal W.plain (some (liftA 1 x)) (w2f Γ i)
      [mkC (.light .plus) (newA 0) (newA 0), mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]
      [mkC (.waved .s) (liftA 1 x) (newA 0)] (-cm * Γ.coeff)
      w2f_sub (w2f_cover W.lt W.kind) hN₁ hN₂
      (by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        refine reach_of_waved _ (c := mkC (.waved .s) (liftA 1 x) (newA 0)) ?_ ⟨.s, rfl⟩
        simp [labW])
    simpa [labW] using this
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 1) (liftA_isLeft 1) E ?_ ?_ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    simp [liftCs_length, labelQs_length] at this ⊢
    omega
  · have h0 := unpart_zero_of_old W.normal E
      (solid_old_famA (o := some (liftA 1 x))
        (N₁ := [mkC (.light .plus) (newA 0) (newA 0), mkC (.weight .plus) (liftA 1 x) (liftA 1 x)])
        (N₂ := [mkC (.waved .s) (liftA 1 x) (newA 0)]) w2f_sub (by
          intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with rfl | rfl | rfl <;> rfl))
    exact ⟨by rw [h0]; norm_num, fun h => absurd h (by rw [h0]; norm_num)⟩
  · refine labels_le_one (u := liftA 1 x) ?_
    exact lab_famA (N₁ := [mkC (.light .plus) (newA 0) (newA 0),
        mkC (.weight .plus) (liftA 1 x) (liftA 1 x)])
      (N₂ := [mkC (.waved .s) (liftA 1 x) (newA 0)]) W.unl (liftA 1 x) w2f_sub (by
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
        rcases hc with rfl | rfl | rfl <;> rfl)
  · have h2 := w2f_ord W.lt W.kind
    simp [Graph.ord_eq, ordL_liftCs, ordL_labelQs, mkC, Kind.ord]
    linarith

private theorem out2B_t8 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    Out2B C Γ x (w2t8 x Γ i) := by
  unfold w2t8
  have hN₁ : ∀ c' ∈ [mkC (.light .plus) (newA 1 : Atom k (n + 2)) (newA 1),
      mkC (.weight .plus) (newA 0) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact NewOK_light _ _
    · exact NewOK_weight _ _
  have hN₂ : ∀ c' ∈ [mkC (.waved .plus) (liftA 2 x : Atom k (n + 2)) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact NewOK_waved _ _ _
    · exact NewOK_waved _ _ _
  have E : ExtData (liftA 2) Γ x
      (⟨labelQs (newA 0) (liftCs 2 (w2f Γ i) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ : Graph k (n + 2)) := by
    have := extA (j := 2) W.normal W.plain (some (newA 0)) (w2f Γ i)
      [mkC (.light .plus) (newA 1) (newA 1), mkC (.weight .plus) (newA 0) (newA 0)]
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]
      (-cm * Γ.coeff) w2f_sub (w2f_cover W.lt W.kind) hN₁ hN₂
      (by
        have h0 : (⟨labW (some (newA 0)) (liftCs 2 (w2f Γ i) ++
            [mkC (.light .plus) (newA 1) (newA 1),
            mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
            mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ :
              Graph k (n + 2)).wavedGraph.Reachable
            (liftA 2 x) (newA 0) := by
          refine reach_of_waved _ (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) ?_ ⟨.plus, rfl⟩
          simp [labW]
        have h1 : (⟨labW (some (newA 0)) (liftCs 2 (w2f Γ i) ++
            [mkC (.light .plus) (newA 1) (newA 1),
            mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
            mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ :
              Graph k (n + 2)).wavedGraph.Reachable
            (newA 0) (newA 1) := by
          refine reach_of_waved _ (c := mkC (.waved .s) (newA 0) (newA 1)) ?_ ⟨.s, rfl⟩
          simp [labW]
        intro i
        fin_cases i
        · exact h0
        · exact h0.trans h1)
    simpa [labW] using this
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 2) (liftA_isLeft 2) E ?_ ?_ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    simp [liftCs_length, labelQs_length] at this ⊢
    omega
  · have h0 := unpart_zero_of_old W.normal E
      (solid_old_famA (o := some (newA 0))
        (N₁ := [mkC (.light .plus) (newA 1) (newA 1), mkC (.weight .plus) (newA 0) (newA 0)])
        (N₂ := [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)])
        w2f_sub (by
          intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with rfl | rfl | rfl | rfl <;> rfl))
    exact ⟨by rw [h0]; norm_num, fun h => absurd h (by rw [h0]; norm_num)⟩
  · refine labels_le_one (u := newA 0) ?_
    exact lab_famA (N₁ := [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.weight .plus) (newA 0) (newA 0)])
      (N₂ := [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)])
      W.unl (newA 0) w2f_sub (by
        intro c hc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> rfl)
  · have h2 := w2f_ord W.lt W.kind
    simp [Graph.ord_eq, ordL_liftCs, ordL_labelQs, mkC, Kind.ord]
    linarith

end QTerms

/-! ## The terms with a derivative -/

section BTerms

variable {k n : ℕ}

private theorem endB_map {V W : Type*} (φ : V → W) (c : Comp V) : (c.map φ).endB = φ c.endB := by
  unfold Comp.endB
  by_cases h : c.kind.isWeight = true <;> simp [Comp.map, h]

private theorem liftCs_ne_newA {j : ℕ} {f : List (Comp (Atom k n))} (i : Fin j) :
    ∀ c ∈ liftCs j f, c.x ≠ (newA i : Atom k (n + j)) ∧ c.endB ≠ (newA i : Atom k (n + j)) := by
  intro c hc
  obtain ⟨c₀, -, rfl⟩ := mem_liftCs.1 hc
  refine ⟨?_, ?_⟩
  · simpa [Comp.map] using liftA_ne_newA j c₀.x i
  · rw [endB_map]
    exact liftA_ne_newA j _ i

private theorem newA_ne_newA {j : ℕ} {i i' : Fin j} (h : i ≠ i') :
    (newA i : Atom k (n + j)) ≠ newA i' := by
  intro h'
  have := congrArg Fin.val (Sum.inr.inj h')
  exact h (Fin.ext (Nat.add_left_cancel this))

private theorem out2B_t3 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i)
    {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))) :
    Out2B C Γ x (w2t3 x Γ d) := by
  unfold w2t3
  have hN₁ : ∀ c' ∈ [mkC (.waved .s) (liftA 1 x : Atom k (n + 1)) (newA 0),
      mkC (.G .plus) (newA 0) (liftA 1 x)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact NewOK_waved _ _ _
    · exact NewOK_G _ (liftA_ne_newA 1 x 0).symm
  have hatt : ∀ i' : Fin 1, (⟨labW none (d ++ [mkC (.waved .s) (liftA 1 x : Atom k (n + 1))
        (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)]) ++ [], cm * Γ.coeff⟩ :
        Graph k (n + 1)).wavedGraph.Reachable
      (liftA 1 x) (newA i') := by
    intro i'
    have hi : i' = 0 := Subsingleton.elim _ _
    subst hi
    refine reach_of_waved _ (c := mkC (.waved .s) (liftA 1 x) (newA 0)) ?_ ⟨.s, rfl⟩
    simp [labW]
  obtain ⟨E, hu1, hu2⟩ := famB (j := 1) W.normal W.plain none (w2f Γ i) (newA 0) (liftA 1 x)
    (liftA_ne_newA 1 x 0).symm (liftCs_ne_newA 0) d
    [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)] []
    (cm * Γ.coeff) w2f_sub (w2f_cover W.lt W.kind) hd hN₁ (by simp) (by simp)
    (by simp [mkC, Kind.isSolid]) hatt
  simp only [labW, List.append_nil] at E hu1 hu2
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 1) (liftA_isLeft 1) E ?_
    ⟨hu1, hu2⟩ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    have h3 := dTerm_length hd
    simp [liftCs_length] at this h3 ⊢
    omega
  · refine labels_le_one (u := liftA 1 x) fun c hc => Or.inl ?_
    rcases List.mem_append.1 hc with h | h
    · exact label_dTerms (label_none_lift (fun c hc => W.unl c (w2f_sub c hc)) ) hd c h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> rfl
  · obtain ⟨c, hcF, ps, hps, hord⟩ := dTerm_ord_data hd
    obtain ⟨hp1, hp2⟩ := liftCs_ne_newA (j := 1) 0 c hcF
    obtain ⟨h1, h2⟩ := dPieces_ord_ge hps hp1 hp2
    have h3 := w2f_ord W.lt W.kind
    rw [ordL_liftCs] at hord
    simp [Graph.ord_eq, mkC, Kind.ord]
    linarith

private theorem out2B_t4 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i)
    {d : List (Comp (Atom k (n + 2)))}
    (hd : d ∈ dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))) :
    Out2B C Γ x (w2t4 x Γ d) := by
  unfold w2t4
  have hN₁ : ∀ c' ∈ [mkC (.waved .plus) (liftA 2 x : Atom k (n + 2)) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.G .plus) (newA 1) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact NewOK_waved _ _ _
    · exact NewOK_waved _ _ _
    · exact NewOK_G _ (newA_ne_newA (by decide))
  have hatt : ∀ i' : Fin 2, (⟨labW none (d ++ [mkC (.waved .plus)
        (liftA 2 x : Atom k (n + 2)) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.G .plus) (newA 1) (newA 0)]) ++ [],
      cm * Γ.coeff⟩ : Graph k (n + 2)).wavedGraph.Reachable (liftA 2 x) (newA i') := by
    have h0 : (⟨labW none (d ++ [mkC (.waved .plus) (liftA 2 x : Atom k (n + 2)) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.G .plus) (newA 1) (newA 0)]) ++ [],
        cm * Γ.coeff⟩ : Graph k (n + 2)).wavedGraph.Reachable (liftA 2 x) (newA 0) := by
      refine reach_of_waved _ (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) ?_ ⟨.plus, rfl⟩
      simp [labW]
    have h1 : (⟨labW none (d ++ [mkC (.waved .plus) (liftA 2 x : Atom k (n + 2)) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.G .plus) (newA 1) (newA 0)]) ++ [],
        cm * Γ.coeff⟩ : Graph k (n + 2)).wavedGraph.Reachable (newA 0) (newA 1) := by
      refine reach_of_waved _ (c := mkC (.waved .s) (newA 0) (newA 1)) ?_ ⟨.s, rfl⟩
      simp [labW]
    intro i'
    fin_cases i'
    · exact h0
    · exact h0.trans h1
  obtain ⟨E, hu1, hu2⟩ := famB (j := 2) W.normal W.plain none (w2f Γ i) (newA 1) (newA 0)
    (newA_ne_newA (by decide)) (liftCs_ne_newA 1) d
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.G .plus) (newA 1) (newA 0)] []
    (cm * Γ.coeff) w2f_sub (w2f_cover W.lt W.kind) hd hN₁ (by simp) (by simp)
    (by simp [mkC, Kind.isSolid]) hatt
  simp only [labW, List.append_nil] at E hu1 hu2
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 2) (liftA_isLeft 2) E ?_
    ⟨hu1, hu2⟩ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    have h3 := dTerm_length hd
    simp [liftCs_length] at this h3 ⊢
    omega
  · refine labels_le_one (u := liftA 2 x) fun c hc => Or.inl ?_
    rcases List.mem_append.1 hc with h | h
    · exact label_dTerms (label_none_lift (fun c hc => W.unl c (w2f_sub c hc)) ) hd c h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> rfl
  · obtain ⟨c, hcF, ps, hps, hord⟩ := dTerm_ord_data hd
    obtain ⟨hp1, hp2⟩ := liftCs_ne_newA (j := 2) 1 c hcF
    obtain ⟨hq1, hq2⟩ := liftCs_ne_newA (j := 2) 0 c hcF
    have h1 := dPieces_ord_two hps hp1 hp2 hq1 hq2
    have h2 := (dPieces_ord_ge hps hp1 hp2).2
    have h3 := w2f_ord W.lt W.kind
    rw [ordL_liftCs] at hord
    simp [Graph.ord_eq, mkC, Kind.ord]
    linarith

end BTerms

/-! ## The `Q`-terms with a derivative -/

section BQTerms

variable {k n : ℕ}

private theorem out2B_t9 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i)
    {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))) :
    Out2B C Γ x (w2t9 x Γ d) := by
  unfold w2t9
  have hN₁ : ∀ c' ∈ [mkC (.G .plus) (newA 0 : Atom k (n + 1)) (liftA 1 x)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl
    exact NewOK_G _ (liftA_ne_newA 1 x 0).symm
  have hN₂ : ∀ c' ∈ [mkC (.waved .s) (liftA 1 x : Atom k (n + 1)) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl
    exact NewOK_waved _ _ _
  have hatt : ∀ i' : Fin 1, (⟨labW (some (liftA 1 x : Atom k (n + 1)))
      (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
      -cm * Γ.coeff⟩ : Graph k (n + 1)).wavedGraph.Reachable (liftA 1 x) (newA i') := by
    intro i'
    have hi : i' = 0 := Subsingleton.elim _ _
    subst hi
    refine reach_of_waved _ (c := mkC (.waved .s) (liftA 1 x) (newA 0)) ?_ ⟨.s, rfl⟩
    simp [labW]
  obtain ⟨E, hu1, hu2⟩ := famB (j := 1) W.normal W.plain (some (liftA 1 x)) (w2f Γ i) (newA 0)
    (liftA 1 x) (liftA_ne_newA 1 x 0).symm (liftCs_ne_newA 0) d
    [mkC (.G .plus) (newA 0) (liftA 1 x)] [mkC (.waved .s) (liftA 1 x) (newA 0)]
    (-cm * Γ.coeff) w2f_sub (w2f_cover W.lt W.kind) hd hN₁ hN₂ (by simp)
    (by simp [mkC, Kind.isSolid]) hatt
  simp only [labW] at E hu1 hu2
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 1) (liftA_isLeft 1) E ?_
    ⟨hu1, hu2⟩ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    have h3 := dTerm_length hd
    simp [liftCs_length, labelQs_length] at this h3 ⊢
    omega
  · refine labels_le_one (u := liftA 1 x) ?_
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · refine label_labelQs _ (fun c hc => ?_) c h
      rcases List.mem_append.1 hc with h | h
      · exact label_dTerms (label_none_lift (fun c hc => W.unl c (w2f_sub c hc))) hd c h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl; exact Or.inl rfl
  · obtain ⟨c, hcF, ps, hps, hord⟩ := dTerm_ord_data hd
    obtain ⟨hp1, hp2⟩ := liftCs_ne_newA (j := 1) 0 c hcF
    obtain ⟨h1, h2⟩ := dPieces_ord_ge hps hp1 hp2
    have h3 := w2f_ord W.lt W.kind
    rw [ordL_liftCs] at hord
    simp [Graph.ord_eq, ordL_labelQs, mkC, Kind.ord]
    linarith

private theorem out2B_t10 {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i)
    {d : List (Comp (Atom k (n + 2)))}
    (hd : d ∈ dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))) :
    Out2B C Γ x (w2t10 x Γ d) := by
  unfold w2t10
  have hN₁ : ∀ c' ∈ [mkC (.G .plus) (newA 1 : Atom k (n + 2)) (newA 0)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl
    exact NewOK_G _ (newA_ne_newA (by decide))
  have hN₂ : ∀ c' ∈ [mkC (.waved .plus) (liftA 2 x : Atom k (n + 2)) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)], NewOK c' := by
    intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact NewOK_waved _ _ _
    · exact NewOK_waved _ _ _
  have hatt : ∀ i' : Fin 2, (⟨labW (some (newA 0 : Atom k (n + 2)))
      (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ : Graph k (n + 2)).wavedGraph.Reachable
      (liftA 2 x) (newA i') := by
    have h0 : (⟨labW (some (newA 0 : Atom k (n + 2)))
        (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ : Graph k (n + 2)).wavedGraph.Reachable
        (liftA 2 x) (newA 0) := by
      refine reach_of_waved _ (c := mkC (.waved .plus) (liftA 2 x) (newA 0)) ?_ ⟨.plus, rfl⟩
      simp [labW]
    have h1 : (⟨labW (some (newA 0 : Atom k (n + 2)))
        (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ : Graph k (n + 2)).wavedGraph.Reachable
        (newA 0) (newA 1) := by
      refine reach_of_waved _ (c := mkC (.waved .s) (newA 0) (newA 1)) ?_ ⟨.s, rfl⟩
      simp [labW]
    intro i'
    fin_cases i'
    · exact h0
    · exact h0.trans h1
  obtain ⟨E, hu1, hu2⟩ := famB (j := 2) W.normal W.plain (some (newA 0)) (w2f Γ i) (newA 1)
    (newA 0) (newA_ne_newA (by decide)) (liftCs_ne_newA 1) d
    [mkC (.G .plus) (newA 1) (newA 0)]
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]
    (-cm * Γ.coeff) w2f_sub (w2f_cover W.lt W.kind) hd hN₁ hN₂ (by simp)
    (by simp [mkC, Kind.isSolid]) hatt
  simp only [labW] at E hu1 hu2
  refine out2B_mk W.normal W.plain W.right W.unl (liftA_injective 2) (liftA_isLeft 2) E ?_
    ⟨hu1, hu2⟩ ?_ ?_
  · have := W.normal.1.size
    have h2 := w2f_length W.lt
    have h3 := dTerm_length hd
    simp [liftCs_length, labelQs_length] at this h3 ⊢
    omega
  · refine labels_le_one (u := newA 0) ?_
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · refine label_labelQs _ (fun c hc => ?_) c h
      rcases List.mem_append.1 hc with h | h
      · exact label_dTerms (label_none_lift (fun c hc => W.unl c (w2f_sub c hc))) hd c h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> exact Or.inl rfl
  · obtain ⟨c, hcF, ps, hps, hord⟩ := dTerm_ord_data hd
    obtain ⟨hp1, hp2⟩ := liftCs_ne_newA (j := 2) 1 c hcF
    obtain ⟨hq1, hq2⟩ := liftCs_ne_newA (j := 2) 0 c hcF
    have h1 := dPieces_ord_two hps hp1 hp2 hq1 hq2
    have h2 := (dPieces_ord_ge hps hp1 hp2).2
    have h3 := w2f_ord W.lt W.kind
    rw [ordL_liftCs] at hord
    simp [Graph.ord_eq, ordL_labelQs, mkC, Kind.ord]
    linarith

end BQTerms

/-! ## Complex conjugation and `Out2B` -/

section ConjOut2

variable {k n : ℕ}

private theorem partnered_conj (g : Graph k n) (c : Comp (Atom k n)) :
    partnered g.conj c.conj = partnered g c := by
  unfold partnered
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Graph.conj_comps, List.mem_map]
  constructor
  · rintro ⟨c₂, ⟨c₃, hc₃, rfl⟩, h⟩
    refine ⟨c₃, hc₃, ?_⟩
    simpa [Comp.conj, Kind.conj_eq_xdot] using h
  · rintro ⟨c₃, hc₃, h⟩
    refine ⟨c₃.conj, ⟨c₃, hc₃, rfl⟩, ?_⟩
    simpa [Comp.conj, Kind.conj_eq_xdot] using h

private theorem unpartL_conj (g : Graph k n) : unpartL g.conj = (unpartL g).map Comp.conj := by
  unfold unpartL
  rw [Graph.conj_comps, List.filter_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp [partnered_conj, Kind.conj_isSolid]

private theorem samePair_conj {c d : Comp (Atom k n)} : SamePair c.conj d.conj ↔ SamePair c d := by
  unfold SamePair
  simp

private theorem unp_conj {g : Graph k n}
    (h : (unpartL g).length ≤ 3 ∧ ((unpartL g).length = 3 →
      ∃ c₁ ∈ unpartL g, ∃ c₂ ∈ unpartL g, ¬ SamePair c₁ c₂)) :
    (unpartL g.conj).length ≤ 3 ∧ ((unpartL g.conj).length = 3 →
      ∃ c₁ ∈ unpartL g.conj, ∃ c₂ ∈ unpartL g.conj, ¬ SamePair c₁ c₂) := by
  rw [unpartL_conj]
  simp only [List.length_map]
  refine ⟨h.1, fun h3 => ?_⟩
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := h.2 h3
  exact ⟨c₁.conj, List.mem_map.2 ⟨c₁, hc₁, rfl⟩, c₂.conj, List.mem_map.2 ⟨c₂, hc₂, rfl⟩,
    fun h => hne (samePair_conj.1 h)⟩

private theorem Out2B.conj {C : ℕ} {g₁ : Graph k n} {x : Atom k n} {t : Tracked k n}
    (h : Out2B C g₁.conj x t) : Out2B C g₁ x ⟨t.nOut, t.g.conj, t.f⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Graph.conj_length] using h.size
  · unfold Graph.ConnNoX
    rw [Graph.conj_edgeGraphNoX]
    exact h.conn
  · intro a b
    change (t.g.conj).wavedThetaGraph.Reachable _ _
    rw [Graph.conj_wavedThetaGraph]
    exact h.int a b
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.noIntDot c hc ((Kind.conj_eq_dot _).1 hk)
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.dotOK c hc ((Kind.conj_eq_dot _).1 hk)
  · intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.sl c hc (by simpa [Kind.conj_isSolid] using hk)
  · exact unp_conj h.unp
  · exact Graph.conj_Plain h.plain
  · refine ⟨by rw [Graph.conj_labels]; exact h.lab.1, ?_⟩
    intro c' hc' hk
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    exact h.lab.2 c hc (by simpa [Kind.conj_eq_dot, Kind.conj_eq_xdot] using hk)
  · have := h.ord
    rw [Graph.conj_ord] at this ⊢
    exact this
  · intro u hu
    change (t.g.conj).wavedGraph.Reachable _ _
    rw [Graph.conj_wavedGraph]
    exact h.new u hu

end ConjOut2

/-! ## The light weight expansion: the terms satisfy `Out2B` -/

section Out2Main

variable {k n : ℕ}

private theorem out2B_pos {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} (W : W2Ctx C x Γ i) :
    ∀ t ∈ w2E x Γ i, Out2B C Γ x t := by
  intro t ht
  unfold w2E at ht
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    or_assoc] at ht
  rcases ht with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ | rfl | rfl | rfl | rfl |
    ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
  · exact out2B_t1 W
  · exact out2B_t2 W
  · exact out2B_t3 W hd
  · exact out2B_t4 W hd
  · exact out2B_t5 W
  · exact out2B_t6 W
  · exact out2B_t7 W
  · exact out2B_t8 W
  · exact out2B_t9 W hd
  · exact out2B_t10 W hd

private theorem plainB_label {c : Comp (Atom k n)} (h : c.isPlainB = true) : c.label = none := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only [Comp.isPlainB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h.1.2

private theorem w2Ctx_of_pos {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hx : x.isRight = true) (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i : ℕ}
    (hi : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = some i) :
    W2Ctx C x Γ i := by
  obtain ⟨hlt, hk, hax⟩ := w2_setup hi
  exact ⟨hN, hP, hx, fun c hc => plainB_label (hpl c hc), hlt, hk, hax⟩

private theorem oWeight2T_cases {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain) (hx : x.isRight = true) :
    ∀ t ∈ oWeight2T x Γ, Out2B C Γ x t ∨ t = Tracked.self Γ := by
  intro t ht
  unfold oWeight2T at ht
  by_cases hpl : (!(Γ.comps.all Comp.isPlainB)) = true
  · rw [ite_eq_left hpl] at ht
    exact Or.inr (List.mem_singleton.1 ht)
  · rw [ite_eq_right hpl] at ht
    have hpl' : ∀ c ∈ Γ.comps, c.isPlainB = true := by
      simpa using hpl
    cases hpos : oWeight2Pos x Γ with
    | some E =>
      rw [hpos] at ht
      simp only at ht
      have hi : ∃ i, Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = some i := by
        by_contra hno
        push Not at hno
        have : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
          cases h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
          | none => rfl
          | some i => exact absurd h (hno i)
        rw [← oWeight2Pos_none_iff] at this
        rw [hpos] at this
        cases this
      obtain ⟨i, hi⟩ := hi
      rw [oWeight2Pos_eq hi] at hpos
      obtain rfl := Option.some.inj hpos
      exact Or.inl (out2B_pos (w2Ctx_of_pos hN hP hx hpl' hi) t ht)
    | none =>
      rw [hpos] at ht
      simp only at ht
      cases hpos' : oWeight2Pos x Γ.conj with
      | some E =>
        rw [hpos'] at ht
        simp only at ht
        have hi : ∃ i, Γ.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) =
            some i := by
          by_contra hno
          push Not at hno
          have : Γ.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
            cases h : Γ.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
            | none => rfl
            | some i => exact absurd h (hno i)
          rw [← oWeight2Pos_none_iff] at this
          rw [hpos'] at this
          cases this
        obtain ⟨i, hi⟩ := hi
        rw [oWeight2Pos_eq hi] at hpos'
        obtain rfl := Option.some.inj hpos'
        have hpl'' : ∀ c ∈ Γ.conj.comps, c.isPlainB = true := by
          intro c hc
          obtain ⟨c₀, hc₀, rfl⟩ := Graph.mem_conj_comps.1 hc
          have h := hpl' c₀ hc₀
          rcases c₀ with ⟨κ, a, b, mi, l⟩
          cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;>
            simp_all [Comp.conj, Comp.isPlainB, Kind.conj]
        obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
        exact Or.inl ((out2B_pos (w2Ctx_of_pos (Graph.conj_Normal hN) (Graph.conj_Plain hP) hx
          hpl'' hi) t' ht').conj)
      | none =>
        rw [hpos'] at ht
        exact Or.inr (List.mem_singleton.1 ht)

end Out2Main

/-! ## The dotted edge partition on the output of the light weight expansion -/

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

/-! ## The dot operator: normality, order, new atoms -/

section DotOp2

variable {k n : ℕ}

private theorem Out2B.regular {C : ℕ} {g₁ : Graph k n} {x : Atom k n} {t : Tracked k n}
    (h : Out2B C g₁ x t) : t.g.Regular (C + 5) :=
  ⟨h.size, fun u v => reach_map (G := t.g.edgeGraphNoX) (H := t.g.edgeGraph) id
    (fun _ _ hab => (edgeGraphNoX_le_edgeGraph t.g hab).reachable) (h.conn u v), h.int,
    h.noIntDot⟩

private theorem dot_ord_ge {g : Graph k n} (hd : DotOK g)
    (hsl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hunp : (unpartL g).length ≤ 3 ∧ ((unpartL g).length = 3 →
      ∃ c₁ ∈ unpartL g, ∃ c₂ ∈ unpartL g, ¬ SamePair c₁ c₂)) :
    ∀ t ∈ oDotT g, g.ord ≤ t.g.ord := by
  intro t ht
  rcases mem_oDotT_cases' ht with rfl | ⟨A, hA, hm⟩
  · exact le_rfl
  · obtain ⟨K, r, e, hord, -, -, -, hle, -, -⟩ := dot_order hd hsl hunp.1 hunp.2 hA hm
    have : (e : ℤ) ≤ 2 * ((K : ℤ) + r) := by exact_mod_cast hle
    rw [hord]
    linarith

private theorem dot_op_spec {C : ℕ} {g₁ : Graph k n} {x : Atom k n} {t₂ : Tracked k n}
    (h : Out2B C g₁ x t₂) :
    ∀ t₃ ∈ oDotT t₂.g, t₃.g.Normal (2 * (C + 5)) ∧ t₃.g.Plain ∧ t₂.g.ord ≤ t₃.g.ord ∧
      ∀ u, (∀ v, t₃.f (t₂.f v) ≠ u) → t₃.g.wavedGraph.Reachable (t₃.f (t₂.f x)) u := by
  intro t₃ ht₃
  refine ⟨?_, oDotT_plain h.plain t₃ ht₃, dot_ord_ge h.dotOK h.sl h.unp t₃ ht₃,
    NR_dot h.new ht₃⟩
  exact (oDot_normal k t₂.nOut (C + 5) t₂.g h.regular h.conn h.lab.1 h.lab.2 t₃ ht₃).1

end DotOp2

/-! ## The expansion `O^{(x),1}_weight` preserves normality and plainness -/

section Weight1Op

variable {k n : ℕ}

private theorem Kind.isWeight_false_of_mol {κ : Kind}
    (h : κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) : κ.isWeight = false := by
  cases κ <;> simp_all [Kind.isWeight, Kind.joinsMol, Kind.isDiffusive]

private theorem Kind.isWeight_false_of_solid {κ : Kind} (h : κ.isSolid = true)
    : κ.isWeight = false := by
  cases κ <;> simp_all [Kind.isSolid, Kind.isWeight]

private theorem normal_of_weightRel {C : ℕ} {g g' : Graph k n} (hN : g.Normal C) (hP : g.Plain)
    (h1 : ∀ c ∈ g.comps, c.kind.isWeight = false → c ∈ g'.comps)
    (h2 : ∀ c' ∈ g'.comps, c' ∈ g.comps ∨ c'.kind.isWeight = true)
    (h3 : g'.comps.length ≤ g.comps.length) : g'.Normal C := by
  obtain ⟨⟨hsz, hcn, hint, hnid⟩, hsol, hxs⟩ := hN
  have hnw : ∀ c ∈ g'.comps, c.kind.isWeight = false → c ∈ g.comps := by
    intro c hc hk
    rcases h2 c hc with h | h
    · exact h
    · rw [h] at hk; cases hk
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    refine reach_map (G := g.edgeGraph) (H := g'.edgeGraph) id (fun a b hab => ?_) (hcn u v)
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hrel⟩ := hab
    have key : ∀ c ∈ g.comps, c.x ≠ c.y → c ∈ g'.comps := by
      intro c hc hxy
      apply h1 c hc
      by_contra hw
      have hw' : c.kind.isWeight = true := by simpa using hw
      exact hxy ((hP c hc).2.2.2.2.1 hw').symm
    rcases hrel with ⟨c, hc, h1', h2'⟩ | ⟨c, hc, h1', h2'⟩
    · have := reach_of_comp g' (key c hc (by rw [h1', h2']; exact hne))
      rw [h1', h2'] at this; exact this
    · have := reach_of_comp g' (key c hc (by rw [h1', h2']; exact hne.symm))
      rw [h1', h2'] at this; exact this.symm
  · intro a b
    refine reach_map (G := g.wavedThetaGraph) (H := g'.wavedThetaGraph) id (fun u v huv => ?_)
      (hint a b)
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv
    obtain ⟨hne, hrel⟩ := huv
    refine SimpleGraph.Adj.reachable ?_
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
    refine ⟨hne, ?_⟩
    have hnr : ∀ c ∈ g.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) →
        c ∈ g'.comps := by
      intro c hc hk
      exact h1 c hc (Kind.isWeight_false_of_mol hk)
    rcases hrel with ⟨c, hc, hk, h1', h2'⟩ | ⟨c, hc, hk, h1', h2'⟩
    · exact Or.inl ⟨c, hnr c hc hk, hk, h1', h2'⟩
    · exact Or.inr ⟨c, hnr c hc hk, hk, h1', h2'⟩
  · intro c hc hk
    have hw : c.kind.isWeight = false := by simp [hk, Kind.isWeight]
    exact hnid c (hnw c hc hw) hk
  · intro c hc hk
    exact hsol c (hnw c hc (Kind.isWeight_false_of_solid hk)) hk
  · intro u v huv
    have hw : ∀ c ∈ g'.comps, (c.kind = .xdot ∨ c.kind.isSolid = true) → c ∈ g.comps := by
      intro c hc hk
      apply hnw c hc
      rcases hk with hk | hk
      · simp [hk, Kind.isWeight]
      · exact Kind.isWeight_false_of_solid hk
    have hv : ∀ c ∈ g.comps, (c.kind = .xdot ∨ c.kind.isSolid = true) → c ∈ g'.comps := by
      intro c hc hk
      apply h1 c hc
      rcases hk with hk | hk
      · simp [hk, Kind.isWeight]
      · exact Kind.isWeight_false_of_solid hk
    constructor
    · rintro ⟨c, hc, hk, hm⟩
      obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hxs u v huv).1 ⟨c, hw c hc (Or.inl hk), hk, hm⟩
      exact ⟨c₂, hv c₂ hc₂ (Or.inr hk₂), hk₂, hm₂⟩
    · rintro ⟨c, hc, hk, hm⟩
      obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hxs u v huv).2 ⟨c, hw c hc (Or.inr hk), hk, hm⟩
      exact ⟨c₂, hv c₂ hc₂ (Or.inl hk₂), hk₂, hm₂⟩

private theorem oWeight1T_mem {x : Atom k n} {Γ : Graph k n} {t : Tracked k n}
    (ht : t ∈ oWeight1T x Γ) :
    ∃ p ∈ splitRegular x Γ.comps, t = ⟨n, ⟨p.1, p.2 * Γ.coeff⟩, id⟩ := by
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  exact ⟨p, hp, rfl⟩

private theorem oWeight1_spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain)
    {t : Tracked k n} (ht : t ∈ oWeight1T x Γ) :
    ∃ g' : Graph k n, t = ⟨n, g', id⟩ ∧ g'.Normal C ∧ g'.Plain ∧
      (∃ l d : ℕ, l + d = regL x Γ.comps ∧ g'.ord = Γ.ord + l ∧ wtL x g'.comps + d = wtL x Γ.comps ∧
        (∀ u, u ≠ x → wtL u g'.comps = wtL u Γ.comps) ∧ regL x g'.comps = 0) ∧
      (∀ c ∈ Γ.comps, c.label.isSome = true → c ∈ g'.comps) ∧
      (Γ.LabelFree → g'.LabelFree) ∧
      (∀ c ∈ Γ.comps, c.kind.isWeight = false → c ∈ g'.comps) := by
  obtain ⟨p, hp, rfl⟩ := oWeight1T_mem ht
  obtain ⟨l, d, h1, h2, h3, h4, h5, h6, h7, h8⟩ := splitRegular_spec x Γ.comps p hp
  have hr1 : ∀ c ∈ Γ.comps, c.kind.isWeight = false → c ∈ p.1 := by
    intro c hc hk
    apply h7 c hc
    unfold isRegAt
    cases hκ : c.kind <;> simp_all [Kind.isWeight, Kind.isReg]
  have hr2 : ∀ c' ∈ p.1, c' ∈ Γ.comps ∨ c'.kind.isWeight = true := by
    intro c' hc'
    rcases h6 c' hc' with h | ⟨c, hc, ch, -, -, rfl⟩
    · exact Or.inl h
    · exact Or.inr rfl
  set g' : Graph k n := ⟨p.1, p.2 * Γ.coeff⟩ with hg'
  refine ⟨g', rfl, normal_of_weightRel hN hP hr1 hr2 h8, ?_, ⟨l, d, h1, ?_, h3, h4, h5⟩, ?_, ?_,
    hr1⟩
  · intro c' hc'
    rcases h6 c' hc' with h | ⟨c, hc, ch, hreg, hk, rfl⟩
    · exact hP c' h
    · obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := hP c hc
      obtain ⟨-, -, hl⟩ := (isRegAt_iff x c).1 hreg
      refine ⟨h1', (fun ch' h => by cases h), (fun ch' d' h => by cases h), (fun h => by cases h),
        ⟨fun _ => ?_, fun h => by simp [hl] at h⟩⟩
      exact h5' (by simp [hk, Kind.isWeight])
  · change ordL p.1 - 2 * n = Γ.ord + l
    rw [h2, Graph.ord_eq]
    ring
  · intro c hc hs
    apply h7 c hc
    unfold isRegAt
    simp only [Bool.and_eq_false_iff]
    right
    simp [hs]
  · intro hlf c' hc'
    rcases h6 c' hc' with h | ⟨c, hc, ch, hreg, hk, rfl⟩
    · exact hlf c' h
    · obtain ⟨-, -, hl⟩ := (isRegAt_iff x c).1 hreg
      exact hl

end Weight1Op

/-! ## The canonical properties of the weight expansion -/

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

/-! ## The four operators of the weight expansion -/

section OpChain

variable {k n : ℕ}

/-- The chain of four operators behind a graph of `oWeightT`. -/
private theorem mem_oWeightT {x : Atom k n} {Γ : Graph k n} {t : Tracked k n}
    (ht : t ∈ oWeightT x Γ) :
    (¬ (Γ.comps.any (fun c => c.kind.isWL && c.x == x)) = true ∧
        t = Tracked.self Γ) ∨
    (∃ t₁ ∈ oWeight1T x Γ, ∃ t₂ ∈ oWeight2T (t₁.f x) t₁.g, ∃ t₃ ∈ oDotT t₂.g,
      ∃ t₄ ∈ oWeight1T ((t₃.f ∘ (t₂.f ∘ t₁.f)) x) t₃.g,
        t = ⟨t₄.nOut, t₄.g, t₄.f ∘ (t₃.f ∘ (t₂.f ∘ t₁.f))⟩) := by
  unfold oWeightT at ht
  split_ifs at ht with hc
  · right
    simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨u₃, hu₃, s, hs, rfl⟩ := ht
    obtain ⟨u₂, hu₂, s₃, hs₃, rfl⟩ := hu₃
    obtain ⟨u₁, hu₁, s₂, hs₂, rfl⟩ := hu₂
    exact ⟨u₁, hu₁, s₂, hs₂, s₃, hs₃, s, hs, rfl⟩
  · exact Or.inl ⟨hc, List.mem_singleton.1 ht⟩

end OpChain

/-! ## The canonical properties of the weight expansion: assembly -/

section CanonicalMain

variable {k n : ℕ}

private theorem wavedGraph_le_of_weightRel {g g' : Graph k n}
    (h1 : ∀ c ∈ g.comps, c.kind.isWeight = false → c ∈ g'.comps) :
    g.wavedGraph ≤ g'.wavedGraph := by
  intro u v h
  rw [Graph.wavedGraph, SimpleGraph.fromRel_adj] at h
  rw [Graph.wavedGraph, SimpleGraph.fromRel_adj]
  refine ⟨h.1, ?_⟩
  have key : ∀ a b, (∃ c ∈ g.comps, (∃ w, c.kind = .waved w) ∧ c.x = a ∧ c.y = b) →
      ∃ c ∈ g'.comps, (∃ w, c.kind = .waved w) ∧ c.x = a ∧ c.y = b := by
    rintro a b ⟨c, hc, ⟨w, hw⟩, h1', h2'⟩
    exact ⟨c, h1 c hc (by simp [hw, Kind.isWeight]), ⟨w, hw⟩, h1', h2'⟩
  rcases h.2 with h | h
  · exact Or.inl (key _ _ h)
  · exact Or.inr (key _ _ h)

private theorem final_op_spec {C : ℕ} {x₃ : Atom k n} {g₃ : Graph k n} (hN : g₃.Normal C)
    (hP : g₃.Plain)
    {t₄ : Tracked k n} (h : t₄ ∈ oWeight1T x₃ g₃) :
    ∃ g' : Graph k n, t₄ = ⟨n, g', id⟩ ∧ g'.Normal C ∧ g'.Plain ∧ g₃.ord ≤ g'.ord ∧
      g₃.wavedGraph ≤ g'.wavedGraph := by
  obtain ⟨g', rfl, hN', hP', ⟨l, d, -, hord, -⟩, -, -, hnw⟩ := oWeight1_spec hN hP h
  refine ⟨g', rfl, hN', hP', ?_, wavedGraph_le_of_weightRel hnw⟩
  rw [hord]
  have : (0 : ℤ) ≤ l := by positivity
  linarith

/-- The third operator on the self branch. -/
private theorem dot_self_op_spec {C : ℕ} {g₁ : Graph k n} (hN : g₁.Normal C) {t₃ : Tracked k n}
    (h : t₃ ∈ oDotT g₁) : t₃ = Tracked.self g₁ := by
  rw [oDotT_normal_self hN] at h
  exact List.mem_singleton.1 h

private theorem canonical_chain {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    (hP : Γ.Plain)
    (hx : x.isRight = true) {t₁ : Tracked k n} (h1 : t₁ ∈ oWeight1T x Γ)
    {t₂ : Tracked k t₁.nOut} (h2 : t₂ ∈ oWeight2T (t₁.f x) t₁.g)
    {t₃ : Tracked k t₂.nOut} (h3 : t₃ ∈ oDotT t₂.g)
    {t₄ : Tracked k t₃.nOut} (h4 : t₄ ∈ oWeight1T ((t₃.f ∘ (t₂.f ∘ t₁.f)) x) t₃.g) :
    t₄.g.Normal (2 * C + 16) ∧ t₄.g.Plain ∧ Γ.ord ≤ t₄.g.ord ∧
      ∀ u, (∀ v, (t₄.f ∘ (t₃.f ∘ (t₂.f ∘ t₁.f))) v ≠ u) →
        t₄.g.wavedGraph.Reachable ((t₄.f ∘ (t₃.f ∘ (t₂.f ∘ t₁.f))) x) u := by
  obtain ⟨g₁, rfl, hN₁, hP₁, ⟨l, d, -, hord₁, -⟩, -, -, -⟩ := oWeight1_spec hN hP h1
  have hΓg₁ : Γ.ord ≤ g₁.ord := by
    rw [hord₁]
    have : (0 : ℤ) ≤ l := by positivity
    linarith
  -- the second and third operators
  have key : ∃ C' : ℕ, C' ≤ 2 * C + 16 ∧ t₃.g.Normal C' ∧ t₃.g.Plain ∧ g₁.ord ≤ t₃.g.ord ∧
      ∀ u, (∀ v, (t₃.f ∘ t₂.f) v ≠ u) → t₃.g.wavedGraph.Reachable ((t₃.f ∘ t₂.f) x) u := by
    rcases oWeight2T_cases hN₁ hP₁ hx t₂ h2 with hO | hself
    · obtain ⟨hN₃, hP₃, hord₃, hnew₃⟩ := dot_op_spec hO t₃ h3
      exact ⟨2 * (C + 5), by omega, hN₃, hP₃, hO.ord.trans hord₃, hnew₃⟩
    · subst hself
      have := dot_self_op_spec hN₁ h3
      subst this
      exact ⟨C, by omega, hN₁, hP₁, le_rfl, fun u hu => absurd rfl (hu u)⟩
  obtain ⟨C', hC', hN₃, hP₃, hord₃, hnew₃⟩ := key
  obtain ⟨g₄, rfl, hN₄, hP₄, hord₄, hw₄⟩ := final_op_spec hN₃ hP₃ h4
  refine ⟨hN₄.mono hC', hP₄, hΓg₁.trans (hord₃.trans hord₄), ?_⟩
  intro u hu
  exact (hnew₃ u hu).mono hw₄

end CanonicalMain

section MergeWt

variable {k n : ℕ}

end MergeWt

section MergeFormula

variable {k n : ℕ}

end MergeFormula

section MergeE1

variable {k n : ℕ}

end MergeE1

section MergeE2

variable {k n : ℕ}

end MergeE2

section Delta0

variable {V : Type*} [DecidableEq V]

end Delta0

section WtLists

variable {V : Type*} [DecidableEq V]

end WtLists

section WtLift

variable {k n : ℕ}

end WtLift

section T3Data

variable {k n : ℕ}

end T3Data

section Classify

variable {k m : ℕ}

end Classify

section FinalOp

variable {k n : ℕ}

end FinalOp

section TermOrders

variable {k n : ℕ}

end TermOrders

section WLTerm3

variable {k n : ℕ}

end WLTerm3

section WLCore

variable {k n : ℕ}

end WLCore

section Labelled

variable {k n : ℕ}

end Labelled

section TermWL

variable {k n : ℕ}

end TermWL

section TermConj

variable {k n : ℕ}

end TermConj

section WeightLemma

variable {k n : ℕ}

end WeightLemma

/-! ## Products of component factors -/

section Values

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The product of the factors of the components `cs`. -/
private def pv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  (cs.map (Comp.val D σ)).prod

/-- The product of the factors of the random components of `cs`. -/
private def rv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  ((cs.filter fun c => c.kind.isRandom).map (Comp.val D σ)).prod

/-- The product of the factors of the deterministic components of `cs`. -/
private def dv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  ((cs.filter fun c => !c.kind.isRandom).map (Comp.val D σ)).prod

variable {V W : Type*} (D : Data ι) (σ : V → ι)

@[simp] private theorem pv_nil : pv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] private theorem pv_cons (c : Comp V) (cs : List (Comp V)) :
    pv D σ (c :: cs) = Comp.val D σ c * pv D σ cs := by
  simp [pv]

@[simp] private theorem pv_append (cs cs' : List (Comp V)) :
    pv D σ (cs ++ cs') = pv D σ cs * pv D σ cs' := by
  simp [pv]

@[simp] private theorem rv_nil : rv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] private theorem rv_cons (c : Comp V) (cs : List (Comp V)) :
    rv D σ (c :: cs) = (if c.kind.isRandom then Comp.val D σ c else 1) * rv D σ cs := by
  unfold rv
  by_cases h : c.kind.isRandom <;> simp [h]

@[simp] private theorem rv_append (cs cs' : List (Comp V)) :
    rv D σ (cs ++ cs') = rv D σ cs * rv D σ cs' := by
  simp [rv]

@[simp] private theorem dv_nil : dv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] private theorem dv_cons (c : Comp V) (cs : List (Comp V)) :
    dv D σ (c :: cs) = (if c.kind.isRandom then 1 else Comp.val D σ c) * dv D σ cs := by
  unfold dv
  by_cases h : c.kind.isRandom <;> simp [h]

@[simp] private theorem dv_append (cs cs' : List (Comp V)) :
    dv D σ (cs ++ cs') = dv D σ cs * dv D σ cs' := by
  simp [dv]

private theorem pv_eq (cs : List (Comp V)) : pv D σ cs = dv D σ cs * rv D σ cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [pv_cons, dv_cons, rv_cons, ih]
    split_ifs <;> ring

private theorem val_map (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

private theorem rv_map (σ : W → ι) (f : V → W) (cs : List (Comp V)) :
    rv D σ (cs.map (Comp.map f)) = rv D (σ ∘ f) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, rv_cons, rv_cons, ih, val_map]; rfl

private theorem dv_map (σ : W → ι) (f : V → W) (cs : List (Comp V)) :
    dv D σ (cs.map (Comp.map f)) = dv D (σ ∘ f) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, dv_cons, dv_cons, ih, val_map]; rfl

@[simp] private theorem mkC_kind (κ : Kind) (u v : V) : (mkC κ u v).kind = κ := rfl

private theorem val_solidC [DecidableEq V] (ch : Charge) (u v : V) :
    Comp.val D σ (solidC ch u v) = ch.apply (D.Gm ∅ (σ u) (σ v)) := by
  unfold solidC
  split_ifs with h
  · subst h
    simp [mkC, Comp.val]
  · simp [mkC, Comp.val]

end Values

/-! ## Atom labellings of graphs with new atoms -/

section Labellings

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n j : ℕ}

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem elim_append_liftA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι)
    (u : Atom k n) : Sum.elim e (Fin.append s a) (liftA j u) = Sum.elim e s u := by
  rcases u with i | i <;> simp [liftA, Fin.append_left]

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem elim_append_newA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι)
    (i : Fin j) : Sum.elim e (Fin.append s a) (newA i) = a i := by
  simp [newA, Fin.append_right]

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem elim_append_comp_liftA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι) :
    Sum.elim e (Fin.append s a) ∘ liftA j = Sum.elim e s := by
  funext u
  simp

/-- The value of a graph with `j` more internal atoms, the labels of the new atoms summed
last. -/
private theorem valR_split {Ω : Type} (g : Graph k (n + j)) (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) :
    g.valR PF D e ω =
      ∑ s : Fin n → ι, ∑ a : Fin j → ι, g.termR PF D (Sum.elim e (Fin.append s a)) ω := by
  unfold Graph.valR
  rw [← (Fin.appendEquiv n j).sum_comp, Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] in
/-- A sum over the labellings of one atom is a sum over `ι`. -/
private theorem sum_fin1 (f : (Fin 1 → ι) → ℂ) : ∑ a, f a = ∑ α, f ![α] := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun a => ?_
  congr 1
  funext i
  fin_cases i
  rfl

omit [DecidableEq ι] in
/-- A sum over the labellings of two atoms is a double sum. -/
private theorem sum_fin2 (f : (Fin 2 → ι) → ℂ) : ∑ a, f a = ∑ α, ∑ β, f ![α, β] := by
  rw [← (piFinTwoEquiv fun _ => ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

end Labellings

/-! ## Terms of unlabelled graphs and of graphs with one label `Q_u` -/

section TermR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type} {k N : ℕ}

private theorem dedup_singleton {α : Type*} [DecidableEq α] (l : List α) (a : α)
    (h1 : ∀ x ∈ l, x = a) (h2 : a ∈ l) : l.dedup = [a] := by
  have hnd := List.nodup_dedup l
  have hmem : ∀ x, x ∈ l.dedup ↔ x ∈ l := fun x => List.mem_dedup
  cases hd : l.dedup with
  | nil => exact absurd ((hmem a).2 h2) (by rw [hd]; simp)
  | cons x rest =>
    rw [hd] at hnd
    have hx : x = a := h1 x ((hmem x).1 (by rw [hd]; simp))
    have hrest : rest = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro y hy
      have hya : y = a := h1 y ((hmem y).1 (by rw [hd]; simp [hy]))
      exact (List.nodup_cons.1 hnd).1 (by rw [hx, ← hya]; exact hy)
    rw [hrest, hx]

/-- The term of a graph without labels. -/
private theorem termR_unl (g : Graph k N) (h : ∀ c ∈ g.comps, c.label = none)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k N → ι) (ω : Ω) :
    g.termR PF D σ ω = g.coeff.eval (D ω).m * pv (D ω) σ g.comps := by
  have h1 : g.comps.filter (fun c => c.label.isNone) = g.comps :=
    List.filter_eq_self.2 fun c hc => by simp [h c hc]
  have h2 : g.labels = [] := by
    unfold Graph.labels
    rw [List.filterMap_eq_nil_iff.2 fun c hc => h c hc]
    rfl
  simp [Graph.termR, h1, h2, pv]

private theorem labelQs_none {V : Type*} (D₀ : Data ι) (σ : V → ι) (u : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (((labelQs u cs).filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod = dv D₀ σ cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hc := h c (List.mem_cons_self ..)
    simp only [labelQs, List.map_cons, Comp.labelQ] at ih' ⊢
    by_cases hr : c.kind.isRandom
    · simp [hr, ih']
    · simp [hr, hc, ih']

private theorem labelQs_some {V : Type*} [DecidableEq V] (D₀ : Data ι) (σ : V → ι) (u : V)
    (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (((labelQs u cs).filter fun c => decide (c.label = some (.Q, u))).map
      (Comp.val D₀ σ)).prod = rv D₀ σ cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hc := h c (List.mem_cons_self ..)
    simp only [labelQs, List.map_cons, Comp.labelQ] at ih' ⊢
    by_cases hr : c.kind.isRandom
    · simp only [hr, ite_true, List.filter_cons, decide_true, rv_cons, List.map_cons,
        List.prod_cons, ih']
      rfl
    · simp [hr, hc, ih']

private theorem labelQs_labels {V : Type*} [DecidableEq V] (u : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) (hr : ∃ c ∈ cs, c.kind.isRandom = true) :
    ((labelQs u cs).filterMap Comp.label).dedup = [(.Q, u)] := by
  apply dedup_singleton
  · intro l hl
    obtain ⟨c', hc', hl'⟩ := List.mem_filterMap.1 hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    unfold Comp.labelQ at hl'
    split_ifs at hl' with hcr
    · exact (Option.some.inj hl').symm
    · rw [h c hc] at hl'
      exact absurd hl' (by simp)
  · obtain ⟨c, hc, hcr⟩ := hr
    exact List.mem_filterMap.2 ⟨Comp.labelQ u c, List.mem_map.2 ⟨c, hc, rfl⟩,
      by simp [Comp.labelQ, hcr]⟩

/-- The term of a graph `𝒢₀ Q_u(𝒢₁)` whose labelled part is `labelQs u cs`. -/
private theorem termR_Q (u : Atom k N) (cs ds : List (Comp (Atom k N))) (d : Coeff)
    (hcs : ∀ c ∈ cs, c.label = none) (hds : ∀ c ∈ ds, c.label = none)
    (hr : ∃ c ∈ cs, c.kind.isRandom = true)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k N → ι) (ω : Ω) :
    (⟨labelQs u cs ++ ds, d⟩ : Graph k N).termR PF D σ ω =
      d.eval (D ω).m * dv (D ω) σ cs * pv (D ω) σ ds *
        PF.op .Q (σ u) (fun ω' => rv (D ω') σ cs) ω := by
  have hl : (⟨labelQs u cs ++ ds, d⟩ : Graph k N).labels = [(.Q, u)] := by
    unfold Graph.labels
    rw [List.filterMap_append, List.filterMap_eq_nil_iff.2 fun c hc => hds c hc, List.append_nil]
    exact labelQs_labels u cs hcs hr
  have h1 : ∀ D₀ : Data ι, ((ds.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod =
      pv D₀ σ ds := fun D₀ => by
    rw [List.filter_eq_self.2 fun c hc => by simp [hds c hc]]
    rfl
  have h2 : ds.filter (fun c => decide (c.label = some (.Q, u))) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simp [hds c hc]
  simp only [Graph.termR, hl, List.filter_append, List.map_append, List.prod_append,
    labelQs_none _ _ u cs hcs, h1, h2, List.map_nil, List.prod_nil, mul_one, List.map_cons,
    List.prod_cons, labelQs_some _ _ u cs hcs]
  ring

end TermR

/-! ## Closure of the test functions and linearity of `P_x` -/

section TestClosure

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem test_mul' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω * g ω :=
  A.test_mul f g hf hg

private theorem test_add' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω + g ω :=
  A.test_add f g hf hg

private theorem test_const' (c : ℂ) : A.Test fun _ => c := A.test_const c

private theorem test_sub' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω - g ω := by
  have e : (fun ω => f ω - g ω) = fun ω => f ω + (-1 : ℂ) * g ω := funext fun ω => by ring
  rw [e]
  exact test_add' A hf (test_mul' A (test_const' A _) hg)

private theorem test_star' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => star (f ω) :=
  A.test_star f hf

private theorem test_G (a b : ι) : A.Test fun ω => A.G ω a b := by
  have h := A.test_entry a b
  have e : (fun ω => (D ω).Gm ∅ a b) = fun ω => A.G ω a b :=
    funext fun ω => by rw [A.data_G]; rfl
  rwa [e] at h

private theorem test_dh' (a b : ι) {F : Ω → ℂ} (hF : A.Test F) :
    A.Test fun ω => A.dh a b F ω :=
  A.test_dh a b F hF

private theorem test_listProd' {β : Type*} (l : List β) {f : β → Ω → ℂ}
    (h : ∀ q ∈ l, A.Test (f q)) :
    A.Test fun ω => (l.map fun q => f q ω).prod := by
  induction l with
  | nil => simpa using test_const' A 1
  | cons y l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact test_mul' A (h y (List.mem_cons_self ..)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

end TestClosure

section Aux

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem P_add' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω + g ω) ω = PF.P x f ω + PF.P x g ω :=
  congrFun (A.laws.add x f g hf hg) ω

private theorem P_cmul' {f : Ω → ℂ} (c : ℂ) (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => c * f ω) ω = c * PF.P x f ω :=
  congrFun (A.laws.smul x c f hf) ω

include A in
private theorem P_zero' (x : ι) (ω : Ω) : PF.P x (fun _ => 0) ω = 0 := by
  have h := P_cmul' A 0 (A.laws.good_const 0) x ω
  simpa using h

private theorem P_neg' {f : Ω → ℂ} (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => -f ω) ω = -PF.P x f ω := by
  have h := P_cmul' A (-1) hf x ω
  simpa using h

omit [Fintype ι] [DecidableEq ι] in
private theorem P_congr' {f g : Ω → ℂ} (h : ∀ ω, f ω = g ω) (x : ι) :
    PF.P x f = PF.P x g := by
  rw [funext h]

private theorem P_listSum' {β : Type*} (l : List β) {f : β → Ω → ℂ} (h : ∀ q ∈ l, A.Good (f q))
    (x : ι) (ω : Ω) :
    PF.P x (fun ω => (l.map fun q => f q ω).sum) ω = (l.map fun q => PF.P x (f q) ω).sum := by
  induction l with
  | nil => simpa using P_zero' A x ω
  | cons y l ih =>
    have hg : A.Good fun ω => (l.map fun q => f q ω).sum := by
      clear ih
      induction l with
      | nil => simpa using A.laws.good_const 0
      | cons z l ih' =>
        simp only [List.map_cons, List.sum_cons]
        exact A.laws.good_add _ _ (h z (by simp)) (ih' fun q hq => h q (by
          simp only [List.mem_cons] at hq ⊢; tauto))
    simp only [List.map_cons, List.sum_cons]
    rw [P_add' A (h y (List.mem_cons_self ..)) hg, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

private theorem dh_mul' (a b : ι) {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.dh a b (fun ω => f ω * g ω) = fun ω => A.dh a b f ω * g ω + f ω * A.dh a b g ω :=
  A.dh_mul a b f g hf hg

omit [Fintype ι] [DecidableEq ι] in
private theorem Q_apply' (x : ι) (f : Ω → ℂ) (ω : Ω) :
    PF.op .Q x f ω = f ω - PF.P x f ω := rfl

end Aux

/-! ## Factors of components under the model relations -/

/-- A component without minor that is not a `(G_{xx})⁻¹` or `W_D` weight. -/
private def basB {V : Type*} (c : Comp V) : Bool :=
  c.minor.isEmpty &&
    match c.kind with
    | .inv _ | .wD _ _ => false
    | _ => true

private theorem basB_map {V W : Type*} (f : V → W) (c : Comp V) : basB (c.map f) = basB c := by
  simp [basB, Comp.map]

private theorem basB_of_plain {V : Type*} {c : Comp V} (h : c.isPlainB = true) :
    basB c = true ∧ c.label = none := by
  rcases c with ⟨κ, x, y, mi, l⟩
  simp only [Comp.isPlainB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, h2⟩
  rw [basB, h1, Bool.true_and]
  exact h3

section ModelVal

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem Gm_eq (ω : Ω) (a b : ι) : (D ω).Gm ∅ a b = A.G ω a b := by
  rw [A.data_G]
  rfl

private theorem m_eq (ω : Ω) : (D ω).m = msc A.z := A.data_m ω

private theorem S_eq (ω : Ω) (a b : ι) : (D ω).S a b = (A.S a b : ℂ) := by
  rw [A.data_S]
  rfl

private theorem val_G {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.G ch) x y) = ch.apply (A.G ω (σ x) (σ y)) := by
  simp [mkC, Comp.val, Gm_eq A]

private theorem val_weight {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.weight ch) x y) = ch.apply (A.G ω (σ x) (σ x)) := by
  simp [mkC, Comp.val, Gm_eq A]

private theorem val_light {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.light ch) x y) = ch.apply (A.G ω (σ x) (σ x) - msc A.z) := by
  simp [mkC, Comp.val, Gm_eq A, m_eq A]

private theorem val_s {V : Type*} (σ : V → ι) (ω : Ω) (x y : V) :
    Comp.val (D ω) σ (mkC (.waved .s) x y) = (A.S (σ x) (σ y) : ℂ) := by
  simp [mkC, Comp.val, S_eq A]

private theorem val_Sp {V : Type*} (σ : V → ι) (ω : Ω) (x y : V) :
    Comp.val (D ω) σ (mkC (.waved .plus) x y) = (D ω).Sp (σ x) (σ y) := by
  simp [mkC, Comp.val]

private theorem val_solid {V : Type*} [DecidableEq V] (σ : V → ι) (ω : Ω) (ch : Charge)
    (x y : V) : Comp.val (D ω) σ (solidC ch x y) = ch.apply (A.G ω (σ x) (σ y)) := by
  rw [val_solidC, Gm_eq A]

private theorem dh_G' (a b x y : ι) :
    A.dh a b (fun ω => A.G ω x y) = fun ω => -(A.G ω x a * A.G ω b y) :=
  A.dh_green a b x y

private theorem dh_starG' (a b x y : ι) :
    A.dh a b (fun ω => star (A.G ω x y)) = fun ω => -(star (A.G ω x b) * star (A.G ω a y)) :=
  A.dh_conj_green a b x y

/-- The factor of a random component without minor is a test function. -/
private theorem val_test {V : Type*} (σ : V → ι) (c : Comp V) (hb : basB c = true)
    (hr : c.kind.isRandom = true) : A.Test fun ω => Comp.val (D ω) σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  simp only [basB, Bool.and_eq_true, List.isEmpty_iff] at hb
  obtain ⟨rfl, hk⟩ := hb
  rw [show (fun ω => Comp.val (D ω) σ ⟨κ, x, y, [], l⟩) =
    fun ω => Comp.val (D ω) σ (mkC κ x y) from rfl]
  cases κ with
  | G ch =>
    simp only [val_G A]
    cases ch
    · exact test_G A _ _
    · exact test_star' A (test_G A _ _)
  | weight ch =>
    simp only [val_weight A]
    cases ch
    · exact test_G A _ _
    · exact test_star' A (test_G A _ _)
  | light ch =>
    simp only [val_light A]
    cases ch
    · exact test_sub' A (test_G A _ _) (test_const' A _)
    · exact test_star' A (test_sub' A (test_G A _ _) (test_const' A _))
  | inv ch => simp at hk
  | wD ch d => simp at hk
  | _ => simp [Kind.isRandom] at hr

/-- The product of the random factors of components without minors is a test function. -/
private theorem rv_test {V : Type*} (σ : V → ι) (cs : List (Comp V))
    (hb : ∀ c ∈ cs, basB c = true) : A.Test fun ω => rv (D ω) σ cs := by
  induction cs with
  | nil => simpa using test_const' A 1
  | cons c cs ih =>
    simp only [rv_cons]
    refine test_mul' A ?_ (ih fun c hc => hb c (List.mem_cons_of_mem _ hc))
    by_cases hr : c.kind.isRandom
    · simp only [hr, ite_true]
      exact val_test A σ c (hb c (List.mem_cons_self ..)) hr
    · simp only [hr]
      exact test_const' A 1

/-- `-∂_{h_{pq}}` of the factor of a random component is the product of the factors of
`Comp.dPieces p q` ([I, (3.8)]). -/
private theorem dPieces_spec {V : Type*} [DecidableEq V] (σ : V → ι) (p q : V) (c : Comp V)
    (hb : basB c = true) (hr : c.kind.isRandom = true) :
    ∃ ps, c.dPieces p q = some ps ∧ (∀ c' ∈ ps, basB c' = true ∧ c'.label = none ∧
      c'.kind.isRandom = true) ∧
      A.dh (σ p) (σ q) (fun ω => Comp.val (D ω) σ c) = fun ω => -(rv (D ω) σ ps) := by
  rcases c with ⟨κ, x, y, mi, l⟩
  simp only [basB, Bool.and_eq_true, List.isEmpty_iff] at hb
  obtain ⟨rfl, hk⟩ := hb
  rw [show (fun ω => Comp.val (D ω) σ ⟨κ, x, y, [], l⟩) =
    fun ω => Comp.val (D ω) σ (mkC κ x y) from rfl]
  have hsol : ∀ (ch : Charge) (u v : V), basB (solidC ch u v) = true ∧
      (solidC ch u v).label = none ∧ (solidC ch u v).kind.isRandom = true := by
    intro ch u v
    unfold solidC
    split_ifs <;> simp [basB, mkC, Kind.isRandom]
  have hG : ∀ a b, (fun ω => A.G ω a b) = fun ω => green (A.H ω) A.z a b := fun _ _ => rfl
  cases κ with
  | G ch =>
    cases ch
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_G A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true, mul_one,
        val_solid A, dh_G' A]
      funext ω; simp [Kind.isWeight]
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_G A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true, mul_one,
        val_solid A, dh_starG' A]
      funext ω; simp [Kind.isWeight]
  | weight ch =>
    cases ch
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_weight A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, dh_G' A, Kind.isWeight, ite_true]
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_weight A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, dh_starG' A, Kind.isWeight, ite_true]
  | light ch =>
    have hdc : ∀ (F : Ω → ℂ) (a : ℂ), A.Test F →
        A.dh (σ p) (σ q) (fun ω => F ω - a) = A.dh (σ p) (σ q) F := by
      intro F a hF
      rw [show (fun ω => F ω - a) = F + fun _ => -a from funext fun ω => by simp [sub_eq_add_neg],
        A.dh_add _ _ _ _ hF (A.test_const _), A.dh_const, add_zero]
    cases ch
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_light A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, Kind.isWeight, ite_true]
      rw [hdc _ _ (test_G A _ _), dh_G' A]
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_light A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, Kind.isWeight, ite_true, star_sub]
      rw [hdc _ _ (test_star' A (test_G A _ _)), dh_starG' A]
  | inv ch => simp at hk
  | wD ch d => simp at hk
  | _ => simp [Kind.isRandom] at hr

end ModelVal

private theorem dv_rand {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} (D₀ : Data ι)
    (σ : V → ι) (ps : List (Comp V)) (h : ∀ c ∈ ps, c.kind.isRandom = true) : dv D₀ σ ps = 1 := by
  induction ps with
  | nil => rfl
  | cons c ps ih =>
    rw [dv_cons, ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]
    simp [h c (List.mem_cons_self ..)]

private theorem dTerms_cons {V : Type*} [DecidableEq V] (p q : V) (c : Comp V)
    (cs : List (Comp V)) :
    dTerms p q (c :: cs) =
      ((c.dPieces p q).map fun ps => cs ++ ps).toList ++ (dTerms p q cs).map (c :: ·) := by
  unfold dTerms
  erw [List.finRange_succ]
  rw [List.filterMap_cons, List.filterMap_map, List.map_filterMap]
  cases h : c.dPieces p q <;> simp [h, Option.map_map, Function.comp_def]

private theorem dPieces_none {V : Type*} [DecidableEq V] (p q : V) (c : Comp V)
    (hb : basB c = true) (hr : c.kind.isRandom = false) : c.dPieces p q = none := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> simp_all [Comp.dPieces, Kind.isRandom]

section DTerms

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-- The product rule behind `dTerms`: the sum of the random parts of the graphs of
`dTerms p q cs` is `-∂_{h_{pq}}` of the random part of `cs`; the deterministic parts are those
of `cs`. -/
private theorem dTerms_spec {V : Type*} [DecidableEq V] (σ : V → ι) (p q : V)
    (cs : List (Comp V)) (hb : ∀ c ∈ cs, basB c = true ∧ c.label = none) :
    (∀ d ∈ dTerms p q cs, (∀ c ∈ d, basB c = true ∧ c.label = none) ∧
      ∀ D₀ : Data ι, dv D₀ σ d = dv D₀ σ cs) ∧
    ∀ ω, ((dTerms p q cs).map fun d => rv (D ω) σ d).sum =
      -A.dh (σ p) (σ q) (fun ω' => rv (D ω') σ cs) ω := by
  induction cs with
  | nil =>
    refine ⟨by simp [dTerms], fun ω => ?_⟩
    simp only [dTerms, List.length_nil, List.finRange_zero, List.filterMap_nil, List.map_nil,
      List.sum_nil]
    rw [show (fun ω' => rv (D ω') σ ([] : List (Comp V))) = fun _ => (1 : ℂ) from rfl,
      A.dh_const]
    simp
  | cons c cs ih =>
    have hbc := hb c (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih fun c hc => hb c (List.mem_cons_of_mem _ hc)
    have hcs : ∀ c ∈ cs, basB c = true := fun c hc => (hb c (List.mem_cons_of_mem _ hc)).1
    by_cases hr : c.kind.isRandom
    · obtain ⟨ps, hps, hps1, hps2⟩ := dPieces_spec A σ p q c hbc.1 hr
      rw [dTerms_cons, hps]
      refine ⟨?_, fun ω => ?_⟩
      · intro d hd
        simp only [Option.map_some, Option.toList_some, List.singleton_append, List.mem_cons,
          List.mem_map] at hd
        rcases hd with rfl | ⟨d', hd', rfl⟩
        · refine ⟨fun c' hc' => ?_, fun D₀ => ?_⟩
          · rcases List.mem_append.1 hc' with h | h
            · exact hb c' (List.mem_cons_of_mem _ h)
            · exact ⟨(hps1 c' h).1, (hps1 c' h).2.1⟩
          · rw [dv_append, dv_rand D₀ σ ps fun c' hc' => (hps1 c' hc').2.2, dv_cons]
            simp [hr]
        · obtain ⟨h1, h2⟩ := ih1 d' hd'
          refine ⟨fun c' hc' => ?_, fun D₀ => ?_⟩
          · rcases List.mem_cons.1 hc' with rfl | h
            · exact hbc
            · exact h1 c' h
          · rw [dv_cons, dv_cons, h2]
      · simp only [Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
          List.sum_cons, List.map_map, Function.comp_def, rv_cons, rv_append, hr, ite_true]
        rw [dh_mul' A _ _ (val_test A σ c hbc.1 hr) (rv_test A σ cs hcs)]
        rw [show ((dTerms p q cs).map fun d => Comp.val (D ω) σ c * rv (D ω) σ d).sum =
            Comp.val (D ω) σ c * ((dTerms p q cs).map fun d => rv (D ω) σ d).sum by
          rw [List.sum_map_mul_left], ih2 ω, hps2]
        simp only []
        ring
    · have hn := dPieces_none p q c hbc.1 (by simpa using hr)
      rw [dTerms_cons, hn]
      refine ⟨?_, fun ω => ?_⟩
      · intro d hd
        simp only [Option.map_none, Option.toList_none, List.nil_append, List.mem_map] at hd
        obtain ⟨d', hd', rfl⟩ := hd
        obtain ⟨h1, h2⟩ := ih1 d' hd'
        refine ⟨fun c' hc' => ?_, fun D₀ => ?_⟩
        · rcases List.mem_cons.1 hc' with rfl | h
          · exact hbc
          · exact h1 c' h
        · rw [dv_cons, dv_cons, h2]
      · simp only [Option.map_none, Option.toList_none, List.nil_append, List.map_map,
          Function.comp_def, rv_cons, hr, Bool.false_eq_true, ite_false, one_mul]
        exact ih2 ω

end DTerms

/-! ## Values of tracked formal sums, one labelling of the input atoms at a time -/

section Sums

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) {k n : ℕ}
  (e : Fin k → ι) (ω : Ω)

/-- The tracked graph with one new atom. -/
private def t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
  ⟨n + 1, ⟨cs, d⟩, liftA 1⟩

/-- The tracked graph with two new atoms. -/
private def t2 (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) : Tracked k n :=
  ⟨n + 2, ⟨cs, d⟩, liftA 2⟩

/-- The value of a tracked formal sum. -/
private def S (E : TExpansion k n) : ℂ := E.forget.valR PF D e ω

/-- The term of a graph at the labelling `s` of the internal atoms. -/
private def T0 (g : Graph k n) (s : Fin n → ι) : ℂ := g.termR PF D (Sum.elim e s) ω

/-- The terms of a graph with one new atom at the labelling `s` of the internal atoms of the input
graph, summed over the label of the new atom. -/
private def T1 (g : Graph k (n + 1)) (s : Fin n → ι) : ℂ :=
  ∑ α, g.termR PF D (Sum.elim e (Fin.append s ![α])) ω

/-- The terms of a graph with two new atoms at the labelling `s` of the internal atoms of the input
graph, summed over the labels of the new atoms. -/
private def T2 (g : Graph k (n + 2)) (s : Fin n → ι) : ℂ :=
  ∑ α, ∑ β, g.termR PF D (Sum.elim e (Fin.append s ![α, β])) ω

private theorem S_append (E₁ E₂ : TExpansion k n) :
    S PF D e ω (E₁ ++ E₂) = S PF D e ω E₁ + S PF D e ω E₂ := by
  simp [S, TExpansion.forget, Expansion.valR]

private theorem S_nil : S PF D e ω ([] : TExpansion k n) = 0 := by
  simp [S, TExpansion.forget, Expansion.valR]

private theorem S_cons (t : Tracked k n) (E : TExpansion k n) :
    S PF D e ω (t :: E) = t.g.valR PF D e ω + S PF D e ω E := by
  simp [S, TExpansion.forget, Expansion.valR]

private theorem valR_T0 (g : Graph k n) : g.valR PF D e ω = ∑ s, T0 PF D e ω g s := rfl

private theorem valR_T1 (g : Graph k (n + 1)) : g.valR PF D e ω = ∑ s, T1 PF D e ω g s := by
  rw [valR_split]
  exact Finset.sum_congr rfl fun s _ => sum_fin1 _

private theorem valR_T2 (g : Graph k (n + 2)) : g.valR PF D e ω = ∑ s, T2 PF D e ω g s := by
  rw [valR_split]
  exact Finset.sum_congr rfl fun s _ => sum_fin2 _

omit [DecidableEq ι] in
private theorem list_sum_comm {β : Type*} (l : List β) (f : β → (Fin n → ι) → ℂ) :
    (l.map fun j => ∑ s, f j s).sum = ∑ s, (l.map fun j => f j s).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.sum_add_distrib]

private theorem S_map_t1 {β : Type*} (l : List β) (G : β → List (Comp (Atom k (n + 1))))
    (d : β → Coeff) :
    S PF D e ω (l.map fun j => t1 (G j) (d j)) =
      ∑ s, (l.map fun j => T1 PF D e ω ⟨G j, d j⟩ s).sum := by
  rw [← list_sum_comm]
  simp [S, TExpansion.forget, Expansion.valR, t1, List.map_map, Function.comp_def, valR_T1]

private theorem S_map_t2 {β : Type*} (l : List β) (G : β → List (Comp (Atom k (n + 2))))
    (d : β → Coeff) :
    S PF D e ω (l.map fun j => t2 (G j) (d j)) =
      ∑ s, (l.map fun j => T2 PF D e ω ⟨G j, d j⟩ s).sum := by
  rw [← list_sum_comm]
  simp [S, TExpansion.forget, Expansion.valR, t2, List.map_map, Function.comp_def, valR_T2]

private theorem S_cons_t0 (g : Graph k n) (f : Atom k n → Atom k n) (E : TExpansion k n) :
    S PF D e ω (⟨n, g, f⟩ :: E) = ∑ s, T0 PF D e ω g s + S PF D e ω E := by
  rw [S_cons]
  rfl

private theorem S_cons_t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) (E : TExpansion k n) :
    S PF D e ω (t1 cs d :: E) = ∑ s, T1 PF D e ω ⟨cs, d⟩ s + S PF D e ω E := by
  rw [S_cons, t1, valR_T1]

private theorem S_cons_t2 (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) (E : TExpansion k n) :
    S PF D e ω (t2 cs d :: E) = ∑ s, T2 PF D e ω ⟨cs, d⟩ s + S PF D e ω E := by
  rw [S_cons, t2, valR_T2]

end Sums

/-! ## Splitting `P_u = 1 - Q_u` -/

/-- A list of components without labels. -/
private def Unl {V : Type*} (cs : List (Comp V)) : Prop := ∀ c ∈ cs, c.label = none

private theorem Unl_append {V : Type*} {cs cs' : List (Comp V)} :
    Unl (cs ++ cs') ↔ Unl cs ∧ Unl cs' := by
  simp [Unl, or_imp, forall_and]

private theorem Unl_nil {V : Type*} : Unl ([] : List (Comp V)) := by simp [Unl]

private theorem Unl_liftCs {k n : ℕ} (j : ℕ) {cs : List (Comp (Atom k n))} (h : Unl cs) :
    Unl (liftCs j cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  simp [Comp.map, h c' hc']

section PairLemmas

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k N : ℕ}

/-- An unlabelled graph and its `Q_u` copy with the opposite coefficient: `P_u` of the random
part. -/
private theorem termR_pair (u : Atom k N) (cs ds cs₁ : List (Comp (Atom k N))) (d d' : Coeff)
    (hcs : Unl cs) (hds : Unl ds) (hcs₁ : Unl cs₁) (hr : ∃ c ∈ cs, c.kind.isRandom = true)
    (hd : ∀ z, d'.eval z = -d.eval z)
    (hp : ∀ (D₀ : Data ι) (σ₀ : Atom k N → ι), pv D₀ σ₀ cs₁ = pv D₀ σ₀ cs * pv D₀ σ₀ ds)
    (σ : Atom k N → ι) (ω : Ω) :
    (⟨cs₁, d⟩ : Graph k N).termR PF D σ ω + (⟨labelQs u cs ++ ds, d'⟩ : Graph k N).termR PF D σ ω =
      d.eval (D ω).m * dv (D ω) σ cs * pv (D ω) σ ds *
        PF.P (σ u) (fun ω' => rv (D ω') σ cs) ω := by
  rw [termR_unl (⟨cs₁, d⟩ : Graph k N) hcs₁, termR_Q u cs ds d' hcs hds hr, hd, hp, pv_eq _ _ cs,
    Q_apply']
  ring

end PairLemmas

section LiftVal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n j : ℕ} (D₀ : Data ι)

private theorem rv_liftCs (σ : Atom k (n + j) → ι) (cs : List (Comp (Atom k n))) :
    rv D₀ σ (liftCs j cs) = rv D₀ (σ ∘ liftA j) cs := rv_map _ _ _ _

private theorem dv_liftCs (σ : Atom k (n + j) → ι) (cs : List (Comp (Atom k n))) :
    dv D₀ σ (liftCs j cs) = dv D₀ (σ ∘ liftA j) cs := dv_map _ _ _ _

end LiftVal

private theorem ceval_cm (z : ℂ) : Coeff.eval z cm = z := by simp [Coeff.eval, cm, CVar.eval]

private theorem ceval_mul (z : ℂ) (p q : Coeff) :
    Coeff.eval z (p * q) = Coeff.eval z p * Coeff.eval z q := by
  simp [Coeff.eval]

private theorem ceval_neg (z : ℂ) (p : Coeff) : Coeff.eval z (-p) = -Coeff.eval z p := by
  simp [Coeff.eval]

/-! ## Complex conjugation -/

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The data record with the deterministic matrices `Θ`, `Σ_o`, `Θ^{(n)}_err`, the ghost factor
and the auxiliary matrices conjugated. -/
private def conjD (D₀ : Data ι) : Data ι :=
  { D₀ with
    Theta := D₀.Theta.map star
    Sig := fun o => (D₀.Sig o).map star
    ThetaErr := fun a b => (D₀.ThetaErr a b).map star
    ghost := star D₀.ghost
    aux := fun j => (D₀.aux j).map star }

omit [Fintype ι] [DecidableEq ι] in
private theorem conjD_conjD (D₀ : Data ι) : conjD (conjD D₀) = D₀ := by
  rcases D₀ with ⟨m, Gm, S, Sp, Sm, Th, Sig, TE, gh, aux⟩
  simp only [conjD, Matrix.map_map]
  congr <;> simp [Function.comp_def]

omit [DecidableEq ι] in
private theorem chain_conjD (D₀ : Data ι) (o : List ℕ) :
    (conjD D₀).chain o = (D₀.chain o).map star := by
  unfold Data.chain
  suffices h : ∀ M : Matrix ι ι ℂ, o.foldl (fun M l => M * (conjD D₀).Sig l * (conjD D₀).Theta)
      (M.map star) = (o.foldl (fun M l => M * D₀.Sig l * D₀.Theta) M).map star by
    exact h D₀.Theta
  induction o with
  | nil => intro M; rfl
  | cons l o ih =>
    intro M
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    change M.map (starRingEnd ℂ) * (D₀.Sig l).map (starRingEnd ℂ) *
      D₀.Theta.map (starRingEnd ℂ) = (M * D₀.Sig l * D₀.Theta).map (starRingEnd ℂ)
    rw [Matrix.map_mul, Matrix.map_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem star_ofReal_mat (S : Matrix ι ι ℝ) (a b : ι) :
    star ((S.map fun r => (r : ℂ)) a b) = (S.map fun r => (r : ℂ)) a b := by
  simp [Matrix.map_apply]

/-- The factor of the conjugate component is the conjugate of the factor under `conjD`, when `S`
is real and `S⁻ = \overline{S⁺}`. -/
private theorem val_conj {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (hS : ∀ a b, star (D₀.S a b) = D₀.S a b) (hSm : D₀.Sm = D₀.Sp.map star) :
    Comp.val D₀ σ { c with kind := c.kind.conj } = star (Comp.val (conjD D₀) σ c) := by
  rcases c with ⟨κ, x, y, mi, l⟩
  have hfl : ∀ (ch : Charge) (w : ℂ), ch.flip.apply w = star (ch.apply w) := by
    intro ch w
    cases ch <;> simp [Charge.flip, Charge.apply]
  cases κ with
  | G ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | weight ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | light ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | inv ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | wD ch d => simp only [Comp.val, Kind.conj, hfl]; rfl
  | waved w =>
    cases w
    · simp only [Comp.val, Kind.conj]
      exact (hS _ _).symm
    · simp only [Comp.val, Kind.conj, hSm, Matrix.map_apply]
      rfl
    · simp only [Comp.val, Kind.conj]
      change D₀.Sp _ _ = star (D₀.Sm _ _)
      rw [hSm, Matrix.map_apply, star_star]
  | theta o =>
    simp only [Comp.val, Kind.conj, chain_conjD, Matrix.map_apply, star_star]
  | thetaErr a b => simp [Comp.val, Kind.conj, conjD]
  | ghost => simp [Comp.val, Kind.conj, conjD]
  | aux j r b => simp [Comp.val, Kind.conj, conjD]
  | dot => simp only [Comp.val, Kind.conj]; split_ifs <;> simp
  | xdot => simp only [Comp.val, Kind.conj]; split_ifs <;> simp

private theorem CVar_conj_eval (z : ℂ) (v : CVar) :
    CVar.eval z (CVar.conj v) = star (CVar.eval z v) := by
  cases v <;> simp [CVar.conj, CVar.eval, star_inv₀]

private theorem Coeff_conj_eval (z : ℂ) (p : Coeff) :
    (Coeff.conj p).eval z = star (p.eval z) := by
  unfold Coeff.conj Coeff.eval
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_rename, Complex.star_def, MvPolynomial.eval,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  funext v
  simp [CVar_conj_eval]

end Conj

section ConjAdm

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

/-- The model relations hold for the data records `conjD (D ω)`. -/
private def conjAdm (A : ModelAdm Ω ι PF D) : ModelAdm Ω ι PF (fun ω => conjD (D ω)) where
  H := A.H
  z := A.z
  S := A.S
  E := A.E
  Meas := A.Meas
  Good := A.Good
  Test := A.Test
  dh := A.dh
  isHermitian := A.isHermitian
  im_pos := A.im_pos
  isSymm := A.isSymm
  nonneg := A.nonneg
  rowSum := A.rowSum
  data_m := A.data_m
  data_G := A.data_G
  data_minor := A.data_minor
  data_S := A.data_S
  data_Sp := A.data_Sp
  data_Sm := A.data_Sm
  data_Theta := fun ω => by
    have h := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) (A.data_Theta ω)
    simp only [Matrix.map_mul] at h
    have hr : ∀ M : Matrix ι ι ℂ, (∀ a b, star (M a b) = M a b) → M.map (starRingEnd ℂ) = M :=
      fun M hM => by ext a b; exact hM a b
    have h1 : ∀ a b, star ((((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b) =
        (((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b := by
      intro a b
      simp [A.data_S, Matrix.map_apply]
    have h2 : ∀ a b, star ((1 - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b) =
        (1 - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b := by
      intro a b
      rw [Matrix.sub_apply, star_sub, h1, Matrix.one_apply]
      split_ifs <;> simp
    rw [hr _ h1, hr _ h2] at h
    exact h
  laws := A.laws
  meas_add := A.meas_add
  meas_mul := A.meas_mul
  meas_minor := A.meas_minor
  P_star := A.P_star
  good_star := A.good_star
  good_entry := A.good_entry
  good_inv := A.good_inv
  good_H := A.good_H
  test_good := A.test_good
  test_const := A.test_const
  test_add := A.test_add
  test_mul := A.test_mul
  test_star := A.test_star
  test_entry := A.test_entry
  test_dh := A.test_dh
  dh_add := A.dh_add
  dh_mul := A.dh_mul
  dh_const := A.dh_const
  dh_green := A.dh_green
  dh_conj_green := A.dh_conj_green
  ibp := A.ibp

omit [Fintype ι] [DecidableEq ι] in
private theorem conjD_conjD' : (fun ω => conjD (conjD (D ω))) = D := funext fun _ => conjD_conjD _

private theorem val_conjD_random {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (h : c.kind.isRandom = true) : Comp.val (conjD D₀) σ c = Comp.val D₀ σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> first | rfl | simp [Kind.isRandom] at h

/-- Components without label, or random components without minor that are not `(G_{xx})⁻¹` or
`W_D` weights. -/
private def OK {V : Type*} (cs : List (Comp V)) : Prop :=
  ∀ c ∈ cs, c.label = none ∨ (c.kind.isRandom = true ∧ basB c = true)

/-- The term of the conjugate graph is the conjugate of the term under `conjD`. -/
private theorem termR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (σ : Atom k N → ι) (ω : Ω) :
    g.conj.termR PF D σ ω = star (g.termR PF (fun ω => conjD (D ω)) σ ω) := by
  have hS : ∀ ω a b, star ((D ω).S a b) = (D ω).S a b := fun ω a b => by
    rw [A.data_S]; exact star_ofReal_mat _ a b
  have hc : ∀ ω (c : Comp (Atom k N)), Comp.val (D ω) σ { c with kind := c.kind.conj } =
      star (Comp.val (conjD (D ω)) σ c) := fun ω c => val_conj _ σ c (hS ω) (A.data_Sm ω)
  have hlab : g.conj.labels = g.labels := by
    unfold Graph.labels Graph.conj
    rw [List.filterMap_map]
    rfl
  have hprod : ∀ (ω : Ω) (p : Comp (Atom k N) → Bool), (((g.comps.map fun c =>
      { c with kind := c.kind.conj }).filter p).map (Comp.val (D ω) σ)).prod =
      star (((g.comps.filter fun c => p { c with kind := c.kind.conj }).map
        (Comp.val (conjD (D ω)) σ)).prod) := by
    intro ω p
    rw [List.filter_map, List.map_map, Complex.star_def, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun c _ => by
      simp only [Function.comp_apply, hc, Complex.star_def])
  unfold Graph.termR
  rw [hlab]
  simp only [Graph.conj, Coeff_conj_eval] at hprod ⊢
  rw [hprod ω]
  have hop : ∀ ℓ ∈ g.labels, PF.op ℓ.1 (σ ℓ.2) (fun ω' => (((g.comps.map fun c =>
      { c with kind := c.kind.conj }).filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) ω =
      star (PF.op ℓ.1 (σ ℓ.2) (fun ω' => ((g.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (conjD (D ω')) σ)).prod) ω) := by
    intro ℓ hℓ
    have hf : (fun ω' => (((g.comps.map fun c => { c with kind := c.kind.conj }).filter
        fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod) =
        fun ω' => star (((g.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (conjD (D ω')) σ)).prod) := funext fun ω' => hprod ω' _
    have hgood : A.Good fun ω' => ((g.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (conjD (D ω')) σ)).prod := by
      refine A.test_good _ (test_listProd' A _ fun c hc' => ?_)
      obtain ⟨hcm, hcl⟩ := List.mem_filter.1 hc'
      rcases hok c hcm with h | ⟨hr, hb⟩
      · simp [h] at hcl
      · simp only [val_conjD_random _ σ c hr]
        exact val_test A σ c hb hr
    rw [hf]
    rcases ℓ with ⟨pq, u⟩
    cases pq
    · exact congrFun (A.P_star _ _ hgood) ω
    · simp only [PFamily.op, Pi.sub_apply, star_sub]
      rw [congrFun (A.P_star _ _ hgood) ω]
  rw [List.map_congr_left hop, Complex.star_def, map_mul, map_mul]
  simp only [map_list_prod, List.map_map, Function.comp_def]
  rfl

private theorem valR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (e : Fin k → ι) (ω : Ω) :
    g.conj.valR PF D e ω = star (g.valR PF (fun ω => conjD (D ω)) e ω) := by
  simp only [Graph.valR, termR_conj A g hok, Complex.star_def, map_sum]

end ConjAdm

/-! ## Labelled components of the output graphs -/

section OKLists

/-- Components without minor and without label that are not `(G_{xx})⁻¹` or `W_D` weights. -/
private def PB {V : Type*} (cs : List (Comp V)) : Prop :=
  ∀ c ∈ cs, basB c = true ∧ c.label = none

private theorem PB_append {V : Type*} {a b : List (Comp V)} : PB (a ++ b) ↔ PB a ∧ PB b := by
  simp only [PB, List.mem_append, or_imp, forall_and]
  tauto

private theorem PB_cons {V : Type*} {c : Comp V} {cs : List (Comp V)} :
    PB (c :: cs) ↔ (basB c = true ∧ c.label = none) ∧ PB cs := by
  simp [PB]

private theorem PB_nil {V : Type*} : PB ([] : List (Comp V)) := by simp [PB]

private theorem PB_liftCs {k n : ℕ} (j : ℕ) {cs : List (Comp (Atom k n))} (h : PB cs) :
    PB (liftCs j cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact ⟨by rw [basB_map]; exact (h c' hc').1, by simp [Comp.map, (h c' hc').2]⟩

private theorem PB_sub {V : Type*} {cs cs' : List (Comp V)} (h : PB cs)
    (hs : ∀ c ∈ cs', c ∈ cs) : PB cs' := fun c hc => h c (hs c hc)

private theorem PB_solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    basB (solidC ch u v) = true ∧ (solidC ch u v).label = none := by
  unfold solidC
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem PB_of_plain {k n : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.isPlainB = true) : PB cs := fun c hc => basB_of_plain (h c hc)

private theorem OK_of_PB {V : Type*} {cs : List (Comp V)} (h : PB cs) : OK cs :=
  fun c hc => Or.inl (h c hc).2

private theorem OK_labelQs {V : Type*} (u : V) {cs : List (Comp V)} (h : PB cs) :
    OK (labelQs u cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  unfold Comp.labelQ
  split_ifs with hr
  · exact Or.inr ⟨hr, (h c' hc').1⟩
  · exact Or.inl (h c' hc').2

private theorem OK_append {V : Type*} {a b : List (Comp V)} (ha : OK a) (hb : OK b) :
    OK (a ++ b) := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact ha c h
  · exact hb c h

private theorem dPieces_PB {V : Type*} [DecidableEq V] (p q : V) (c : Comp V) :
    ∀ ps, c.dPieces p q = some ps → PB ps := by
  intro ps h
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> try (cases ‹Charge›)
  all_goals simp only [Comp.dPieces, Option.some.injEq, reduceCtorEq] at h
  all_goals (subst h; simp only [PB_cons, PB_nil, and_true]; exact ⟨PB_solidC _ _ _,
    PB_solidC _ _ _⟩)

private theorem dTerms_PB {V : Type*} [DecidableEq V] (p q : V) {cs : List (Comp V)}
    (h : PB cs) : ∀ d ∈ dTerms p q cs, PB d := by
  induction cs with
  | nil => simp [dTerms]
  | cons c cs ih =>
    intro d hd
    rw [dTerms_cons] at hd
    rcases List.mem_append.1 hd with hd | hd
    · cases hp : c.dPieces p q with
      | none => simp [hp] at hd
      | some ps =>
        simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hd
        subst hd
        exact PB_append.2 ⟨fun c' hc' => h c' (List.mem_cons_of_mem _ hc'),
          dPieces_PB p q c ps hp⟩
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact PB_cons.2 ⟨h c (List.mem_cons_self ..),
        ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) d' hd'⟩

private theorem fa_append {k n : ℕ} {P : Tracked k n → Prop} {E₁ E₂ : TExpansion k n}
    (h₁ : ∀ t ∈ E₁, P t) (h₂ : ∀ t ∈ E₂, P t) : ∀ t ∈ E₁ ++ E₂, P t := by
  intro t ht
  rcases List.mem_append.1 ht with h | h
  · exact h₁ t h
  · exact h₂ t h

private theorem fa_map {k n : ℕ} {β : Type*} {P : Tracked k n → Prop} {l : List β}
    {f : β → Tracked k n} (h : ∀ j ∈ l, P (f j)) : ∀ t ∈ l.map f, P t := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
  exact h j hj

private theorem fa_cons {k n : ℕ} {P : Tracked k n → Prop} {t : Tracked k n}
    {E : TExpansion k n} (h₁ : P t) (h₂ : ∀ t ∈ E, P t) : ∀ t' ∈ t :: E, P t' := by
  intro t' ht'
  rcases List.mem_cons.1 ht' with rfl | h
  · exact h₁
  · exact h₂ t' h

private theorem fa_nil {k n : ℕ} {P : Tracked k n → Prop} : ∀ t ∈ ([] : TExpansion k n), P t := by
  simp

end OKLists

section Assembly

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  {k n : ℕ}


private theorem conj_plain {Γ : Graph k n} (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) :
    ∀ c ∈ Γ.conj.comps, c.isPlainB = true := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  have h := hpl c' hc'
  rcases c' with ⟨κ, x, y, mi, l⟩
  cases κ <;> try (cases ‹Charge›)
  all_goals first | exact h | (cases ‹Wave› <;> exact h)

private theorem S_conj (A : ModelAdm Ω ι PF D) (E : TExpansion k n)
    (hok : ∀ t ∈ E, OK t.g.comps) (e : Fin k → ι) (ω : Ω) :
    S PF D e ω E.conj = star (S PF (fun ω => conjD (D ω)) e ω E) := by
  induction E with
  | nil => simp [TExpansion.conj, S_nil]
  | cons t E ih =>
    have h1 := hok t (List.mem_cons_self ..)
    have h2 := ih fun t' ht' => hok t' (List.mem_cons_of_mem _ ht')
    simp only [TExpansion.conj, List.map_cons] at h2 ⊢
    rw [S_cons, S_cons, h2, valR_conj A t.g h1, star_add]

private theorem valR_eq_star (A : ModelAdm Ω ι PF D) (Γ : Graph k n)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (e : Fin k → ι) (ω : Ω) :
    Γ.valR PF D e ω = star (Γ.conj.valR PF (fun ω => conjD (D ω)) e ω) := by
  have h := valR_conj (conjAdm A) Γ (OK_of_PB (PB_of_plain hpl)) e ω
  rw [conjD_conjD'] at h
  rw [h, star_star]

end Assembly

/-! ## Value of the light weight expansion: removing the expanded weight -/

section Prelim

variable {V : Type*} {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem rv_eraseIdx (D₀ : Data ι) (σ : V → ι) (cs : List (Comp V)) (i : ℕ)
    (hi : i < cs.length) :
    rv D₀ σ cs = (if (cs[i]'hi).kind.isRandom then Comp.val D₀ σ (cs[i]'hi) else 1) *
      rv D₀ σ (cs.eraseIdx i) := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp [rv_cons]
    | succ i =>
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, rv_cons]
      rw [ih i (by simpa using hi)]
      ring

private theorem dv_eraseIdx (D₀ : Data ι) (σ : V → ι) (cs : List (Comp V)) (i : ℕ)
    (hi : i < cs.length) :
    dv D₀ σ cs = (if (cs[i]'hi).kind.isRandom then 1 else Comp.val D₀ σ (cs[i]'hi)) *
      dv D₀ σ (cs.eraseIdx i) := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => simp [dv_cons]
    | succ i =>
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, dv_cons]
      rw [ih i (by simpa using hi)]
      ring

end Prelim

section Plain

variable {k n : ℕ}

private theorem plain_Unl' {cs : List (Comp (Atom k n))} (h : ∀ c ∈ cs, c.isPlainB = true)
    : Unl cs :=
  fun c hc => (basB_of_plain (h c hc)).2

private theorem plain_bas_lift' {cs : List (Comp (Atom k n))} (h : ∀ c ∈ cs, c.isPlainB = true)
    (j : ℕ) :
    ∀ c ∈ liftCs j cs, basB c = true ∧ c.label = none := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2⟩ := basB_of_plain (h c' hc')
  exact ⟨by rw [basB_map]; exact h1, by simp [Comp.map, h2]⟩

private theorem comp0_eq {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true)
    (hi : i < Γ.comps.length) (hk : (Γ.comps[i]).kind = .light .plus)
    (hxi : (Γ.comps[i]).x = x) : Γ.comps[i] = mkC (.light .plus) x (Γ.comps[i]).y := by
  have hp := hpl _ (List.getElem_mem hi)
  rcases h : Γ.comps[i] with ⟨κ, a, b, mi, l⟩
  rw [h] at hk hxi hp
  simp only at hk hxi
  subst hk hxi
  simp only [Comp.isPlainB, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
  obtain ⟨⟨h1, h2⟩, -⟩ := hp
  subst h1 h2
  rfl

end Plain

section ValueRel

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

private theorem rvG_eq {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true)
    (hi : i < Γ.comps.length) (hk : (Γ.comps[i]).kind = .light .plus)
    (hxi : (Γ.comps[i]).x = x) (σ : Atom k n → ι) (ω : Ω) :
    rv (D ω) σ Γ.comps = (A.G ω (σ x) (σ x) - msc A.z) * rv (D ω) σ (w2f Γ i) := by
  rw [rv_eraseIdx (D ω) σ Γ.comps i hi, comp0_eq hpl hi hk hxi]
  simp only [mkC_kind, Kind.isRandom, ite_true, val_light A, Charge.apply]
  rfl

private theorem dvG_eq {Γ : Graph k n} {i : ℕ} (hi : i < Γ.comps.length)
    (hk : (Γ.comps[i]).kind = .light .plus) (D₀ : Data ι) (σ : Atom k n → ι) :
    dv D₀ σ Γ.comps = dv D₀ σ (w2f Γ i) := by
  rw [dv_eraseIdx D₀ σ Γ.comps i hi, hk]
  simp [Kind.isRandom]
  rfl

end ValueRel

/-! ## Value of the light weight expansion: the terms at one labelling -/

section WBlocks

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i : ℕ)
  (e : Fin k → ι) (ω : Ω)

private theorem wb1 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T1 PF D e ω ⟨liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.light .plus) (newA 0) (newA 0)], cm * Γ.coeff⟩ s =
    ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) Γ.comps * (A.S (Sum.elim e s x) β : ℂ)) *
      (rv (D ω) (Sum.elim e s) Γ.comps * (A.G ω β β - msc A.z)) := by
  simp only [T1]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hUc : Unl (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [termR_unl (⟨_, cm * Γ.coeff⟩ : Graph k (n + 1)) hUc, m_eq A, ceval_mul, ceval_cm, pv_eq]
  simp only [dv_append, rv_append, dv_liftCs, rv_liftCs, elim_append_comp_liftA, dv_cons,
    rv_cons, dv_nil, rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true,
    mul_one, one_mul, val_s A, val_light A, elim_append_liftA, elim_append_newA,
    Matrix.cons_val_zero, Charge.apply]
  ring

private theorem wb2 (hU : Unl (w2f Γ i)) (s : Fin n → ι) :
    T2 PF D e ω ⟨liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
        mkC (.light .plus) (newA 1) (newA 1)], cm * Γ.coeff⟩ s =
    ∑ α, ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (w2f Γ i) * ((D ω).Sp (Sum.elim e s x) α * (A.S α β : ℂ))) *
      (rv (D ω) (Sum.elim e s) (w2f Γ i) * ((A.G ω α α - msc A.z) * (A.G ω β β - msc A.z))) := by
  simp only [T2]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hUc : Unl (liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.light .plus) (newA 1) (newA 1)]) :=
    Unl_append.2 ⟨Unl_liftCs 2 hU, by simp [Unl, mkC]⟩
  rw [termR_unl (⟨_, cm * Γ.coeff⟩ : Graph k (n + 2)) hUc, m_eq A, ceval_mul, ceval_cm, pv_eq]
  simp only [dv_append, rv_append, dv_liftCs, rv_liftCs, elim_append_comp_liftA, dv_cons,
    rv_cons, dv_nil, rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true,
    mul_one, one_mul, val_s A, val_Sp, val_light A, elim_append_liftA, elim_append_newA,
    Matrix.cons_val_zero, Matrix.cons_val_one, Charge.apply]
  ring

private theorem wb5 (hU : Unl Γ.comps) (hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true)
    (s : Fin n → ι) :
    T0 PF D e ω ⟨labelQs x Γ.comps, Γ.coeff⟩ s =
    Γ.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) Γ.comps *
      PF.op .Q (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) Γ.comps) ω := by
  have h := termR_Q (PF := PF) (D := D) x Γ.comps [] Γ.coeff hU Unl_nil hr (Sum.elim e s) ω
  simp only [List.append_nil] at h
  rw [T0, h, m_eq A]
  simp only [pv_nil, mul_one]

private theorem wb6 (hU : Unl (w2f Γ i)) (s : Fin n → ι) :
    T1 PF D e ω ⟨labelQs (newA 0) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
        [mkC (.waved .plus) (liftA 1 x) (newA 0)], Γ.coeff⟩ s =
    ∑ α, Γ.coeff.eval (msc A.z) * (dv (D ω) (Sum.elim e s) (w2f Γ i) *
      (D ω).Sp (Sum.elim e s x) α) *
      PF.op .Q α (fun ω' => rv (D ω') (Sum.elim e s) (w2f Γ i) *
        (A.G ω' α α - msc A.z)) ω := by
  simp only [T1]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hUb : Unl (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [termR_Q (newA 0) _ _ _ hUb (by simp [mkC])
      ⟨mkC (.light .plus) (newA 0) (newA 0), List.mem_append_right _ (by simp), rfl⟩]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α]))
      (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) =
      rv (D ω') (Sum.elim e s) (w2f Γ i) * (A.G ω' α α - msc A.z) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_light A, elim_append_newA, Matrix.cons_val_zero,
      Charge.apply]
  rw [funext hrv, elim_append_newA]
  simp only [pv_cons, pv_nil, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
    mkC_kind, Kind.isRandom, ite_true, mul_one, val_Sp, elim_append_newA, elim_append_liftA,
    Matrix.cons_val_zero, m_eq A]
  ring

private theorem wb7 (hU : Unl (w2f Γ i)) (s : Fin n → ι) :
    T1 PF D e ω ⟨labelQs (liftA 1 x) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0),
        mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
        -cm * Γ.coeff⟩ s =
    ∑ β, -(msc A.z * Γ.coeff.eval (msc A.z)) *
      (dv (D ω) (Sum.elim e s) (w2f Γ i) * (A.S (Sum.elim e s x) β : ℂ)) *
      PF.op .Q (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (w2f Γ i) *
        ((A.G ω' β β - msc A.z) * A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  simp only [T1]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hUb : Unl (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0),
      mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [termR_Q (liftA 1 x) _ _ _ hUb (by simp [mkC])
      ⟨mkC (.light .plus) (newA 0) (newA 0), List.mem_append_right _ (by simp), rfl⟩]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![β]))
      (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0),
        mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) =
      rv (D ω') (Sum.elim e s) (w2f Γ i) * ((A.G ω' β β - msc A.z) *
        A.G ω' (Sum.elim e s x) (Sum.elim e s x)) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_light A, val_weight A, elim_append_newA,
      elim_append_liftA, Matrix.cons_val_zero, Charge.apply]
  rw [funext hrv, elim_append_liftA]
  simp only [pv_cons, pv_nil, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
    mkC_kind, Kind.isRandom, ite_true, mul_one, val_s A, elim_append_newA, elim_append_liftA,
    Matrix.cons_val_zero, m_eq A, ceval_mul, ceval_cm, ceval_neg]
  ring

private theorem wb8 (hU : Unl (w2f Γ i)) (s : Fin n → ι) :
    T2 PF D e ω ⟨labelQs (newA 0) (liftCs 2 (w2f Γ i) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], -cm * Γ.coeff⟩ s =
    ∑ α, ∑ β, -(msc A.z * Γ.coeff.eval (msc A.z)) *
      (dv (D ω) (Sum.elim e s) (w2f Γ i) * ((D ω).Sp (Sum.elim e s x) α * (A.S α β : ℂ))) *
      PF.op .Q α (fun ω' => rv (D ω') (Sum.elim e s) (w2f Γ i) *
        ((A.G ω' β β - msc A.z) * A.G ω' α α)) ω := by
  simp only [T2]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hUb : Unl (liftCs 2 (w2f Γ i) ++ [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.weight .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 2 hU, by simp [Unl, mkC]⟩
  rw [termR_Q (newA 0) _ _ _ hUb (by simp [mkC])
      ⟨mkC (.light .plus) (newA 1) (newA 1), List.mem_append_right _ (by simp), rfl⟩]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
      (liftCs 2 (w2f Γ i) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.weight .plus) (newA 0) (newA 0)]) =
      rv (D ω') (Sum.elim e s) (w2f Γ i) * ((A.G ω' β β - msc A.z) * A.G ω' α α) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_light A, val_weight A, elim_append_newA,
      Matrix.cons_val_zero, Matrix.cons_val_one, Charge.apply]
  rw [funext hrv, elim_append_newA]
  simp only [pv_cons, pv_nil, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
    mkC_kind, Kind.isRandom, ite_true, mul_one, val_s A, val_Sp, elim_append_newA,
    elim_append_liftA, Matrix.cons_val_zero, Matrix.cons_val_one, m_eq A, ceval_mul, ceval_cm,
    ceval_neg]
  ring

private theorem wb34a (hpl : ∀ c ∈ w2f Γ i, c.isPlainB = true) (s : Fin n → ι) :
    ((dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))).map fun d =>
        T1 PF D e ω ⟨d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 x)], cm * Γ.coeff⟩ s).sum +
      ((dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))).map fun d =>
        T1 PF D e ω ⟨labelQs (liftA 1 x) (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
          [mkC (.waved .s) (liftA 1 x) (newA 0)], -cm * Γ.coeff⟩ s).sum =
    ((dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i))).map fun d =>
      ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) (w2f Γ i) * (A.S (Sum.elim e s x) β : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![β]))
          (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)])) ω).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hdU := ((dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
    (plain_bas_lift' hpl 1)).1 d hd)
  have hU3 : Unl (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) :=
    Unl_append.2 ⟨fun c hc => (hdU.1 c hc).2, by simp [Unl, mkC]⟩
  have hU4 : Unl (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.G .plus) (newA 0) (liftA 1 x)]) :=
    Unl_append.2 ⟨fun c hc => (hdU.1 c hc).2, by simp [Unl, mkC]⟩
  rw [termR_pair (PF := PF) (D := D) (liftA 1 x) _ [mkC (.waved .s) (liftA 1 x) (newA 0)] _ _ _
    hU3 (by simp [Unl, mkC]) hU4
    ⟨mkC (.G .plus) (newA 0) (liftA 1 x), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp [pv_append, pv_cons, pv_nil]; ring),
    elim_append_liftA, m_eq A, ceval_mul, ceval_cm]
  have h2 := hdU.2 (D ω)
  rw [dv_liftCs, elim_append_comp_liftA] at h2
  simp only [dv_append, h2, dv_cons, dv_nil, mkC_kind, Kind.isRandom, ite_true, mul_one,
    pv_cons, pv_nil, val_s A, elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
  ring

private theorem wb34b (hpl : ∀ c ∈ w2f Γ i, c.isPlainB = true) (s : Fin n → ι) :
    ((dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))).map fun d =>
        T2 PF D e ω ⟨d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.G .plus) (newA 1) (newA 0)],
          cm * Γ.coeff⟩ s).sum +
      ((dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))).map fun d =>
        T2 PF D e ω ⟨labelQs (newA 0) (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++
          [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
          -cm * Γ.coeff⟩ s).sum =
    ((dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i))).map fun d =>
      ∑ α, ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) (w2f Γ i) * ((D ω).Sp (Sum.elim e s x) α * (A.S α β : ℂ))) *
        PF.P α (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
          (d ++ [mkC (.G .plus) (newA 1) (newA 0)])) ω).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  simp only [T2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hdU := ((dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
    (plain_bas_lift' hpl 2)).1 d hd)
  have hU3 : Unl (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (hdU.1 c hc).2, by simp [Unl, mkC]⟩
  have hU4 : Unl (d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.G .plus) (newA 1) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (hdU.1 c hc).2, by simp [Unl, mkC]⟩
  rw [termR_pair (PF := PF) (D := D) (newA 0) _ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] _ _ _ hU3 (by simp [Unl, mkC]) hU4
    ⟨mkC (.G .plus) (newA 1) (newA 0), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp [pv_append, pv_cons, pv_nil]; ring),
    elim_append_newA, m_eq A, ceval_mul, ceval_cm]
  have h2 := hdU.2 (D ω)
  rw [dv_liftCs, elim_append_comp_liftA] at h2
  simp only [dv_append, h2, dv_cons, dv_nil, mkC_kind, Kind.isRandom, ite_true, mul_one,
    pv_cons, pv_nil, val_s A, val_Sp, elim_append_liftA, elim_append_newA, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

end WBlocks

/-! ## Value of the light weight expansion: the identity at one labelling -/

private theorem b_split1 {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (X : ι)
    (g : ι → ℂ) : ∑ α, (1 + M) X α * g α = g X + ∑ α, M X α * g α := by
  simp only [Matrix.add_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem b_split2 {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (X : ι)
    (s h : ι → ι → ℂ) :
    ∑ α, ∑ β, (1 + M) X α * s α β * h α β =
      ∑ β, s X β * h X β + ∑ α, ∑ β, M X α * s α β * h α β := by
  rw [show (∑ α, ∑ β, (1 + M) X α * s α β * h α β) =
      ∑ α, (1 + M) X α * ∑ β, s α β * h α β from Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring, b_split1]
  congr 1
  exact Finset.sum_congr rfl fun α _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring

private theorem list_finset_comm {ι β : Type*} [Fintype ι] (l : List β) (f : β → ι → ℂ) :
    (l.map fun j => ∑ α, f j α).sum = ∑ α, (l.map fun j => f j α).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.sum_add_distrib]

section WCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem wt_core_abs (X : ι) (F rvL : Ω → ℂ) (hF : A.Test F)
    (hR : ∀ ω', rvL ω' = (A.G ω' X X - msc A.z) * F ω') {γ₁ γ₂ : Type*}
    (l₁ : List γ₁) (l₂ : List γ₂) (r₁ : γ₁ → ι → Ω → ℂ) (r₂ : γ₂ → ι → ι → Ω → ℂ)
    (hr₁ : ∀ β ω', (l₁.map fun d => r₁ d β ω').sum = A.G ω' β X * -A.dh β X F ω')
    (hr₂ : ∀ α β ω', (l₂.map fun d => r₂ d α β ω').sum = A.G ω' β α * -A.dh β α F ω')
    (hg₁ : ∀ β, ∀ d ∈ l₁, A.Good (r₁ d β)) (hg₂ : ∀ α β, ∀ d ∈ l₂, A.Good (r₂ d α β))
    (c Det : ℂ) (ω : Ω) :
    c * Det * rvL ω =
      ∑ β, msc A.z * c * (Det * (A.S X β : ℂ)) * (rvL ω * (A.G ω β β - msc A.z)) +
      ∑ α, ∑ β, msc A.z * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        (F ω * ((A.G ω α α - msc A.z) * (A.G ω β β - msc A.z))) +
      (l₁.map fun d => ∑ β, msc A.z * c * (Det * (A.S X β : ℂ)) * PF.P X (r₁ d β) ω).sum +
      (l₂.map fun d => ∑ α, ∑ β, msc A.z * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (r₂ d α β) ω).sum +
      c * Det * PF.op .Q X rvL ω +
      ∑ α, c * (Det * (D ω).Sp X α) *
        PF.op .Q α (fun ω' => F ω' * (A.G ω' α α - msc A.z)) ω +
      ∑ β, -(msc A.z * c) * (Det * (A.S X β : ℂ)) *
        PF.op .Q X (fun ω' => F ω' * ((A.G ω' β β - msc A.z) * A.G ω' X X)) ω +
      ∑ α, ∑ β, -(msc A.z * c) * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.op .Q α (fun ω' => F ω' * ((A.G ω' β β - msc A.z) * A.G ω' α α)) ω := by
  set m := msc A.z with hm
  have hI := weightIdentity Ω ι PF D A X F hF ω
  dsimp only at hI
  rw [← hm] at hI
  have gG : ∀ (a b : ι), A.Good fun ω' => A.G ω' a b := fun a b => A.test_good _ (test_G A a b)
  -- the splits `b = δ + S⁺`
  have sp1 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    (A.G ω a a - m) * (A.G ω b b - m) * F ω)
  have sp2 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    PF.P a (fun ω' => A.G ω' b a * A.dh b a F ω') ω)
  have sp3 := b_split1 (D ω).Sp X (fun a =>
    PF.op .Q a (fun ω' => (A.G ω' a a - m) * F ω') ω)
  have sp4 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    PF.op .Q a (fun ω' => (A.G ω' b b - m) * A.G ω' a a * F ω') ω)
  -- the conversions
  have c4 : ∀ β, -PF.P X (fun ω' => A.G ω' β X * A.dh β X F ω') ω =
      (l₁.map fun d => PF.P X (r₁ d β) ω).sum := fun β => by
    rw [← P_listSum' A l₁ (hg₁ β) X ω, P_congr' (fun ω' => hr₁ β ω'),
      ← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _) (test_dh' A _ _ hF)))]
    exact congrFun (P_congr' (fun ω' => by ring) X) ω
  have c4' : ∀ α β, -PF.P α (fun ω' => A.G ω' β α * A.dh β α F ω') ω =
      (l₂.map fun d => PF.P α (r₂ d α β) ω).sum := fun α β => by
    rw [← P_listSum' A l₂ (hg₂ α β) α ω, P_congr' (fun ω' => hr₂ α β ω'),
      ← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _) (test_dh' A _ _ hF)))]
    exact congrFun (P_congr' (fun ω' => by ring) α) ω
  have c3 : PF.op .Q X (fun ω' => (A.G ω' X X - m) * F ω') ω = PF.op .Q X rvL ω := by
    rw [show (fun ω' => (A.G ω' X X - m) * F ω') = rvL from (funext hR).symm]
  have c3' : ∀ α, PF.op .Q α (fun ω' => (A.G ω' α α - m) * F ω') ω =
      PF.op .Q α (fun ω' => F ω' * (A.G ω' α α - m)) ω := fun α => by
    rw [Q_apply', Q_apply', P_congr' (g := fun ω' => F ω' * (A.G ω' α α - m)) fun ω' => by ring]
    ring
  have c4q : ∀ a b, PF.op .Q a (fun ω' => (A.G ω' b b - m) * A.G ω' a a * F ω') ω =
      PF.op .Q a (fun ω' => F ω' * ((A.G ω' b b - m) * A.G ω' a a)) ω := fun a b => by
    rw [Q_apply', Q_apply', P_congr' (g := fun ω' => F ω' * ((A.G ω' b b - m) * A.G ω' a a))
      fun ω' => by ring]
    ring
  have e1a : ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) * (A.G ω α α - m) *
        (A.G ω β β - m) * F ω =
      ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        ((A.G ω α α - m) * (A.G ω β β - m) * F ω) :=
    Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have e1b : c * Det * (m * ∑ β, (A.S X β : ℂ) * ((A.G ω X X - m) * (A.G ω β β - m) * F ω)) =
      ∑ β, m * c * (Det * (A.S X β : ℂ)) * (rvL ω * (A.G ω β β - m)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by rw [hR ω]; ring
  have e1c : c * Det * (m * ∑ α, ∑ β, (D ω).Sp X α * (A.S α β : ℂ) *
        ((A.G ω α α - m) * (A.G ω β β - m) * F ω)) =
      ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        (F ω * ((A.G ω α α - m) * (A.G ω β β - m))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have E1 : c * Det * (m * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        (A.G ω α α - m) * (A.G ω β β - m) * F ω) =
      ∑ β, m * c * (Det * (A.S X β : ℂ)) * (rvL ω * (A.G ω β β - m)) +
      ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        (F ω * ((A.G ω α α - m) * (A.G ω β β - m))) := by
    rw [e1a, sp1]
    linear_combination e1b + e1c
  have E2 : c * Det * -(m * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        PF.P α (fun ω' => A.G ω' β α * A.dh β α F ω') ω) =
      (l₁.map fun d => ∑ β, m * c * (Det * (A.S X β : ℂ)) * PF.P X (r₁ d β) ω).sum +
      (l₂.map fun d => ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (r₂ d α β) ω).sum := by
    rw [sp2]
    have k5 : (l₁.map fun d => ∑ β, m * c * (Det * (A.S X β : ℂ)) * PF.P X (r₁ d β) ω).sum =
        -(c * Det * (m * ∑ β, (A.S X β : ℂ) *
          PF.P X (fun ω' => A.G ω' β X * A.dh β X F ω') ω)) := by
      rw [list_finset_comm]
      simp only [List.sum_map_mul_left, ← c4]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    have k6 : (l₂.map fun d => ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (r₂ d α β) ω).sum =
        -(c * Det * (m * ∑ α, ∑ β, (D ω).Sp X α * (A.S α β : ℂ) *
          PF.P α (fun ω' => A.G ω' β α * A.dh β α F ω') ω)) := by
      rw [list_finset_comm]
      simp only [list_finset_comm, List.sum_map_mul_left, ← c4']
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun β _ => by ring
    linear_combination -k5 - k6
  have E3 : c * Det * ∑ α, (1 + (D ω).Sp) X α *
        PF.op .Q α (fun ω' => (A.G ω' α α - m) * F ω') ω =
      c * Det * PF.op .Q X rvL ω + ∑ α, c * (Det * (D ω).Sp X α) *
        PF.op .Q α (fun ω' => F ω' * (A.G ω' α α - m)) ω := by
    rw [sp3, c3]
    simp only [c3', mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  have E4 : c * Det * -(m * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        PF.op .Q α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω) =
      ∑ β, -(m * c) * (Det * (A.S X β : ℂ)) *
        PF.op .Q X (fun ω' => F ω' * ((A.G ω' β β - m) * A.G ω' X X)) ω +
      ∑ α, ∑ β, -(m * c) * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.op .Q α (fun ω' => F ω' * ((A.G ω' β β - m) * A.G ω' α α)) ω := by
    rw [sp4]
    have k7 : c * Det * (m * ∑ β, (A.S X β : ℂ) *
        PF.op .Q X (fun ω' => (A.G ω' β β - m) * A.G ω' X X * F ω') ω) =
        -(∑ β, -(m * c) * (Det * (A.S X β : ℂ)) *
          PF.op .Q X (fun ω' => F ω' * ((A.G ω' β β - m) * A.G ω' X X)) ω) := by
      simp only [c4q]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    have k8 : c * Det * (m * ∑ α, ∑ β, (D ω).Sp X α * (A.S α β : ℂ) *
        PF.op .Q α (fun ω' => (A.G ω' β β - m) * A.G ω' α α * F ω') ω) =
        -(∑ α, ∑ β, -(m * c) * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
          PF.op .Q α (fun ω' => F ω' * ((A.G ω' β β - m) * A.G ω' α α)) ω) := by
      simp only [c4q]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    linear_combination -k7 - k8
  linear_combination (c * Det) * hI + E1 + E2 + E3 + E4 + (c * Det) * hR ω

end WCore

/-! ## Value of the light weight expansion -/

section WPos

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

private theorem w2t1_eq (x : Atom k n) (Γ : Graph k n) : w2t1 x Γ =
    t1 (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * Γ.coeff) := rfl

private theorem w2t2_eq (x : Atom k n) (Γ : Graph k n) (i : ℕ) : w2t2 x Γ i =
    t2 (liftCs 2 (w2f Γ i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.light .plus) (newA 1) (newA 1)]) (cm * Γ.coeff) := rfl

private theorem w2t3_eq (x : Atom k n) (Γ : Graph k n) : w2t3 x Γ = fun d =>
    t1 (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)])
      (cm * Γ.coeff) := rfl

private theorem w2t4_eq (x : Atom k n) (Γ : Graph k n) : w2t4 x Γ = fun d =>
    t2 (d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.G .plus) (newA 1) (newA 0)]) (cm * Γ.coeff) := rfl

private theorem w2t6_eq (x : Atom k n) (Γ : Graph k n) (i : ℕ) : w2t6 x Γ i =
    t1 (labelQs (newA 0) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 1 x) (newA 0)]) Γ.coeff := rfl

private theorem w2t7_eq (x : Atom k n) (Γ : Graph k n) (i : ℕ) : w2t7 x Γ i =
    t1 (labelQs (liftA 1 x) (liftCs 1 (w2f Γ i) ++ [mkC (.light .plus) (newA 0) (newA 0),
      mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)])
      (-cm * Γ.coeff) := rfl

private theorem w2t8_eq (x : Atom k n) (Γ : Graph k n) (i : ℕ) : w2t8 x Γ i =
    t2 (labelQs (newA 0) (liftCs 2 (w2f Γ i) ++ [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) (-cm * Γ.coeff) := rfl

private theorem w2t9_eq (x : Atom k n) (Γ : Graph k n) : w2t9 x Γ = fun d =>
    t1 (labelQs (liftA 1 x) (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) (-cm * Γ.coeff) := rfl

private theorem w2t10_eq (x : Atom k n) (Γ : Graph k n) : w2t10 x Γ = fun d =>
    t2 (labelQs (newA 0) (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)])
      (-cm * Γ.coeff) := rfl

private theorem T0_self (Γ : Graph k n) (e : Fin k → ι) (ω : Ω) (hU : Unl Γ.comps) (s : Fin n → ι) :
    T0 PF D e ω Γ s = Γ.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) Γ.comps *
      rv (D ω) (Sum.elim e s) Γ.comps := by
  rw [T0, termR_unl Γ hU, m_eq A, pv_eq]
  ring

include A in
private theorem wt_pos_valR (x : Atom k n) (Γ : Graph k n) (i : ℕ)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (hi : i < Γ.comps.length)
    (hk : (Γ.comps[i]).kind = .light .plus) (hxi : (Γ.comps[i]).x = x)
    (e : Fin k → ι) (ω : Ω) : S PF D e ω (w2E x Γ i) = Γ.valR PF D e ω := by
  have hU : Unl Γ.comps := plain_Unl' hpl
  have hpF : ∀ c ∈ w2f Γ i, c.isPlainB = true := fun c hc =>
    hpl c (List.mem_of_mem_eraseIdx hc)
  have hUF : Unl (w2f Γ i) := plain_Unl' hpF
  have hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true :=
    ⟨Γ.comps[i], List.getElem_mem hi, by rw [hk]; rfl⟩
  simp only [w2E, w2t1_eq, w2t2_eq, w2t3_eq, w2t4_eq, w2t5, w2t6_eq, w2t7_eq, w2t8_eq, w2t9_eq,
    w2t10_eq, S_append, S_cons_t1, S_cons_t2, S_cons_t0, S_nil, S_map_t1, S_map_t2, add_zero]
  rw [valR_T0]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdG : dv (D ω) (Sum.elim e s) Γ.comps = dv (D ω) (Sum.elim e s) (w2f Γ i) :=
    dvG_eq hi hk _ _
  have h1 := wb1 A x Γ e ω hU s
  have h2 := wb2 A x Γ i e ω hUF s
  have h34a := wb34a A x Γ i e ω hpF s
  have h34b := wb34b A x Γ i e ω hpF s
  have h5 := wb5 A x Γ e ω hU hr s
  have h6 := wb6 A x Γ i e ω hUF s
  have h7 := wb7 A x Γ i e ω hUF s
  have h8 := wb8 A x Γ i e ω hUF s
  have hΓ := T0_self A Γ e ω hU s
  rw [hdG] at h1 h5 hΓ
  have hFt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (w2f Γ i) :=
    rv_test A _ _ fun c hc => (basB_of_plain (hpF c hc)).1
  have hR : ∀ ω', rv (D ω') (Sum.elim e s) Γ.comps = (A.G ω' (Sum.elim e s x) (Sum.elim e s x) -
      msc A.z) * rv (D ω') (Sum.elim e s) (w2f Γ i) := fun ω' => rvG_eq A hpl hi hk hxi _ ω'
  have hr₁ : ∀ β ω', ((dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x)
      (liftCs 1 (w2f Γ i))).map fun d => rv (D ω') (Sum.elim e (Fin.append s ![β]))
        (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)])).sum =
      A.G ω' β (Sum.elim e s x) *
        -A.dh β (Sum.elim e s x) (fun ω'' => rv (D ω'') (Sum.elim e s) (w2f Γ i)) ω' := by
    intro β ω'
    have hdF' := (dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
      (plain_bas_lift' hpF 1)).2 ω'
    simp only [rv_liftCs, elim_append_comp_liftA, elim_append_newA, elim_append_liftA,
      Matrix.cons_val_zero] at hdF'
    rw [← hdF', ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [rv_append, rv_cons, rv_nil, mkC_kind, Kind.isRandom, ite_true, mul_one, val_G A,
      elim_append_newA, elim_append_liftA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hr₂ : ∀ α β ω', ((dTerms (newA 1 : Atom k (n + 2)) (newA 0)
      (liftCs 2 (w2f Γ i))).map fun d => rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
        (d ++ [mkC (.G .plus) (newA 1) (newA 0)])).sum =
      A.G ω' β α * -A.dh β α (fun ω'' => rv (D ω'') (Sum.elim e s) (w2f Γ i)) ω' := by
    intro α β ω'
    have hdF' := (dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
      (plain_bas_lift' hpF 2)).2 ω'
    simp only [rv_liftCs, elim_append_comp_liftA, elim_append_newA, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hdF'
    rw [← hdF', ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [rv_append, rv_cons, rv_nil, mkC_kind, Kind.isRandom, ite_true, mul_one, val_G A,
      elim_append_newA, Matrix.cons_val_zero, Matrix.cons_val_one,
      Charge.apply]
    ring
  have hg₁ : ∀ β, ∀ d ∈ dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i)),
      A.Good fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![β]))
        (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) := by
    intro β d hd
    have hb := ((dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
      (plain_bas_lift' hpF 1)).1 d hd).1
    refine A.test_good _ (rv_test A _ _ fun c hc => ?_)
    rcases List.mem_append.1 hc with hc | hc
    · exact (hb c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      rfl
  have hg₂ : ∀ α β, ∀ d ∈ dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i)),
      A.Good fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
        (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) := by
    intro α β d hd
    have hb := ((dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
      (plain_bas_lift' hpF 2)).1 d hd).1
    refine A.test_good _ (rv_test A _ _ fun c hc => ?_)
    rcases List.mem_append.1 hc with hc | hc
    · exact (hb c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      rfl
  have hcore := wt_core_abs A (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (w2f Γ i))
    (fun ω' => rv (D ω') (Sum.elim e s) Γ.comps) hFt hR
    (dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i)))
    (dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i)))
    (fun d β ω' => rv (D ω') (Sum.elim e (Fin.append s ![β]))
      (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]))
    (fun d α β ω' => rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
      (d ++ [mkC (.G .plus) (newA 1) (newA 0)])) hr₁ hr₂ hg₁ hg₂
    (Γ.coeff.eval (msc A.z)) (dv (D ω) (Sum.elim e s) (w2f Γ i)) ω
  beta_reduce at hcore
  linear_combination h1 + h2 + h34a + h34b + h5 + h6 + h7 + h8 - hΓ - hcore

end WPos

/-! ## Value of the regular weight splitting -/

section SplitVal

variable {V : Type*} [DecidableEq V]

private theorem splitRegular_labels (x : V) (cs : List (Comp V)) :
    ∀ p ∈ splitRegular x cs, p.1.filterMap Comp.label = cs.filterMap Comp.label ∧
      ∀ ℓ, p.1.filter (fun c => decide (c.label = some ℓ)) =
        cs.filter (fun c => decide (c.label = some ℓ)) := by
  induction cs with
  | nil =>
    intro p hp
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    simp
  | cons c cs ih =>
    intro p hp
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hch⟩, hx, hl⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hch] at hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨h1, h2⟩ := ih p' hp'
        exact ⟨by simp [hl, h1], fun ℓ => by simp [hl, h2]⟩
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨h1, h2⟩ := ih p' hp'
        exact ⟨by simp [hl, h1], fun ℓ => by simp [hl, h2]⟩
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr'] at hp
      obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
      obtain ⟨h1, h2⟩ := ih p' hp'
      exact ⟨by simp [List.filterMap_cons, h1], fun ℓ => by simp [List.filter_cons, h2]⟩

private theorem ceval_mOf (z : ℂ) (ch : Charge) : Coeff.eval z (mOf ch) = ch.apply z := by
  cases ch
  · simp [mOf, Coeff.eval, CVar.eval, Charge.apply]
  · simp [mOf, Coeff.eval, CVar.eval, Charge.apply]

private theorem apply_split (ch : Charge) (g m : ℂ) : ch.apply g = ch.apply m + ch.apply
    (g - m) := by
  cases ch <;> simp [Charge.apply, star_sub]

/-- The matrix entry at the ends of a weight. -/
private def Comp.gv {ι : Type*} [Fintype ι] [DecidableEq ι] (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    : ℂ :=
  D₀.Gm (c.minor.map σ).toFinset (σ c.x) (σ c.x)

omit [DecidableEq V] in
private theorem val_weight_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (D₀ : Data ι) (σ : V → ι)
    (c : Comp V) {ch : Charge} (h : c.kind = .weight ch) :
    Comp.val D₀ σ c = ch.apply (Comp.gv D₀ σ c) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at h
  subst h
  rfl

omit [DecidableEq V] in
private theorem val_light_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (D₀ : Data ι) (σ : V → ι)
    (c' c : Comp V) {ch : Charge} (_h : c.kind = .weight ch) (hk : c'.kind = .light ch)
    (hx : c'.x = c.x) (hm : c'.minor = c.minor) :
    Comp.val D₀ σ c' = ch.apply (Comp.gv D₀ σ c - D₀.m) := by
  rcases c' with ⟨κ, a, b, mi, l⟩
  simp only at hk hx hm
  subst hk hx hm
  unfold Comp.gv
  simp only [Comp.val]

private theorem splitRegular_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (D₀ : Data ι) (σ : V → ι)
    (x : V) (cs : List (Comp V)) :
    ((splitRegular x cs).map fun p => p.2.eval D₀.m *
      ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod).sum =
    ((cs.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod := by
  induction cs with
  | nil => simp [splitRegular, Coeff.eval]
  | cons c cs ih =>
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hch⟩, hx, hl⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hch, List.map_append, List.sum_append, List.map_map,
        List.map_map]
      have e1 : ∀ p : List (Comp V) × Coeff, ((fun p : List (Comp V) × Coeff => p.2.eval D₀.m *
          ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) ∘
          fun p : List (Comp V) × Coeff => (p.1, mOf ch * p.2)) p =
          ch.apply D₀.m * (p.2.eval D₀.m *
            ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) := by
        intro p
        simp only [Function.comp_apply]
        rw [← ceval_mOf D₀.m ch]
        simp only [Coeff.eval, map_mul]
        ring
      have e2 : ∀ p : List (Comp V) × Coeff, ((fun p : List (Comp V) × Coeff => p.2.eval D₀.m *
          ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) ∘
          fun p : List (Comp V) × Coeff => ({ c with kind := Kind.light ch } :: p.1, p.2)) p =
          Comp.val D₀ σ { c with kind := Kind.light ch } * (p.2.eval D₀.m *
            ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) := by
        intro p
        simp only [Function.comp_apply, List.filter_cons, hl, Option.isNone_none, ite_true,
          List.map_cons, List.prod_cons]
        ring
      rw [List.map_congr_left fun p _ => e1 p, List.map_congr_left fun p _ => e2 p,
        List.sum_map_mul_left, List.sum_map_mul_left, ih]
      simp only [List.filter_cons, hl, Option.isNone_none, ite_true, List.map_cons, List.prod_cons]
      have hs := apply_split ch (Comp.gv D₀ σ c) D₀.m
      rw [val_weight_eq D₀ σ c hch,
        val_light_eq D₀ σ { c with kind := Kind.light ch, label := none } c hch rfl rfl rfl, hs]
      ring
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr', List.map_map]
      by_cases hl : c.label.isNone = true
      · have e : ∀ p : List (Comp V) × Coeff, ((fun p : List (Comp V) × Coeff => p.2.eval D₀.m *
            ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) ∘
            fun p : List (Comp V) × Coeff => (c :: p.1, p.2)) p =
            Comp.val D₀ σ c * (p.2.eval D₀.m *
              ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) := by
          intro p
          simp only [Function.comp_apply, List.filter_cons, hl, ite_true, List.map_cons,
            List.prod_cons]
          ring
        rw [List.map_congr_left fun p _ => e p, List.sum_map_mul_left, ih]
        simp only [List.filter_cons, hl, ite_true, List.map_cons, List.prod_cons]
      · have hl' : c.label.isNone = false := Bool.eq_false_iff.2 hl
        have e : ∀ p : List (Comp V) × Coeff, ((fun p : List (Comp V) × Coeff => p.2.eval D₀.m *
            ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod) ∘
            fun p : List (Comp V) × Coeff => (c :: p.1, p.2)) p =
            p.2.eval D₀.m *
              ((p.1.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod := by
          intro p
          simp only [Function.comp_apply, List.filter_cons, hl', Bool.false_eq_true, ite_false]
        rw [List.map_congr_left fun p _ => e p, ih]
        simp only [List.filter_cons, hl', Bool.false_eq_true, ite_false]

end SplitVal

/-! ## The terms of the light weight expansion have the conjugation property -/

section W2OK

variable {k n : ℕ}

/-- Proves `PB` of a list of explicit components. -/
local macro "pb_lit" : tactic =>
  `(tactic| repeat (first | exact PB_nil | refine PB_cons.2 ⟨⟨rfl, rfl⟩, ?_⟩))

private theorem w2E_OK (x : Atom k n) (Γ : Graph k n) (i : ℕ) (hPB : PB Γ.comps) :
    ∀ t ∈ w2E x Γ i, OK t.g.comps := by
  have hPBf : PB (w2f Γ i) := PB_sub hPB fun c hc => List.mem_of_mem_eraseIdx hc
  have hF1 : PB (liftCs 1 (w2f Γ i)) := PB_liftCs 1 hPBf
  have hF2 : PB (liftCs 2 (w2f Γ i)) := PB_liftCs 2 hPBf
  have hD1 : ∀ d ∈ dTerms (newA 0 : Atom k (n + 1)) (liftA 1 x) (liftCs 1 (w2f Γ i)), PB d :=
    dTerms_PB _ _ hF1
  have hD2 : ∀ d ∈ dTerms (newA 1 : Atom k (n + 2)) (newA 0) (liftCs 2 (w2f Γ i)), PB d :=
    dTerms_PB _ _ hF2
  unfold w2E
  refine fa_append (fa_append (fa_append (fa_append (fa_append ?_ ?_) ?_) ?_) ?_) ?_
  · refine fa_cons ?_ (fa_cons ?_ fa_nil)
    · exact OK_of_PB (PB_append.2 ⟨PB_liftCs 1 hPB, by pb_lit⟩)
    · exact OK_of_PB (PB_append.2 ⟨hF2, by pb_lit⟩)
  · exact fa_map fun d hd => OK_of_PB (PB_append.2 ⟨hD1 d hd, by pb_lit⟩)
  · exact fa_map fun d hd => OK_of_PB (PB_append.2 ⟨hD2 d hd, by pb_lit⟩)
  · refine fa_cons ?_ (fa_cons ?_ (fa_cons ?_ (fa_cons ?_ fa_nil)))
    · exact OK_labelQs x hPB
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF1, by pb_lit⟩)) (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF1, by pb_lit⟩)) (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF2, by pb_lit⟩)) (OK_of_PB (by pb_lit))
  · exact fa_map fun d hd => OK_append (OK_labelQs _ (PB_append.2 ⟨hD1 d hd, by pb_lit⟩))
      (OK_of_PB (by pb_lit))
  · exact fa_map fun d hd => OK_append (OK_labelQs _ (PB_append.2 ⟨hD2 d hd, by pb_lit⟩))
      (OK_of_PB (by pb_lit))

end W2OK

/-! ## The value of the weight expansion -/

section WeightValue

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  {k n : ℕ} (e : Fin k → ι) (ω : Ω)

private theorem S_oWeight1T (x : Atom k n) (Γ : Graph k n) :
    S PF D e ω (oWeight1T x Γ) = Γ.valR PF D e ω := by
  have h1 : S PF D e ω (oWeight1T x Γ) = ((splitRegular x Γ.comps).map fun p =>
      (⟨p.1, p.2 * Γ.coeff⟩ : Graph k n).valR PF D e ω).sum := by
    simp [oWeight1T, S, TExpansion.forget, Expansion.valR, List.map_map, Function.comp_def]
  rw [h1]
  simp only [Graph.valR]
  rw [list_sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hterm : ∀ p ∈ splitRegular x Γ.comps,
      (⟨p.1, p.2 * Γ.coeff⟩ : Graph k n).termR PF D (Sum.elim e s) ω =
      Γ.coeff.eval (D ω).m * (p.2.eval (D ω).m *
        ((p.1.filter fun c => c.label.isNone).map (Comp.val (D ω) (Sum.elim e s))).prod) *
      (Γ.labels.map fun ℓ => PF.op ℓ.1 (Sum.elim e s ℓ.2)
        (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (D ω') (Sum.elim e s))).prod) ω).prod := by
    intro p hp
    obtain ⟨h1, h2⟩ := splitRegular_labels x Γ.comps p hp
    unfold Graph.termR Graph.labels
    simp only [h1, h2]
    simp only [Coeff.eval, map_mul]
    ring
  rw [List.map_congr_left hterm, List.sum_map_mul_right, List.sum_map_mul_left,
    splitRegular_sum]
  rfl

private theorem S_bind_of (E : TExpansion k n)
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n')
    (h : ∀ {n' : ℕ} (f : Atom k n → Atom k n') (g : Graph k n'),
      S PF D e ω (O f g) = g.valR PF D e ω) :
    S PF D e ω (E.bind O) = S PF D e ω E := by
  induction E with
  | nil => rfl
  | cons t E ih =>
    have hb : TExpansion.bind (t :: E) O =
        (O t.f t.g).map (fun s => (⟨s.nOut, s.g, s.f ∘ t.f⟩ : Tracked k n)) ++
          TExpansion.bind E O := by
      simp [TExpansion.bind, List.flatMap_cons]
    rw [hb, S_append, ih, S_cons]
    congr 1
    rw [← h t.f t.g]
    simp [S, TExpansion.forget, List.map_map, Function.comp_def]

private theorem S_oDotT (g : Graph k n) : S PF D e ω (oDotT g) = g.valR PF D e ω := by
  have h := oDot_value k n Ω ι PF D trivial g e
  unfold oDot at h
  exact congrFun h ω

end WeightValue

/-! ## The value of the light weight expansion step -/

section W2Value

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} (e : Fin k → ι) (ω : Ω)

private theorem findIdx_some_of_pos_some {x : Atom k n} {Γ : Graph k n} {E : TExpansion k n}
    (h : oWeight2Pos x Γ = some E) :
    ∃ i, Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = some i := by
  by_contra hno
  push Not at hno
  have : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
    cases h' : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
    | none => rfl
    | some i => exact absurd h' (hno i)
  rw [← oWeight2Pos_none_iff, h] at this
  cases this

include A in
private theorem S_oWeight2T (x : Atom k n) (Γ : Graph k n) :
    S PF D e ω (oWeight2T x Γ) = Γ.valR PF D e ω := by
  have hself : ∀ Γ' : Graph k n, S PF D e ω [Tracked.self Γ'] = Γ'.valR PF D e ω := by
    intro Γ'
    simp [S, TExpansion.forget, Expansion.valR, Tracked.self]
  unfold oWeight2T
  by_cases hpl : (!(Γ.comps.all Comp.isPlainB)) = true
  · rw [ite_eq_left hpl]
    exact hself Γ
  · rw [ite_eq_right hpl]
    have hpl' : ∀ c ∈ Γ.comps, c.isPlainB = true := by
      simpa using hpl
    cases hpos : oWeight2Pos x Γ with
    | some E =>
      dsimp only
      obtain ⟨i, hi⟩ := findIdx_some_of_pos_some hpos
      rw [oWeight2Pos_eq hi] at hpos
      obtain rfl := Option.some.inj hpos
      obtain ⟨hlt, hk, hax⟩ := w2_setup hi
      exact wt_pos_valR A x Γ i hpl' hlt hk hax e ω
    | none =>
      dsimp only
      cases hpos' : oWeight2Pos x Γ.conj with
      | some E =>
        dsimp only
        obtain ⟨i, hi⟩ := findIdx_some_of_pos_some hpos'
        rw [oWeight2Pos_eq hi] at hpos'
        obtain rfl := Option.some.inj hpos'
        obtain ⟨hlt, hk, hax⟩ := w2_setup hi
        have hpl'' := conj_plain hpl'
        rw [S_conj A _ (w2E_OK x Γ.conj i (PB_of_plain hpl'')) e ω,
          wt_pos_valR (conjAdm A) x Γ.conj i hpl'' hlt hk hax e ω]
        exact (valR_eq_star A Γ hpl' e ω).symm
      | none =>
        dsimp only
        exact hself Γ

end W2Value

/-! ## The weight expansion preserves the value -/

section ChainValue

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} (e : Fin k → ι) (ω : Ω)

include A in
private theorem S_oWeightT (x : Atom k n) (Γ : Graph k n) :
    S PF D e ω (oWeightT x Γ) = Γ.valR PF D e ω := by
  unfold oWeightT
  split_ifs
  · rw [S_bind_of e ω _ (fun {n'} f g => oWeight1T (f x) g) (fun f g => S_oWeight1T e ω (f x) g),
      S_bind_of e ω _ (fun {n'} _ g => oDotT g) (fun f g => S_oDotT e ω g),
      S_bind_of e ω _ (fun {n'} f g => oWeight2T (f x) g)
        (fun f g => S_oWeight2T A e ω (f x) g),
      S_oWeight1T]
  · simp [S, TExpansion.forget, Expansion.valR, Tracked.self]

end ChainValue



/-- [I, Def 3.6] = [II, Def 4.3]: `O^{(x)}_weight` preserves the value of every graph under the
model relations ([I, (3.5)] and [I, (3.6)] for the light weight expansion; `m + (G_{xx} - m)` and
`O_dot` around it). -/
theorem oWeight_value (k n : ℕ) (x : Atom k n) :
    PreservesValue (oWeight x) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  funext ω
  exact S_oWeightT A e ω x Γ

/-- [I, Def 3.8 (ii)–(iv)] for `O^{(x)}_weight` with `C' = 2C + 16`: at an internal atom `x` of a
plain normal regular graph, every output graph is plain and normal regular with bound `2C + 16`,
has scaling order at least that of the input, and every new atom is joined to the image of `x` by
a path of waved edges. -/
theorem oWeight_canonical :
    CanonicalAt @oWeightT fun C => 2 * C + 16 := by
  intro k n C x Γ hx hN hP t ht
  rcases mem_oWeightT ht with ⟨-, rfl⟩ | ⟨t₁, h1, t₂, h2, t₃, h3, t₄, h4, rfl⟩
  · exact ⟨hN.mono (show C ≤ 2 * C + 16 by omega), hP, le_rfl, fun u hu => absurd rfl (hu u)⟩
  · exact canonical_chain hN hP hx h1 h2 h3 h4

section Instances

end Instances

end RBM8D.Graphs
