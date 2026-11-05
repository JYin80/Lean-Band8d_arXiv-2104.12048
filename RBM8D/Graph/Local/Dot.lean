import RBM8D.Graph.Local.Basic

/-!
# Dotted edge operations

`O_merge` and `O_dot` ([I, Defs 3.1, 3.2] = [II, Defs 4.1, 4.2]) and [I, Lemma 3.3].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The atoms of a graph, externals first. -/
def allAtoms (k n : ℕ) : List (Atom k n) :=
  (List.finRange k).map Sum.inl ++ (List.finRange n).map Sum.inr

/-- The partition `P` with the blocks of `u` and `v` joined. -/
def joinBlocks {V : Type*} [DecidableEq V] (P : List (List V)) (u v : V) : List (List V) :=
  P.filter (fun B => !(B.contains u || B.contains v)) ++
    [(P.filter fun B => B.contains u || B.contains v).flatten]

/-- The partition of the atoms `as` into the classes of atoms joined by paths of dotted edges. -/
def dotBlocks {V : Type*} [DecidableEq V] (as : List V) (cs : List (Comp V)) : List (List V) :=
  cs.foldl (fun P c => if c.kind = .dot then joinBlocks P c.x c.y else P) (as.map fun a => [a])

/-- The representative of the block of `u`: its first atom. -/
def blockRep {V : Type*} [DecidableEq V] (P : List (List V)) (u : V) : V :=
  match P.find? (fun B => B.contains u) with
  | some (r :: _) => r
  | _ => u

/-- The kind of a solid edge between identified atoms: the weight of the same charge. -/
def Kind.toWeight : Kind → Kind
  | .G c => .weight c
  | κ => κ

/-- The merging operation `O_merge` of [I, Def 3.1] = [II, Def 4.1]: internal atoms joined by a
path of dotted edges become one internal atom; solid edges between atoms joined by a path of
dotted edges become weights on their first end; dotted edges between identified atoms are
removed. External atoms are never identified with other atoms. The result is `none` when a
`×`-dotted edge joins two atoms joined by a path of dotted edges (the value is then `0`). -/
def Graph.mergeT {k n : ℕ} (Γ : Graph k n) : Option (Tracked k n) :=
  let P := dotBlocks (allAtoms k n) Γ.comps
  let rep := blockRep P
  if Γ.comps.any (fun c => c.kind == .xdot && rep c.x == rep c.y) then none else
  let roots := ((List.finRange n).map fun i => rep (Sum.inr i)).dedup
  let f : Atom k n → Atom k roots.length := fun u =>
    match u with
    | .inl a => .inl a
    | .inr i => .inr ⟨roots.idxOf (rep (.inr i)),
        List.idxOf_lt_length_of_mem
          (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩
  some ⟨roots.length,
    ⟨Γ.comps.filterMap fun c =>
      if c.kind == .dot && f c.x == f c.y then none
      else if c.kind.isSolid && rep c.x == rep c.y then
        some { c.map f with kind := c.kind.toWeight, y := f c.x }
      else some (c.map f), Γ.coeff⟩, f⟩

/-- The pairs of distinct atoms of [I, Def 3.2]: joined by a solid edge and by no `×`-dotted edge
(flag `true`), or by a `×`-dotted edge and by no solid edge (flag `false`). Each unordered pair
appears once. -/
def Graph.splitPairs {k n : ℕ} (Γ : Graph k n) : List (Atom k n × Atom k n × Bool) :=
  let joined (p : Kind → Bool) (u v : Atom k n) : Bool :=
    Γ.comps.any fun c => p c.kind && ((c.x == u && c.y == v) || (c.x == v && c.y == u))
  let cand := Γ.comps.filterMap fun c =>
    if (c.kind.isSolid || c.kind == .xdot) && c.x != c.y then some (c.x, c.y) else none
  let uniq := cand.foldl
    (fun acc p => if acc.any (fun q => q == p || q == p.swap) then acc else acc ++ [p]) []
  uniq.filterMap fun p =>
    let s := joined Kind.isSolid p.1 p.2
    let x := joined (· == .xdot) p.1 p.2
    if s != x then some (p.1, p.2, s) else none

/-- One term of the expansion of [I, Def 3.2]: the pairs of `A` get a dotted edge, the other
pairs with a solid edge get a `×`-dotted edge; the `×`-dotted edges of the pairs without solid
edge are removed, and each pair of `A` without solid edge contributes the sign `-1`
(`1_{α ≠ β} = 1 - 1_{α = β}`). -/
def Graph.dotChoice {k n : ℕ} (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    Graph k n :=
  let xonly (u v : Atom k n) : Bool :=
    SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))
  let kept := Γ.comps.filter fun c => !(c.kind == .xdot && xonly c.x c.y)
  let added := SP.filterMap fun p =>
    if p ∈ A then some (mkC .dot p.1 p.2.1) else if p.2.2 then some (mkC .xdot p.1 p.2.1)
    else none
  ⟨kept ++ added, (-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * Γ.coeff⟩

/-- The dotted edge partition `O_dot` of [I, Def 3.2] = [II, Def 4.2], tracked: the sum over all
choices of `dotChoice` followed by `O_merge`, inconsistent choices dropped. It is the identity on
graphs with no pair to split, no dotted edge between internal atoms and no solid self-loop (in
particular on normal regular graphs), on graphs with two or more distinct `P`/`Q` labels, and on
graphs with a labelled dotted or `×`-dotted edge. -/
def oDotT {k n : ℕ} (Γ : Graph k n) : TExpansion k n :=
  let SP := Γ.splitPairs
  if 2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true then
    [Tracked.self Γ]
  else if SP.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y)) then
    [Tracked.self Γ]
  else SP.sublists.filterMap fun A => (Γ.dotChoice SP A).mergeT

/-- The dotted edge partition `O_dot` ([I, Def 3.2] = [II, Def 4.2]). -/
def oDot {k n : ℕ} (Γ : Graph k n) : Expansion k := (oDotT Γ).forget

/-- The admissibility predicate that holds for every data record and every family. -/
def anyAdm : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι], PFamily Ω ι → (Ω → Data ι) → Prop :=
  fun _ _ _ _ _ _ => True

/-! ## Dot blocks -/

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
        -- every element of the joined block is connected to `c.x` by dotted edges
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

private theorem blockRep_spec (P : List (List V)) (u : V) :
    blockRep P u = u ∨ ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
  unfold blockRep
  generalize hf : P.find? (fun B => B.contains u) = o
  rcases o with _ | ⟨_ | ⟨r, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    refine ⟨r :: rest, List.mem_of_find?_eq_some hf, ?_, List.mem_cons_self ..⟩
    simpa [List.contains_iff_mem] using List.find?_some hf

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

private theorem Graph.mrep_conn (Γ : Graph k n) (u : Atom k n) :
    Relation.EqvGen (dotRel Γ.comps) u (Γ.mrep u) := by
  rcases blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : Γ.mrep u = u := h
    rw [this]
    exact Relation.EqvGen.refl _
  · exact dotBlocks_conn _ _ B hB u hu _ hr

private theorem eqvGen_dotRel_eq {V ι : Type*} {cs : List (Comp V)} (σ : V → ι)
    (hz : ∀ c ∈ cs, c.kind = .dot → σ c.x = σ c.y) {u v : V}
    (h : Relation.EqvGen (dotRel cs) u v) : σ u = σ v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact hz c hc hk
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- A labelling that agrees on the ends of every dotted component is constant on the blocks. -/
private theorem Graph.sigma_rep (Γ : Graph k n) {ι : Type*} (σ : Atom k n → ι)
    (hz : ∀ c ∈ Γ.comps, c.kind = .dot → σ c.x = σ c.y) (u : Atom k n) :
    σ (Γ.mrep u) = σ u :=
  (eqvGen_dotRel_eq σ hz (Γ.mrep_conn u)).symm

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

private theorem mergeT_none {Γ : Graph k n} (h : Γ.mergeT = none) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ Γ.mrep c.x = Γ.mrep c.y := by
  rw [mergeT_eq] at h
  split_ifs at h with hc
  rw [List.any_eq_true] at hc
  obtain ⟨c, hc, hb⟩ := hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨c, hc, hb.1, hb.2⟩

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

/-! ## Products over lists -/

section ListLemmas

private theorem prod_map_filter_filterMap {α β : Type*} (cs : List α) (φ : α → Option β)
    (p : α → Bool) (p' : β → Bool) (v : α → ℂ) (v' : β → ℂ)
    (hφ : ∀ c ∈ cs, ∀ c', φ c = some c' → p' c' = p c ∧ v' c' = v c)
    (hn : ∀ c ∈ cs, φ c = none → p c = false ∨ v c = 1) :
    (((cs.filterMap φ).filter p').map v').prod = ((cs.filter p).map v).prod := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih (fun c hc => hφ c (List.mem_cons_of_mem _ hc))
      (fun c hc => hn c (List.mem_cons_of_mem _ hc))
    by_cases hφc : φ c = none
    · rw [List.filterMap_cons_none hφc]
      rcases hn c (List.mem_cons_self ..) hφc with h | h
      · rw [List.filter_cons_of_neg (by simp [h])]
        exact ih'
      · by_cases hp : p c = true
        · rw [List.filter_cons_of_pos hp, List.map_cons, List.prod_cons, h, one_mul]
          exact ih'
        · rw [List.filter_cons_of_neg hp]
          exact ih'
    · obtain ⟨c', hc'⟩ := Option.ne_none_iff_exists'.1 hφc
      obtain ⟨h1, h2⟩ := hφ c (List.mem_cons_self ..) c' hc'
      rw [List.filterMap_cons_some hc']
      by_cases hp : p c = true
      · rw [List.filter_cons_of_pos (by rw [h1]; exact hp), List.filter_cons_of_pos hp,
          List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, h2, ih']
      · rw [List.filter_cons_of_neg (by rw [h1]; exact hp), List.filter_cons_of_neg hp]
        exact ih'

private theorem dedup_eq_singleton {α : Type*} [DecidableEq α] (l : List α) (a : α)
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

/-- A list of components with at most one distinct label: either no label at all, or all labels
equal. -/
private theorem labels_cases {V : Type*} [DecidableEq V] (cs : List (Comp V))
    (hl : (cs.filterMap Comp.label).dedup.length ≤ 1) :
    (∀ c ∈ cs, c.label = none) ∨
      ∃ ℓ, (∀ c ∈ cs, c.label = none ∨ c.label = some ℓ) ∧ ∃ c ∈ cs, c.label = some ℓ := by
  by_cases h : ∀ c ∈ cs, c.label = none
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨c₀, hc₀, hne⟩ := h
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hne
    refine ⟨ℓ, ?_, c₀, hc₀, hℓ⟩
    intro c hc
    rcases hcl : c.label with _ | ℓ'
    · exact Or.inl rfl
    · right
      have h1 : ℓ' ∈ (cs.filterMap Comp.label).dedup :=
        List.mem_dedup.2 (List.mem_filterMap.2 ⟨c, hc, hcl⟩)
      have h2 : ℓ ∈ (cs.filterMap Comp.label).dedup :=
        List.mem_dedup.2 (List.mem_filterMap.2 ⟨c₀, hc₀, hℓ⟩)
      generalize (cs.filterMap Comp.label).dedup = d at hl h1 h2
      rcases d with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · simp at h1
      · simp only [List.mem_singleton] at h1 h2
        rw [h1, h2]
      · simp at hl

end ListLemmas

/-! ## The value of `O_merge` -/

section MergeValue

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]

private theorem Comp.val_map {V W : Type*} (D : Data ι) (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

private theorem mergeComp_label {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) := by
  unfold mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    rfl

private theorem mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : mergeComp rep f c = none) : c.kind = .dot ∧ f c.x = f c.y := by
  unfold mergeComp at h
  split_ifs at h with h1
  simpa using h1

private theorem mergeComp_isSome {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    {c : Comp (Atom k n)} (h : ¬ (c.kind = .dot ∧ f c.x = f c.y)) :
    ∃ c', mergeComp rep f c = some c' := by
  unfold mergeComp
  split_ifs with h1 h2
  · exact absurd (by simpa using h1) h
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem mergeComp_of_not_solid {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = false)
    (h : ¬ (c.kind = .dot ∧ f c.x = f c.y)) : mergeComp rep f c = some (c.map f) := by
  unfold mergeComp
  split_ifs with h1 h2
  · exact absurd (by simpa using h1) h
  · simp [hs] at h2
  · rfl

private theorem mergeComp_val {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    (D₀ : Data ι) (σ' : Atom k m → ι) {c : Comp (Atom k n)} {c' : Comp (Atom k m)}
    (h : mergeComp rep f c = some c')
    (hs : c.kind.isSolid = true → rep c.x = rep c.y → σ' (f c.x) = σ' (f c.y)) :
    Comp.val D₀ σ' c' = Comp.val D₀ (σ' ∘ f) c := by
  unfold mergeComp at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have hsolid : c.kind.isSolid = true := h2.1
    have hrep : rep c.x = rep c.y := h2.2
    have hσ := hs hsolid hrep
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    simp only [Comp.val, Comp.map, List.map_map, hch, Kind.toWeight, Function.comp_apply, hσ]
  · obtain rfl := Option.some.inj h
    exact Comp.val_map D₀ σ' f c

end MergeValue

section MergeValue2

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]

private theorem termR_eq_zero_of_val {Γ : Graph k n} (PF : PFamily Ω ι) (D : Ω → Data ι)
    (σ : Atom k n → ι) (ω : Ω) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hl : c.label = none)
    (h0 : Comp.val (D ω) σ c = 0) : Γ.termR PF D σ ω = 0 := by
  unfold Graph.termR
  have : ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl]⟩, h0⟩)
  rw [this]
  simp

private theorem mergeComp_kind {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : mergeComp rep f c = some c') :
    c'.kind = c.kind ∨ ∃ ch, c.kind = .G ch ∧ c'.kind = .weight ch := by
  unfold mergeComp at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    right
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have hsolid : c.kind.isSolid = true := h2.1
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    exact ⟨ch, hch, by simp [hch, Kind.toWeight]⟩
  · obtain rfl := Option.some.inj h
    left
    rfl

private theorem MergeSpec.termR_eq {Γ : Graph k n} {t : Tracked k n} (hs : MergeSpec Γ t)
    (hl : Γ.labels.length ≤ 1)
    (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ' : Atom k t.nOut → ι) (ω : Ω)
    (hz : ∀ c ∈ Γ.comps, c.kind = .dot → σ' (t.f c.x) = σ' (t.f c.y)) :
    t.g.termR PF D σ' ω = Γ.termR PF D (σ' ∘ t.f) ω := by
  have hrep : ∀ c ∈ Γ.comps, Γ.mrep c.x = Γ.mrep c.y → σ' (t.f c.x) = σ' (t.f c.y) := by
    intro c _ hr
    have h1 := Γ.sigma_rep (σ' ∘ t.f) hz c.x
    have h2 := Γ.sigma_rep (σ' ∘ t.f) hz c.y
    simp only [Function.comp_apply] at h1 h2
    rw [← h1, ← h2, hr]
  have key : ∀ (p : Option (PQ × Atom k n) → Bool) (p' : Option (PQ × Atom k t.nOut) → Bool),
      (∀ c ∈ Γ.comps, ∀ c', mergeComp Γ.mrep t.f c = some c' → p' c'.label = p c.label) →
      ∀ D₀ : Data ι, ((t.g.comps.filter fun c => p' c.label).map (Comp.val D₀ σ')).prod =
        ((Γ.comps.filter fun c => p c.label).map (Comp.val D₀ (σ' ∘ t.f))).prod := by
    intro p p' hp D₀
    rw [hs.comps_eq]
    apply prod_map_filter_filterMap
    · intro c hc c' hc'
      exact ⟨hp c hc c' hc', mergeComp_val D₀ σ' hc' (fun _ hr => hrep c hc hr)⟩
    · intro c hc hnone
      obtain ⟨hk, hf⟩ := mergeComp_none hnone
      right
      simp [Comp.val, hk, Function.comp_apply, hf]
  have hU := key (fun o => o.isNone) (fun o => o.isNone) (by
    intro c _ c' hc'
    rw [mergeComp_label hc']
    simp)
  rcases labels_cases Γ.comps hl with hnone | ⟨ℓ, hℓ, c₀, hc₀, hc₀ℓ⟩
  · have hg : Γ.labels = [] := by
      unfold Graph.labels
      rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
      exact hnone
    have ht : t.g.labels = [] := by
      unfold Graph.labels
      rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
      intro c' hc'
      rw [hs.comps_eq, List.mem_filterMap] at hc'
      obtain ⟨c, hc, hc'⟩ := hc'
      rw [mergeComp_label hc', hnone c hc]
      rfl
    unfold Graph.termR
    rw [hg, ht, hs.coeff_eq]
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [hU]
  · have hg : Γ.labels = [ℓ] := by
      unfold Graph.labels
      apply dedup_eq_singleton
      · intro x hx
        obtain ⟨c, hc, hcx⟩ := List.mem_filterMap.1 hx
        rcases hℓ c hc with h | h
        · rw [h] at hcx; cases hcx
        · rw [h] at hcx; exact (Option.some.inj hcx).symm
      · exact List.mem_filterMap.2 ⟨c₀, hc₀, hc₀ℓ⟩
    have ht : t.g.labels = [Prod.map id t.f ℓ] := by
      unfold Graph.labels
      apply dedup_eq_singleton
      · intro x hx
        obtain ⟨c', hc', hcx⟩ := List.mem_filterMap.1 hx
        rw [hs.comps_eq, List.mem_filterMap] at hc'
        obtain ⟨c, hc, hc'⟩ := hc'
        rw [mergeComp_label hc'] at hcx
        rcases hℓ c hc with h | h
        · rw [h] at hcx; cases hcx
        · rw [h] at hcx
          exact (Option.some.inj hcx).symm
      · have hnd : ¬ (c₀.kind = .dot ∧ t.f c₀.x = t.f c₀.y) := by
          rintro ⟨hk, -⟩
          have := hlab c₀ hc₀ (Or.inl hk)
          rw [hc₀ℓ] at this
          cases this
        obtain ⟨c', hc'⟩ := mergeComp_isSome Γ.mrep t.f hnd
        refine List.mem_filterMap.2 ⟨c', ?_, ?_⟩
        · rw [hs.comps_eq]
          exact List.mem_filterMap.2 ⟨c₀, hc₀, hc'⟩
        · rw [mergeComp_label hc', hc₀ℓ]
          rfl
    unfold Graph.termR
    rw [hg, ht, hs.coeff_eq]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hU]
    congr 1
    change PF.op ℓ.1 (σ' (t.f ℓ.2)) _ ω = PF.op ℓ.1 ((σ' ∘ t.f) ℓ.2) _ ω
    congr 2
    funext ω'
    exact key (fun o => decide (o = some ℓ)) (fun o => decide (o = some (Prod.map id t.f ℓ))) (by
      intro c hc c' hc'
      rw [mergeComp_label hc']
      rcases hℓ c hc with h | h <;> simp [h]) (D ω')

end MergeValue2

/-! ## The pairs to split -/

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

private theorem splitPairs_nodup (Γ : Graph k n) : Γ.splitPairs.Nodup := by
  rw [splitPairs_eq]
  apply List.Nodup.filterMap
  · have key : ∀ (x : Atom k n × Atom k n) (b : Atom k n × Atom k n × Bool),
        b ∈ (if (spJoined Γ Kind.isSolid x.1 x.2 != spJoined Γ (· == .xdot) x.1 x.2) = true then
          some (x.1, x.2, spJoined Γ Kind.isSolid x.1 x.2) else none) →
        b.1 = x.1 ∧ b.2.1 = x.2 := by
      intro x b hx
      split_ifs at hx
      · rw [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact ⟨rfl, rfl⟩
      · simp at hx
    intro a a' b hb hb'
    obtain ⟨h1, h2⟩ := key a b hb
    obtain ⟨h3, h4⟩ := key a' b hb'
    exact Prod.ext (h1.symm.trans h3) (h2.symm.trans h4)
  · exact (spUniq_pairwise Γ).imp fun {a b} h hab => h (Or.inl hab.symm)

end SplitPairs

/-! ## Algebra of the expansion of `O_dot` -/

section DotAlgebra

/-- The distributive law over the sublists of a list without repetitions. -/
private theorem sum_sublists_prod {α : Type*} [BEq α] [LawfulBEq α] (s a b : α → ℂ) :
    ∀ L : List α, L.Nodup →
      (L.sublists.map fun A =>
        (A.map s).prod * (L.map fun p => if p ∈ A then a p else b p).prod).sum =
        (L.map fun p => b p + s p * a p).prod := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons p L ih =>
    intro hnd
    have hp : p ∉ L := (List.nodup_cons.1 hnd).1
    have hL := (List.nodup_cons.1 hnd).2
    rw [((List.sublists_cons_perm_append p L).map _).sum_eq, List.map_append, List.sum_append,
      List.map_map, List.map_cons, List.prod_cons, ← ih hL]
    have h1 : (L.sublists.map fun A =>
        (A.map s).prod * ((p :: L).map fun q => if q ∈ A then a q else b q).prod) =
        L.sublists.map fun A => b p *
          ((A.map s).prod * (L.map fun q => if q ∈ A then a q else b q).prod) := by
      apply List.map_congr_left
      intro A hA
      have hpA : p ∉ A := fun h => hp ((List.mem_sublists.1 hA).subset h)
      simp only [List.map_cons, List.prod_cons, ite_eq_right hpA]
      ring
    have h2 : (L.sublists.map ((fun A =>
        (A.map s).prod * ((p :: L).map fun q => if q ∈ A then a q else b q).prod) ∘
          List.cons p)) =
        L.sublists.map fun A => s p * a p *
          ((A.map s).prod * (L.map fun q => if q ∈ A then a q else b q).prod) := by
      apply List.map_congr_left
      intro A _
      simp only [Function.comp_apply, List.map_cons, List.prod_cons]
      rw [ite_eq_left (List.mem_cons_self ..)]
      have : (L.map fun q => if q ∈ p :: A then a q else b q) =
          L.map fun q => if q ∈ A then a q else b q := by
        apply List.map_congr_left
        intro q hq
        have hqp : q ≠ p := fun h => hp (h ▸ hq)
        by_cases hqA : q ∈ A
        · rw [ite_eq_left (List.mem_cons_of_mem _ hqA), ite_eq_left hqA]
        · have : q ∉ p :: A := fun h => by
            rcases List.mem_cons.1 h with h | h
            · exact hqp h
            · exact hqA h
          rw [ite_eq_right this, ite_eq_right hqA]
      rw [this]
      ring
    rw [h1, h2, List.sum_map_mul_left, List.sum_map_mul_left]
    ring

private theorem prod_filterMap_map {α β : Type*} (l : List α) (φ : α → Option β) (v : β → ℂ) :
    ((l.filterMap φ).map v).prod = (l.map fun a => match φ a with
      | some b => v b | none => 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hφ : φ a with
    | none => rw [List.filterMap_cons_none hφ, ih, List.map_cons, List.prod_cons]; simp [hφ]
    | some b =>
      rw [List.filterMap_cons_some hφ, List.map_cons, List.prod_cons, ih, List.map_cons,
        List.prod_cons]
      simp [hφ]

private theorem prod_01 {α : Type*} (l : List α) (g : α → ℂ) (h : ∀ x ∈ l, g x = 0 ∨ g x = 1) :
    (l.map g).prod = if ∀ x ∈ l, g x = 1 then 1 else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rcases h x (List.mem_cons_self ..) with hx | hx
    · have : ¬ ∀ y ∈ x :: l, g y = 1 := fun H => by
        have := H x (List.mem_cons_self ..)
        rw [hx] at this
        exact zero_ne_one this
      rw [ite_eq_right this, hx]
      simp
    · simp only [hx, one_mul, List.mem_cons, forall_eq_or_imp, true_and]

private theorem prod_map_filter_split {α : Type*} (l : List α) (r : α → Bool) (u : α → ℂ) :
    (l.map u).prod = ((l.filter r).map u).prod * ((l.filter fun x => !r x).map u).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases hx : r x = true
    · rw [List.filter_cons_of_pos hx, List.filter_cons_of_neg (by simp [hx]), List.map_cons,
        List.prod_cons]
      ring
    · have hx' : r x = false := by simpa using hx
      rw [List.filter_cons_of_neg hx, List.filter_cons_of_pos (by simp [hx']), List.map_cons,
        List.prod_cons]
      ring

private theorem prod_filter_isNone {V : Type*} (l : List (Comp V)) (v : Comp V → ℂ) :
    ((l.filter fun c => c.label.isNone).map v).prod =
      (l.map fun c => if c.label.isNone then v c else 1).prod := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    by_cases h : c.label.isNone = true
    · rw [List.filter_cons_of_pos (p := fun c : Comp V => c.label.isNone) (a := c) h,
        List.map_cons, List.prod_cons]
      simp [h]
    · rw [List.filter_cons_of_neg (p := fun c : Comp V => c.label.isNone) (a := c) h]
      simp [h]

private theorem neg_one_pow_filter {α : Type*} (A : List α) (q : α → Bool) :
    (-1 : ℂ) ^ (A.filter q).length = (A.map fun p => if q p then (-1 : ℂ) else 1).prod := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    by_cases h : q p = true
    · rw [List.filter_cons_of_pos h, List.length_cons, pow_succ, ite_eq_left h]
      ring
    · rw [List.filter_cons_of_neg h, ite_eq_right h, one_mul]

private theorem list_sum_map_finset_sum {α ι' : Type*} [Fintype ι'] (l : List α)
    (F : α → ι' → ℂ) :
    (l.map fun a => ∑ s, F a s).sum = ∑ s, (l.map fun a => F a s).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [List.map_cons, List.sum_cons]

private theorem sum_filterMap_map {α β : Type*} (l : List α) (φ : α → Option β) (w : β → ℂ) :
    ((l.filterMap φ).map w).sum = (l.map fun a => (φ a).elim 0 w).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hφ : φ a with
    | none => rw [List.filterMap_cons_none hφ, ih, List.map_cons, List.sum_cons]; simp [hφ]
    | some b =>
      rw [List.filterMap_cons_some hφ, List.map_cons, List.sum_cons, ih, List.map_cons,
        List.sum_cons]
      simp [hφ]

private theorem filter_filter_of_imp {α : Type*} (l : List α) (r q : α → Bool)
    (h : ∀ x ∈ l, q x = true → r x = true) : (l.filter r).filter q = l.filter q := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  by_cases hq : q x = true
  · simp [hq, h x hx hq]
  · simp [show q x = false by simpa using hq]

private theorem filterMap_filter_of_none {α β : Type*} (l : List α) (r : α → Bool)
    (f : α → Option β) (h : ∀ x ∈ l, r x = false → f x = none) :
    (l.filter r).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx : r x = true
    · rw [List.filter_cons_of_pos hx]
      cases hf : f x with
      | none => rw [List.filterMap_cons_none hf, List.filterMap_cons_none hf, ih']
      | some b => rw [List.filterMap_cons_some hf, List.filterMap_cons_some hf, ih']
    · have hx' : r x = false := by simpa using hx
      rw [List.filter_cons_of_neg hx, ih',
        List.filterMap_cons_none (h x (List.mem_cons_self ..) hx')]

end DotAlgebra

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

section Labels

variable (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
  (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
include hlab

private theorem dotChoice_filterMap_label :
    (Γ.dotChoice SP A).comps.filterMap Comp.label = Γ.comps.filterMap Comp.label := by
  rw [dotChoice_eq]
  change (keptComps Γ SP ++ addedComps SP A).filterMap Comp.label = _
  rw [List.filterMap_append]
  have h1 : (addedComps SP A).filterMap Comp.label = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    exact (addedComps_label hc).1
  rw [h1, List.append_nil]
  unfold keptComps
  apply filterMap_filter_of_none
  intro c hc hr
  apply hlab c hc
  right
  exact (by simpa using hr : c.kind = .xdot ∧ xonlyB SP c.x c.y = true).1

private theorem dotChoice_filter (ℓ : PQ × Atom k n) :
    (Γ.dotChoice SP A).comps.filter (fun c => decide (c.label = some ℓ)) =
      Γ.comps.filter (fun c => decide (c.label = some ℓ)) := by
  rw [dotChoice_eq]
  change (keptComps Γ SP ++ addedComps SP A).filter _ = _
  rw [List.filter_append]
  have h1 : (addedComps SP A).filter (fun c => decide (c.label = some ℓ)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    simp [(addedComps_label hc).1]
  rw [h1, List.append_nil]
  unfold keptComps
  apply filter_filter_of_imp
  intro c hc hq
  have : c.label = some ℓ := by simpa using hq
  have hne : ¬ (c.kind = .xdot) := by
    intro hk
    rw [hlab c hc (Or.inr hk)] at this
    cases this
  simp [hne]

private theorem dotChoice_hlab :
    ∀ c ∈ (Γ.dotChoice SP A).comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
  intro c hc hk
  rw [dotChoice_eq] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hlab c ((mem_keptComps Γ SP c).1 hc).1 hk
  · exact (addedComps_label hc).1

private theorem dotChoice_labels_length (hl : Γ.labels.length ≤ 1) :
    (Γ.dotChoice SP A).labels.length ≤ 1 := by
  unfold Graph.labels at hl ⊢
  rw [dotChoice_filterMap_label Γ SP A hlab]
  exact hl

end Labels

end DotChoice

section DotSum

variable {k n : ℕ}

private theorem sp_false {Γ : Graph k n} {p : Atom k n × Atom k n × Bool}
    (hp : p ∈ Γ.splitPairs) (hf : p.2.2 = false) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = p.1 ∧ c.y = p.2.1 ∨ c.x = p.2.1 ∧ c.y = p.1) := by
  obtain ⟨-, hne, hs⟩ := mem_splitPairs.1 hp
  rw [hf] at hs
  have hx : spJoined Γ (· == .xdot) p.1 p.2.1 = true := by
    cases h : spJoined Γ (· == .xdot) p.1 p.2.1
    · rw [← hs, h] at hne
      simp at hne
    · rfl
  obtain ⟨c, hc, hk, hm⟩ := (spJoined_iff _ _ _ _).1 hx
  exact ⟨c, hc, by simpa using hk, hm⟩

private theorem sp_true {Γ : Graph k n} {p : Atom k n × Atom k n × Bool}
    (hp : p ∈ Γ.splitPairs) (ht : p.2.2 = true) :
    ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = p.1 ∧ c.y = p.2.1 ∨ c.x = p.2.1 ∧ c.y = p.1) := by
  obtain ⟨-, -, hs⟩ := mem_splitPairs.1 hp
  rw [ht] at hs
  obtain ⟨c, hc, hk, hm⟩ := (spJoined_iff _ _ _ _).1 hs.symm
  exact ⟨c, hc, hk, hm⟩

/-- The factor of a value coming from the labels. -/
private def labelFactor {Ω ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) : ℂ :=
  (Γ.labels.map fun ℓ =>
    PF.op ℓ.1 (σ ℓ.2)
      (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) ω).prod

private theorem termR_eq_factors {Ω ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) :
    Γ.termR PF D σ ω = Γ.coeff.eval (D ω).m *
      ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod *
        labelFactor Γ PF D σ ω := rfl

private theorem labelFactor_dotChoice {Ω ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (SP A : List (Atom k n × Atom k n × Bool))
    (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) :
    labelFactor (Γ.dotChoice SP A) PF D σ ω = labelFactor Γ PF D σ ω := by
  have h1 : (Γ.dotChoice SP A).labels = Γ.labels := by
    unfold Graph.labels
    rw [dotChoice_filterMap_label Γ SP A hlab]
  unfold labelFactor
  rw [h1]
  simp only [dotChoice_filter Γ SP A hlab]

private theorem dotChoice_sum {Ω ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) :
    (Γ.splitPairs.sublists.map fun A =>
      (Γ.dotChoice Γ.splitPairs A).termR PF D σ ω).sum = Γ.termR PF D σ ω := by
  set SP := Γ.splitPairs with hSP
  have hnd : SP.Nodup := splitPairs_nodup Γ
  set val := Comp.val (D ω) σ with hval
  set s : (Atom k n × Atom k n × Bool) → ℂ := fun p => if p.2.2 then 1 else -1 with hs
  set a : (Atom k n × Atom k n × Bool) → ℂ := fun p => val (mkC .dot p.1 p.2.1) with ha
  set b : (Atom k n × Atom k n × Bool) → ℂ :=
    fun p => if p.2.2 then val (mkC .xdot p.1 p.2.1) else 1 with hb
  set Uk : ℂ := (((keptComps Γ SP).filter fun c => c.label.isNone).map val).prod with hUk
  set Lf : ℂ := labelFactor Γ PF D σ ω with hLf
  set ev : ℂ := Γ.coeff.eval (D ω).m with hev
  have hterm : ∀ A : List (Atom k n × Atom k n × Bool),
      (Γ.dotChoice SP A).termR PF D σ ω = (ev * Uk * Lf) *
        ((A.map s).prod * (SP.map fun p => if p ∈ A then a p else b p).prod) := by
    intro A
    rw [termR_eq_factors, labelFactor_dotChoice Γ SP A hlab, dotChoice_eq]
    change (Coeff.eval (D ω).m ((-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * Γ.coeff)) *
      (((keptComps Γ SP ++ addedComps SP A).filter fun c => c.label.isNone).map val).prod *
        Lf = _
    have h1 : Coeff.eval (D ω).m ((-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * Γ.coeff) =
        (-1 : ℂ) ^ (A.filter fun p => !p.2.2).length * ev := by
      simp [Coeff.eval, hev]
    have h2 : ((keptComps Γ SP ++ addedComps SP A).filter fun c => c.label.isNone).map val =
        ((keptComps Γ SP).filter fun c => c.label.isNone).map val ++
          (addedComps SP A).map val := by
      rw [List.filter_append, List.map_append]
      congr 2
      rw [List.filter_eq_self]
      intro c hc
      simp [(addedComps_label hc).1]
    have h3 : ((addedComps SP A).map val).prod =
        (SP.map fun p => if p ∈ A then a p else b p).prod := by
      unfold addedComps
      rw [prod_filterMap_map]
      congr 1
      apply List.map_congr_left
      intro p _
      by_cases hpA : p ∈ A
      · simp [hpA, ha]
      · by_cases hpf : p.2.2 = true <;> simp [hpA, hpf, hb]
    have h4 : (-1 : ℂ) ^ (A.filter fun p => !p.2.2).length = (A.map s).prod := by
      rw [neg_one_pow_filter]
      congr 1
      apply List.map_congr_left
      intro p _
      cases hf : p.2.2 <;> simp [hs, hf]
    rw [h1, h2, List.prod_append, h3, h4]
    ring
  -- the sum over the sublists
  have hsum : (SP.sublists.map fun A => (Γ.dotChoice SP A).termR PF D σ ω).sum =
      (ev * Uk * Lf) * (SP.map fun p => b p + s p * a p).prod := by
    rw [← sum_sublists_prod s a b SP hnd, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro A _
    exact hterm A
  rw [hsum, termR_eq_factors]
  -- the unlabelled product of `Γ`
  have hY : (SP.map fun p => b p + s p * a p) = SP.map fun p =>
      if p.2.2 then (1 : ℂ) else (if σ p.1 = σ p.2.1 then 0 else 1) := by
    apply List.map_congr_left
    intro p _
    cases hf : p.2.2 <;> by_cases he : σ p.1 = σ p.2.1 <;>
      simp [hs, ha, hb, hval, Comp.val, mkC, hf, he]
  have hXform : ((Γ.comps.filter fun c => c.label.isNone).map val).prod =
      Uk * ((Γ.comps.filter fun c => c.kind == .xdot && xonlyB SP c.x c.y).map val).prod := by
    rw [prod_filter_isNone,
      prod_map_filter_split Γ.comps (fun c => !(c.kind == .xdot && xonlyB SP c.x c.y))]
    congr 1
    · rw [hUk, prod_filter_isNone]
      rfl
    · have hf : (Γ.comps.filter fun x => !!(x.kind == .xdot && xonlyB SP x.x x.y)) =
          Γ.comps.filter fun c => c.kind == .xdot && xonlyB SP c.x c.y := by
        apply List.filter_congr
        intro x _
        exact Bool.not_not _
      rw [hf]
      congr 1
      apply List.map_congr_left
      intro x hx
      obtain ⟨hxc, hxb⟩ := List.mem_filter.1 hx
      have hxk : x.kind = .xdot := by simpa using (Bool.and_eq_true_iff.1 hxb).1
      simp [hlab x hxc (Or.inr hxk)]
  rw [hXform, hY]
  have hval01 : ∀ c ∈ Γ.comps.filter (fun c => c.kind == .xdot && xonlyB SP c.x c.y),
      val c = 0 ∨ val c = 1 := by
    intro c hc
    have hck : c.kind = .xdot := by
      simpa using (Bool.and_eq_true_iff.1 (List.mem_filter.1 hc).2).1
    simp only [hval, Comp.val, hck]
    split_ifs <;> simp
  have hg01 : ∀ p ∈ SP, (if p.2.2 then (1 : ℂ) else (if σ p.1 = σ p.2.1 then 0 else 1)) = 0 ∨
      (if p.2.2 then (1 : ℂ) else (if σ p.1 = σ p.2.1 then 0 else 1)) = 1 := by
    intro p _
    split_ifs <;> simp
  rw [prod_01 _ _ hval01, prod_01 _ _ hg01]
  have hiff : (∀ c ∈ Γ.comps.filter (fun c => c.kind == .xdot && xonlyB SP c.x c.y), val c = 1) ↔
      (∀ p ∈ SP, (if p.2.2 then (1 : ℂ) else (if σ p.1 = σ p.2.1 then 0 else 1)) = 1) := by
    constructor
    · intro H p hp
      cases hf : p.2.2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨c, hc, hk, hm⟩ := sp_false hp hf
        have hcm : c ∈ Γ.comps.filter (fun c => c.kind == .xdot && xonlyB SP c.x c.y) := by
          rw [List.mem_filter]
          refine ⟨hc, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq]
          refine ⟨hk, (xonlyB_iff _ _ _).2 ⟨p, hp, hf, ?_⟩⟩
          rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h2.symm, h1.symm⟩
        have := H c hcm
        simp only [hval, Comp.val, hk] at this
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at this
          split_ifs at this ⊢ <;> simp_all
        · rw [h1, h2] at this
          split_ifs at this ⊢ <;> simp_all
      · simp
    · intro H c hc
      obtain ⟨hcm, hcb⟩ := List.mem_filter.1 hc
      obtain ⟨hk, hx⟩ := Bool.and_eq_true_iff.1 hcb
      have hk' : c.kind = .xdot := by simpa using hk
      obtain ⟨p, hp, hf, hm⟩ := (xonlyB_iff _ _ _).1 hx
      have := H p hp
      rw [hf] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      simp only [hval, Comp.val, hk']
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
        split_ifs at this ⊢ <;> simp_all
      · rw [← h1, ← h2]
        split_ifs at this ⊢ <;> simp_all
  by_cases hc : ∀ c ∈ Γ.comps.filter (fun c => c.kind == .xdot && xonlyB SP c.x c.y), val c = 1
  · rw [ite_eq_left hc, ite_eq_left (hiff.1 hc)]
    ring
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.2 h))]
    ring

end DotSum

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

private theorem oDotT_branch3 {Γ : Graph k n}
    (h1 : ¬ (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true))
    (h2 : ¬ (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true) :
    oDotT Γ = Γ.splitPairs.sublists.filterMap fun A => (Γ.dotChoice Γ.splitPairs A).mergeT := by
  unfold oDotT
  dsimp only
  rw [ite_eq_right h1, ite_eq_right h2]

/-- If `oDotT` is not in its first case, `Γ` has at most one distinct label and no labelled
dotted or `×`-dotted edge. -/
private theorem not_branch1 {Γ : Graph k n}
    (h : ¬ (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true)) :
    Γ.labels.length ≤ 1 ∧
      ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
  refine ⟨by omega, ?_⟩
  intro c hc hk
  by_contra hne
  apply h
  right
  rw [List.any_eq_true]
  refine ⟨c, hc, ?_⟩
  have : c.label.isSome = true := Option.isSome_iff_ne_none.2 hne
  rcases hk with hk | hk <;> simp [hk, this]

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

private theorem MergeSpec.mem_of_solid (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hsol : c.kind.isSolid = true) (hr : Γ.mrep c.x ≠ Γ.mrep c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [mergeComp_solid hsol, ite_eq_right hr]⟩

private theorem MergeSpec.mem_of_dot (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hf : t.f c.x ≠ t.f c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [mergeComp_dot hk, ite_eq_right hf]⟩

/-- A `×`-dotted component of `t.g` is the image of a `×`-dotted component of `Γ`. -/
private theorem MergeSpec.of_mem_xdot (hs : MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind = .xdot) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .xdot := h ▸ hk
    refine ⟨c, hc, hck, ?_⟩
    rw [mergeComp_other (by rw [hck]; exact fun h => by cases h) (by simp [hck, Kind.isSolid])]
      at hm
    exact (Option.some.inj hm).symm
  · rw [hch'] at hk
    cases hk

/-- A solid component of `t.g` is the image of a solid component of `Γ` whose ends are in
different blocks. -/
private theorem MergeSpec.of_mem_solid (hs : MergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind.isSolid = true) :
    ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ Γ.mrep c.x ≠ Γ.mrep c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind.isSolid = true := by rw [← h]; exact hk
    rw [mergeComp_solid hck] at hm
    split_ifs at hm with hr
    · exfalso
      obtain rfl := Option.some.inj hm
      obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
        cases hkk : c.kind <;> simp_all [Kind.isSolid]
      simp [Kind.toWeight, hch, Kind.isSolid] at hk
    · exact ⟨c, hc, hck, hr, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    simp [Kind.isSolid] at hk

private theorem MergeSpec.dot_reach (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) :
    t.g.edgeGraphNoX.Reachable (t.f c.x) (t.f c.y) := by
  by_cases hf : t.f c.x = t.f c.y
  · rw [hf]
  · refine SimpleGraph.Adj.reachable ?_
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
    exact ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_dot hc hk hf, by simp [Comp.map, hk], rfl, rfl⟩⟩

private theorem MergeSpec.eqv_reach (hs : MergeSpec Γ t) {u v : Atom k n}
    (h : Relation.EqvGen (dotRel Γ.comps) u v) :
    t.g.edgeGraphNoX.Reachable (t.f u) (t.f v) := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact hs.dot_reach hc hk
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private theorem MergeSpec.noX_reach (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .xdot) :
    t.g.edgeGraphNoX.Reachable (t.f c.x) (t.f c.y) := by
  by_cases hd : c.kind = .dot
  · exact hs.dot_reach hc hd
  by_cases hsol : c.kind.isSolid = true
  · by_cases hr : Γ.mrep c.x = Γ.mrep c.y
    · have hconn : Relation.EqvGen (dotRel Γ.comps) c.x c.y :=
        (Γ.mrep_conn c.x).trans _ _ _ (hr ▸ (Γ.mrep_conn c.y).symm)
      exact hs.eqv_reach hconn
    · by_cases hf : t.f c.x = t.f c.y
      · rw [hf]
      refine SimpleGraph.Adj.reachable ?_
      rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
      refine ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_solid hc hsol hr, ?_, rfl, rfl⟩⟩
      simpa [Comp.map] using hk
  · have hsol' : c.kind.isSolid = false := by simpa using hsol
    by_cases hf : t.f c.x = t.f c.y
    · rw [hf]
    refine SimpleGraph.Adj.reachable ?_
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj]
    refine ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_other hc hd hsol', ?_, rfl, rfl⟩⟩
    simpa [Comp.map] using hk

private theorem MergeSpec.connNoX (hs : MergeSpec Γ t) (hconn : Γ.ConnNoX) : t.g.ConnNoX := by
  have hadj : ∀ u v, Γ.edgeGraphNoX.Adj u v →
      t.g.edgeGraphNoX.Reachable (t.f u) (t.f v) := by
    intro u v h
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at h
    obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := h
    · exact hs.noX_reach hc hk
    · exact (hs.noX_reach hc hk).symm
  intro u' v'
  obtain ⟨u, rfl⟩ := hs.f_surj u'
  obtain ⟨v, rfl⟩ := hs.f_surj v'
  have h := hconn u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ h2 ih => exact ih.trans (hadj _ _ h2)

private theorem MergeSpec.wt_reach (hs : MergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) :
    t.g.wavedThetaGraph.Reachable (t.f c.x) (t.f c.y) := by
  have hd : c.kind ≠ .dot := by
    rcases hk with ⟨-, h⟩ | h
    · exact h
    · intro hd
      rw [hd] at h
      simp [Kind.isDiffusive] at h
  have hsol : c.kind.isSolid = false := by
    rcases hk with ⟨h, -⟩ | h
    · cases hkk : c.kind <;> simp_all [Kind.joinsMol, Kind.isSolid]
    · cases hkk : c.kind <;> simp_all [Kind.isDiffusive, Kind.isSolid]
  by_cases hf : t.f c.x = t.f c.y
  · rw [hf]
  refine SimpleGraph.Adj.reachable ?_
  rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj]
  exact ⟨hf, Or.inl ⟨c.map t.f, hs.mem_of_other hc hd hsol, by simpa [Comp.map] using hk, rfl, rfl⟩⟩

private theorem MergeSpec.internal (hs : MergeSpec Γ t)
    (hint : ∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b)) :
    ∀ a b : Fin t.nOut, t.g.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b) := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hadj : ∀ u v, Γ.wavedThetaGraph.Adj u v →
      t.g.wavedThetaGraph.Reachable (t.f u) (t.f v) := by
    intro u v h
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at h
    obtain ⟨-, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ := h
    · exact hs.wt_reach hc hk
    · exact (hs.wt_reach hc hk).symm
  intro a b
  obtain ⟨i, rfl⟩ := hgs a
  obtain ⟨j, rfl⟩ := hgs b
  have key : ∀ y, Relation.ReflTransGen Γ.wavedThetaGraph.Adj (Sum.inr i) y →
      t.g.wavedThetaGraph.Reachable (t.f (.inr i)) (t.f y) := by
    intro y hy
    induction hy with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ h2 ih => exact ih.trans (hadj _ _ h2)
  have h := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (hint i j)
  have h2 := key _ h
  rwa [hg, hg] at h2

/-- Dotted edges of `t.g` have an external end. -/
private theorem MergeSpec.noIntDot (hs : MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind = .dot → c'.x.isLeft = true ∨ c'.y.isLeft = true := by
  intro c' hc' hk'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := h ▸ hk'
    rw [mergeComp_dot hck] at hm
    split_ifs at hm with hf
    obtain rfl := Option.some.inj hm
    by_contra hcon
    simp only [not_or, Bool.not_eq_true, Comp.map] at hcon
    obtain ⟨hx, hy⟩ := hcon
    apply hf
    have hx' : c.x.isRight = true := by
      rcases hcx : c.x with a | i
      · rw [hcx] at hx
        simp [hs.f_inl] at hx
      · rfl
    have hy' : c.y.isRight = true := by
      rcases hcy : c.y with a | i
      · rw [hcy] at hy
        simp [hs.f_inl] at hy
      · rfl
    exact hs.f_eq _ _ (Γ.mrep_dot hc hck) hx' hy'
  · rw [hch'] at hk'
    cases hk'

private theorem MergeSpec.solid_ne (hs : MergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → c'.x ≠ c'.y := by
  intro c' hc' hk'
  obtain ⟨c, hc, -, hr, rfl⟩ := hs.of_mem_solid hc' hk'
  exact hs.f_ne _ _ hr

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

private theorem xdot_split {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .xdot) (hne : c.x ≠ c.y) :
    xonlyB Γ.splitPairs c.x c.y = true ∨
      ∃ c₂ ∈ Γ.comps, c₂.kind.isSolid = true ∧ SamePair c c₂ := by
  obtain ⟨q, hq, hqc⟩ := rep_of hc (Or.inr hk) hne
  have hx : spJoined Γ (· == .xdot) q.1 q.2 = true := joined_of hc (by simp [hk]) hqc
  by_cases hs : spJoined Γ Kind.isSolid q.1 q.2 = true
  · right
    exact spJoined_samePair hqc hs
  · left
    have hs' : spJoined Γ Kind.isSolid q.1 q.2 = false := by simpa using hs
    have hp : (q.1, q.2, false) ∈ Γ.splitPairs :=
      mem_splitPairs.2 ⟨hq, by simp [hs', hx], hs'.symm⟩
    rw [xonlyB_iff]
    refine ⟨_, hp, rfl, ?_⟩
    exact hqc

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

private theorem foldl_spStep_length (l acc : List (Atom k n × Atom k n)) :
    (l.foldl spStep acc).length ≤ acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons p l ih =>
    refine (ih _).trans ?_
    unfold spStep
    split_ifs <;> (simp; try omega)

private theorem splitPairs_length (Γ : Graph k n) : Γ.splitPairs.length ≤ Γ.comps.length := by
  rw [splitPairs_eq]
  refine (List.length_filterMap_le _ _).trans ?_
  unfold spUniq
  refine (foldl_spStep_length _ _).trans ?_
  simp only [List.length_nil, zero_add]
  exact List.length_filterMap_le _ _

private theorem dotChoice_length (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool)) :
    (Γ.dotChoice SP A).comps.length ≤ Γ.comps.length + SP.length := by
  rw [dotChoice_eq]
  change (keptComps Γ SP ++ addedComps SP A).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (List.length_filter_le _ _) (List.length_filterMap_le _ _)

private theorem mem_dotChoice_of_ne_xdot (Γ : Graph k n) (SP A : List (Atom k n × Atom k n × Bool))
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hk : c.kind ≠ .xdot) :
    c ∈ (Γ.dotChoice SP A).comps := by
  rw [dotChoice_eq]
  exact List.mem_append_left _ ((mem_keptComps Γ SP c).2 ⟨hc, fun h => hk h.1⟩)

end SplitFacts

/-! ## `O_dot` on normal regular graphs -/

section NormalAssembly

variable {k n : ℕ}

private theorem identity_normal {Γ : Graph k n} {C : ℕ} (hreg : Γ.Regular C)
    (hconn : Γ.ConnNoX) (hsp : Γ.splitPairs = [])
    (hnosl : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) :
    Γ.Normal (2 * C) ∧ Γ.ConnNoX := by
  refine ⟨⟨⟨by have := hreg.size; omega, hreg.connected, hreg.internal, hreg.noIntDot⟩,
    hnosl, ?_⟩, hconn⟩
  intro u v huv
  constructor
  · rintro ⟨c, hc, hk, hm⟩
    have hne : c.x ≠ c.y := by
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact huv
      · rw [h1, h2]; exact huv.symm
    rcases xdot_split hc hk hne with h | ⟨c₂, hc₂, hk₂, hsp₂⟩
    · rw [hsp] at h
      simp [xonlyB] at h
    · refine ⟨c₂, hc₂, hk₂, ?_⟩
      unfold SamePair at hsp₂
      rcases hsp₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  · rintro ⟨c, hc, hk, hm⟩
    have hne : c.x ≠ c.y := by
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact huv
      · rw [h1, h2]; exact huv.symm
    rcases solid_split hc hk hne with ⟨c₃, hc₃, hk₃, hsp₃, -⟩ | ⟨p, hp, -⟩
    · refine ⟨c₃, hc₃, hk₃, ?_⟩
      unfold SamePair at hsp₃
      rcases hsp₃ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    · rw [hsp] at hp
      simp at hp

private theorem mergeT_dotChoice_normal {Γ : Graph k n} {C : ℕ} (hreg : Γ.Regular C)
    (hconn : Γ.ConnNoX) (A : List (Atom k n × Atom k n × Bool)) {t : Tracked k n}
    (hm : (Γ.dotChoice Γ.splitPairs A).mergeT = some t) :
    t.g.Normal (2 * C) ∧ t.g.ConnNoX := by
  set SP := Γ.splitPairs with hSP
  set Γ₁ := Γ.dotChoice SP A with hΓ₁
  have hs : MergeSpec Γ₁ t := mergeT_spec hm
  have hconn₁ : Γ₁.ConnNoX := by
    intro u v
    refine (hconn u v).mono ?_
    intro a b hab
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hab ⊢
    obtain ⟨hne, h⟩ := hab
    refine ⟨hne, ?_⟩
    rcases h with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
    · exact Or.inl ⟨c, mem_dotChoice_of_ne_xdot Γ SP A hc hk, hk, h1, h2⟩
    · exact Or.inr ⟨c, mem_dotChoice_of_ne_xdot Γ SP A hc hk, hk, h1, h2⟩
  have hint₁ : ∀ a b : Fin n, Γ₁.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b) := by
    intro a b
    refine (hreg.internal a b).mono ?_
    intro x y hxy
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hxy ⊢
    obtain ⟨hne, h⟩ := hxy
    refine ⟨hne, ?_⟩
    have hkx : ∀ c : Comp (Atom k n),
        (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) → c.kind ≠ .xdot := by
      intro c hk hx
      rcases hk with ⟨h1, -⟩ | h1 <;> simp [hx, Kind.joinsMol, Kind.isDiffusive] at h1
    rcases h with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
    · exact Or.inl ⟨c, mem_dotChoice_of_ne_xdot Γ SP A hc (hkx c hk), hk, h1, h2⟩
    · exact Or.inr ⟨c, mem_dotChoice_of_ne_xdot Γ SP A hc (hkx c hk), hk, h1, h2⟩
  have hconnt : t.g.ConnNoX := hs.connNoX hconn₁
  refine ⟨⟨⟨?_, ?_, hs.internal hint₁, hs.noIntDot⟩, hs.solid_ne, ?_⟩, hconnt⟩
  · -- size
    have h1 : t.g.comps.length ≤ Γ₁.comps.length := by
      rw [hs.comps_eq]
      exact List.length_filterMap_le _ _
    have h2 : Γ₁.comps.length ≤ Γ.comps.length + SP.length := dotChoice_length Γ SP A
    have h3 : SP.length ≤ Γ.comps.length := splitPairs_length Γ
    have h4 := hs.nOut_le
    have h5 := hreg.size
    omega
  · intro u v
    exact (hconnt u v).mono (by
      intro a b hab
      rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hab
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
      obtain ⟨hne, h⟩ := hab
      refine ⟨hne, ?_⟩
      rcases h with ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩
      · exact Or.inl ⟨c, hc, h1, h2⟩
      · exact Or.inr ⟨c, hc, h1, h2⟩)
  · -- the `×`-dotted edges are the solid edges
    intro u v _
    constructor
    · rintro ⟨c', hc', hk', hm'⟩
      obtain ⟨c, hc, hk, rfl⟩ := hs.of_mem_xdot hc' hk'
      have hr : Γ₁.mrep c.x ≠ Γ₁.mrep c.y := hs.xdot_ne c hc hk
      have hne : c.x ≠ c.y := fun h => hr (by rw [h])
      have key : ∃ c₂ ∈ Γ.comps, c₂.kind.isSolid = true ∧ SamePair c c₂ := by
        have hc2 : c ∈ keptComps Γ SP ++ addedComps SP A := hc
        rcases List.mem_append.1 hc2 with hc2 | hc2
        · obtain ⟨hcΓ, hnot⟩ := (mem_keptComps Γ SP c).1 hc2
          rcases xdot_split hcΓ hk hne with h | h
          · exact absurd ⟨hk, h⟩ hnot
          · exact h
        · obtain ⟨p, hp, ⟨-, hpc⟩ | ⟨-, hpf, hpc⟩⟩ := mem_addedComps.1 hc2
          · rw [hpc] at hk
            simp [mkC] at hk
          · obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := sp_true hp hpf
            refine ⟨c₂, hc₂, hk₂, ?_⟩
            unfold SamePair
            rw [hpc]
            simp only [mkC]
            rcases hm₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2⟩
      obtain ⟨c₂, hc₂, hk₂, hsp⟩ := key
      have hc₂' : c₂ ∈ Γ₁.comps := mem_dotChoice_of_ne_xdot Γ SP A hc₂ (by
        intro h
        rw [h] at hk₂
        simp [Kind.isSolid] at hk₂)
      have hr₂ : Γ₁.mrep c₂.x ≠ Γ₁.mrep c₂.y := by
        unfold SamePair at hsp
        rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hr
        · rw [h1, h2]; exact fun h => hr h.symm
      refine ⟨c₂.map t.f, hs.mem_of_solid hc₂' hk₂ hr₂, by simpa [Comp.map] using hk₂, ?_⟩
      simp only [Comp.map] at hm' ⊢
      unfold SamePair at hsp
      rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
    · rintro ⟨c', hc', hk', hm'⟩
      obtain ⟨c, hc, hsol, hr, rfl⟩ := hs.of_mem_solid hc' hk'
      have hcΓ : c ∈ Γ.comps := by
        have hc2 : c ∈ keptComps Γ SP ++ addedComps SP A := hc
        rcases List.mem_append.1 hc2 with hc2 | hc2
        · exact ((mem_keptComps Γ SP c).1 hc2).1
        · exfalso
          rcases (addedComps_label hc2).2 with h | h <;> simp [h, Kind.isSolid] at hsol
      have hne : c.x ≠ c.y := fun h => hr (by rw [h])
      rcases solid_split hcΓ hsol hne with ⟨c₃, hc₃, hk₃, hsp, hx⟩ | ⟨p, hp, hpf, hpm⟩
      · have hc₃' : c₃ ∈ Γ₁.comps := by
          change c₃ ∈ keptComps Γ SP ++ addedComps SP A
          refine List.mem_append_left _ ((mem_keptComps Γ SP c₃).2 ⟨hc₃, ?_⟩)
          rintro ⟨-, h⟩
          rw [hx] at h
          exact Bool.false_ne_true h
        refine ⟨c₃.map t.f, hs.mem_of_other hc₃' (by rw [hk₃]; exact fun h => by cases h)
          (by simp [hk₃, Kind.isSolid]), by simpa [Comp.map] using hk₃, ?_⟩
        simp only [Comp.map] at hm' ⊢
        unfold SamePair at hsp
        rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
      · by_cases hpA : p ∈ A
        · exfalso
          have hmem : mkC .dot p.1 p.2.1 ∈ Γ₁.comps := by
            change _ ∈ keptComps Γ SP ++ addedComps SP A
            exact List.mem_append_right _ (mem_addedComps.2 ⟨p, hp, Or.inl ⟨hpA, rfl⟩⟩)
          have := Γ₁.mrep_dot hmem rfl
          simp only [mkC] at this
          rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2] at this
            exact hr this
          · rw [h1, h2] at this
            exact hr this.symm
        · have hmem : mkC .xdot p.1 p.2.1 ∈ Γ₁.comps := by
            change _ ∈ keptComps Γ SP ++ addedComps SP A
            exact List.mem_append_right _ (mem_addedComps.2 ⟨p, hp, Or.inr ⟨hpA, hpf, rfl⟩⟩)
          refine ⟨(mkC .xdot p.1 p.2.1).map t.f,
            hs.mem_of_other hmem (by simp [mkC]) (by simp [mkC, Kind.isSolid]),
            by simp [mkC, Comp.map], ?_⟩
          simp only [Comp.map, mkC] at hm' ⊢
          rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

end NormalAssembly

/-- Value of `O_merge` ([I, Def 3.1] = [II, Def 4.1]): for a graph with at most one distinct
`P`/`Q` label and no labelled dotted or `×`-dotted edge, the graph returned by `mergeT` has the
value of the graph, and the value of the graph is `0` when `mergeT` is `none`. -/
theorem oMerge_value (k n : ℕ) (Γ : Graph k n) :
    Γ.labels.length ≤ 1 →
    (∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none) →
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι),
      match Γ.mergeT with
      | some t => t.g.valR PF D e = Γ.valR PF D e
      | none => Γ.valR PF D e = 0 := by
  intro hl hlab Ω ι _ _ PF D e
  have hzero : ∀ (s : Fin n → ι) (ω : Ω),
      ¬ (∀ c ∈ Γ.comps, c.kind = .dot → Sum.elim e s c.x = Sum.elim e s c.y) →
        Γ.termR PF D (Sum.elim e s) ω = 0 := by
    intro s ω hz
    push Not at hz
    obtain ⟨c, hc, hk, hne⟩ := hz
    exact termR_eq_zero_of_val PF D _ ω hc (hlab c hc (Or.inl hk)) (by simp [Comp.val, hk, hne])
  rcases hm : Γ.mergeT with _ | t
  · obtain ⟨c, hc, hk, hr⟩ := mergeT_none hm
    change Γ.valR PF D e = 0
    funext ω
    simp only [Graph.valR, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hz : ∀ c ∈ Γ.comps, c.kind = .dot → Sum.elim e s c.x = Sum.elim e s c.y
    · apply termR_eq_zero_of_val PF D _ ω hc (hlab c hc (Or.inr hk))
      have h1 := Γ.sigma_rep _ hz c.x
      have h2 := Γ.sigma_rep _ hz c.y
      have : Sum.elim e s c.x = Sum.elim e s c.y := by rw [← h1, ← h2, hr]
      simp [Comp.val, hk, this]
    · exact hzero s ω hz
  · change t.g.valR PF D e = Γ.valR PF D e
    have hs := mergeT_spec hm
    obtain ⟨g, hg, hgs⟩ := hs.f_inr
    funext ω
    simp only [Graph.valR]
    have hσ : ∀ s' : Fin t.nOut → ι, Sum.elim e (s' ∘ g) = Sum.elim e s' ∘ t.f := by
      intro s'
      funext u
      rcases u with a | i
      · simp [hs.f_inl a]
      · simp [hg i]
    refine Fintype.sum_of_injective (fun s' : Fin t.nOut → ι => s' ∘ g) ?_ _ _ ?_ ?_
    · intro s₁ s₂ h12
      funext j
      obtain ⟨i, rfl⟩ := hgs j
      exact congrFun h12 i
    · intro s hs'
      by_cases hz : ∀ c ∈ Γ.comps, c.kind = .dot → Sum.elim e s c.x = Sum.elim e s c.y
      · exfalso
        apply hs'
        have hfac : ∀ i i' : Fin n, g i = g i' → s i = s i' := by
          intro i i' hii
          have hf : t.f (.inr i) = t.f (.inr i') := by rw [hg, hg, hii]
          have hr : Γ.mrep (.inr i) = Γ.mrep (.inr i') := by
            by_contra hne
            exact hs.f_ne _ _ hne hf
          have h1 := Γ.sigma_rep _ hz (.inr i)
          have h2 := Γ.sigma_rep _ hz (.inr i')
          simpa [hr] using (h1.symm.trans (by rw [hr]; exact h2) : _)
        refine ⟨fun j => s (Classical.choose (hgs j)), ?_⟩
        funext i
        simp only [Function.comp_apply]
        exact hfac _ _ (Classical.choose_spec (hgs (g i)))
      · exact hzero s ω hz
    · intro s'
      by_cases hz : ∀ c ∈ Γ.comps, c.kind = .dot → Sum.elim e s' (t.f c.x) = Sum.elim e s' (t.f c.y)
      · rw [hσ s']
        exact hs.termR_eq hl hlab PF D _ ω hz
      · have hz' : ¬ ∀ c ∈ Γ.comps, c.kind = .dot →
            Sum.elim e (s' ∘ g) c.x = Sum.elim e (s' ∘ g) c.y := by
          rwa [hσ s']
        rw [hzero _ ω hz']
        push Not at hz
        obtain ⟨c, hc, hk, hne⟩ := hz
        have hnd : ¬ (c.kind = .dot ∧ t.f c.x = t.f c.y) := fun ⟨_, h⟩ => hne (by rw [h])
        obtain ⟨c', hc'⟩ := mergeComp_isSome Γ.mrep t.f hnd
        have hmem : c' ∈ t.g.comps := by
          rw [hs.comps_eq]
          exact List.mem_filterMap.2 ⟨c, hc, hc'⟩
        have hc'eq : c' = c.map t.f := by
          have := mergeComp_of_not_solid (rep := Γ.mrep) (f := t.f) (c := c)
            (by simp [hk, Kind.isSolid]) hnd
          rw [this] at hc'
          exact (Option.some.inj hc').symm
        refine termR_eq_zero_of_val PF D _ ω hmem ?_ ?_
        · rw [mergeComp_label hc', hlab c hc (Or.inl hk)]
          rfl
        · simp [Comp.val, hc'eq, Comp.map, hk, hne]

/-- `O_dot` preserves the value of every graph ([I, Def 3.2] = [II, Def 4.2]), for every data
record and every family of conditional expectations. -/
theorem oDot_value (k n : ℕ) :
    PreservesValue (oDot (k := k) (n := n)) anyAdm := by
  intro Ω ι _ _ PF D _ Γ e
  funext ω
  have hid : ∀ E : TExpansion k n, E = [Tracked.self Γ] →
      (E.forget).valR PF D e ω = Γ.valR PF D e ω := by
    rintro E rfl
    simp [TExpansion.forget, Expansion.valR, Tracked.self]
  unfold oDot
  by_cases hb1 : (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true)
  · exact hid _ (oDotT_branch1 hb1)
  by_cases hb2 : (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true
  · exact hid _ (oDotT_branch2 hb1 hb2)
  rw [oDotT_branch3 hb1 hb2]
  obtain ⟨hl, hlab⟩ := not_branch1 hb1
  set SP := Γ.splitPairs with hSP
  have hmerge : ∀ A : List (Atom k n × Atom k n × Bool),
      ((Γ.dotChoice SP A).mergeT.elim 0 fun t => t.g.valR PF D e ω) =
        (Γ.dotChoice SP A).valR PF D e ω := by
    intro A
    have h := oMerge_value k n (Γ.dotChoice SP A) (dotChoice_labels_length Γ SP A hlab hl)
      (dotChoice_hlab Γ SP A hlab) Ω ι PF D e
    cases hm : (Γ.dotChoice SP A).mergeT with
    | none =>
      rw [hm] at h
      simp only at h
      rw [h]
      rfl
    | some t =>
      rw [hm] at h
      exact congrFun h ω
  change (((SP.sublists.filterMap fun A => (Γ.dotChoice SP A).mergeT).map
      fun t => (⟨t.nOut, t.g⟩ : Σ n : ℕ, Graph k n)).map
        (fun g => g.2.valR PF D e ω)).sum = Γ.valR PF D e ω
  rw [List.map_map, sum_filterMap_map]
  refine Eq.trans (congrArg List.sum (List.map_congr_left fun A _ => hmerge A)) ?_
  simp only [Graph.valR]
  rw [list_sum_map_finset_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact dotChoice_sum Γ hlab PF D (Sum.elim e s) ω

/-- [I, Lemma 3.3] for regular inputs: if `Γ` is regular with bound `C`, connected without
`×`-dotted edges, has at most one distinct `P`/`Q` label and no labelled dotted or `×`-dotted
edge, then every graph of `O_dot` of `Γ` is normal regular with bound `2 C` and connected without
`×`-dotted edges. -/
theorem oDot_normal (k n C : ℕ) (Γ : Graph k n) :
    Γ.Regular C → Γ.ConnNoX → Γ.labels.length ≤ 1 →
    (∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none) →
    ∀ t ∈ oDotT Γ, t.g.Normal (2 * C) ∧ t.g.ConnNoX := by
  intro hreg hconn hl hlab t ht
  have hb1 : ¬ (2 ≤ Γ.labels.length ∨
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) = true) := by
    rintro (h | h)
    · omega
    · rw [List.any_eq_true] at h
      obtain ⟨c, hc, hb⟩ := h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
      rw [hlab c hc hb.1] at hb
      simp at hb
  by_cases hb2 : (Γ.splitPairs.isEmpty && !(Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))) = true
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hb2
    have hnosl : ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y := by
      intro c hc hsol hxy
      have := List.any_eq_false.1 hb2.2 c hc
      simp [hsol, hxy] at this
    have hid := identity_normal hreg hconn hb2.1 hnosl
    rw [oDotT_branch2 hb1 (by simpa using hb2), List.mem_singleton] at ht
    subst ht
    exact hid
  · rw [oDotT_branch3 hb1 hb2, List.mem_filterMap] at ht
    obtain ⟨A, -, hm⟩ := ht
    exact mergeT_dotChoice_normal hreg hconn A hm

section Instances

end Instances

end RBM8D.Graphs
