import RBM8D.Graph.Local.IBP
import RBM8D.Graph.QExp.Defs

/-!
# The `P`-graph step of the `Q`-expansions

[II, Lemma 4.13], with [II, (4.23), (4.24)].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Kinds -/

section KindFacts

theorem Kind.isRandom_of_isSolid {κ : Kind} (h : κ.isSolid = true) : κ.isRandom = true := by
  cases κ <;> simp_all [Kind.isSolid, Kind.isRandom]

theorem Kind.ne_dot_of_isRandom {κ : Kind} (h : κ.isRandom = true) : κ ≠ .dot := by
  rintro rfl; simp [Kind.isRandom] at h

theorem Kind.ne_xdot_of_isRandom {κ : Kind} (h : κ.isRandom = true) : κ ≠ .xdot := by
  rintro rfl; simp [Kind.isRandom] at h

theorem Kind.isSolid_iff {κ : Kind} : κ.isSolid = true ↔ ∃ ch, κ = .G ch := by
  cases κ <;> simp [Kind.isSolid]

theorem Kind.not_joinsMol_of_isRandom {κ : Kind} (h : κ.isRandom = true) :
    κ.joinsMol = false := by
  cases κ <;> simp_all [Kind.isRandom, Kind.joinsMol]

theorem Kind.not_isDiffusive_of_isRandom {κ : Kind} (h : κ.isRandom = true) :
    κ.isDiffusive = false := by
  cases κ <;> simp_all [Kind.isRandom, Kind.isDiffusive]

end KindFacts

/-! ## Graphs with the same components -/

section SameComps

variable {k n : ℕ}

theorem Graph.ord_perm {g g' : Graph k n} (h : g.comps.Perm g'.comps) :
    g.ord = g'.ord := by
  unfold Graph.ord
  rw [(h.map _).sum_eq]

end SameComps

/-! ## Dot blocks -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
def dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
theorem dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    dotRel cs ≤ dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

omit [DecidableEq V] in
theorem flatten_map_singleton' (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
def blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

theorem dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, blockStep]

theorem dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

theorem dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [dotBlocks_nil, flatten_map_singleton']
  | append_singleton cs c ih =>
    rw [dotBlocks_snoc, blockStep]
    split_ifs
    · exact (joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

theorem dotBlocks_conn (as : List V) (cs : List (Comp V)) :
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

theorem dotBlocks_joined (as : List V) (cs : List (Comp V))
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
theorem blockRep_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B : List V}
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

theorem blockRep_spec (P : List (List V)) (u : V) :
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

theorem mem_allAtoms (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

theorem allAtoms_nodup : (allAtoms k n).Nodup := by
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
def Graph.psteps_mrep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

theorem Graph.mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : Γ.psteps_mrep c.x = Γ.psteps_mrep c.y := by
  obtain ⟨B, hB, hx, hy⟩ := dotBlocks_joined (allAtoms k n) Γ.comps
    (fun c _ => ⟨mem_allAtoms _, mem_allAtoms _⟩) c hc hk
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (dotBlocks_flatten_perm _ _).nodup_iff.2 allAtoms_nodup
  exact blockRep_eq_of_mem hnd hB hx hy

theorem Graph.mrep_conn (Γ : Graph k n) (u : Atom k n) :
    Relation.EqvGen (dotRel Γ.comps) u (Γ.psteps_mrep u) := by
  rcases blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : Γ.psteps_mrep u = u := h
    rw [this]
    exact Relation.EqvGen.refl _
  · exact dotBlocks_conn _ _ B hB u hu _ hr

theorem eqvGen_dotRel_eq {V ι : Type*} {cs : List (Comp V)} (σ : V → ι)
    (hz : ∀ c ∈ cs, c.kind = .dot → σ c.x = σ c.y) {u v : V}
    (h : Relation.EqvGen (dotRel cs) u v) : σ u = σ v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    exact hz c hc hk
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- The roots: the representatives of the internal atoms, without repetition. -/
def Graph.mroots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => Γ.psteps_mrep (Sum.inr i)).dedup

theorem Graph.mem_mroots (Γ : Graph k n) (i : Fin n) : Γ.psteps_mrep (.inr i) ∈ Γ.mroots :=
  List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- The new internal atom of an internal atom: the position of its root. -/
def Graph.midx (Γ : Graph k n) (i : Fin n) : Fin Γ.mroots.length :=
  ⟨Γ.mroots.idxOf (Γ.psteps_mrep (.inr i)), List.idxOf_lt_length_of_mem (Γ.mem_mroots i)⟩

/-- The atom map of `O_merge`. -/
def Graph.mmap (Γ : Graph k n) : Atom k n → Atom k Γ.mroots.length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr (Γ.midx i)

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
def psteps_mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

theorem mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && Γ.psteps_mrep c.x == Γ.psteps_mrep c.y) then none else
    some ⟨Γ.mroots.length, ⟨Γ.comps.filterMap (psteps_mergeComp Γ.psteps_mrep Γ.mmap), Γ.coeff⟩, Γ.mmap⟩ := rfl

/-- The structure of a tracked graph `t` with `Γ.mergeT = some t`: its components, its atom map
and its blocks. -/
structure PStepsMergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (psteps_mergeComp Γ.psteps_mrep t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, Γ.psteps_mrep u = Γ.psteps_mrep v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, Γ.psteps_mrep u ≠ Γ.psteps_mrep v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → Γ.psteps_mrep c.x ≠ Γ.psteps_mrep c.y

theorem psteps_mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
    PStepsMergeSpec Γ t := by
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
      change Γ.mroots.idxOf (Γ.psteps_mrep (.inr i)) = Γ.mroots.idxOf (Γ.psteps_mrep (.inr j))
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


/-! ## Blocks as classes of an equivalence -/

section BlockEqv

variable {k n : ℕ}

theorem reachable_fromRel_iff {V : Type*} (r : V → V → Prop) (u v : V) :
    (SimpleGraph.fromRel r).Reachable u v ↔ Relation.EqvGen r u v := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Relation.EqvGen.refl _
    | cons hadj _ ih =>
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact (Relation.EqvGen.rel _ _ h).trans _ _ _ ih
      · exact (Relation.EqvGen.rel _ _ h).symm.trans _ _ _ ih
  · intro h
    induction h with
    | rel a b hab =>
      by_cases hne : a = b
      · rw [hne]
      · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hab⟩).reachable
    | refl a => exact SimpleGraph.Reachable.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem Graph.sameBlock_iff_eqvGen (g : Graph k n) (u v : Atom k n) :
    g.SameBlock u v ↔ Relation.EqvGen (dotRel g.comps) u v := by
  unfold Graph.SameBlock Graph.dotGraph
  rw [reachable_fromRel_iff]
  rfl

theorem eqvGen_of_mrep_eq (g : Graph k n) {u v : Atom k n} (h : g.psteps_mrep u = g.psteps_mrep v) :
    Relation.EqvGen (dotRel g.comps) u v :=
  (g.mrep_conn u).trans _ _ _ (by rw [h]; exact (g.mrep_conn v).symm)

theorem mrep_eq_of_eqvGen (g : Graph k n) {u v : Atom k n}
    (h : Relation.EqvGen (dotRel g.comps) u v) : g.psteps_mrep u = g.psteps_mrep v := by
  induction h with
  | rel a b hab =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hab
    exact g.mrep_dot hc hk
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem Graph.sameBlock_iff_mrep (g : Graph k n) (u v : Atom k n) :
    g.SameBlock u v ↔ g.psteps_mrep u = g.psteps_mrep v := by
  rw [Graph.sameBlock_iff_eqvGen]
  exact ⟨mrep_eq_of_eqvGen g, eqvGen_of_mrep_eq g⟩

theorem Graph.sameBlock_refl (g : Graph k n) (u : Atom k n) : g.SameBlock u u :=
  SimpleGraph.Reachable.refl _

theorem Graph.sameBlock_symm {g : Graph k n} {u v : Atom k n} (h : g.SameBlock u v) :
    g.SameBlock v u :=
  SimpleGraph.Reachable.symm h

theorem Graph.sameBlock_trans {g : Graph k n} {u v w : Atom k n} (h : g.SameBlock u v)
    (h' : g.SameBlock v w) : g.SameBlock u w :=
  SimpleGraph.Reachable.trans h h'

theorem Graph.sameBlock_of_dot {g : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ g.comps)
    (hk : c.kind = .dot) : g.SameBlock c.x c.y := by
  rw [Graph.sameBlock_iff_eqvGen]
  exact Relation.EqvGen.rel _ _ ⟨c, hc, hk, rfl, rfl⟩

theorem Graph.sameBlock_mono {g g' : Graph k n}
    (h : ∀ c ∈ g.comps, c.kind = .dot → c ∈ g'.comps) {u v : Atom k n} (huv : g.SameBlock u v) :
    g'.SameBlock u v := by
  rw [Graph.sameBlock_iff_eqvGen] at huv ⊢
  refine Relation.EqvGen.mono ?_ _ _ huv
  rintro a b ⟨c, hc, hk, rfl, rfl⟩
  exact ⟨c, h c hc hk, hk, rfl, rfl⟩

/-- A labelling that agrees on the ends of every dotted edge agrees on the atoms of one block. -/
theorem Graph.sigma_eq_of_sameBlock {ι : Type*} {g : Graph k n} (σ : Atom k n → ι)
    (hz : ∀ c ∈ g.comps, c.kind = .dot → σ c.x = σ c.y) {u v : Atom k n} (h : g.SameBlock u v) :
    σ u = σ v := by
  rw [Graph.sameBlock_iff_eqvGen] at h
  exact eqvGen_dotRel_eq σ hz h

end BlockEqv

/-! ## Counting classes of an equivalence -/

section QuotCount

variable {V W : Type*}

theorem quot_eqvGen_sound {r : V → V → Prop} {a b : V} (h : Relation.EqvGen r a b) :
    (Quot.mk (Relation.EqvGen r) a) = Quot.mk _ b :=
  Quot.sound h

theorem eqvGen_idem {r : V → V → Prop} {a b : V}
    (h : Relation.EqvGen (Relation.EqvGen r) a b) : Relation.EqvGen r a b := by
  induction h with
  | rel x y hxy => exact hxy
  | refl x => exact Relation.EqvGen.refl x
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

theorem eqvGen_false {a b : V} (h : Relation.EqvGen (fun (_ _ : V) => False) a b) :
    a = b := by
  induction h with
  | rel x y hxy => exact hxy.elim
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem quot_eqvGen_exact {r : V → V → Prop} {a b : V}
    (h : (Quot.mk (Relation.EqvGen r) a) = Quot.mk _ b) : Relation.EqvGen r a b :=
  eqvGen_idem (Quot.eqvGen_exact h)

/-- Equal equivalence closures give the same number of classes. -/
theorem card_quot_congr {r r' : V → V → Prop}
    (h : ∀ a b, Relation.EqvGen r a b ↔ Relation.EqvGen r' a b) :
    Nat.card (Quot (Relation.EqvGen r)) = Nat.card (Quot (Relation.EqvGen r')) := by
  have : Relation.EqvGen r = Relation.EqvGen r' := by
    funext a b
    exact propext (h a b)
  rw [this]

/-- A surjective map that identifies exactly the related pairs gives the same number of
classes. -/
theorem card_quot_map {r : V → V → Prop} {s : W → W → Prop} (f : V → W)
    (hf : Function.Surjective f)
    (h : ∀ a b, Relation.EqvGen r a b ↔ Relation.EqvGen s (f a) (f b)) :
    Nat.card (Quot (Relation.EqvGen r)) = Nat.card (Quot (Relation.EqvGen s)) := by
  let φ : Quot (Relation.EqvGen r) → Quot (Relation.EqvGen s) :=
    Quot.lift (fun a => Quot.mk _ (f a)) (fun a b hab => quot_eqvGen_sound ((h a b).1 hab))
  have hφ : Function.Bijective φ := by
    constructor
    · intro p q hpq
      induction p using Quot.ind with
      | mk a =>
        induction q using Quot.ind with
        | mk b => exact quot_eqvGen_sound ((h a b).2 (quot_eqvGen_exact hpq))
    · intro q
      induction q using Quot.ind with
      | mk w =>
        obtain ⟨a, rfl⟩ := hf w
        exact ⟨Quot.mk _ a, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective φ hφ)

/-- The equivalence classes of the empty relation are the points. -/
theorem card_quot_bot (r : V → V → Prop) (h : ∀ a b, ¬ r a b) :
    Nat.card (Quot (Relation.EqvGen r)) = Nat.card V := by
  have heq : ∀ a b, Relation.EqvGen r a b ↔ a = b := by
    intro a b
    constructor
    · intro hab
      induction hab with
      | rel x y hxy => exact absurd hxy (h x y)
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    · rintro rfl
      exact Relation.EqvGen.refl a
  refine (card_quot_map (s := fun (_ _ : V) => False) id Function.surjective_id ?_).trans ?_
  · intro a b
    rw [heq]
    constructor
    · rintro rfl; exact Relation.EqvGen.refl a
    · exact eqvGen_false
  · let e : Quot (Relation.EqvGen fun (_ _ : V) => False) ≃ V :=
      { toFun := Quot.lift id (fun a b hab => eqvGen_false hab)
        invFun := Quot.mk _
        left_inv := fun q => by induction q using Quot.ind; rfl
        right_inv := fun a => rfl }
    exact Nat.card_congr e

/-- The reachability of a relation with one more related pair. -/
theorem eqvGen_add_iff {r r' : V → V → Prop} {u v : V}
    (hr' : ∀ a b, r' a b ↔ r a b ∨ (a = u ∧ b = v)) (a b : V) :
    Relation.EqvGen r' a b ↔ Relation.EqvGen r a b ∨
      (Relation.EqvGen r a u ∧ Relation.EqvGen r v b) ∨
      (Relation.EqvGen r a v ∧ Relation.EqvGen r u b) := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
      rcases (hr' x y).1 hxy with h | ⟨rfl, rfl⟩
      · exact Or.inl (Relation.EqvGen.rel _ _ h)
      · exact Or.inr (Or.inl ⟨Relation.EqvGen.refl _, Relation.EqvGen.refl _⟩)
    | refl x => exact Or.inl (Relation.EqvGen.refl _)
    | symm x y _ ih =>
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
      · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
    | trans x y z _ _ ih1 ih2 =>
      rcases ih1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ih2 with h' | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact Or.inl (h.trans _ _ _ h')
      · exact Or.inr (Or.inl ⟨h.trans _ _ _ h1', h2'⟩)
      · exact Or.inr (Or.inr ⟨h.trans _ _ _ h1', h2'⟩)
      · exact Or.inr (Or.inl ⟨h1, h2.trans _ _ _ h'⟩)
      · exact Or.inr (Or.inl ⟨h1, h2'⟩)
      · exact Or.inl (h1.trans _ _ _ h2')
      · exact Or.inr (Or.inr ⟨h1, h2.trans _ _ _ h'⟩)
      · exact Or.inl (h1.trans _ _ _ h2')
      · exact Or.inr (Or.inr ⟨h1, h2'⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Relation.EqvGen.mono (fun x y hxy => (hr' x y).2 (Or.inl hxy)) _ _ h
    · have huv : Relation.EqvGen r' u v := Relation.EqvGen.rel _ _ ((hr' u v).2 (Or.inr ⟨rfl, rfl⟩))
      exact ((Relation.EqvGen.mono (fun x y hxy => (hr' x y).2 (Or.inl hxy)) _ _ h1).trans _ _ _
        huv).trans _ _ _ (Relation.EqvGen.mono (fun x y hxy => (hr' x y).2 (Or.inl hxy)) _ _ h2)
    · have huv : Relation.EqvGen r' u v := Relation.EqvGen.rel _ _ ((hr' u v).2 (Or.inr ⟨rfl, rfl⟩))
      exact ((Relation.EqvGen.mono (fun x y hxy => (hr' x y).2 (Or.inl hxy)) _ _ h1).trans _ _ _
        huv.symm).trans _ _ _ (Relation.EqvGen.mono (fun x y hxy => (hr' x y).2 (Or.inl hxy)) _ _ h2)

/-- One more related pair between two classes merges them: one class less. -/
theorem card_quot_add [Finite V] {r r' : V → V → Prop} {u v : V}
    (hr' : ∀ a b, r' a b ↔ r a b ∨ (a = u ∧ b = v)) (huv : ¬ Relation.EqvGen r u v) :
    Nat.card (Quot (Relation.EqvGen r)) = Nat.card (Quot (Relation.EqvGen r')) + 1 := by
  classical
  have hmono : ∀ a b, Relation.EqvGen r a b → Relation.EqvGen r' a b :=
    fun a b h => Relation.EqvGen.mono (fun x y hxy => (hr' x y).2 (Or.inl hxy)) _ _ h
  let φ : Quot (Relation.EqvGen r) → Quot (Relation.EqvGen r') :=
    Quot.lift (fun a => Quot.mk _ a) (fun a b hab => quot_eqvGen_sound (hmono a b hab))
  let qv : Quot (Relation.EqvGen r) := Quot.mk _ v
  let ψ : Quot (Relation.EqvGen r) → Option (Quot (Relation.EqvGen r')) :=
    fun q => if q = qv then none else some (φ q)
  have hψ : Function.Bijective ψ := by
    constructor
    · intro p q hpq
      by_cases hp : p = qv <;> by_cases hq : q = qv
      · rw [hp, hq]
      · simp only [ψ, hp, hq, ite_true, ite_false] at hpq; cases hpq
      · simp only [ψ, hp, hq, ite_true, ite_false] at hpq; cases hpq
      · simp only [ψ, hp, hq, ite_false, Option.some.injEq] at hpq
        induction p using Quot.ind with
        | mk a =>
          induction q using Quot.ind with
          | mk b =>
            have hab := quot_eqvGen_exact hpq
            rcases (eqvGen_add_iff hr' a b).1 hab with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact quot_eqvGen_sound h
            · exact absurd (quot_eqvGen_sound h2.symm) hq
            · exact absurd (quot_eqvGen_sound h1) hp
    · intro o
      rcases o with _ | q
      · exact ⟨qv, by simp [ψ]⟩
      · induction q using Quot.ind with
        | mk a =>
          by_cases ha : (Quot.mk (Relation.EqvGen r) a) = qv
          · refine ⟨Quot.mk _ u, ?_⟩
            have hu : (Quot.mk (Relation.EqvGen r) u) ≠ qv := fun h =>
              huv (quot_eqvGen_exact h)
            simp only [ψ, hu, ite_false, Option.some.injEq]
            apply quot_eqvGen_sound
            have hav := quot_eqvGen_exact ha
            exact (Relation.EqvGen.rel _ _ ((hr' u v).2 (Or.inr ⟨rfl, rfl⟩))).trans _ _ _
              (hmono _ _ hav.symm)
          · exact ⟨Quot.mk _ a, by simp [ψ, ha, φ]⟩
  have h1 := Nat.card_congr (Equiv.ofBijective ψ hψ)
  rw [h1]
  have : Finite (Quot (Relation.EqvGen r')) := Quot.finite _
  exact Finite.card_option

end QuotCount

/-! ## The number of blocks and the dot excess -/

section Excess

variable {k n : ℕ}

/-- The number of blocks of the dotted edges `cs` on the atoms. -/
def nBlk (cs : List (Comp (Atom k n))) : ℕ := Nat.card (Quot (Relation.EqvGen (dotRel cs)))

/-- The number of dotted edges of `cs`. -/
def nDotL (cs : List (Comp (Atom k n))) : ℕ := (cs.filter fun c => decide (c.kind = .dot)).length

/-- The dot excess of the dotted edges `cs`. -/
def excL (cs : List (Comp (Atom k n))) : ℤ := (nDotL cs : ℤ) - ((k + n : ℕ) : ℤ) + nBlk cs

theorem dotRel_cons_of_ne {c : Comp (Atom k n)} (hc : c.kind ≠ .dot)
    (cs : List (Comp (Atom k n))) (a b : Atom k n) : dotRel (c :: cs) a b ↔ dotRel cs a b := by
  constructor
  · rintro ⟨d, hd, hk, rfl, rfl⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact absurd hk hc
    · exact ⟨d, hd, hk, rfl, rfl⟩
  · rintro ⟨d, hd, hk, rfl, rfl⟩
    exact ⟨d, List.mem_cons_of_mem _ hd, hk, rfl, rfl⟩

theorem dotRel_cons_of_dot {c : Comp (Atom k n)} (hc : c.kind = .dot)
    (cs : List (Comp (Atom k n))) (a b : Atom k n) :
    dotRel (c :: cs) a b ↔ dotRel cs a b ∨ (a = c.x ∧ b = c.y) := by
  constructor
  · rintro ⟨d, hd, hk, rfl, rfl⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨d, hd, hk, rfl, rfl⟩
  · rintro (⟨d, hd, hk, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨d, List.mem_cons_of_mem _ hd, hk, rfl, rfl⟩
    · exact ⟨c, List.mem_cons_self .., hc, rfl, rfl⟩

theorem dotRel_perm {cs cs' : List (Comp (Atom k n))} (h : cs.Perm cs') (a b : Atom k n) :
    dotRel cs a b ↔ dotRel cs' a b := by
  constructor
  · rintro ⟨d, hd, hk, rfl, rfl⟩; exact ⟨d, h.mem_iff.1 hd, hk, rfl, rfl⟩
  · rintro ⟨d, hd, hk, rfl, rfl⟩; exact ⟨d, h.mem_iff.2 hd, hk, rfl, rfl⟩

theorem nBlk_perm {cs cs' : List (Comp (Atom k n))} (h : cs.Perm cs') :
    nBlk cs = nBlk cs' := by
  unfold nBlk
  have : dotRel cs = dotRel cs' := by funext a b; exact propext (dotRel_perm h a b)
  rw [this]

theorem excL_perm {cs cs' : List (Comp (Atom k n))} (h : cs.Perm cs') :
    excL cs = excL cs' := by
  unfold excL nDotL
  rw [nBlk_perm h, (h.filter _).length_eq]

theorem nBlk_nil : nBlk ([] : List (Comp (Atom k n))) = k + n := by
  unfold nBlk
  rw [card_quot_bot _ (by rintro a b ⟨d, hd, -⟩; simp at hd), Nat.card_eq_fintype_card]
  simp

theorem excL_cons_ne {c : Comp (Atom k n)} (hc : c.kind ≠ .dot)
    (cs : List (Comp (Atom k n))) : excL (c :: cs) = excL cs := by
  unfold excL nDotL nBlk
  have : dotRel (c :: cs) = dotRel cs := by funext a b; exact propext (dotRel_cons_of_ne hc cs a b)
  rw [this, List.filter_cons_of_neg (by simpa using hc)]

theorem excL_cons_dot_in {c : Comp (Atom k n)} (hc : c.kind = .dot)
    (cs : List (Comp (Atom k n))) (h : Relation.EqvGen (dotRel cs) c.x c.y) :
    excL (c :: cs) = excL cs + 1 := by
  unfold excL nDotL nBlk
  have heq : ∀ a b, Relation.EqvGen (dotRel (c :: cs)) a b ↔ Relation.EqvGen (dotRel cs) a b := by
    intro a b
    rw [eqvGen_add_iff (dotRel_cons_of_dot hc cs)]
    constructor
    · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h'
      · exact (h1.trans _ _ _ h).trans _ _ _ h2
      · exact (h1.trans _ _ _ h.symm).trans _ _ _ h2
    · exact fun h' => Or.inl h'
  rw [card_quot_congr heq, List.filter_cons_of_pos (by simpa using hc), List.length_cons]
  push_cast
  ring

theorem excL_cons_dot_out {c : Comp (Atom k n)} (hc : c.kind = .dot)
    (cs : List (Comp (Atom k n))) (h : ¬ Relation.EqvGen (dotRel cs) c.x c.y) :
    excL (c :: cs) = excL cs := by
  unfold excL nDotL nBlk
  rw [card_quot_add (dotRel_cons_of_dot hc cs) h, List.filter_cons_of_pos (by simpa using hc),
    List.length_cons]
  push_cast
  ring

/-- The dot excess is nonnegative, and when it is positive some dotted edge has its ends joined
by the other dotted edges. -/
theorem excL_spec (cs : List (Comp (Atom k n))) :
    0 ≤ excL cs ∧ (0 < excL cs → ∃ i c, cs[i]? = some c ∧ c.kind = .dot ∧
      Relation.EqvGen (dotRel (cs.eraseIdx i)) c.x c.y) := by
  induction cs with
  | nil =>
    unfold excL nDotL
    rw [nBlk_nil]
    simp
  | cons c cs ih =>
    obtain ⟨ih0, ih1⟩ := ih
    by_cases hc : c.kind = .dot
    · by_cases hr : Relation.EqvGen (dotRel cs) c.x c.y
      · rw [excL_cons_dot_in hc cs hr]
        exact ⟨by linarith, fun _ => ⟨0, c, rfl, hc, by simpa using hr⟩⟩
      · rw [excL_cons_dot_out hc cs hr]
        refine ⟨ih0, fun hpos => ?_⟩
        obtain ⟨i, d, hd, hdk, hdr⟩ := ih1 hpos
        refine ⟨i + 1, d, by simpa using hd, hdk, ?_⟩
        rw [List.eraseIdx_cons_succ]
        refine Relation.EqvGen.mono ?_ _ _ hdr
        rintro a b ⟨e, he, hk, rfl, rfl⟩
        exact ⟨e, List.mem_cons_of_mem _ he, hk, rfl, rfl⟩
    · rw [excL_cons_ne hc cs]
      refine ⟨ih0, fun hpos => ?_⟩
      obtain ⟨i, d, hd, hdk, hdr⟩ := ih1 hpos
      refine ⟨i + 1, d, by simpa using hd, hdk, ?_⟩
      rw [List.eraseIdx_cons_succ]
      refine Relation.EqvGen.mono ?_ _ _ hdr
      rintro a b ⟨e, he, hk, rfl, rfl⟩
      exact ⟨e, List.mem_cons_of_mem _ he, hk, rfl, rfl⟩

/-- A dotted edge between two blocks keeps the dot excess. -/
theorem excL_append_dot_out (cs : List (Comp (Atom k n))) (u v : Atom k n)
    (h : ¬ Relation.EqvGen (dotRel cs) u v) : excL (cs ++ [mkC .dot u v]) = excL cs := by
  rw [excL_perm (List.perm_append_comm), List.singleton_append]
  exact excL_cons_dot_out rfl cs h

/-- Components other than dotted edges do not change the dot excess. -/
theorem excL_append_nodot (cs ds : List (Comp (Atom k n)))
    (h : ∀ c ∈ ds, c.kind ≠ .dot) : excL (ds ++ cs) = excL cs := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.cons_append, excL_cons_ne (h d (List.mem_cons_self ..)),
      ih fun c hc => h c (List.mem_cons_of_mem _ hc)]

end Excess

/-! ## Products over lists -/

section ListLemmas

theorem dedup_eq_singleton {α : Type*} [DecidableEq α] (l : List α) (a : α)
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

end ListLemmas

/-! ## The value of `O_merge` -/

section MergeValue

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]

theorem mergeComp_label {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : psteps_mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) := by
  unfold psteps_mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain rfl := Option.some.inj h
    rfl

theorem mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : psteps_mergeComp rep f c = none) : c.kind = .dot ∧ f c.x = f c.y := by
  unfold psteps_mergeComp at h
  split_ifs at h with h1
  simpa using h1

theorem mergeComp_of_not_solid {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = false)
    (h : ¬ (c.kind = .dot ∧ f c.x = f c.y)) : psteps_mergeComp rep f c = some (c.map f) := by
  unfold psteps_mergeComp
  split_ifs with h1 h2
  · exact absurd (by simpa using h1) h
  · simp [hs] at h2
  · rfl

theorem mergeComp_of_solid {m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} (hs : c.kind.isSolid = true)
    (h : rep c.x ≠ rep c.y) : psteps_mergeComp rep f c = some (c.map f) := by
  unfold psteps_mergeComp
  split_ifs with h1 h2
  · simp at h1
    cases hk : c.kind <;> simp_all [Kind.isSolid]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact absurd h2.2 h
  · rfl

end MergeValue

section MergeValue2

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]

theorem termR_eq_zero_of_val {Γ : Graph k n} (PF : PFamily Ω ι) (D : Ω → Data ι)
    (σ : Atom k n → ι) (ω : Ω) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hl : c.label = none)
    (h0 : Comp.val (D ω) σ c = 0) : Γ.termR PF D σ ω = 0 := by
  unfold Graph.termR
  have : ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl]⟩, h0⟩)
  rw [this]
  simp

theorem psteps_mergeComp_kind {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : psteps_mergeComp rep f c = some c') :
    c'.kind = c.kind ∨ ∃ ch, c.kind = .G ch ∧ c'.kind = .weight ch := by
  unfold psteps_mergeComp at h
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

theorem PStepsMergeSpec.hlab {Γ : Graph k n} {t : Tracked k n} (hs : PStepsMergeSpec Γ t)
    (hlab : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none) :
    ∀ c' ∈ t.g.comps, (c'.kind = .dot ∨ c'.kind = .xdot) → c'.label = none := by
  intro c' hc' hk'
  rw [hs.comps_eq, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hmc⟩ := hc'
  rw [mergeComp_label hmc]
  rcases psteps_mergeComp_kind hmc with h | ⟨ch, hch, hch'⟩
  · rw [hlab c hc (by rwa [h] at hk')]
    rfl
  · rw [hch'] at hk'
    rcases hk' with h | h <;> cases h

end MergeValue2

section MergeFacts

variable {k n : ℕ}

theorem psteps_mergeComp_dot {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hk : c.kind = .dot) :
    psteps_mergeComp rep f c = if f c.x = f c.y then none else some (c.map f) := by
  unfold psteps_mergeComp
  by_cases h : f c.x = f c.y
  · simp [hk, h]
  · simp [hk, h, Kind.isSolid]

theorem psteps_mergeComp_solid {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hs : c.kind.isSolid = true) :
    psteps_mergeComp rep f c = if rep c.x = rep c.y then
      some { c.map f with kind := c.kind.toWeight, y := f c.x } else some (c.map f) := by
  have hnd : c.kind ≠ .dot := by
    intro h
    rw [h] at hs
    simp [Kind.isSolid] at hs
  unfold psteps_mergeComp
  by_cases h : rep c.x = rep c.y
  · simp [hs, h, hnd]
  · simp [hs, h, hnd]

theorem mergeComp_other {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (hd : c.kind ≠ .dot) (hs : c.kind.isSolid = false) :
    psteps_mergeComp rep f c = some (c.map f) := by
  unfold psteps_mergeComp
  simp [hd, hs]

variable {Γ : Graph k n} {t : Tracked k n}

theorem PStepsMergeSpec.mem_comps (hs : PStepsMergeSpec Γ t) {c' : Comp (Atom k t.nOut)} :
    c' ∈ t.g.comps ↔ ∃ c ∈ Γ.comps, psteps_mergeComp Γ.psteps_mrep t.f c = some c' := by
  rw [hs.comps_eq, List.mem_filterMap]

/-- A component that is neither a dotted edge nor a solid edge keeps its kind and is mapped. -/
theorem PStepsMergeSpec.mem_of_other (hs : PStepsMergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hd : c.kind ≠ .dot) (hsol : c.kind.isSolid = false) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, mergeComp_other hd hsol⟩

theorem PStepsMergeSpec.mem_of_solid (hs : PStepsMergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hsol : c.kind.isSolid = true) (hr : Γ.psteps_mrep c.x ≠ Γ.psteps_mrep c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [psteps_mergeComp_solid hsol, ite_eq_right hr]⟩

theorem PStepsMergeSpec.mem_of_dot (hs : PStepsMergeSpec Γ t) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .dot) (hf : t.f c.x ≠ t.f c.y) :
    c.map t.f ∈ t.g.comps :=
  hs.mem_comps.2 ⟨c, hc, by rw [psteps_mergeComp_dot hk, ite_eq_right hf]⟩

/-- A `×`-dotted component of `t.g` is the image of a `×`-dotted component of `Γ`. -/
theorem PStepsMergeSpec.of_mem_xdot (hs : PStepsMergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind = .xdot) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases psteps_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .xdot := h ▸ hk
    refine ⟨c, hc, hck, ?_⟩
    rw [mergeComp_other (by rw [hck]; exact fun h => by cases h) (by simp [hck, Kind.isSolid])]
      at hm
    exact (Option.some.inj hm).symm
  · rw [hch'] at hk
    cases hk

/-- A solid component of `t.g` is the image of a solid component of `Γ` whose ends are in
different blocks. -/
theorem PStepsMergeSpec.of_mem_solid (hs : PStepsMergeSpec Γ t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind.isSolid = true) :
    ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ Γ.psteps_mrep c.x ≠ Γ.psteps_mrep c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases psteps_mergeComp_kind hm with h | ⟨ch, hch, hch'⟩
  · have hck : c.kind.isSolid = true := by rw [← h]; exact hk
    rw [psteps_mergeComp_solid hck] at hm
    split_ifs at hm with hr
    · exfalso
      obtain rfl := Option.some.inj hm
      obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
        cases hkk : c.kind <;> simp_all [Kind.isSolid]
      simp [Kind.toWeight, hch, Kind.isSolid] at hk
    · exact ⟨c, hc, hck, hr, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    simp [Kind.isSolid] at hk

theorem PStepsMergeSpec.solid_ne (hs : PStepsMergeSpec Γ t) :
    ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → c'.x ≠ c'.y := by
  intro c' hc' hk'
  obtain ⟨c, hc, -, hr, rfl⟩ := hs.of_mem_solid hc' hk'
  exact hs.f_ne _ _ hr

end MergeFacts

section MergeOrder

variable {k n : ℕ}

theorem Kind.ord_toWeight_solid {κ : Kind} (h : κ.isSolid = true) :
    κ.toWeight.ord = κ.ord - 1 := by
  cases κ <;> simp_all [Kind.isSolid, Kind.ord, Kind.toWeight]

theorem sum_ord_mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (cs : List (Comp (Atom k n))) :
    ((cs.filterMap (psteps_mergeComp rep f)).map fun c => c.kind.ord).sum =
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
      · rw [psteps_mergeComp_dot hd, ite_eq_left hf]
        simp only [List.map_cons, List.sum_cons, List.filter_cons, hd, hf, beq_self_eq_true,
          Bool.and_self, ite_true, hsd, Bool.false_and, Bool.false_eq_true, ite_false,
          List.length_cons, Nat.cast_add, Nat.cast_one, hdo]
        rw [ih]
        ring
      · rw [psteps_mergeComp_dot hd, ite_eq_right hf]
        have hfb : (f c.x == f c.y) = false := by simpa using hf
        simp only [List.map_cons, List.sum_cons, List.filter_cons, hd, hfb, beq_self_eq_true,
          Bool.and_false, hsd, Bool.false_and, Bool.false_eq_true, ite_false, Comp.map, hdo]
        rw [ih]
        ring
    · by_cases hs : c.kind.isSolid = true
      · have hnd : (c.kind == .dot) = false := by simpa using hd
        by_cases hr : rep c.x = rep c.y
        · rw [psteps_mergeComp_solid hs, ite_eq_left hr]
          simp only [List.map_cons, List.sum_cons, List.filter_cons, hnd, Bool.false_and,
            Bool.false_eq_true, ite_false, hs, hr, beq_self_eq_true, Bool.and_self, ite_true,
            List.length_cons, Comp.map, Nat.cast_add, Nat.cast_one]
          rw [ih, Kind.ord_toWeight_solid hs]
          ring
        · rw [psteps_mergeComp_solid hs, ite_eq_right hr]
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

theorem PStepsMergeSpec.ord_eq {h : Graph k n} {t : Tracked k n} (hs : PStepsMergeSpec h t) :
    t.g.ord = h.ord
      - 2 * ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ)
      - ((h.comps.filter fun c => c.kind.isSolid && h.psteps_mrep c.x == h.psteps_mrep c.y).length : ℤ)
      + 2 * ((n : ℤ) - t.nOut) := by
  unfold Graph.ord
  rw [hs.comps_eq, sum_ord_mergeComp]
  ring


end MergeOrder

/-! ## Blocks and the dot excess under `O_merge` -/

section MergeBlocks

variable {k n : ℕ} {h : Graph k n} {t : Tracked k n}

theorem PStepsMergeSpec.sameBlock_of_f_eq (hs : PStepsMergeSpec h t) {u v : Atom k n}
    (hf : t.f u = t.f v) : h.SameBlock u v := by
  rw [Graph.sameBlock_iff_mrep]
  by_contra hne
  exact hs.f_ne u v hne hf

theorem PStepsMergeSpec.dot_image (hs : PStepsMergeSpec h t) {c' : Comp (Atom k t.nOut)}
    (hc' : c' ∈ t.g.comps) (hk : c'.kind = .dot) :
    ∃ c ∈ h.comps, c.kind = .dot ∧ t.f c.x ≠ t.f c.y ∧ c' = c.map t.f := by
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rcases psteps_mergeComp_kind hm with hkk | ⟨ch, hch, hch'⟩
  · have hck : c.kind = .dot := hkk ▸ hk
    rw [psteps_mergeComp_dot hck] at hm
    split_ifs at hm with hf
    exact ⟨c, hc, hck, hf, (Option.some.inj hm).symm⟩
  · rw [hch'] at hk
    cases hk

theorem PStepsMergeSpec.sameBlock_iff (hs : PStepsMergeSpec h t) (a b : Atom k n) :
    t.g.SameBlock (t.f a) (t.f b) ↔ h.SameBlock a b := by
  constructor
  · intro hab
    rw [Graph.sameBlock_iff_eqvGen] at hab
    have key : ∀ p q, Relation.EqvGen (dotRel t.g.comps) p q →
        ∀ a b, t.f a = p → t.f b = q → h.SameBlock a b := by
      intro p q hpq
      induction hpq with
      | rel p q hr =>
        obtain ⟨c', hc', hk, rfl, rfl⟩ := hr
        obtain ⟨c, hc, hck, -, rfl⟩ := hs.dot_image hc' hk
        intro a b ha hb
        exact (hs.sameBlock_of_f_eq ha).trans
          ((Graph.sameBlock_of_dot hc hck).trans (hs.sameBlock_of_f_eq hb.symm))
      | refl p =>
        intro a b ha hb
        exact hs.sameBlock_of_f_eq (ha.trans hb.symm)
      | symm p q _ ih =>
        intro a b ha hb
        exact Graph.sameBlock_symm (ih b a hb ha)
      | trans p q r _ _ ih1 ih2 =>
        intro a b ha hb
        obtain ⟨m, hm⟩ := hs.f_surj q
        exact (ih1 a m ha hm).trans (ih2 m b hm hb)
    exact key _ _ hab a b rfl rfl
  · intro hab
    rw [Graph.sameBlock_iff_eqvGen] at hab ⊢
    have key : ∀ p q, Relation.EqvGen (dotRel h.comps) p q →
        Relation.EqvGen (dotRel t.g.comps) (t.f p) (t.f q) := by
      intro p q hpq
      induction hpq with
      | rel p q hr =>
        obtain ⟨c, hc, hk, rfl, rfl⟩ := hr
        by_cases hf : t.f c.x = t.f c.y
        · rw [hf]; exact Relation.EqvGen.refl _
        · exact Relation.EqvGen.rel _ _ ⟨c.map t.f, hs.mem_of_dot hc hk hf, hk, rfl, rfl⟩
      | refl p => exact Relation.EqvGen.refl _
      | symm p q _ ih => exact ih.symm
      | trans p q r _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
    exact key _ _ hab

theorem PStepsMergeSpec.xdotApart (hs : PStepsMergeSpec h t) : t.g.XdotApart := by
  intro c' hc' hk hb
  obtain ⟨c, hc, hck, rfl⟩ := hs.of_mem_xdot hc' hk
  exact hs.xdot_ne c hc hck ((Graph.sameBlock_iff_mrep _ _ _).1 ((hs.sameBlock_iff _ _).1 hb))

theorem PStepsMergeSpec.nBlk_eq (hs : PStepsMergeSpec h t) : nBlk t.g.comps = nBlk h.comps := by
  unfold nBlk
  refine (card_quot_map t.f hs.f_surj fun a b => ?_).symm
  rw [← Graph.sameBlock_iff_eqvGen, ← Graph.sameBlock_iff_eqvGen, hs.sameBlock_iff]

theorem nDot_filterMap_mergeComp {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (cs : List (Comp (Atom k n))) :
    nDotL (cs.filterMap (psteps_mergeComp rep f)) +
        (cs.filter fun c => c.kind == .dot && f c.x == f c.y).length = nDotL cs := by
  unfold nDotL
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.filterMap_cons]
    by_cases hd : c.kind = .dot
    · rw [psteps_mergeComp_dot hd]
      by_cases hf : f c.x = f c.y
      · simp [hd, hf]
        omega
      · simp [hd, hf, Comp.map]
        omega
    · by_cases hs : c.kind.isSolid = true
      · rw [psteps_mergeComp_solid hs]
        obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hs
        split_ifs with hr
        · simp [hch, Kind.toWeight]
          omega
        · simp [hch, Comp.map]
          omega
      · rw [mergeComp_other hd (by simpa using hs)]
        simp [hd, Comp.map]
        omega

/-- The dot excess under `O_merge`: the dotted edges between identified atoms are removed and
the number of atoms drops by the number of identified internal atoms. -/
theorem PStepsMergeSpec.excL_eq (hs : PStepsMergeSpec h t) :
    excL t.g.comps = excL h.comps -
      ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ) +
      ((n : ℤ) - t.nOut) := by
  have h1 := nDot_filterMap_mergeComp h.psteps_mrep t.f h.comps
  rw [← hs.comps_eq] at h1
  unfold excL
  rw [hs.nBlk_eq]
  push_cast
  have h2 : ((nDotL t.g.comps : ℕ) : ℤ) = (nDotL h.comps : ℤ) -
      ((h.comps.filter fun c => c.kind == .dot && t.f c.x == t.f c.y).length : ℤ) := by
    rw [← h1]; push_cast; ring
  rw [h2]
  ring

end MergeBlocks

/-! ## Identified internal atoms -/

section Twins

variable {k n : ℕ}

theorem card_le_of_twins {m : ℕ} (g : Fin n → Fin m) (hg : Function.Surjective g)
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

theorem PStepsMergeSpec.g_eq {h : Graph k n} {t : Tracked k n} (hs : PStepsMergeSpec h t)
    {g : Fin n → Fin t.nOut} (hg : ∀ i, t.f (.inr i) = .inr (g i)) {i j : Fin n}
    (hr : h.psteps_mrep (.inr i) = h.psteps_mrep (.inr j)) : g i = g j := by
  have := hs.f_eq _ _ hr rfl rfl
  rw [hg, hg] at this
  exact Sum.inr.inj this

/-- Two distinct internal atoms in one dot block make `n - nOut` positive. -/
theorem PStepsMergeSpec.r_one {h : Graph k n} {t : Tracked k n} (hs : PStepsMergeSpec h t) {i j : Fin n}
    (hij : i ≠ j) (hr : h.psteps_mrep (.inr i) = h.psteps_mrep (.inr j)) : t.nOut + 1 ≤ n := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hgij := hs.g_eq hg hr
  have := card_le_of_twins g hgs {j}
    (fun v hv => ⟨i, by simpa [Finset.mem_singleton.1 hv] using hij,
      by rw [Finset.mem_singleton.1 hv]; exact hgij⟩)
  simpa using this

end Twins

/-! ## Terms with unlabelled factors -/

section TermUnl

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)

theorem termR_perm' {L L' : List (Comp (Atom k n))} (h : L.Perm L') (co : Coeff)
    (σ : Atom k n → ι) (ω : Ω) :
    Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω = Graph.termR (⟨L', co⟩ : Graph k n) PF D σ ω := by
  have h1 : ((L.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod =
      ((L'.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod :=
    ((h.filter _).map _).prod_eq
  have h2 : (L.filterMap Comp.label).dedup.Perm (L'.filterMap Comp.label).dedup :=
    (h.filterMap _).dedup
  have h3 : ∀ ℓ : PQ × Atom k n,
      (fun ω' => ((L.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) =
      (fun ω' => ((L'.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) :=
    fun ℓ => funext fun ω' => ((h.filter _).map _).prod_eq
  simp only [Graph.termR, Graph.labels, h3, h1]
  congr 1
  exact (h2.map _).prod_eq

/-- The term with one more unlabelled component is multiplied by its factor. -/
theorem termR_cons_unl (c : Comp (Atom k n)) (hc : c.label = none)
    (L : List (Comp (Atom k n))) (co : Coeff) (σ : Atom k n → ι) (ω : Ω) :
    Graph.termR (⟨c :: L, co⟩ : Graph k n) PF D σ ω =
      Comp.val (D ω) σ c * Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω := by
  have hc1 : (c :: L).filter (fun c => c.label.isNone) = c :: L.filter (fun c => c.label.isNone) :=
    List.filter_cons_of_pos (by simp [hc])
  have hc2 : ∀ ℓ : PQ × Atom k n, (c :: L).filter (fun c => decide (c.label = some ℓ)) =
      L.filter (fun c => decide (c.label = some ℓ)) :=
    fun ℓ => List.filter_cons_of_neg (by simp [hc])
  have hc3 : (c :: L).filterMap Comp.label = L.filterMap Comp.label := by simp [hc]
  simp only [Graph.termR, Graph.labels, hc1, hc2, hc3, List.map_cons, List.prod_cons]
  ring

theorem termR_append_unl (c : Comp (Atom k n)) (hc : c.label = none)
    (L : List (Comp (Atom k n))) (co : Coeff) (σ : Atom k n → ι) (ω : Ω) :
    Graph.termR (⟨L ++ [c], co⟩ : Graph k n) PF D σ ω =
      Comp.val (D ω) σ c * Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω := by
  rw [termR_perm' PF D (List.perm_append_comm) co σ ω, List.singleton_append,
    termR_cons_unl PF D c hc]

theorem termR_neg (L : List (Comp (Atom k n))) (co : Coeff) (σ : Atom k n → ι) (ω : Ω) :
    Graph.termR (⟨L, -co⟩ : Graph k n) PF D σ ω = -Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω := by
  simp only [Graph.termR, Graph.labels, Coeff.eval, map_neg]
  ring

theorem termR_eq_zero_of_dot (g : Graph k n) (σ : Atom k n → ι) (ω : Ω)
    (hlab : ∀ c ∈ g.comps, c.kind = .dot → c.label = none)
    (hz : ¬ ∀ c ∈ g.comps, c.kind = .dot → σ c.x = σ c.y) : g.termR PF D σ ω = 0 := by
  push Not at hz
  obtain ⟨c, hc, hk, hne⟩ := hz
  exact termR_eq_zero_of_val PF D σ ω hc (hlab c hc hk) (by simp [Comp.val, hk, hne])

/-- A graph with a `×`-dotted edge inside a block has value `0`. -/
private theorem termR_eq_zero_of_not_xdotApart (g : Graph k n) (σ : Atom k n → ι) (ω : Ω)
    (hlab : ∀ c ∈ g.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
    (hx : ¬ g.XdotApart) : g.termR PF D σ ω = 0 := by
  by_cases hz : ∀ c ∈ g.comps, c.kind = .dot → σ c.x = σ c.y
  · unfold Graph.XdotApart at hx
    push Not at hx
    obtain ⟨c, hc, hk, hb⟩ := hx
    have := Graph.sigma_eq_of_sameBlock σ hz hb
    exact termR_eq_zero_of_val PF D σ ω hc (hlab c hc (Or.inr hk)) (by simp [Comp.val, hk, this])
  · exact termR_eq_zero_of_dot PF D g σ ω (fun c hc hk => hlab c hc (Or.inl hk)) hz

theorem valR_eq_zero_of_not_xdotApart (g : Graph k n) (e : Fin k → ι)
    (hlab : ∀ c ∈ g.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none)
    (hx : ¬ g.XdotApart) : g.valR PF D e = 0 := by
  funext ω
  simp only [Graph.valR, Pi.zero_apply]
  exact Finset.sum_eq_zero fun s _ => termR_eq_zero_of_not_xdotApart PF D g _ ω hlab hx

/-- `1 = 1_{u = v} + 1_{u ≠ v}`. -/
theorem valR_split (L : List (Comp (Atom k n))) (co : Coeff) (u v : Atom k n)
    (e : Fin k → ι) (ω : Ω) :
    (⟨L ++ [mkC .dot u v], co⟩ : Graph k n).valR PF D e ω +
      (⟨L ++ [mkC .xdot u v], co⟩ : Graph k n).valR PF D e ω =
      (⟨L, co⟩ : Graph k n).valR PF D e ω := by
  simp only [Graph.valR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [termR_append_unl PF D _ rfl, termR_append_unl PF D _ rfl]
  simp only [Comp.val, mkC]
  by_cases huv : Sum.elim e s u = Sum.elim e s v <;> simp [huv]

/-- `1_{u ≠ v} = 1 - 1_{u = v}`. -/
theorem valR_xdot (L : List (Comp (Atom k n))) (co : Coeff) {i : ℕ} {c : Comp (Atom k n)}
    (hc : L[i]? = some c) (hk : c.kind = .xdot) (hl : c.label = none) (e : Fin k → ι) (ω : Ω) :
    (⟨L.eraseIdx i, co⟩ : Graph k n).valR PF D e ω +
      (⟨L.eraseIdx i ++ [mkC .dot c.x c.y], -co⟩ : Graph k n).valR PF D e ω =
      (⟨L, co⟩ : Graph k n).valR PF D e ω := by
  have hi : i < L.length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hc
    cases hc
  have hp : L.Perm (c :: L.eraseIdx i) := by
    have := List.getElem_cons_eraseIdx_perm hi
    rw [List.getElem?_eq_getElem hi] at hc
    rw [← Option.some.inj hc]
    exact this.symm
  simp only [Graph.valR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [termR_append_unl PF D _ rfl, termR_neg, termR_perm' PF D hp, termR_cons_unl PF D c hl]
  simp only [Comp.val, mkC, hk]
  by_cases huv : Sum.elim e s c.x = Sum.elim e s c.y <;> simp [huv]

end TermUnl

/-! ## `O_merge` followed by the removal of redundant dotted edges -/

section MergeClean

variable {k : ℕ}

theorem perm_cons_eraseIdx {α : Type*} {L : List α} {i : ℕ} {c : α} (hc : L[i]? = some c) :
    L.Perm (c :: L.eraseIdx i) := by
  have hi : i < L.length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hc
    cases hc
  have := List.getElem_cons_eraseIdx_perm hi
  rw [List.getElem?_eq_getElem hi] at hc
  rw [← Option.some.inj hc]
  exact this.symm

end MergeClean

/-! ## Relations between an input graph and an output graph -/

section Rel

variable {k : ℕ}

/-- The composition of tracked graphs: `s` is an output of `t.g`. -/
def Tracked.comp {n : ℕ} (t : Tracked k n) (s : Tracked k t.nOut) : Tracked k n :=
  ⟨s.nOut, s.g, s.f ∘ t.f⟩

/-- Components carry labels only if they are random. -/
def Graph.LabRand {n : ℕ} (g : Graph k n) : Prop :=
  ∀ c ∈ g.comps, c.label.isSome = true → c.kind.isRandom = true

theorem Graph.Plain.labRand {n : ℕ} {g : Graph k n} (h : g.Plain) : g.LabRand :=
  fun c hc => (h c hc).2.2.2.2.2

/-- The clauses kept from an input graph `g` at `x` to an output `s` (one step of the
construction, or several). -/
structure SR {n : ℕ} (g : Graph k n) (x : Atom k n) (s : Tracked k n) : Prop where
  carries : s.Carries g
  dc : g.DoublyConnected → s.g.DoublyConnected
  exc : excL s.g.comps ≤ excL g.comps
  fx : (s.f x).isRight = true
  chain : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨s.nOut, s.g⟩
  newWaved : ∀ u, s.IsNew u → s.g.wavedGraph.Reachable (s.f x) u

theorem subperm_map' {α β : Type*} {l l' : List α} (h : l.Subperm l') (f : α → β) :
    (l.map f).Subperm (l'.map f) := by
  obtain ⟨l'', hp, hs⟩ := h
  exact ⟨l''.map f, hp.map f, hs.map f⟩

theorem subperm_filter_of_forall {α : Type*} {l l' : List α} (h : l.Subperm l')
    (p : α → Bool) (hp : ∀ a ∈ l, p a = true) : l.Subperm (l'.filter p) := by
  have := h.filter p
  rwa [List.filter_eq_self.2 hp] at this

theorem Tracked.Carries.mem {n : ℕ} {g : Graph k n} {s : Tracked k n} (h : s.Carries g)
    {c : Comp (Atom k n)} (hc : c ∈ g.comps) (hl : c.label = none) (hd : c.kind ≠ .dot)
    (hx : c.kind ≠ .xdot) : c.map s.f ∈ s.g.comps :=
  h.1.subset (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl, hd, hx]⟩, rfl⟩)

theorem Tracked.Carries.trans {n : ℕ} {g : Graph k n} {t : Tracked k n}
    {s : Tracked k t.nOut} (h1 : t.Carries g) (h2 : s.Carries t.g) : (t.comp s).Carries g := by
  refine ⟨?_, fun u v huv => h2.2 _ _ (h1.2 u v huv)⟩
  have hA := subperm_filter_of_forall h1.1
    (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)) (by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have := (List.mem_filter.1 hd).2
      simp only [decide_eq_true_eq] at this ⊢
      simp only [Comp.map]
      refine ⟨by rw [this.1]; rfl, this.2.1, this.2.2⟩)
  have hB := (subperm_map' hA (Comp.map s.f)).trans h2.1
  simp only [List.map_map] at hB
  change ((g.comps.filter _).map (Comp.map (s.f ∘ t.f))).Subperm s.g.comps
  convert hB using 2
  funext c
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map, Function.comp_def]

theorem Tracked.Carries.waved {n : ℕ} {g : Graph k n} {s : Tracked k n}
    (h : s.Carries g) (hw : ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) → c.label = none)
    {u v : Atom k n} (huv : g.wavedGraph.Reachable u v) :
    s.g.wavedGraph.Reachable (s.f u) (s.f v) := by
  unfold Graph.wavedGraph at huv ⊢
  rw [reachable_fromRel_iff] at huv ⊢
  induction huv with
  | rel a b hab =>
    obtain ⟨c, hc, ⟨w, hw'⟩, rfl, rfl⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨c.map s.f, h.mem hc (hw c hc ⟨w, hw'⟩) (by rw [hw']; simp)
      (by rw [hw']; simp), ⟨w, hw'⟩, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

theorem Graph.LabRand.waved {n : ℕ} {g : Graph k n} (h : g.LabRand) :
    ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) → c.label = none := by
  rintro c hc ⟨w, hw⟩
  by_contra hne
  have := h c hc (Option.isSome_iff_ne_none.2 hne)
  rw [hw] at this
  simp [Kind.isRandom] at this

theorem SR.trans {n : ℕ} {g : Graph k n} {x : Atom k n} {t : Tracked k n}
    {s : Tracked k t.nOut} (h1 : SR g x t) (hp : t.g.LabRand) (h2 : SR t.g (t.f x) s) :
    SR g x (t.comp s) := by
  refine ⟨h1.carries.trans h2.carries, fun h => h2.dc (h1.dc h),
    h2.exc.trans h1.exc, h2.fx, h1.chain.trans h2.chain, ?_⟩
  intro u hu
  by_cases hs : s.IsNew u
  · exact h2.newWaved u hs
  · unfold Tracked.IsNew at hs
    push Not at hs
    obtain ⟨w, rfl⟩ := hs
    have hw : t.IsNew w := fun v hv => hu v (by simp [Tracked.comp, hv])
    exact h2.carries.waved hp.waved (h1.newWaved w hw)

theorem SR.refl {n : ℕ} (g : Graph k n) (x : Atom k n) (hx : x.isRight = true) :
    SR g x (Tracked.self g) := by
  refine ⟨⟨?_, fun u v h => h⟩, id, le_rfl, hx, Relation.ReflTransGen.refl, ?_⟩
  · have : (g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).map
        (Comp.map (Tracked.self g).f) = g.comps.filter fun c => decide (c.label = none ∧
          c.kind ≠ .dot ∧ c.kind ≠ .xdot) := by
      simp only [Tracked.self]
      conv_rhs => rw [← List.map_id (g.comps.filter _)]
      refine List.map_congr_left fun c _ => ?_
      cases c; simp [Comp.map]
    rw [this]
    exact List.filter_sublist.subperm
  · intro u hu
    exact absurd rfl (hu u)

theorem Tracked.psteps_comp_self {n : ℕ} (t : Tracked k n) :
    t.comp (Tracked.self t.g) = t := by
  rcases t with ⟨m, g, f⟩
  rfl

end Rel

/-! ## Formal sums and their values -/

section Sums

variable {k : ℕ}

theorem TExpansion.valR_cons {n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (t : Tracked k n) (E : TExpansion k n) :
    (TExpansion.forget (t :: E)).valR PF D e =
      t.g.valR PF D e + (TExpansion.forget E).valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR]

theorem TExpansion.valR_append {n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (E E' : TExpansion k n) :
    (TExpansion.forget (E ++ E')).valR PF D e =
      (TExpansion.forget E).valR PF D e + (TExpansion.forget E').valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR]

theorem TExpansion.valR_map_comp {n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (t : Tracked k n)
    (F : TExpansion k t.nOut) :
    (TExpansion.forget (F.map t.comp)).valR PF D e = (TExpansion.forget F).valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR, Tracked.comp, List.map_map, Function.comp_def]

theorem TExpansion.valueEq_bind {n : ℕ} (g : Graph k n) (R : TExpansion k n)
    (hR : R.ValueEq g modelAdm) (Fs : List (Σ t : Tracked k n, TExpansion k t.nOut))
    (hFs : Fs.map Sigma.fst = R) (hF : ∀ p ∈ Fs, p.2.ValueEq p.1.g modelAdm) :
    TExpansion.ValueEq (Fs.flatMap fun p => p.2.map p.1.comp) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  rw [← hR Ω ι PF D hA e, ← hFs]
  clear hFs hR
  induction Fs with
  | nil => rfl
  | cons p Fs ih =>
    rw [List.flatMap_cons, TExpansion.valR_append, TExpansion.valR_map_comp,
      hF p (List.mem_cons_self ..) Ω ι PF D hA e, ih fun q hq => hF q (List.mem_cons_of_mem _ hq),
      List.map_cons, TExpansion.valR_cons]

theorem TExpansion.length_bind {n : ℕ} (Fs : List (Σ t : Tracked k n, TExpansion k t.nOut))
    (K : ℕ) (hK : ∀ p ∈ Fs, p.2.length ≤ K) :
    (Fs.flatMap fun p => p.2.map p.1.comp).length ≤ Fs.length * K := by
  induction Fs with
  | nil => simp
  | cons p Fs ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
    have := hK p (List.mem_cons_self ..)
    have := ih fun q hq => hK q (List.mem_cons_of_mem _ hq)
    nlinarith

end Sums

/-! ## The doubly connected property through lists of components -/

section DCList

variable {k : ℕ}

/-- The relation of the net of a list of components on the internal atoms. -/
def nrel {n : ℕ} (g : Graph k n) (L : List (Comp (Atom k n))) (a b : Fin n) : Prop :=
  g.SameMol (.inr a) (.inr b) ∨ ∃ c ∈ L, c.x = .inr a ∧ c.y = .inr b

/-- The doubly connected property with the two nets given as lists of components. -/
def Graph.DCL {n : ℕ} (g : Graph k n) : Prop :=
  ∃ Lb Lu : List (Comp (Atom k n)), (Lb ++ Lu).Subperm g.comps ∧
    (∀ c ∈ Lb, c.kind.isDiffusive = true) ∧
    (∀ c ∈ Lu, c.kind.isDiffusive = true ∨ c.kind.isBlue = true) ∧
    (SimpleGraph.fromRel (nrel g Lb)).Preconnected ∧ (SimpleGraph.fromRel (nrel g Lu)).Preconnected

theorem net_eq_fromRel {n : ℕ} (g : Graph k n) (B : Finset (Fin g.comps.length)) :
    g.net B = SimpleGraph.fromRel (nrel g (B.toList.map fun i => g.comps[i])) := by
  ext a b
  unfold Graph.net nrel
  simp only [SimpleGraph.fromRel_adj, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨hne, h | h⟩
    · refine ⟨hne, Or.inl ?_⟩
      rcases h with h | ⟨i, hi, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨i, hi, rfl⟩, hx, hy⟩
    · refine ⟨hne, Or.inr ?_⟩
      rcases h with h | ⟨i, hi, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, ⟨i, hi, rfl⟩, hx, hy⟩
  · rintro ⟨hne, h | h⟩
    · refine ⟨hne, Or.inl ?_⟩
      rcases h with h | ⟨c, ⟨i, hi, rfl⟩, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, hx, hy⟩
    · refine ⟨hne, Or.inr ?_⟩
      rcases h with h | ⟨c, ⟨i, hi, rfl⟩, hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, hx, hy⟩

theorem Graph.dcl_of_dc {n : ℕ} {g : Graph k n} (h : g.DoublyConnected) : g.DCL := by
  obtain ⟨black, blue, hdisj, hb, hu, hsb, hsu⟩ := h
  refine ⟨black.toList.map (fun i => g.comps[i]), blue.toList.map (fun i => g.comps[i]), ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← List.map_append]
    have hnd : (black.toList ++ blue.toList).Nodup := by
      rw [List.nodup_append]
      refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
      intro a ha b hb' hab
      subst hab
      exact Finset.disjoint_left.1 hdisj (Finset.mem_toList.1 ha) (Finset.mem_toList.1 hb')
    have hsub : (black.toList ++ blue.toList).Subperm (List.finRange g.comps.length) :=
      hnd.subperm fun i _ => List.mem_finRange i
    have := subperm_map' hsub (fun i => g.comps[i])
    rwa [show (List.finRange g.comps.length).map (fun i => g.comps[i]) = g.comps from
      List.map_getElem_finRange g.comps] at this
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact hb i (Finset.mem_toList.1 hi)
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact hu i (Finset.mem_toList.1 hi)
  · have := hsb; unfold Graph.Spans at this; rwa [net_eq_fromRel] at this
  · have := hsu; unfold Graph.Spans at this; rwa [net_eq_fromRel] at this

theorem Graph.dc_of_dcl {n : ℕ} {g : Graph k n} (h : g.DCL) : g.DoublyConnected := by
  classical
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := h
  let φ := hsub.idxInj
  have hφ : Function.Injective φ := hsub.idxInj_injective
  have hget : ∀ i : Fin (Lb ++ Lu).length, g.comps[φ i] = (Lb ++ Lu)[(i : ℕ)] :=
    fun i => hsub.getElem_idxInj_eq_getElem
  let iB : Finset (Fin (Lb ++ Lu).length) := Finset.univ.filter fun i => (i : ℕ) < Lb.length
  let iU : Finset (Fin (Lb ++ Lu).length) := Finset.univ.filter fun i => Lb.length ≤ (i : ℕ)
  refine ⟨iB.map ⟨φ, hφ⟩, iU.map ⟨φ, hφ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
    obtain ⟨i', hi', he⟩ := Finset.mem_map.1 hj'
    have := hφ he
    subst this
    simp only [iB, iU, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    omega
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
    simp only [iB, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Function.Embedding.coeFn_mk]
    rw [hget i, List.getElem_append_left hi]
    exact hb _ (List.getElem_mem _)
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
    simp only [iU, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Function.Embedding.coeFn_mk]
    rw [hget i, List.getElem_append_right hi]
    exact hu _ (List.getElem_mem _)
  · have hmem : ∀ c, c ∈ Lb → ∃ j ∈ iB.map ⟨φ, hφ⟩, g.comps[j] = c := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have hi' : i < (Lb ++ Lu).length := by simp; omega
      refine ⟨φ ⟨i, hi'⟩, Finset.mem_map.2 ⟨⟨i, hi'⟩, by simp [iB, hi], rfl⟩, ?_⟩
      rw [hget, List.getElem_append_left hi]
    unfold Graph.Spans Graph.net
    intro a b
    have hab := hsb a b
    rw [reachable_fromRel_iff] at hab ⊢
    refine Relation.EqvGen.mono ?_ _ _ hab
    rintro x y (hxy | ⟨c, hc, hx, hy⟩)
    · exact Or.inl hxy
    · obtain ⟨j, hj, rfl⟩ := hmem c hc
      exact Or.inr ⟨j, hj, hx, hy⟩
  · have hmem : ∀ c, c ∈ Lu → ∃ j ∈ iU.map ⟨φ, hφ⟩, g.comps[j] = c := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have hi' : Lb.length + i < (Lb ++ Lu).length := by simp; omega
      refine ⟨φ ⟨Lb.length + i, hi'⟩, Finset.mem_map.2 ⟨⟨Lb.length + i, hi'⟩, by simp [iU], rfl⟩,
        ?_⟩
      rw [hget, List.getElem_append_right (by simp)]
      simp
    unfold Graph.Spans Graph.net
    intro a b
    have hab := hsu a b
    rw [reachable_fromRel_iff] at hab ⊢
    refine Relation.EqvGen.mono ?_ _ _ hab
    rintro x y (hxy | ⟨c, hc, hx, hy⟩)
    · exact Or.inl hxy
    · obtain ⟨j, hj, rfl⟩ := hmem c hc
      exact Or.inr ⟨j, hj, hx, hy⟩

/-- Diffusive and ghost edges. -/
def dgB (κ : Kind) : Bool := κ.isDiffusive || κ == .ghost

theorem kind_of_blue_not_dg {κ : Kind} (h : κ.isBlue = true) (h' : dgB κ = false) :
    κ = .G .plus := by
  cases κ with
  | G ch => cases ch <;> simp_all [Kind.isBlue]
  | ghost => simp [dgB] at h'
  | _ => simp [Kind.isBlue] at h

/-- The blue connection on the internal atoms of `g`: molecules and solid edges `G` of charge
`plus`. -/
def bconn {n : ℕ} (g : Graph k n) (a b : Fin n) : Prop :=
  g.SameMol (.inr a) (.inr b) ∨ ∃ d ∈ g.comps, d.kind = .G .plus ∧ d.x = .inr a ∧ d.y = .inr b

/-- The transfer of the doubly connected property along an atom map `f` from `g` to `g'`:
internal atoms go to internal atoms, molecules into molecules, every internal atom of `g'` lies in
the molecule of an image, the unlabelled components are carried, and the solid edges `G` between
internal atoms are replaced by paths of molecules and solid edges `G`. -/
theorem dc_transfer {n n' : ℕ} {g : Graph k n} {g' : Graph k n'} (f : Atom k n → Atom k n')
    (hlr : g.LabRand)
    (hint : ∀ i : Fin n, ∃ j, f (.inr i) = .inr j)
    (hmol : ∀ u v, u.isRight = true → v.isRight = true → g.SameMol u v → g'.SameMol (f u) (f v))
    (hcov : ∀ j : Fin n', ∃ i : Fin n, g'.SameMol (.inr j) (f (.inr i)))
    (hcar : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).map
      (Comp.map f)).Subperm g'.comps)
    (hblue : ∀ c ∈ g.comps, c.kind = .G .plus → ∀ a b a' b', c.x = .inr a → c.y = .inr b →
      f (.inr a) = .inr a' → f (.inr b) = .inr b' → Relation.EqvGen (bconn g') a' b')
    (h : g.DoublyConnected) : g'.DoublyConnected := by
  classical
  apply Graph.dc_of_dcl
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc h
  choose fi hfi using hint
  -- the diffusive and ghost components are carried
  have henv : ∀ c ∈ g.comps, dgB c.kind = true →
      decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot) = true := by
    intro c hc hd
    have hnr : c.kind.isRandom = false := by
      cases hk : c.kind <;> simp_all [dgB, Kind.isDiffusive, Kind.isRandom]
    have hl : c.label = none := by
      by_contra hne
      have := hlr c hc (Option.isSome_iff_ne_none.2 hne)
      rw [hnr] at this; cases this
    have hnd : c.kind ≠ .dot := by intro h'; rw [h'] at hd; simp [dgB, Kind.isDiffusive] at hd
    have hnx : c.kind ≠ .xdot := by intro h'; rw [h'] at hd; simp [dgB, Kind.isDiffusive] at hd
    simp [hl, hnd, hnx]
  set Lud := Lu.filter fun c => dgB c.kind with hLud
  have hA : (Lb ++ Lud).Subperm (g.comps.filter fun c => dgB c.kind) := by
    have h1 := hsub.filter (fun c => dgB c.kind)
    rw [List.filter_append, List.filter_eq_self.2 (fun c hc => by
      simp [dgB, hb c hc])] at h1
    exact h1
  have hB : (g.comps.filter fun c => dgB c.kind).Subperm
      (g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)) := by
    rw [show (g.comps.filter fun c => dgB c.kind) =
      (g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).filter
        (fun c => dgB c.kind) from ?_]
    · exact List.filter_sublist.subperm
    · rw [List.filter_filter]
      refine List.filter_congr fun c hc => ?_
      by_cases hd : dgB c.kind = true
      · simp [hd, henv c hc hd]
      · simp [hd]
  have hC : ((Lb ++ Lud).map (Comp.map f)).Subperm
      (g'.comps.filter fun c => !(c.kind == .G .plus)) := by
    refine subperm_filter_of_forall ((subperm_map' (hA.trans hB) _).trans hcar) _ ?_
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    have : dgB d.kind = true := by
      rcases List.mem_append.1 hd with hd | hd
      · simp [dgB, hb d hd]
      · exact (List.mem_filter.1 hd).2
    simp only [Comp.map]
    cases hk : d.kind <;> simp_all [dgB, Kind.isDiffusive]
  set Lb' := Lb.map (Comp.map f)
  set Lu' := Lud.map (Comp.map f) ++ g'.comps.filter fun c => c.kind == .G .plus
  -- reachability in the nets of `g'`
  have hmolE : ∀ (L : List (Comp (Atom k n'))) (a b : Fin n'), g'.SameMol (.inr a) (.inr b) →
      Relation.EqvGen (nrel g' L) a b := fun L a b h => Relation.EqvGen.rel _ _ (Or.inl h)
  have hcover : ∀ (L : List (Comp (Atom k n'))),
      (∀ a b : Fin n, Relation.EqvGen (nrel g' L) (fi a) (fi b)) →
      (SimpleGraph.fromRel (nrel g' L)).Preconnected := by
    intro L hL j₁ j₂
    rw [reachable_fromRel_iff]
    obtain ⟨i₁, h₁⟩ := hcov j₁
    obtain ⟨i₂, h₂⟩ := hcov j₂
    rw [hfi] at h₁ h₂
    exact ((hmolE L _ _ h₁).trans _ _ _ (hL i₁ i₂)).trans _ _ _ (hmolE L _ _ h₂).symm
  have hlift : ∀ (L : List (Comp (Atom k n))) (L' : List (Comp (Atom k n'))),
      (∀ c ∈ L, ∀ a b, c.x = .inr a → c.y = .inr b → Relation.EqvGen (nrel g' L') (fi a) (fi b)) →
      ∀ a b, Relation.EqvGen (nrel g L) a b → Relation.EqvGen (nrel g' L') (fi a) (fi b) := by
    intro L L' hL a b hab
    induction hab with
    | rel a b hr =>
      rcases hr with hm | ⟨c, hc, hx, hy⟩
      · have := hmol _ _ rfl rfl hm
        rw [hfi, hfi] at this
        exact hmolE L' _ _ this
      · exact hL c hc a b hx hy
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  refine ⟨Lb', Lu', ?_, ?_, ?_, ?_, ?_⟩
  · have hp : List.Perm ((g'.comps.filter fun c => !(c.kind == .G .plus)) ++
        (g'.comps.filter fun c => c.kind == .G .plus)) g'.comps := by
      have := List.filter_append_perm (fun c : Comp (Atom k n') => !(c.kind == .G .plus)) g'.comps
      simpa using this
    have := (hC.append (List.Subperm.refl (g'.comps.filter fun c => c.kind == .G .plus))).trans
      hp.subperm
    simpa [Lb', Lu', List.map_append, List.append_assoc] using this
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact hb d hd
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have := (List.mem_filter.1 hd).2
      simp only [dgB, Bool.or_eq_true, beq_iff_eq] at this
      rcases this with h | h
      · exact Or.inl h
      · right; simp [Comp.map, h, Kind.isBlue]
    · have := (List.mem_filter.1 hc).2
      simp only [beq_iff_eq] at this
      right; simp [this, Kind.isBlue]
  · refine hcover Lb' fun a b => hlift Lb Lb' ?_ a b ?_
    · intro c hc a b hx hy
      refine Relation.EqvGen.rel _ _ (Or.inr ⟨c.map f, List.mem_map.2 ⟨c, hc, rfl⟩, ?_, ?_⟩)
      · simp [Comp.map, hx, hfi]
      · simp [Comp.map, hy, hfi]
    · have := hsb a b; rwa [reachable_fromRel_iff] at this
  · refine hcover Lu' fun a b => hlift Lu Lu' ?_ a b ?_
    · intro c hc a b hx hy
      by_cases hd : dgB c.kind = true
      · refine Relation.EqvGen.rel _ _ (Or.inr ⟨c.map f, List.mem_append_left _
          (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hd⟩, rfl⟩), ?_, ?_⟩)
        · simp [Comp.map, hx, hfi]
        · simp [Comp.map, hy, hfi]
      · have hGp : c.kind = .G .plus := by
          rcases hu c hc with h' | h'
          · exact absurd (by simp [dgB, h']) hd
          · exact kind_of_blue_not_dg h' (by simpa using hd)
        have hcmem : c ∈ g.comps := hsub.subset (List.mem_append_right _ hc)
        have hbc := hblue c hcmem hGp a b (fi a) (fi b) hx hy (hfi a) (hfi b)
        refine Relation.EqvGen.mono ?_ _ _ hbc
        rintro p q (hm | ⟨d, hd, hdk, hdx, hdy⟩)
        · exact Or.inl hm
        · exact Or.inr ⟨d, List.mem_append_right _ (List.mem_filter.2 ⟨hd, by simp [hdk]⟩), hdx,
            hdy⟩
    · have := hsu a b; rwa [reachable_fromRel_iff] at this

end DCList

/-! ## Solid edges without `×`-dotted edge and `×`-dotted edges without solid edge -/

section Defects

variable {k n : ℕ}

/-- `d` joins the same two atoms as `c`. -/
def SamePairB (c d : Comp (Atom k n)) : Bool :=
  (d.x == c.x && d.y == c.y) || (d.x == c.y && d.y == c.x)

/-- Some `×`-dotted edge joins the two atoms of `c`. -/
def Graph.partB (g : Graph k n) (c : Comp (Atom k n)) : Bool :=
  g.comps.any fun d => d.kind == .xdot && SamePairB c d

/-- Some solid edge joins the two atoms of `c`. -/
def Graph.solidB (g : Graph k n) (c : Comp (Atom k n)) : Bool :=
  g.comps.any fun d => d.kind.isSolid && SamePairB c d

/-- The solid edges whose two atoms are joined by no `×`-dotted edge. -/
def Graph.unpart (g : Graph k n) : List (Comp (Atom k n)) :=
  g.comps.filter fun c => c.kind.isSolid && !g.partB c

/-- The `×`-dotted edges whose two atoms are joined by no solid edge. -/
def Graph.orph (g : Graph k n) : List (Comp (Atom k n)) :=
  g.comps.filter fun c => c.kind == .xdot && !g.solidB c

theorem samePairB_iff (c d : Comp (Atom k n)) :
    SamePairB c d = true ↔ (d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x) := by
  simp [SamePairB]

theorem Graph.partB_iff (g : Graph k n) (c : Comp (Atom k n)) :
    g.partB c = true ↔ ∃ d ∈ g.comps, d.kind = .xdot ∧
      ((d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x)) := by
  simp only [Graph.partB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, samePairB_iff]

theorem Graph.solidB_iff (g : Graph k n) (c : Comp (Atom k n)) :
    g.solidB c = true ↔ ∃ d ∈ g.comps, d.kind.isSolid = true ∧
      ((d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x)) := by
  simp only [Graph.solidB, List.any_eq_true, Bool.and_eq_true, samePairB_iff]

theorem Graph.mem_unpart {g : Graph k n} {c : Comp (Atom k n)} :
    c ∈ g.unpart ↔ c ∈ g.comps ∧ c.kind.isSolid = true ∧ g.partB c = false := by
  simp [Graph.unpart]

theorem Graph.mem_orph {g : Graph k n} {c : Comp (Atom k n)} :
    c ∈ g.orph ↔ c ∈ g.comps ∧ c.kind = .xdot ∧ g.solidB c = false := by
  simp [Graph.orph]

/-- A graph with all solid edges `×`-dotted and all `×`-dotted edges on solid edges is normal. -/
theorem Graph.normal_of {C : ℕ} {g : Graph k n} (hr : g.Regular C)
    (hl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y) (hu : g.unpart = [])
    (ho : g.orph = []) : g.Normal C := by
  refine ⟨hr, hl, fun u v _ => ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc, hk, hp⟩
    have hs : g.solidB c = true := by
      by_contra hne
      have : c ∈ g.orph := Graph.mem_orph.2 ⟨hc, hk, by simpa using hne⟩
      rw [ho] at this; simp at this
    obtain ⟨d, hd, hdk, hdp⟩ := (g.solidB_iff c).1 hs
    refine ⟨d, hd, hdk, ?_⟩
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdp with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp_all
  · rintro ⟨c, hc, hk, hp⟩
    have hs : g.partB c = true := by
      by_contra hne
      have : c ∈ g.unpart := Graph.mem_unpart.2 ⟨hc, hk, by simpa using hne⟩
      rw [hu] at this; simp at this
    obtain ⟨d, hd, hdk, hdp⟩ := (g.partB_iff c).1 hs
    refine ⟨d, hd, hdk, ?_⟩
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdp with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp_all

open Classical in
/-- The number of solid edges without `×`-dotted edge between the blocks of `u` and `v`. -/
def Graph.nBetween (g : Graph k n) (u v : Atom k n) : ℕ :=
  (g.unpart.filter fun c => (g.SameBlock c.x u ∧ g.SameBlock c.y v) ∨
    (g.SameBlock c.x v ∧ g.SameBlock c.y u)).length

/-- At most `b` solid edges without `×`-dotted edge join two given blocks. -/
def Graph.Beta (g : Graph k n) (b : ℕ) : Prop :=
  ∀ u v, ¬ g.SameBlock u v → g.nBetween u v ≤ b

/-- Every labelled component attached to the block of `a` is a solid edge between the blocks of
`a` and `b`. -/
def Graph.LabIn (g : Graph k n) (a b : Atom k n) : Prop :=
  ∀ c ∈ g.comps, c.label.isSome = true → (g.SameBlock c.x a ∨ g.SameBlock c.y a) →
    c.kind.isSolid = true ∧
      ((g.SameBlock c.x a ∧ g.SameBlock c.y b) ∨ (g.SameBlock c.x b ∧ g.SameBlock c.y a))

/-- Two blocks joined by two solid edges without `×`-dotted edge are not the block of `x`, or the
labelled components attached to the other block are these edges. -/
def Graph.HAvoid (g : Graph k n) (x : Atom k n) : Prop :=
  ∀ u v, ¬ g.SameBlock u v → 2 ≤ g.nBetween u v →
    (¬ g.SameBlock u x ∧ ¬ g.SameBlock v x) ∨ (g.SameBlock u x ∧ g.LabIn v u) ∨
      (g.SameBlock v x ∧ g.LabIn u v)

theorem Graph.LabIn.congr {g g' : Graph k n} {a b : Atom k n} (h : g.LabIn a b)
    (hlab : ∀ c, c.label.isSome = true → c ∈ g'.comps → c ∈ g.comps)
    (hbl : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) : g'.LabIn a b := by
  intro c hc hl hb
  simp only [hbl] at hb ⊢
  exact h c (hlab c hl hc) hl hb

theorem Graph.HAvoid.congr {g g' : Graph k n} {x : Atom k n} (h : g.HAvoid x)
    (hlab : ∀ c, c.label.isSome = true → c ∈ g'.comps → c ∈ g.comps)
    (hbl : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v)
    (hnb : ∀ u v, g'.nBetween u v ≤ g.nBetween u v) : g'.HAvoid x := by
  intro u v huv h2
  have huv' : ¬ g.SameBlock u v := fun h' => huv ((hbl u v).2 h')
  rcases h u v huv' (le_trans h2 (hnb u v)) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩
  · exact Or.inl ⟨by rw [hbl]; exact h1, by rw [hbl]; exact h1'⟩
  · exact Or.inr (Or.inl ⟨by rw [hbl]; exact h1, h1'.congr hlab hbl⟩)
  · exact Or.inr (Or.inr ⟨by rw [hbl]; exact h1, h1'.congr hlab hbl⟩)

open Classical in
/-- The weight of a labelled component at a set `B` of atoms: `4` for a light weight, `1` for a
regular weight, `1` for each end of a solid edge in `B`. -/
def wBP (B : Atom k n → Prop) (c : Comp (Atom k n)) : ℕ :=
  if c.label.isSome then
    match c.kind with
    | .light _ => if B c.x then 4 else 0
    | .weight _ => if B c.x then 1 else 0
    | .G _ => (if B c.x then 1 else 0) + (if B c.y then 1 else 0)
    | _ => 0
  else 0

/-- The weighted number of labelled weights and edge ends at the block of `x`. -/
def Graph.pw (g : Graph k n) (x : Atom k n) : ℕ :=
  (g.comps.map (wBP fun u => g.SameBlock u x)).sum

open Classical in
/-- The number of ends of labelled components in the block of `x` other than `x` itself. -/
def vP (x : Atom k n) (B : Atom k n → Prop) (c : Comp (Atom k n)) : ℕ :=
  if c.label.isSome then (if c.x ≠ x ∧ B c.x then 1 else 0) + (if c.y ≠ x ∧ B c.y then 1 else 0)
  else 0

/-- The number of ends of labelled components in the block of `x` other than `x`. -/
def Graph.viol (g : Graph k n) (x : Atom k n) : ℕ :=
  (g.comps.map (vP x fun u => g.SameBlock u x)).sum

/-- The intermediate graphs of the construction at the atom `x` (internal): regular with bound `C`
and connected without `×`-dotted edges, plain, every label `P_x`, no `×`-dotted edge inside a
block, at most one internal atom per block, no solid edge inside a block, and every solid edge
without `×`-dotted edge labelled and attached to an internal atom. -/
structure NN (C : ℕ) (x : Atom k n) (g : Graph k n) : Prop where
  hx : x.isRight = true
  reg : g.Regular C
  cnx : g.ConnNoX
  noLoop : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y
  plain : g.Plain
  lab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)
  xa : g.XdotApart
  ib : ∀ i j : Fin n, g.SameBlock (.inr i) (.inr j) → i = j
  inBlk : ∀ c ∈ g.comps, c.kind.isSolid = true → ¬ g.SameBlock c.x c.y
  unpLab : ∀ c ∈ g.unpart, c.label.isSome = true
  unpInt : ∀ c ∈ g.unpart, c.x.isRight = true ∨ c.y.isRight = true

/-- The labelled components attached to the block of `x` are attached at `x`. -/
def Graph.S6 (g : Graph k n) (x : Atom k n) : Prop :=
  ∀ c ∈ g.comps, c.label.isSome = true →
    (g.SameBlock c.x x → c.x = x) ∧ (g.SameBlock c.y x → c.y = x)

/-- The states of the construction: `NN` without solid edges without `×`-dotted edge or
`×`-dotted edges without solid edge, and with the labelled components at `x`. -/
structure St (C : ℕ) (x : Atom k n) (g : Graph k n) : Prop where
  nn : NN C x g
  unp : g.unpart = []
  orp : g.orph = []
  s6 : g.S6 x

theorem St.normal {C : ℕ} {x : Atom k n} {g : Graph k n} (h : St C x g) : g.Normal C :=
  Graph.normal_of h.nn.reg h.nn.noLoop h.unp h.orp

theorem ConnNoX.connected {g : Graph k n} (h : g.ConnNoX) : g.edgeGraph.Preconnected := by
  intro u v
  have := h u v
  refine SimpleGraph.Reachable.mono ?_ this
  intro a b hab
  rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hab
  rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
  rcases hab with ⟨hne, ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩⟩
  · exact ⟨hne, Or.inl ⟨c, hc, h1, h2⟩⟩
  · exact ⟨hne, Or.inr ⟨c, hc, h1, h2⟩⟩

end Defects

/-! ## Steps without identification -/

section SimpleSteps

variable {k n : ℕ}

theorem filter_length_lt_of {α : Type*} (L : List α) (p q : α → Bool)
    (hpq : ∀ a ∈ L, p a = true → q a = true) (h : ∃ a ∈ L, q a = true ∧ p a = false) :
    (L.filter p).length < (L.filter q).length := by
  induction L with
  | nil => obtain ⟨a, ha, -⟩ := h; simp at ha
  | cons b L ih =>
    have hpq' : ∀ a ∈ L, p a = true → q a = true := fun a ha => hpq a (List.mem_cons_of_mem _ ha)
    have hle : (L.filter p).length ≤ (L.filter q).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact List.countP_mono_left fun a ha hp => hpq' a ha hp
    obtain ⟨a, ha, hqa, hpa⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [List.filter_cons_of_neg (by simp [hpa]), List.filter_cons_of_pos hqa, List.length_cons]
      omega
    · have := ih hpq' ⟨a, ha, hqa, hpa⟩
      by_cases hpb : p b = true
      · rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos (hpq b (List.mem_cons_self ..) hpb)]
        simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg hpb]
        by_cases hqb : q b = true
        · rw [List.filter_cons_of_pos hqb]; simp only [List.length_cons]; omega
        · rw [List.filter_cons_of_neg hqb]; exact this

theorem filter_sublist_filter_of_mem {α : Type*} (L : List α) (p q : α → Bool)
    (hpq : ∀ a ∈ L, p a = true → q a = true) : (L.filter p).Sublist (L.filter q) := by
  induction L with
  | nil => exact List.Sublist.slnil
  | cons b L ih =>
    have ih' := ih fun a ha => hpq a (List.mem_cons_of_mem _ ha)
    by_cases hpb : p b = true
    · rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos (hpq b (List.mem_cons_self ..) hpb)]
      exact ih'.cons_cons b
    · rw [List.filter_cons_of_neg hpb]
      by_cases hqb : q b = true
      · rw [List.filter_cons_of_pos hqb]; exact ih'.cons b
      · rw [List.filter_cons_of_neg hqb]; exact ih'

theorem filter_length_le_of {α : Type*} (L : List α) (p q : α → Bool)
    (hpq : ∀ a ∈ L, p a = true → q a = true) : (L.filter p).length ≤ (L.filter q).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left fun a ha hp => hpq a ha hp

theorem Graph.sameBlock_iff_of_dots {g g' : Graph k n}
    (h : ∀ c, c.kind = .dot → (c ∈ g.comps ↔ c ∈ g'.comps)) (u v : Atom k n) :
    g.SameBlock u v ↔ g'.SameBlock u v := by
  constructor
  · exact Graph.sameBlock_mono fun c hc hk => (h c hk).1 hc
  · exact Graph.sameBlock_mono fun c hc hk => (h c hk).2 hc

theorem blockPred_congr {g g' : Graph k n} (x : Atom k n)
    (h : ∀ u v, g.SameBlock u v ↔ g'.SameBlock u v) :
    (fun u => g.SameBlock u x) = fun u => g'.SameBlock u x := by
  funext u
  exact propext (h u x)

theorem wBP_congr {m : ℕ} {B : Atom k n → Prop} {B' : Atom k m → Prop}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)}
    (hl : c'.label.isSome = c.label.isSome) (hk : c'.kind = c.kind) (hx : B' c'.x ↔ B c.x)
    (hy : B' c'.y ↔ B c.y) : wBP B' c' = wBP B c := by
  classical
  have e1 : (if B' c'.x then 1 else 0) = (if B c.x then 1 else 0) := by
    by_cases h1 : B c.x
    · rw [if_pos (hx.2 h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hx.1 h)), if_neg h1]
  have e4 : (if B' c'.x then 4 else 0) = (if B c.x then 4 else 0) := by
    by_cases h1 : B c.x
    · rw [if_pos (hx.2 h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hx.1 h)), if_neg h1]
  have e2 : (if B' c'.y then 1 else 0) = (if B c.y then 1 else 0) := by
    by_cases h1 : B c.y
    · rw [if_pos (hy.2 h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hy.1 h)), if_neg h1]
  unfold wBP
  rw [hl, hk]
  by_cases h0 : c.label.isSome = true
  · simp only [h0, ite_true]
    cases c.kind with
    | light ch => exact e4
    | weight ch => exact e1
    | G ch => simp only [e1, e2]
    | _ => rfl
  · simp only [h0]
    rfl

/-- An output of a step that keeps the atoms: the clauses `SR` from the components it keeps. -/
theorem SR.of_id {g g' : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    (hlr : g.LabRand)
    (henv : (g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).Subperm
      g'.comps)
    (hdots : ∀ c ∈ g.comps, c.kind = .dot → c ∈ g'.comps)
    (hGp : ∀ c ∈ g.comps, c.kind = .G .plus → c.x.isRight = true → c.y.isRight = true →
      c ∈ g'.comps)
    (hexc : excL g'.comps ≤ excL g.comps)
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n, g'⟩) :
    SR g x (Tracked.self g') := by
  have hmapid : ∀ L : List (Comp (Atom k n)), L.map (Comp.map id) = L := by
    intro L
    conv_rhs => rw [← List.map_id L]
    refine List.map_congr_left fun c _ => ?_
    rcases c with ⟨κ, a, b, mi, l⟩
    rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map]
  have hcar : (Tracked.self g').Carries g := by
    refine ⟨?_, fun u v huv => Graph.sameBlock_mono hdots huv⟩
    have : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
        c.kind ≠ .xdot)).map (Comp.map (id : Atom k n → Atom k n))).Subperm g'.comps := by
      rw [hmapid]; exact henv
    exact this
  have hmol : ∀ u v, g.SameMol u v → g'.SameMol u v := by
    rintro u v (rfl | ⟨hu, hv, hr⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨hu, hv, ?_⟩
      unfold Graph.molGraph at hr ⊢
      rw [reachable_fromRel_iff] at hr ⊢
      refine Relation.EqvGen.mono ?_ _ _ hr
      rintro a b ⟨c, hc, hj, rfl, rfl⟩
      refine ⟨c, ?_, hj, rfl, rfl⟩
      by_cases hd : c.kind = .dot
      · exact hdots c hc hd
      · have hl : c.label = none := by
          by_contra hne
          have := hlr c hc (Option.isSome_iff_ne_none.2 hne)
          rw [Kind.not_joinsMol_of_isRandom this] at hj; cases hj
        have hnx : c.kind ≠ .xdot := by intro h; rw [h] at hj; simp [Kind.joinsMol] at hj
        exact henv.subset (List.mem_filter.2 ⟨hc, by simp [hl, hd, hnx]⟩)
  have hcar' : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
      c.kind ≠ .xdot)).map (Comp.map (id : Atom k n → Atom k n))).Subperm g'.comps := by
    rw [hmapid]; exact henv
  refine ⟨hcar, ?_, hexc, hx, hch, fun u hu => absurd rfl (hu u)⟩
  intro hdc
  refine dc_transfer id hlr (fun i => ⟨i, rfl⟩) (fun u v _ _ h => hmol u v h)
    (fun j => ⟨j, Or.inl rfl⟩) hcar' ?_ hdc
  intro c hc hk a b a' b' hx' hy' ha hb
  simp only [id] at ha hb
  rw [Sum.inr.injEq] at ha hb
  subst ha hb
  exact Relation.EqvGen.rel _ _ (Or.inr ⟨c, hGp c hc hk (by rw [hx']; rfl) (by rw [hy']; rfl), hk,
    hx', hy'⟩)

/-- The `×`-dotted branch of `1 = 1_{u = v} + 1_{u ≠ v}` at the two atoms of a solid edge without
`×`-dotted edge. -/
theorem xdotBranch {C : ℕ} {x : Atom k n} {g : Graph k n} (hN : NN C x g)
    {c₀ : Comp (Atom k n)} (hc₀ : c₀ ∈ g.unpart) {u v : Atom k n}
    (huv : (u = c₀.x ∧ v = c₀.y) ∨ (u = c₀.y ∧ v = c₀.x)) :
    let g' : Graph k n := ⟨g.comps ++ [mkC .xdot u v], g.coeff⟩
    NN (C + 1) x g' ∧ g'.unpart.length < g.unpart.length ∧ g'.orph.length ≤ g.orph.length ∧
      (∀ b, g.Beta b → g'.Beta b) ∧ (g.HAvoid x → g'.HAvoid x) ∧ g'.pw x = g.pw x ∧
      g'.ord = g.ord ∧ excL g'.comps = excL g.comps ∧ (g.S6 x → g'.S6 x) ∧
      (∀ a b, g'.SameBlock a b ↔ g.SameBlock a b) := by
  intro g'
  obtain ⟨hc₀m, hc₀s, hc₀p⟩ := Graph.mem_unpart.1 hc₀
  have hdots : ∀ c, c.kind = .dot → (c ∈ g.comps ↔ c ∈ g'.comps) := by
    intro c hk
    simp only [g', List.mem_append, List.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · simp [mkC] at hk
  have hbl : ∀ a b, g'.SameBlock a b ↔ g.SameBlock a b :=
    fun a b => (Graph.sameBlock_iff_of_dots hdots a b).symm
  have hnb : ¬ g.SameBlock u v := by
    have := hN.inBlk c₀ hc₀m hc₀s
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · exact fun h => this (Graph.sameBlock_symm h)
  have hsolid : ∀ c, c.kind.isSolid = true → (c ∈ g'.comps ↔ c ∈ g.comps) := by
    intro c hk
    simp only [g', List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · simp [mkC, Kind.isSolid] at hk
    · exact Or.inl
  have hsolidB : ∀ c, g'.solidB c = g.solidB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.solidB_iff, Graph.solidB_iff]
    constructor
    · rintro ⟨d, hd, hdk, hdp⟩; exact ⟨d, (hsolid d hdk).1 hd, hdk, hdp⟩
    · rintro ⟨d, hd, hdk, hdp⟩; exact ⟨d, (hsolid d hdk).2 hd, hdk, hdp⟩
  have hpartB : ∀ c, g.partB c = true → g'.partB c = true := by
    intro c hc
    obtain ⟨d, hd, hdk, hdp⟩ := (g.partB_iff c).1 hc
    exact (g'.partB_iff c).2 ⟨d, List.mem_append_left _ hd, hdk, hdp⟩
  have hc₀p' : g'.partB c₀ = true := by
    refine (g'.partB_iff c₀).2 ⟨mkC .xdot u v, List.mem_append_right _ (List.mem_singleton_self _),
      rfl, ?_⟩
    simp only [mkC]
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hunp : ∀ c ∈ g'.unpart, c ∈ g.unpart := by
    intro c hc
    obtain ⟨hcm, hk, hp⟩ := Graph.mem_unpart.1 hc
    refine Graph.mem_unpart.2 ⟨(hsolid c hk).1 hcm, hk, ?_⟩
    by_contra hh
    rw [hpartB c (by simpa using hh)] at hp; cases hp
  have hunp_eq : g'.unpart = g.comps.filter fun c => c.kind.isSolid && !g'.partB c := by
    unfold Graph.unpart
    simp only [g']
    rw [List.filter_append, List.filter_cons_of_neg (by simp [mkC, Kind.isSolid]), List.filter_nil,
      List.append_nil]
  have hnbet : ∀ a c, g'.nBetween a c ≤ g.nBetween a c := by
    intro a c
    classical
    unfold Graph.nBetween
    refine List.Sublist.length_le ?_
    simp only [hbl]
    refine List.Sublist.filter _ ?_
    rw [hunp_eq]
    unfold Graph.unpart
    exact filter_sublist_filter_of_mem _ _ _ (fun c _ hc => by
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc ⊢
      refine ⟨hc.1, ?_⟩
      by_contra hh
      rw [hpartB c (by simpa using hh)] at hc; exact absurd hc.2 (by simp))
  refine ⟨⟨hN.hx, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hbl⟩
  · have := hN.reg.size; simp [g']; omega
  · intro a b
    have := hN.cnx a b
    refine ConnNoX.connected ?_ a b
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
    intro p q hpq
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inl ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
  · intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.reg.internal a b)
    intro p q hpq
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inl ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
  · intro c hc hk
    rcases List.mem_append.1 hc with hc | hc
    · exact hN.reg.noIntDot c hc hk
    · simp at hc; subst hc; simp [mkC] at hk
  · intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
    intro p q hpq
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inl ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, List.mem_append_left _ hc, hk, h1, h2⟩⟩
  · intro c hc hk
    exact hN.noLoop c ((hsolid c hk).1 hc) hk
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hN.plain c hc
    · simp at hc; subst hc
      refine ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC], ?_, by simp [mkC]⟩
      simp [mkC, Kind.isWeight]
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hN.lab c hc
    · simp at hc; subst hc; exact Or.inl rfl
  · intro c hc hk
    rw [hbl]
    rcases List.mem_append.1 hc with hc | hc
    · exact hN.xa c hc hk
    · simp at hc; subst hc; exact hnb
  · intro i j h; exact hN.ib i j ((hbl _ _).1 h)
  · intro c hc hk
    rw [hbl]; exact hN.inBlk c ((hsolid c hk).1 hc) hk
  · intro c hc; exact hN.unpLab c (hunp c hc)
  · intro c hc; exact hN.unpInt c (hunp c hc)
  · rw [hunp_eq]
    exact filter_length_lt_of _ _ _ (by
      intro c _ hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc ⊢
      refine ⟨hc.1, ?_⟩
      by_contra hh
      rw [hpartB c (by simpa using hh)] at hc; exact absurd hc.2 (by simp))
      ⟨c₀, hc₀m, by simp [hc₀s, hc₀p], by simp [hc₀p']⟩
  · have hsx : g'.solidB (mkC .xdot u v) = true := by
      refine (g'.solidB_iff _).2 ⟨c₀, List.mem_append_left _ hc₀m, hc₀s, ?_⟩
      simp only [mkC]
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    have hsx' : ({ comps := g.comps ++ [mkC .xdot u v], coeff := g.coeff } : Graph k n).solidB
        (mkC .xdot u v) = true := hsx
    unfold Graph.orph
    simp only [g']
    rw [List.filter_append, List.filter_cons_of_neg (by simp [hsx']), List.filter_nil,
      List.append_nil]
    apply le_of_eq
    congr 1
    apply List.filter_congr
    intro c _
    rw [hsolidB]
  · intro b hB a c hac
    exact le_trans (hnbet a c) (hB a c fun h => hac ((hbl a c).2 h))
  · intro hH
    refine hH.congr (fun c hl hc => ?_) hbl hnbet
    rcases List.mem_append.1 hc with hc | hc
    · exact hc
    · simp at hc; subst hc; simp [mkC] at hl
  · unfold Graph.pw
    rw [blockPred_congr x hbl]
    simp only [g', List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    simp [wBP, mkC]
  · simp [Graph.ord, g', mkC, Kind.ord]
  · simp only [g']
    rw [excL_perm List.perm_append_comm, List.singleton_append, excL_cons_ne (by simp [mkC])]
  · intro h6 c hc hl
    rw [hbl, hbl]
    rcases List.mem_append.1 hc with hc | hc
    · exact h6 c hc hl
    · simp at hc; subst hc; simp [mkC] at hl

theorem oSplitT_eq {g : Graph k n} {u v : Atom k n} (huv : u ≠ v) :
    oSplitT u v g = [Tracked.self ⟨g.comps ++ [mkC .dot u v], g.coeff⟩,
      Tracked.self ⟨g.comps ++ [mkC .xdot u v], g.coeff⟩] := by
  simp [oSplitT, huv]

theorem oXdotT_eq {g : Graph k n} {i : ℕ} {d : Comp (Atom k n)} (hd : g.comps[i]? = some d)
    (hk : d.kind = .xdot) (hl : d.label = none) (hs : g.solidB d = false) :
    oXdotT i g = [Tracked.self ⟨g.comps.eraseIdx i, g.coeff⟩,
      Tracked.self ⟨g.comps.eraseIdx i ++ [mkC .dot d.x d.y], -g.coeff⟩] := by
  unfold oXdotT
  rw [hd]
  simp only
  rw [ite_eq_left_of_eq_true]
  simp only [eq_iff_iff, iff_true]
  refine ⟨hk, hl, ?_⟩
  have : g.solidB d = (g.comps.any fun e => e.kind.isSolid &&
      ((e.x == d.x && e.y == d.y) || (e.x == d.y && e.y == d.x))) := rfl
  rw [← this, hs]

/-- Removal of a `×`-dotted edge without solid edge. -/
theorem xdotRemove {C : ℕ} {x : Atom k n} {g : Graph k n} (hN : NN C x g) {i : ℕ}
    {d : Comp (Atom k n)} (hd : g.comps[i]? = some d) (hdo : d ∈ g.orph) :
    let g' : Graph k n := ⟨g.comps.eraseIdx i, g.coeff⟩
    NN C x g' ∧ g'.unpart.length ≤ g.unpart.length ∧ g'.orph.length < g.orph.length ∧
      (∀ b, g.Beta b → g'.Beta b) ∧ (g.HAvoid x → g'.HAvoid x) ∧ g'.pw x = g.pw x ∧
      g'.ord = g.ord ∧ excL g'.comps = excL g.comps ∧ (g.S6 x → g'.S6 x) ∧
      (∀ a b, g'.SameBlock a b ↔ g.SameBlock a b) ∧ g'.comps.Sublist g.comps := by
  intro g'
  obtain ⟨hdm, hdk, hds⟩ := Graph.mem_orph.1 hdo
  have hp : g.comps.Perm (d :: g'.comps) := perm_cons_eraseIdx hd
  have hmem : ∀ c, c ∈ g.comps ↔ c = d ∨ c ∈ g'.comps := by
    intro c; rw [hp.mem_iff, List.mem_cons]
  have hne : ∀ c, c.kind ≠ .xdot → (c ∈ g'.comps ↔ c ∈ g.comps) := by
    intro c hc
    rw [hmem]
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · exact absurd hdk hc
      · exact h
  have hdots : ∀ c, c.kind = .dot → (c ∈ g.comps ↔ c ∈ g'.comps) :=
    fun c hk => (hne c (by rw [hk]; simp)).symm
  have hbl : ∀ a b, g'.SameBlock a b ↔ g.SameBlock a b :=
    fun a b => (Graph.sameBlock_iff_of_dots hdots a b).symm
  have hsub : ∀ c ∈ g'.comps, c ∈ g.comps := fun c hc => (hmem c).2 (Or.inr hc)
  have hsolidB : ∀ c, g'.solidB c = g.solidB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.solidB_iff, Graph.solidB_iff]
    constructor
    · rintro ⟨e, he, hek, hep⟩; exact ⟨e, hsub e he, hek, hep⟩
    · rintro ⟨e, he, hek, hep⟩
      refine ⟨e, (hne e ?_).2 he, hek, hep⟩
      intro h; rw [h] at hek; simp [Kind.isSolid] at hek
  have hpartB : ∀ c ∈ g.comps, c.kind.isSolid = true → g'.partB c = g.partB c := by
    intro c hcm hc
    rw [Bool.eq_iff_iff, Graph.partB_iff, Graph.partB_iff]
    constructor
    · rintro ⟨e, he, hek, hep⟩; exact ⟨e, hsub e he, hek, hep⟩
    · rintro ⟨e, he, hek, hep⟩
      rcases (hmem e).1 he with rfl | he'
      · exfalso
        have : g.solidB e = true := (g.solidB_iff e).2 ⟨c, hcm, hc, by
          rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h2.symm, h1.symm⟩⟩
        rw [hds] at this; cases this
      · exact ⟨e, he', hek, hep⟩
  have hsolid : ∀ c, c.kind.isSolid = true → (c ∈ g'.comps ↔ c ∈ g.comps) := by
    intro c hc; refine hne c ?_; intro h; rw [h] at hc; simp [Kind.isSolid] at hc
  have hunp : g'.unpart.Perm g.unpart := by
    have h1 := hp.filter (fun c => c.kind.isSolid && !g.partB c)
    rw [List.filter_cons_of_neg (by simp [hdk, Kind.isSolid])] at h1
    unfold Graph.unpart
    refine (List.Perm.of_eq ?_).trans h1.symm
    apply List.filter_congr
    intro c hc
    by_cases hcs : c.kind.isSolid = true
    · rw [hpartB c (hsub c hc) hcs]
    · simp [hcs]
  have horph : g.orph.Perm (d :: g'.orph) := by
    have h1 := hp.filter (fun c => c.kind == .xdot && !g.solidB c)
    rw [List.filter_cons_of_pos (by simp [hdk, hds])] at h1
    unfold Graph.orph
    refine h1.trans (List.Perm.of_eq ?_)
    congr 1
    apply List.filter_congr
    intro c _
    rw [hsolidB]
  have hnbet : ∀ a c, g'.nBetween a c = g.nBetween a c := by
    intro a c
    classical
    unfold Graph.nBetween
    simp only [hbl]
    exact (hunp.filter _).length_eq
  refine ⟨⟨hN.hx, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hbl, List.eraseIdx_sublist _ _⟩
  · have := hN.reg.size
    have h2 : g.comps.length = (g.comps.eraseIdx i).length + 1 := by simpa using hp.length_eq
    simp only [g']; omega
  · have hcx : g'.ConnNoX := by
      intro a b
      refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
      intro p q hpq
      rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
      rcases hpq with ⟨hne', ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
      · exact ⟨hne', Or.inl ⟨c, (hne c hk).2 hc, hk, h1, h2⟩⟩
      · exact ⟨hne', Or.inr ⟨c, (hne c hk).2 hc, hk, h1, h2⟩⟩
    exact ConnNoX.connected hcx
  · intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.reg.internal a b)
    intro p q hpq
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    have hk' : ∀ c : Comp (Atom k n), ((c.kind.joinsMol = true ∧ c.kind ≠ .dot) ∨
        c.kind.isDiffusive = true) → c.kind ≠ .xdot := by
      intro c h he; rw [he] at h; simp [Kind.joinsMol, Kind.isDiffusive] at h
    rcases hpq with ⟨hne', ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inl ⟨c, (hne c (hk' c hk)).2 hc, hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inr ⟨c, (hne c (hk' c hk)).2 hc, hk, h1, h2⟩⟩
  · intro c hc hk; exact hN.reg.noIntDot c (hsub c hc) hk
  · intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
    intro p q hpq
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne', ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inl ⟨c, (hne c hk).2 hc, hk, h1, h2⟩⟩
    · exact ⟨hne', Or.inr ⟨c, (hne c hk).2 hc, hk, h1, h2⟩⟩
  · intro c hc hk; exact hN.noLoop c (hsub c hc) hk
  · intro c hc; exact hN.plain c (hsub c hc)
  · intro c hc; exact hN.lab c (hsub c hc)
  · intro c hc hk; rw [hbl]; exact hN.xa c (hsub c hc) hk
  · intro i j h; exact hN.ib i j ((hbl _ _).1 h)
  · intro c hc hk; rw [hbl]; exact hN.inBlk c (hsub c hc) hk
  · intro c hc; exact hN.unpLab c (hunp.subset hc)
  · intro c hc; exact hN.unpInt c (hunp.subset hc)
  · exact le_of_eq hunp.length_eq
  · rw [horph.length_eq]; simp
  · intro b hB a c hac
    rw [hnbet]; exact hB a c fun h => hac ((hbl a c).2 h)
  · intro hH
    exact hH.congr (fun c _ hc => hsub c hc) hbl (fun a c => le_of_eq (hnbet a c))
  · unfold Graph.pw
    rw [blockPred_congr x hbl, (hp.map _).sum_eq]
    simp [wBP, hdk]
  · have := Graph.ord_perm (g := g) (g' := ⟨d :: g'.comps, g.coeff⟩) hp
    rw [this]; simp [Graph.ord, hdk, Kind.ord, g']
  · rw [excL_perm hp, excL_cons_ne (by rw [hdk]; simp)]
  · intro h6 c hc hl
    rw [hbl, hbl]; exact h6 c (hsub c hc) hl

end SimpleSteps

/-! ## Properties kept by `O_merge` -/

section MergeProps

variable {k n : ℕ} {h : Graph k n} {t : Tracked k n}

theorem PStepsMergeSpec.f_inr' (hs : PStepsMergeSpec h t) (i : Fin n) :
    ∃ j, t.f (.inr i) = .inr j := by
  obtain ⟨g, hg, -⟩ := hs.f_inr
  exact ⟨g i, hg i⟩

theorem PStepsMergeSpec.surj_inr (hs : PStepsMergeSpec h t) (j : Fin t.nOut) :
    ∃ i, t.f (.inr i) = .inr j := by
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  obtain ⟨i, rfl⟩ := hgs j
  exact ⟨i, hg i⟩

theorem PStepsMergeSpec.isRight_f (hs : PStepsMergeSpec h t) (u : Atom k n) :
    (t.f u).isRight = u.isRight := by
  rcases u with a | i
  · rw [hs.f_inl]; rfl
  · obtain ⟨j, hj⟩ := hs.f_inr' i; rw [hj]; rfl

theorem mergeComp_x {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : psteps_mergeComp rep f c = some c') :
    c'.x = f c.x ∧ c'.minor = c.minor.map f := by
  unfold psteps_mergeComp at h
  split_ifs at h
  · obtain rfl := Option.some.inj h; exact ⟨rfl, rfl⟩
  · obtain rfl := Option.some.inj h; exact ⟨rfl, rfl⟩

theorem mergeComp_y {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : psteps_mergeComp rep f c = some c') :
    (c'.y = f c.y ∧ c'.kind = c.kind) ∨
      (c.kind.isSolid = true ∧ rep c.x = rep c.y ∧ c'.y = f c.x ∧ c'.kind = c.kind.toWeight) := by
  unfold psteps_mergeComp at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Or.inr ⟨h2.1, h2.2, rfl, rfl⟩
  · obtain rfl := Option.some.inj h; exact Or.inl ⟨rfl, rfl⟩

/-- `O_merge` keeps plain graphs plain. -/
theorem PStepsMergeSpec.plain (hs : PStepsMergeSpec h t) (hp : h.Plain) : t.g.Plain := by
  intro c' hc'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp c hc
  obtain ⟨hx, hmi⟩ := mergeComp_x hm
  have hl := mergeComp_label hm
  refine ⟨by rw [hmi, h1]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch hk
    rcases mergeComp_y hm with ⟨-, hk'⟩ | ⟨hs', -, -, hk'⟩
    · rw [hk'] at hk; exact h2 ch hk
    · obtain ⟨ch', hch⟩ := Kind.isSolid_iff.1 hs'
      rw [hk', hch] at hk; simp [Kind.toWeight] at hk
  · intro ch d hk
    rcases mergeComp_y hm with ⟨-, hk'⟩ | ⟨hs', -, -, hk'⟩
    · rw [hk'] at hk; exact h3 ch d hk
    · obtain ⟨ch', hch⟩ := Kind.isSolid_iff.1 hs'
      rw [hk', hch] at hk; simp [Kind.toWeight] at hk
  · intro hk
    have := (psteps_mergeComp_kind hm)
    rcases this with hk' | ⟨ch, hch, hch'⟩
    · have hd : c.kind = .dot := hk' ▸ hk
      rw [psteps_mergeComp_dot hd] at hm
      split_ifs at hm with hf
      obtain rfl := Option.some.inj hm
      exact hf
    · rw [hch'] at hk; cases hk
  · intro hw
    rcases mergeComp_y hm with ⟨hy, hk'⟩ | ⟨-, -, hy, -⟩
    · rw [hk'] at hw; rw [hy, hx, h5 hw]
    · rw [hy, hx]
  · intro hls
    rw [hl] at hls
    have := h6 (by simpa using hls)
    rcases mergeComp_y hm with ⟨-, hk'⟩ | ⟨hs', -, -, hk'⟩
    · rw [hk']; exact this
    · obtain ⟨ch', hch⟩ := Kind.isSolid_iff.1 hs'
      rw [hk', hch]; rfl

/-- In the output of `O_merge`, every dotted edge has an external end. -/
theorem PStepsMergeSpec.noIntDot (hs : PStepsMergeSpec h t) :
    ∀ c' ∈ t.g.comps, c'.kind = .dot → c'.x.isLeft = true ∨ c'.y.isLeft = true := by
  intro c' hc' hk
  obtain ⟨c, hc, hck, hf, rfl⟩ := hs.dot_image hc' hk
  by_contra hcon
  push Not at hcon
  have h1 : (t.f c.x).isRight = true := by simpa [Comp.map] using hcon.1
  have h2 : (t.f c.y).isRight = true := by simpa [Comp.map] using hcon.2
  rw [hs.isRight_f] at h1 h2
  exact hf (hs.f_eq _ _ (h.mrep_dot hc hck) h1 h2)

/-- In the output of `O_merge`, two internal atoms in one block are equal. -/
theorem PStepsMergeSpec.ib (hs : PStepsMergeSpec h t) :
    ∀ i j : Fin t.nOut, t.g.SameBlock (.inr i) (.inr j) → i = j := by
  intro i j hij
  obtain ⟨a, ha⟩ := hs.surj_inr i
  obtain ⟨b, hb⟩ := hs.surj_inr j
  rw [← ha, ← hb, hs.sameBlock_iff, Graph.sameBlock_iff_mrep] at hij
  have := hs.f_eq _ _ hij rfl rfl
  rw [ha, hb] at this
  exact Sum.inr.inj this

/-- In the output of `O_merge`, no solid edge lies inside a block. -/
theorem PStepsMergeSpec.inBlk (hs : PStepsMergeSpec h t) :
    ∀ c' ∈ t.g.comps, c'.kind.isSolid = true → ¬ t.g.SameBlock c'.x c'.y := by
  intro c' hc' hk hb
  obtain ⟨c, hc, -, hr, rfl⟩ := hs.of_mem_solid hc' hk
  exact hr ((Graph.sameBlock_iff_mrep _ _ _).1 ((hs.sameBlock_iff _ _).1 hb))

theorem PStepsMergeSpec.labels (hs : PStepsMergeSpec h t) {x : Atom k n}
    (hl : ∀ c ∈ h.comps, c.label = none ∨ c.label = some (.P, x)) :
    ∀ c' ∈ t.g.comps, c'.label = none ∨ c'.label = some (.P, t.f x) := by
  intro c' hc'
  obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 hc'
  rw [mergeComp_label hm]
  rcases hl c hc with h | h <;> simp [h]

theorem dotRel_le_noX {k n : ℕ} (g : Graph k n) (a b : Atom k n)
    (h : Relation.EqvGen (dotRel g.comps) a b) :
    Relation.EqvGen (fun u v => ∃ c ∈ g.comps, c.kind ≠ .xdot ∧ c.x = u ∧ c.y = v) a b := by
  refine Relation.EqvGen.mono ?_ _ _ h
  rintro u v ⟨c, hc, hk, rfl, rfl⟩
  exact ⟨c, hc, by rw [hk]; simp, rfl, rfl⟩

/-- `O_merge` keeps the graph connected without its `×`-dotted edges. -/
theorem PStepsMergeSpec.connNoX (hs : PStepsMergeSpec h t) (hc : h.ConnNoX) : t.g.ConnNoX := by
  have key : ∀ a b, h.edgeGraphNoX.Reachable a b → t.g.edgeGraphNoX.Reachable (t.f a) (t.f b) := by
    intro a b hab
    unfold Graph.edgeGraphNoX at hab ⊢
    rw [reachable_fromRel_iff] at hab ⊢
    induction hab with
    | rel a b hr =>
      obtain ⟨c, hcm, hk, rfl, rfl⟩ := hr
      by_cases hb : h.SameBlock c.x c.y
      · have := (hs.sameBlock_iff c.x c.y).2 hb
        rw [Graph.sameBlock_iff_eqvGen] at this
        exact dotRel_le_noX _ _ _ this
      · have hnd : c.kind ≠ .dot := fun hd => hb (Graph.sameBlock_of_dot hcm hd)
        have hm : psteps_mergeComp h.psteps_mrep t.f c = some (c.map t.f) := by
          by_cases hsol : c.kind.isSolid = true
          · exact mergeComp_of_solid hsol (fun hr => hb ((Graph.sameBlock_iff_mrep _ _ _).2 hr))
          · exact mergeComp_of_not_solid (by simpa using hsol) (fun h' => hnd h'.1)
        exact Relation.EqvGen.rel _ _ ⟨c.map t.f, hs.mem_comps.2 ⟨c, hcm, hm⟩, hk, rfl, rfl⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  intro p q
  obtain ⟨a, rfl⟩ := hs.f_surj p
  obtain ⟨b, rfl⟩ := hs.f_surj q
  exact key a b (hc a b)

/-- `O_merge` keeps internal atoms joined by waved and diffusive edges. -/
theorem PStepsMergeSpec.internal (hs : PStepsMergeSpec h t)
    (hi : ∀ a b : Fin n, h.wavedThetaGraph.Reachable (.inr a) (.inr b)) :
    ∀ a b : Fin t.nOut, t.g.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
  have key : ∀ a b, h.wavedThetaGraph.Reachable a b →
      t.g.wavedThetaGraph.Reachable (t.f a) (t.f b) := by
    intro a b hab
    unfold Graph.wavedThetaGraph at hab ⊢
    rw [reachable_fromRel_iff] at hab ⊢
    induction hab with
    | rel a b hr =>
      obtain ⟨c, hcm, hk, rfl, rfl⟩ := hr
      have hnd : c.kind ≠ .dot := by
        rintro hd; rw [hd] at hk; simp [Kind.isDiffusive] at hk
      have hns : c.kind.isSolid = false := by
        rcases hk with ⟨hj, -⟩ | hj <;>
        · cases hkk : c.kind <;> simp_all [Kind.isSolid, Kind.joinsMol, Kind.isDiffusive]
      exact Relation.EqvGen.rel _ _ ⟨c.map t.f, hs.mem_of_other hcm hnd hns, hk, rfl, rfl⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  intro a b
  obtain ⟨i, hi'⟩ := hs.surj_inr a
  obtain ⟨j, hj'⟩ := hs.surj_inr b
  rw [← hi', ← hj']
  exact key _ _ (hi i j)

/-- The unlabelled components other than dotted, `×`-dotted and solid edges between two atoms of
one block are mapped by `O_merge`. -/
theorem PStepsMergeSpec.carries_sub (hs : PStepsMergeSpec h t)
    (hsol : ∀ c ∈ h.comps, c.label = none → c.kind.isSolid = true → ¬ h.SameBlock c.x c.y) :
    ((h.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).map
      (Comp.map t.f)).Sublist t.g.comps := by
  rw [hs.comps_eq]
  have key : ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, c ∈ h.comps) →
      ((L.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).map
        (Comp.map t.f)).Sublist (L.filterMap (psteps_mergeComp h.psteps_mrep t.f)) := by
    intro L hL
    induction L with
    | nil => exact List.Sublist.slnil
    | cons c L ih =>
      have ih' := ih fun d hd => hL d (List.mem_cons_of_mem _ hd)
      rw [List.filterMap_cons]
      by_cases hp : (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)
      · rw [List.filter_cons_of_pos (by simpa using hp), List.map_cons]
        have hm : psteps_mergeComp h.psteps_mrep t.f c = some (c.map t.f) := by
          by_cases hs' : c.kind.isSolid = true
          · exact mergeComp_of_solid hs' (fun hr => hsol c (hL c (List.mem_cons_self ..)) hp.1 hs'
              ((Graph.sameBlock_iff_mrep _ _ _).2 hr))
          · exact mergeComp_of_not_solid (by simpa using hs') (fun h' => hp.2.1 h'.1)
        rw [hm]
        exact ih'.cons_cons _
      · rw [List.filter_cons_of_neg (by simpa using hp)]
        cases psteps_mergeComp h.psteps_mrep t.f c with
        | none => exact ih'
        | some c' => exact ih'.cons _
  exact key h.comps fun c hc => hc

end MergeProps

/-! ## Graphs that differ by redundant dotted edges -/

section Agree

variable {k n : ℕ}

/-- `g'` has the components of `g` other than dotted edges (with multiplicity), some of its dotted
edges, and the same blocks. -/
structure Agree (g' g : Graph k n) : Prop where
  nd : (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
    (g.comps.filter fun c => decide (c.kind ≠ .dot))
  dots : ∀ c ∈ g'.comps, c ∈ g.comps
  blk : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v

theorem Agree.mem_nd {g' g : Graph k n} (h : Agree g' g) {c : Comp (Atom k n)}
    (hc : c.kind ≠ .dot) : c ∈ g'.comps ↔ c ∈ g.comps := by
  constructor
  · exact h.dots c
  · intro hm
    have : c ∈ g.comps.filter fun c => decide (c.kind ≠ .dot) := List.mem_filter.2 ⟨hm, by simpa⟩
    exact (List.mem_filter.1 (h.nd.mem_iff.2 this)).1

theorem filter_nd_eq {L : List (Comp (Atom k n))} (p : Comp (Atom k n) → Bool)
    (hp : ∀ c, p c = true → c.kind ≠ .dot) :
    L.filter p = (L.filter fun c => decide (c.kind ≠ .dot)).filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  by_cases h : p c = true
  · simp [h, hp c h]
  · simp at h; simp [h]

theorem Agree.partB {g' g : Graph k n} (h : Agree g' g) (c : Comp (Atom k n)) :
    g'.partB c = g.partB c := by
  rw [Bool.eq_iff_iff, Graph.partB_iff, Graph.partB_iff]
  constructor
  · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, h.dots d hd, hk, hp⟩
  · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (h.mem_nd (by rw [hk]; simp)).2 hd, hk, hp⟩

theorem Agree.solidB {g' g : Graph k n} (h : Agree g' g) (c : Comp (Atom k n)) :
    g'.solidB c = g.solidB c := by
  rw [Bool.eq_iff_iff, Graph.solidB_iff, Graph.solidB_iff]
  have hnd : ∀ d : Comp (Atom k n), d.kind.isSolid = true → d.kind ≠ .dot := by
    intro d hd h'; rw [h'] at hd; simp [Kind.isSolid] at hd
  constructor
  · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, h.dots d hd, hk, hp⟩
  · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (h.mem_nd (hnd d hk)).2 hd, hk, hp⟩

theorem Agree.unpart {g' g : Graph k n} (h : Agree g' g) : g'.unpart.Perm g.unpart := by
  unfold Graph.unpart
  have hp : ∀ c, (c.kind.isSolid && !g'.partB c) = true → c.kind ≠ .dot := by
    intro c hc h'; simp [h', Kind.isSolid] at hc
  have hp' : ∀ c, (c.kind.isSolid && !g.partB c) = true → c.kind ≠ .dot := by
    intro c hc h'; simp [h', Kind.isSolid] at hc
  rw [filter_nd_eq _ hp, filter_nd_eq _ hp']
  have : (fun c => c.kind.isSolid && !g'.partB c) = fun c => c.kind.isSolid && !g.partB c := by
    funext c; rw [h.partB]
  rw [this]
  exact h.nd.filter _

theorem Agree.orph {g' g : Graph k n} (h : Agree g' g) : g'.orph.Perm g.orph := by
  unfold Graph.orph
  have hp : ∀ c, (c.kind == .xdot && !g'.solidB c) = true → c.kind ≠ .dot := by
    intro c hc h'; simp [h'] at hc
  have hp' : ∀ c, (c.kind == .xdot && !g.solidB c) = true → c.kind ≠ .dot := by
    intro c hc h'; simp [h'] at hc
  rw [filter_nd_eq _ hp, filter_nd_eq _ hp']
  have : (fun c => c.kind == .xdot && !g'.solidB c) = fun c => c.kind == .xdot && !g.solidB c := by
    funext c; rw [h.solidB]
  rw [this]
  exact h.nd.filter _

theorem Agree.pw {g' g : Graph k n} (h : Agree g' g) (x : Atom k n) :
    g'.pw x = g.pw x := by
  unfold Graph.pw
  rw [blockPred_congr x h.blk]
  have hw : ∀ c : Comp (Atom k n), c.kind = .dot → wBP (fun u => g.SameBlock u x) c = 0 := by
    intro c hc; simp [wBP, hc]
  have key : ∀ L : List (Comp (Atom k n)), (L.map (wBP fun u => g.SameBlock u x)).sum =
      ((L.filter fun c => decide (c.kind ≠ .dot)).map (wBP fun u => g.SameBlock u x)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons c L ih =>
      by_cases hc : c.kind = .dot
      · rw [List.filter_cons_of_neg (by simpa using hc)]
        simp [ih, hw c hc]
      · rw [List.filter_cons_of_pos (by simpa using hc)]
        simp [ih]
  rw [key, key g.comps, (h.nd.map _).sum_eq]

theorem Agree.of_cleanup {g' g : Graph k n} (hsub : g'.comps.Sublist g.comps)
    (hnd : (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
      (g.comps.filter fun c => decide (c.kind ≠ .dot)))
    (hbl : ∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) : Agree g' g :=
  ⟨hnd, fun c hc => hsub.subset hc, hbl⟩

/-- Graphs that agree in this sense satisfy the clauses `NN` together. -/
theorem Agree.nn {C : ℕ} {x : Atom k n} {g' g : Graph k n} (h : Agree g' g)
    (hlen : g'.comps.length ≤ g.comps.length)
    (hx : x.isRight = true) (hr : g.Regular C) (hcx : g.ConnNoX)
    (hl : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y) (hp : g.Plain)
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hxa : g.XdotApart)
    (hib : ∀ i j : Fin n, g.SameBlock (.inr i) (.inr j) → i = j)
    (hin : ∀ c ∈ g.comps, c.kind.isSolid = true → ¬ g.SameBlock c.x c.y)
    (hul : ∀ c ∈ g.unpart, c.label.isSome = true)
    (hui : ∀ c ∈ g.unpart, c.x.isRight = true ∨ c.y.isRight = true) : NN C x g' := by
  have hnd : ∀ c : Comp (Atom k n), c.kind.isSolid = true → c.kind ≠ .dot := by
    intro d hd h'; rw [h'] at hd; simp [Kind.isSolid] at hd
  have hcx' : g'.ConnNoX := by
    intro a b
    have hab := hcx a b
    unfold Graph.edgeGraphNoX at hab ⊢
    rw [reachable_fromRel_iff] at hab ⊢
    induction hab with
    | rel a b hr' =>
      obtain ⟨c, hcm, hk, rfl, rfl⟩ := hr'
      by_cases hd : c.kind = .dot
      · have hb := (h.blk c.x c.y).2 (Graph.sameBlock_of_dot hcm hd)
        rw [Graph.sameBlock_iff_eqvGen] at hb
        exact dotRel_le_noX _ _ _ hb
      · exact Relation.EqvGen.rel _ _ ⟨c, (h.mem_nd hd).2 hcm, hk, rfl, rfl⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  refine ⟨hx, ⟨by have := hr.size; omega, ConnNoX.connected hcx', ?_, ?_⟩, hcx', ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro a b
    refine SimpleGraph.Reachable.mono ?_ (hr.internal a b)
    intro p q hpq
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    have hk' : ∀ c : Comp (Atom k n), ((c.kind.joinsMol = true ∧ c.kind ≠ .dot) ∨
        c.kind.isDiffusive = true) → c.kind ≠ .dot := by
      intro c hc he; rw [he] at hc; simp [Kind.joinsMol, Kind.isDiffusive] at hc
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inl ⟨c, (h.mem_nd (hk' c hk)).2 hc, hk, h1, h2⟩⟩
    · exact ⟨hne, Or.inr ⟨c, (h.mem_nd (hk' c hk)).2 hc, hk, h1, h2⟩⟩
  · intro c hc hk; exact hr.noIntDot c (h.dots c hc) hk
  · intro c hc hk; exact hl c (h.dots c hc) hk
  · intro c hc; exact hp c (h.dots c hc)
  · intro c hc; exact hlab c (h.dots c hc)
  · intro c hc hk; rw [h.blk]; exact hxa c (h.dots c hc) hk
  · intro i j hij; exact hib i j ((h.blk _ _).1 hij)
  · intro c hc hk; rw [h.blk]; exact hin c (h.dots c hc) hk
  · intro c hc; exact hul c (h.unpart.subset hc)
  · intro c hc; exact hui c (h.unpart.subset hc)

end Agree

/-! ## Facts for the identification of two blocks -/

section IdentifyAux

variable {k n : ℕ}

theorem dotRel_append_dot (L : List (Comp (Atom k n))) (u v a b : Atom k n) :
    dotRel (L ++ [mkC .dot u v]) a b ↔ dotRel L a b ∨ (a = u ∧ b = v) := by
  rw [dotRel_perm List.perm_append_comm, List.singleton_append]
  exact dotRel_cons_of_dot rfl L a b

theorem sameBlock_append_dot (g : Graph k n) (u v : Atom k n) (co : Coeff) (a b : Atom k n) :
    (⟨g.comps ++ [mkC .dot u v], co⟩ : Graph k n).SameBlock a b ↔ g.SameBlock a b ∨
      (g.SameBlock a u ∧ g.SameBlock v b) ∨ (g.SameBlock a v ∧ g.SameBlock u b) := by
  rw [Graph.sameBlock_iff_eqvGen, Graph.sameBlock_iff_eqvGen, Graph.sameBlock_iff_eqvGen,
    Graph.sameBlock_iff_eqvGen, Graph.sameBlock_iff_eqvGen, Graph.sameBlock_iff_eqvGen]
  exact eqvGen_add_iff (dotRel_append_dot g.comps u v) a b

theorem labels_le_one (g : Graph k n) (ℓ : PQ × Atom k n)
    (h : ∀ c ∈ g.comps, c.label = none ∨ c.label = some ℓ) : g.labels.length ≤ 1 := by
  unfold Graph.labels
  have hsub : ∀ m ∈ (g.comps.filterMap Comp.label).dedup, m = ℓ := by
    intro m hm
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 (List.mem_dedup.1 hm)
    rcases h c hc with h' | h'
    · rw [h'] at hcl; cases hcl
    · rw [h'] at hcl; exact (Option.some.inj hcl).symm
  have hnd := List.nodup_dedup (g.comps.filterMap Comp.label)
  generalize (g.comps.filterMap Comp.label).dedup = l at hsub hnd
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp
  · simp
  · exfalso
    have ha := hsub a (by simp)
    have hb := hsub b (by simp)
    rw [List.nodup_cons] at hnd
    exact hnd.1 (by rw [ha, ← hb]; simp)

/-- Counting the images of `filterMap`: every component contributes to at most one side. -/
theorem count_filterMap {α β : Type*} (L : List α) (φ : α → Option β) (P : β → Bool)
    (Q R : α → Bool)
    (h1 : ∀ c ∈ L, ∀ c', φ c = some c' → P c' = true → Q c = true ∧ R c = false)
    (h2 : ∀ c ∈ L, R c = true → Q c = true) :
    ((L.filterMap φ).filter P).length + (L.filter R).length ≤ (L.filter Q).length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih (fun d hd => h1 d (List.mem_cons_of_mem _ hd))
      (fun d hd => h2 d (List.mem_cons_of_mem _ hd))
    rw [List.filterMap_cons]
    have hc1 := h1 c (List.mem_cons_self ..)
    have hc2 := h2 c (List.mem_cons_self ..)
    rcases hφ : φ c with _ | c'
    · simp only
      by_cases hR : R c = true
      · rw [List.filter_cons_of_pos hR, List.filter_cons_of_pos (hc2 hR)]
        simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg hR]
        by_cases hQ : Q c = true
        · rw [List.filter_cons_of_pos hQ]; simp only [List.length_cons]; omega
        · rw [List.filter_cons_of_neg hQ]; exact ih'
    · simp only
      by_cases hP : P c' = true
      · obtain ⟨hQ, hR⟩ := hc1 c' hφ hP
        rw [List.filter_cons_of_pos hP, List.filter_cons_of_neg (by simp [hR]),
          List.filter_cons_of_pos hQ]
        simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg hP]
        by_cases hR : R c = true
        · rw [List.filter_cons_of_pos hR, List.filter_cons_of_pos (hc2 hR)]
          simp only [List.length_cons]; omega
        · rw [List.filter_cons_of_neg hR]
          by_cases hQ : Q c = true
          · rw [List.filter_cons_of_pos hQ]; simp only [List.length_cons]; omega
          · rw [List.filter_cons_of_neg hQ]; exact ih'

/-- Sums over the images of `filterMap`. -/
theorem sum_filterMap {α β : Type*} (L : List α) (φ : α → Option β) (w : α → ℕ)
    (w' : β → ℕ) (e : α → ℕ) (h : ∀ c ∈ L, (φ c).elim 0 w' + e c = w c) :
    ((L.filterMap φ).map w').sum + (L.map e).sum = (L.map w).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c (List.mem_cons_self ..)
    rw [List.filterMap_cons]
    rcases hφ : φ c with _ | c'
    · rw [hφ] at hc; simp only [Option.elim_none, zero_add] at hc
      simp only [List.map_cons, List.sum_cons]; omega
    · rw [hφ] at hc; simp only [Option.elim_some] at hc
      simp only [List.map_cons, List.sum_cons]; omega

end IdentifyAux

/-! ## Identifying two blocks -/

section Identify

variable {k n : ℕ}

/-- The output of identifying the blocks of `u` and `v` (a dotted edge `u – v` added to `g`,
followed by `O_merge` and the removal of redundant dotted edges). -/
structure IdOut (C : ℕ) (x : Atom k n) (g : Graph k n) (u v : Atom k n) (co : Coeff)
    (t : Tracked k n) : Prop where
  chain : Relation.ReflTransGen QElemStep ⟨n, ⟨g.comps ++ [mkC .dot u v], co⟩⟩ ⟨t.nOut, t.g⟩
  nn : NN (C + 1) (t.f x) t.g
  unp : t.g.unpart.length + g.nBetween u v ≤ g.unpart.length
  orp : t.g.orph.length ≤ g.orph.length
  ord : t.g.ord + g.nBetween u v = g.ord + 2
  exc : excL t.g.comps = excL g.comps
  coeff : t.g.coeff = co
  carries : t.Carries g
  dc : g.DoublyConnected → t.g.DoublyConnected
  surj : ∀ w, ∃ a, t.f a = w
  val : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι), t.g.valR PF D e = (⟨g.comps ++ [mkC .dot u v], co⟩ : Graph k n).valR PF D e
  pwHAv : (¬ g.SameBlock u x ∧ ¬ g.SameBlock v x) ∨ (g.SameBlock u x ∧ g.LabIn v u) ∨
    (g.SameBlock v x ∧ g.LabIn u v) → t.g.pw (t.f x) = g.pw x
  blk : ∀ a b, t.g.SameBlock (t.f a) (t.f b) ↔
    (⟨g.comps ++ [mkC .dot u v], co⟩ : Graph k n).SameBlock a b
  size : t.g.comps.length ≤ g.comps.length + 1

end Identify

/-! ## Making a graph normal -/

section Normalize

variable {k : ℕ}

theorem NN.mono {n C C' : ℕ} {x : Atom k n} {g : Graph k n} (h : NN C x g)
    (hC : C ≤ C') : NN C' x g :=
  { h with reg := ⟨h.reg.size.trans hC, h.reg.connected, h.reg.internal, h.reg.noIntDot⟩ }

theorem Tracked.Carries.self_trans {n : ℕ} {g g' : Graph k n} {t : Tracked k n}
    (h1 : (Tracked.self g').Carries g) (h2 : t.Carries g') : t.Carries g := by
  have h2' : t.Carries (Tracked.self g').g := h2
  have := h1.trans h2'
  rcases t with ⟨m, gt, ft⟩
  exact this

theorem SR.self_comp {n : ℕ} {g g' : Graph k n} {x : Atom k n}
    (h1 : SR g x (Tracked.self g')) (hp : g'.LabRand) {t : Tracked k n} (h2 : SR g' x t) :
    SR g x t := by
  have h2' : SR (Tracked.self g').g ((Tracked.self g').f x) t := h2
  have := SR.trans h1 hp h2'
  rcases t with ⟨m, gt, ft⟩
  exact this

end Normalize

/-! ## Moving the labelled components of the block of `x` to `x` -/

section RebaseValue

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)

/-- Replacing one component by another with the same label and the same factor keeps the term. -/
theorem termR_cons_congr (c c' : Comp (Atom k n)) (L : List (Comp (Atom k n))) (co : Coeff)
    (σ : Atom k n → ι) (ω : Ω) (hl : c'.label = c.label)
    (hv : ∀ D₀ : Data ι, Comp.val D₀ σ c' = Comp.val D₀ σ c) :
    Graph.termR (⟨c' :: L, co⟩ : Graph k n) PF D σ ω =
      Graph.termR (⟨c :: L, co⟩ : Graph k n) PF D σ ω := by
  simp only [Graph.termR, Graph.labels, List.filterMap_cons, hl, List.filter_cons]
  simp only [apply_ite (List.map _), List.map_cons, apply_ite List.prod, List.prod_cons, hv]

/-- Moving an end `u` of a component other than a dotted edge to an atom `v` of its block keeps the
value. -/
theorem valR_rebase (g : Graph k n) {i : ℕ} {c : Comp (Atom k n)} (hc : g.comps[i]? = some c)
    (hk : c.kind ≠ .dot) {u v : Atom k n} (huv : g.SameBlock u v)
    (hlab : ∀ d ∈ g.comps, d.kind = .dot → d.label = none) (e : Fin k → ι) :
    (⟨g.comps.set i { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y },
      g.coeff⟩ : Graph k n).valR PF D e = g.valR PF D e := by
  set c' : Comp (Atom k n) :=
    { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }
  have hp : g.comps.Perm (c :: g.comps.eraseIdx i) := perm_cons_eraseIdx hc
  have hi : i < g.comps.length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hc
    cases hc
  have hp' : (g.comps.set i c').Perm (c' :: g.comps.eraseIdx i) := by
    have h1 : (g.comps.set i c')[i]? = some c' := by simp [hi]
    have := perm_cons_eraseIdx h1
    rwa [List.eraseIdx_set_eq] at this
  funext ω
  unfold Graph.valR
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [termR_perm' PF D hp' g.coeff, termR_perm' PF D hp g.coeff]
  by_cases hz : ∀ d ∈ g.comps, d.kind = .dot → Sum.elim e s d.x = Sum.elim e s d.y
  · have hσ := Graph.sigma_eq_of_sameBlock (Sum.elim e s) hz huv
    refine termR_cons_congr PF D c c' _ _ _ ω rfl fun D₀ => ?_
    simp only [c', Comp.val]
    have h1 : Sum.elim e s (if c.x = u then v else c.x) = Sum.elim e s c.x := by
      split_ifs with h
      · rw [h, hσ]
      · rfl
    have h2 : Sum.elim e s (if c.y = u then v else c.y) = Sum.elim e s c.y := by
      split_ifs with h
      · rw [h, hσ]
      · rfl
    rw [h1, h2]
  · have hz' : ¬ ∀ d ∈ (⟨c :: g.comps.eraseIdx i, g.coeff⟩ : Graph k n).comps, d.kind = .dot →
        Sum.elim e s d.x = Sum.elim e s d.y := fun h => hz fun d hd hdk => h d (hp.subset hd) hdk
    have hz'' : ¬ ∀ d ∈ (⟨c' :: g.comps.eraseIdx i, g.coeff⟩ : Graph k n).comps, d.kind = .dot →
        Sum.elim e s d.x = Sum.elim e s d.y := by
      intro h
      apply hz'
      intro d hd hdk
      rcases List.mem_cons.1 hd with rfl | hd
      · exact absurd hdk hk
      · exact h d (List.mem_cons_of_mem _ hd) hdk
    rw [termR_eq_zero_of_dot PF D _ _ ω (fun d hd hdk => by
        rcases List.mem_cons.1 hd with rfl | hd
        · exact absurd hdk hk
        · exact hlab d (List.mem_of_mem_eraseIdx hd) hdk) hz'',
      termR_eq_zero_of_dot PF D _ _ ω (fun d hd hdk => hlab d (hp.symm.subset hd) hdk) hz']

end RebaseValue

section RemoveOrph

variable {k n : ℕ}

/-- The clauses kept by a sequence of steps that keeps the atoms, the blocks, the scaling order and
the value. -/
structure KeepOut (C : ℕ) (x : Atom k n) (g g' : Graph k n) : Prop where
  chain : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n, g'⟩
  nn : NN C x g'
  unp : g'.unpart = []
  orp : g'.orph = []
  ord : g'.ord = g.ord
  pw : g'.pw x = g.pw x
  vio : g'.viol x = g.viol x
  exc : excL g'.comps = excL g.comps
  blk : ∀ a b, g'.SameBlock a b ↔ g.SameBlock a b
  val : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι), g'.valR PF D e = g.valR PF D e
  sr : SR g x (Tracked.self g')
  labc : ∀ c ∈ g'.comps, c.label.isSome = true → c ∈ g.comps
  labc' : ∀ c ∈ g.comps, c.label.isSome = true → c ∈ g'.comps
  size : g'.comps.length ≤ g.comps.length

end RemoveOrph

section RebaseOne

variable {k n : ℕ}

/-- The clauses on the output of moving one labelled component of the block of `x` to `x`. -/
structure RebOut (C : ℕ) (x : Atom k n) (g g' : Graph k n) : Prop where
  chain : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n, g'⟩
  nn : NN C x g'
  unp : g'.unpart = []
  orp : g'.orph = []
  ord : g'.ord = g.ord
  pw : g'.pw x = g.pw x
  vio : g'.viol x < g.viol x
  exc : excL g'.comps = excL g.comps
  val : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι), g'.valR PF D e = g.valR PF D e
  sr : SR g x (Tracked.self g')
  size : g'.comps.length ≤ g.comps.length + 1

theorem exists_pos_of_sum_pos {α : Type*} (L : List α) (f : α → ℕ)
    (h : 0 < (L.map f).sum) : ∃ a ∈ L, 0 < f a := by
  by_contra hne
  push Not at hne
  have : (L.map f).sum = 0 := by
    rw [List.sum_eq_zero_iff]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact Nat.le_zero.1 (hne a ha)
  omega

end RebaseOne

/-! ## Graphs with one more internal atom -/

section LiftFacts

variable {k n : ℕ}

theorem liftA_injective (j : ℕ) : Function.Injective (liftA (k := k) (n := n) j) := by
  intro u v h
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [liftA, Sum.map_inl, Sum.map_inr, id_eq, Sum.inl.injEq, Sum.inr.injEq,
      Fin.castAdd_inj, reduceCtorEq] at h ⊢ <;> exact h

theorem liftA_isRight (j : ℕ) (u : Atom k n) : (liftA j u).isRight = u.isRight := by
  rcases u with a | a <;> simp [liftA]

theorem liftA_ne_newA (j : ℕ) (u : Atom k n) (i : Fin j) : liftA j u ≠ newA i := by
  rcases u with a | a
  · simp [liftA, newA]
  · intro h
    have := congrArg Fin.val (Sum.inr.inj h)
    simp at this
    have := a.isLt
    omega

theorem atom_cases {j : ℕ} (u : Atom k (n + j)) :
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

theorem atom_cases1 (u : Atom k (n + 1)) :
    (∃ v : Atom k n, u = liftA 1 v) ∨ u = newA 0 := by
  rcases atom_cases (j := 1) u with h | ⟨i, rfl⟩
  · exact Or.inl h
  · right; rw [Subsingleton.elim i 0]

theorem liftA_inr (i : Fin n) : liftA (k := k) 1 (.inr i) = .inr (Fin.castAdd 1 i) := rfl

theorem newA_isRight : (newA (k := k) (n := n) (0 : Fin 1)).isRight = true := rfl

end LiftFacts

section DTermsFacts

variable {V : Type*} [DecidableEq V]

theorem psteps_mem_dTerms {p q : V} {cs : List (Comp V)} {d : List (Comp V)} :
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

end DTermsFacts

/-! ## The labelled group and the unlabelled factor of a `P`-form -/

section PCore

variable {k n : ℕ}

/-- The relabelling of `pLiftT`: random components get the label `P_y`. -/
def rl {V : Type*} (y : V) (c : Comp V) : Comp V :=
  if c.kind.isRandom then { c with label := some (.P, y) } else c

/-- The components kept in `Graph.pCore`. -/
def coreP {V : Type*} (c : Comp V) : Bool := c.label.isSome || !c.kind.isRandom

theorem pCore_comps (g : Graph k n) :
    g.pCore.comps = (g.comps.filter coreP).map fun c => { c with label := none } := rfl

theorem pEnv_eq (g : Graph k n) : g.pEnv = g.comps.filter fun c => !coreP c := by
  unfold Graph.pEnv coreP
  apply List.filter_congr
  intro c _
  cases c.label <;> cases c.kind.isRandom <;> rfl

theorem comps_perm_core (g : Graph k n) : g.comps.Perm (g.comps.filter coreP ++ g.pEnv) := by
  rw [pEnv_eq]
  exact (List.filter_append_perm _ _).symm

theorem relab_pCore {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand) :
    g.pCore.comps.map (rl x) = g.comps.filter coreP := by
  rw [pCore_comps, List.map_map]
  conv_rhs => rw [← List.map_id (g.comps.filter coreP)]
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨hcm, hcp⟩ := List.mem_filter.1 hc
  simp only [Function.comp_apply, id_eq, rl]
  rcases hlab c hcm with h | h
  · have hr : c.kind.isRandom = false := by
      unfold coreP at hcp; rw [h] at hcp; simpa using hcp
    rw [if_neg (by simp [hr])]
    rcases c with ⟨κ, a, b, mi, l⟩
    simp only at h ⊢; rw [h]
  · have hr : c.kind.isRandom = true := hlr c hcm (by rw [h]; rfl)
    rw [if_pos hr]
    rcases c with ⟨κ, a, b, mi, l⟩
    simp only at h ⊢; rw [h]

theorem rl_map {V W : Type*} (f : V → W) (y : V) (c : Comp V) :
    rl (f y) (c.map f) = (rl y c).map f := by
  unfold rl
  by_cases h : c.kind.isRandom = true
  · rw [if_pos (by simpa [Comp.map] using h), if_pos h]; rfl
  · rw [if_neg (by simpa [Comp.map] using h), if_neg h]

theorem mem_pLiftT {u : Atom k n} {g : Graph k n} {E : TExpansion k n} {t : Tracked k n} :
    t ∈ pLiftT u g E ↔ ∃ s ∈ E, (s.g.comps.any fun c => decide (c.label = some (.Q, s.f u))) = false ∧
      t = ⟨s.nOut, ⟨s.g.comps.map (rl (s.f u)) ++ g.pEnv.map (Comp.map s.f), s.g.coeff⟩, s.f⟩ := by
  unfold pLiftT
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, ht⟩
    split_ifs at ht with hq
    obtain rfl := Option.some.inj ht
    exact ⟨s, hs, by simpa using hq, rfl⟩
  · rintro ⟨s, hs, hq, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [if_neg (by simpa using hq)]
    rfl

end PCore

/-! ## Blocks of a graph with one more internal atom -/

section LiftBlocks

variable {k n : ℕ}

/-- A surjection up to one extra point, identifying exactly the related pairs: one class more. -/
theorem card_quot_lift {V W : Type*} [Finite V] {r : V → V → Prop} {s : W → W → Prop}
    (f : V → W) (hf : Function.Injective f) (w₀ : W) (hw₀ : ∀ v, f v ≠ w₀)
    (hcov : ∀ w, w = w₀ ∨ ∃ v, w = f v)
    (h : ∀ a b, Relation.EqvGen s a b → a = b ∨ ∃ u v, a = f u ∧ b = f v ∧ Relation.EqvGen r u v)
    (hmap : ∀ u v, Relation.EqvGen r u v → Relation.EqvGen s (f u) (f v)) :
    Nat.card (Quot (Relation.EqvGen s)) = Nat.card (Quot (Relation.EqvGen r)) + 1 := by
  classical
  let ψ : Quot (Relation.EqvGen r) → Quot (Relation.EqvGen s) :=
    Quot.lift (fun u => Quot.mk _ (f u)) (fun u v huv => quot_eqvGen_sound (hmap u v huv))
  let φ : Option (Quot (Relation.EqvGen r)) → Quot (Relation.EqvGen s) :=
    fun o => o.elim (Quot.mk _ w₀) ψ
  have hφ : Function.Bijective φ := by
    constructor
    · intro o o' hoo
      rcases o with _ | q <;> rcases o' with _ | q'
      · rfl
      · induction q' using Quot.ind with
        | mk v =>
          exfalso
          have := quot_eqvGen_exact hoo
          rcases h _ _ this with h' | ⟨u, v', h1, -, -⟩
          · exact hw₀ v h'.symm
          · exact hw₀ u h1.symm
      · induction q using Quot.ind with
        | mk v =>
          exfalso
          have := quot_eqvGen_exact hoo
          rcases h _ _ this with h' | ⟨u, v', -, h2, -⟩
          · exact hw₀ v h'
          · exact hw₀ v' h2.symm
      · induction q using Quot.ind with
        | mk u =>
          induction q' using Quot.ind with
          | mk v =>
            have := quot_eqvGen_exact hoo
            congr 1
            rcases h _ _ this with h' | ⟨u', v', h1, h2, h3⟩
            · rw [hf h']
            · rw [hf h1, hf h2]; exact quot_eqvGen_sound h3
    · intro q
      induction q using Quot.ind with
      | mk w =>
        rcases hcov w with rfl | ⟨v, rfl⟩
        · exact ⟨none, rfl⟩
        · exact ⟨some (Quot.mk _ v), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ)]
  have : Finite (Quot (Relation.EqvGen r)) := Quot.finite _
  exact Finite.card_option

theorem dotRel_lift {rest : List (Comp (Atom k n))} {A : List (Comp (Atom k (n + 1)))}
    {L : List (Comp (Atom k (n + 1)))} (hL : L.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hA : ∀ a ∈ A, a.kind ≠ .dot) (a b : Atom k (n + 1)) :
    dotRel L a b ↔ ∃ c ∈ rest, c.kind = .dot ∧ a = liftA 1 c.x ∧ b = liftA 1 c.y := by
  rw [dotRel_perm hL]
  constructor
  · rintro ⟨d, hd, hk, rfl, rfl⟩
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
      exact ⟨c, hc, hk, rfl, rfl⟩
    · exact absurd hk (hA d hd)
  · rintro ⟨c, hc, hk, rfl, rfl⟩
    exact ⟨c.map (liftA 1), List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩), hk, rfl, rfl⟩

theorem eqvGen_lift_cases {rest : List (Comp (Atom k n))}
    {A : List (Comp (Atom k (n + 1)))} {L : List (Comp (Atom k (n + 1)))}
    (hL : L.Perm (rest.map (Comp.map (liftA 1)) ++ A)) (hA : ∀ a ∈ A, a.kind ≠ .dot)
    {a b : Atom k (n + 1)} (h : Relation.EqvGen (dotRel L) a b) :
    a = b ∨ ∃ u v, a = liftA 1 u ∧ b = liftA 1 v ∧ Relation.EqvGen (dotRel rest) u v := by
  induction h with
  | rel a b hr =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := (dotRel_lift hL hA a b).1 hr
    exact Or.inr ⟨c.x, c.y, rfl, rfl, Relation.EqvGen.rel _ _ ⟨c, hc, hk, rfl, rfl⟩⟩
  | refl a => exact Or.inl rfl
  | symm a b _ ih =>
    rcases ih with h | ⟨u, v, h1, h2, h3⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨v, u, h2, h1, h3.symm⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with rfl | ⟨u, v, h1, h2, h3⟩
    · exact ih2
    · rcases ih2 with rfl | ⟨v', w, h1', h2', h3'⟩
      · exact Or.inr ⟨u, v, h1, h2, h3⟩
      · rw [h2] at h1'
        have := liftA_injective 1 h1'
        subst this
        exact Or.inr ⟨u, w, h1, h2', h3.trans _ _ _ h3'⟩

theorem sameBlock_lift {g : Graph k n} {rest : List (Comp (Atom k n))}
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hdots : ∀ c, c.kind = .dot → (c ∈ rest ↔ c ∈ g.comps))
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A)) (hA : ∀ a ∈ A, a.kind ≠ .dot)
    (u v : Atom k n) : g₁.SameBlock (liftA 1 u) (liftA 1 v) ↔ g.SameBlock u v := by
  have hrel : ∀ a b, dotRel rest a b ↔ dotRel g.comps a b := by
    intro a b
    constructor
    · rintro ⟨c, hc, hk, rfl, rfl⟩; exact ⟨c, (hdots c hk).1 hc, hk, rfl, rfl⟩
    · rintro ⟨c, hc, hk, rfl, rfl⟩; exact ⟨c, (hdots c hk).2 hc, hk, rfl, rfl⟩
  have hr : dotRel rest = dotRel g.comps := by funext a b; exact propext (hrel a b)
  rw [Graph.sameBlock_iff_eqvGen, Graph.sameBlock_iff_eqvGen, ← hr]
  constructor
  · intro h
    rcases eqvGen_lift_cases hL hA h with h' | ⟨u', v', h1, h2, h3⟩
    · rw [liftA_injective 1 h']; exact Relation.EqvGen.refl _
    · rw [liftA_injective 1 h1, liftA_injective 1 h2]; exact h3
  · intro h
    induction h with
    | rel a b hab =>
      obtain ⟨c, hc, hk, rfl, rfl⟩ := hab
      exact Relation.EqvGen.rel _ _ ((dotRel_lift hL hA _ _).2 ⟨c, hc, hk, rfl, rfl⟩)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

theorem sameBlock_new {rest : List (Comp (Atom k n))}
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A)) (hA : ∀ a ∈ A, a.kind ≠ .dot)
    (b : Atom k (n + 1)) : g₁.SameBlock (newA 0) b ↔ b = newA 0 := by
  constructor
  · intro h
    rw [Graph.sameBlock_iff_eqvGen] at h
    rcases eqvGen_lift_cases hL hA h with h' | ⟨u, v, h1, -, -⟩
    · exact h'.symm
    · exact absurd h1.symm (liftA_ne_newA 1 u 0)
  · rintro rfl; exact Graph.sameBlock_refl _ _

theorem excL_lift {g : Graph k n} {R rest : List (Comp (Atom k n))}
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)} (hR : g.comps.Perm (R ++ rest))
    (hRd : ∀ c ∈ R, c.kind ≠ .dot)
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A)) (hA : ∀ a ∈ A, a.kind ≠ .dot) :
    excL g₁.comps = excL g.comps := by
  have hdots : ∀ c, c.kind = .dot → (c ∈ rest ↔ c ∈ g.comps) := by
    intro c hk
    rw [hR.mem_iff, List.mem_append]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact absurd hk (hRd c h)
      · exact h
  have hn : nDotL g₁.comps = nDotL g.comps := by
    unfold nDotL
    rw [(hL.filter _).length_eq, (hR.filter _).length_eq, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter, List.countP_append, List.countP_append, List.countP_map,
      (List.countP_eq_zero (l := R)).2 (fun c hc => by simpa using hRd c hc),
      (List.countP_eq_zero (l := A)).2 (fun c hc => by simpa using hA c hc)]
    simp only [add_zero, zero_add]
    rfl
  have hb : nBlk g₁.comps = nBlk g.comps + 1 := by
    unfold nBlk
    have hrel : dotRel rest = dotRel g.comps := by
      funext a b
      apply propext
      constructor
      · rintro ⟨c, hc, hk, rfl, rfl⟩; exact ⟨c, (hdots c hk).1 hc, hk, rfl, rfl⟩
      · rintro ⟨c, hc, hk, rfl, rfl⟩; exact ⟨c, (hdots c hk).2 hc, hk, rfl, rfl⟩
    rw [← hrel]
    refine card_quot_lift (liftA 1) (liftA_injective 1) (newA 0) (fun v => liftA_ne_newA 1 v 0)
      (fun w => (atom_cases1 w).elim (fun ⟨v, hv⟩ => Or.inr ⟨v, hv⟩) Or.inl)
      (fun a b h => eqvGen_lift_cases hL hA h) ?_
    intro u v huv
    induction huv with
    | rel a b hab =>
      obtain ⟨c, hc, hk, rfl, rfl⟩ := hab
      exact Relation.EqvGen.rel _ _ ((dotRel_lift hL hA _ _).2 ⟨c, hc, hk, rfl, rfl⟩)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  unfold excL
  rw [hn, hb]
  push_cast
  ring

end LiftBlocks

/-! ## The terms of the steps inside `P_x` with one new atom -/

section LiftTerm

variable {k n : ℕ}

/-- The clauses on a graph `g₁` with one new atom `α` obtained from `g` by removing the labelled
components `R`, moving the others to the new atom set, and adding the components `A`. -/
structure LTOut (C : ℕ) (x : Atom k n) (g : Graph k n) (A : List (Comp (Atom k (n + 1))))
    (g₁ : Graph k (n + 1)) : Prop where
  nn : NN (C + A.length + 1) (liftA 1 x) g₁
  sr : SR g x ⟨n + 1, g₁, liftA 1⟩
  unp : g₁.unpart.length ≤ (A.filter fun a => a.kind.isSolid).length
  unpSub : g₁.unpart.Subperm A
  orp : g₁.orph.length ≤ g.comps.length
  size : g₁.comps.length ≤ g.comps.length + A.length
  blk : ∀ u v, g₁.SameBlock (liftA 1 u) (liftA 1 v) ↔ g.SameBlock u v
  blkNew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0

theorem liftTerm {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    (hRl : ∀ c ∈ R, c.label = some (.P, x))
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hAd : ∀ a ∈ A, a.kind ≠ .dot ∧ a.kind ≠ .xdot)
    (hAl : ∀ a ∈ A, a.label = if a.kind.isRandom then some (.P, liftA 1 x) else none)
    (hAp : ∀ a ∈ A, a.minor = [] ∧ (∀ ch, a.kind ≠ .inv ch) ∧ (∀ ch d, a.kind ≠ .wD ch d) ∧
      (a.kind.isWeight = true → a.y = a.x))
    (hAs : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ A)
    (hAb : ∀ a ∈ A, a.kind.isSolid = true → a.x ≠ a.y ∧
      ∀ u v, a.x = liftA 1 u → a.y = liftA 1 v → ¬ g.SameBlock u v)
    (hAi : ∀ a ∈ A, a.kind.isSolid = true → a.x.isRight = true ∨ a.y.isRight = true)
    (hcon : ∀ c ∈ R, Relation.EqvGen (fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v)
      (liftA 1 c.x) (liftA 1 c.y))
    (hblue : ∀ c ∈ R, c.kind = .G .plus → ∀ a b, c.x = .inr a → c.y = .inr b →
      Relation.EqvGen (bconn g₁) (Fin.castAdd 1 a) (Fin.castAdd 1 b))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) : LTOut C x g A g₁ := by
  have hN := hS.nn
  have hRr : ∀ c ∈ R, c.kind.isRandom = true := fun c hc =>
    hN.plain.labRand c (hR.symm.subset (List.mem_append_left _ hc)) (by rw [hRl c hc]; rfl)
  have hRd : ∀ c ∈ R, c.kind ≠ .dot := fun c hc => Kind.ne_dot_of_isRandom (hRr c hc)
  have hRx : ∀ c ∈ R, c.kind ≠ .xdot := fun c hc => Kind.ne_xdot_of_isRandom (hRr c hc)
  have hAd' : ∀ a ∈ A, a.kind ≠ .dot := fun a ha => (hAd a ha).1
  have hrest : ∀ c ∈ rest, c ∈ g.comps := fun c hc => hR.symm.subset (List.mem_append_right _ hc)
  have hmemg : ∀ c ∈ g.comps, c ∈ R ∨ c ∈ rest := fun c hc => List.mem_append.1 (hR.subset hc)
  have hdots : ∀ c, c.kind = .dot → (c ∈ rest ↔ c ∈ g.comps) := by
    intro c hk
    constructor
    · exact hrest c
    · intro hc
      rcases hmemg c hc with h | h
      · exact absurd hk (hRd c h)
      · exact h
  have hblk := sameBlock_lift hdots hL hAd'
  have hblkN := sameBlock_new hL hAd'
  have hmem₁ : ∀ c, c ∈ g₁.comps ↔ (∃ d ∈ rest, c = d.map (liftA 1)) ∨ c ∈ A := by
    intro c
    rw [hL.mem_iff, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨d, hd, rfl⟩ | h)
      · exact Or.inl ⟨d, hd, rfl⟩
      · exact Or.inr h
    · rintro (⟨d, hd, rfl⟩ | h)
      · exact Or.inl ⟨d, hd, rfl⟩
      · exact Or.inr h
  have hlift₁ : ∀ d ∈ rest, d.map (liftA 1) ∈ g₁.comps := fun d hd => (hmem₁ _).2 (Or.inl ⟨d, hd, rfl⟩)
  have hA₁ : ∀ a ∈ A, a ∈ g₁.comps := fun a ha => (hmem₁ a).2 (Or.inr ha)
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  -- the new atom is joined to the image of `x`
  have hsx : ∀ (rel : Atom k (n + 1) → Atom k (n + 1) → Prop),
      (∀ d ∈ g₁.comps, (∃ w, d.kind = .waved w) → rel d.x d.y) →
      Relation.EqvGen rel (liftA 1 x) (newA 0) := by
    intro rel hrel
    exact Relation.EqvGen.rel _ _ (hrel _ (hA₁ _ hAs) ⟨.s, rfl⟩)
  -- the clauses `NN`
  have hcnx : g₁.ConnNoX := by
    have key : ∀ u v, g.edgeGraphNoX.Reachable u v →
        g₁.edgeGraphNoX.Reachable (liftA 1 u) (liftA 1 v) := by
      intro u v huv
      unfold Graph.edgeGraphNoX at huv ⊢
      rw [reachable_fromRel_iff] at huv ⊢
      induction huv with
      | rel a b hr =>
        obtain ⟨d, hd, hk, rfl, rfl⟩ := hr
        rcases hmemg d hd with h | h
        · exact hcon d h
        · exact Relation.EqvGen.rel _ _ ⟨d.map (liftA 1), hlift₁ d h, hk, rfl, rfl⟩
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
    have hnew : g₁.edgeGraphNoX.Reachable (liftA 1 x) (newA 0) := by
      unfold Graph.edgeGraphNoX
      rw [reachable_fromRel_iff]
      exact hsx _ fun d hd ⟨w, hw⟩ => ⟨d, hd, by rw [hw]; simp, rfl, rfl⟩
    have hall : ∀ a, g₁.edgeGraphNoX.Reachable (liftA 1 x) a := by
      intro a
      rcases atom_cases1 a with ⟨v, rfl⟩ | rfl
      · exact key x v (hN.cnx x v)
      · exact hnew
    intro a b
    exact (hall a).symm.trans (hall b)
  have hint₁ : ∀ a b : Fin (n + 1), g₁.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    have key : ∀ u v, g.wavedThetaGraph.Reachable u v →
        g₁.wavedThetaGraph.Reachable (liftA 1 u) (liftA 1 v) := by
      intro u v huv
      unfold Graph.wavedThetaGraph at huv ⊢
      rw [reachable_fromRel_iff] at huv ⊢
      induction huv with
      | rel a b hr =>
        obtain ⟨d, hd, hk, rfl, rfl⟩ := hr
        have hnr : d.kind.isRandom = false := by
          rcases hk with ⟨hj, -⟩ | hj <;>
          · by_contra hh
            have hh' : d.kind.isRandom = true := by simpa using hh
            first
            | (rw [Kind.not_joinsMol_of_isRandom hh'] at hj; cases hj)
            | (rw [Kind.not_isDiffusive_of_isRandom hh'] at hj; cases hj)
        rcases hmemg d hd with h | h
        · rw [hRr d h] at hnr; cases hnr
        · exact Relation.EqvGen.rel _ _ ⟨d.map (liftA 1), hlift₁ d h, hk, rfl, rfl⟩
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
    obtain ⟨xi, hxi⟩ : ∃ xi, x = .inr xi := by
      rcases hx : x with a | a
      · have := hN.hx; rw [hx] at this; simp at this
      · exact ⟨a, rfl⟩
    have hnew : g₁.wavedThetaGraph.Reachable (liftA 1 x) (newA 0) := by
      unfold Graph.wavedThetaGraph
      rw [reachable_fromRel_iff]
      exact hsx _ fun d hd ⟨w, hw⟩ => ⟨d, hd, Or.inl ⟨by rw [hw]; rfl, by rw [hw]; simp⟩, rfl, rfl⟩
    have hall : ∀ a : Fin (n + 1), g₁.wavedThetaGraph.Reachable (liftA 1 x) (.inr a) := by
      intro a
      rcases atom_cases1 (k := k) (.inr a) with ⟨v, hv⟩ | hv
      · rw [hv]
        rcases v with b | b
        · simp [liftA] at hv
        · rw [hxi]; exact key _ _ (hN.reg.internal xi b)
      · rw [hv]; exact hnew
    intro a b
    exact (hall a).symm.trans (hall b)
  have hpart : ∀ d ∈ rest, d.kind.isSolid = true → g₁.partB (d.map (liftA 1)) = true := by
    intro d hd hds
    have : g.partB d = true := by
      by_contra hp'
      have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hrest d hd, hds, by simpa using hp'⟩
      rw [hS.unp] at this; simp at this
    obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 this
    have he' : e ∈ rest := by
      rcases hmemg e he with h | h
      · exact absurd hek (hRx e h)
      · exact h
    refine (g₁.partB_iff _).2 ⟨e.map (liftA 1), hlift₁ e he', hek, ?_⟩
    rcases hep with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
    · exact Or.inr ⟨by simp [Comp.map, h1], by simp [Comp.map, h2]⟩
  have hunpA : ∀ c ∈ g₁.unpart, c ∈ A := by
    intro c hc
    obtain ⟨hcm, hcs, hcp⟩ := Graph.mem_unpart.1 hc
    rcases (hmem₁ c).1 hcm with ⟨d, hd, rfl⟩ | h
    · rw [hpart d hd hcs] at hcp; cases hcp
    · exact h
  have hNN : NN (C + A.length + 1) (liftA 1 x) g₁ := by
    refine ⟨hx₁, ⟨?_, ConnNoX.connected hcnx, hint₁, ?_⟩, hcnx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 := hL.length_eq
      have h2 := hR.length_eq
      simp only [List.length_append, List.length_map] at h1 h2
      have := hS.nn.reg.size
      omega
    · intro c hc hk
      rcases (hmem₁ c).1 hc with ⟨d, hd, rfl⟩ | h
      · have := hN.reg.noIntDot d (hrest d hd) hk
        simp only [Comp.map]
        rcases this with h' | h'
        · left; rcases hdx : d.x with a | a <;> rw [hdx] at h' <;> simp_all [liftA]
        · right; rcases hdy : d.y with a | a <;> rw [hdy] at h' <;> simp_all [liftA]
      · exact absurd hk (hAd' c h)
    · intro c hc hk
      rcases (hmem₁ c).1 hc with ⟨d, hd, rfl⟩ | h
      · intro he
        exact hN.noLoop d (hrest d hd) hk (liftA_injective 1 he)
      · exact (hAb c h hk).1
    · intro c hc
      rcases (hmem₁ c).1 hc with ⟨d, hd, rfl⟩ | h
      · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN.plain d (hrest d hd)
        refine ⟨by simp [Comp.map, h1], h2, h3, fun hk he => h4 hk (liftA_injective 1 he), ?_, ?_⟩
        · intro hw; simp only [Comp.map]; rw [h5 hw]
        · intro hl; exact h6 (by simpa [Comp.map] using hl)
      · obtain ⟨h1, h2, h3, h4⟩ := hAp c h
        refine ⟨h1, h2, h3, fun hk => absurd hk (hAd' c h), h4, ?_⟩
        intro hl
        rw [hAl c h] at hl
        by_contra hr
        rw [if_neg hr] at hl
        cases hl
    · intro c hc
      rcases (hmem₁ c).1 hc with ⟨d, hd, rfl⟩ | h
      · rcases hN.lab d (hrest d hd) with h' | h'
        · left; simp [Comp.map, h']
        · right; simp [Comp.map, h']
      · rw [hAl c h]
        split_ifs
        · right; rfl
        · left; rfl
    · intro c hc hk
      rcases (hmem₁ c).1 hc with ⟨d, hd, rfl⟩ | h
      · simp only [Comp.map]
        rw [hblk]
        exact hN.xa d (hrest d hd) hk
      · exact absurd hk (hAd c h).2
    · intro i j hij
      rcases atom_cases1 (k := k) (.inr i) with ⟨u, hu⟩ | hu <;>
        rcases atom_cases1 (k := k) (.inr j) with ⟨v, hv⟩ | hv
      · have h' : g.SameBlock u v := by rw [← hblk, ← hu, ← hv]; exact hij
        have hur : u.isRight = true := by rw [← liftA_isRight 1 u, ← hu]; rfl
        have hvr : v.isRight = true := by rw [← liftA_isRight 1 v, ← hv]; rfl
        obtain ⟨a, rfl⟩ : ∃ a, u = .inr a := by
          rcases u with a | a
          · simp at hur
          · exact ⟨a, rfl⟩
        obtain ⟨b, rfl⟩ : ∃ b, v = .inr b := by
          rcases v with b | b
          · simp at hvr
          · exact ⟨b, rfl⟩
        have := hN.ib a b h'
        subst this
        exact Sum.inr.inj (hu.trans hv.symm)
      · rw [hu, hv] at hij
        have := (hblkN _).1 (Graph.sameBlock_symm hij)
        exact absurd this (liftA_ne_newA 1 u 0)
      · rw [hu] at hij
        have := (hblkN _).1 hij
        rw [hv] at this
        exact absurd this (liftA_ne_newA 1 v 0)
      · exact Sum.inr.inj (hu.trans hv.symm)
    · intro c hc hk hb
      rcases (hmem₁ c).1 hc with ⟨d, hd, rfl⟩ | h
      · simp only [Comp.map] at hb
        rw [hblk] at hb
        exact hN.inBlk d (hrest d hd) hk hb
      · obtain ⟨hne, hnb⟩ := hAb c h hk
        rcases atom_cases1 c.x with ⟨u, hu⟩ | hu
        · rcases atom_cases1 c.y with ⟨v, hv⟩ | hv
          · rw [hu, hv, hblk] at hb
            exact hnb u v hu hv hb
          · rw [hv] at hb
            have := (hblkN _).1 (Graph.sameBlock_symm hb)
            rw [hu] at this
            exact liftA_ne_newA 1 u 0 this
        · rw [hu] at hb hne
          exact hne ((hblkN _).1 hb).symm
    · intro c hc
      have := hunpA c hc
      obtain ⟨-, hcs, -⟩ := Graph.mem_unpart.1 hc
      rw [hAl c this, if_pos (Kind.isRandom_of_isSolid hcs)]
      rfl
    · intro c hc
      exact hAi c (hunpA c hc) (Graph.mem_unpart.1 hc).2.1
  -- the environment
  have henv : (g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).Perm
      (rest.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)) := by
    have := hR.filter (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
    rw [List.filter_append, (List.filter_eq_nil_iff (l := R)).2 (fun c hc => by simp [hRl c hc]),
      List.nil_append] at this
    exact this
  have hcar : ((g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧
      c.kind ≠ .xdot)).map (Comp.map (liftA 1))).Subperm g₁.comps := by
    refine (henv.map _).subperm.trans ?_
    refine (subperm_map' List.filter_sublist.subperm _).trans ?_
    exact (List.sublist_append_left _ _).subperm.trans hL.symm.subperm
  refine ⟨hNN, ⟨⟨hcar, fun u v huv => (hblk u v).2 huv⟩, ?_, ?_, hx₁, hch, ?_⟩, ?_, ?_, ?_, ?_, hblk,
    hblkN⟩
  · intro hdc
    refine dc_transfer (liftA 1) hN.plain.labRand (fun i => ⟨Fin.castAdd 1 i, rfl⟩) ?_ ?_ hcar ?_ hdc
    · have key : ∀ p q, Relation.EqvGen (fun u v => ∃ c ∈ g.comps, c.kind.joinsMol = true ∧
          c.x = u ∧ c.y = v) p q → Relation.EqvGen (fun u v => ∃ c ∈ g₁.comps,
            c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) (liftA 1 p) (liftA 1 q) := by
        intro p q hr
        induction hr with
        | rel a b hr' =>
          obtain ⟨d, hd, hj, rfl, rfl⟩ := hr'
          rcases hmemg d hd with h | h
          · rw [Kind.not_joinsMol_of_isRandom (hRr d h)] at hj; cases hj
          · exact Relation.EqvGen.rel _ _ ⟨d.map (liftA 1), hlift₁ d h, hj, rfl, rfl⟩
        | refl a => exact Relation.EqvGen.refl _
        | symm a b _ ih => exact ih.symm
        | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
      intro u v hu hv huv
      rcases huv with rfl | ⟨-, -, hr⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨by rw [liftA_isRight]; exact hu, by rw [liftA_isRight]; exact hv, ?_⟩
        unfold Graph.molGraph at hr ⊢
        rw [reachable_fromRel_iff] at hr ⊢
        exact key _ _ hr
    · intro j
      obtain ⟨xi, hxi⟩ : ∃ xi, x = .inr xi := by
        rcases hx : x with a | a
        · have := hN.hx; rw [hx] at this; simp at this
        · exact ⟨a, rfl⟩
      rcases atom_cases1 (k := k) (.inr j) with ⟨v, hv⟩ | hv
      · rcases v with b | b
        · simp [liftA] at hv
        · exact ⟨b, Or.inl hv⟩
      · refine ⟨xi, Or.inr ⟨rfl, rfl, ?_⟩⟩
        rw [hv, ← hxi]
        unfold Graph.molGraph
        rw [reachable_fromRel_iff]
        exact (hsx _ fun d hd ⟨w, hw⟩ => ⟨d, hd, by rw [hw]; rfl, rfl, rfl⟩).symm
    · intro c hc hk a b a' b' hx' hy' ha hb
      rcases hmemg c hc with h | h
      · have := hblue c h hk a b hx' hy'
        have ha' : a' = Fin.castAdd 1 a := by
          have : liftA 1 (Sum.inr a : Atom k n) = .inr a' := ha
          exact (Sum.inr.inj this).symm
        have hb' : b' = Fin.castAdd 1 b := by
          have : liftA 1 (Sum.inr b : Atom k n) = .inr b' := hb
          exact (Sum.inr.inj this).symm
        rw [ha', hb']; exact this
      · refine Relation.EqvGen.rel _ _ (Or.inr ⟨c.map (liftA 1), hlift₁ c h, hk, ?_, ?_⟩)
        · simp only [Comp.map]; rw [hx']; exact ha
        · simp only [Comp.map]; rw [hy']; exact hb
  · exact le_of_eq (excL_lift hR hRd hL hAd')
  · intro u hu
    rcases atom_cases1 u with ⟨v, rfl⟩ | rfl
    · exact absurd rfl (hu v)
    · unfold Graph.wavedGraph
      rw [reachable_fromRel_iff]
      exact hsx _ fun d hd hw => ⟨d, hd, hw, rfl, rfl⟩
  · have hp := hL.filter (fun c => c.kind.isSolid && !g₁.partB c)
    unfold Graph.unpart
    rw [hp.length_eq, List.filter_append, List.length_append,
      List.filter_eq_nil_iff.2 (fun c hc => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false]
        intro hds
        exact hpart d hd (by simpa [Comp.map] using hds))]
    simp only [List.length_nil, zero_add]
    exact filter_length_le_of _ _ _ (fun c _ hc => by simp only [Bool.and_eq_true] at hc; exact hc.1)
  · have hp := hL.filter (fun c => c.kind.isSolid && !g₁.partB c)
    unfold Graph.unpart
    refine hp.subperm.trans ?_
    rw [List.filter_append, List.filter_eq_nil_iff.2 (fun c hc => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false]
        intro hds
        exact hpart d hd (by simpa [Comp.map] using hds)), List.nil_append]
    exact List.filter_sublist.subperm
  · have hp := hL.filter (fun c => c.kind == .xdot && !g₁.solidB c)
    unfold Graph.orph
    rw [hp.length_eq, List.filter_append, List.length_append,
      (List.filter_eq_nil_iff (l := A)).2 (fun c hc => by simp [(hAd c hc).2])]
    simp only [List.length_nil, add_zero]
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_map]
    have := hR.length_eq
    simp only [List.length_append] at this
    omega
  · have h1 := hL.length_eq
    have h2 := hR.length_eq
    simp only [List.length_append, List.length_map] at h1 h2
    omega

/-- The sum of the scaling orders of a list of components. -/
def psteps_ordL {V : Type*} (cs : List (Comp V)) : ℤ := (cs.map fun c => c.kind.ord).sum

theorem ord_lift {g : Graph k n} {R rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm (R ++ rest)) {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A)) :
    g₁.ord = g.ord - psteps_ordL R + psteps_ordL A - 2 := by
  unfold Graph.ord psteps_ordL
  rw [(hL.map _).sum_eq, (hR.map _).sum_eq]
  simp only [List.map_append, List.sum_append, List.map_map]
  have : ((rest.map ((fun c => c.kind.ord) ∘ Comp.map (liftA 1)))).sum =
      (rest.map fun c => c.kind.ord).sum := rfl
  rw [this]
  push_cast
  ring

theorem pw_lift {x : Atom k n} {g : Graph k n} {R rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm (R ++ rest)) {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hblk : ∀ u v, g₁.SameBlock (liftA 1 u) (liftA 1 v) ↔ g.SameBlock u v) :
    g₁.pw (liftA 1 x) + (R.map (wBP fun u => g.SameBlock u x)).sum =
      g.pw x + (A.map (wBP fun u => g₁.SameBlock u (liftA 1 x))).sum := by
  unfold Graph.pw
  rw [(hL.map _).sum_eq, (hR.map _).sum_eq]
  simp only [List.map_append, List.sum_append, List.map_map]
  have : (rest.map ((wBP fun u => g₁.SameBlock u (liftA 1 x)) ∘ Comp.map (liftA 1))).sum =
      (rest.map (wBP fun u => g.SameBlock u x)).sum := by
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply]
    exact wBP_congr (c := c) (c' := c.map (liftA 1)) (by simp [Comp.map]) rfl
      (by simp only [Comp.map]; exact hblk _ _) (by simp only [Comp.map]; exact hblk _ _)
  rw [this]
  ring

end LiftTerm

/-! ## Products of component factors -/

section Values

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The product of the factors of the components `cs`. -/
def pv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  (cs.map (Comp.val D σ)).prod

/-- The product of the factors of the random components of `cs`. -/
def rv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  ((cs.filter fun c => c.kind.isRandom).map (Comp.val D σ)).prod

/-- The product of the factors of the deterministic components of `cs`. -/
def dv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  ((cs.filter fun c => !c.kind.isRandom).map (Comp.val D σ)).prod

variable {V W : Type*} (D : Data ι) (σ : V → ι)

@[simp] private theorem pv_nil : pv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] theorem pv_cons (c : Comp V) (cs : List (Comp V)) :
    pv D σ (c :: cs) = Comp.val D σ c * pv D σ cs := by
  simp [pv]

@[simp] private theorem rv_nil : rv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] theorem rv_cons (c : Comp V) (cs : List (Comp V)) :
    rv D σ (c :: cs) = (if c.kind.isRandom then Comp.val D σ c else 1) * rv D σ cs := by
  unfold rv
  by_cases h : c.kind.isRandom <;> simp [h]

@[simp] theorem rv_append (cs cs' : List (Comp V)) :
    rv D σ (cs ++ cs') = rv D σ cs * rv D σ cs' := by
  simp [rv]

@[simp] private theorem dv_nil : dv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] theorem dv_cons (c : Comp V) (cs : List (Comp V)) :
    dv D σ (c :: cs) = (if c.kind.isRandom then 1 else Comp.val D σ c) * dv D σ cs := by
  unfold dv
  by_cases h : c.kind.isRandom <;> simp [h]

@[simp] theorem dv_append (cs cs' : List (Comp V)) :
    dv D σ (cs ++ cs') = dv D σ cs * dv D σ cs' := by
  simp [dv]

theorem pv_eq (cs : List (Comp V)) : pv D σ cs = dv D σ cs * rv D σ cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [pv_cons, dv_cons, rv_cons, ih]
    split_ifs <;> ring

theorem val_map (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

theorem rv_map (σ : W → ι) (f : V → W) (cs : List (Comp V)) :
    rv D σ (cs.map (Comp.map f)) = rv D (σ ∘ f) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, rv_cons, rv_cons, ih, val_map]; rfl

theorem dv_map (σ : W → ι) (f : V → W) (cs : List (Comp V)) :
    dv D σ (cs.map (Comp.map f)) = dv D (σ ∘ f) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, dv_cons, dv_cons, ih, val_map]; rfl

@[simp] private theorem mkC_kind (κ : Kind) (u v : V) : (mkC κ u v).kind = κ := rfl

theorem val_solidC [DecidableEq V] (ch : Charge) (u v : V) :
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
@[simp] theorem elim_append_liftA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι)
    (u : Atom k n) : Sum.elim e (Fin.append s a) (liftA j u) = Sum.elim e s u := by
  rcases u with i | i <;> simp [liftA, Fin.append_left]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem elim_append_newA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι)
    (i : Fin j) : Sum.elim e (Fin.append s a) (newA i) = a i := by
  simp [newA, Fin.append_right]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem elim_append_comp_liftA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι) :
    Sum.elim e (Fin.append s a) ∘ liftA j = Sum.elim e s := by
  funext u
  simp

/-- The value of a graph with `j` more internal atoms, the labels of the new atoms summed
last. -/
theorem valR_splitN {Ω : Type} (g : Graph k (n + j)) (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) :
    g.valR PF D e ω =
      ∑ s : Fin n → ι, ∑ a : Fin j → ι, g.termR PF D (Sum.elim e (Fin.append s a)) ω := by
  unfold Graph.valR
  rw [← (Fin.appendEquiv n j).sum_comp, Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] in
/-- A sum over the labellings of one atom is a sum over `ι`. -/
theorem sum_fin1 (f : (Fin 1 → ι) → ℂ) : ∑ a, f a = ∑ α, f ![α] := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun a => ?_
  congr 1
  funext i
  fin_cases i
  rfl

end Labellings

section TermR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type} {k N : ℕ}

end TermR

/-! ## Closure of the test functions and linearity of `P_x` -/

section TestClosure

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

theorem test_mul' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω * g ω :=
  A.test_mul f g hf hg

theorem test_add' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω + g ω :=
  A.test_add f g hf hg

theorem test_const' (c : ℂ) : A.Test fun _ => c := A.test_const c

theorem test_sub' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω - g ω := by
  have e : (fun ω => f ω - g ω) = fun ω => f ω + (-1 : ℂ) * g ω := funext fun ω => by ring
  rw [e]
  exact test_add' A hf (test_mul' A (test_const' A _) hg)

theorem test_neg' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => -f ω := by
  have e : (fun ω => -f ω) = fun ω => (-1 : ℂ) * f ω := funext fun ω => by ring
  rw [e]
  exact test_mul' A (test_const' A _) hf

theorem test_star' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => star (f ω) :=
  A.test_star f hf

theorem test_G (a b : ι) : A.Test fun ω => A.G ω a b := by
  have h := A.test_entry a b
  have e : (fun ω => (D ω).Gm ∅ a b) = fun ω => A.G ω a b :=
    funext fun ω => by rw [A.data_G]; rfl
  rwa [e] at h

theorem test_dh' (a b : ι) {F : Ω → ℂ} (hF : A.Test F) :
    A.Test fun ω => A.dh a b F ω :=
  A.test_dh a b F hF

theorem test_listProd' {β : Type*} (l : List β) {f : β → Ω → ℂ}
    (h : ∀ q ∈ l, A.Test (f q)) :
    A.Test fun ω => (l.map fun q => f q ω).prod := by
  induction l with
  | nil => simpa using test_const' A 1
  | cons y l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact test_mul' A (h y (List.mem_cons_self ..)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

end TestClosure

/-- Proves `A.Test f` for `f` built from resolvent entries, conjugates, derivatives, sums,
products and constants. -/
local macro "test_tac" A:term : tactic =>
  `(tactic| repeat' (first
    | with_reducible assumption
    | with_reducible apply test_G $A
    | with_reducible apply test_dh' $A
    | with_reducible apply test_star' $A
    | with_reducible apply test_mul' $A
    | with_reducible apply test_sub' $A
    | with_reducible apply test_add' $A
    | with_reducible apply test_neg' $A
    | with_reducible apply test_sum' $A
    | with_reducible apply test_const' $A
    | intro))

/-- Proves `A.Good f` for a test function `f`. -/
local macro "good_tac" A:term : tactic =>
  `(tactic| (apply ($A).test_good; test_tac $A))

section Aux

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

theorem P_add' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω + g ω) ω = PF.P x f ω + PF.P x g ω :=
  congrFun (A.laws.add x f g hf hg) ω

theorem P_cmul' {f : Ω → ℂ} (c : ℂ) (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => c * f ω) ω = c * PF.P x f ω :=
  congrFun (A.laws.smul x c f hf) ω

include A in
theorem P_zero' (x : ι) (ω : Ω) : PF.P x (fun _ => 0) ω = 0 := by
  have h := P_cmul' A 0 (A.laws.good_const 0) x ω
  simpa using h

theorem P_neg' {f : Ω → ℂ} (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => -f ω) ω = -PF.P x f ω := by
  have h := P_cmul' A (-1) hf x ω
  simpa using h

theorem P_sub' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω - g ω) ω = PF.P x f ω - PF.P x g ω := by
  have hg' : A.Good fun ω => -g ω := by
    have e : (fun ω => -g ω) = fun ω => (-1 : ℂ) * g ω := funext fun ω => by ring
    rw [e]
    exact A.laws.good_mul _ _ (A.laws.good_const _) hg
  have h := P_add' A hf hg' x ω
  rw [P_neg' A hg x ω] at h
  simpa [sub_eq_add_neg] using h

theorem good_sum' {κ : Type} (s : Finset κ) {f : κ → Ω → ℂ} (h : ∀ i, A.Good (f i)) :
    A.Good fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using A.laws.good_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact A.laws.good_add _ _ (h a) ih

theorem P_sum' {κ : Type} (s : Finset κ) {f : κ → Ω → ℂ} (h : ∀ i, A.Good (f i))
    (x : ι) (ω : Ω) :
    PF.P x (fun ω => ∑ i ∈ s, f i ω) ω = ∑ i ∈ s, PF.P x (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using P_zero' A x ω
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [P_add' A (h a) (good_sum' A s h) x ω, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem P_congr' {f g : Ω → ℂ} (h : ∀ ω, f ω = g ω) (x : ι) :
    PF.P x f = PF.P x g := by
  rw [funext h]

theorem P_listSum' {β : Type*} (l : List β) {f : β → Ω → ℂ} (h : ∀ q ∈ l, A.Good (f q))
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

theorem dh_mul' (a b : ι) {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.dh a b (fun ω => f ω * g ω) = fun ω => A.dh a b f ω * g ω + f ω * A.dh a b g ω :=
  A.dh_mul a b f g hf hg

theorem dh_G (a b x y : ι) :
    A.dh a b (fun ω => A.G ω x y) = fun ω => -(A.G ω x a * A.G ω b y) :=
  A.dh_green a b x y


theorem H_mul_G (ω : Ω) (a b : ι) :
    ∑ β, A.H ω a β * A.G ω β b = (if a = b then 1 else 0) + A.z * A.G ω a b := by
  have hz : A.z.im ≠ 0 := ne_of_gt A.im_pos
  have h := congrFun (congrFun (sub_mul_green (A.isHermitian ω) hz) a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul,
    Finset.sum_sub_distrib, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  unfold ModelAdm.G
  linear_combination h

theorem G_mul_H (ω : Ω) (a b : ι) :
    ∑ β, A.G ω a β * A.H ω β b = (if a = b then 1 else 0) + A.z * A.G ω a b := by
  have hz : A.z.im ≠ 0 := ne_of_gt A.im_pos
  have h := congrFun (congrFun (green_mul_sub (A.isHermitian ω) hz) a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, mul_sub,
    Finset.sum_sub_distrib, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  unfold ModelAdm.G
  linear_combination h

theorem rowSum' (p : ι) : ∑ β, (A.S p β : ℂ) = 1 := by
  have h := A.rowSum p
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

theorem S_symm' (a b : ι) : (A.S a b : ℂ) = (A.S b a : ℂ) := by
  rw [A.isSymm.apply b a]

/-! ### One integration by parts in a row or a column -/

/-- The expansion `G_{pb} = m δ_{pb} - m² G_{pb} - m ∑_β h_{pβ} G_{βb}` followed by Gaussian
integration by parts in `P_p` ([I, (3.8)], [I, Lemma 2.4]). -/
theorem ibp_row (p b : ι) {K : Ω → ℂ} (hK : A.Test K) (ω : Ω) :
    PF.P p (fun ω => A.G ω p b * K ω) ω =
      msc A.z * (if p = b then 1 else 0) * PF.P p K ω
      + msc A.z * ∑ β, (A.S p β : ℂ) *
          PF.P p (fun ω => (A.G ω β β - msc A.z) * A.G ω p b * K ω) ω
      - msc A.z * ∑ β, (A.S p β : ℂ) * PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω := by
  set m := msc A.z with hm
  have hmz : m * (m + A.z) = -1 := msc_mul A.z
  have hpt : ∀ ω, A.G ω p b * K ω = -m ^ 2 * (A.G ω p b * K ω) +
      (m * (if p = b then 1 else 0)) * K ω + (-m) * ∑ β, A.H ω p β * (A.G ω β b * K ω) := by
    intro ω
    have h := H_mul_G A ω p b
    have e : ∑ β, A.H ω p β * (A.G ω β b * K ω) = (∑ β, A.H ω p β * A.G ω β b) * K ω := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [e, h]
    linear_combination (A.G ω p b * K ω) * hmz
  have hGH : ∀ β, A.Good fun ω => A.H ω p β * (A.G ω β b * K ω) := fun β =>
    A.laws.good_mul _ _ (A.good_H p β) (by good_tac A)
  have hibp : ∀ β, PF.P p (fun ω => A.H ω p β * (A.G ω β b * K ω)) ω =
      (A.S p β : ℂ) * (-PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω +
        PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω) := by
    intro β
    rw [A.ibp p p β (Or.inl rfl) (fun ω => A.G ω β b * K ω) (by test_tac A)]
    beta_reduce
    rw [dh_mul' A β p (test_G A β b) hK, dh_G]
    beta_reduce
    rw [P_add' A (by good_tac A) (by good_tac A), ← P_neg' A (by good_tac A)]
    congr 3
    funext ω
    ring
  have hX : PF.P p (fun ω => A.G ω p b * K ω) ω =
      -m ^ 2 * PF.P p (fun ω => A.G ω p b * K ω) ω + (m * (if p = b then 1 else 0)) *
        PF.P p K ω + (-m) * ∑ β, (A.S p β : ℂ) *
          (-PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω +
            PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω) := by
    conv_lhs => rw [P_congr' hpt p]
    rw [P_add' A (by good_tac A)
        (by exact A.laws.good_mul _ _ (A.laws.good_const _) (good_sum' A _ hGH)),
      P_add' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A),
      P_cmul' A _ (A.test_good _ hK), P_cmul' A _ (good_sum' A _ hGH), P_sum' A _ hGH]
    simp only [hibp]
  have hsplit : ∀ β, PF.P p (fun ω => (A.G ω β β - m) * A.G ω p b * K ω) ω =
      PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω -
        m * PF.P p (fun ω => A.G ω p b * K ω) ω := by
    intro β
    rw [P_congr' (g := fun ω => A.G ω β β * A.G ω p b * K ω - m * (A.G ω p b * K ω))
      (fun ω => by ring), P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A)]
  simp only [hsplit]
  have hs := rowSum' A p
  simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib] at hX ⊢
  rw [← Finset.sum_mul, hs]
  linear_combination hX

/-- The expansion `G_{ap} = m δ_{ap} - m² G_{ap} - m ∑_β G_{aβ} h_{βp}` followed by Gaussian
integration by parts in `P_p` ([I, (3.8)], [I, Lemma 2.4]). -/
theorem ibp_col (p a : ι) {K : Ω → ℂ} (hK : A.Test K) (ω : Ω) :
    PF.P p (fun ω => A.G ω a p * K ω) ω =
      msc A.z * (if a = p then 1 else 0) * PF.P p K ω
      + msc A.z * ∑ β, (A.S p β : ℂ) *
          PF.P p (fun ω => (A.G ω β β - msc A.z) * A.G ω a p * K ω) ω
      - msc A.z * ∑ β, (A.S p β : ℂ) * PF.P p (fun ω => A.G ω a β * A.dh p β K ω) ω := by
  set m := msc A.z with hm
  have hmz : m * (m + A.z) = -1 := msc_mul A.z
  have hpt : ∀ ω, A.G ω a p * K ω = -m ^ 2 * (A.G ω a p * K ω) +
      (m * (if a = p then 1 else 0)) * K ω + (-m) * ∑ β, A.H ω β p * (A.G ω a β * K ω) := by
    intro ω
    have h := G_mul_H A ω a p
    have e : ∑ β, A.H ω β p * (A.G ω a β * K ω) = (∑ β, A.G ω a β * A.H ω β p) * K ω := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [e, h]
    linear_combination (A.G ω a p * K ω) * hmz
  have hGH : ∀ β, A.Good fun ω => A.H ω β p * (A.G ω a β * K ω) := fun β =>
    A.laws.good_mul _ _ (A.good_H β p) (by good_tac A)
  have hibp : ∀ β, PF.P p (fun ω => A.H ω β p * (A.G ω a β * K ω)) ω =
      (A.S p β : ℂ) * (-PF.P p (fun ω => A.G ω β β * A.G ω a p * K ω) ω +
        PF.P p (fun ω => A.G ω a β * A.dh p β K ω) ω) := by
    intro β
    rw [A.ibp p β p (Or.inr rfl) (fun ω => A.G ω a β * K ω) (by test_tac A)]
    beta_reduce
    rw [dh_mul' A p β (test_G A a β) hK, dh_G, S_symm' A β p]
    beta_reduce
    rw [P_add' A (by good_tac A) (by good_tac A), ← P_neg' A (by good_tac A)]
    congr 3
    funext ω
    ring
  have hX : PF.P p (fun ω => A.G ω a p * K ω) ω =
      -m ^ 2 * PF.P p (fun ω => A.G ω a p * K ω) ω + (m * (if a = p then 1 else 0)) *
        PF.P p K ω + (-m) * ∑ β, (A.S p β : ℂ) *
          (-PF.P p (fun ω => A.G ω β β * A.G ω a p * K ω) ω +
            PF.P p (fun ω => A.G ω a β * A.dh p β K ω) ω) := by
    conv_lhs => rw [P_congr' hpt p]
    rw [P_add' A (by good_tac A)
        (by exact A.laws.good_mul _ _ (A.laws.good_const _) (good_sum' A _ hGH)),
      P_add' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A),
      P_cmul' A _ (A.test_good _ hK), P_cmul' A _ (good_sum' A _ hGH), P_sum' A _ hGH]
    simp only [hibp]
  have hsplit : ∀ β, PF.P p (fun ω => (A.G ω β β - m) * A.G ω a p * K ω) ω =
      PF.P p (fun ω => A.G ω β β * A.G ω a p * K ω) ω -
        m * PF.P p (fun ω => A.G ω a p * K ω) ω := by
    intro β
    rw [P_congr' (g := fun ω => A.G ω β β * A.G ω a p * K ω - m * (A.G ω a p * K ω))
      (fun ω => by ring), P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A)]
  simp only [hsplit]
  have hs := rowSum' A p
  simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib] at hX ⊢
  rw [← Finset.sum_mul, hs]
  linear_combination hX

omit [Fintype ι] [DecidableEq ι] in
theorem Q_apply' (x : ι) (f : Ω → ℂ) (ω : Ω) :
    PF.op .Q x f ω = f ω - PF.P x f ω := rfl

end Aux

/-! ## Factors of components under the model relations -/

/-- A component without minor that is not a `(G_{xx})⁻¹` or `W_D` weight. -/
def basB {V : Type*} (c : Comp V) : Bool :=
  c.minor.isEmpty &&
    match c.kind with
    | .inv _ | .wD _ _ => false
    | _ => true

theorem basB_map {V W : Type*} (f : V → W) (c : Comp V) : basB (c.map f) = basB c := by
  simp [basB, Comp.map]

theorem basB_of_plain {V : Type*} {c : Comp V} (h : c.isPlainB = true) :
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

theorem Gm_eq (ω : Ω) (a b : ι) : (D ω).Gm ∅ a b = A.G ω a b := by
  rw [A.data_G]
  rfl

theorem m_eq (ω : Ω) : (D ω).m = msc A.z := A.data_m ω

theorem S_eq (ω : Ω) (a b : ι) : (D ω).S a b = (A.S a b : ℂ) := by
  rw [A.data_S]
  rfl

theorem val_G {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.G ch) x y) = ch.apply (A.G ω (σ x) (σ y)) := by
  simp [mkC, Comp.val, Gm_eq A]

theorem val_weight {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.weight ch) x y) = ch.apply (A.G ω (σ x) (σ x)) := by
  simp [mkC, Comp.val, Gm_eq A]

theorem val_light {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.light ch) x y) = ch.apply (A.G ω (σ x) (σ x) - msc A.z) := by
  simp [mkC, Comp.val, Gm_eq A, m_eq A]

theorem val_s {V : Type*} (σ : V → ι) (ω : Ω) (x y : V) :
    Comp.val (D ω) σ (mkC (.waved .s) x y) = (A.S (σ x) (σ y) : ℂ) := by
  simp [mkC, Comp.val, S_eq A]

theorem val_solid {V : Type*} [DecidableEq V] (σ : V → ι) (ω : Ω) (ch : Charge)
    (x y : V) : Comp.val (D ω) σ (solidC ch x y) = ch.apply (A.G ω (σ x) (σ y)) := by
  rw [val_solidC, Gm_eq A]

theorem dh_G' (a b x y : ι) :
    A.dh a b (fun ω => A.G ω x y) = fun ω => -(A.G ω x a * A.G ω b y) :=
  A.dh_green a b x y

theorem dh_starG' (a b x y : ι) :
    A.dh a b (fun ω => star (A.G ω x y)) = fun ω => -(star (A.G ω x b) * star (A.G ω a y)) :=
  A.dh_conj_green a b x y

/-- The factor of a random component without minor is a test function. -/
theorem val_test {V : Type*} (σ : V → ι) (c : Comp V) (hb : basB c = true)
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
theorem rv_test {V : Type*} (σ : V → ι) (cs : List (Comp V))
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
theorem dPieces_spec {V : Type*} [DecidableEq V] (σ : V → ι) (p q : V) (c : Comp V)
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

theorem dv_rand {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} (D₀ : Data ι)
    (σ : V → ι) (ps : List (Comp V)) (h : ∀ c ∈ ps, c.kind.isRandom = true) : dv D₀ σ ps = 1 := by
  induction ps with
  | nil => rfl
  | cons c ps ih =>
    rw [dv_cons, ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]
    simp [h c (List.mem_cons_self ..)]

theorem dTerms_cons {V : Type*} [DecidableEq V] (p q : V) (c : Comp V)
    (cs : List (Comp V)) :
    dTerms p q (c :: cs) =
      ((c.dPieces p q).map fun ps => cs ++ ps).toList ++ (dTerms p q cs).map (c :: ·) := by
  unfold dTerms
  erw [List.finRange_succ]
  rw [List.filterMap_cons, List.filterMap_map, List.map_filterMap]
  cases h : c.dPieces p q <;> simp [h, Option.map_map, Function.comp_def]

theorem dPieces_none {V : Type*} [DecidableEq V] (p q : V) (c : Comp V)
    (hb : basB c = true) (hr : c.kind.isRandom = false) : c.dPieces p q = none := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> simp_all [Comp.dPieces, Kind.isRandom]

section DTerms

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-- The product rule behind `dTerms`: the sum of the random parts of the graphs of
`dTerms p q cs` is `-∂_{h_{pq}}` of the random part of `cs`; the deterministic parts are those
of `cs`. -/
theorem dTerms_spec {V : Type*} [DecidableEq V] (σ : V → ι) (p q : V)
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

section ProdRule

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-- The product rule over a list whose entries have distinct keys: each factor differentiated
in turn, the others kept. -/
theorem dh_prod_rule {β : Type*} (a b : ι) (key : β → ℕ) (M : List β)
    (hM : (M.map key).Nodup) (f : β → Ω → ℂ) (hf : ∀ q ∈ M, A.Test (f q)) :
    A.dh a b (fun ω => (M.map fun q => f q ω).prod) = fun ω =>
      (M.map fun q => A.dh a b (f q) ω *
        (M.map fun q' => if key q' = key q then 1 else f q' ω).prod).sum := by
  induction M with
  | nil =>
    funext ω
    simpa using congrFun (A.dh_const a b 1) ω
  | cons q₀ M ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hM
    obtain ⟨hq₀, hM⟩ := hM
    have hf' : ∀ q ∈ M, A.Test (f q) := fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have h1 : (fun ω => ((q₀ :: M).map fun q => f q ω).prod) =
        fun ω => f q₀ ω * (M.map fun q => f q ω).prod := by
      funext ω; simp
    rw [h1, dh_mul' A a b (hf q₀ (List.mem_cons_self ..)) (test_listProd' A M hf'), ih hM hf']
    funext ω
    have hne : ∀ q ∈ M, key q ≠ key q₀ := fun q hq h => hq₀ ⟨q, hq, h⟩
    have h2 : (M.map fun q' => if key q' = key q₀ then 1 else f q' ω) = M.map fun q => f q ω :=
      List.map_congr_left fun q hq => by simp [hne q hq]
    have h3 : ∀ q ∈ M, (if key q₀ = key q then 1 else f q₀ ω) = f q₀ ω := fun q hq => by
      simp [Ne.symm (hne q hq)]
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ite_true, h2, one_mul]
    congr 1
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    rw [h3 q hq]
    ring

end ProdRule

/-! ## Components by position -/

section Zip

variable {α : Type*}

theorem zip_snd_nodup (l : List α) : (l.zipIdx.map Prod.snd).Nodup := by
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' ..

theorem zip_eq_of_snd {l : List α} {p p' : α × ℕ} (hp : p ∈ l.zipIdx)
    (hp' : p' ∈ l.zipIdx) (h : p.2 = p'.2) : p = p' := by
  rw [List.mem_zipIdx_iff_getElem?] at hp hp'
  rw [h, hp'] at hp
  exact Prod.ext (Option.some.inj hp).symm h

theorem mem_zip_of_get {l : List α} {i : ℕ} {a : α} (h : l[i]? = some a) :
    (a, i) ∈ l.zipIdx :=
  List.mem_zipIdx_iff_getElem?.2 h

theorem mem_filter_snd {l : List α} {P : α × ℕ → Bool} {p : α × ℕ} (hp : p ∈ l.zipIdx) :
    p.2 ∈ (l.zipIdx.filter P).map Prod.snd ↔ P p = true := by
  constructor
  · intro h
    obtain ⟨q, hq, hqp⟩ := List.mem_map.1 h
    rw [List.mem_filter] at hq
    rw [zip_eq_of_snd hp hq.1 hqp.symm]
    exact hq.2
  · intro h
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, h⟩, rfl⟩

theorem contains_filter_snd {l : List α} {P : α × ℕ → Bool} {p : α × ℕ}
    (hp : p ∈ l.zipIdx) : ((l.zipIdx.filter P).map Prod.snd).contains p.2 = P p := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_filter_snd hp]

theorem eraseIdx_eq_filter (l : List α) (i : ℕ) :
    l.eraseIdx i = (l.zipIdx.filter fun p => p.2 != i).map Prod.fst := by
  suffices h : ∀ (l : List α) (k i : ℕ),
      ((l.zipIdx k).filter fun p => p.2 != i + k).map Prod.fst = l.eraseIdx i by
    simpa using (h l 0 i).symm
  intro l
  induction l with
  | nil => intro k i; rfl
  | cons a l ih =>
    intro k i
    cases i with
    | zero =>
      simp only [List.zipIdx_cons, Nat.zero_add, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ite_false, List.eraseIdx_cons_zero]
      rw [List.filter_eq_self.2, List.zipIdx_map_fst]
      intro p hp
      have := List.le_snd_of_mem_zipIdx hp
      simp only [bne_iff_ne, ne_eq]
      omega
    | succ i =>
      simp only [List.zipIdx_cons, List.filter_cons, List.eraseIdx_cons_succ]
      have hne : (k != i + 1 + k) = true := by simp
      rw [ite_eq_left hne, List.map_cons]
      congr 1
      rw [← ih (k + 1) i]
      congr 2
      funext p
      congr 1
      omega

theorem prod_ite_single {M : Type*} [CommMonoid M] (l : List (α × ℕ))
    (hl : (l.map Prod.snd).Nodup) (g : α × ℕ → M) {p : α × ℕ} (hp : p ∈ l) :
    (l.map fun p' => if p'.2 = p.2 then g p' else 1).prod = g p := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    obtain ⟨hq, hl⟩ := hl
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [ite_eq_left rfl]
      have : (l.map fun p' => if p'.2 = p.2 then g p' else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun p' hp' => ite_eq_right fun h => hq ⟨p', hp', h⟩
      rw [this]
      simp
    · have hne : q.2 ≠ p.2 := fun h => hq ⟨p, hp, h.symm⟩
      rw [ite_eq_right hne, ih hl hp, one_mul]

theorem prod_single_out {M : Type*} [CommMonoid M] (l : List (α × ℕ))
    (hl : (l.map Prod.snd).Nodup) (g : α × ℕ → M) {p : α × ℕ} (hp : p ∈ l) :
    (l.map g).prod = g p * (l.map fun p' => if p'.2 = p.2 then 1 else g p').prod := by
  rw [← prod_ite_single l hl g hp, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun p' _ => ?_
  split_ifs <;> simp

theorem sum_filter_snd {M : Type*} [AddCommMonoid M] (l : List (α × ℕ))
    (P : α × ℕ → Bool) (h : ℕ → M) :
    (((l.filter P).map Prod.snd).map h).sum = (l.map fun p => if P p then h p.2 else 0).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q
    · rw [List.filter_cons_of_pos hq]
      simp only [List.map_cons, List.sum_cons, hq, ite_true, ih]
    · rw [List.filter_cons_of_neg hq]
      simp only [List.map_cons, List.sum_cons, hq, Bool.false_eq_true, ite_false, ih, zero_add]

end Zip

section ZipVal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*}

theorem rv_zfilter (D₀ : Data ι) (σ : V → ι) (l : List (Comp V × ℕ))
    (P : Comp V × ℕ → Bool) :
    rv D₀ σ ((l.filter P).map Prod.fst) =
      (l.map fun p => if P p && p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q <;> by_cases hr : q.1.kind.isRandom <;> simp [hq, hr, ih]

theorem dv_zfilter (D₀ : Data ι) (σ : V → ι) (l : List (Comp V × ℕ))
    (P : Comp V × ℕ → Bool) :
    dv D₀ σ ((l.filter P).map Prod.fst) =
      (l.map fun p => if P p && !p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q <;> by_cases hr : q.1.kind.isRandom <;> simp [hq, hr, ih]

theorem rv_zip (D₀ : Data ι) (σ : V → ι) (l : List (Comp V)) :
    rv D₀ σ l =
      (l.zipIdx.map fun p => if p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  have h := rv_zfilter D₀ σ l.zipIdx fun _ => true
  rw [List.filter_true, List.zipIdx_map_fst] at h
  simpa using h

theorem dv_zip (D₀ : Data ι) (σ : V → ι) (l : List (Comp V)) :
    dv D₀ σ l =
      (l.zipIdx.map fun p => if !p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  have h := dv_zfilter D₀ σ l.zipIdx fun _ => true
  rw [List.filter_true, List.zipIdx_map_fst] at h
  simpa using h

end ZipVal

/-! ## Values of tracked formal sums, one labelling of the input atoms at a time -/

section Sums

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) {k n : ℕ}
  (e : Fin k → ι) (ω : Ω)

/-- The tracked graph with one new atom. -/
def t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
  ⟨n + 1, ⟨cs, d⟩, liftA 1⟩

/-- The value of a tracked formal sum. -/
def S (E : TExpansion k n) : ℂ := E.forget.valR PF D e ω

/-- The term of a graph at the labelling `s` of the internal atoms. -/
def T0 (g : Graph k n) (s : Fin n → ι) : ℂ := g.termR PF D (Sum.elim e s) ω

/-- The terms of a graph with one new atom at the labelling `s` of the internal atoms of the input
graph, summed over the label of the new atom. -/
def T1 (g : Graph k (n + 1)) (s : Fin n → ι) : ℂ :=
  ∑ α, g.termR PF D (Sum.elim e (Fin.append s ![α])) ω

theorem S_append (E₁ E₂ : TExpansion k n) :
    S PF D e ω (E₁ ++ E₂) = S PF D e ω E₁ + S PF D e ω E₂ := by
  simp [S, TExpansion.forget, Expansion.valR]

theorem S_nil : S PF D e ω ([] : TExpansion k n) = 0 := by
  simp [S, TExpansion.forget, Expansion.valR]

theorem S_cons (t : Tracked k n) (E : TExpansion k n) :
    S PF D e ω (t :: E) = t.g.valR PF D e ω + S PF D e ω E := by
  simp [S, TExpansion.forget, Expansion.valR]

theorem S_ite (b : Prop) [Decidable b] (E : TExpansion k n) :
    S PF D e ω (if b then [] else E) = if b then 0 else S PF D e ω E := by
  by_cases hb : b <;> simp [hb, S_nil]

omit [DecidableEq ι] in
theorem ite_sum (b : Prop) [Decidable b] (f : (Fin n → ι) → ℂ) :
    (if b then 0 else ∑ s, f s) = ∑ s, if b then 0 else f s := by
  by_cases hb : b <;> simp [hb]

theorem valR_T0 (g : Graph k n) : g.valR PF D e ω = ∑ s, T0 PF D e ω g s := rfl

theorem valR_T1 (g : Graph k (n + 1)) : g.valR PF D e ω = ∑ s, T1 PF D e ω g s := by
  rw [valR_splitN]
  exact Finset.sum_congr rfl fun s _ => sum_fin1 _

omit [DecidableEq ι] in
theorem list_sum_comm {β : Type*} (l : List β) (f : β → (Fin n → ι) → ℂ) :
    (l.map fun j => ∑ s, f j s).sum = ∑ s, (l.map fun j => f j s).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.sum_add_distrib]

theorem S_map_t1 {β : Type*} (l : List β) (G : β → List (Comp (Atom k (n + 1))))
    (d : β → Coeff) :
    S PF D e ω (l.map fun j => t1 (G j) (d j)) =
      ∑ s, (l.map fun j => T1 PF D e ω ⟨G j, d j⟩ s).sum := by
  rw [← list_sum_comm]
  simp [S, TExpansion.forget, Expansion.valR, t1, List.map_map, Function.comp_def, valR_T1]

theorem S_t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) :
    S PF D e ω [t1 cs d] = ∑ s, T1 PF D e ω ⟨cs, d⟩ s := by
  simp [S, TExpansion.forget, Expansion.valR, t1, valR_T1]

theorem S_cons_t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) (E : TExpansion k n) :
    S PF D e ω (t1 cs d :: E) = ∑ s, T1 PF D e ω ⟨cs, d⟩ s + S PF D e ω E := by
  rw [S_cons, t1, valR_T1]

end Sums

/-! ## Splitting `P_u = 1 - Q_u` -/

/-- A list of components without labels. -/
def Unl {V : Type*} (cs : List (Comp V)) : Prop := ∀ c ∈ cs, c.label = none

theorem Unl_append {V : Type*} {cs cs' : List (Comp V)} :
    Unl (cs ++ cs') ↔ Unl cs ∧ Unl cs' := by
  simp [Unl, or_imp, forall_and]

theorem Unl_liftCs {k n : ℕ} (j : ℕ) {cs : List (Comp (Atom k n))} (h : Unl cs) :
    Unl (liftCs j cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  simp [Comp.map, h c' hc']

theorem Unl_sub {V : Type*} {cs cs' : List (Comp V)} (h : Unl cs) (hs : ∀ c ∈ cs', c ∈ cs) :
    Unl cs' := fun c hc => h c (hs c hc)

/-! ## The graphs of the multi-edge expansion, case (i) -/

section OutDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges attached to `x`, in the order of case (i). -/
def psteps_oXIdx : List ℕ :=
  Γ.edgeIdx x .plus true ++ Γ.edgeIdx x .minus true ++ Γ.edgeIdx x .plus false ++
    Γ.edgeIdx x .minus false

/-- The waved edge `s_{xα}`. -/
def oSx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0)

/-- The solid edge `G_{α y₁}`. -/
def oGy : Comp (Atom k (n + 1)) := mkC (.G .plus) (newA 0) (liftA 1 e₁.y)

/-- A main term of [I, (3.13)] for the edge `Ḡ_{x y'}` at position `j`: the components other than
`G_{x y₁}` and `Ḡ_{x y'}`, and `s_{xα} G_{α y₁} Ḡ_{α y'}`. -/
def oBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ((Γ.comps.getD j e₁).y))]

/-- A main term of [I, (3.13)] for the edge `G_{w x}` at position `j`: the components other than
`G_{x y₁}` and `G_{w x}`, and `s_{xα} G_{α y₁} G_{w α}`. -/
def oBaseP (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, oGy e₁, mkC (.G .plus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The `(k₁ - 1)` term of [I, (3.13)]: the components other than `G_{x y₁}`, and
`s_{xα} G_{xα} G_{α y₁}`. -/
def oE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, mkC (.G .plus) (liftA 1 x) (newA 0), oGy e₁]

/-- The `k₄` term of [I, (3.13)]: the components other than `G_{x y₁}`, and
`s_{xα} Ḡ_{αx} G_{α y₁}`. -/
def oE2 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, mkC (.G .minus) (newA 0) (liftA 1 x), oGy e₁]

/-- The term `s_{xα} (G_{αα} - m) 𝒢` of [I, (3.13)] and [I, (3.14)]. -/
def oL3 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 Γ.comps ++ [oSx x, mkC (.light .plus) (newA 0) (newA 0)]

/-- The derivative terms of [I, (3.13)]: the edges at `x` other than `G_{x y₁}`, one graph of
`-∂_{h_{αx}}` of the other components, and `s_{xα} G_{α y₁}`. -/
def oDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (psteps_oXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((psteps_oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [oSx x, oGy e₁]

/-- The formal sum of `multiEOut`. -/
def psteps_oOut : TExpansion k n :=
  (Γ.edgeIdx x .minus true).map (fun j => t1 (oBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => t1 (oBaseP x Γ i₁ e₁ j) (cm * cm * Γ.coeff)) ++
    (Γ.edgeIdx x .minus true).map (fun j => t1 (oBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => t1 (oBaseP x Γ i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [t1 (oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [t1 (oE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (if (Γ.edgeIdx x .minus false).length = 0 then [] else
      [t1 (oE2 x Γ i₁ e₁) (((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)]) ++
    (oDs x Γ i₁ e₁).map (fun d => t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus true).map (fun j => t1 (labelQs (liftA 1 x) (oBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => t1 (labelQs (liftA 1 x) (oBaseP x Γ i₁ e₁ j ++
      [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [t1 (labelQs (liftA 1 x) (oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [t1 (labelQs (liftA 1 x) (oE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (if (Γ.edgeIdx x .minus false).length = 0 then [] else
      [t1 (labelQs (liftA 1 x) (oE2 x Γ i₁ e₁))
        (-((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)]) ++
    (oDs x Γ i₁ e₁).map (fun d => t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

theorem multiEOut_some {E : TExpansion k n} (h : multiEOut x Γ = some E) :
    ∃ i₁ is₂ e₁, Γ.edgeIdx x .plus true = i₁ :: is₂ ∧ Γ.comps[i₁]? = some e₁ ∧
      Γ.xdotsAt x (psteps_oXIdx x Γ) = true ∧ E = psteps_oOut x Γ i₁ is₂ e₁ := by
  unfold multiEOut at h
  split at h
  · exact absurd h (by simp)
  rename_i i₁ is₂ hOP
  split at h
  · exact absurd h (by simp)
  rename_i e₁ hL
  dsimp only at h
  rw [ite_eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨hX, h⟩
  · exact absurd h (by simp)
  refine ⟨i₁, is₂, e₁, hOP, hL, by simpa [psteps_oXIdx] using hX, ?_⟩
  exact (Option.some.inj h).symm

end OutDefs

section LiftVal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n j : ℕ} (D₀ : Data ι)

theorem rv_liftCs (σ : Atom k (n + j) → ι) (cs : List (Comp (Atom k n))) :
    rv D₀ σ (liftCs j cs) = rv D₀ (σ ∘ liftA j) cs := rv_map _ _ _ _

theorem dv_liftCs (σ : Atom k (n + j) → ι) (cs : List (Comp (Atom k n))) :
    dv D₀ σ (liftCs j cs) = dv D₀ (σ ∘ liftA j) cs := dv_map _ _ _ _

end LiftVal

theorem fst_mem_of_zip {α : Type*} {l : List α} {p : α × ℕ} (h : p ∈ l.zipIdx) :
    p.1 ∈ l :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 h)

theorem mem_eraseIdxs {α : Type*} {is : List ℕ} {l : List α} {a : α}
    (h : a ∈ eraseIdxs is l) : a ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact fst_mem_of_zip (List.mem_filter.1 hp).1

theorem mem_pickIdxs {α : Type*} {is : List ℕ} {l : List α} {a : α}
    (h : a ∈ pickIdxs is l) : a ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact fst_mem_of_zip (List.mem_filter.1 hp).1

theorem ceval_cm (z : ℂ) : Coeff.eval z cm = z := by simp [Coeff.eval, cm, CVar.eval]

theorem ceval_cmb (z : ℂ) : Coeff.eval z cmb = star z := by
  simp [Coeff.eval, cmb, CVar.eval]

theorem ceval_mul (z : ℂ) (p q : Coeff) :
    Coeff.eval z (p * q) = Coeff.eval z p * Coeff.eval z q := by
  simp [Coeff.eval]

theorem ceval_nat (z : ℂ) (a : ℕ) : Coeff.eval z (a : Coeff) = a := by
  simp [Coeff.eval]


theorem plain_Unl {k n : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.isPlainB = true) : Unl cs := fun c hc => (basB_of_plain (h c hc)).2

theorem plain_bas_lift {k n : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.isPlainB = true) (j : ℕ) :
    ∀ c ∈ liftCs j cs, basB c = true ∧ c.label = none := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2⟩ := basB_of_plain (h c' hc')
  exact ⟨by rw [basB_map]; exact h1, by simp [Comp.map, h2]⟩

/-! ## Solid edges at `x` by position -/

section EdgePos

variable {k n : ℕ} (x : Atom k n)

/-- The filter of `Graph.edgeIdx`. -/
def ep (ch : Charge) (out : Bool) : Comp (Atom k n) × ℕ → Bool := fun p =>
  p.1.kind == .G ch && (if out then p.1.x == x && p.1.y != x else p.1.y == x && p.1.x != x)

theorem edgeIdx_eq (Γ : Graph k n) (ch : Charge) (out : Bool) :
    Γ.edgeIdx x ch out = (Γ.comps.zipIdx.filter (ep x ch out)).map Prod.snd := rfl

/-- The component at a position is a solid edge attached to `x` (self-loops excluded). -/
def cX (p : Comp (Atom k n) × ℕ) : Bool :=
  ep x .plus true p || ep x .minus true p || ep x .plus false p || ep x .minus false p

theorem ep_spec {ch : Charge} {out : Bool} {p : Comp (Atom k n) × ℕ}
    (h : ep x ch out p = true) :
    p.1.kind = .G ch ∧ (out = true → p.1.x = x ∧ p.1.y ≠ x) ∧
      (out = false → p.1.y = x ∧ p.1.x ≠ x) := by
  unfold ep at h
  cases out <;> simp_all

theorem cX_random {p : Comp (Atom k n) × ℕ} (h : cX x p = true) :
    p.1.kind.isRandom = true := by
  unfold cX at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h <;> rw [(ep_spec x h).1] <;> rfl

theorem cX_of_ep {ch : Charge} {out : Bool} {p : Comp (Atom k n) × ℕ}
    (h : ep x ch out p = true) : cX x p = true := by
  unfold cX
  cases ch <;> cases out <;> simp [h]

/-- At most one of the four filters holds. -/
theorem ep_excl {p : Comp (Atom k n) × ℕ} {ch ch' : Charge} {out out' : Bool}
    (h : ep x ch out p = true) (h' : ep x ch' out' p = true) : ch = ch' ∧ out = out' := by
  obtain ⟨k1, o1, i1⟩ := ep_spec x h
  obtain ⟨k2, o2, i2⟩ := ep_spec x h'
  rw [k1] at k2
  refine ⟨by injection k2, ?_⟩
  cases out <;> cases out'
  · rfl
  · exact absurd (o2 rfl).1 (i1 rfl).2
  · exact absurd (o1 rfl).1 (i2 rfl).2
  · rfl

theorem contains_oXIdx (Γ : Graph k n) {p : Comp (Atom k n) × ℕ}
    (hp : p ∈ Γ.comps.zipIdx) : (psteps_oXIdx x Γ).contains p.2 = cX x p := by
  simp only [psteps_oXIdx, edgeIdx_eq, List.contains_append, contains_filter_snd hp, cX]

end EdgePos

/-! ## Products over the components, with the solid edges at `x` singled out -/

section EdgeProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} (cP : Comp (Atom k n) × ℕ → Bool)
  (Γ : Graph k n) (i₁ : ℕ) (σ : Atom k n → ι)

/-- The factor at a position of the edges selected by `cP`, the edge at `i₁` excepted. -/
def kx (D₀ : Data ι) (p : Comp (Atom k n) × ℕ) : ℂ :=
  if cP p && p.2 != i₁ then Comp.val D₀ σ p.1 else 1

/-- The product of the edges selected by `cP`, the edge at `i₁` excepted. -/
def Kx (D₀ : Data ι) : ℂ := (Γ.comps.zipIdx.map (kx cP i₁ σ D₀)).prod

/-- The product of the edges selected by `cP`, the edges at `i₁` and `j` excepted. -/
def Kxq (D₀ : Data ι) (j : ℕ) : ℂ :=
  (Γ.comps.zipIdx.map fun p => if p.2 = j then 1 else kx cP i₁ σ D₀ p).prod

/-- `Kx` with the factor at `q` singled out. -/
theorem Kx_single (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx) :
    Kx cP Γ i₁ σ D₀ = kx cP i₁ σ D₀ q * Kxq cP Γ i₁ σ D₀ q.2 :=
  prod_single_out _ (zip_snd_nodup _) _ hq

variable {cP Γ i₁} {xI : List ℕ} {e₁ : Comp (Atom k n)}
  (hxI : ∀ p ∈ Γ.comps.zipIdx, xI.contains p.2 = cP p)
  (hcR : ∀ p, cP p = true → p.1.kind.isRandom = true)
  (he : (e₁, i₁) ∈ Γ.comps.zipIdx) (hce : cP (e₁, i₁) = true)

include hxI hcR he hce in
theorem gR1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ * (Kx cP Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs xI Γ.comps)) := by
  rw [rv_zip, Kx, eraseIdxs, rv_zfilter,
    ← prod_ite_single _ (zip_snd_nodup _) (fun p => Comp.val D₀ σ p.1) he,
    ← List.prod_map_mul, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp, kx]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hce, hcR _ hce]
  · by_cases hc : cP p = true
    · simp [hc, hcR _ hc, h1]
    · simp [hc, h1]

include hxI hcR he hce in
theorem gR2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) = Kx cP Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs xI Γ.comps) := by
  rw [eraseIdx_eq_filter, rv_zfilter, Kx, eraseIdxs, rv_zfilter, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp, kx]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hce]
  · by_cases hc : cP p = true
    · simp [hc, hcR _ hc, h1]
    · simp [hc, h1]

include hxI hcR he hce in
theorem gR3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cP q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq cP Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs xI Γ.comps) := by
  rw [eraseIdxs, rv_zfilter, Kxq, eraseIdxs, rv_zfilter, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp, kx]
  by_cases h2 : p.2 = q.2
  · obtain rfl := zip_eq_of_snd hp hq h2
    simp [hqc]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hce]
  · by_cases hc : cP p = true
    · simp [hc, hcR _ hc, h1, h2]
    · simp [hc, h1, h2]

include hxI hcR in
theorem gR4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs (xI.filter (· != i₁)) Γ.comps) = Kx cP Γ i₁ σ D₀ := by
  rw [pickIdxs, rv_zfilter, Kx]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  have hcont : (xI.filter (· != i₁)).contains p.2 = (cP p && p.2 != i₁) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter, ← List.contains_iff_mem,
      hxI p hp]
    simp
  rw [hcont, kx]
  by_cases hc : cP p = true
  · simp [hc, hcR _ hc]
  · simp [hc]

include hcR he hce in
theorem gD1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps := by
  rw [eraseIdx_eq_filter, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hcR _ hce]
  · simp [h1]

include hcR he hce in
theorem gD3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cP q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps := by
  rw [eraseIdxs, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  by_cases h2 : p.2 = q.2
  · obtain rfl := zip_eq_of_snd hp hq h2
    simp [hcR _ hqc]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hcR _ hce]
  · simp [h1, h2]

include hxI hcR in
theorem gD4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs xI Γ.comps) = dv D₀ σ Γ.comps := by
  rw [eraseIdxs, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp]
  by_cases hc : cP p = true
  · simp [hc, hcR _ hc]
  · simp [hc]

include hxI hcR in
theorem gD5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs (xI.filter (· != i₁)) Γ.comps) = 1 := by
  rw [pickIdxs, dv_zfilter]
  refine List.prod_eq_one fun a ha => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  have hcont : (xI.filter (· != i₁)).contains p.2 = (cP p && p.2 != i₁) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter, ← List.contains_iff_mem,
      hxI p hp]
    simp
  rw [hcont]
  by_cases hc : cP p = true
  · simp [hc, hcR _ hc]
  · simp [hc]

end EdgeProd

/-! ## Case (i): the products over the components -/

section OutProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
  {i₁ : ℕ} (σ : Atom k n → ι) {is₂ : List ℕ} {e₁ : Comp (Atom k n)}

omit [Fintype ι] [DecidableEq ι] in
theorem out_hxI : ∀ p ∈ Γ.comps.zipIdx, (psteps_oXIdx x Γ).contains p.2 = cX x p :=
  fun _ hp => contains_oXIdx x Γ hp

variable (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂) (hL : Γ.comps[i₁]? = some e₁)
include hOP hL

omit [Fintype ι] [DecidableEq ι] hOP in
theorem e₁_mem : (e₁, i₁) ∈ Γ.comps.zipIdx := mem_zip_of_get hL

omit [Fintype ι] [DecidableEq ι] in
theorem e₁_ep : ep x .plus true (e₁, i₁) = true := by
  have h : i₁ ∈ Γ.edgeIdx x .plus true := by rw [hOP]; exact List.mem_cons_self ..
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (e₁_mem hL)).1 h

theorem out_R1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ *
      (Kx (cX x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps)) :=
  gR1 σ out_hxI (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀

theorem out_R2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) =
      Kx (cX x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) :=
  gR2 σ out_hxI (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀

theorem out_R3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cX x q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq (cX x) Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) :=
  gR3 σ out_hxI (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀ hq hqc

theorem out_D1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps :=
  gD1 σ (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀

theorem out_D3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cX x q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps :=
  gD3 σ (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀ hq hqc

omit hOP hL in
theorem out_R4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs ((psteps_oXIdx x Γ).filter (· != i₁)) Γ.comps) = Kx (cX x) Γ i₁ σ D₀ :=
  gR4 σ out_hxI (fun _ h => cX_random x h) D₀

omit hOP hL in
theorem out_D4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) = dv D₀ σ Γ.comps :=
  gD4 σ out_hxI (fun _ h => cX_random x h) D₀

omit hOP hL in
theorem out_D5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs ((psteps_oXIdx x Γ).filter (· != i₁)) Γ.comps) = 1 :=
  gD5 σ out_hxI (fun _ h => cX_random x h) D₀

end OutProd

/-! ## Case (i): `-∂_{h_{αx}}` of the edges at `x` -/

section OutDeriv

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n} (σ : Atom k n → ι)

theorem getD_of_zip {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (d : Comp (Atom k n)) : Γ.comps.getD p.2 d = p.1 := by
  rw [List.getD_eq_getElem?_getD, List.mem_zipIdx_iff_getElem?.1 hp]
  rfl

/-- The factor of a solid edge without minor. -/
theorem val_edge {c : Comp (Atom k n)} (hc : c.isPlainB = true) {ch : Charge}
    (hk : c.kind = .G ch) (ω : Ω) :
    Comp.val (D ω) σ c = ch.apply (A.G ω (σ c.x) (σ c.y)) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only [Comp.isPlainB, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨⟨rfl, _⟩, _⟩ := hc
  simp only at hk
  subst hk
  exact val_G A σ ω ch a b

theorem fun_edge {c : Comp (Atom k n)} (hc : c.isPlainB = true) {ch : Charge}
    (hk : c.kind = .G ch) :
    (fun ω => Comp.val (D ω) σ c) = fun ω => ch.apply (A.G ω (σ c.x) (σ c.y)) :=
  funext fun ω => val_edge A σ hc hk ω

theorem dh_OP {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus true p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(A.G ω (σ x) β * Comp.val (D ω) σ p.1) := by
  obtain ⟨hk, ho, -⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (ho rfl).1, val_edge A σ hc hk]

theorem dh_OM {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus true p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(star (A.G ω (σ x) (σ x)) * star (A.G ω β (σ p.1.y))) := by
  obtain ⟨hk, ho, -⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (ho rfl).1]

theorem dh_IP {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus false p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(A.G ω (σ p.1.x) β * A.G ω (σ x) (σ x)) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (hi rfl).1]

theorem dh_IM {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus false p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(Comp.val (D ω) σ p.1 * star (A.G ω β (σ x))) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (hi rfl).1, val_edge A σ hc hk]

theorem kx_test (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true)
    {cP : Comp (Atom k n) × ℕ → Bool} (hcR : ∀ p, cP p = true → p.1.kind.isRandom = true)
    (i₁ : ℕ) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx) :
    A.Test fun ω => kx cP i₁ σ (D ω) p := by
  unfold kx
  by_cases hb : (cP p && p.2 != i₁) = true
  · simp only [hb, ite_true]
    have hc := Bool.and_eq_true_iff.1 hb
    exact val_test A σ p.1 (basB_of_plain (hpl _ (fst_mem_of_zip hp))).1 (hcR _ hc.1)
  · simp only [hb]
    exact test_const' A 1

theorem dh_kx (cP : Comp (Atom k n) × ℕ → Bool) (i₁ : ℕ) (p : Comp (Atom k n) × ℕ)
    (a b : ι) :
    A.dh a b (fun ω => kx cP i₁ σ (D ω) p) =
      if (cP p && p.2 != i₁) = true then A.dh a b (fun ω => Comp.val (D ω) σ p.1) else 0 := by
  unfold kx
  by_cases hb : (cP p && p.2 != i₁) = true
  · simp only [hb, ite_true]
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact A.dh_const a b 1

theorem ep_false {p : Comp (Atom k n) × ℕ} {ch ch' : Charge} {out out' : Bool}
    (h : ep x ch out p = true) (hne : ¬ (ch = ch' ∧ out = out')) : ep x ch' out' p = false := by
  by_contra h'
  exact hne (ep_excl x h (by simpa using h'))

/-- The term of `-∂_{h_{βx}}` at one position, times the other factors, sorted into the four
families of [I, (3.13)]. -/
theorem out_PP (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (β : ι) (ω : Ω) :
    -(A.dh β (σ x) (fun ω => kx (cX x) i₁ σ (D ω) p) ω) * Kxq (cX x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) * A.G ω β (σ e₁.y) =
      (if ep x .minus true p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω β (σ e₁.y) * star (A.G ω β (σ (Γ.comps.getD p.2 e₁).y))) *
          star (A.G ω (σ x) (σ x)) else 0) +
      (if ep x .plus false p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω β (σ e₁.y) * A.G ω (σ (Γ.comps.getD p.2 e₁).x) β) *
          A.G ω (σ x) (σ x) else 0) +
      (if (ep x .plus true p && p.2 != i₁) = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (A.G ω (σ x) β * A.G ω β (σ e₁.y)) else 0) +
      (if ep x .minus false p = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (star (A.G ω β (σ x)) * A.G ω β (σ e₁.y)) else 0) := by
  have hplp := hpl _ (fst_mem_of_zip hp)
  rw [dh_kx A σ (cX x) i₁ p]
  by_cases hb : (cX x p && p.2 != i₁) = true
  · rw [ite_eq_left hb]
    obtain ⟨hc, hne⟩ := Bool.and_eq_true_iff.1 hb
    have hne' : p.2 ≠ i₁ := by simpa using hne
    have hK := Kx_single (cX x) Γ i₁ σ (D ω) hp
    rw [kx, ite_eq_left hb] at hK
    have hgd := getD_of_zip hp e₁
    simp only [cX, Bool.or_eq_true] at hc
    rcases hc with ((h | h) | h) | h
    · rw [dh_OP A σ hplp h, out_R2 σ hOP hL, hK,
        ep_false h (ch' := .minus) (out' := true) (by simp),
        ep_false h (ch' := .plus) (out' := false) (by simp),
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, hne, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
      ring
    · rw [dh_OM A σ hplp h, out_R3 σ hOP hL (D ω) hp (cX_of_ep x h), hgd,
        ep_false h (ch' := .plus) (out' := false) (by simp),
        ep_false h (ch' := .plus) (out' := true) (by simp),
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
    · rw [dh_IP A σ hplp h, out_R3 σ hOP hL (D ω) hp (cX_of_ep x h), hgd,
        ep_false h (ch' := .minus) (out' := true) (by simp),
        ep_false h (ch' := .plus) (out' := true) (by simp),
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
    · rw [dh_IM A σ hplp h, out_R2 σ hOP hL, hK,
        ep_false h (ch' := .minus) (out' := true) (by simp),
        ep_false h (ch' := .plus) (out' := false) (by simp),
        ep_false h (ch' := .plus) (out' := true) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
  · rw [ite_eq_right hb]
    have h1 : ep x .minus true p = false := by
      by_contra h
      have h' : ep x .minus true p = true := by simpa using h
      apply hb
      rw [cX_of_ep x h', Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (e₁_mem hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (e₁_ep hOP hL)).1 (by simp)
    have h2 : ep x .plus false p = false := by
      by_contra h
      have h' : ep x .plus false p = true := by simpa using h
      apply hb
      rw [cX_of_ep x h', Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (e₁_mem hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (e₁_ep hOP hL)).2 (by simp)
    have h3 : ep x .minus false p = false := by
      by_contra h
      have h' : ep x .minus false p = true := by simpa using h
      apply hb
      rw [cX_of_ep x h', Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (e₁_mem hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (e₁_ep hOP hL)).1 (by simp)
    have h4 : (ep x .plus true p && p.2 != i₁) = false := by
      by_contra h
      have h' : (ep x .plus true p && p.2 != i₁) = true := by simpa using h
      obtain ⟨h5, h6⟩ := Bool.and_eq_true_iff.1 h'
      exact hb (by rw [cX_of_ep x h5, h6]; rfl)
    simp [h1, h2, h3, h4]

theorem list_sum_neg {β : Type*} (l : List β) (f : β → ℂ) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp [ih]; ring

theorem sum_ite_const {β : Type*} (l : List β) (P : β → Bool) (c : ℂ) :
    (l.map fun p => if P p = true then c else 0).sum = ((l.filter P).length : ℂ) * c := by
  induction l with
  | nil => simp
  | cons q l ih =>
    by_cases hq : P q = true
    · simp [hq, ih]; ring
    · simp [hq, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem len_OP {i₁ : ℕ} {is₂ : List ℕ} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂) :
    (Γ.comps.zipIdx.filter fun p => ep x .plus true p && p.2 != i₁).length = is₂.length := by
  have hnd : (i₁ :: is₂).Nodup := by
    rw [← hOP, edgeIdx_eq]
    exact (zip_snd_nodup Γ.comps).sublist ((List.filter_sublist).map _)
  have h : ((Γ.comps.zipIdx.filter fun p => ep x .plus true p && p.2 != i₁).map Prod.snd) =
      is₂ := by
    have e1 : (Γ.comps.zipIdx.filter fun p => ep x .plus true p && p.2 != i₁) =
        (Γ.comps.zipIdx.filter (ep x .plus true)).filter (fun p => p.2 != i₁) := by
      rw [List.filter_filter]
      congr 1
      funext p
      exact Bool.and_comm _ _
    have e2 : ((Γ.comps.zipIdx.filter (ep x .plus true)).filter (fun p => p.2 != i₁)).map
        Prod.snd = ((Γ.comps.zipIdx.filter (ep x .plus true)).map Prod.snd).filter (· != i₁) := by
      rw [List.filter_map]
      rfl
    rw [e1, e2, ← edgeIdx_eq, hOP]
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
    intro a ha
    have : a ≠ i₁ := fun h => (List.nodup_cons.1 hnd).1 (h ▸ ha)
    simpa using this
  rw [← h, List.length_map]

/-- `G_{β y₁}` times `-∂_{h_{βx}}` of the product of the edges at `x` other than `G_{x y₁}` and of
the rest: the four families of [I, (3.13)] and the derivative terms. -/
theorem out_KEY (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    A.G ω β (σ e₁.y) * -(A.dh β (σ x) (fun ω' => Kx (cX x) Γ i₁ σ (D ω') *
        rv (D ω') σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps)) ω) =
      ((Γ.edgeIdx x .minus true).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω β (σ e₁.y) * star (A.G ω β (σ (Γ.comps.getD j e₁).y))) *
          star (A.G ω (σ x) (σ x))).sum +
      ((Γ.edgeIdx x .plus false).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω β (σ e₁.y) * A.G ω (σ (Γ.comps.getD j e₁).x) β) *
          A.G ω (σ x) (σ x)).sum +
      (is₂.length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ x) β * A.G ω β (σ e₁.y))) +
      ((Γ.edgeIdx x .minus false).length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (star (A.G ω β (σ x)) * A.G ω β (σ e₁.y))) +
      ((oDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum := by
  have hKt : A.Test fun ω' => Kx (cX x) Γ i₁ σ (D ω') :=
    test_listProd' A _ fun p hp => kx_test A σ hpl (fun _ h => cX_random x h) i₁ hp
  have hFb : ∀ c ∈ eraseIdxs (psteps_oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hFt : A.Test fun ω' => rv (D ω') σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) :=
    rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1
  have hdK : A.dh β (σ x) (fun ω' => Kx (cX x) Γ i₁ σ (D ω')) = fun ω' =>
      (Γ.comps.zipIdx.map fun p => A.dh β (σ x) (fun ω'' => kx (cX x) i₁ σ (D ω'') p) ω' *
        Kxq (cX x) Γ i₁ σ (D ω') p.2).sum :=
    dh_prod_rule A β (σ x) Prod.snd _ (zip_snd_nodup _) (fun p ω => kx (cX x) i₁ σ (D ω) p)
      (fun p hp => kx_test A σ hpl (fun _ h => cX_random x h) i₁ hp)
  have hdF := (dTerms_spec A σ' (newA 0) (liftA 1 x) _ (plain_bas_lift hFb 1)).2 ω
  simp only [rv_liftCs, hσ', hβ] at hdF
  rw [show σ' (liftA 1 x) = σ x by rw [← hσ']; rfl] at hdF
  have hD : ((oDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum =
      Kx (cX x) Γ i₁ σ (D ω) * A.G ω β (σ e₁.y) *
        ((dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (psteps_oXIdx x Γ) Γ.comps))).map
          fun d => rv (D ω) σ' d).sum := by
    rw [oDs, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_liftCs, hσ', out_R4, oSx, oGy, rv_cons,
      rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      Charge.apply, one_mul, mul_one, hβ]
    rw [show σ' (liftA 1 e₁.y) = σ e₁.y by rw [← hσ']; rfl]
    ring
  rw [dh_mul' A β (σ x) hKt hFt, hD, hdF, hdK]
  have hPP : ∀ p ∈ Γ.comps.zipIdx,
      -(A.dh β (σ x) (fun ω => kx (cX x) i₁ σ (D ω) p) ω) * Kxq (cX x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) * A.G ω β (σ e₁.y) = _ :=
    fun p hp => out_PP A σ hpl hOP hL hp β ω
  have hsum : A.G ω β (σ e₁.y) * -((Γ.comps.zipIdx.map fun p =>
        A.dh β (σ x) (fun ω'' => kx (cX x) i₁ σ (D ω'') p) ω * Kxq (cX x) Γ i₁ σ (D ω) p.2).sum *
        rv (D ω) σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps)) =
      (Γ.comps.zipIdx.map fun p => -(A.dh β (σ x) (fun ω => kx (cX x) i₁ σ (D ω) p) ω) *
        Kxq (cX x) Γ i₁ σ (D ω) p.2 * rv (D ω) σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps) *
        A.G ω β (σ e₁.y)).sum := by
    rw [← List.sum_map_mul_right, ← list_sum_neg, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    ring
  rw [List.map_congr_left hPP] at hsum
  simp only [List.sum_map_add] at hsum
  have h1 := sum_filter_snd Γ.comps.zipIdx (ep x .minus true) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω β (σ e₁.y) * star (A.G ω β (σ (Γ.comps.getD j e₁).y))) * star (A.G ω (σ x) (σ x)))
  have h2 := sum_filter_snd Γ.comps.zipIdx (ep x .plus false) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω β (σ e₁.y) * A.G ω (σ (Γ.comps.getD j e₁).x) β) * A.G ω (σ x) (σ x))
  have h3 := sum_ite_const Γ.comps.zipIdx (fun p => ep x .plus true p && p.2 != i₁)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ x) β * A.G ω β (σ e₁.y)))
  have h4 := sum_ite_const Γ.comps.zipIdx (ep x .minus false)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (star (A.G ω β (σ x)) * A.G ω β (σ e₁.y)))
  rw [len_OP hOP] at h3
  rw [← edgeIdx_eq] at h1 h2
  have h5 : (Γ.comps.zipIdx.filter (ep x .minus false)).length =
      (Γ.edgeIdx x .minus false).length := by
    rw [edgeIdx_eq, List.length_map]
  rw [h5] at h4
  simp only []
  linear_combination hsum - h1 - h2 + h3 + h4

theorem good_listSum {β : Type*} (l : List β) {f : β → Ω → ℂ} (h : ∀ q ∈ l, A.Good (f q)) :
    A.Good fun ω => (l.map fun q => f q ω).sum := by
  induction l with
  | nil => simpa using A.laws.good_const 0
  | cons z l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact A.laws.good_add _ _ (h z (List.mem_cons_self ..))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Linearity of `P_x` on a sum of the shape of [I, (3.13)]. -/
theorem P_lin5 {γ : Type*} (X : ι) (l₁ l₂ : List ℕ) (l₅ : List γ) (f₁ f₂ : ℕ → Ω → ℂ)
    (f₅ : γ → Ω → ℂ) (c₃ c₄ : ℂ) (g₃ g₄ : Ω → ℂ) (h₁ : ∀ j ∈ l₁, A.Good (f₁ j))
    (h₂ : ∀ j ∈ l₂, A.Good (f₂ j)) (h₃ : A.Good g₃) (h₄ : A.Good g₄)
    (h₅ : ∀ d ∈ l₅, A.Good (f₅ d)) (ω : Ω) :
    PF.P X (fun ω' => (l₁.map fun j => f₁ j ω').sum + (l₂.map fun j => f₂ j ω').sum +
        c₃ * g₃ ω' + c₄ * g₄ ω' + (l₅.map fun d => f₅ d ω').sum) ω =
      (l₁.map fun j => PF.P X (f₁ j) ω).sum + (l₂.map fun j => PF.P X (f₂ j) ω).sum +
        c₃ * PF.P X g₃ ω + c₄ * PF.P X g₄ ω + (l₅.map fun d => PF.P X (f₅ d) ω).sum := by
  have g1 := good_listSum A l₁ h₁
  have g2 := good_listSum A l₂ h₂
  have g5 := good_listSum A l₅ h₅
  have g3 : A.Good fun ω => c₃ * g₃ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₃
  have g4 : A.Good fun ω => c₄ * g₄ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₄
  have g12 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + (l₂.map fun q => f₂ q ω).sum :=
    A.laws.good_add _ _ g1 g2
  have g123 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + (l₂.map fun q => f₂ q ω).sum +
      c₃ * g₃ ω := A.laws.good_add _ _ g12 g3
  have g1234 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + (l₂.map fun q => f₂ q ω).sum +
      c₃ * g₃ ω + c₄ * g₄ ω := A.laws.good_add _ _ g123 g4
  rw [P_add' A g1234 g5, P_add' A g123 g4, P_add' A g12 g3, P_add' A g1 g2, P_cmul' A _ h₃,
    P_cmul' A _ h₄, P_listSum' A l₁ h₁, P_listSum' A l₂ h₂, P_listSum' A l₅ h₅]

theorem bas_sub {cs : List (Comp (Atom k n))} (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true)
    (hs : ∀ c ∈ cs, c ∈ Γ.comps) : ∀ c ∈ cs, basB c = true :=
  fun c hc => (basB_of_plain (hpl c (hs c hc))).1

theorem out_Pexp (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) * -(A.dh β (σ x) (fun ω'' => Kx (cX x) Γ i₁ σ (D ω'') *
        rv (D ω'') σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps)) ω')) ω =
      ((Γ.edgeIdx x .minus true).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' β (σ e₁.y) * star (A.G ω' β (σ (Γ.comps.getD j e₁).y))) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ((Γ.edgeIdx x .plus false).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' β (σ e₁.y) * A.G ω' (σ (Γ.comps.getD j e₁).x) β) *
          A.G ω' (σ x) (σ x)) ω).sum +
      (is₂.length : ℂ) * PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ x) β * A.G ω' β (σ e₁.y))) ω +
      ((Γ.edgeIdx x .minus false).length : ℂ) * PF.P (σ x) (fun ω' =>
          rv (D ω') σ (Γ.comps.eraseIdx i₁) * (star (A.G ω' β (σ x)) * A.G ω' β (σ e₁.y))) ω +
      ((oDs x Γ i₁ e₁).map fun d => PF.P (σ x) (fun ω' => rv (D ω') σ' d) ω).sum := by
  rw [P_congr' (fun ω' => out_KEY A σ hpl hOP hL σ' hσ' β hβ ω')]
  have hE : ∀ (is : List ℕ), A.Test fun ω' => rv (D ω') σ (eraseIdxs is Γ.comps) :=
    fun is => rv_test A σ _ (bas_sub hpl fun c hc => mem_eraseIdxs hc)
  have hR : A.Test fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) :=
    rv_test A σ _ (bas_sub hpl fun c hc => List.mem_of_mem_eraseIdx hc)
  have hFb : ∀ c ∈ eraseIdxs (psteps_oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  refine P_lin5 A (σ x) _ _ _ _ _ _ _ _ _ _ (fun j _ => A.test_good _ ?_)
    (fun j _ => A.test_good _ ?_)
    (A.test_good _ ?_) (A.test_good _ ?_) (fun d hd => A.test_good _ ?_) ω
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _)
      (test_star' A (test_G A _ _)))) (test_star' A (test_G A _ _))
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _) (test_G A _ _)))
      (test_G A _ _)
  · exact test_mul' A hR (test_mul' A (test_G A _ _) (test_G A _ _))
  · exact test_mul' A hR (test_mul' A (test_star' A (test_G A _ _)) (test_G A _ _))
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hd'b := ((dTerms_spec A σ' (newA 0) (liftA 1 x) _ (plain_bas_lift hFb 1)).1 d' hd').1
    refine rv_test A σ' _ fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rw [basB_map]
        exact bas_sub hpl (fun c hc => mem_pickIdxs hc) c' hc'
      · exact (hd'b c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

end OutDeriv

/-! ## `×`-dotted edges at `x` -/

section Xdots

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

theorem xdot_of {is : List ℕ} (h : Γ.xdotsAt x is = true) {i : ℕ} (hi : i ∈ is)
    {c : Comp (Atom k n)} (hc : Γ.comps[i]? = some c) :
    ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = x ∧ c'.y = (if c.x = x then c.y else c.x)) ∨
        (c'.x = (if c.x = x then c.y else c.x) ∧ c'.y = x)) := by
  unfold Graph.xdotsAt at h
  have h1 := List.all_eq_true.1 h i hi
  rw [hc] at h1
  simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true] at h1
  obtain ⟨c', hc', hk, h2⟩ := h1
  refine ⟨c', hc', hk, ?_⟩
  by_cases hx : c.x = x
  · simpa [hx] using h2
  · simpa [hx] using h2

/-- The deterministic part vanishes when the ends of a `×`-dotted edge have the same label. -/
theorem dv_xdot_zero (D₀ : Data ι) (σ : Atom k n → ι) {u : Atom k n}
    {c' : Comp (Atom k n)} (hc' : c' ∈ Γ.comps) (hk : c'.kind = .xdot)
    (hxy : (c'.x = x ∧ c'.y = u) ∨ (c'.x = u ∧ c'.y = x)) (hσ : σ x = σ u) :
    dv D₀ σ Γ.comps = 0 := by
  unfold dv
  refine List.prod_eq_zero (List.mem_map.2 ⟨c', List.mem_filter.2 ⟨hc', by simp [hk,
    Kind.isRandom]⟩, ?_⟩)
  simp only [Comp.val, hk]
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, hσ]

end Xdots

theorem list_finset_comm {ι β : Type*} [Fintype ι] (l : List β) (f : β → ι → ℂ) :
    (l.map fun j => ∑ α, f j α).sum = ∑ α, (l.map fun j => f j α).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.sum_add_distrib]

/-! ## Case (i): the identity at one labelling -/

section OutCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

/-- [I, (3.11)] in the form of the graphs of `multiEOut`, at one labelling `σ` of the atoms of the
input graph (`τ α` labels the new atom by `α`). -/
theorem out_core (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (psteps_oXIdx x Γ) = true) (σ : Atom k n → ι)
    (τ : ι → Atom k (n + 1) → ι) (hτ1 : ∀ α, τ α ∘ liftA 1 = σ) (hτ2 : ∀ α, τ α (newA 0) = α)
    (ω : Ω) :
    Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps * rv (D ω) σ Γ.comps =
      ((Γ.edgeIdx x .minus true).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' α (σ e₁.y) * star (A.G ω' α (σ (Γ.comps.getD j e₁).y))) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ((Γ.edgeIdx x .plus false).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' α (σ e₁.y) * A.G ω' (σ (Γ.comps.getD j e₁).x) α) *
          A.G ω' (σ x) (σ x)) ω).sum +
      ∑ α, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' α α - msc A.z)) ω +
      ∑ α, (is₂.length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ x) α * A.G ω' α (σ e₁.y))) ω +
      ∑ α, ((Γ.edgeIdx x .minus false).length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (star (A.G ω' α (σ x)) * A.G ω' α (σ e₁.y))) ω +
      ((oDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') (τ α) d) ω).sum +
      Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps *
        PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω := by
  set c := Γ.coeff.eval (msc A.z)
  set Det := dv (D ω) σ Γ.comps
  have hFb : ∀ c ∈ eraseIdxs (psteps_oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  -- `x` and `y₁` with the same label: every term vanishes
  have he₁ := ep_spec x (e₁_ep hOP hL)
  by_cases hXY : σ x = σ e₁.y
  · have hx1 : i₁ ∈ psteps_oXIdx x Γ := by
      rw [psteps_oXIdx, hOP]
      simp
    obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX hx1 hL
    rw [ite_eq_left (he₁.2.1 rfl).1] at hxy
    have h0 : Det = 0 := dv_xdot_zero (D ω) σ hc' hk hxy hXY
    simp [h0]
  -- the integration by parts in `P_x`
  have hpe : (e₁.isPlainB = true) := hpl e₁ (List.mem_of_getElem? hL)
  have hve : ∀ ω', Comp.val (D ω') σ e₁ = A.G ω' (σ x) (σ e₁.y) := by
    intro ω'
    rw [val_edge A σ hpe he₁.1, (he₁.2.1 rfl).1]
    rfl
  set K : Ω → ℂ := fun ω' => Kx (cX x) Γ i₁ σ (D ω') * rv (D ω') σ (eraseIdxs (psteps_oXIdx x Γ) Γ.comps)
    with hKdef
  have hKt : A.Test K :=
    test_mul' A (test_listProd' A _ fun p hp => kx_test A σ hpl (fun _ h => cX_random x h) i₁ hp)
      (rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1)
  have hR1 : ∀ ω', rv (D ω') σ Γ.comps = A.G ω' (σ x) (σ e₁.y) * K ω' := by
    intro ω'
    rw [out_R1 σ hOP hL, hve]
  have hP : PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω =
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω +
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) * PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) *
        -(A.dh β (σ x) K ω')) ω := by
    rw [P_congr' hR1, ibp_row A (σ x) (σ e₁.y) hKt ω, ite_eq_right hXY]
    have h1 : ∀ β, PF.P (σ x) (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' (σ x) (σ e₁.y) *
        K ω') ω = PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω :=
      fun β => by
        rw [P_congr' (g := fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z))
          fun ω' => by rw [hR1]; ring]
    have h2 : ∀ β, PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) * A.dh β (σ x) K ω') ω =
        -PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) * -(A.dh β (σ x) K ω')) ω := fun β => by
      rw [← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _)
        (test_neg' A (test_dh' A _ _ hKt))))]
      rw [P_congr' (g := fun ω' => -(A.G ω' β (σ e₁.y) * -(A.dh β (σ x) K ω'))) fun ω' => by
        ring]
    simp only [h1, h2]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  rw [show rv (D ω) σ Γ.comps = PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω +
    PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω by rw [Q_apply']; ring, hP]
  simp only [hKdef, fun β => out_Pexp A σ hpl hOP hL (τ β) (hτ1 β) β (hτ2 β) ω]
  rw [list_finset_comm, list_finset_comm, list_finset_comm]
  simp only [List.sum_map_mul_left, ← Finset.sum_add_distrib]
  rw [add_comm _ (c * Det * PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω), mul_add]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

end OutCore

/-! ## The graphs of the multi-edge expansion, case (iii) -/

section InDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges entering `x`, in the order of case (iii). -/
def psteps_iXIdx : List ℕ := Γ.edgeIdx x .plus false ++ Γ.edgeIdx x .minus false

/-- The solid edge `G_{w₁ α}`. -/
def iGw : Comp (Atom k (n + 1)) := mkC (.G .plus) (liftA 1 e₁.x) (newA 0)

/-- A main term of [I, (3.14)] for the edge `Ḡ_{w' x}` at position `j`: the components other than
`G_{w₁ x}` and `Ḡ_{w' x}`, and `s_{xα} G_{w₁ α} Ḡ_{w' α}`. -/
def iBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, iGw e₁, mkC (.G .minus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The `(k₃ - 1)` term of [I, (3.14)]: the components other than `G_{w₁ x}`, and
`s_{xα} G_{w₁ α} G_{αx}`. -/
def iE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)]

/-- The derivative terms of [I, (3.14)]: the edges entering `x` other than `G_{w₁ x}`, one graph of
`-∂_{h_{xα}}` of the other components, and `s_{xα} G_{w₁ α}`. -/
def iDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (psteps_iXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((psteps_iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [oSx x, iGw e₁]

/-- The formal sum of `multiEIn`. -/
def psteps_iOut : TExpansion k n :=
  (Γ.edgeIdx x .minus false).map (fun j => t1 (iBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .minus false).map (fun j => t1 (iBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [t1 (oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [t1 (iE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (iDs x Γ i₁ e₁).map (fun d => t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus false).map (fun j => t1 (labelQs (liftA 1 x) (iBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [t1 (labelQs (liftA 1 x) (oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [t1 (labelQs (liftA 1 x) (iE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (iDs x Γ i₁ e₁).map (fun d => t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

theorem multiEIn_some {E : TExpansion k n} (h : multiEIn x Γ = some E) :
    ∃ i₁ is₂ e₁, Γ.edgeIdx x .plus false = i₁ :: is₂ ∧ Γ.comps[i₁]? = some e₁ ∧
      Γ.xdotsAt x (psteps_iXIdx x Γ) = true ∧ E = psteps_iOut x Γ i₁ is₂ e₁ := by
  unfold multiEIn at h
  split at h
  · exact absurd h (by simp)
  rename_i i₁ is₂ hIP
  split at h
  · exact absurd h (by simp)
  rename_i e₁ hL
  dsimp only at h
  rw [ite_eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨hX, h⟩
  · exact absurd h (by simp)
  refine ⟨i₁, is₂, e₁, hIP, hL, by simpa [psteps_iXIdx] using hX, ?_⟩
  exact (Option.some.inj h).symm

end InDefs

section InPos

variable {k n : ℕ} (x : Atom k n)

/-- The component at a position is a solid edge entering `x` (self-loops excluded). -/
def cI (p : Comp (Atom k n) × ℕ) : Bool := ep x .plus false p || ep x .minus false p

theorem cI_random {p : Comp (Atom k n) × ℕ} (h : cI x p = true) :
    p.1.kind.isRandom = true := by
  unfold cI at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> rw [(ep_spec x h).1] <;> rfl

theorem contains_iXIdx (Γ : Graph k n) {p : Comp (Atom k n) × ℕ}
    (hp : p ∈ Γ.comps.zipIdx) : (psteps_iXIdx x Γ).contains p.2 = cI x p := by
  simp only [psteps_iXIdx, edgeIdx_eq, List.contains_append, contains_filter_snd hp, cI]

end InPos

section InProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
  {i₁ : ℕ} (σ : Atom k n → ι) {is₂ : List ℕ} {e₁ : Comp (Atom k n)}

omit [Fintype ι] [DecidableEq ι] in
theorem in_hxI : ∀ p ∈ Γ.comps.zipIdx, (psteps_iXIdx x Γ).contains p.2 = cI x p :=
  fun _ hp => contains_iXIdx x Γ hp

theorem in_hcR : ∀ p : Comp (Atom k n) × ℕ, cI x p = true → p.1.kind.isRandom = true :=
  fun _ h => cI_random x h

variable (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂) (hL : Γ.comps[i₁]? = some e₁)
include hIP hL

omit [Fintype ι] [DecidableEq ι] in
theorem in_e₁_ep : ep x .plus false (e₁, i₁) = true := by
  have h : i₁ ∈ Γ.edgeIdx x .plus false := by rw [hIP]; exact List.mem_cons_self ..
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (mem_zip_of_get hL)).1 h

omit [Fintype ι] [DecidableEq ι] in
theorem in_e₁_cI : cI x (e₁, i₁) = true := by
  simp [cI, in_e₁_ep hIP hL]

theorem in_R1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ *
      (Kx (cI x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) :=
  gR1 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

theorem in_R2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) =
      Kx (cI x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) :=
  gR2 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

theorem in_R3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cI x q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq (cI x) Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) :=
  gR3 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀ hq hqc

theorem in_D1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps :=
  gD1 σ in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

theorem in_D3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cI x q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps :=
  gD3 σ in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀ hq hqc

omit hIP hL in
theorem in_R4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs ((psteps_iXIdx x Γ).filter (· != i₁)) Γ.comps) = Kx (cI x) Γ i₁ σ D₀ :=
  gR4 σ in_hxI in_hcR D₀

omit hIP hL in
theorem in_D4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) = dv D₀ σ Γ.comps :=
  gD4 σ in_hxI in_hcR D₀

omit hIP hL in
theorem in_D5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs ((psteps_iXIdx x Γ).filter (· != i₁)) Γ.comps) = 1 :=
  gD5 σ in_hxI in_hcR D₀

end InProd

section InDeriv

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n} (σ : Atom k n → ι)

theorem dh_IPx {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus false p = true) (β : ι) :
    A.dh (σ x) β (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(Comp.val (D ω) σ p.1 * A.G ω β (σ x)) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (hi rfl).1, val_edge A σ hc hk]

theorem dh_IMx {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus false p = true) (β : ι) :
    A.dh (σ x) β (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(star (A.G ω (σ p.1.x) β) * star (A.G ω (σ x) (σ x))) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (hi rfl).1]

/-- The term of `-∂_{h_{xβ}}` at one position, times the other factors, sorted into the
families of [I, (3.14)]. -/
theorem in_PP (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (β : ι) (ω : Ω) :
    -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) * Kxq (cI x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) * A.G ω (σ e₁.x) β =
      (if ep x .minus false p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD p.2 e₁).x) β)) *
          star (A.G ω (σ x) (σ x)) else 0) +
      (if (ep x .plus false p && p.2 != i₁) = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (A.G ω (σ e₁.x) β * A.G ω β (σ x)) else 0) := by
  have hplp := hpl _ (fst_mem_of_zip hp)
  rw [dh_kx A σ (cI x) i₁ p]
  by_cases hb : (cI x p && p.2 != i₁) = true
  · rw [ite_eq_left hb]
    obtain ⟨hc, hne⟩ := Bool.and_eq_true_iff.1 hb
    have hK := Kx_single (cI x) Γ i₁ σ (D ω) hp
    rw [kx, ite_eq_left hb] at hK
    have hgd := getD_of_zip hp e₁
    simp only [cI, Bool.or_eq_true] at hc
    rcases hc with h | h
    · rw [dh_IPx A σ hplp h, in_R2 σ hIP hL, hK,
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, hne, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
      ring
    · rw [dh_IMx A σ hplp h, in_R3 σ hIP hL (D ω) hp (by simp [cI, h]), hgd,
        ep_false h (ch' := .plus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
  · rw [ite_eq_right hb]
    have h1 : ep x .minus false p = false := by
      by_contra h
      have h' : ep x .minus false p = true := by simpa using h
      apply hb
      rw [show cI x p = true by simp [cI, h'], Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (mem_zip_of_get hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (in_e₁_ep hIP hL)).1 (by simp)
    have h4 : (ep x .plus false p && p.2 != i₁) = false := by
      by_contra h
      have h' : (ep x .plus false p && p.2 != i₁) = true := by simpa using h
      obtain ⟨h5, h6⟩ := Bool.and_eq_true_iff.1 h'
      exact hb (by rw [show cI x p = true by simp [cI, h5], h6]; rfl)
    simp [h1, h4]

omit [Fintype ι] [DecidableEq ι] in
theorem len_IP {i₁ : ℕ} {is₂ : List ℕ} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂) :
    (Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁).length = is₂.length := by
  have hnd : (i₁ :: is₂).Nodup := by
    rw [← hIP, edgeIdx_eq]
    exact (zip_snd_nodup Γ.comps).sublist ((List.filter_sublist).map _)
  have h : ((Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁).map Prod.snd) =
      is₂ := by
    have e1 : (Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁) =
        (Γ.comps.zipIdx.filter (ep x .plus false)).filter (fun p => p.2 != i₁) := by
      rw [List.filter_filter]
      congr 1
      funext p
      exact Bool.and_comm _ _
    have e2 : ((Γ.comps.zipIdx.filter (ep x .plus false)).filter (fun p => p.2 != i₁)).map
        Prod.snd = ((Γ.comps.zipIdx.filter (ep x .plus false)).map Prod.snd).filter (· != i₁) := by
      rw [List.filter_map]
      rfl
    rw [e1, e2, ← edgeIdx_eq, hIP]
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
    intro a ha
    have : a ≠ i₁ := fun h => (List.nodup_cons.1 hnd).1 (h ▸ ha)
    simpa using this
  rw [← h, List.length_map]

/-- `G_{w₁ β}` times `-∂_{h_{xβ}}` of the product of the edges entering `x` other than
`G_{w₁ x}` and of the rest: the families of [I, (3.14)] and the derivative terms. -/
theorem in_KEY (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    A.G ω (σ e₁.x) β * -(A.dh (σ x) β (fun ω' => Kx (cI x) Γ i₁ σ (D ω') *
        rv (D ω') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) ω) =
      ((Γ.edgeIdx x .minus false).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD j e₁).x) β)) *
          star (A.G ω (σ x) (σ x))).sum +
      (is₂.length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ e₁.x) β * A.G ω β (σ x))) +
      ((iDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum := by
  have hKt : A.Test fun ω' => Kx (cI x) Γ i₁ σ (D ω') :=
    test_listProd' A _ fun p hp => kx_test A σ hpl in_hcR i₁ hp
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hFt : A.Test fun ω' => rv (D ω') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) :=
    rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1
  have hdK : A.dh (σ x) β (fun ω' => Kx (cI x) Γ i₁ σ (D ω')) = fun ω' =>
      (Γ.comps.zipIdx.map fun p => A.dh (σ x) β (fun ω'' => kx (cI x) i₁ σ (D ω'') p) ω' *
        Kxq (cI x) Γ i₁ σ (D ω') p.2).sum :=
    dh_prod_rule A (σ x) β Prod.snd _ (zip_snd_nodup _) (fun p ω => kx (cI x) i₁ σ (D ω) p)
      (fun p hp => kx_test A σ hpl in_hcR i₁ hp)
  have hdF := (dTerms_spec A σ' (liftA 1 x) (newA 0) _ (plain_bas_lift hFb 1)).2 ω
  simp only [rv_liftCs, hσ', hβ] at hdF
  rw [show σ' (liftA 1 x) = σ x by rw [← hσ']; rfl] at hdF
  have hD : ((iDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum =
      Kx (cI x) Γ i₁ σ (D ω) * A.G ω (σ e₁.x) β *
        ((dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (psteps_iXIdx x Γ) Γ.comps))).map
          fun d => rv (D ω) σ' d).sum := by
    rw [iDs, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_liftCs, hσ', in_R4, oSx, iGw, rv_cons,
      rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      Charge.apply, one_mul, mul_one, hβ]
    rw [show σ' (liftA 1 e₁.x) = σ e₁.x by rw [← hσ']; rfl]
    ring
  rw [dh_mul' A (σ x) β hKt hFt, hD, hdF, hdK]
  have hPP : ∀ p ∈ Γ.comps.zipIdx,
      -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) * Kxq (cI x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) * A.G ω (σ e₁.x) β = _ :=
    fun p hp => in_PP A σ hpl hIP hL hp β ω
  have hsum : A.G ω (σ e₁.x) β * -((Γ.comps.zipIdx.map fun p =>
        A.dh (σ x) β (fun ω'' => kx (cI x) i₁ σ (D ω'') p) ω * Kxq (cI x) Γ i₁ σ (D ω) p.2).sum *
        rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) =
      (Γ.comps.zipIdx.map fun p => -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) *
        Kxq (cI x) Γ i₁ σ (D ω) p.2 * rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) *
        A.G ω (σ e₁.x) β).sum := by
    rw [← List.sum_map_mul_right, ← list_sum_neg, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    ring
  rw [List.map_congr_left hPP] at hsum
  simp only [List.sum_map_add] at hsum
  have h1 := sum_filter_snd Γ.comps.zipIdx (ep x .minus false) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD j e₁).x) β)) * star (A.G ω (σ x) (σ x)))
  have h3 := sum_ite_const Γ.comps.zipIdx (fun p => ep x .plus false p && p.2 != i₁)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ e₁.x) β * A.G ω β (σ x)))
  rw [len_IP hIP] at h3
  rw [← edgeIdx_eq] at h1
  simp only []
  linear_combination hsum - h1 + h3

/-- Linearity of `P_x` on a sum of the shape of [I, (3.14)]. -/
theorem P_lin3 {γ : Type*} (X : ι) (l₁ : List ℕ) (l₅ : List γ) (f₁ : ℕ → Ω → ℂ)
    (f₅ : γ → Ω → ℂ) (c₃ : ℂ) (g₃ : Ω → ℂ) (h₁ : ∀ j ∈ l₁, A.Good (f₁ j)) (h₃ : A.Good g₃)
    (h₅ : ∀ d ∈ l₅, A.Good (f₅ d)) (ω : Ω) :
    PF.P X (fun ω' => (l₁.map fun j => f₁ j ω').sum + c₃ * g₃ ω' +
        (l₅.map fun d => f₅ d ω').sum) ω =
      (l₁.map fun j => PF.P X (f₁ j) ω).sum + c₃ * PF.P X g₃ ω +
        (l₅.map fun d => PF.P X (f₅ d) ω).sum := by
  have g1 := good_listSum A l₁ h₁
  have g5 := good_listSum A l₅ h₅
  have g3 : A.Good fun ω => c₃ * g₃ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₃
  have g13 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + c₃ * g₃ ω :=
    A.laws.good_add _ _ g1 g3
  rw [P_add' A g13 g5, P_add' A g1 g3, P_cmul' A _ h₃, P_listSum' A l₁ h₁, P_listSum' A l₅ h₅]

theorem in_Pexp (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * -(A.dh (σ x) β (fun ω'' =>
        Kx (cI x) Γ i₁ σ (D ω'') * rv (D ω'') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) ω')) ω =
      ((Γ.edgeIdx x .minus false).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' (σ e₁.x) β * star (A.G ω' (σ (Γ.comps.getD j e₁).x) β)) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      (is₂.length : ℂ) * PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ e₁.x) β * A.G ω' β (σ x))) ω +
      ((iDs x Γ i₁ e₁).map fun d => PF.P (σ x) (fun ω' => rv (D ω') σ' d) ω).sum := by
  rw [P_congr' (fun ω' => in_KEY A σ hpl hIP hL σ' hσ' β hβ ω')]
  have hE : ∀ (is : List ℕ), A.Test fun ω' => rv (D ω') σ (eraseIdxs is Γ.comps) :=
    fun is => rv_test A σ _ (bas_sub hpl fun c hc => mem_eraseIdxs hc)
  have hR : A.Test fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) :=
    rv_test A σ _ (bas_sub hpl fun c hc => List.mem_of_mem_eraseIdx hc)
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  refine P_lin3 A (σ x) _ _ _ _ _ _ (fun j _ => A.test_good _ ?_) (A.test_good _ ?_)
    (fun d hd => A.test_good _ ?_) ω
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _)
      (test_star' A (test_G A _ _)))) (test_star' A (test_G A _ _))
  · exact test_mul' A hR (test_mul' A (test_G A _ _) (test_G A _ _))
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hd'b := ((dTerms_spec A σ' (liftA 1 x) (newA 0) _ (plain_bas_lift hFb 1)).1 d' hd').1
    refine rv_test A σ' _ fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rw [basB_map]
        exact bas_sub hpl (fun c hc => mem_pickIdxs hc) c' hc'
      · exact (hd'b c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

end InDeriv

/-! ## Case (iii): the identity at one labelling, and the value of `multiEIn` -/

section InCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

/-- The identity behind [I, (3.14)] in the form of the graphs of `multiEIn`, at one labelling
`σ` of the atoms of the input graph (`τ α` labels the new atom by `α`). -/
theorem in_core (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (psteps_iXIdx x Γ) = true) (σ : Atom k n → ι)
    (τ : ι → Atom k (n + 1) → ι) (hτ1 : ∀ α, τ α ∘ liftA 1 = σ) (hτ2 : ∀ α, τ α (newA 0) = α)
    (ω : Ω) :
    Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps * rv (D ω) σ Γ.comps =
      ((Γ.edgeIdx x .minus false).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' (σ e₁.x) α * star (A.G ω' (σ (Γ.comps.getD j e₁).x) α)) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ∑ α, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' α α - msc A.z)) ω +
      ∑ α, (is₂.length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ e₁.x) α * A.G ω' α (σ x))) ω +
      ((iDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') (τ α) d) ω).sum +
      Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps *
        PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω := by
  set c := Γ.coeff.eval (msc A.z)
  set Det := dv (D ω) σ Γ.comps
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have he₁ := ep_spec x (in_e₁_ep hIP hL)
  by_cases hXY : σ x = σ e₁.x
  · have hx1 : i₁ ∈ psteps_iXIdx x Γ := by
      rw [psteps_iXIdx, hIP]
      simp
    obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX hx1 hL
    rw [ite_eq_right (he₁.2.2 rfl).2] at hxy
    have h0 : Det = 0 := dv_xdot_zero (D ω) σ hc' hk hxy hXY
    simp [h0]
  have hpe : (e₁.isPlainB = true) := hpl e₁ (List.mem_of_getElem? hL)
  have hve : ∀ ω', Comp.val (D ω') σ e₁ = A.G ω' (σ e₁.x) (σ x) := by
    intro ω'
    rw [val_edge A σ hpe he₁.1, (he₁.2.2 rfl).1]
    rfl
  set K : Ω → ℂ := fun ω' => Kx (cI x) Γ i₁ σ (D ω') *
    rv (D ω') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) with hKdef
  have hKt : A.Test K :=
    test_mul' A (test_listProd' A _ fun p hp => kx_test A σ hpl in_hcR i₁ hp)
      (rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1)
  have hR1 : ∀ ω', rv (D ω') σ Γ.comps = A.G ω' (σ e₁.x) (σ x) * K ω' := by
    intro ω'
    rw [in_R1 σ hIP hL, hve]
  have hP : PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω =
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω +
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) * PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β *
        -(A.dh (σ x) β K ω')) ω := by
    rw [P_congr' hR1, ibp_col A (σ x) (σ e₁.x) hKt ω, ite_eq_right (Ne.symm hXY)]
    have h1 : ∀ β, PF.P (σ x) (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' (σ e₁.x) (σ x) *
        K ω') ω = PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω :=
      fun β => by
        rw [P_congr' (g := fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z))
          fun ω' => by rw [hR1]; ring]
    have h2 : ∀ β, PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * A.dh (σ x) β K ω') ω =
        -PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * -(A.dh (σ x) β K ω')) ω := fun β => by
      rw [← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _)
        (test_neg' A (test_dh' A _ _ hKt))))]
      rw [P_congr' (g := fun ω' => -(A.G ω' (σ e₁.x) β * -(A.dh (σ x) β K ω'))) fun ω' => by
        ring]
    simp only [h1, h2]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  rw [show rv (D ω) σ Γ.comps = PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω +
    PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω by rw [Q_apply']; ring, hP]
  simp only [hKdef, fun β => in_Pexp A σ hpl hIP hL (τ β) (hτ1 β) β (hτ2 β) ω]
  rw [list_finset_comm, list_finset_comm]
  simp only [List.sum_map_mul_left, ← Finset.sum_add_distrib]
  rw [add_comm _ (c * Det * PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω), mul_add]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  ring


end InCore


section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The data record with the deterministic matrices `Θ`, `Σ_o`, `Θ^{(n)}_err`, the ghost factor
and the auxiliary matrices conjugated. -/
def conjD (D₀ : Data ι) : Data ι :=
  { D₀ with
    Theta := D₀.Theta.map star
    Sig := fun o => (D₀.Sig o).map star
    ThetaErr := fun a b => (D₀.ThetaErr a b).map star
    ghost := star D₀.ghost
    aux := fun j => (D₀.aux j).map star }

omit [Fintype ι] [DecidableEq ι] in
theorem conjD_conjD (D₀ : Data ι) : conjD (conjD D₀) = D₀ := by
  rcases D₀ with ⟨m, Gm, S, Sp, Sm, Th, Sig, TE, gh, aux⟩
  simp only [conjD, Matrix.map_map]
  congr <;> simp [Function.comp_def]

omit [DecidableEq ι] in
theorem chain_conjD (D₀ : Data ι) (o : List ℕ) :
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
theorem star_ofReal_mat (S : Matrix ι ι ℝ) (a b : ι) :
    star ((S.map fun r => (r : ℂ)) a b) = (S.map fun r => (r : ℂ)) a b := by
  simp [Matrix.map_apply]

/-- The factor of the conjugate component is the conjugate of the factor under `conjD`, when `S`
is real and `S⁻ = \overline{S⁺}`. -/
theorem val_conj {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
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

theorem CVar_conj_eval (z : ℂ) (v : CVar) :
    CVar.eval z (CVar.conj v) = star (CVar.eval z v) := by
  cases v <;> simp [CVar.conj, CVar.eval, star_inv₀]

theorem Coeff_conj_eval (z : ℂ) (p : Coeff) :
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
def conjAdm (A : ModelAdm Ω ι PF D) : ModelAdm Ω ι PF (fun ω => conjD (D ω)) where
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

theorem val_conjD_random {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (h : c.kind.isRandom = true) : Comp.val (conjD D₀) σ c = Comp.val D₀ σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> first | rfl | simp [Kind.isRandom] at h

/-- Components without label, or random components without minor that are not `(G_{xx})⁻¹` or
`W_D` weights. -/
def OK {V : Type*} (cs : List (Comp V)) : Prop :=
  ∀ c ∈ cs, c.label = none ∨ (c.kind.isRandom = true ∧ basB c = true)

/-- The term of the conjugate graph is the conjugate of the term under `conjD`. -/
theorem termR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
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

theorem valR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (e : Fin k → ι) (ω : Ω) :
    g.conj.valR PF D e ω = star (g.valR PF (fun ω => conjD (D ω)) e ω) := by
  simp only [Graph.valR, termR_conj A g hok, Complex.star_def, map_sum]

end ConjAdm

/-! ## Terms of graphs `Γ_ω P_y(𝒢)` -/

section PTerm

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k N : ℕ}

include A in
theorem P_const' (y : ι) (a : ℂ) (ω : Ω) : PF.P y (fun _ => a) ω = a := by
  have := A.laws.of_meas y (fun _ => a) (A.laws.good_const a) (A.laws.meas_const y a)
  exact congrFun this ω

theorem filter_rl_unl {V : Type*} (y : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (cs.map (rl y)).filter (fun c => c.label.isNone) = cs.filter fun c => !c.kind.isRandom := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c (List.mem_cons_self ..)
    simp only [List.map_cons, List.filter_cons, rl]
    by_cases hr : c.kind.isRandom = true
    · simp [hr, ih']
    · simp [hr, hc, ih']

theorem filter_rl_lab {V : Type*} [DecidableEq V] (y : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (cs.map (rl y)).filter (fun c => decide (c.label = some (.P, y))) =
      (cs.filter fun c => c.kind.isRandom).map (rl y) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c (List.mem_cons_self ..)
    simp only [List.map_cons, List.filter_cons, rl]
    by_cases hr : c.kind.isRandom = true
    · simp [hr, ih', rl]
    · simp [hr, hc, ih']

theorem val_rl {V : Type*} (D₀ : Data ι) (σ : V → ι) (y : V) (c : Comp V) :
    Comp.val D₀ σ (rl y c) = Comp.val D₀ σ c := by
  unfold rl; split_ifs <;> rfl

include A in
/-- The term of a graph whose random components of `cs` carry the label `P_y`, the other
components (of `cs` and of `env`) no label. -/
theorem termR_lifted (y : Atom k N) (cs env : List (Comp (Atom k N))) (co : Coeff)
    (hcs : ∀ c ∈ cs, c.label = none) (henv : ∀ c ∈ env, c.label = none)
    (σ : Atom k N → ι) (ω : Ω) :
    Graph.termR (⟨cs.map (rl y) ++ env, co⟩ : Graph k N) PF D σ ω =
      co.eval (D ω).m * dv (D ω) σ cs * pv (D ω) σ env *
        PF.P (σ y) (fun ω' => rv (D ω') σ cs) ω := by
  have hfe : env.filter (fun c => c.label.isNone) = env :=
    List.filter_eq_self.2 fun c hc => by simp [henv c hc]
  have hfe' : ∀ ℓ : PQ × Atom k N, env.filter (fun c => decide (c.label = some ℓ)) = [] :=
    fun ℓ => List.filter_eq_nil_iff.2 fun c hc => by simp [henv c hc]
  have hunl : (((cs.map (rl y) ++ env).filter fun c => c.label.isNone).map
      (Comp.val (D ω) σ)).prod = dv (D ω) σ cs * pv (D ω) σ env := by
    rw [List.filter_append, filter_rl_unl y cs hcs, hfe, List.map_append, List.prod_append]
    rfl
  by_cases hr : ∃ c ∈ cs, c.kind.isRandom = true
  · have hlab : (Graph.labels (⟨cs.map (rl y) ++ env, co⟩ : Graph k N)) = [(.P, y)] := by
      unfold Graph.labels
      simp only
      apply dedup_eq_singleton
      · intro l hl
        obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 hl
        rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
          unfold rl at hcl
          split_ifs at hcl
          · exact (Option.some.inj hcl).symm
          · rw [hcs d hd] at hcl; cases hcl
        · rw [henv c hc] at hcl; cases hcl
      · obtain ⟨c, hc, hcr⟩ := hr
        exact List.mem_filterMap.2 ⟨rl y c, List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩),
          by simp [rl, hcr]⟩
    have hf : (fun ω' => (((cs.map (rl y) ++ env).filter fun c =>
        decide (c.label = some (.P, y))).map (Comp.val (D ω') σ)).prod) =
        fun ω' => rv (D ω') σ cs := by
      funext ω'
      rw [List.filter_append, filter_rl_lab y cs hcs, hfe', List.append_nil, List.map_map]
      unfold rv
      congr 1
      exact List.map_congr_left fun c _ => val_rl _ _ y c
    unfold Graph.termR
    rw [hlab, hunl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, PFamily.op]
    rw [hf]
    ring
  · push Not at hr
    have hlab : (Graph.labels (⟨cs.map (rl y) ++ env, co⟩ : Graph k N)) = [] := by
      unfold Graph.labels
      rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        unfold rl
        rw [if_neg (by simp [hr d hd])]
        exact hcs d hd
      · exact henv c hc
    have hrv : ∀ ω', rv (D ω') σ cs = 1 := by
      intro ω'
      unfold rv
      rw [List.filter_eq_nil_iff.2 (fun c hc => by simp [hr c hc])]
      rfl
    unfold Graph.termR
    rw [hlab, hunl]
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [show (fun ω' => rv (D ω') σ cs) = fun _ => (1 : ℂ) from funext hrv, P_const' A]
    ring

theorem pCore_unl (g : Graph k N) : ∀ c ∈ g.pCore.comps, c.label = none := by
  intro c hc
  rw [pCore_comps] at hc
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
  rfl

theorem pEnv_unl (g : Graph k N) : ∀ c ∈ g.pEnv, c.label = none := by
  intro c hc
  unfold Graph.pEnv at hc
  have := (List.mem_filter.1 hc).2
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1

include A in
/-- The term of a graph `Γ_ω P_x(𝒢)`: the coefficient, the deterministic factors of `𝒢` and of
`Γ_ω`, the random factors of `Γ_ω`, and `P_x` of the random factors of `𝒢`. -/
theorem termR_pform {x : Atom k N} {g : Graph k N}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand)
    (σ : Atom k N → ι) (ω : Ω) :
    g.termR PF D σ ω = g.coeff.eval (D ω).m * dv (D ω) σ g.pCore.comps * pv (D ω) σ g.pEnv *
      PF.P (σ x) (fun ω' => rv (D ω') σ g.pCore.comps) ω := by
  have hp : g.comps.Perm (g.pCore.comps.map (rl x) ++ g.pEnv) := by
    rw [relab_pCore hlab hlr]
    exact comps_perm_core g
  rcases g with ⟨L, co⟩
  rw [termR_perm' PF D hp co σ ω]
  exact termR_lifted A x _ _ co (pCore_unl _) (pEnv_unl _) σ ω

end PTerm

/-! ## `O^{(x),1}_weight` inside `P_x` -/

section SplitReg

variable {V : Type*} [DecidableEq V]

/-- A regular weight without label on `x`. -/
def isRegAt (x : V) (c : Comp V) : Bool :=
  (match c.kind with
    | .weight _ => true
    | _ => false) && decide (c.x = x) && c.label.isNone

theorem isRegAt_iff (x : V) (c : Comp V) :
    isRegAt x c = true ↔ (∃ ch, c.kind = .weight ch) ∧ c.x = x ∧ c.label = none := by
  unfold isRegAt
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp [Option.isNone_iff_eq_none]

theorem splitRegular_nonreg (x : V) (c : Comp V) (cs : List (Comp V))
    (h : isRegAt x c = false) :
    splitRegular x (c :: cs) = (splitRegular x cs).map fun p => (c :: p.1, p.2) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ with
  | weight ch =>
    simp only [splitRegular]
    by_cases ha : a = x
    · have hl : l ≠ none := fun hl => by simp [isRegAt, ha, hl] at h
      simp [ha, Option.isNone_iff_eq_none, hl]
    · simp [ha]
  | _ => simp [splitRegular]

theorem splitRegular_reg (x : V) (c : Comp V) (cs : List (Comp V)) (h : isRegAt x c = true)
    {ch : Charge} (hk : c.kind = .weight ch) :
    splitRegular x (c :: cs) =
      (splitRegular x cs).map (fun p => (p.1, mOf ch * p.2)) ++
        (splitRegular x cs).map fun p => ({ c with kind := .light ch } :: p.1, p.2) := by
  obtain ⟨-, hx, hl⟩ := (isRegAt_iff x c).1 h
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at hk hx hl
  subst hk hx hl
  simp [splitRegular]

/-- The light weight with the kind of a regular weight. -/
def toLight (c : Comp V) : Comp V :=
  { c with kind := match c.kind with
    | .weight ch => .light ch
    | κ => κ }

/-- The outputs of `splitRegular`: some regular weights on `x` become light weights, the others are
removed, the other components are kept. -/
theorem splitRegular_dec (x : V) (cs : List (Comp V)) :
    ∀ p ∈ splitRegular x cs, ∃ W₁ W₂ rest : List (Comp V), cs.Perm (W₁ ++ W₂ ++ rest) ∧
      p.1.Perm (W₁.map toLight ++ rest) ∧ (∀ c ∈ W₁ ++ W₂, isRegAt x c = true) ∧
      (∀ c ∈ rest, isRegAt x c = false) := by
  induction cs with
  | nil =>
    intro p hp
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨[], [], [], by simp, by simp, by simp, by simp⟩
  | cons c cs ih =>
    intro p hp
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hk] at hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := ih q hq
        refine ⟨W₁, c :: W₂, rest, ?_, h2, ?_, h4⟩
        · refine (h1.cons c).trans ?_
          simp only [List.append_assoc, List.cons_append]
          exact (List.perm_middle).symm
        · intro d hd
          simp only [List.mem_append, List.mem_cons] at hd
          rcases hd with hd | rfl | hd
          · exact h3 d (List.mem_append_left _ hd)
          · exact hr
          · exact h3 d (List.mem_append_right _ hd)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := ih q hq
        refine ⟨c :: W₁, W₂, rest, ?_, ?_, ?_, h4⟩
        · simpa using h1.cons c
        · have : toLight c = { c with kind := .light ch } := by simp [toLight, hk]
          simpa [this] using h2.cons (toLight c)
        · intro d hd
          simp only [List.mem_append, List.mem_cons] at hd
          rcases hd with (rfl | hd) | hd
          · exact hr
          · exact h3 d (List.mem_append_left _ hd)
          · exact h3 d (List.mem_append_right _ hd)
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr'] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := ih q hq
      refine ⟨W₁, W₂, c :: rest, ?_, ?_, h3, ?_⟩
      · exact (h1.cons c).trans List.perm_middle.symm
      · exact (h2.cons c).trans List.perm_middle.symm
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hr'
        · exact h4 d hd

end SplitReg

section SplitRegValue

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} [DecidableEq V]

/-- The values of the outputs of `splitRegular`: the random parts sum to the random part of the
input, the deterministic parts are those of the input. -/
theorem splitRegular_value (x : V) (cs : List (Comp V)) (D₀ : Data ι) (σ : V → ι) :
    ((splitRegular x cs).map fun p => p.2.eval D₀.m * rv D₀ σ p.1).sum = rv D₀ σ cs ∧
      ∀ p ∈ splitRegular x cs, dv D₀ σ p.1 = dv D₀ σ cs := by
  induction cs with
  | nil => simp [splitRegular, Coeff.eval]
  | cons c cs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hk]
      have hrc : c.kind.isRandom = true := by rw [hk]; rfl
      refine ⟨?_, ?_⟩
      · simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append, rv_cons,
          hrc, ite_true, Kind.isRandom, ↓reduceIte]
        have e1 : ∀ p : List (Comp V) × Coeff, (mOf ch * p.2).eval D₀.m * rv D₀ σ p.1 =
            (mOf ch).eval D₀.m * (p.2.eval D₀.m * rv D₀ σ p.1) := by
          intro p; simp only [Coeff.eval, map_mul]; ring
        have e2 : ∀ p : List (Comp V) × Coeff, p.2.eval D₀.m * (Comp.val D₀ σ
            { c with kind := .light ch } * rv D₀ σ p.1) =
            Comp.val D₀ σ { c with kind := .light ch } * (p.2.eval D₀.m * rv D₀ σ p.1) := by
          intro p; ring
        simp only [e1, e2, List.sum_map_mul_left, ih1]
        rw [← add_mul]
        congr 1
        rcases c with ⟨κ, a, b, mi, l⟩
        simp only at hk
        subst hk
        cases ch <;> simp [Comp.val, mOf, Coeff.eval, CVar.eval, Charge.apply]
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          rw [ih2 q hq, dv_cons, if_pos hrc, one_mul]
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          rw [dv_cons, dv_cons, ih2 q hq, if_pos hrc,
            if_pos (show ({ c with kind := .light ch } : Comp V).kind.isRandom = true from rfl)]
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr']
      refine ⟨?_, ?_⟩
      · simp only [List.map_map, Function.comp_def, rv_cons]
        have e : ∀ p : List (Comp V) × Coeff, p.2.eval D₀.m *
            ((if c.kind.isRandom then Comp.val D₀ σ c else 1) * rv D₀ σ p.1) =
            (if c.kind.isRandom then Comp.val D₀ σ c else 1) * (p.2.eval D₀.m * rv D₀ σ p.1) := by
          intro p; ring
        simp only [e, List.sum_map_mul_left, ih1]
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        rw [dv_cons, dv_cons, ih2 q hq]

end SplitRegValue

/-! ## The clauses on the terms of one step inside `P_x` -/

section TermOKDef

variable {k n : ℕ}

/-- The clauses on a term `t` of one step inside `P_x` applied to `g` at `x`, before the
normalization: the clauses `NN` with bound `C₁`, at most three solid edges without `×`-dotted
edge, at most two between two blocks, the clauses `SR`, the scaling order does not drop, and if
it is unchanged the weighted number of labelled weights and edge ends at the block of `x` drops
and the normalization makes no identification of the same scaling order. -/
structure PStepsTermOK (C₁ : ℕ) (x : Atom k n) (g : Graph k n) (t : Tracked k n) : Prop where
  nn : NN C₁ (t.f x) t.g
  unp : t.g.unpart.length ≤ 3
  bnd : t.g.unpart.length + t.g.orph.length ≤ C₁
  beta : t.g.Beta 2
  sr : SR g x t
  ord : g.ord ≤ t.g.ord
  eq : t.g.ord = g.ord → t.g.pw (t.f x) < g.pw x ∧ (t.g.Beta 1 ∨ t.g.HAvoid (t.f x))

theorem Graph.beta_of_unpart {g : Graph k n} {b : ℕ} (h : g.unpart.length ≤ b) :
    g.Beta b := by
  intro u v _
  classical
  unfold Graph.nBetween
  exact (List.length_filter_le _ _).trans h

end TermOKDef

/-! ## `O^{(x),1}_weight` inside `P_x`: the terms -/

section WeightSwap

variable {k n : ℕ}

/-- A weight or light weight with label `P_x` on `x`. -/
def WtAt (x : Atom k n) (c : Comp (Atom k n)) : Prop :=
  ((∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) ∧ c.x = x ∧ c.y = x ∧
    c.minor = [] ∧ c.label = some (.P, x)

/-- Replacing labelled weights on `x` by other labelled weights on `x` keeps the clauses. -/
theorem weightSwap {C : ℕ} {x : Atom k n} {g g₁ : Graph k n} (hS : St C x g)
    {R A L : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ L)) (h₁ : g₁.comps.Perm (A ++ L))
    (hRw : ∀ c ∈ R, WtAt x c) (hAw : ∀ c ∈ A, WtAt x c) (hlen : A.length ≤ R.length)
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n, g₁⟩) :
    St C x g₁ ∧ SR g x (Tracked.self g₁) ∧
      g₁.ord = g.ord - psteps_ordL R + psteps_ordL A ∧
      g₁.pw x + (R.map (wBP fun u => g.SameBlock u x)).sum =
        g.pw x + (A.map (wBP fun u => g.SameBlock u x)).sum := by
  have hN := hS.nn
  have hnw : ∀ c, WtAt x c → c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false ∧
      c.kind.isRandom = true := by
    rintro c ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, -⟩ <;> rw [hk] <;> simp [Kind.isSolid, Kind.isRandom]
  have hmemg : ∀ c, c ∈ g.comps ↔ c ∈ R ∨ c ∈ L := fun c => by rw [hR.mem_iff, List.mem_append]
  have hmem₁ : ∀ c, c ∈ g₁.comps ↔ c ∈ A ∨ c ∈ L := fun c => by rw [h₁.mem_iff, List.mem_append]
  -- the components that are not weights of `R` or `A` are the same
  have hsame : ∀ c, ¬ WtAt x c → (c ∈ g₁.comps ↔ c ∈ g.comps) := by
    intro c hc
    rw [hmem₁, hmemg]
    constructor
    · rintro (h | h)
      · exact absurd (hAw c h) hc
      · exact Or.inr h
    · rintro (h | h)
      · exact absurd (hRw c h) hc
      · exact Or.inr h
  have hdx : ∀ c, (c.kind = .dot ∨ c.kind = .xdot ∨ c.kind.isSolid = true) →
      (c ∈ g₁.comps ↔ c ∈ g.comps) := by
    intro c hc
    refine hsame c fun hw => ?_
    obtain ⟨h1, h2, h3, -⟩ := hnw c hw
    rcases hc with h | h | h
    · exact h1 h
    · exact h2 h
    · rw [h3] at h; cases h
  have hbl : ∀ u v, g₁.SameBlock u v ↔ g.SameBlock u v :=
    Graph.sameBlock_iff_of_dots fun c hk => (hdx c (Or.inl hk)).symm |>.symm
  have hpartB : ∀ c, g₁.partB c = g.partB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.partB_iff, Graph.partB_iff]
    constructor
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inl hk))).1 hd, hk, hp⟩
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inl hk))).2 hd, hk, hp⟩
  have hsolidB : ∀ c, g₁.solidB c = g.solidB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.solidB_iff, Graph.solidB_iff]
    constructor
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inr hk))).1 hd, hk, hp⟩
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inr hk))).2 hd, hk, hp⟩
  have hunp : g₁.unpart = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hcm, hcs, hcp⟩ := Graph.mem_unpart.1 hc
    have : c ∈ g.unpart := Graph.mem_unpart.2 ⟨(hdx c (Or.inr (Or.inr hcs))).1 hcm, hcs,
      by rw [← hpartB]; exact hcp⟩
    rw [hS.unp] at this; simp at this
  have horph : g₁.orph = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hcm, hck, hcs⟩ := Graph.mem_orph.1 hc
    have : c ∈ g.orph := Graph.mem_orph.2 ⟨(hdx c (Or.inr (Or.inl (by simpa using hck)))).1 hcm,
      hck, by rw [← hsolidB]; exact hcs⟩
    rw [hS.orp] at this; simp at this
  -- the edge graphs are the same: weights are loops
  have hedge : ∀ c ∈ g₁.comps, c ∉ g.comps → c.x = c.y := by
    intro c hc hc'
    by_cases hw : WtAt x c
    · rw [hw.2.1, hw.2.2.1]
    · exact absurd ((hsame c hw).1 hc) hc'
  have hedge' : ∀ c ∈ g.comps, c ∉ g₁.comps → c.x = c.y := by
    intro c hc hc'
    by_cases hw : WtAt x c
    · rw [hw.2.1, hw.2.2.1]
    · exact absurd ((hsame c hw).2 hc) hc'
  have hcnx : g₁.ConnNoX := by
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
    intro p q hpq
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inl ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact hedge' c hc hc₁) hne
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inr ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact (hedge' c hc hc₁).symm) hne
  have hint : ∀ a b : Fin n, g₁.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.reg.internal a b)
    intro p q hpq
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inl ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact hedge' c hc hc₁) hne
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inr ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact (hedge' c hc hc₁).symm) hne
  have hsize : g₁.comps.length ≤ g.comps.length := by
    have := h₁.length_eq; have := hR.length_eq
    simp only [List.length_append] at *; omega
  have hNN : NN C x g₁ := by
    refine ⟨hN.hx, ⟨by have := hN.reg.size; omega, ConnNoX.connected hcnx, hint, ?_⟩, hcnx, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc hk; exact hN.reg.noIntDot c ((hdx c (Or.inl hk)).1 hc) hk
    · intro c hc hk; exact hN.noLoop c ((hdx c (Or.inr (Or.inr hk))).1 hc) hk
    · intro c hc
      by_cases hw : WtAt x c
      · obtain ⟨hk, hx, hy, hmi, hl⟩ := hw
        refine ⟨hmi, ?_, ?_, ?_, ?_, ?_⟩
        · intro ch h; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] at h <;> cases h
        · intro ch d h; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] at h <;> cases h
        · intro h; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] at h <;> cases h
        · intro _; rw [hx, hy]
        · intro _; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] <;> rfl
      · exact hN.plain c ((hsame c hw).1 hc)
    · intro c hc
      by_cases hw : WtAt x c
      · exact Or.inr hw.2.2.2.2
      · exact hN.lab c ((hsame c hw).1 hc)
    · intro c hc hk; rw [hbl]; exact hN.xa c ((hdx c (Or.inr (Or.inl hk))).1 hc) hk
    · intro a b h; exact hN.ib a b ((hbl _ _).1 h)
    · intro c hc hk; rw [hbl]; exact hN.inBlk c ((hdx c (Or.inr (Or.inr hk))).1 hc) hk
    · intro c hc; rw [hunp] at hc; simp at hc
    · intro c hc; rw [hunp] at hc; simp at hc
  have hS6 : g₁.S6 x := by
    intro c hc hl
    rw [hbl, hbl]
    by_cases hw : WtAt x c
    · exact ⟨fun _ => hw.2.1, fun _ => hw.2.2.1⟩
    · exact hS.s6 c ((hsame c hw).1 hc) hl
  have hexc : excL g₁.comps = excL g.comps := by
    rw [excL_perm h₁, excL_perm hR, excL_append_nodot L A (fun c hc => (hnw c (hAw c hc)).1),
      excL_append_nodot L R (fun c hc => (hnw c (hRw c hc)).1)]
  refine ⟨⟨hNN, hunp, horph, hS6⟩, ?_, ?_, ?_⟩
  · refine SR.of_id hN.hx hN.plain.labRand ?_ (fun c hc hk => (hdx c (Or.inl hk)).2 hc) ?_
      (le_of_eq hexc) hch
    · have h1 := hR.filter (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
      have h2 := h₁.filter (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
      rw [List.filter_append, (List.filter_eq_nil_iff (l := R)).2 (fun c hc => by
        simp [(hRw c hc).2.2.2.2]), List.nil_append] at h1
      rw [List.filter_append, (List.filter_eq_nil_iff (l := A)).2 (fun c hc => by
        simp [(hAw c hc).2.2.2.2]), List.nil_append] at h2
      exact (h1.trans h2.symm).subperm.trans List.filter_sublist.subperm
    · intro c hc hk _ _; exact (hdx c (Or.inr (Or.inr (by rw [hk]; rfl)))).2 hc
  · unfold Graph.ord psteps_ordL
    rw [(h₁.map _).sum_eq, (hR.map _).sum_eq]
    simp only [List.map_append, List.sum_append]
    ring
  · unfold Graph.pw
    rw [blockPred_congr x hbl, (h₁.map _).sum_eq, (hR.map _).sum_eq]
    simp only [List.map_append, List.sum_append]
    ring

end WeightSwap

section RoundW

variable {k n : ℕ}

theorem map_comp_id {V : Type*} (L : List (Comp V)) : L.map (Comp.map id) = L := by
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun c _ => ?_
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map]

theorem pLiftT_oWeight1T (x : Atom k n) (g : Graph k n) :
    pLiftT x g (oWeight1T x g.pCore) = (splitRegular x g.pCore.comps).map fun p =>
      (⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩, id⟩ : Tracked k n) := by
  unfold pLiftT oWeight1T
  rw [List.filterMap_map]
  apply List.filterMap_eq_map_iff_forall_eq_some.2
  intro p hp
  have hunl : ∀ c ∈ p.1, c.label = none := by
    intro c hc
    obtain ⟨W₁, W₂, rest, h1, h2, -, -⟩ := splitRegular_dec x _ p hp
    rcases List.mem_append.1 (h2.subset hc) with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact pCore_unl g w (h1.symm.subset (by simp [hw]))
    · exact pCore_unl g c (h1.symm.subset (by simp [h]))
  have hq : ¬ (p.1.any fun c => decide (c.label = some (.Q, id x))) = true := by
    simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro c hc
    rw [hunl c hc]
    simp
  simp only [Function.comp_apply]
  rw [if_neg hq, map_comp_id]
  rfl

theorem pCore_mem {g : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ g.pCore.comps) :
    ∃ d ∈ g.comps, coreP d = true ∧ c = { d with label := none } := by
  rw [pCore_comps] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact ⟨d, (List.mem_filter.1 hd).1, (List.mem_filter.1 hd).2, rfl⟩

theorem pCore_random {g : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ g.pCore.comps)
    (hr : c.kind.isRandom = true) : ∃ d ∈ g.comps, d.label.isSome = true ∧
      c = { d with label := none } := by
  obtain ⟨d, hd, hcp, rfl⟩ := pCore_mem hc
  refine ⟨d, hd, ?_, rfl⟩
  unfold coreP at hcp
  simp only at hr
  simpa [hr] using hcp

/-- The terms of `O^{(x),1}_weight` inside `P_x`. -/
theorem termsW {S : ℕ} {x : Atom k n} {g : Graph k n} (hS : St S x g)
    (hW : ∃ c ∈ g.pCore.comps, isRegAt x c = true) :
    ∀ t ∈ pLiftT x g (oWeight1T x g.pCore), PStepsTermOK S x g t ∧ t.g.comps.length ≤ g.comps.length ∧
      t.nOut = n := by
  have hN := hS.nn
  intro t ht
  rw [pLiftT_oWeight1T] at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := splitRegular_dec x _ p hp
  set R := (W₁ ++ W₂).map (rl x)
  set A := (W₁.map toLight).map (rl x)
  set L := rest.map (rl x) ++ g.pEnv
  have hgR : g.comps.Perm (R ++ L) := by
    have hp0 : g.comps.Perm (g.pCore.comps.map (rl x) ++ g.pEnv) := by
      rw [relab_pCore hN.lab hN.plain.labRand]; exact comps_perm_core g
    refine hp0.trans ?_
    have := (h1.map (rl x)).append_right g.pEnv
    simpa [R, L, List.append_assoc] using this
  have hgA : (p.1.map (rl x) ++ g.pEnv).Perm (A ++ L) := by
    have := (h2.map (rl x)).append_right g.pEnv
    simpa [A, L, List.append_assoc] using this
  -- the weights of `W₁ ++ W₂` are labelled weights on `x`
  have hW' : ∀ w ∈ W₁ ++ W₂, (∃ ch, w.kind = .weight ch) ∧ w.x = x ∧ w.y = x ∧ w.minor = [] := by
    intro w hw
    obtain ⟨⟨ch, hk⟩, hx, -⟩ := (isRegAt_iff x w).1 (h3 w hw)
    obtain ⟨d, hd, -, rfl⟩ := pCore_mem (h1.symm.subset (List.mem_append_left _ hw))
    obtain ⟨hmi, -, -, -, hwf, -⟩ := hN.plain d hd
    have hy : d.y = d.x := hwf (by simp only at hk; rw [hk]; rfl)
    exact ⟨⟨ch, hk⟩, hx, by simp only at hx ⊢; rw [hy]; exact hx, hmi⟩
  have hRw : ∀ c ∈ R, WtAt x c := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨ch, hk⟩, hx, hy, hmi⟩ := hW' w hw
    refine ⟨Or.inl ⟨ch, by simp [rl, hk, Kind.isRandom]⟩, by simp [rl, hk, Kind.isRandom, hx],
      by simp [rl, hk, Kind.isRandom, hy], by simp [rl, hk, Kind.isRandom, hmi],
      by simp [rl, hk, Kind.isRandom]⟩
  have hAw : ∀ c ∈ A, WtAt x c := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨⟨ch, hk⟩, hx, hy, hmi⟩ := hW' w (List.mem_append_left _ hw)
    refine ⟨Or.inr ⟨ch, by simp [rl, toLight, hk, Kind.isRandom]⟩,
      by simp [rl, toLight, hk, Kind.isRandom, hx], by simp [rl, toLight, hk, Kind.isRandom, hy],
      by simp [rl, toLight, hk, Kind.isRandom, hmi], by simp [rl, toLight, hk, Kind.isRandom]⟩
  have hP : g.IsPFormAt x := by
    obtain ⟨c, hc, hcr⟩ := hW
    obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hcr
    obtain ⟨d, hd, hdl, rfl⟩ := pCore_random hc (by rw [hk]; rfl)
    refine ⟨⟨d, hd, ?_⟩, hN.lab⟩
    rcases hN.lab d hd with h | h
    · rw [h] at hdl; cases hdl
    · exact h
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩
      ⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩⟩ := by
    refine .single (QElemStep.pWeight1 x g ⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩, id⟩ hP
      hN.plain ?_)
    rw [pLiftT_oWeight1T]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  have hlen : A.length ≤ R.length := by simp [A, R]
  obtain ⟨hS₁, hSR, hord, hpw⟩ := weightSwap hS hgR hgA hRw hAw hlen hch
  -- the counts
  have hordR : psteps_ordL R = 0 := by
    unfold psteps_ordL
    rw [List.sum_eq_zero]
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
    obtain ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, -⟩ := hRw c hc
    · rw [hk]; rfl
    · exfalso
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      obtain ⟨⟨ch', hk'⟩, -⟩ := hW' w hw
      simp [rl, hk', Kind.isRandom] at hk
  have hordA : psteps_ordL A = W₁.length := by
    unfold psteps_ordL
    simp only [A, List.map_map]
    rw [show (W₁.map ((fun c => c.kind.ord) ∘ rl x ∘ toLight)) = W₁.map fun _ => (1 : ℤ) from ?_]
    · simp
    · refine List.map_congr_left fun w hw => ?_
      obtain ⟨⟨ch, hk⟩, -⟩ := hW' w (List.mem_append_left _ hw)
      simp [rl, toLight, hk, Kind.isRandom, Kind.ord]
  have hpwR : (R.map (wBP fun u => g.SameBlock u x)).sum = R.length := by
    rw [show R.map (wBP fun u => g.SameBlock u x) = R.map fun _ => 1 from
      List.map_congr_left fun c hc => ?_]
    · simp
    · obtain ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, hx, -, -, hl⟩ := hRw c hc
      · simp [wBP, hk, hl, hx, Graph.sameBlock_refl]
      · exfalso
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
        obtain ⟨⟨ch', hk'⟩, -⟩ := hW' w hw
        simp [rl, hk', Kind.isRandom] at hk
  have hpwA : (A.map (wBP fun u => g.SameBlock u x)).sum = 4 * A.length := by
    rw [show A.map (wBP fun u => g.SameBlock u x) = A.map fun _ => 4 from
      List.map_congr_left fun c hc => ?_]
    · simp [mul_comm]
    · obtain ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, hx, -, -, hl⟩ := hAw c hc
      · exfalso
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc'
        obtain ⟨⟨ch', hk'⟩, -⟩ := hW' w (List.mem_append_left _ hw)
        simp [rl, toLight, hk', Kind.isRandom] at hk
      · simp [wBP, hk, hl, hx, Graph.sameBlock_refl]
  have hRpos : 1 ≤ R.length := by
    obtain ⟨c, hc, hcr⟩ := hW
    have : c ∈ W₁ ++ W₂ := by
      rcases List.mem_append.1 (h1.subset hc) with h | h
      · exact h
      · rw [h4 c h] at hcr; cases hcr
    simp only [R, List.length_map]
    exact List.length_pos_of_mem this
  refine ⟨⟨hS₁.nn, by rw [hS₁.unp]; simp, by rw [hS₁.unp, hS₁.orp]; simp,
    Graph.beta_of_unpart (by rw [hS₁.unp]; simp), hSR, ?_, ?_⟩, ?_, rfl⟩
  · simp only
    rw [hord, hordR, hordA]; push_cast; linarith [Nat.cast_nonneg (α := ℤ) W₁.length]
  · intro heq
    simp only at heq ⊢
    rw [hord, hordR, hordA] at heq
    have hW1 : W₁.length = 0 := by omega
    have hA0 : A.length = 0 := by simp [A, hW1]
    refine ⟨?_, Or.inl (Graph.beta_of_unpart (by rw [hS₁.unp]; simp))⟩
    rw [hpwR, hpwA, hA0] at hpw
    show (⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩ : Graph k n).pw x < g.pw x
    omega
  · simp only
    have := hgA.length_eq
    have := hgR.length_eq
    simp only [List.length_append] at *
    have : A.length ≤ R.length := hlen
    omega

theorem pCore_basB {g : Graph k n} (hp : g.Plain) : ∀ c ∈ g.pCore.comps, basB c = true := by
  intro c hc
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  obtain ⟨h1, h2, h3, -⟩ := hp d hd
  have hb : basB d = true := by
    unfold basB
    rw [h1]
    cases hk : d.kind with
    | inv ch => exact absurd hk (h2 ch)
    | wD ch dd => exact absurd hk (h3 ch dd)
    | _ => rfl
  exact hb

/-- The value of `O^{(x),1}_weight` inside `P_x`. -/
theorem valueW {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain) :
    TExpansion.ValueEq (pLiftT x g (oWeight1T x g.pCore)) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  rw [pLiftT_oWeight1T]
  simp only [TExpansion.forget, Expansion.valR, List.map_map, Function.comp_def, Graph.valR]
  have hunl : ∀ p ∈ splitRegular x g.pCore.comps, ∀ c ∈ p.1, c.label = none := by
    intro p hp' c hc
    obtain ⟨W₁, W₂, rest, h1, h2, -, -⟩ := splitRegular_dec x _ p hp'
    rcases List.mem_append.1 (h2.subset hc) with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact pCore_unl g w (h1.symm.subset (by simp [hw]))
    · exact pCore_unl g c (h1.symm.subset (by simp [h]))
  have hterm : ∀ p ∈ splitRegular x g.pCore.comps, ∀ s : Fin n → ι,
      Graph.termR (⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩ : Graph k n) PF D (Sum.elim e s) ω =
        (p.2 * g.coeff).eval (D ω).m * dv (D ω) (Sum.elim e s) p.1 *
          pv (D ω) (Sum.elim e s) g.pEnv *
          PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) p.1) ω :=
    fun p hp' s => termR_lifted A x _ _ _ (hunl p hp') (pEnv_unl g) _ ω
  rw [List.map_congr_left fun p hp' => Finset.sum_congr rfl fun s _ => hterm p hp' s,
    list_finset_comm (splitRegular x g.pCore.comps) (fun p s =>
      (p.2 * g.coeff).eval (D ω).m * dv (D ω) (Sum.elim e s) p.1 *
        pv (D ω) (Sum.elim e s) g.pEnv *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) p.1) ω)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [termR_pform A hlab hp.labRand]
  set σ := Sum.elim e s
  have hv := fun D₀ => splitRegular_value x g.pCore.comps D₀ σ
  have hm : ∀ ω', (D ω').m = msc A.z := A.data_m
  have hbas := pCore_basB hp
  have hsum : (fun ω' => rv (D ω') σ g.pCore.comps) = fun ω' =>
      ((splitRegular x g.pCore.comps).map fun p => p.2.eval (msc A.z) * rv (D ω') σ p.1).sum := by
    funext ω'
    rw [← (hv (D ω')).1, hm]
  have hgood : ∀ p ∈ splitRegular x g.pCore.comps, A.Good fun ω' => rv (D ω') σ p.1 := by
    intro p hp'
    refine A.test_good _ (rv_test A σ _ fun c hc => ?_)
    obtain ⟨W₁, W₂, rest, h1, h2, -, -⟩ := splitRegular_dec x _ p hp'
    rcases List.mem_append.1 (h2.subset hc) with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      have := hbas w (h1.symm.subset (by simp [hw]))
      simp only [basB, toLight] at this ⊢
      rcases hk : w.kind <;> simp_all
    · exact hbas c (h1.symm.subset (by simp [h]))
  rw [hsum, P_listSum' A _ (f := fun p ω' => p.2.eval (msc A.z) * rv (D ω') σ p.1)
    (fun p hp' => A.laws.good_mul (fun _ => p.2.eval (msc A.z)) _
      (A.laws.good_const _) (hgood p hp'))]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' => ?_)
  rw [(hv (D ω)).2 p hp', P_cmul' A _ (hgood p hp'), hm]
  simp only [Coeff.eval, map_mul]
  ring

end RoundW

/-! ## Solid edges between blocks in a graph with one new atom -/

section ShapeBeta

variable {k n : ℕ}

/-- `a` has the new atom as an end. -/
def touchN (a : Comp (Atom k (n + 1))) : Bool := a.x == newA 0 || a.y == newA 0

/-- The end of `a` other than the new atom. -/
def otherN (a : Comp (Atom k (n + 1))) : Atom k (n + 1) :=
  if a.x = newA 0 then a.y else a.x

theorem Graph.LabIn.congr_right {g : Graph k n} {a b b' : Atom k n} (h : g.LabIn a b)
    (hb : g.SameBlock b b') : g.LabIn a b' := by
  intro c hc hl hca
  obtain ⟨hs, h1 | h1⟩ := h c hc hl hca
  · exact ⟨hs, Or.inl ⟨h1.1, Graph.sameBlock_trans h1.2 hb⟩⟩
  · exact ⟨hs, Or.inr ⟨Graph.sameBlock_trans h1.1 hb, h1.2⟩⟩

theorem length_filter_le_one_of_pairwise {α : Type*} {R : α → α → Prop} {L : List α}
    (hL : L.Pairwise R) (p : α → Bool) (hp : ∀ a b, p a = true → p b = true → ¬ R a b) :
    (L.filter p).length ≤ 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.length_cons]
      have : L.filter p = [] :=
        List.filter_eq_nil_iff.2 fun b hb hpb => hp a b ha hpb (hL.1 b hb)
      rw [this]; simp
    · rw [List.filter_cons_of_neg ha]; exact ih hL.2

open Classical in
theorem Graph.nBetween_comm (g : Graph k n) (u v : Atom k n) :
    g.nBetween u v = g.nBetween v u := by
  unfold Graph.nBetween
  congr 1
  apply List.filter_congr
  intro c _
  simp only [decide_eq_decide]
  exact Or.comm

open Classical in
/-- In a graph with one new atom whose solid edges without `×`-dotted edge are among `A`: at most
two of them between two blocks, at most one if the edges at the new atom go to distinct blocks,
and the clause `Graph.HAvoid`. -/
theorem shapeBeta {g₁ : Graph k (n + 1)} {A : List (Comp (Atom k (n + 1)))}
    (hsub : g₁.unpart.Subperm A)
    (hnew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0)
    (hAb : ∀ a ∈ A, a.kind.isSolid = true → a.x ≠ a.y)
    (hN : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1)
    (hT : (A.filter fun a => a.kind.isSolid && touchN a).length ≤ 2) :
    g₁.Beta 2 ∧
    (((A.filter fun a => a.kind.isSolid && touchN a).map otherN).Pairwise
      (fun a b => ¬ g₁.SameBlock a b) → g₁.Beta 1) ∧
    ∀ y, ¬ g₁.SameBlock (newA 0) y →
      ((∀ a ∈ A, a.kind.isSolid = true → touchN a = true → ¬ g₁.SameBlock (otherN a) y) ∨
        g₁.LabIn (newA 0) y) → g₁.HAvoid y := by
  have hle : ∀ u v, g₁.nBetween u v ≤ (A.filter fun a => a.kind.isSolid &&
      decide ((g₁.SameBlock a.x u ∧ g₁.SameBlock a.y v) ∨
        (g₁.SameBlock a.x v ∧ g₁.SameBlock a.y u))).length := by
    intro u v
    unfold Graph.nBetween
    refine le_trans (le_of_eq ?_) (hsub.filter (fun a => a.kind.isSolid &&
      decide ((g₁.SameBlock a.x u ∧ g₁.SameBlock a.y v) ∨
        (g₁.SameBlock a.x v ∧ g₁.SameBlock a.y u)))).length_le
    congr 1
    apply List.filter_congr
    intro c hc
    rw [(Graph.mem_unpart.1 hc).2.1]
    rfl
  have hα : ∀ u, g₁.SameBlock u (newA 0) → u = newA 0 :=
    fun u h => (hnew u).1 (Graph.sameBlock_symm h)
  have hfar : ∀ u v, ¬ g₁.SameBlock u (newA 0) → ¬ g₁.SameBlock v (newA 0) →
      g₁.nBetween u v ≤ 1 := by
    intro u v hu hv
    refine (hle u v).trans (le_trans (filter_length_le_of _ _ _ fun a _ ha => ?_) hN)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [Bool.and_eq_true, Bool.not_eq_true', ha.1, true_and]
    unfold touchN
    by_contra hne
    simp only [Bool.not_eq_false, Bool.or_eq_true, beq_iff_eq] at hne
    rcases ha.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hne with h | h
    · rw [h] at h1; exact hu (Graph.sameBlock_symm h1)
    · rw [h] at h2; exact hv (Graph.sameBlock_symm h2)
    · rw [h] at h1; exact hv (Graph.sameBlock_symm h1)
    · rw [h] at h2; exact hu (Graph.sameBlock_symm h2)
  have hnear : ∀ v, ¬ g₁.SameBlock (newA 0) v →
      g₁.nBetween (newA 0) v ≤ (A.filter fun a => a.kind.isSolid && touchN a &&
        decide (g₁.SameBlock (otherN a) v)).length := by
    intro v hv
    refine (hle _ v).trans (filter_length_le_of _ _ _ fun a ha h => ?_)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨hs, hb⟩ := h
    have hne := hAb a ha hs
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hα _ h1
      refine ⟨⟨hs, by simp [touchN, this]⟩, ?_⟩
      simp only [otherN, this, if_true]; exact h2
    · have := hα _ h2
      have hx : a.x ≠ newA 0 := fun h => hne (h.trans this.symm)
      refine ⟨⟨hs, by simp [touchN, this]⟩, ?_⟩
      simp only [otherN, hx, if_false]; exact h1
  have hnear2 : ∀ v, ¬ g₁.SameBlock (newA 0) v → g₁.nBetween (newA 0) v ≤ 2 := by
    intro v hv
    refine (hnear v hv).trans (le_trans (filter_length_le_of _ _ _ fun a _ h => ?_) hT)
    simp only [Bool.and_eq_true] at h ⊢
    exact h.1
  have hcases : ∀ u v, ¬ g₁.SameBlock u v →
      g₁.nBetween u v ≤ 1 ∨ (u = newA 0 ∧ ¬ g₁.SameBlock (newA 0) v) ∨
        (v = newA 0 ∧ ¬ g₁.SameBlock (newA 0) u) := by
    intro u v huv
    by_cases hu : g₁.SameBlock u (newA 0)
    · have := hα u hu
      subst this
      exact Or.inr (Or.inl ⟨rfl, huv⟩)
    · by_cases hv : g₁.SameBlock v (newA 0)
      · have := hα v hv
        subst this
        exact Or.inr (Or.inr ⟨rfl, fun h => huv (Graph.sameBlock_symm h)⟩)
      · exact Or.inl (hfar u v hu hv)
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    rcases hcases u v huv with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · omega
    · exact hnear2 v h
    · rw [Graph.nBetween_comm]; exact hnear2 u h
  · intro hpw
    have hone : ∀ v, (A.filter fun a => a.kind.isSolid && touchN a &&
        decide (g₁.SameBlock (otherN a) v)).length ≤ 1 := by
      intro v
      have := length_filter_le_one_of_pairwise hpw (fun b => decide (g₁.SameBlock b v))
        (fun a b ha hb hab => by
          simp only [decide_eq_true_eq] at ha hb
          exact hab (Graph.sameBlock_trans ha (Graph.sameBlock_symm hb)))
      rw [List.filter_map, List.length_map, List.filter_filter] at this
      refine le_trans (le_of_eq ?_) this
      congr 1
      apply List.filter_congr
      intro a _
      simp only [Function.comp_apply]
      rw [Bool.and_comm]
    intro u v huv
    rcases hcases u v huv with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact h
    · exact (hnear v h).trans (hone v)
    · rw [Graph.nBetween_comm]; exact (hnear u h).trans (hone u)
  · intro y hy hcond u v huv h2
    have hzero : ∀ w, g₁.SameBlock w y → (∀ a ∈ A, a.kind.isSolid = true → touchN a = true →
        ¬ g₁.SameBlock (otherN a) y) → (A.filter fun a => a.kind.isSolid && touchN a &&
          decide (g₁.SameBlock (otherN a) w)).length = 0 := by
      intro w hw hH
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro a ha h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact hH a ha h.1.1 h.1.2 (Graph.sameBlock_trans h.2 hw)
    rcases hcases u v huv with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · omega
    · by_cases hv : g₁.SameBlock v y
      · rcases hcond with hH | hH
        · have := (hnear v h).trans (le_of_eq (hzero v hv hH)); omega
        · exact Or.inr (Or.inr ⟨hv, hH.congr_right (Graph.sameBlock_symm hv)⟩)
      · exact Or.inl ⟨hy, hv⟩
    · by_cases hu : g₁.SameBlock u y
      · rcases hcond with hH | hH
        · rw [Graph.nBetween_comm] at h2
          have := (hnear u h).trans (le_of_eq (hzero u hu hH)); omega
        · exact Or.inr (Or.inl ⟨hu, hH.congr_right (Graph.sameBlock_symm hu)⟩)
      · exact Or.inl ⟨hu, hy⟩

end ShapeBeta

/-! ## The clauses on a term with one new atom -/

section ShapeTerm

variable {k n : ℕ}

theorem length_filter_split {α : Type*} (L : List α) (p q : α → Bool) :
    (L.filter p).length = (L.filter fun a => p a && !q a).length +
      (L.filter fun a => p a && q a).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp [ih] <;> omega

/-- A term with one new atom obtained by removing the labelled components `R` and adding the
components `A` has the clauses `PStepsTermOK`, if the scaling order does not drop, and if it is unchanged
the weighted number of labelled weights and edge ends at the block of `x` drops and the edges at
the new atom go to distinct blocks, or not to the block of `x`, or are the only labelled
components at the new atom and go to the block of `x`. -/
theorem termOfShape {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hlt : LTOut C x g A g₁) (hA4 : A.length ≤ 4)
    (hAb : ∀ a ∈ A, a.kind.isSolid = true → a.x ≠ a.y)
    (hN : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1)
    (hT : (A.filter fun a => a.kind.isSolid && touchN a).length ≤ 2)
    (hord : psteps_ordL R + 2 ≤ psteps_ordL A)
    (heq : psteps_ordL A = psteps_ordL R + 2 →
      (A.map (wBP fun u => g₁.SameBlock u (liftA 1 x))).sum <
        (R.map (wBP fun u => g.SameBlock u x)).sum ∧
      (((A.filter fun a => a.kind.isSolid && touchN a).map otherN).Pairwise
          (fun a b => ¬ g₁.SameBlock a b) ∨
        (∀ a ∈ A, a.kind.isSolid = true → touchN a = true →
          ¬ g₁.SameBlock (otherN a) (liftA 1 x)) ∨
        g₁.LabIn (newA 0) (liftA 1 x))) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  obtain ⟨hB2, hB1, hHA⟩ := shapeBeta hlt.unpSub hlt.blkNew hAb hN hT
  have hunp : g₁.unpart.length ≤ 3 := by
    refine hlt.unp.trans ?_
    rw [length_filter_split A (fun a => a.kind.isSolid) touchN]
    omega
  have hsz := hS.nn.reg.size
  have hord' := ord_lift (g := g) hR hL
  have hpw := pw_lift (x := x) hR hL hlt.blk
  have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h =>
    liftA_ne_newA 1 x 0 ((hlt.blkNew _).1 h)
  refine ⟨hlt.nn.mono (by omega), hunp, ?_, hB2, hlt.sr, ?_, ?_⟩
  · have := hlt.orp
    show g₁.unpart.length + g₁.orph.length ≤ C + 5
    omega
  · show g.ord ≤ g₁.ord
    rw [hord']; linarith
  · intro he
    change g₁.ord = g.ord at he
    rw [hord'] at he
    obtain ⟨hlt', hc⟩ := heq (by linarith)
    refine ⟨?_, ?_⟩
    · show g₁.pw (liftA 1 x) < g.pw x
      omega
    · rcases hc with hc | hc | hc
      · exact Or.inl (hB1 hc)
      · exact Or.inr (hHA _ hαx (Or.inl hc))
      · exact Or.inr (hHA _ hαx (Or.inr hc))

end ShapeTerm

/-! ## Terms with one new atom: the general form -/

section TermGen

variable {k n : ℕ}

/-- The conditions on one added component of a term with one new atom: not a dotted or
`×`-dotted edge, labelled `P` at the image of `x` exactly when random, plain and well formed, a
solid edge joins two distinct atoms not in one block and has an internal end. -/
def AOK (x : Atom k n) (g : Graph k n) (a : Comp (Atom k (n + 1))) : Prop :=
  (a.kind ≠ .dot ∧ a.kind ≠ .xdot) ∧
  a.label = (if a.kind.isRandom then some (.P, liftA 1 x) else none) ∧
  (a.minor = [] ∧ (∀ ch, a.kind ≠ .inv ch) ∧ (∀ ch d, a.kind ≠ .wD ch d) ∧
    (a.kind.isWeight = true → a.y = a.x)) ∧
  (a.kind.isSolid = true → a.x ≠ a.y ∧
    ∀ u v, a.x = liftA 1 u → a.y = liftA 1 v → ¬ g.SameBlock u v) ∧
  (a.kind.isSolid = true → a.x.isRight = true ∨ a.y.isRight = true)

theorem bconn_of_G {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind = .G .plus) {a b : Fin m} (hx : d.x = .inr a) (hy : d.y = .inr b) :
    Relation.EqvGen (bconn g₁) a b :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨d, hd, hk, hx, hy⟩)

theorem bconn_of_mol {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind.joinsMol = true) {a b : Fin m} (hx : d.x = .inr a) (hy : d.y = .inr b) :
    Relation.EqvGen (bconn g₁) a b := by
  refine Relation.EqvGen.rel _ _ (Or.inl ?_)
  by_cases hab : a = b
  · exact Or.inl (by rw [hab])
  · refine Or.inr ⟨rfl, rfl, SimpleGraph.Adj.reachable ?_⟩
    rw [Graph.molGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simpa using hab, Or.inl ⟨d, hd, hk, hx, hy⟩⟩

/-- A term with one new atom whose added components satisfy `AOK` has the clauses `PStepsTermOK` under
the conditions of `termOfShape`. -/
theorem termGen {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    (hRl : ∀ c ∈ R, c.label = some (.P, x))
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hAOK : ∀ a ∈ A, AOK x g a)
    (hAs : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ A)
    (hcon : ∀ c ∈ R, Relation.EqvGen
      (fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v) (liftA 1 c.x) (liftA 1 c.y))
    (hblue : ∀ c ∈ R, c.kind = .G .plus → ∀ a b, c.x = .inr a → c.y = .inr b →
      Relation.EqvGen (bconn g₁) (Fin.castAdd 1 a) (Fin.castAdd 1 b))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩)
    (hA4 : A.length ≤ 4)
    (hN : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1)
    (hT : (A.filter fun a => a.kind.isSolid && touchN a).length ≤ 2)
    (hord : psteps_ordL R + 2 ≤ psteps_ordL A)
    (heq : psteps_ordL A = psteps_ordL R + 2 → LTOut C x g A g₁ →
      (A.map (wBP fun u => g₁.SameBlock u (liftA 1 x))).sum <
        (R.map (wBP fun u => g.SameBlock u x)).sum ∧
      (((A.filter fun a => a.kind.isSolid && touchN a).map otherN).Pairwise
          (fun a b => ¬ g₁.SameBlock a b) ∨
        (∀ a ∈ A, a.kind.isSolid = true → touchN a = true →
          ¬ g₁.SameBlock (otherN a) (liftA 1 x)) ∨
        g₁.LabIn (newA 0) (liftA 1 x))) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hlt : LTOut C x g A g₁ := liftTerm hS hR hRl hL (fun a ha => (hAOK a ha).1)
    (fun a ha => (hAOK a ha).2.1) (fun a ha => (hAOK a ha).2.2.1) hAs
    (fun a ha => (hAOK a ha).2.2.2.1) (fun a ha => (hAOK a ha).2.2.2.2) hcon hblue hch
  exact termOfShape hS hR hL hlt hA4 (fun a ha hs => ((hAOK a ha).2.2.2.1 hs).1) hN hT hord
    (fun h => heq h hlt)

/-- `LabIn` at the new atom from the added components. -/
theorem labIn_new {g₁ : Graph k (n + 1)} {rest : List (Comp (Atom k n))}
    {A : List (Comp (Atom k (n + 1)))}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hnew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0) {y : Atom k (n + 1)}
    (hA : ∀ a ∈ A, a.label.isSome = true → (a.x = newA 0 ∨ a.y = newA 0) →
      a.kind.isSolid = true ∧
        ((a.x = newA 0 ∧ g₁.SameBlock a.y y) ∨ (g₁.SameBlock a.x y ∧ a.y = newA 0))) :
    g₁.LabIn (newA 0) y := by
  intro c hc hl hca
  have hca' : c.x = newA 0 ∨ c.y = newA 0 := by
    rcases hca with h | h
    · exact Or.inl ((hnew _).1 (Graph.sameBlock_symm h))
    · exact Or.inr ((hnew _).1 (Graph.sameBlock_symm h))
  rcases List.mem_append.1 (hL.subset hc) with h | h
  · exfalso
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 h
    rcases hca' with h' | h' <;> exact liftA_ne_newA 1 _ 0 h'
  · obtain ⟨hs, h1 | h1⟩ := hA c h hl hca'
    · exact ⟨hs, Or.inl ⟨by rw [h1.1]; exact Graph.sameBlock_refl _ _, h1.2⟩⟩
    · exact ⟨hs, Or.inr ⟨h1.1, by rw [h1.2]; exact Graph.sameBlock_refl _ _⟩⟩

end TermGen

/-! ## Terms with one new atom: the added components -/

section TermElems

variable {k n : ℕ}

theorem aok_G {x : Atom k n} {g : Graph k n} {a : Comp (Atom k (n + 1))} {ch : Charge}
    (hk : a.kind = .G ch) (hm : a.minor = []) (hl : a.label = some (.P, liftA 1 x))
    (hne : a.x ≠ a.y) (hb : ∀ u v, a.x = liftA 1 u → a.y = liftA 1 v → ¬ g.SameBlock u v)
    (hi : a.x.isRight = true ∨ a.y.isRight = true) : AOK x g a :=
  ⟨⟨by rw [hk]; simp, by rw [hk]; simp⟩, by rw [hl, hk]; simp [Kind.isRandom],
    ⟨hm, by rw [hk]; simp, by rw [hk]; simp, by rw [hk]; simp [Kind.isWeight]⟩,
    fun _ => ⟨hne, hb⟩, fun _ => hi⟩

theorem aok_W {x : Atom k n} {g : Graph k n} {a : Comp (Atom k (n + 1))} {ch : Charge}
    (hk : a.kind = .weight ch ∨ a.kind = .light ch) (hm : a.minor = [])
    (hl : a.label = some (.P, liftA 1 x)) (hy : a.y = a.x) : AOK x g a := by
  rcases hk with hk | hk <;>
  exact ⟨⟨by rw [hk]; simp, by rw [hk]; simp⟩, by rw [hl, hk]; simp [Kind.isRandom],
    ⟨hm, by rw [hk]; simp, by rw [hk]; simp, fun _ => hy⟩, by rw [hk]; simp [Kind.isSolid],
    by rw [hk]; simp [Kind.isSolid]⟩

theorem aok_sx {x : Atom k n} {g : Graph k n} :
    AOK x g (mkC (.waved .s) (liftA 1 x) (newA 0)) :=
  ⟨⟨by simp [mkC], by simp [mkC]⟩, by simp [mkC, Kind.isRandom],
    ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC, Kind.isWeight]⟩, by simp [mkC, Kind.isSolid],
    by simp [mkC, Kind.isSolid]⟩

/-- A solid edge from the new atom to an old atom satisfies `AOK`. -/
theorem aok_Gnew {x : Atom k n} {g : Graph k n} {a : Comp (Atom k (n + 1))} {ch : Charge}
    {z : Atom k n} (hk : a.kind = .G ch) (hm : a.minor = []) (hl : a.label = some (.P, liftA 1 x))
    (he : (a.x = newA 0 ∧ a.y = liftA 1 z) ∨ (a.x = liftA 1 z ∧ a.y = newA 0)) : AOK x g a := by
  refine aok_G hk hm hl ?_ ?_ ?_
  · rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact (liftA_ne_newA 1 z 0).symm
    · exact liftA_ne_newA 1 z 0
  · intro u v hu hv
    exfalso
    rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [h1] at hu; exact liftA_ne_newA 1 u 0 hu.symm
    · rw [h2] at hv; exact liftA_ne_newA 1 v 0 hv.symm
  · rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
    · left; rw [h1]; rfl
    · right; rw [h2]; rfl

open Classical in
theorem wBP_G {B : Atom k n → Prop} {a : Comp (Atom k n)} {ch : Charge}
    (hk : a.kind = .G ch) (hl : a.label.isSome = true) :
    wBP B a = (if B a.x then 1 else 0) + (if B a.y then 1 else 0) := by
  unfold wBP; rw [if_pos hl, hk]

open Classical in
theorem wBP_W {B : Atom k n → Prop} {a : Comp (Atom k n)} {ch : Charge}
    (hk : a.kind = .weight ch) (hl : a.label.isSome = true) :
    wBP B a = if B a.x then 1 else 0 := by
  unfold wBP; rw [if_pos hl, hk]

open Classical in
theorem wBP_L {B : Atom k n → Prop} {a : Comp (Atom k n)} {ch : Charge}
    (hk : a.kind = .light ch) (hl : a.label.isSome = true) :
    wBP B a = if B a.x then 4 else 0 := by
  unfold wBP; rw [if_pos hl, hk]

theorem wBP_none {B : Atom k n → Prop} {a : Comp (Atom k n)} (hl : a.label = none) :
    wBP B a = 0 := by
  unfold wBP; rw [hl]; rfl

theorem wBP_det {B : Atom k n → Prop} {a : Comp (Atom k n)}
    (hk : a.kind.isRandom = false) : wBP B a = 0 := by
  rcases a with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp_all [wBP, Kind.isRandom]

end TermElems

/-! ## Paths in a graph with one new atom -/

section Paths

variable {k : ℕ}

/-- Two internal atoms joined by a path of molecules and solid edges `G` of charge `plus`. -/
def BB {m : ℕ} (g₁ : Graph k m) (u v : Atom k m) : Prop :=
  ∃ a b, u = .inr a ∧ v = .inr b ∧ Relation.EqvGen (bconn g₁) a b

theorem BB.trans {m : ℕ} {g₁ : Graph k m} {u v w : Atom k m} (h1 : BB g₁ u v)
    (h2 : BB g₁ v w) : BB g₁ u w := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h1
  obtain ⟨b', c, hb, rfl, h'⟩ := h2
  cases Sum.inr.inj hb
  exact ⟨a, c, rfl, rfl, h.trans _ _ _ h'⟩

theorem BB.symm {m : ℕ} {g₁ : Graph k m} {u v : Atom k m} (h : BB g₁ u v) : BB g₁ v u := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  exact ⟨b, a, rfl, rfl, h.symm⟩

theorem BB.ends {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} {p q : Atom k m}
    (he : (d.x = p ∧ d.y = q) ∨ (d.x = q ∧ d.y = p)) (h : BB g₁ d.x d.y) : BB g₁ p q := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2] at h; exact h.symm

theorem BB_of_G {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind = .G .plus) (hx : d.x.isRight = true) (hy : d.y.isRight = true) :
    BB g₁ d.x d.y := by
  rcases hdx : d.x with a | a
  · rw [hdx] at hx; cases hx
  rcases hdy : d.y with b | b
  · rw [hdy] at hy; cases hy
  exact ⟨a, b, rfl, rfl, bconn_of_G hd hk hdx hdy⟩

theorem BB_of_mol {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind.joinsMol = true) (hx : d.x.isRight = true) (hy : d.y.isRight = true) :
    BB g₁ d.x d.y := by
  rcases hdx : d.x with a | a
  · rw [hdx] at hx; cases hx
  rcases hdy : d.y with b | b
  · rw [hdy] at hy; cases hy
  exact ⟨a, b, rfl, rfl, bconn_of_mol hd hk hdx hdy⟩

theorem BB.refl {m : ℕ} {g₁ : Graph k m} {u : Atom k m} (hu : u.isRight = true) :
    BB g₁ u u := by
  rcases u with a | a
  · cases hu
  · exact ⟨a, a, rfl, rfl, Relation.EqvGen.refl _⟩

/-- The relation of the paths without `×`-dotted edges. -/
def NX {m : ℕ} (g₁ : Graph k m) : Atom k m → Atom k m → Prop :=
  Relation.EqvGen fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v

theorem NX.ends {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind ≠ .xdot) {p q : Atom k m} (he : (d.x = p ∧ d.y = q) ∨ (d.x = q ∧ d.y = p)) :
    NX g₁ p q := by
  have h : NX g₁ d.x d.y := Relation.EqvGen.rel _ _ ⟨d, hd, hk, rfl, rfl⟩
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2] at h; exact h.symm

end Paths

theorem ite_len_le_one {α : Type*} (p : Prop) [Decidable p] (a : α) :
    (if p then [a] else []).length ≤ 1 := by
  split <;> simp

/-! ## Derivative terms with one new atom -/

section TermD

variable {k n : ℕ}

/-- A derivative term: `r` (a light weight at `x`, or a solid edge between `x` and `z`) and `c`
removed; a solid edge `e` between the new atom and `z`, a solid edge `αp` from the new atom to one
end `w` of `c` and a component `xp` from `x` to the other end `v` (a weight if `v = x`) added,
with the waved edge between `x` and the new atom. -/
theorem termD' {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r c : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r, c] ++ rest))
    (hrl : r.label = some (.P, x)) (hcl : c.label = some (.P, x))
    {z : Atom k n} (hz : z = x ∨ ¬ g.SameBlock z x) {ch : Charge}
    (hr : (r.kind = .light ch ∧ r.x = x ∧ z = x) ∨
      (r.kind = .G ch ∧ ((r.x = x ∧ r.y = z) ∨ (r.x = z ∧ r.y = x))))
    (hcx : c.kind.isSolid = true → (c.x = x ∨ c.y = x) → z = x ∧ r.kind.isWeight = true)
    {cc : Charge} (hck : c.kind = .G cc ∨ c.kind = .weight cc ∨ c.kind = .light cc)
    {w v : Atom k n} (hwv : (w = c.x ∧ v = c.y) ∨ (w = c.y ∧ v = c.x))
    {αp xp e : Comp (Atom k (n + 1))}
    (hαp : αp.kind = .G cc ∧ αp.minor = [] ∧ αp.label = some (.P, liftA 1 x) ∧
      ((αp.x = newA 0 ∧ αp.y = liftA 1 w) ∨ (αp.x = liftA 1 w ∧ αp.y = newA 0)))
    (hxp : xp.kind = (if v = x then .weight cc else .G cc) ∧ xp.minor = [] ∧
      xp.label = some (.P, liftA 1 x) ∧
      ((xp.x = liftA 1 x ∧ xp.y = liftA 1 v) ∨ (xp.x = liftA 1 v ∧ xp.y = liftA 1 x)))
    (he : e.kind = .G ch ∧ e.minor = [] ∧ e.label = some (.P, liftA 1 x) ∧
      ((e.x = newA 0 ∧ e.y = liftA 1 z) ∨ (e.x = liftA 1 z ∧ e.y = newA 0)))
    {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      [αp, xp, mkC (.waved .s) (liftA 1 x) (newA 0), e]))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  classical
  have hN := hS.nn
  have hcm : c ∈ g.comps := hR.symm.subset (by simp)
  have hrm : r ∈ g.comps := hR.symm.subset (by simp)
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  have hS6c := hS.s6 c hcm (by rw [hcl]; rfl)
  have hplc := hN.plain c hcm
  have hcy : c.kind.isWeight = true → c.y = c.x := hplc.2.2.2.2.1
  have hvx : v = x ∨ ¬ g.SameBlock v x := by
    by_cases h : g.SameBlock v x
    · left
      rcases hwv with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hS6c.2 h
      · exact hS6c.1 h
    · exact Or.inr h
  set sx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0) with hsx
  have hmem : ∀ a ∈ [αp, xp, sx, e], a ∈ g₁.comps := fun a ha =>
    hL.symm.subset (List.mem_append_right _ ha)
  have hαm := hmem αp (by simp)
  have hxm := hmem xp (by simp)
  have hsm := hmem sx (by simp)
  have hem := hmem e (by simp)
  -- the added components
  have hxpA : AOK x g xp := by
    by_cases hv : v = x
    · rw [if_pos hv] at hxp
      refine aok_W (Or.inl hxp.1) hxp.2.1 hxp.2.2.1 ?_
      rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hv]
    · rw [if_neg hv] at hxp
      have hvx' : ¬ g.SameBlock v x := hvx.resolve_left hv
      refine aok_G hxp.1 hxp.2.1 hxp.2.2.1 ?_ ?_ ?_
      · rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> intro h
        · exact hv (liftA_injective 1 h).symm
        · exact hv (liftA_injective 1 h)
      · intro u u' hu hu'
        rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at hu; rw [h2] at hu'
          rw [← liftA_injective 1 hu, ← liftA_injective 1 hu']
          exact fun h => hvx' (Graph.sameBlock_symm h)
        · rw [h1] at hu; rw [h2] at hu'
          rw [← liftA_injective 1 hu, ← liftA_injective 1 hu']
          exact hvx'
      · rcases hxp.2.2.2 with ⟨h1, -⟩ | ⟨-, h2⟩
        · left; rw [h1]; exact hx₁
        · right; rw [h2]; exact hx₁
  have hAOK : ∀ a ∈ [αp, xp, sx, e], AOK x g a := by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact aok_Gnew hαp.1 hαp.2.1 hαp.2.2.1 hαp.2.2.2
    · exact hxpA
    · exact aok_sx
    · exact aok_Gnew he.1 he.2.1 he.2.2.1 he.2.2.2
  -- counts
  have hαs : αp.kind.isSolid = true := by rw [hαp.1]; rfl
  have hes : e.kind.isSolid = true := by rw [he.1]; rfl
  have hsxs : sx.kind.isSolid = false := rfl
  have hαt : touchN αp = true := by
    unfold touchN; rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have het : touchN e = true := by
    unfold touchN; rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hxt : touchN xp = false := by
    unfold touchN
    rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, liftA_ne_newA]
  have hαo : otherN αp = liftA 1 w := by
    unfold otherN
    rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, h2]
    · rw [if_neg (by rw [h1]; exact liftA_ne_newA 1 w 0), h1]
  have heo : otherN e = liftA 1 z := by
    unfold otherN
    rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, h2]
    · rw [if_neg (by rw [h1]; exact liftA_ne_newA 1 z 0), h1]
  have hTl : [αp, xp, sx, e].filter (fun a => a.kind.isSolid && touchN a) = [αp, e] := by
    simp [List.filter_cons, hαs, hαt, hxt, hsxs, hes, het]
  have hord_r : r.kind.ord = 1 := by
    rcases hr with ⟨hk, -⟩ | ⟨hk, -⟩ <;> rw [hk] <;> rfl
  have hord_c : c.kind.ord ≤ 1 := by
    rcases hck with hk | hk | hk <;> rw [hk] <;> simp [Kind.ord]
  have hord_x : xp.kind.ord = if v = x then 0 else 1 := by
    rw [hxp.1]; split_ifs <;> rfl
  have hordR : psteps_ordL [r, c] = 1 + c.kind.ord := by simp [psteps_ordL, hord_r]
  have hordA : psteps_ordL [αp, xp, sx, e] = 4 + xp.kind.ord := by
    simp only [psteps_ordL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hαp.1, he.1, hsx,
      mkC]
    simp only [Kind.ord]; ring
  -- paths
  have hNXs : NX g₁ (liftA 1 x) (newA 0) := NX.ends hsm (by simp [hsx, mkC]) (Or.inl ⟨rfl, rfl⟩)
  have hNXe : NX g₁ (newA 0) (liftA 1 z) := NX.ends hem (by rw [he.1]; simp) he.2.2.2
  have hNXα : NX g₁ (newA 0) (liftA 1 w) := NX.ends hαm (by rw [hαp.1]; simp) hαp.2.2.2
  have hNXx : NX g₁ (liftA 1 x) (liftA 1 v) := by
    refine NX.ends hxm ?_ hxp.2.2.2
    rw [hxp.1]; split_ifs <;> simp
  have hBs : BB g₁ (liftA 1 x) (newA 0) :=
    BB.ends (d := sx) (Or.inl ⟨rfl, rfl⟩) (BB_of_mol hsm rfl hx₁ newA_isRight)
  refine termGen hS hR ?_ hL hAOK (by rw [hsx]; simp) ?_ ?_ hch (by simp) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact hrl
    · exact hcl
  · intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · rcases hr with ⟨hk, -, -⟩ | ⟨hk, h⟩
      · have : a.y = a.x := (hN.plain a hrm).2.2.2.2.1 (by rw [hk]; rfl)
        rw [this]; exact Relation.EqvGen.refl _
      · have hp : NX g₁ (liftA 1 x) (liftA 1 z) := hNXs.trans _ _ _ hNXe
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hp
        · rw [h1, h2]; exact hp.symm
    · have hp : NX g₁ (liftA 1 w) (liftA 1 v) :=
        hNXα.symm.trans _ _ _ (hNXs.symm.trans _ _ _ hNXx)
      rcases hwv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hp
      · rw [← h1, ← h2]; exact hp.symm
  · intro a ha hk u u' hu hu'
    suffices BB g₁ (liftA 1 a.x) (liftA 1 a.y) by
      obtain ⟨p, q, hp, hq, h⟩ := this
      rw [hu, liftA_inr] at hp; rw [hu', liftA_inr] at hq
      cases Sum.inr.inj hp; cases Sum.inr.inj hq
      exact h
    have hai : a.x.isRight = true ∧ a.y.isRight = true := by rw [hu, hu']; exact ⟨rfl, rfl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · rcases hr with ⟨hk', -⟩ | ⟨hk', h⟩
      · rw [hk] at hk'; cases hk'
      · rw [hk] at hk'
        cases hk'
        have hzi : z.isRight = true := by
          rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
          · rw [← h2]; exact hai.2
          · rw [← h1]; exact hai.1
        have hBe : BB g₁ (newA 0) (liftA 1 z) :=
          BB.ends he.2.2.2 (BB_of_G hem he.1 (by
            rcases he.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
            · exact newA_isRight
            · rw [liftA_isRight]; exact hzi) (by
            rcases he.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
            · rw [liftA_isRight]; exact hzi
            · exact newA_isRight))
        have hp := hBs.trans hBe
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hp
        · rw [h1, h2]; exact hp.symm
    · have hcc : cc = .plus := by
        rcases hck with h | h | h <;> rw [hk] at h <;> cases h; rfl
      subst hcc
      have hwi : w.isRight = true := by
        rcases hwv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
        · exact hai.1
        · exact hai.2
      have hvi : v.isRight = true := by
        rcases hwv with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
        · exact hai.2
        · exact hai.1
      have hBα : BB g₁ (newA 0) (liftA 1 w) :=
        BB.ends hαp.2.2.2 (BB_of_G hαm hαp.1 (by
          rcases hαp.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
          · exact newA_isRight
          · rw [liftA_isRight]; exact hwi) (by
          rcases hαp.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
          · rw [liftA_isRight]; exact hwi
          · exact newA_isRight))
      have hBx : BB g₁ (liftA 1 x) (liftA 1 v) := by
        by_cases hv : v = x
        · rw [hv]; exact BB.refl hx₁
        · have hk' : xp.kind = .G .plus := by rw [hxp.1, if_neg hv]
          refine BB.ends hxp.2.2.2 (BB_of_G hxm hk' ?_ ?_)
          · rcases hxp.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
            · exact hx₁
            · rw [liftA_isRight]; exact hvi
          · rcases hxp.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
            · rw [liftA_isRight]; exact hvi
            · exact hx₁
      have hp : BB g₁ (liftA 1 w) (liftA 1 v) := hBα.symm.trans (hBs.symm.trans hBx)
      rcases hwv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hp
      · rw [← h1, ← h2]; exact hp.symm
  · simp only [List.filter_cons, List.filter_nil, hαs, hαt, hxt, hsxs, hes, het, Bool.not_true,
      Bool.and_false, Bool.not_false, Bool.and_true, Bool.false_and]
    exact ite_len_le_one _ _
  · rw [hTl]; simp
  · rw [hordR, hordA]
    have : (0 : ℤ) ≤ xp.kind.ord := by rw [hord_x]; split_ifs <;> norm_num
    linarith
  · intro heq hlt
    rw [hordR, hordA] at heq
    have hv : v = x := by
      by_contra hv
      rw [hord_x, if_neg hv] at heq
      linarith
    rw [hord_x, if_pos hv] at heq
    have hc1 : c.kind.ord = 1 := by linarith
    set B₁ : Atom k (n + 1) → Prop := fun u => g₁.SameBlock u (liftA 1 x) with hB₁
    have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h =>
      liftA_ne_newA 1 x 0 ((hlt.blkNew _).1 h)
    have hblk : ∀ u, g₁.SameBlock (liftA 1 u) (liftA 1 x) ↔ g.SameBlock u x := fun u => hlt.blk u x
    have hwA : wBP B₁ αp = if g.SameBlock w x then 1 else 0 := by
      rw [wBP_G hαp.1 (by rw [hαp.2.2.1]; rfl)]
      rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        simp only [hB₁, hαx, hblk, if_false] <;> simp
    have hwX : wBP B₁ xp = 1 := by
      have hk' : xp.kind = .weight cc := by rw [hxp.1, if_pos hv]
      rw [wBP_W hk' (by rw [hxp.2.2.1]; rfl)]
      have : xp.x = liftA 1 x := by
        rcases hxp.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]; rw [hv]
      rw [this, if_pos (Graph.sameBlock_refl _ _)]
    have hwS : wBP B₁ sx = 0 := wBP_none rfl
    have hwE : wBP B₁ e = if g.SameBlock z x then 1 else 0 := by
      rw [wBP_G he.1 (by rw [he.2.2.1]; rfl)]
      rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        simp only [hB₁, hαx, hblk, if_false] <;> simp
    have hsumA : ([αp, xp, sx, e].map (wBP B₁)).sum ≤ 3 := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hwA, hwX, hwS, hwE]
      split_ifs <;> omega
    have hcR : wBP (fun u => g.SameBlock u x) c ≤ ([r, c].map (wBP fun u => g.SameBlock u x)).sum := by
      simp
    have hrR : wBP (fun u => g.SameBlock u x) r ≤ ([r, c].map (wBP fun u => g.SameBlock u x)).sum := by
      simp
    rcases hck with hk | hk | hk
    · -- `c` a solid edge with an end at `x`
      have hcxx : c.x = x ∨ c.y = x := by
        rcases hwv with ⟨-, h2⟩ | ⟨-, h2⟩
        · right; rw [← h2, hv]
        · left; rw [← h2, hv]
      obtain ⟨hzx, hrw⟩ := hcx (by rw [hk]; rfl) hcxx
      have hrL : r.kind = .light ch ∧ r.x = x := by
        rcases hr with ⟨h1, h2, -⟩ | ⟨h1, -⟩
        · exact ⟨h1, h2⟩
        · rw [h1] at hrw; cases hrw
      have hw4 : wBP (fun u => g.SameBlock u x) r = 4 := by
        rw [wBP_L hrL.1 (by rw [hrl]; rfl), if_pos (by rw [hrL.2]; exact Graph.sameBlock_refl _ _)]
      have hwx : ¬ g.SameBlock w x := by
        have hib := hN.inBlk c hcm (by rw [hk]; rfl)
        rcases hwv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1]; rw [← hv, h2]; exact hib
        · rw [h1]; rw [← hv, h2]; exact fun h => hib (Graph.sameBlock_symm h)
      have hsumA' : ([αp, xp, sx, e].map (wBP B₁)).sum = 2 := by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hwA, hwX, hwS, hwE,
          if_neg hwx, hzx, if_pos (Graph.sameBlock_refl _ _)]
        rfl
      refine ⟨by omega, Or.inl ?_⟩
      rw [hTl]
      simp only [List.map_cons, List.map_nil, hαo, heo, hzx, List.pairwise_cons,
        List.mem_cons, List.mem_nil_iff, or_false, forall_eq, and_true,
        List.not_mem_nil, false_imp_iff, imp_true_iff]
      rw [hblk]; exact ⟨hwx, trivial, List.Pairwise.nil⟩
    · rw [hk] at hc1; simp [Kind.ord] at hc1
    · -- `c` a light weight at `x`
      have hcyx : c.y = c.x := hcy (by rw [hk]; rfl)
      have hcx' : c.x = x := by
        rcases hwv with ⟨-, h2⟩ | ⟨-, h2⟩
        · rw [← hcyx, ← h2, hv]
        · rw [← h2, hv]
      have hw' : w = x := by
        rcases hwv with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1, hcx']
        · rw [h1, hcyx, hcx']
      have hc4 : wBP (fun u => g.SameBlock u x) c = 4 := by
        rw [wBP_L hk (by rw [hcl]; rfl), if_pos (by rw [hcx']; exact Graph.sameBlock_refl _ _)]
      refine ⟨by omega, ?_⟩
      rcases hz with hzx | hzx
      · right; right
        refine labIn_new hL hlt.blkNew fun a ha hl hα => ?_
        rcases List.mem_append.1 ((List.perm_append_comm.trans hL.symm).symm.subset
            (hL.symm.subset (List.mem_append_right _ ha))) with h | h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · refine ⟨hαs, ?_⟩
            rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hw']; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hw']; exact Graph.sameBlock_refl _ _, h2⟩
          · exfalso
            rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hα <;>
              rcases hα with h' | h' <;> exact liftA_ne_newA 1 _ 0 h'
          · simp [hsx, mkC] at hl
          · refine ⟨hes, ?_⟩
            rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hzx]; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hzx]; exact Graph.sameBlock_refl _ _, h2⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · refine ⟨hαs, ?_⟩
            rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hw']; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hw']; exact Graph.sameBlock_refl _ _, h2⟩
          · exfalso
            rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hα <;>
              rcases hα with h' | h' <;> exact liftA_ne_newA 1 _ 0 h'
          · simp [hsx, mkC] at hl
          · refine ⟨hes, ?_⟩
            rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hzx]; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hzx]; exact Graph.sameBlock_refl _ _, h2⟩
      · left
        rw [hTl]
        simp only [List.map_cons, List.map_nil, hαo, heo, hw', List.pairwise_cons,
          List.mem_cons, List.mem_nil_iff, or_false, forall_eq, and_true,
          List.not_mem_nil, false_imp_iff, imp_true_iff]
        rw [hlt.blk]; exact ⟨fun h => hzx (Graph.sameBlock_symm h), trivial, List.Pairwise.nil⟩

end TermD

/-! ## Derivative terms: the factors of `-∂_{h_{pq}}` -/

section TermD2

variable {k n : ℕ}

theorem dPieces_form {c : Comp (Atom k n)} (hcy : c.kind.isWeight = true → c.y = c.x)
    {p q : Atom k (n + 1)} {ps : List (Comp (Atom k (n + 1)))}
    (h : (c.map (liftA 1)).dPieces p q = some ps) :
    ∃ cc, (c.kind = .G cc ∨ c.kind = .weight cc ∨ c.kind = .light cc) ∧
      (ps = [solidC cc (liftA 1 c.x) p, solidC cc q (liftA 1 c.y)] ∨
       ps = [solidC cc (liftA 1 c.x) q, solidC cc p (liftA 1 c.y)]) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at hcy ⊢
  cases κ with
  | G ch =>
    cases ch
    · refine ⟨.plus, Or.inl rfl, Or.inl ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
    · refine ⟨.minus, Or.inl rfl, Or.inr ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
  | weight ch =>
    have hb : b = a := hcy rfl
    subst hb
    cases ch
    · refine ⟨.plus, Or.inr (Or.inl rfl), Or.inl ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
    · refine ⟨.minus, Or.inr (Or.inl rfl), Or.inr ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
  | light ch =>
    have hb : b = a := hcy rfl
    subst hb
    cases ch
    · refine ⟨.plus, Or.inr (Or.inr rfl), Or.inl ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
    · refine ⟨.minus, Or.inr (Or.inr rfl), Or.inr ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
  | _ => simp [Comp.dPieces, Comp.map] at h

theorem xp_form (x : Atom k n) (cc : Charge) {a b v : Atom k n}
    (hab : (a = x ∧ b = v) ∨ (a = v ∧ b = x)) :
    (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).kind =
        (if v = x then .weight cc else .G cc) ∧
      (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).minor = [] ∧
      (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).label = some (.P, liftA 1 x) ∧
      (((rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).x = liftA 1 x ∧
          (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).y = liftA 1 v) ∨
        ((rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).x = liftA 1 v ∧
          (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).y = liftA 1 x)) := by
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> by_cases h : v = x
  · subst h; simp [solidC, rl, mkC, Kind.isRandom]
  · simp [solidC, rl, mkC, Kind.isRandom, (liftA_injective (k := k) (n := n) 1).eq_iff, h,
      Ne.symm h]
  · subst h; simp [solidC, rl, mkC, Kind.isRandom]
  · simp [solidC, rl, mkC, Kind.isRandom, (liftA_injective (k := k) (n := n) 1).eq_iff, h,
      Ne.symm h]

theorem αp_form (x : Atom k n) (cc : Charge) {u w : Atom k (n + 1)} (z : Atom k n)
    (huw : (u = newA 0 ∧ w = liftA 1 z) ∨ (u = liftA 1 z ∧ w = newA 0)) :
    (rl (liftA 1 x) (solidC cc u w)).kind = .G cc ∧
      (rl (liftA 1 x) (solidC cc u w)).minor = [] ∧
      (rl (liftA 1 x) (solidC cc u w)).label = some (.P, liftA 1 x) ∧
      (((rl (liftA 1 x) (solidC cc u w)).x = newA 0 ∧
          (rl (liftA 1 x) (solidC cc u w)).y = liftA 1 z) ∨
        ((rl (liftA 1 x) (solidC cc u w)).x = liftA 1 z ∧
          (rl (liftA 1 x) (solidC cc u w)).y = newA 0)) := by
  have hne := liftA_ne_newA (k := k) 1 z 0
  rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [solidC, rl, mkC, Kind.isRandom, Ne.symm hne]
  · simp [solidC, rl, mkC, Kind.isRandom, hne]

/-- A derivative term of `-∂_{h_{pq}}` at a labelled component `c`, with `{p, q}` the new atom
and the image of `x`, has the clauses `PStepsTermOK` (see `termD'`). -/
theorem termD {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r c : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r, c] ++ rest))
    (hrl : r.label = some (.P, x)) (hcl : c.label = some (.P, x))
    {z : Atom k n} (hz : z = x ∨ ¬ g.SameBlock z x) {ch : Charge}
    (hr : (r.kind = .light ch ∧ r.x = x ∧ z = x) ∨
      (r.kind = .G ch ∧ ((r.x = x ∧ r.y = z) ∨ (r.x = z ∧ r.y = x))))
    (hcx : c.kind.isSolid = true → (c.x = x ∨ c.y = x) → z = x ∧ r.kind.isWeight = true)
    {p q : Atom k (n + 1)} (hpq : (p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0))
    {ps : List (Comp (Atom k (n + 1)))} (hps : (c.map (liftA 1)).dPieces p q = some ps)
    {e₀ : Comp (Atom k (n + 1))}
    (he : (e₀.x = newA 0 ∧ e₀.y = liftA 1 z) ∨ (e₀.x = liftA 1 z ∧ e₀.y = newA 0))
    (hek : e₀ = solidC ch e₀.x e₀.y)
    {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), e₀]).map (rl (liftA 1 x))))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hcm : c ∈ g.comps := hR.symm.subset (by simp)
  have hcy := (hS.nn.plain c hcm).2.2.2.2.1
  obtain ⟨cc, hck, hps'⟩ := dPieces_form hcy hps
  have he' := αp_form x ch z he
  rw [← hek] at he'
  have hsx : rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) =
      mkC (.waved .s) (liftA 1 x) (newA 0) := by simp [rl, mkC, Kind.isRandom]
  -- the two orders of the factors
  have key : ∀ s₁ s₂ : Atom k (n + 1), ((s₁ = newA 0 ∧ s₂ = liftA 1 x) ∨
      (s₁ = liftA 1 x ∧ s₂ = newA 0)) →
      ps = [solidC cc (liftA 1 c.x) s₁, solidC cc s₂ (liftA 1 c.y)] →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro s₁ s₂ hs hps₁
    rw [hps₁] at hL
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, hsx] at hL
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact termD' hS hR hrl hcl hz hr hcx hck (Or.inl ⟨rfl, rfl⟩)
        (αp_form x cc c.x (Or.inr ⟨rfl, rfl⟩)) (xp_form x cc (Or.inl ⟨rfl, rfl⟩)) he' hL hch
    · have hL' := hL.trans (List.Perm.append_left _ (List.Perm.swap _ _ _))
      exact termD' hS hR hrl hcl hz hr hcx hck (Or.inr ⟨rfl, rfl⟩)
        (αp_form x cc c.y (Or.inl ⟨rfl, rfl⟩)) (xp_form x cc (Or.inr ⟨rfl, rfl⟩)) he' hL' hch
  rcases hps' with h | h
  · exact key p q hpq h
  · exact key q p (by rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                      · exact Or.inr ⟨h2, h1⟩
                      · exact Or.inl ⟨h2, h1⟩) h

end TermD2

/-! ## [II, (4.23)] inside `P_x`: the terms -/

section RoundL

variable {k n : ℕ}

/-- The terms of [II, (4.23)] without derivative: a light weight on the new atom added, and a
light weight on `x` removed or not. -/
theorem termLa {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    (hRl : ∀ c ∈ R, c.label = some (.P, x))
    (hR' : R = [] ∨ ∃ ℓ ch', R = [ℓ] ∧ ℓ.kind = .light ch' ∧ ℓ.x = x) {ch : Charge}
    {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))]))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hla : rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0)) =
      ⟨.light ch, newA 0, newA 0, [], some (.P, liftA 1 x)⟩ := by
    simp [rl, mkC, Kind.isRandom]
  rw [hla] at hL
  set la : Comp (Atom k (n + 1)) := ⟨.light ch, newA 0, newA 0, [], some (.P, liftA 1 x)⟩
  set sx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0) with hsx
  have hRm : ∀ c ∈ R, c ∈ g.comps := fun c hc => hR.symm.subset (List.mem_append_left _ hc)
  have hR1 : ∀ c ∈ R, c.kind.isWeight = true := by
    intro c hc
    rcases hR' with rfl | ⟨ℓ, ch', rfl, hk, -⟩
    · simp at hc
    · rw [List.mem_singleton] at hc; subst hc; rw [hk]; rfl
  refine termGen hS hR hRl hL ?_ (by rw [hsx]; simp) ?_ ?_ hch (by simp) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact aok_sx
    · exact aok_W (Or.inr rfl) rfl rfl rfl
  · intro c hc
    have : c.y = c.x := (hS.nn.plain c (hRm c hc)).2.2.2.2.1 (hR1 c hc)
    rw [this]; exact Relation.EqvGen.refl _
  · intro c hc hk
    have := hR1 c hc
    rw [hk] at this; cases this
  · simp [hsx, la, mkC, Kind.isSolid]
  · simp [hsx, la, mkC, Kind.isSolid]
  · have : psteps_ordL R ≤ 1 := by
      rcases hR' with rfl | ⟨ℓ, ch', rfl, hk, -⟩
      · simp [psteps_ordL]
      · simp [psteps_ordL, hk, Kind.ord]
    have h3 : psteps_ordL [sx, la] = 3 := by simp [psteps_ordL, hsx, la, mkC, Kind.ord]
    rw [h3]; linarith
  · intro heq hlt
    have h3 : psteps_ordL [sx, la] = 3 := by simp [psteps_ordL, hsx, la, mkC, Kind.ord]
    rcases hR' with rfl | ⟨ℓ, ch', rfl, hk, hx⟩
    · rw [h3] at heq; simp [psteps_ordL] at heq
    · have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h =>
        liftA_ne_newA 1 x 0 ((hlt.blkNew _).1 h)
      have hℓl : ℓ.label.isSome = true := by rw [hRl ℓ (by simp)]; rfl
      refine ⟨?_, Or.inl ?_⟩
      · rw [List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons, List.sum_nil,
          wBP_none rfl, wBP_L (B := fun u => g₁.SameBlock u (liftA 1 x)) (a := la) rfl rfl,
          if_neg hαx]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [wBP_L hk hℓl, if_pos (by rw [hx]; exact Graph.sameBlock_refl _ _)]
        norm_num
      · simp [hsx, la, mkC, Kind.isSolid]

end RoundL

section RoundL2

variable {k n : ℕ}

theorem mem_oWeightP2Pos {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hE : oWeightP2Pos x h = some E) {s : Tracked k n} (hs : s ∈ E) :
    ∃ i, ∃ hi : i < h.comps.length, h.comps[i].kind = .light .plus ∧ h.comps[i].x = x ∧
      ∃ cs co, s = ⟨n + 1, ⟨cs, co⟩, liftA 1⟩ ∧
        (cs = liftCs 1 (h.comps.eraseIdx i) ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
            mkC (.light .plus) (newA 0) (newA 0)] ∨
         cs = liftCs 1 h.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
            mkC (.light .plus) (newA 0) (newA 0)] ∨
         ∃ j, ∃ hj : j < (h.comps.eraseIdx i).length, ∃ ps,
           (((h.comps.eraseIdx i)[j]).map (liftA 1)).dPieces (newA 0) (liftA 1 x) = some ps ∧
           cs = liftCs 1 ((h.comps.eraseIdx i).eraseIdx j) ++ ps ++
             [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)]) := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  · rename_i i hi
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    simp only [Option.some.injEq] at hE
    subst hE
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨i, hlt, hp.1, hp.2, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | rfl | ⟨d, hd, rfl⟩
    · exact ⟨_, _, rfl, Or.inl rfl⟩
    · exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
    · obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd
      have hj' : j < (h.comps.eraseIdx i).length := by simpa [liftCs] using hj
      refine ⟨_, _, rfl, Or.inr (Or.inr ⟨j, hj', ps, ?_, ?_⟩)⟩
      · rw [← hps]; simp [liftCs]
      · simp [liftCs, List.eraseIdx_map]

end RoundL2

/-! ## Complex conjugation of components -/

section ConjC

/-- The complex conjugate of a component. -/
def conjC {V : Type*} (c : Comp V) : Comp V := { c with kind := c.kind.conj }

theorem Kind.conj_conj' (κ : Kind) : κ.conj.conj = κ := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem conjC_conjC {V : Type*} (c : Comp V) : conjC (conjC c) = c := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp [conjC, Kind.conj_conj']

theorem map_conjC_conjC {V : Type*} (L : List (Comp V)) :
    (L.map conjC).map conjC = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun c _ => conjC_conjC c

theorem conjC_map {V W : Type*} (f : V → W) (c : Comp V) :
    conjC (c.map f) = (conjC c).map f := rfl

theorem solidC_conj {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    conjC (solidC ch u v) = solidC ch.flip u v := by
  unfold solidC
  split_ifs <;> cases ch <;> rfl

theorem conjC_mk {V : Type*} (κ : Kind) (a b : V) (mi : List V) (l : Option (PQ × V)) :
    conjC (⟨κ, a, b, mi, l⟩ : Comp V) = ⟨κ.conj, a, b, mi, l⟩ := rfl

theorem dPieces_conj {V : Type*} [DecidableEq V] (p q : V) (c : Comp V) :
    ((conjC c).dPieces p q).map (List.map conjC) = c.dPieces q p := by
  rcases c with ⟨κ, a, b, mi, l⟩
  rw [conjC_mk]
  cases κ with
  | G ch => cases ch <;> simp [Comp.dPieces, Kind.conj, Kind.isWeight, solidC_conj, Charge.flip]
  | weight ch => cases ch <;> simp [Comp.dPieces, Kind.conj, Kind.isWeight, solidC_conj,
      Charge.flip]
  | light ch => cases ch <;> simp [Comp.dPieces, Kind.conj, Kind.isWeight, solidC_conj,
      Charge.flip]
  | waved w => cases w <;> simp [Comp.dPieces, Kind.conj]
  | _ => simp [Comp.dPieces, Kind.conj]

private theorem conjC_mkC {V : Type*} (κ : Kind) (u v : V) : conjC (mkC κ u v) = mkC κ.conj u v :=
  rfl

theorem Graph.conj_comps' {k n : ℕ} (g : Graph k n) : g.conj.comps = g.comps.map conjC :=
  rfl

private theorem Graph.conj_coeff' {k n : ℕ} (g : Graph k n) : g.conj.coeff = Coeff.conj g.coeff :=
  rfl

theorem mem_TExpansion_conj {k n : ℕ} {E : TExpansion k n} {s : Tracked k n} :
    s ∈ E.conj ↔ ∃ s₀ ∈ E, s = ⟨s₀.nOut, s₀.g.conj, s₀.f⟩ := by
  unfold TExpansion.conj
  rw [List.mem_map]
  constructor
  · rintro ⟨s₀, hs, rfl⟩; exact ⟨s₀, hs, rfl⟩
  · rintro ⟨s₀, hs, rfl⟩; exact ⟨s₀, hs, rfl⟩

end ConjC

section RoundL3

variable {k n : ℕ}

/-- A term of an identity applied to `Γ.pCore`, read inside `P_x`: the removed components `R₀`
and the added components `A₀`. -/
theorem liftOut {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand)
    {R₀ B : List (Comp (Atom k n))} (hB : g.pCore.comps.Perm (R₀ ++ B))
    (A₀ : List (Comp (Atom k (n + 1)))) :
    g.comps.Perm (R₀.map (rl x) ++ (B.map (rl x) ++ g.pEnv)) ∧
    ((liftCs 1 B ++ A₀).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))).Perm
      ((B.map (rl x) ++ g.pEnv).map (Comp.map (liftA 1)) ++ A₀.map (rl (liftA 1 x))) := by
  constructor
  · refine (comps_perm_core g).trans ?_
    rw [← relab_pCore hlab hlr, ← List.append_assoc, ← List.map_append]
    exact (hB.map _).append_right _
  · have : (rl (liftA 1 x) ∘ Comp.map (liftA 1)) = (Comp.map (liftA 1) ∘ rl x) := by
      funext c; simp only [Function.comp_apply]; exact rl_map (liftA 1) x c
    simp only [liftCs, List.map_append, List.map_map, this, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

theorem rl_core {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand)
    {c₀ : Comp (Atom k n)} (hc : c₀ ∈ g.pCore.comps) (hr : c₀.kind.isRandom = true) :
    rl x c₀ ∈ g.comps ∧ (rl x c₀).label = some (.P, x) ∧ (rl x c₀).kind = c₀.kind ∧
      (rl x c₀).x = c₀.x ∧ (rl x c₀).y = c₀.y := by
  refine ⟨?_, by simp [rl, hr], by simp [rl, hr], by simp [rl, hr], by simp [rl, hr]⟩
  have : rl x c₀ ∈ g.pCore.comps.map (rl x) := List.mem_map_of_mem hc
  rw [relab_pCore hlab hlr] at this
  exact (List.mem_filter.1 this).1

theorem dPieces_rl {V W : Type*} [DecidableEq W] (y : V) (f : V → W) (c : Comp V)
    (p q : W) : ((rl y c).map f).dPieces p q = (c.map f).dPieces p q := by
  unfold rl; split_ifs <;> rfl

theorem dPieces_random {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) : c.kind.isRandom = true := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ with
  | G ch => rfl
  | weight ch => rfl
  | light ch => rfl
  | _ => simp [Comp.dPieces] at h

theorem liftCs_conj (L : List (Comp (Atom k n))) :
    (liftCs 1 L).map conjC = liftCs 1 (L.map conjC) := by
  simp only [liftCs, List.map_map]
  rfl

/-- The terms of [II, (4.23)] inside `P_x` at a light weight with label `P_x` on `x`. -/
theorem termsL {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hLx : ∃ c ∈ g.comps, (∃ ch, c.kind = .light ch) ∧ c.x = x ∧ c.label = some (.P, x)) :
    ∀ t ∈ oWeightP2T x g, PStepsTermOK (C + 5) x g t := by
  have hN := hS.nn
  have hlab := hN.lab
  have hlr := hN.plain.labRand
  have hP : g.IsPFormAt x := by
    obtain ⟨c, hc, -, -, hl⟩ := hLx; exact ⟨⟨c, hc, hl⟩, hN.lab⟩
  have hsxrl : rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) =
      mkC (.waved .s) (liftA 1 x) (newA 0) := by simp [rl, mkC, Kind.isRandom]
  -- the term shapes
  have keyA : ∀ (ℓ₀ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (ch : Charge),
      g.pCore.comps.Perm ([ℓ₀] ++ B) → ℓ₀.kind = .light ch → ℓ₀.x = x →
      ∀ co (g₁ : Graph k (n + 1)), g₁ = ⟨(liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩ →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ℓ₀ B ch hB hk hx co g₁ hg₁ hch
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]
    have hc := rl_core hlab hlr (hB.symm.subset (List.mem_append_left _ (List.mem_singleton_self _)))
      (by rw [hk]; rfl)
    have hL' : g₁.comps.Perm (((B.map (rl x) ++ g.pEnv)).map (Comp.map (liftA 1)) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))]) := by
      rw [hg₁]; simpa only [List.map_cons, List.map_nil, hsxrl] using hL
    refine termLa hS hR ?_ (Or.inr ⟨_, ch, rfl, by rw [hc.2.2.1, hk], by rw [hc.2.2.2.1, hx]⟩)
      hL' hch
    intro c hc'
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc'
    rw [hc']; exact hc.2.1
  have keyB : ∀ (ch : Charge) co (g₁ : Graph k (n + 1)),
      g₁ = ⟨(liftCs 1 g.pCore.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩ →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ch co g₁ hg₁ hch
    have hB : g.pCore.comps.Perm ([] ++ g.pCore.comps) := by simp
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]
    have hL' : g₁.comps.Perm (((g.pCore.comps.map (rl x) ++ g.pEnv)).map (Comp.map (liftA 1)) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))]) := by
      rw [hg₁]; simpa only [List.map_cons, List.map_nil, hsxrl] using hL
    exact termLa hS hR (by simp) (Or.inl (by simp)) hL' hch
  have keyC : ∀ (ℓ₀ c₀ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (ch : Charge),
      g.pCore.comps.Perm ([ℓ₀, c₀] ++ B) → ℓ₀.kind = .light ch → ℓ₀.x = x →
      ∀ p q : Atom k (n + 1), ((p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0)) →
      ∀ ps, (c₀.map (liftA 1)).dPieces p q = some ps →
      ∀ co (g₁ : Graph k (n + 1)), g₁ = ⟨(liftCs 1 B ++ (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G ch) (newA 0) (liftA 1 x)])).map (rl (liftA 1 x)) ++
          g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩ →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ℓ₀ c₀ B ch hB hk hx p q hpq ps hps co g₁ hg₁ hch
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G ch) (newA 0) (liftA 1 x)])
    have hℓ := rl_core hlab hlr (hB.symm.subset (List.mem_append_left B (by simp : ℓ₀ ∈ [ℓ₀, c₀])))
      (by rw [hk]; rfl)
    have hc := rl_core hlab hlr (hB.symm.subset (List.mem_append_left B (by simp : c₀ ∈ [ℓ₀, c₀])))
      (by have := dPieces_random hps; simpa [Comp.map] using this)
    simp only [List.map_cons, List.map_nil] at hR
    have hL' : g₁.comps.Perm (((B.map (rl x) ++ g.pEnv)).map (Comp.map (liftA 1)) ++
        (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G ch) (newA 0) (liftA 1 x)]).map
          (rl (liftA 1 x))) := by rw [hg₁]; exact hL
    refine termD hS hR hℓ.2.1 hc.2.1 (Or.inl rfl) (ch := ch)
      (Or.inl ⟨by rw [hℓ.2.2.1, hk], by rw [hℓ.2.2.2.1, hx], rfl⟩)
      (fun _ _ => ⟨rfl, by rw [hℓ.2.2.1, hk]; rfl⟩) hpq (by rw [dPieces_rl]; exact hps)
      (e₀ := mkC (.G ch) (newA 0) (liftA 1 x)) (Or.inl ⟨rfl, rfl⟩) ?_ hL' hch
    simp [solidC, mkC, Ne.symm (liftA_ne_newA 1 x 0)]
  intro t ht
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨t.nOut, t.g⟩ :=
    .single (QElemStep.pWeight2 x g t hP hN.plain ht)
  unfold oWeightP2T at ht
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · rw [hE] at ht
    dsimp only at ht
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E
    · exfalso
      have hn1 : g.pCore.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
        unfold oWeightP2Pos at hE
        split at hE
        · assumption
        · cases hE
      have hn2 : g.pCore.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) =
          none := by
        unfold oWeightP2Pos at hE'
        split at hE'
        · assumption
        · cases hE'
      obtain ⟨c, hc, ⟨ch, hk⟩, hx, hl⟩ := hLx
      have hc₀ : { c with label := none } ∈ g.pCore.comps := by
        rw [pCore_comps]
        exact List.mem_map_of_mem (List.mem_filter.2 ⟨hc, by simp [coreP, hl]⟩)
      cases ch
      · have := List.findIdx?_eq_none_iff.1 hn1 _ hc₀
        simp [hk, hx] at this
      · have := List.findIdx?_eq_none_iff.1 hn2 (conjC { c with label := none })
          (by rw [Graph.conj_comps']; exact List.mem_map_of_mem hc₀)
        simp [conjC, hk, hx, Kind.conj, Charge.flip] at this
    · rw [hE'] at ht
      dsimp only at ht
      obtain ⟨s', hs', -, rfl⟩ := mem_pLiftT.1 ht
      obtain ⟨s, hs, rfl⟩ := mem_TExpansion_conj.1 hs'
      obtain ⟨i, hi, hk, hx, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE' hs
      have hcore : g.pCore.conj.comps.map conjC = g.pCore.comps := by
        rw [Graph.conj_comps', map_conjC_conjC]
      have hk' : (conjC g.pCore.conj.comps[i]).kind = .light .minus := by
        simp only [conjC, hk]; rfl
      have hx' : (conjC g.pCore.conj.comps[i]).x = x := hx
      have hpermi : g.pCore.comps.Perm ([conjC g.pCore.conj.comps[i]] ++
          (g.pCore.conj.comps.eraseIdx i).map conjC) := by
        have := (List.getElem_cons_eraseIdx_perm hi).symm.map conjC
        rw [hcore] at this
        simpa only [List.map_cons, List.singleton_append] using this
      rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
      · refine keyA _ ((g.pCore.conj.comps.eraseIdx i).map conjC) .minus hpermi hk' hx' co.conj _
          ?_ hch
        simp only [Graph.conj_comps', Graph.conj_coeff', List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          conjC_mkC, Kind.conj, Charge.flip]
      · refine keyB .minus co.conj _ ?_ hch
        simp only [Graph.conj_comps', Graph.conj_coeff', List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          conjC_mkC, Kind.conj, Charge.flip, map_conjC_conjC]
      · have hB : g.pCore.comps.Perm ([conjC g.pCore.conj.comps[i],
            conjC (g.pCore.conj.comps.eraseIdx i)[j]] ++
            ((g.pCore.conj.comps.eraseIdx i).eraseIdx j).map conjC) := by
          have := ((List.getElem_cons_eraseIdx_perm hi).symm.trans
            (List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hj).symm)).map conjC
          rw [hcore] at this
          simpa only [List.map_cons, List.cons_append, List.nil_append] using this
        have hps' : ((conjC (g.pCore.conj.comps.eraseIdx i)[j]).map (liftA 1)).dPieces
            (liftA 1 x) (newA 0) = some (ps.map conjC) := by
          rw [← dPieces_conj, conjC_map, conjC_conjC, hps]
          rfl
        refine keyC _ _ _ .minus hB hk' hx' _ _ (Or.inr ⟨rfl, rfl⟩) _ hps' co.conj _ ?_ hch
        simp only [Graph.conj_comps', Graph.conj_coeff', List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          conjC_mkC, Kind.conj, Charge.flip, List.append_assoc]
  · rw [hE] at ht
    dsimp only at ht
    obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
    obtain ⟨i, hi, hk, hx, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
    rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
    · exact keyA _ _ .plus (List.getElem_cons_eraseIdx_perm hi).symm hk hx co _ rfl hch
    · exact keyB .plus co _ rfl hch
    · have hB : g.pCore.comps.Perm ([g.pCore.comps[i], (g.pCore.comps.eraseIdx i)[j]] ++
          (g.pCore.comps.eraseIdx i).eraseIdx j) :=
        (List.getElem_cons_eraseIdx_perm hi).symm.trans
          (List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hj).symm)
      exact keyC _ _ _ .plus hB hk hx _ _ (Or.inl ⟨rfl, rfl⟩) ps hps co _
        (by simp only [List.append_assoc]) hch

end RoundL3

/-! ## Terms with one new atom read inside `P_x`: values -/

section PLiftVal

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

theorem pv_map' {V W : Type*} (D₀ : Data ι) (σ : W → ι) (f : V → W)
    (cs : List (Comp V)) : pv D₀ σ (cs.map (Comp.map f)) = pv D₀ (σ ∘ f) cs := by
  rw [pv_eq, pv_eq, rv_map, dv_map]

/-- A term with one new atom read inside `P_x`: the factors of `Γ_ω`, and the sum over the label
of the new atom. -/
theorem T1_plift (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (hcs : Unl cs) (e : Fin k → ι) (ω : Ω) (s : Fin n → ι) :
    T1 PF D e ω ⟨cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), d⟩ s =
      pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, d.eval (msc A.z) *
        dv (D ω) (Sum.elim e (Fin.append s ![α])) cs *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) cs) ω := by
  unfold T1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [termR_lifted A (liftA 1 x) cs _ d hcs (fun c hc => ?_) _ ω, pv_map',
    elim_append_comp_liftA, elim_append_liftA, m_eq A]
  · ring
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, pEnv_unl g c' hc']

theorem pLiftT_cons_t1 (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (hcs : Unl cs) (E : TExpansion k n) :
    pLiftT x g (t1 cs d :: E) =
      t1 (cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))) d :: pLiftT x g E := by
  unfold pLiftT
  rw [List.filterMap_cons, if_neg]
  · rfl
  · simp only [t1, List.any_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro c hc
    rw [hcs c hc]
    simp

theorem pLiftT_map_t1 (x : Atom k n) (g : Graph k n) {β : Type*} (l : List β)
    (G : β → List (Comp (Atom k (n + 1)))) (d : β → Coeff) (hG : ∀ j ∈ l, Unl (G j)) :
    pLiftT x g (l.map fun j => t1 (G j) (d j)) =
      l.map fun j => t1 ((G j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))) (d j) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, pLiftT_cons_t1 x g _ _ (hG j (by simp)),
      ih fun j' hj' => hG j' (List.mem_cons_of_mem _ hj')]
    rfl

theorem pLiftT_nil (x : Atom k n) (g : Graph k n) : pLiftT x g [] = [] := rfl

theorem pLiftT_append (x : Atom k n) (g : Graph k n) (E₁ E₂ : TExpansion k n) :
    pLiftT x g (E₁ ++ E₂) = pLiftT x g E₁ ++ pLiftT x g E₂ := by
  unfold pLiftT
  rw [List.filterMap_append]

theorem good_of_test {f : Ω → ℂ} (h : A.Test f) : A.Good f := A.test_good f h

/-- [II, (4.23)] with `P_x` distributed over the sums. -/
theorem weightP_lin (X : ι) (F : Ω → ℂ) (hF : A.Test F) (ω : Ω) :
    PF.P X (fun ω' => (A.G ω' X X - msc A.z) * F ω') ω =
      ∑ α, msc A.z ^ 2 * (A.S X α : ℂ) * PF.P X (fun ω' => (A.G ω' α α - msc A.z) * F ω') ω +
      ∑ α, msc A.z * (A.S X α : ℂ) *
        PF.P X (fun ω' => (A.G ω' α α - msc A.z) * (A.G ω' X X - msc A.z) * F ω') ω -
      ∑ α, msc A.z * (A.S X α : ℂ) *
        PF.P X (fun ω' => A.G ω' α X * A.dh α X F ω') ω := by
  have h := congrFun (weightP Ω ι PF D A X F hF) ω
  simp only [Pi.sub_apply] at h
  rw [h]
  have tG : ∀ a b, A.Test fun ω => A.G ω a b := test_G A
  have t1' : ∀ α, A.Test fun ω' => (A.G ω' α α - msc A.z) * F ω' :=
    fun α => test_mul' A (test_sub' A (tG _ _) (test_const' A _)) hF
  have t2' : ∀ α, A.Test fun ω' => (A.G ω' α α - msc A.z) * (A.G ω' X X - msc A.z) * F ω' :=
    fun α => test_mul' A (test_mul' A (test_sub' A (tG _ _) (test_const' A _))
      (test_sub' A (tG _ _) (test_const' A _))) hF
  have t3' : ∀ α, A.Test fun ω' => A.G ω' α X * A.dh α X F ω' :=
    fun α => test_mul' A (tG _ _) (test_dh' A _ _ hF)
  rw [P_congr' (f := fun ω => msc A.z ^ 2 * ∑ α, (A.S X α : ℂ) * (A.G ω α α - msc A.z) * F ω +
      msc A.z * ∑ α, (A.S X α : ℂ) * (A.G ω α α - msc A.z) * (A.G ω X X - msc A.z) * F ω)
    (g := fun ω => (∑ α, msc A.z ^ 2 * (A.S X α : ℂ) * ((A.G ω α α - msc A.z) * F ω)) +
      ∑ α, msc A.z * (A.S X α : ℂ) * ((A.G ω α α - msc A.z) * (A.G ω X X - msc A.z) * F ω))
    (fun ω => by simp only [Finset.mul_sum]; congr 1 <;>
      exact Finset.sum_congr rfl fun α _ => by ring)]
  rw [P_congr' (f := fun ω => msc A.z * ∑ α, (A.S X α : ℂ) * A.G ω α X * A.dh α X F ω)
    (g := fun ω => ∑ α, msc A.z * (A.S X α : ℂ) * (A.G ω α X * A.dh α X F ω))
    (fun ω => by simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => by ring)]
  have g1 : ∀ α, A.Good fun ω => msc A.z ^ 2 * (A.S X α : ℂ) * ((A.G ω α α - msc A.z) * F ω) :=
    fun α => good_of_test A (test_mul' A (test_const' A _) (t1' α))
  have g2 : ∀ α, A.Good fun ω => msc A.z * (A.S X α : ℂ) *
      ((A.G ω α α - msc A.z) * (A.G ω X X - msc A.z) * F ω) :=
    fun α => good_of_test A (test_mul' A (test_const' A _) (t2' α))
  have g3 : ∀ α, A.Good fun ω => msc A.z * (A.S X α : ℂ) * (A.G ω α X * A.dh α X F ω) :=
    fun α => good_of_test A (test_mul' A (test_const' A _) (t3' α))
  rw [P_add' A (good_sum' A _ g1) (good_sum' A _ g2), P_sum' A _ g1, P_sum' A _ g2, P_sum' A _ g3]
  simp only [P_cmul' A _ (good_of_test A (t1' _)), P_cmul' A _ (good_of_test A (t2' _)),
    P_cmul' A _ (good_of_test A (t3' _))]

end PLiftVal

/-! ## The value of [II, (4.23)] inside `P_x` -/

theorem dTerms_unl {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    (h : ∀ c ∈ cs, c.label = none) : ∀ d ∈ dTerms p q cs, ∀ c ∈ d, c.label = none := by
  intro d hd c hc
  obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd
  rcases List.mem_append.1 hc with h' | h'
  · exact h c (List.mem_of_mem_eraseIdx h')
  · have key : ∀ (ch : Charge) (u v : V), (solidC ch u v).label = none := by
      intro ch u v; unfold solidC; split_ifs <;> rfl
    rcases hk : cs[j] with ⟨κ, a, b, mi, l⟩
    rw [hk] at hps
    cases κ with
    | G ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact key _ _ _
    | weight ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact key _ _ _
    | light ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact key _ _ _
    | _ => simp [Comp.dPieces] at hps

section ValueL

variable {k n : ℕ}

theorem core_lift_bas {g : Graph k n} (hp : g.Plain) (L : List (Comp (Atom k n)))
    (hL : ∀ c ∈ L, c ∈ g.pCore.comps) :
    ∀ c ∈ liftCs 1 L, basB c = true ∧ c.label = none := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  refine ⟨by rw [basB_map]; exact pCore_basB hp c' (hL c' hc'), ?_⟩
  simp [Comp.map, pCore_unl g c' (hL c' hc')]

/-- The value of [II, (4.23)] at the first light weight of positive charge on `x` of `𝒢`, inside
`P_x`. -/
theorem valueL_plain {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    {E : TExpansion k n} (hE : oWeightP2Pos x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i hi
  obtain ⟨hlt, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hpi
  simp only [Option.some.injEq] at hE
  subst hE
  set core := g.pCore.comps with hcore
  set core' := core.eraseIdx i with hcore'
  have hsub' : ∀ c ∈ core', c ∈ g.pCore.comps := fun c hc => List.mem_of_mem_eraseIdx hc
  have hbF := core_lift_bas hp core' hsub'
  have hU1 : Unl (liftCs 1 core' ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (hbF c hc).2, by simp [Unl, mkC]⟩
  have hU2 : Unl (liftCs 1 core ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (core_lift_bas hp core (fun c hc => hc) c hc).2,
      by simp [Unl, mkC]⟩
  have hspec := fun (σ : Atom k (n + 1) → ι) =>
    dTerms_spec A σ (newA 0) (liftA 1 x) (liftCs 1 core') hbF
  have hU3 : ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'),
      Unl (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)]) :=
    fun d hd => Unl_append.2 ⟨dTerms_unl (fun c hc => (hbF c hc).2) d hd, by simp [Unl, mkC]⟩
  change S PF D e ω (pLiftT x g ([t1 (liftCs 1 core' ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * cm * g.coeff),
    t1 (liftCs 1 core ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * g.coeff)] ++
    (dTerms (newA 0) (liftA 1 x) (liftCs 1 core')).map fun d =>
      t1 (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)])
        (cm * g.coeff))) = g.valR PF D e ω
  rw [pLiftT_append, pLiftT_cons_t1 x g _ _ hU1, pLiftT_cons_t1 x g _ _ hU2,
    pLiftT_map_t1 x g _ _ _ hU3]
  simp only [List.cons_append, List.nil_append, List.singleton_append]
  rw [S_cons_t1, S_cons_t1, pLiftT_nil, List.nil_append, S_map_t1, valR_T0,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [T1_plift A x g _ _ hU1, T1_plift A x g _ _ hU2]
  rw [List.map_congr_left fun d hd => T1_plift A x g _ _ (hU3 d hd) e ω s]
  rw [T0, termR_pform A hlab hp.labRand, m_eq A]
  -- the core and its parts
  have hci : core[i].kind = .light .plus ∧ core[i].x = x := hpi
  have hperm : core.Perm (core[i] :: core') := (List.getElem_cons_eraseIdx_perm hlt).symm
  have hrcore : ∀ ω', rv (D ω') (Sum.elim e s) core =
      (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) * rv (D ω') (Sum.elim e s) core' := by
    intro ω'
    have : rv (D ω') (Sum.elim e s) core = rv (D ω') (Sum.elim e s) (core[i] :: core') := by
      unfold rv; exact (List.Perm.prod_eq ((hperm.filter _).map _))
    rw [this, rv_cons]
    have hck : core[i] = mkC (.light .plus) x x := by
      have hmem : core[i] ∈ g.pCore.comps := List.getElem_mem hlt
      obtain ⟨d, hd, -, hdc⟩ := pCore_mem hmem
      have hwf := (hp d hd).2.2.2.2.1
      have hdk : d.kind = .light .plus := by rw [← hci.1, hdc]
      have hdx : d.x = x := by rw [← hci.2, hdc]
      have hdy : d.y = x := by rw [hwf (by rw [hdk]; rfl), hdx]
      have hdm : d.minor = [] := (hp d hd).1
      rw [hdc]
      rcases d with ⟨κ, a, b, mi, l⟩
      simp only at hdk hdx hdy hdm
      subst hdk hdx hdy hdm
      rfl
    rw [hck]
    simp [val_light A, Charge.apply, Kind.isRandom]
  have hdcore : dv (D ω) (Sum.elim e s) core = dv (D ω) (Sum.elim e s) core' := by
    have : dv (D ω) (Sum.elim e s) core = dv (D ω) (Sum.elim e s) (core[i] :: core') := by
      unfold dv; exact (List.Perm.prod_eq ((hperm.filter _).map _))
    rw [this, dv_cons, hci.1]
    simp [Kind.isRandom]
  set F : Ω → ℂ := fun ω' => rv (D ω') (Sum.elim e s) core' with hF
  have hFt : A.Test F := rv_test A _ core' fun c hc => pCore_basB hp c (hsub' c hc)
  have hσα : ∀ α : ι, Sum.elim e (Fin.append s ![α]) ∘ liftA 1 = Sum.elim e s := fun α =>
    elim_append_comp_liftA e s ![α]
  -- the first two terms
  have h1 : ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) (liftCs 1 core' ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ) := by
    intro α
    simp [dv_liftCs, hσα, Kind.isRandom, val_s A]
  have h1r : ∀ α ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (liftCs 1 core' ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      (A.G ω' α α - msc A.z) * F ω' := by
    intro α ω'
    simp [rv_liftCs, hσα, Kind.isRandom, val_light A, Charge.apply, hF]
    ring
  have h2 : ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) (liftCs 1 core ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ) := by
    intro α
    simp [dv_liftCs, hσα, Kind.isRandom, val_s A, hdcore]
  have h2r : ∀ α ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (liftCs 1 core ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      (A.G ω' α α - msc A.z) * (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) * F ω' := by
    intro α ω'
    simp [rv_liftCs, hσα, Kind.isRandom, val_light A, Charge.apply, hrcore, hF]
    ring
  -- the derivative terms
  have hdd : ∀ α, ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'),
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)]) =
        dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ) := by
    intro α d hd
    have := ((hspec (Sum.elim e (Fin.append s ![α]))).1 d hd).2 (D ω)
    rw [dv_liftCs, hσα] at this
    simp [this, Kind.isRandom, val_s A]
  have hdr : ∀ α, ∀ ω', ((dTerms (newA 0) (liftA 1 x) (liftCs 1 core')).map fun d =>
      rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)])).sum =
        -(A.G ω' α (Sum.elim e s x) * A.dh α (Sum.elim e s x) F ω') := by
    intro α ω'
    have := (hspec (Sum.elim e (Fin.append s ![α]))).2 ω'
    simp only [rv_liftCs, hσα, elim_append_newA, Matrix.cons_val_zero, elim_append_liftA] at this
    have hpt : ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'),
        rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 x)]) =
          rv (D ω') (Sum.elim e (Fin.append s ![α])) d * A.G ω' α (Sum.elim e s x) := by
      intro d _
      simp [Kind.isRandom, val_G A, Charge.apply]
    refine (congrArg List.sum (List.map_congr_left hpt)).trans ?_
    rw [List.sum_map_mul_right, this]
    ring
  have hgd : ∀ α, ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'), A.Good fun ω' =>
      rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)]) := by
    intro α d hd
    refine good_of_test A (rv_test A _ _ fun c hc => ?_)
    rcases List.mem_append.1 hc with h | h
    · exact (((hspec (Sum.elim e (Fin.append s ![α]))).1 d hd).1 c h).1
    · simp at h; rcases h with rfl | rfl <;> rfl
  have hD : ((dTerms (newA 0) (liftA 1 x) (liftCs 1 core')).map fun d =>
      pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (cm * g.coeff).eval (msc A.z) *
        dv (D ω) (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 x)]) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++
          [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)])) ω).sum =
      ∑ α, pv (D ω) (Sum.elim e s) g.pEnv * (msc A.z * g.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ)) *
        -PF.P (Sum.elim e s x) (fun ω' => A.G ω' α (Sum.elim e s x) *
          A.dh α (Sum.elim e s x) F ω') ω) := by
    rw [List.sum_map_mul_left, list_finset_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
    rw [List.map_congr_left fun d hd => by rw [hdd α d hd]]
    rw [List.sum_map_mul_left, ← P_listSum' A _ (hgd α), P_congr' (hdr α),
      P_neg' A (good_of_test A (test_mul' A (test_G A _ _) (test_dh' A _ _ hFt))),
      ceval_mul, ceval_cm]
  rw [hD, hdcore, P_congr' hrcore]
  simp only [h1, h2, h1r, h2r, ceval_mul, ceval_cm]
  rw [weightP_lin A (Sum.elim e s x) F hFt ω]
  simp only [Finset.mul_sum, mul_add, mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

end ValueL

/-! ## Complex conjugation of the identities inside `P_x` -/

section ConjValue

variable {k n : ℕ}

theorem Kind.conj_isRandom' (κ : Kind) : κ.conj.isRandom = κ.isRandom := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem rl_conjC {V : Type*} (y : V) (c : Comp V) : rl y (conjC c) = conjC (rl y c) := by
  unfold rl
  by_cases h : c.kind.isRandom = true
  · rw [if_pos (by simpa [conjC, Kind.conj_isRandom'] using h), if_pos h]; rfl
  · rw [if_neg (by simpa [conjC, Kind.conj_isRandom'] using h), if_neg h]

theorem pEnv_conj (g : Graph k n) : g.conj.pEnv = g.pEnv.map conjC := by
  unfold Graph.pEnv
  rw [Graph.conj_comps', List.filter_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp [conjC, Kind.conj_isRandom']

theorem pLiftT_conj (x : Atom k n) (g : Graph k n) (E : TExpansion k n) :
    pLiftT x g E.conj = (pLiftT x g.conj E).conj := by
  unfold pLiftT TExpansion.conj
  rw [List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro t _
  simp only [Function.comp_apply, Graph.conj_comps', List.any_map]
  have hq : ((t.g.comps.map conjC).any fun c => decide (c.label = some (.Q, t.f x))) =
      (t.g.comps.any fun c => decide (c.label = some (.Q, t.f x))) := by
    rw [List.any_map]; rfl
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hq ▸ h1) h2
  · exact absurd (hq ▸ h2) h1
  · simp only [Option.map_some, Option.some.injEq]
    have e1 : (t.g.comps.map conjC).map (rl (t.f x)) =
        (t.g.comps.map (rl (t.f x))).map conjC := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun c _ => rl_conjC _ _
    have e2 : g.pEnv.map (Comp.map t.f) = ((g.pEnv.map conjC).map (Comp.map t.f)).map conjC := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun c _ => by
        simp only [Function.comp_apply, conjC_map, conjC_conjC]
    show (⟨t.nOut, ⟨(t.g.comps.map conjC).map (rl (t.f x)) ++ g.pEnv.map (Comp.map t.f),
      Coeff.conj t.g.coeff⟩, t.f⟩ : Tracked k n) = ⟨t.nOut, ⟨(t.g.comps.map (rl (t.f x)) ++
        g.conj.pEnv.map (Comp.map t.f)).map conjC, Coeff.conj t.g.coeff⟩, t.f⟩
    rw [e1, e2, pEnv_conj, ← List.map_append]

end ConjValue

section ConjValue2

variable {k n : ℕ}

/-- A formal sum with the value of `\overline{Γ}` gives, conjugated, a formal sum with the value
of `Γ`. -/
theorem valueEq_conj {g : Graph k n} {F : TExpansion k n}
    (hF : F.ValueEq g.conj modelAdm) (hokg : OK g.comps) (hokF : ∀ t ∈ F, OK t.g.comps) :
    F.conj.ValueEq g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  have h1 := congrFun (hF Ω ι PF (fun ω => conjD (D ω)) ⟨conjAdm A⟩ e) ω
  have h2 := valR_conj (conjAdm A) g hokg e ω
  simp only [conjD_conjD] at h2
  simp only [TExpansion.conj, TExpansion.forget, Expansion.valR, List.map_map,
    Function.comp_def] at h1 ⊢
  rw [List.map_congr_left fun t ht => valR_conj A t.g (hokF t ht) e ω]
  have h3 : ((F.map fun t => star (t.g.valR PF (fun ω => conjD (D ω)) e ω)).sum) =
      star ((F.map fun t => t.g.valR PF (fun ω => conjD (D ω)) e ω).sum) := by
    rw [Complex.star_def, map_list_sum, List.map_map]
    rfl
  rw [h3, h1, h2]
  simp

end ConjValue2

/-! ## The value of [II, (4.23)] inside `P_x`, both charges -/

section ValueL2

variable {k n : ℕ}

theorem Kind.conj_isWeight' (κ : Kind) : κ.conj.isWeight = κ.isWeight := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem Kind.conj_inv' (κ : Kind) (ch : Charge) : κ.conj = .inv ch ↔ κ = .inv ch.flip := by
  cases κ with
  | inv c => cases c <;> cases ch <;> simp [Kind.conj, Charge.flip]
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem Kind.conj_wD' (κ : Kind) (ch : Charge) (d : ℕ) :
    κ.conj = .wD ch d ↔ κ = .wD ch.flip d := by
  cases κ with
  | wD c d' => cases c <;> cases ch <;> simp [Kind.conj, Charge.flip]
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem Kind.conj_dot' (κ : Kind) : κ.conj = .dot ↔ κ = .dot := by
  cases κ with
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem Graph.Plain.conj {g : Graph k n} (hp : g.Plain) : g.conj.Plain := by
  intro c hc
  rw [Graph.conj_comps'] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp d hd
  refine ⟨h1, fun ch h => h2 ch.flip ((Kind.conj_inv' _ _).1 h),
    fun ch dd h => h3 ch.flip dd ((Kind.conj_wD' _ _ _).1 h),
    fun h => h4 ((Kind.conj_dot' _).1 h), ?_, ?_⟩
  · intro hw
    exact h5 (by simpa [conjC, Kind.conj_isWeight'] using hw)
  · intro hl
    simpa [conjC, Kind.conj_isRandom'] using h6 hl

theorem lab_conj {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) :
    ∀ c ∈ g.conj.comps, c.label = none ∨ c.label = some (.P, x) := by
  intro c hc
  rw [Graph.conj_comps'] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact hlab d hd

theorem pCore_conj (g : Graph k n) : g.conj.pCore = g.pCore.conj := by
  unfold Graph.pCore
  simp only [Graph.conj_comps', Graph.conj_coeff']
  congr 1
  rw [List.filter_map, List.map_map, List.map_map]
  rw [List.filter_congr (p := (fun c : Comp (Atom k n) => c.label.isSome || !c.kind.isRandom) ∘ conjC)
    (q := fun c => c.label.isSome || !c.kind.isRandom)
    (fun c _ => by simp [conjC, Kind.conj_isRandom'])]
  rfl

theorem okP {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain) :
    OK g.comps := by
  intro c hc
  rcases hlab c hc with h | h
  · exact Or.inl h
  · refine Or.inr ⟨hp.labRand c hc (by rw [h]; rfl), ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := hp c hc
    unfold basB
    rw [h1]
    cases hk : c.kind with
    | inv ch => exact absurd hk (h2 ch)
    | wD ch dd => exact absurd hk (h3 ch dd)
    | _ => rfl

theorem basB_solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    basB (solidC ch u v) = true ∧ (solidC ch u v).label = none := by
  unfold solidC; split_ifs <;> exact ⟨rfl, rfl⟩

theorem dTerms_ub {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    (h : ∀ c ∈ cs, c.label = none ∧ basB c = true) :
    ∀ d ∈ dTerms p q cs, ∀ c ∈ d, c.label = none ∧ basB c = true := by
  intro d hd c hc
  obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd
  rcases List.mem_append.1 hc with h' | h'
  · exact h c (List.mem_of_mem_eraseIdx h')
  · rcases hk : cs[j] with ⟨κ, a, b, mi, l⟩
    rw [hk] at hps
    cases κ with
    | G ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
    | weight ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
    | light ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
    | _ => simp [Comp.dPieces] at hps

theorem ok_pLiftT {x : Atom k n} {g : Graph k n} {E : TExpansion k n}
    (hE : ∀ s ∈ E, ∀ c ∈ s.g.comps, c.label = none ∧ basB c = true) :
    ∀ t ∈ pLiftT x g E, OK t.g.comps := by
  intro t ht
  obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨hl, hb⟩ := hE s hs d hd
    unfold rl
    split_ifs with hr
    · exact Or.inr ⟨hr, by simpa [basB] using hb⟩
    · exact Or.inl hl
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    left
    simp [Comp.map, pEnv_unl g d hd]

theorem oWeightP2Pos_ub {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hh : ∀ c ∈ h.comps, c.label = none ∧ basB c = true) (hE : oWeightP2Pos x h = some E) :
    ∀ s ∈ E, ∀ c ∈ s.g.comps, c.label = none ∧ basB c = true := by
  intro s hs
  obtain ⟨i, hi, -, -, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
  have hl : ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, c ∈ h.comps) →
      ∀ c ∈ liftCs 1 L, c.label = none ∧ basB c = true := by
    intro L hL c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2⟩ := hh c' (hL c' hc')
    exact ⟨by simp [Comp.map, h1], by rw [basB_map]; exact h2⟩
  have hm : ∀ (κ : Kind) (u v : Atom k (n + 1)), κ.isRandom = false ∨ κ = .light .plus ∨
      κ = .G .plus → (mkC κ u v).label = none ∧ basB (mkC κ u v) = true := by
    intro κ u v hκ
    rcases hκ with hκ | rfl | rfl
    · refine ⟨rfl, ?_⟩
      unfold basB; simp only [mkC, List.isEmpty_nil, Bool.true_and]
      cases κ <;> simp_all [Kind.isRandom]
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  simp only
  rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl _ (fun c hc => List.mem_of_mem_eraseIdx hc) c h'
    · simp at h'; rcases h' with rfl | rfl
      · exact hm _ _ _ (Or.inl rfl)
      · exact hm _ _ _ (Or.inr (Or.inl rfl))
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl _ (fun c hc => hc) c h'
    · simp at h'; rcases h' with rfl | rfl
      · exact hm _ _ _ (Or.inl rfl)
      · exact hm _ _ _ (Or.inr (Or.inl rfl))
  · intro c hc
    have hF := hl (h.comps.eraseIdx i) (fun c hc => List.mem_of_mem_eraseIdx hc)
    have hd : liftCs 1 ((h.comps.eraseIdx i).eraseIdx j) ++ ps ∈
        dTerms (newA 0) (liftA 1 x) (liftCs 1 (h.comps.eraseIdx i)) := by
      rw [psteps_mem_dTerms]
      refine ⟨j, by simpa [liftCs] using hj, ps, by simpa [liftCs] using hps, ?_⟩
      simp [liftCs, List.eraseIdx_map]
    rcases List.mem_append.1 hc with h' | h'
    · exact dTerms_ub hF _ hd c h'
    · simp at h'; rcases h' with rfl | rfl
      · exact hm _ _ _ (Or.inl rfl)
      · exact hm _ _ _ (Or.inr (Or.inr rfl))

/-- The value of `Õ^{(x),2}_weight` inside `P_x`. -/
theorem valueL {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain) :
    TExpansion.ValueEq (oWeightP2T x g) g modelAdm := by
  unfold oWeightP2T
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · dsimp only
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E'
    · dsimp only
      intro Ω ι _ _ PF D _ e
      funext ω
      simp [TExpansion.forget, Expansion.valR, Tracked.self]
    · dsimp only
      rw [pLiftT_conj]
      refine valueEq_conj ?_ (okP hlab hp) ?_
      · refine valueL_plain (lab_conj hlab) hp.conj ?_
        rw [pCore_conj]; exact hE'
      · refine ok_pLiftT (oWeightP2Pos_ub ?_ hE')
        intro c hc
        rw [← pCore_conj] at hc
        exact ⟨pCore_unl _ c hc, pCore_basB hp.conj c hc⟩
  · dsimp only
    exact valueL_plain hlab hp hE

end ValueL2

/-! ## Components at given positions -/

section PickErase

variable {α : Type*}

theorem zipIdx_nodup' (l : List α) : l.zipIdx.Nodup :=
  List.Nodup.of_map Prod.snd (zip_snd_nodup l)

theorem perm_pick_erase (is : List ℕ) (l : List α) :
    l.Perm (pickIdxs is l ++ eraseIdxs is l) := by
  unfold pickIdxs eraseIdxs
  rw [← List.map_append]
  conv_lhs => rw [← List.zipIdx_map_fst 0 l]
  exact ((List.filter_append_perm _ _).symm).map _

theorem zipIdx_filter_eq (l : List α) {i : ℕ} (hi : i < l.length) :
    (l.zipIdx.filter fun p => p.2 == i).Perm [(l[i], i)] := by
  rw [List.perm_ext_iff_of_nodup ((zipIdx_nodup' l).filter _) (List.nodup_singleton _)]
  rintro ⟨a, m⟩
  simp only [List.mem_filter, List.mem_zipIdx_iff_getElem?, beq_iff_eq, List.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h1, rfl⟩
    rw [List.getElem?_eq_getElem hi] at h1
    exact ⟨(Option.some.inj h1).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨List.getElem?_eq_getElem hi, rfl⟩

theorem pick_cons_filter {is : List ℕ} {l : List α} {i : ℕ} (hi : i < l.length)
    (his : i ∈ is) : (pickIdxs is l).Perm (l[i] :: pickIdxs (is.filter (· != i)) l) := by
  unfold pickIdxs
  have h1 := (List.filter_append_perm (fun p : α × ℕ => p.2 == i)
    (l.zipIdx.filter fun p => is.contains p.2)).symm
  rw [List.filter_filter, List.filter_filter] at h1
  have e1 : (l.zipIdx.filter fun p => (p.2 == i) && is.contains p.2) =
      l.zipIdx.filter fun p => p.2 == i := by
    apply List.filter_congr
    intro p _
    by_cases h : p.2 = i
    · simp [h, his]
    · simp [h]
  have e2 : (l.zipIdx.filter fun p => !(p.2 == i) && is.contains p.2) =
      l.zipIdx.filter fun p => (is.filter (· != i)).contains p.2 := by
    apply List.filter_congr
    intro p _
    by_cases h : p.2 = i
    · simp [h]
    · simp [h, List.contains_iff_mem, List.mem_filter]
  rw [e1, e2] at h1
  have := (h1.trans ((zipIdx_filter_eq l hi).append_right _)).map Prod.fst
  simpa using this

theorem pickIdxs_single {l : List α} {i : ℕ} (hi : i < l.length) :
    (pickIdxs [i] l).Perm [l[i]] := by
  have := pick_cons_filter (is := [i]) hi (List.mem_singleton_self _)
  have e : pickIdxs ([i].filter (· != i)) l = [] := by
    simp [pickIdxs]
  rw [e] at this
  exact this

theorem pickIdxs_two {l : List α} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≠ j) : (pickIdxs [i, j] l).Perm [l[i], l[j]] := by
  have h := pick_cons_filter (is := [i, j]) hi (by simp)
  have e : [i, j].filter (· != i) = [j] := by simp [Ne.symm hij]
  rw [e] at h
  exact h.trans (List.Perm.cons _ (pickIdxs_single hj))

end PickErase

/-! ## [II, (4.24)] inside `P_x`: terms moving edges at `x` to the new atom -/

section TermBase

variable {k n : ℕ}

/-- A solid edge with label `P_x` between `x` and `u`. -/
def EdgeAt (x u : Atom k n) (r : Comp (Atom k n)) : Prop :=
  r.kind.isSolid = true ∧ r.label = some (.P, x) ∧ ((r.x = x ∧ r.y = u) ∨ (r.x = u ∧ r.y = x))

/-- A component of kind `κ` with label `P` at the image of `x` between the new atom and `u`. -/
def NewEdge (x u : Atom k n) (κ : Kind) (a : Comp (Atom k (n + 1))) : Prop :=
  a.kind = κ ∧ a.minor = [] ∧ a.label = some (.P, liftA 1 x) ∧
    ((a.x = newA 0 ∧ a.y = liftA 1 u) ∨ (a.x = liftA 1 u ∧ a.y = newA 0))

theorem NewEdge.congr_kind {x u : Atom k n} {κ κ' : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewEdge x u κ a) (e : κ = κ') : NewEdge x u κ' a := e ▸ h

theorem EdgeAt.facts {C : ℕ} {x u : Atom k n} {g : Graph k n} (hS : St C x g)
    {r : Comp (Atom k n)} (hr : r ∈ g.comps) (h : EdgeAt x u r) :
    u ≠ x ∧ ¬ g.SameBlock u x := by
  have hne := hS.nn.noLoop r hr h.1
  have hib := hS.nn.inBlk r hr h.1
  rcases h.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hne hib
  · exact ⟨Ne.symm hne, fun h' => hib (Graph.sameBlock_symm h')⟩
  · exact ⟨hne, hib⟩

theorem NewEdge.aok {x u : Atom k n} {g : Graph k n} {κ : Kind}
    {a : Comp (Atom k (n + 1))} (h : NewEdge x u κ a) (hκ : κ.isSolid = true) : AOK x g a := by
  obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hκ
  exact aok_Gnew (h.1.trans hch) h.2.1 h.2.2.1 h.2.2.2

theorem NewEdge.touch {x u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewEdge x u κ a) : touchN a = true ∧ otherN a = liftA 1 u := by
  unfold touchN otherN
  rcases h.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · rw [h1, h2]
    simp [liftA_ne_newA]

theorem NewEdge.nx {x u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    {g₁ : Graph k (n + 1)} (h : NewEdge x u κ a) (ha : a ∈ g₁.comps) (hκ : κ ≠ .xdot) :
    NX g₁ (newA 0) (liftA 1 u) :=
  NX.ends ha (by rw [h.1]; exact hκ) h.2.2.2

theorem NewEdge.bb {x u : Atom k n} {a : Comp (Atom k (n + 1))}
    {g₁ : Graph k (n + 1)} (h : NewEdge x u (.G .plus) a) (ha : a ∈ g₁.comps)
    (hu : u.isRight = true) : BB g₁ (newA 0) (liftA 1 u) := by
  refine BB.ends h.2.2.2 (BB_of_G ha h.1 ?_ ?_)
  · rcases h.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact newA_isRight
    · rw [liftA_isRight]; exact hu
  · rcases h.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · rw [liftA_isRight]; exact hu
    · exact newA_isRight

open Classical in
theorem NewEdge.wbp {x u : Atom k n} {g : Graph k n} {κ : Kind}
    {a : Comp (Atom k (n + 1))} {g₁ : Graph k (n + 1)} (h : NewEdge x u κ a)
    (hκ : κ.isSolid = true) (hu : ¬ g.SameBlock u x)
    (hblk : ∀ u v, g₁.SameBlock (liftA 1 u) (liftA 1 v) ↔ g.SameBlock u v)
    (hnew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0) :
    wBP (fun v => g₁.SameBlock v (liftA 1 x)) a = 0 := by
  obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hκ
  have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h' =>
    liftA_ne_newA 1 x 0 ((hnew _).1 h')
  rw [wBP_G (h.1.trans hch) (by rw [h.2.2.1]; rfl)]
  rcases h.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [hαx, hblk, hu]

open Classical in
theorem EdgeAt.wbp {C : ℕ} {x u : Atom k n} {g : Graph k n} (hS : St C x g)
    {r : Comp (Atom k n)} (hr : r ∈ g.comps) (h : EdgeAt x u r) :
    wBP (fun v => g.SameBlock v x) r = 1 := by
  obtain ⟨-, hu⟩ := h.facts hS hr
  obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 h.1
  rw [wBP_G hch (by rw [h.2.1]; rfl)]
  rcases h.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    simp [hu, Graph.sameBlock_refl]

/-- The main terms of [II, (4.24)] inside `P_x`: two edges at `x` moved to the new atom, with a
light weight at `x` or not. -/
theorem termBase2 {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r₁ r₂ : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r₁, r₂] ++ rest)) {u₁ u₂ : Atom k n}
    (h₁ : EdgeAt x u₁ r₁) (h₂ : EdgeAt x u₂ r₂)
    {a₁ a₂ : Comp (Atom k (n + 1))} (ha₁ : NewEdge x u₁ r₁.kind a₁)
    (ha₂ : NewEdge x u₂ r₂.kind a₂) {X : List (Comp (Atom k (n + 1)))}
    (hX : ∀ a ∈ X, ∃ ch, a = ⟨.light ch, liftA 1 x, liftA 1 x, [], some (.P, liftA 1 x)⟩)
    (hXl : X.length ≤ 1) {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X)))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hN := hS.nn
  have hr₁ : r₁ ∈ g.comps := hR.symm.subset (by simp)
  have hr₂ : r₂ ∈ g.comps := hR.symm.subset (by simp)
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  have hmem : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X, a ∈ g₁.comps :=
    fun a ha => hL.symm.subset (List.mem_append_right _ ha)
  have hsm := hmem (mkC (.waved .s) (liftA 1 x) (newA 0)) (by simp)
  have ha₁m := hmem a₁ (by simp)
  have ha₂m := hmem a₂ (by simp)
  have hs₁ : r₁.kind.isSolid = true := h₁.1
  have hs₂ : r₂.kind.isSolid = true := h₂.1
  obtain ⟨ch₁, hk₁⟩ := Kind.isSolid_iff.1 hs₁
  obtain ⟨ch₂, hk₂⟩ := Kind.isSolid_iff.1 hs₂
  have hXs : ∀ a ∈ X, a.kind.isSolid = false := by
    intro a ha; obtain ⟨ch, rfl⟩ := hX a ha; rfl
  have hNXs : NX g₁ (liftA 1 x) (newA 0) := NX.ends hsm (by simp [mkC]) (Or.inl ⟨rfl, rfl⟩)
  have hBs : BB g₁ (liftA 1 x) (newA 0) :=
    BB.ends (d := mkC (.waved .s) (liftA 1 x) (newA 0)) (Or.inl ⟨rfl, rfl⟩)
      (BB_of_mol hsm rfl hx₁ newA_isRight)
  have hcon1 : ∀ {r : Comp (Atom k n)} {u : Atom k n} {a : Comp (Atom k (n + 1))},
      EdgeAt x u r → NewEdge x u r.kind a → a ∈ g₁.comps →
      Relation.EqvGen (fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v)
        (liftA 1 r.x) (liftA 1 r.y) := by
    intro r u a hr ha ham
    have hp : NX g₁ (liftA 1 x) (liftA 1 u) :=
      hNXs.trans _ _ _ (ha.nx ham (Kind.ne_xdot_of_isRandom (Kind.isRandom_of_isSolid hr.1)))
    rcases hr.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hp
    · exact hp.symm
  have hblue1 : ∀ {r : Comp (Atom k n)} {u : Atom k n} {a : Comp (Atom k (n + 1))},
      EdgeAt x u r → NewEdge x u r.kind a → a ∈ g₁.comps → r.kind = .G .plus →
      ∀ i j, r.x = .inr i → r.y = .inr j →
        Relation.EqvGen (bconn g₁) (Fin.castAdd 1 i) (Fin.castAdd 1 j) := by
    intro r u a hr ha ham hk i j hi hj
    have hu : u.isRight = true := by
      rcases hr.2.2 with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [← h2, hj]; rfl
      · rw [← h1, hi]; rfl
    have hp : BB g₁ (liftA 1 x) (liftA 1 u) := hBs.trans ((hk ▸ ha).bb ham hu)
    have hp' : BB g₁ (liftA 1 r.x) (liftA 1 r.y) := by
      rcases hr.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact hp
      · exact hp.symm
    obtain ⟨p, q, hp1, hq1, hpq⟩ := hp'
    rw [hi, liftA_inr] at hp1; rw [hj, liftA_inr] at hq1
    cases Sum.inr.inj hp1; cases Sum.inr.inj hq1
    exact hpq
  have hA : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X, AOK x g a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact aok_sx
      · exact ha₁.aok hs₁
      · exact ha₂.aok hs₂
    · obtain ⟨ch, rfl⟩ := hX a ha
      exact aok_W (Or.inr rfl) rfl rfl rfl
  have hfN : (([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X).filter fun a =>
      a.kind.isSolid && !touchN a) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · simp [mkC, Kind.isSolid]
      · simp [ha₁.touch.1]
      · simp [ha₂.touch.1]
    · simp [hXs a ha]
  have hfT : (([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X).filter fun a =>
      a.kind.isSolid && touchN a) = [a₁, a₂] := by
    have hXf : X.filter (fun a => a.kind.isSolid && touchN a) = [] :=
      List.filter_eq_nil_iff.2 (fun a ha => by simp [hXs a ha])
    rw [List.filter_append, hXf, List.append_nil]
    simp [mkC, Kind.isSolid, ha₁.touch.1, ha₂.touch.1, ha₁.1, ha₂.1, hk₁, hk₂]
  have hordX : psteps_ordL X = X.length := by
    unfold psteps_ordL
    rw [show X.map (fun c => c.kind.ord) = X.map fun _ => (1 : ℤ) from
      List.map_congr_left fun a ha => by obtain ⟨ch, rfl⟩ := hX a ha; rfl]
    simp
  have hordR : psteps_ordL [r₁, r₂] = 2 := by
    simp [psteps_ordL, hk₁, hk₂, Kind.ord] <;> norm_num
  have hordA : psteps_ordL ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X) = 4 + X.length := by
    unfold psteps_ordL at hordX ⊢
    rw [List.map_append, List.sum_append, hordX]
    simp [mkC, Kind.ord, ha₁.1, ha₂.1, hk₁, hk₂] <;> ring
  refine termGen hS hR ?_ hL hA (by simp) ?_ ?_ hch ?_ (by rw [hfN]; simp) (by rw [hfT]; simp)
    ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact h₁.2.1
    · exact h₂.2.1
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcon1 h₁ ha₁ ha₁m
    · exact hcon1 h₂ ha₂ ha₂m
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hblue1 h₁ ha₁ ha₁m
    · exact hblue1 h₂ ha₂ ha₂m
  · simp; omega
  · rw [hordR, hordA]; push_cast; linarith [(Nat.cast_nonneg X.length : (0 : ℤ) ≤ X.length)]
  · intro heq hlt
    rw [hordR, hordA] at heq
    have hX0 : X = [] := List.eq_nil_of_length_eq_zero (by push_cast at heq; omega)
    subst hX0
    obtain ⟨-, hu₁⟩ := h₁.facts hS hr₁
    obtain ⟨-, hu₂⟩ := h₂.facts hS hr₂
    refine ⟨?_, Or.inr (Or.inl ?_)⟩
    · simp only [List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        wBP_none (a := mkC (.waved .s) (liftA 1 x) (newA 0)) rfl,
        ha₁.wbp hs₁ hu₁ hlt.blk hlt.blkNew, ha₂.wbp hs₂ hu₂ hlt.blk hlt.blkNew,
        h₁.wbp hS hr₁, h₂.wbp hS hr₂]
      norm_num
    · intro a ha has hat
      simp only [List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · simp [mkC, Kind.isSolid] at has
      · rw [ha₁.touch.2, hlt.blk]; exact hu₁
      · rw [ha₂.touch.2, hlt.blk]; exact hu₂

/-- The term of [II, (4.24)] with one edge at `x` moved to the new atom and an edge between the new
atom and `x` added. -/
theorem termBase1 {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r₁ : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r₁] ++ rest)) {u₁ : Atom k n} (h₁ : EdgeAt x u₁ r₁)
    {a₁ b : Comp (Atom k (n + 1))} (ha₁ : NewEdge x u₁ r₁.kind a₁) {ch : Charge}
    (hb : NewEdge x x (.G ch) b) {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b]))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hN := hS.nn
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  have hmem : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b], a ∈ g₁.comps :=
    fun a ha => hL.symm.subset (List.mem_append_right _ ha)
  have hsm := hmem (mkC (.waved .s) (liftA 1 x) (newA 0)) (by simp)
  have ha₁m := hmem a₁ (by simp)
  have hs₁ : r₁.kind.isSolid = true := h₁.1
  obtain ⟨ch₁, hk₁⟩ := Kind.isSolid_iff.1 hs₁
  have hNXs : NX g₁ (liftA 1 x) (newA 0) := NX.ends hsm (by simp [mkC]) (Or.inl ⟨rfl, rfl⟩)
  have hBs : BB g₁ (liftA 1 x) (newA 0) :=
    BB.ends (d := mkC (.waved .s) (liftA 1 x) (newA 0)) (Or.inl ⟨rfl, rfl⟩)
      (BB_of_mol hsm rfl hx₁ newA_isRight)
  have hA : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b], AOK x g a := by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact aok_sx
    · exact ha₁.aok hs₁
    · exact hb.aok rfl
  refine termGen hS hR ?_ hL hA (by simp) ?_ ?_ hch (by simp) ?_ ?_ ?_ ?_
  · intro c hc
    rw [List.mem_singleton] at hc; subst hc; exact h₁.2.1
  · intro c hc
    rw [List.mem_singleton] at hc; subst hc
    have hp : NX g₁ (liftA 1 x) (liftA 1 u₁) :=
      hNXs.trans _ _ _ (ha₁.nx ha₁m (Kind.ne_xdot_of_isRandom (Kind.isRandom_of_isSolid hs₁)))
    rcases h₁.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hp
    · exact hp.symm
  · intro c hc hk i j hi hj
    rw [List.mem_singleton] at hc; subst hc
    have hu : u₁.isRight = true := by
      rcases h₁.2.2 with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [← h2, hj]; rfl
      · rw [← h1, hi]; rfl
    have hp : BB g₁ (liftA 1 x) (liftA 1 u₁) := hBs.trans ((hk ▸ ha₁).bb ha₁m hu)
    have hp' : BB g₁ (liftA 1 c.x) (liftA 1 c.y) := by
      rcases h₁.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact hp
      · exact hp.symm
    obtain ⟨p, q, hp1, hq1, hpq⟩ := hp'
    rw [hi, liftA_inr] at hp1; rw [hj, liftA_inr] at hq1
    cases Sum.inr.inj hp1; cases Sum.inr.inj hq1
    exact hpq
  · rw [List.filter_eq_nil_iff.2]
    · simp
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · simp [mkC, Kind.isSolid]
    · simp [ha₁.touch.1]
    · simp [hb.touch.1]
  · have : [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b].filter (fun a =>
        a.kind.isSolid && touchN a) = [a₁, b] := by
      simp [mkC, Kind.isSolid, ha₁.touch.1, hb.touch.1, ha₁.1, hb.1, hk₁]
    rw [this]; simp
  · have : psteps_ordL [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] = 4 := by
      simp [psteps_ordL, mkC, Kind.ord, ha₁.1, hb.1, hk₁] <;> norm_num
    rw [this]; simp [psteps_ordL, hk₁, Kind.ord] <;> norm_num
  · intro heq
    have : psteps_ordL [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] = 4 := by
      simp [psteps_ordL, mkC, Kind.ord, ha₁.1, hb.1, hk₁] <;> norm_num
    rw [this] at heq
    simp [psteps_ordL, hk₁, Kind.ord] at heq <;> norm_num at heq

end TermBase

/-! ## [II, (4.24)] inside `P_x`: the shapes of the terms -/

section ShapeE

variable {k n : ℕ}

/-- A solid edge between `x` and `u`. -/
def EdgeH (x u : Atom k n) (r : Comp (Atom k n)) : Prop :=
  r.kind.isSolid = true ∧ ((r.x = x ∧ r.y = u) ∨ (r.x = u ∧ r.y = x))

/-- A component of kind `κ` between the new atom and `u`, without minor and label. -/
def NewH (u : Atom k n) (κ : Kind) (a : Comp (Atom k (n + 1))) : Prop :=
  a = mkC κ (newA 0) (liftA 1 u) ∨ a = mkC κ (liftA 1 u) (newA 0)

/-- The shapes of the terms of [II, (4.24)] at `x` applied to the components `H`, other than the
terms with the label `Q_x`: two edges at `x` moved to the new atom (with a light weight at `x` or
not); one edge moved and an edge between the new atom and `x` added; a light weight on the new
atom added; a derivative term. All with the waved edge between `x` and the new atom. -/
def ShapeE (x : Atom k n) (H : List (Comp (Atom k n)))
    (cs : List (Comp (Atom k (n + 1)))) : Prop :=
  (∃ (r₁ r₂ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (u₁ u₂ : Atom k n)
      (a₁ a₂ : Comp (Atom k (n + 1))) (X : List (Comp (Atom k (n + 1)))),
      H.Perm ([r₁, r₂] ++ B) ∧ EdgeH x u₁ r₁ ∧ EdgeH x u₂ r₂ ∧ NewH u₁ r₁.kind a₁ ∧
      NewH u₂ r₂.kind a₂ ∧ (∀ a ∈ X, ∃ ch, a = mkC (.light ch) (liftA 1 x) (liftA 1 x)) ∧
      X.length ≤ 1 ∧
      cs = liftCs 1 B ++ ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X)) ∨
  (∃ (r₁ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (u₁ : Atom k n)
      (a₁ b : Comp (Atom k (n + 1))) (ch : Charge),
      H.Perm ([r₁] ++ B) ∧ EdgeH x u₁ r₁ ∧ NewH u₁ r₁.kind a₁ ∧ NewH x (.G ch) b ∧
      (cs = liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] ∨
        cs = liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁])) ∨
  (∃ ch : Charge, cs = liftCs 1 H ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light ch) (newA 0) (newA 0)]) ∨
  (∃ (r c : Comp (Atom k n)) (B : List (Comp (Atom k n))) (z : Atom k n) (p q : Atom k (n + 1))
      (ps : List (Comp (Atom k (n + 1)))) (e₀ : Comp (Atom k (n + 1))),
      H.Perm ([r, c] ++ B) ∧ EdgeH x z r ∧ c.kind.isRandom = true ∧
      (c.kind.isSolid = true → c.x ≠ x ∧ c.y ≠ x) ∧
      ((p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0)) ∧
      (c.map (liftA 1)).dPieces p q = some ps ∧ NewH z r.kind e₀ ∧
      cs = liftCs 1 B ++ (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), e₀]))

theorem rl_mkC_random {V : Type*} (y : V) {κ : Kind} (h : κ.isRandom = true) (u v : V) :
    rl y (mkC κ u v) = ⟨κ, u, v, [], some (.P, y)⟩ := by
  simp [rl, mkC, h]

theorem rl_sx (x : Atom k n) :
    rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) = mkC (.waved .s) (liftA 1 x) (newA 0) := by
  simp [rl, mkC, Kind.isRandom]

theorem NewH.newEdge {x u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewH u κ a) (hκ : κ.isRandom = true) : NewEdge x u κ (rl (liftA 1 x) a) := by
  rcases h with rfl | rfl <;> rw [rl_mkC_random _ hκ]
  · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem EdgeH.edgeAt {x u : Atom k n} {r : Comp (Atom k n)} (h : EdgeH x u r) :
    EdgeAt x u (rl x r) := by
  have hr : r.kind.isRandom = true := Kind.isRandom_of_isSolid h.1
  refine ⟨by simp [rl, hr, h.1], by simp [rl, hr], ?_⟩
  simp only [rl, hr, ite_true]
  exact h.2

/-- The terms of the shapes `ShapeE`, read inside `P_x`, have the clauses `PStepsTermOK`. -/
theorem termShape {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {cs : List (Comp (Atom k (n + 1)))} (hcs : ShapeE x g.pCore.comps cs) (co : Coeff)
    {g₁ : Graph k (n + 1)}
    (hg₁ : g₁ = ⟨cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩)
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  subst hg₁
  have hN := hS.nn
  have hlab := hN.lab
  have hlr := hN.plain.labRand
  rcases hcs with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB
      ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X)
    simp only [List.map_cons, List.map_nil] at hR
    rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X).map (rl (liftA 1 x)) =
      [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) a₁, rl (liftA 1 x) a₂] ++
        X.map (rl (liftA 1 x)) by simp [rl_sx]] at hL
    refine termBase2 hS hR hr₁.edgeAt hr₂.edgeAt
      ((ha₁.newEdge (Kind.isRandom_of_isSolid hr₁.1)).congr_kind ?_)
      ((ha₂.newEdge (Kind.isRandom_of_isSolid hr₂.1)).congr_kind ?_) (X := X.map (rl (liftA 1 x)))
      ?_ (by simpa using hXl) hL hch
    · simp [rl, Kind.isRandom_of_isSolid hr₁.1]
    · simp [rl, Kind.isRandom_of_isSolid hr₂.1]
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      obtain ⟨ch, rfl⟩ := hX a' ha'
      exact ⟨ch, rl_mkC_random _ rfl _ _⟩
  · have hna : NewEdge x u₁ (rl x r₁).kind (rl (liftA 1 x) a₁) :=
      (ha₁.newEdge (x := x) (Kind.isRandom_of_isSolid hr₁.1)).congr_kind
        (show r₁.kind = (rl x r₁).kind by simp [rl, Kind.isRandom_of_isSolid hr₁.1])
    rcases hcs with rfl | rfl
    · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b]
      simp only [List.map_cons, List.map_nil] at hR
      rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] : List _).map (rl (liftA 1 x)) =
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) a₁, rl (liftA 1 x) b] by
          simp [rl_sx]] at hL
      exact termBase1 hS hR hr₁.edgeAt hna (hb.newEdge rfl) hL hch
    · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁]
      simp only [List.map_cons, List.map_nil] at hR
      rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁] : List _).map (rl (liftA 1 x)) =
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) b, rl (liftA 1 x) a₁] by
          simp [rl_sx]] at hL
      exact termBase1 hS hR hr₁.edgeAt hna (hb.newEdge rfl)
        (hL.trans (List.Perm.append_left _ (List.Perm.cons _ (List.Perm.swap _ _ _)))) hch
  · have hB : g.pCore.comps.Perm ([] ++ g.pCore.comps) := by simp
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]
    rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)] :
        List _).map (rl (liftA 1 x)) = [mkC (.waved .s) (liftA 1 x) (newA 0),
          rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))] by simp [rl_sx]] at hL
    exact termLa hS hR (by simp) (Or.inl (by simp)) hL hch
  · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), e₀])
    simp only [List.map_cons, List.map_nil] at hR
    obtain ⟨ch, hk⟩ := Kind.isSolid_iff.1 hr.1
    have hrr := hr.edgeAt
    have hrm : rl x r ∈ g.comps := hR.symm.subset (by simp)
    obtain ⟨-, hzx⟩ := hrr.facts hS hrm
    have hcr : (rl x c).label = some (.P, x) := by simp [rl, hc]
    refine termD hS hR hrr.2.1 hcr (Or.inr hzx) (ch := ch) (Or.inr ⟨by simp [rl, hk,
      Kind.isRandom], by simpa [rl, Kind.isRandom_of_isSolid hr.1] using hr.2⟩)
      (fun hs hx => absurd hx (by
        have := hcx (by simpa [rl, hc] using hs)
        simp only [rl, hc, ite_true]
        tauto)) hpq (by rw [dPieces_rl]; exact hps) (e₀ := e₀) ?_ ?_ hL hch
    · rcases he with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rcases he with rfl | rfl
      · simp [solidC, mkC, hk, Ne.symm (liftA_ne_newA 1 z 0)]
      · simp [solidC, mkC, hk, liftA_ne_newA 1 z 0]

end ShapeE

section ShapeConj

variable {k n : ℕ}

theorem Kind.conj_isSolid' (κ : Kind) : κ.conj.isSolid = κ.isSolid := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem EdgeH.conj {x u : Atom k n} {r : Comp (Atom k n)} (h : EdgeH x u r) :
    EdgeH x u (conjC r) :=
  ⟨by simp [conjC, Kind.conj_isSolid', h.1], h.2⟩

theorem NewH.conj {u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewH u κ a) : NewH u κ.conj (conjC a) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ShapeE.conj {x : Atom k n} {H : List (Comp (Atom k n))}
    {cs : List (Comp (Atom k (n + 1)))} (h : ShapeE x H cs) :
    ShapeE x (H.map conjC) (cs.map conjC) := by
  rcases h with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · refine Or.inl ⟨conjC r₁, conjC r₂, B.map conjC, u₁, u₂, conjC a₁, conjC a₂, X.map conjC,
      by simpa using hB.map conjC, hr₁.conj, hr₂.conj, ha₁.conj, ha₂.conj, ?_, by simpa using hXl,
      ?_⟩
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      obtain ⟨ch, rfl⟩ := hX a' ha'
      exact ⟨ch.flip, by cases ch <;> rfl⟩
    · simp [liftCs_conj, conjC_mkC, Kind.conj]
  · refine Or.inr (Or.inl ⟨conjC r₁, B.map conjC, u₁, conjC a₁, conjC b, ch.flip,
      by simpa using hB.map conjC, hr₁.conj, ha₁.conj, ?_, ?_⟩)
    · have := hb.conj
      cases ch <;> exact this
    · rcases hcs with rfl | rfl
      · left; simp [liftCs_conj, conjC_mkC, Kind.conj]
      · right; simp [liftCs_conj, conjC_mkC, Kind.conj]
  · refine Or.inr (Or.inr (Or.inl ⟨ch.flip, ?_⟩))
    simp only [List.map_append, liftCs_conj, List.map_cons, List.map_nil, conjC_mkC]
    cases ch <;> rfl
  · refine Or.inr (Or.inr (Or.inr ⟨conjC r, conjC c, B.map conjC, z, q, p, ps.map conjC,
      conjC e₀, by simpa using hB.map conjC, hr.conj, by simpa [conjC, Kind.conj_isRandom'] using hc,
      fun hs => hcx (by simpa [conjC, Kind.conj_isSolid'] using hs), ?_, ?_, he.conj, ?_⟩))
    · rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    · rw [← dPieces_conj, conjC_map, conjC_conjC, hps]
      rfl
    · simp [liftCs_conj, conjC_mkC, Kind.conj]

end ShapeConj

/-! ## [II, (4.24)]: the terms have the shapes `ShapeE` -/

section ShapesOut

variable {k n : ℕ}

theorem edgeIdx_mem {x : Atom k n} {h : Graph k n} {ch : Charge} {out : Bool} {j : ℕ}
    (hj : j ∈ h.edgeIdx x ch out) :
    ∃ hjl : j < h.comps.length, ep x ch out (h.comps[j], j) = true := by
  rw [edgeIdx_eq] at hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨hpz, hpe⟩ := List.mem_filter.1 hp
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hpz)
  refine ⟨hlt, ?_⟩
  have : ((h.comps[p.2]'hlt), p.2) = p := Prod.ext hget rfl
  rw [this]; exact hpe

theorem ep_edgeH {x : Atom k n} {ch : Charge} {out : Bool} {p : Comp (Atom k n) × ℕ}
    (h : ep x ch out p = true) :
    p.1.kind = .G ch ∧ EdgeH x (if out then p.1.y else p.1.x) p.1 := by
  obtain ⟨hk, ho, hi⟩ := ep_spec x h
  refine ⟨hk, by rw [hk]; rfl, ?_⟩
  cases out
  · exact Or.inr ⟨rfl, (hi rfl).1⟩
  · exact Or.inl ⟨(ho rfl).1, rfl⟩

theorem labelQ_mem {V : Type*} (u : V) {L : List (Comp V)} {c : Comp V} (hc : c ∈ L)
    (hr : c.kind.isRandom = true) : ∃ c' ∈ labelQs u L, c'.label = some (.Q, u) :=
  ⟨Comp.labelQ u c, List.mem_map_of_mem hc, by simp [Comp.labelQ, hr]⟩

/-- Every term of `multiEOut` at `x` is a term with the label `Q_x` or of a shape `ShapeE`. -/
theorem shapesOut {x : Atom k n} {h : Graph k n}
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {E : TExpansion k n} (hE : multiEOut x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = t1 cs co ∧ ShapeE x h.comps cs := by
  obtain ⟨i₁, is₂, e₁, hOP, hL, -, rfl⟩ := multiEOut_some x h hE
  have hi₁ : i₁ < h.comps.length := (List.getElem?_eq_some_iff.1 hL).1
  have he₁ : h.comps[i₁] = e₁ := (List.getElem?_eq_some_iff.1 hL).2
  have hep₁ : ep x .plus true (e₁, i₁) = true := e₁_ep hOP hL
  obtain ⟨hk₁, hE₁⟩ := ep_edgeH hep₁
  simp only [ite_true] at hE₁
  have hr₁ : e₁.kind.isRandom = true := by rw [hk₁]; rfl
  have he₁m : e₁ ∈ h.comps := List.mem_of_getElem? hL
  have hsx : oSx x = mkC (.waved .s) (liftA 1 x) (newA 0) := rfl
  have hgy : oGy e₁ = mkC e₁.kind (newA 0) (liftA 1 e₁.y) := by rw [hk₁]; rfl
  -- the main terms
  have gM : ∀ (j : ℕ) (ch : Charge) (out : Bool), j ∈ h.edgeIdx x ch out →
      (ch, out) ≠ (.plus, true) → ∀ X : List (Comp (Atom k (n + 1))),
        (∀ a ∈ X, ∃ ch, a = mkC (.light ch) (liftA 1 x) (liftA 1 x)) → X.length ≤ 1 →
      ShapeE x h.comps (liftCs 1 (eraseIdxs [i₁, j] h.comps) ++ [oSx x, oGy e₁,
        if out then mkC (.G ch) (newA 0) (liftA 1 (h.comps.getD j e₁).y)
        else mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0)] ++ X) := by
    intro j ch out hj hne X hX hXl
    obtain ⟨hjl, hepj⟩ := edgeIdx_mem hj
    have hij : i₁ ≠ j := by
      rintro rfl
      rw [he₁] at hepj
      obtain ⟨h1, h2⟩ := ep_excl x hep₁ hepj
      exact hne (by rw [← h1, ← h2])
    have hgd : h.comps.getD j e₁ = h.comps[j] := by simp [hjl]
    obtain ⟨hkj, hEj⟩ := ep_edgeH hepj
    refine Or.inl ⟨e₁, h.comps[j], eraseIdxs [i₁, j] h.comps, e₁.y, _, oGy e₁,
      if out then mkC (.G ch) (newA 0) (liftA 1 (h.comps.getD j e₁).y)
        else mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0), X, ?_, hE₁,
      hEj, Or.inl hgy, ?_, hX, hXl, by simp [hsx]⟩
    · have := (perm_pick_erase [i₁, j] h.comps).trans
        ((pickIdxs_two hi₁ hjl hij).append_right _)
      rwa [he₁] at this
    · rw [hgd, hkj]
      cases out
      · exact Or.inr rfl
      · exact Or.inl rfl
  have gE : ∀ (b : Comp (Atom k (n + 1))) (ch : Charge), NewH x (.G ch) b →
      ShapeE x h.comps (liftCs 1 (h.comps.eraseIdx i₁) ++ [oSx x, b, oGy e₁]) := by
    intro b ch hb
    refine Or.inr (Or.inl ⟨e₁, h.comps.eraseIdx i₁, e₁.y, oGy e₁, b, ch, ?_, hE₁, Or.inl hgy, hb,
      Or.inr rfl⟩)
    have := (List.getElem_cons_eraseIdx_perm hi₁).symm
    rwa [he₁] at this
  have gD : ∀ d ∈ oDs x h i₁ e₁, ShapeE x h.comps d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd'
    set fL := eraseIdxs (psteps_oXIdx x h) h.comps with hfL
    have hj' : j < fL.length := by simpa [liftCs] using hj
    have hc : (liftCs 1 fL)[j] = fL[j].map (liftA 1) := by simp [liftCs]
    rw [hc] at hps
    have hcr : fL[j].kind.isRandom = true := by
      have := dPieces_random hps; simpa [Comp.map] using this
    refine Or.inr (Or.inr (Or.inr ⟨e₁, fL[j], pickIdxs ((psteps_oXIdx x h).filter (· != i₁)) h.comps ++
      fL.eraseIdx j, e₁.y, newA 0, liftA 1 x, ps, oGy e₁, ?_, hE₁, hcr, ?_,
      Or.inl ⟨rfl, rfl⟩, hps, Or.inl hgy, ?_⟩))
    · have h1 := perm_pick_erase (psteps_oXIdx x h) h.comps
      have hmem : i₁ ∈ psteps_oXIdx x h := by simp [psteps_oXIdx, hOP]
      have h2 := pick_cons_filter (l := h.comps) hi₁ hmem
      rw [he₁] at h2
      have h3 := List.getElem_cons_eraseIdx_perm hj'
      refine h1.trans ((h2.append h3.symm).trans ?_)
      simp only [List.cons_append, List.singleton_append]
      exact List.Perm.cons _ List.perm_middle
    · intro hs
      have hcm : fL[j] ∈ fL := List.getElem_mem hj'
      obtain ⟨p, hp, hpc⟩ := List.mem_map.1 hcm
      obtain ⟨hpz, hpn⟩ := List.mem_filter.1 hp
      rw [contains_oXIdx x h hpz] at hpn
      have hcX : cX x p = false := by simpa using hpn
      obtain ⟨ch, hk⟩ := Kind.isSolid_iff.1 hs
      have hne := hNL _ (fst_mem_of_zip hpz) (by rw [hpc]; exact hs)
      rw [hpc] at hne
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · have hy' : fL[j].y ≠ x := fun h' => hne (hx.trans h'.symm)
        have : ep x ch true p = true := by
          simp [ep, hpc, hk, hx, hy']
        rw [cX_of_ep x this] at hcX; cases hcX
      · have hx' : fL[j].x ≠ x := fun h' => hne (h'.trans hy.symm)
        have : ep x ch false p = true := by
          simp [ep, hpc, hk, hy, hx']
        rw [cX_of_ep x this] at hcX; cases hcX
    · simp only [oDs, liftCs, List.map_append, List.eraseIdx_map, List.append_assoc, hsx]
  intro s hs
  unfold psteps_oOut at hs
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact labelQ_mem (liftA 1 x) (c := oGy e₁) (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      exact labelQ_mem (liftA 1 x) (c := oGy e₁) (by simp [oE2]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      exact labelQ_mem (liftA 1 x) (c := oGy e₁) (by simp [oE1]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem (liftA 1 x) (c := mkC (.light .plus) (newA 0) (newA 0)) (by simp [oL3]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact labelQ_mem (liftA 1 x) (c := oGy e₁) (by simp [oBaseP]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact labelQ_mem (liftA 1 x) (c := oGy e₁) (by simp [oBaseM]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem _ he₁m hr₁
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    exact ⟨d, _, rfl, gD d hd⟩
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      refine ⟨_, _, rfl, ?_⟩
      have := gE (mkC (.G .minus) (newA 0) (liftA 1 x)) .minus (Or.inl rfl)
      simpa [oE2, oSx] using this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      refine ⟨_, _, rfl, ?_⟩
      have := gE (mkC (.G .plus) (liftA 1 x) (newA 0)) .plus (Or.inr rfl)
      simpa [oE1, oSx] using this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    rw [List.mem_singleton] at hs; subst hs
    exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨.plus, rfl⟩))⟩
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .plus false hj (by simp)
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)] (fun a ha => ⟨.plus, by simpa using ha⟩)
      (by simp)
    simpa [oBaseP] using this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus true hj (by simp)
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)] (fun a ha => ⟨.minus, by simpa using ha⟩)
      (by simp)
    simpa [oBaseM] using this
  rcases List.mem_append.1 hs with hs | hs
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus true hj (by simp) [] (by simp) (by simp)
    simpa [oBaseM] using this
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .plus false hj (by simp) [] (by simp) (by simp)
    simpa [oBaseP] using this

end ShapesOut

section ShapesIn

variable {k n : ℕ}

/-- Every term of `multiEIn` at `x`, when no solid edge leaves `x`, is a term with the label `Q_x`
or of a shape `ShapeE`. -/
theorem shapesIn {x : Atom k n} {h : Graph k n}
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hout : ∀ ch, h.edgeIdx x ch true = [])
    {E : TExpansion k n} (hE : multiEIn x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = t1 cs co ∧ ShapeE x h.comps cs := by
  obtain ⟨i₁, is₂, e₁, hIP, hL, -, rfl⟩ := multiEIn_some x h hE
  have hi₁ : i₁ < h.comps.length := (List.getElem?_eq_some_iff.1 hL).1
  have he₁ : h.comps[i₁] = e₁ := (List.getElem?_eq_some_iff.1 hL).2
  have hep₁ : ep x .plus false (e₁, i₁) = true := in_e₁_ep hIP hL
  obtain ⟨hk₁, hE₁⟩ := ep_edgeH hep₁
  simp only [Bool.false_eq_true, ite_false] at hE₁
  have hr₁ : e₁.kind.isRandom = true := by rw [hk₁]; rfl
  have he₁m : e₁ ∈ h.comps := List.mem_of_getElem? hL
  have hsx : oSx x = mkC (.waved .s) (liftA 1 x) (newA 0) := rfl
  have hgw : iGw e₁ = mkC e₁.kind (liftA 1 e₁.x) (newA 0) := by rw [hk₁]; rfl
  have gM : ∀ (j : ℕ) (ch : Charge), j ∈ h.edgeIdx x ch false → ch ≠ .plus →
      ∀ X : List (Comp (Atom k (n + 1))),
        (∀ a ∈ X, ∃ ch, a = mkC (.light ch) (liftA 1 x) (liftA 1 x)) → X.length ≤ 1 →
      ShapeE x h.comps (liftCs 1 (eraseIdxs [i₁, j] h.comps) ++ [oSx x, iGw e₁,
        mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0)] ++ X) := by
    intro j ch hj hne X hX hXl
    obtain ⟨hjl, hepj⟩ := edgeIdx_mem hj
    have hij : i₁ ≠ j := by
      rintro rfl
      rw [he₁] at hepj
      obtain ⟨h1, -⟩ := ep_excl x hep₁ hepj
      exact hne h1.symm
    have hgd : h.comps.getD j e₁ = h.comps[j] := by simp [hjl]
    obtain ⟨hkj, hEj⟩ := ep_edgeH hepj
    refine Or.inl ⟨e₁, h.comps[j], eraseIdxs [i₁, j] h.comps, e₁.x, _, iGw e₁,
      mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0), X, ?_, hE₁,
      hEj, Or.inr hgw, ?_, hX, hXl, by simp [hsx]⟩
    · have := (perm_pick_erase [i₁, j] h.comps).trans
        ((pickIdxs_two hi₁ hjl hij).append_right _)
      rwa [he₁] at this
    · rw [hgd, hkj]
      exact Or.inr rfl
  have gD : ∀ d ∈ iDs x h i₁ e₁, ShapeE x h.comps d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd'
    set fL := eraseIdxs (psteps_iXIdx x h) h.comps with hfL
    have hj' : j < fL.length := by simpa [liftCs] using hj
    have hc : (liftCs 1 fL)[j] = fL[j].map (liftA 1) := by simp [liftCs]
    rw [hc] at hps
    have hcr : fL[j].kind.isRandom = true := by
      have := dPieces_random hps; simpa [Comp.map] using this
    refine Or.inr (Or.inr (Or.inr ⟨e₁, fL[j], pickIdxs ((psteps_iXIdx x h).filter (· != i₁)) h.comps ++
      fL.eraseIdx j, e₁.x, liftA 1 x, newA 0, ps, iGw e₁, ?_, hE₁, hcr, ?_,
      Or.inr ⟨rfl, rfl⟩, hps, Or.inr hgw, ?_⟩))
    · have h1 := perm_pick_erase (psteps_iXIdx x h) h.comps
      have hmem : i₁ ∈ psteps_iXIdx x h := by simp [psteps_iXIdx, hIP]
      have h2 := pick_cons_filter (l := h.comps) hi₁ hmem
      rw [he₁] at h2
      have h3 := List.getElem_cons_eraseIdx_perm hj'
      refine h1.trans ((h2.append h3.symm).trans ?_)
      simp only [List.cons_append, List.singleton_append]
      exact List.Perm.cons _ List.perm_middle
    · intro hs
      have hcm : fL[j] ∈ fL := List.getElem_mem hj'
      obtain ⟨p, hp, hpc⟩ := List.mem_map.1 hcm
      obtain ⟨hpz, hpn⟩ := List.mem_filter.1 hp
      rw [contains_iXIdx x h hpz] at hpn
      have hcI : cI x p = false := by simpa using hpn
      obtain ⟨ch, hk⟩ := Kind.isSolid_iff.1 hs
      have hne := hNL _ (fst_mem_of_zip hpz) (by rw [hpc]; exact hs)
      rw [hpc] at hne
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · have hy' : fL[j].y ≠ x := fun h' => hne (hx.trans h'.symm)
        have : ep x ch true p = true := by
          simp [ep, hpc, hk, hx, hy']
        have hmem' : p.2 ∈ h.edgeIdx x ch true := by
          rw [edgeIdx_eq]; exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hpz, this⟩, rfl⟩
        rw [hout ch] at hmem'; simp at hmem'
      · have hx' : fL[j].x ≠ x := fun h' => hne (h'.trans hy.symm)
        have : ep x ch false p = true := by
          simp [ep, hpc, hk, hy, hx']
        have : cI x p = true := by
          cases ch <;> simp [cI, this]
        rw [this] at hcI; cases hcI
    · simp only [iDs, liftCs, List.map_append, List.eraseIdx_map, List.append_assoc, hsx]
  intro s hs
  unfold psteps_iOut at hs
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact labelQ_mem (liftA 1 x) (c := iGw e₁) (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      exact labelQ_mem (liftA 1 x) (c := iGw e₁) (by simp [iE1]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem (liftA 1 x) (c := mkC (.light .plus) (newA 0) (newA 0)) (by simp [oL3]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact labelQ_mem (liftA 1 x) (c := iGw e₁) (by simp [iBaseM]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem _ he₁m hr₁
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    exact ⟨d, _, rfl, gD d hd⟩
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      refine ⟨_, _, rfl, Or.inr (Or.inl ⟨e₁, h.comps.eraseIdx i₁, e₁.x, iGw e₁,
        mkC (.G .plus) (newA 0) (liftA 1 x), .plus, ?_, hE₁, Or.inr hgw, Or.inl rfl,
        Or.inl rfl⟩)⟩
      have := (List.getElem_cons_eraseIdx_perm hi₁).symm
      rwa [he₁] at this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    rw [List.mem_singleton] at hs; subst hs
    exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨.plus, rfl⟩))⟩
  rcases List.mem_append.1 hs with hs | hs
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus hj (by simp) [] (by simp) (by simp)
    simpa [iBaseM] using this
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus hj (by simp)
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)] (fun a ha => ⟨.minus, by simpa using ha⟩)
      (by simp)
    simpa [iBaseM] using this

end ShapesIn

/-! ## [II, (4.24)] inside `P_x`: the clauses on the terms -/

section TermsE

variable {k n : ℕ}

theorem Kind.conj_eq_G (κ : Kind) (ch : Charge) : κ.conj = .G ch ↔ κ = .G ch.flip := by
  cases κ with
  | G c => cases c <;> cases ch <;> simp [Kind.conj, Charge.flip]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem psteps_edgeIdx_conj (g : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    g.conj.edgeIdx x ch out = g.edgeIdx x ch.flip out := by
  unfold Graph.edgeIdx
  rw [Graph.conj_comps', List.zipIdx_map, List.filter_map, List.map_map]
  have : (Prod.snd ∘ Prod.map conjC id : Comp (Atom k n) × ℕ → ℕ) = Prod.snd := rfl
  rw [this]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp_apply, Prod.map_fst, conjC]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Kind.conj_eq_G]

theorem noLoop_core {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g) :
    ∀ c ∈ g.pCore.comps, c.kind.isSolid = true → c.x ≠ c.y := by
  intro c hc hs
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  exact hS.nn.noLoop d hd hs

/-- Every term of `Ô^{(x)}_multi-e` on `𝒢` is a term with the label `Q_x` or of a shape
`ShapeE`. -/
theorem shapes_multiEHat {x : Atom k n} {h : Graph k n}
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {E : TExpansion k n} (hE : multiEHat x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = t1 cs co ∧ ShapeE x h.comps cs := by
  have hNL' : ∀ c ∈ h.conj.comps, c.kind.isSolid = true → c.x ≠ c.y := by
    intro c hc hs
    rw [Graph.conj_comps'] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact hNL d hd (by simpa [conjC, Kind.conj_isSolid'] using hs)
  have hconj : ∀ E' : TExpansion k n, (∀ s ∈ E', (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = t1 cs co ∧ ShapeE x h.conj.comps cs) →
      ∀ s ∈ E'.conj, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
        ∃ cs co, s = t1 cs co ∧ ShapeE x h.comps cs := by
    intro E' hE' s hs
    obtain ⟨s', hs', rfl⟩ := mem_TExpansion_conj.1 hs
    rcases hE' s' hs' with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, hsh⟩
    · left
      exact ⟨conjC c, by rw [Graph.conj_comps']; exact List.mem_map_of_mem hc, hl⟩
    · right
      refine ⟨cs.map conjC, Coeff.conj co, rfl, ?_⟩
      have := hsh.conj
      rwa [Graph.conj_comps', map_conjC_conjC] at this
  unfold multiEHat at hE
  split_ifs at hE with h1 h2 h3 h4
  · exact shapesOut hNL hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    exact hconj E' (shapesOut hNL' hE')
  · refine shapesIn hNL (fun ch => ?_) hE
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2
    cases ch
    · exact h1
    · exact h2
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    refine hconj E' (shapesIn hNL' (fun ch => ?_) hE')
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2
    rw [psteps_edgeIdx_conj]
    cases ch
    · exact h2
    · exact h1

/-- The terms of [II, (4.24)] inside `P_x` have the clauses `PStepsTermOK`. -/
theorem termsE {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hP : g.IsPFormAt x) {E : TExpansion k n} (hE : multiEHat x g.pCore = some E) :
    ∀ t ∈ pLiftT x g E, PStepsTermOK (C + 5) x g t := by
  intro t ht
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨t.nOut, t.g⟩ :=
    .single (QElemStep.pMultiE x g E t hP hS.nn.plain hE ht)
  obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
  rcases shapes_multiEHat (noLoop_core hS) hE s hs with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, hsh⟩
  · exfalso
    have := List.any_eq_false.1 hq c hc
    simp [hl] at this
  · exact termShape hS hsh co rfl hch

end TermsE

/-! ## The value of [II, (4.24)] inside `P_x`: the families of terms -/

section PBlocks

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

/-- `P_x` of a factor times a light weight at `x`, split as the weight minus `m`. -/
theorem P_light_split (ω : Ω) (X : ι) {R : Ω → ℂ} (hR : A.Test R) (ch : Charge) :
    PF.P X (fun ω' => R ω' * ch.apply (A.G ω' X X - msc A.z)) ω =
      PF.P X (fun ω' => R ω' * ch.apply (A.G ω' X X)) ω - ch.apply (msc A.z) * PF.P X R ω := by
  have hG : A.Test fun ω' => R ω' * ch.apply (A.G ω' X X) := by
    cases ch
    · exact test_mul' A hR (test_G A _ _)
    · exact test_mul' A hR (test_star' A (test_G A _ _))
  rw [P_congr' (f := fun ω' => R ω' * ch.apply (A.G ω' X X - msc A.z))
    (g := fun ω' => R ω' * ch.apply (A.G ω' X X) - ch.apply (msc A.z) * R ω')
    (fun ω' => by cases ch <;> simp [Charge.apply] <;> ring),
    P_sub' A (good_of_test A hG) (good_of_test A (test_mul' A (test_const' A _) hR)),
    P_cmul' A _ (good_of_test A hR)]

theorem core_plainB {g : Graph k n} (hp : g.Plain) :
    ∀ c ∈ g.pCore.comps, c.isPlainB = true := by
  intro c hc
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  obtain ⟨h1, h2, h3, -⟩ := hp d hd
  unfold Comp.isPlainB
  simp only [h1, List.isEmpty_nil, Option.isNone_none, Bool.true_and]

variable (x : Atom k n) (g : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

theorem PBM (hp : g.Plain) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨(oBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++
        g.pEnv.map (Comp.map (liftA 1)), cm * cmb * g.pCore.coeff⟩ s +
      T1 PF D e ω ⟨(oBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
        (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
          star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have hUM : Unl (oBaseM x g.pCore i₁ e₁ j) := by
    unfold oBaseM oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUM' : Unl (oBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hUM, T1_plift A x g _ _ hUM', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hRt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
      (A.G ω' α (Sum.elim e s e₁.y) *
        star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) :=
    test_mul' A (rv_test A _ _ fun c hc => (basB_of_plain (hpl c (mem_eraseIdxs hc))).1)
      (test_mul' A (test_G A _ _) (test_star' A (test_G A _ _)))
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oBaseM x g.pCore i₁ e₁ j) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) *
          star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) := by
    intro ω'
    simp only [oBaseM, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hrv' : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      (rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) *
          star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y)))) *
        Charge.minus.apply (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) := by
    intro ω'
    rw [rv_append, hrv]
    simp [Kind.isRandom, val_light A]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseM x g.pCore i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oBaseM, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hdv' : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseM x g.pCore i₁ e₁ j) := by
    simp [Kind.isRandom]
  rw [hdv', hdv, P_congr' hrv, P_congr' hrv', P_light_split A ω _ hRt .minus]
  simp only [ceval_mul, ceval_cm, ceval_cmb, Charge.apply]
  ring

theorem PBP (hp : g.Plain) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨(oBaseP x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++
        g.pEnv.map (Comp.map (liftA 1)), cm * cm * g.pCore.coeff⟩ s +
      T1 PF D e ω ⟨(oBaseP x g.pCore i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
        (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
          A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) *
        A.G ω' (Sum.elim e s x) (Sum.elim e s x)) ω := by
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have hUM : Unl (oBaseP x g.pCore i₁ e₁ j) := by
    unfold oBaseP oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUM' : Unl (oBaseP x g.pCore i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hUM, T1_plift A x g _ _ hUM', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hRt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
      (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) :=
    test_mul' A (rv_test A _ _ fun c hc => (basB_of_plain (hpl c (mem_eraseIdxs hc))).1)
      (test_mul' A (test_G A _ _) (test_G A _ _))
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oBaseP x g.pCore i₁ e₁ j) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) := by
    intro ω'
    simp only [oBaseP, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hrv' : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) =
      (rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) *
        Charge.plus.apply (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) := by
    intro ω'
    rw [rv_append, hrv]
    simp [Kind.isRandom, val_light A]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseP x g.pCore i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oBaseP, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hdv' : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) =
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseP x g.pCore i₁ e₁ j) := by
    simp [Kind.isRandom]
  rw [hdv', hdv, P_congr' hrv, P_congr' hrv', P_light_split A ω _ hRt .plus]
  simp only [ceval_mul, ceval_cm, Charge.apply]
  ring

end PBlocks

section PBlocks2

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}
  (x : Atom k n) (g : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

theorem PBL (hp : g.Plain) (s : Fin n → ι) :
    T1 PF D e ω ⟨(oL3 x g.pCore).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
      cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) g.pCore.comps *
        (A.G ω' α α - msc A.z)) ω := by
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (oL3 x g.pCore) := by
    unfold oL3 oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oL3 x g.pCore) =
      rv (D ω') (Sum.elim e s) g.pCore.comps * (A.G ω' α α - msc A.z) := by
    intro ω'
    simp only [oL3, oSx, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_light A,
      elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oL3 x g.pCore) =
      dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oL3, oSx, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_cm]

theorem PBE1 (hp : g.Plain) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨(oE1 x g.pCore i₁ e₁).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), (a : Coeff) * cm * g.pCore.coeff⟩ s) =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (a : ℂ) * msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s x) α * A.G ω' α (Sum.elim e s e₁.y))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  rw [if_neg hb']
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (oE1 x g.pCore i₁ e₁) := by
    unfold oE1 oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oE1 x g.pCore i₁ e₁) =
      rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s x) α * A.G ω' α (Sum.elim e s e₁.y)) := by
    intro ω'
    simp only [oE1, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oE1 x g.pCore i₁ e₁) =
      dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oE1, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

theorem PBE2 (hp : g.Plain) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨(oE2 x g.pCore i₁ e₁).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), (a : Coeff) * cm * g.pCore.coeff⟩ s) =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (a : ℂ) * msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (star (A.G ω' α (Sum.elim e s x)) * A.G ω' α (Sum.elim e s e₁.y))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  rw [if_neg hb']
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (oE2 x g.pCore i₁ e₁) := by
    unfold oE2 oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oE2 x g.pCore i₁ e₁) =
      rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (star (A.G ω' α (Sum.elim e s x)) * A.G ω' α (Sum.elim e s e₁.y)) := by
    intro ω'
    simp only [oE2, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oE2 x g.pCore i₁ e₁) =
      dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oE2, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

theorem PBD (L : List (List (Comp (Atom k (n + 1))))) (hL : ∀ d ∈ L, Unl d)
    (s : Fin n → ι) :
    (L.map fun d => T1 PF D e ω ⟨d.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
      cm * g.pCore.coeff⟩ s).sum =
    pv (D ω) (Sum.elim e s) g.pEnv * (L.map fun d => ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      dv (D ω) (Sum.elim e (Fin.append s ![α])) d *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) d) ω).sum := by
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  rw [T1_plift A x g _ _ (hL d hd), ceval_mul, ceval_cm]

end PBlocks2

/-! ## The value of [II, (4.24)] inside `P_x`, case (i) -/

section ValueEOut

variable {k n : ℕ}

theorem pLiftT_ite (x : Atom k n) (g : Graph k n) (b : Prop) [Decidable b]
    (E : TExpansion k n) : pLiftT x g (if b then [] else E) = if b then [] else pLiftT x g E := by
  split_ifs <;> rfl

theorem pLiftT_map_Q (x : Atom k n) (g : Graph k n) {β : Type*} (l : List β)
    (G : β → List (Comp (Atom k (n + 1)))) (d : β → Coeff)
    (hG : ∀ j ∈ l, ∃ c ∈ G j, c.kind.isRandom = true) :
    pLiftT x g (l.map fun j => t1 (labelQs (liftA 1 x) (G j)) (d j)) = [] := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons]
    have hq : ((t1 (labelQs (liftA 1 x) (G j)) (d j)).g.comps.any fun c =>
        decide (c.label = some (.Q, (t1 (labelQs (liftA 1 x) (G j)) (d j)).f x))) = true := by
      obtain ⟨c, hc, hr⟩ := hG j (List.mem_cons_self ..)
      simp only [t1, List.any_eq_true, decide_eq_true_eq]
      exact ⟨Comp.labelQ (liftA 1 x) c, List.mem_map_of_mem hc, by simp [Comp.labelQ, hr]⟩
    have ih' := ih fun j' hj' => hG j' (List.mem_cons_of_mem _ hj')
    unfold pLiftT at ih' ⊢
    rw [List.filterMap_cons, if_pos hq, ih']

theorem pLiftT_t0Q (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k n)))
    (co : Coeff) (h : ∃ c ∈ cs, c.kind.isRandom = true) :
    pLiftT x g [⟨n, ⟨labelQs x cs, co⟩, id⟩] = [] := by
  have hq : ((⟨n, ⟨labelQs x cs, co⟩, id⟩ : Tracked k n).g.comps.any fun c =>
      decide (c.label = some (.Q, (⟨n, ⟨labelQs x cs, co⟩, id⟩ : Tracked k n).f x))) = true := by
    obtain ⟨c, hc, hr⟩ := h
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ⟨Comp.labelQ x c, List.mem_map_of_mem hc, by simp [Comp.labelQ, hr]⟩
  unfold pLiftT
  rw [List.filterMap_cons, if_pos hq]
  rfl

theorem pLiftT_single_Q (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (h : ∃ c ∈ cs, c.kind.isRandom = true) :
    pLiftT x g [t1 (labelQs (liftA 1 x) cs) d] = [] :=
  pLiftT_map_Q x g [()] (fun _ => cs) (fun _ => d) (fun _ _ => h)

theorem pLiftT_single_t1 (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (hcs : Unl cs) :
    pLiftT x g [t1 cs d] = [t1 (cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))) d] := by
  rw [pLiftT_cons_t1 x g _ _ hcs, pLiftT_nil]

/-- The value of the multi-edge expansion [II, (4.24)] (case (i)) inside `P_x`. -/
theorem valueEOut_plain {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    {E : TExpansion k n} (hE : multiEOut x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  obtain ⟨i₁, is₂, e₁, hOP, hL, hX, hEq⟩ := multiEOut_some x g.pCore hE
  rw [hEq]
  clear hE hEq
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have he₁m : e₁ ∈ g.pCore.comps := List.mem_of_getElem? hL
  have hr₁ : e₁.kind.isRandom = true := by rw [(ep_spec x (e₁_ep hOP hL)).1]; rfl
  have hUM : ∀ j, Unl (oBaseM x g.pCore i₁ e₁ j) := fun j => by
    unfold oBaseM oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUP : ∀ j, Unl (oBaseP x g.pCore i₁ e₁ j) := fun j => by
    unfold oBaseP oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hU3 : Unl (oL3 x g.pCore) := by
    unfold oL3 oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  have hUE1 : Unl (oE1 x g.pCore i₁ e₁) := by
    unfold oE1 oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  have hUE2 : Unl (oE2 x g.pCore i₁ e₁) := by
    unfold oE2 oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  have hFb : ∀ c ∈ eraseIdxs (psteps_oXIdx x g.pCore) g.pCore.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hUD : ∀ d ∈ oDs x g.pCore i₁ e₁, Unl d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    refine Unl_append.2 ⟨Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_pickIdxs hc),
      dTerms_unl (fun c hc => (plain_bas_lift hFb 1 c hc).2) d' hd'⟩, by simp [Unl, oSx, oGy, mkC]⟩
  have hgy : ∃ c ∈ [oSx x, oGy e₁], c.kind.isRandom = true := ⟨oGy e₁, by simp, rfl⟩
  -- the terms with a label `Q_x` are dropped
  change S PF D e ω (pLiftT x g (psteps_oOut x g.pCore i₁ is₂ e₁)) = g.valR PF D e ω
  unfold psteps_oOut
  simp only [pLiftT_append, pLiftT_ite]
  rw [pLiftT_t0Q x g _ _ ⟨e₁, he₁m, hr₁⟩,
    pLiftT_map_Q x g _ (fun d => d) _ (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.1 hd
      exact ⟨oGy e₁, by simp, rfl⟩),
    pLiftT_map_Q x g _ (fun j => oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]) _ (fun j _ => ⟨oGy e₁, by simp [oBaseM], rfl⟩),
    pLiftT_map_Q x g _ (fun j => oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) _ (fun j _ => ⟨oGy e₁, by simp [oBaseP], rfl⟩),
    pLiftT_single_Q x g _ _ ⟨mkC (.light .plus) (newA 0) (newA 0), by simp [oL3], rfl⟩,
    pLiftT_single_Q x g _ _ ⟨oGy e₁, by simp [oE1], rfl⟩,
    pLiftT_single_Q x g _ _ ⟨oGy e₁, by simp [oE2], rfl⟩,
    pLiftT_single_t1 x g _ _ hU3, pLiftT_single_t1 x g _ _ hUE1, pLiftT_single_t1 x g _ _ hUE2,
    pLiftT_map_t1 x g _ (fun j => oBaseM x g.pCore i₁ e₁ j) _ (fun j _ => hUM j),
    pLiftT_map_t1 x g _ (fun j => oBaseP x g.pCore i₁ e₁ j) _ (fun j _ => hUP j),
    pLiftT_map_t1 x g _ (fun j => oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) _
      (fun j _ => Unl_append.2 ⟨hUM j, by simp [Unl, mkC]⟩),
    pLiftT_map_t1 x g _ (fun j => oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) _
      (fun j _ => Unl_append.2 ⟨hUP j, by simp [Unl, mkC]⟩),
    pLiftT_map_t1 x g _ (fun d => d) _ hUD]
  simp only [ite_self, List.append_nil, S_append, S_map_t1, S_t1, S_ite, ite_sum]
  rw [valR_T0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdj : ∀ (ch : Charge) (out : Bool), ∀ j ∈ g.pCore.edgeIdx x ch out,
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) =
        dv (D ω) (Sum.elim e s) g.pCore.comps := by
    intro ch out j hj
    rw [edgeIdx_eq] at hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
    exact out_D3 _ hOP hL (D ω) (List.mem_filter.1 hq).1 (cX_of_ep x (List.mem_filter.1 hq).2)
  have hdE := out_D1 (Sum.elim e s) hOP hL (D ω)
  have hdD : ∀ d ∈ oDs x g.pCore i₁ e₁, ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) d =
      dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    intro d hd α
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (newA 0) (liftA 1 x) _
      (plain_bas_lift hFb 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, out_D4] at h2
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, out_D5, h2, oSx, oGy, dv_cons,
      dv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hM : ((g.pCore.edgeIdx x .minus true).map fun j => T1 PF D e ω
      ⟨(oBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
        cm * cmb * g.pCore.coeff⟩ s).sum +
      ((g.pCore.edgeIdx x .minus true).map fun j => T1 PF D e ω
      ⟨(oBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s).sum =
      pv (D ω) (Sum.elim e s) g.pEnv * ((g.pCore.edgeIdx x .minus true).map fun j => ∑ α,
        msc A.z * g.pCore.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
          (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
            star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) *
          star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [PBM A x g i₁ e₁ e ω hp j s, hdj .minus true j hj]
  have hP : ((g.pCore.edgeIdx x .plus false).map fun j => T1 PF D e ω
      ⟨(oBaseP x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
        cm * cm * g.pCore.coeff⟩ s).sum +
      ((g.pCore.edgeIdx x .plus false).map fun j => T1 PF D e ω
      ⟨(oBaseP x g.pCore i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s).sum =
      pv (D ω) (Sum.elim e s) g.pEnv * ((g.pCore.edgeIdx x .plus false).map fun j => ∑ α,
        msc A.z * g.pCore.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
          (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
            A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) *
          A.G ω' (Sum.elim e s x) (Sum.elim e s x)) ω).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [PBP A x g i₁ e₁ e ω hp j s, hdj .plus false j hj]
  have hL3 := PBL A x g e ω hp s
  have hE1 := PBE1 A x g i₁ e₁ e ω hp (is₂.isEmpty = true) is₂.length
    (fun h => by simpa using h) s
  have hE2 := PBE2 A x g i₁ e₁ e ω hp ((g.pCore.edgeIdx x .minus false).length = 0)
    (g.pCore.edgeIdx x .minus false).length id s
  rw [hdE] at hE1 hE2
  have hD := (PBD A x g e ω _ hUD s).trans (congrArg _ (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => by rw [hdD d hd α])))
  have hT0 : T0 PF D e ω g s = g.pCore.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) g.pCore.comps *
      pv (D ω) (Sum.elim e s) g.pEnv *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) g.pCore.comps) ω := by
    rw [T0, termR_pform A hlab hp.labRand, m_eq A]
    rfl
  have hcore := out_core A hpl hOP hL hX (Sum.elim e s) (fun α => Sum.elim e (Fin.append s ![α]))
    (fun α => elim_append_comp_liftA e s ![α]) (fun α => by simp) ω
  rw [Q_apply'] at hcore
  linear_combination hM + hP + hL3 + hE1 + hE2 + hD - hT0 -
    pv (D ω) (Sum.elim e s) g.pEnv * hcore

end ValueEOut

section PBlocksIn

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}
  (x : Atom k n) (g : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

theorem PBMi (hp : g.Plain) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨(iBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++
        g.pEnv.map (Comp.map (liftA 1)), cm * cmb * g.pCore.coeff⟩ s +
      T1 PF D e ω ⟨(iBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
        (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' (Sum.elim e s e₁.x) α *
          star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have hUM : Unl (iBaseM x g.pCore i₁ e₁ j) := by
    unfold iBaseM oSx iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUM' : Unl (iBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hUM, T1_plift A x g _ _ hUM', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hRt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
      (A.G ω' (Sum.elim e s e₁.x) α *
        star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) :=
    test_mul' A (rv_test A _ _ fun c hc => (basB_of_plain (hpl c (mem_eraseIdxs hc))).1)
      (test_mul' A (test_G A _ _) (test_star' A (test_G A _ _)))
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (iBaseM x g.pCore i₁ e₁ j) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' (Sum.elim e s e₁.x) α *
          star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) := by
    intro ω'
    simp only [iBaseM, oSx, iGw, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hrv' : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      (rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' (Sum.elim e s e₁.x) α *
          star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α))) *
        Charge.minus.apply (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) := by
    intro ω'
    rw [rv_append, hrv]
    simp [Kind.isRandom, val_light A]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (iBaseM x g.pCore i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [iBaseM, oSx, iGw, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hdv' : dv (D ω) (Sum.elim e (Fin.append s ![α])) (iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (iBaseM x g.pCore i₁ e₁ j) := by
    simp [Kind.isRandom]
  rw [hdv', hdv, P_congr' hrv, P_congr' hrv', P_light_split A ω _ hRt .minus]
  simp only [ceval_mul, ceval_cm, ceval_cmb, Charge.apply]
  ring

theorem PBE1i (hp : g.Plain) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨(iE1 x g.pCore i₁ e₁).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), (a : Coeff) * cm * g.pCore.coeff⟩ s) =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (a : ℂ) * msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s e₁.x) α * A.G ω' α (Sum.elim e s x))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  rw [if_neg hb']
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (iE1 x g.pCore i₁ e₁) := by
    unfold iE1 oSx iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (iE1 x g.pCore i₁ e₁) =
      rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s e₁.x) α * A.G ω' α (Sum.elim e s x)) := by
    intro ω'
    simp only [iE1, oSx, iGw, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (iE1 x g.pCore i₁ e₁) =
      dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [iE1, oSx, iGw, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

end PBlocksIn

section ValueEIn

variable {k n : ℕ}

/-- The value of the multi-edge expansion [II, (4.24)] (case (iii)) inside `P_x`. -/
theorem valueEIn_plain {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    {E : TExpansion k n} (hE : multiEIn x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  obtain ⟨i₁, is₂, e₁, hIP, hL, hX, hEq⟩ := multiEIn_some x g.pCore hE
  rw [hEq]
  clear hE hEq
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have he₁m : e₁ ∈ g.pCore.comps := List.mem_of_getElem? hL
  have hr₁ : e₁.kind.isRandom = true := by rw [(ep_spec x (in_e₁_ep hIP hL)).1]; rfl
  have hUM : ∀ j, Unl (iBaseM x g.pCore i₁ e₁ j) := fun j => by
    unfold iBaseM oSx iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hU3 : Unl (oL3 x g.pCore) := by
    unfold oL3 oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  have hUE1 : Unl (iE1 x g.pCore i₁ e₁) := by
    unfold iE1 oSx iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x g.pCore) g.pCore.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hUD : ∀ d ∈ iDs x g.pCore i₁ e₁, Unl d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    refine Unl_append.2 ⟨Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_pickIdxs hc),
      dTerms_unl (fun c hc => (plain_bas_lift hFb 1 c hc).2) d' hd'⟩, by simp [Unl, oSx, iGw, mkC]⟩
  change S PF D e ω (pLiftT x g (psteps_iOut x g.pCore i₁ is₂ e₁)) = g.valR PF D e ω
  unfold psteps_iOut
  simp only [pLiftT_append, pLiftT_ite]
  rw [pLiftT_t0Q x g _ _ ⟨e₁, he₁m, hr₁⟩,
    pLiftT_map_Q x g _ (fun d => d) _ (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.1 hd
      exact ⟨iGw e₁, by simp, rfl⟩),
    pLiftT_map_Q x g _ (fun j => iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]) _ (fun j _ => ⟨iGw e₁, by simp [iBaseM], rfl⟩),
    pLiftT_single_Q x g _ _ ⟨mkC (.light .plus) (newA 0) (newA 0), by simp [oL3], rfl⟩,
    pLiftT_single_Q x g _ _ ⟨iGw e₁, by simp [iE1], rfl⟩,
    pLiftT_single_t1 x g _ _ hU3, pLiftT_single_t1 x g _ _ hUE1,
    pLiftT_map_t1 x g _ (fun j => iBaseM x g.pCore i₁ e₁ j) _ (fun j _ => hUM j),
    pLiftT_map_t1 x g _ (fun j => iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) _
      (fun j _ => Unl_append.2 ⟨hUM j, by simp [Unl, mkC]⟩),
    pLiftT_map_t1 x g _ (fun d => d) _ hUD]
  simp only [ite_self, List.append_nil, S_append, S_map_t1, S_t1, S_ite, ite_sum]
  rw [valR_T0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdj : ∀ j ∈ g.pCore.edgeIdx x .minus false,
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) =
        dv (D ω) (Sum.elim e s) g.pCore.comps := by
    intro j hj
    rw [edgeIdx_eq] at hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
    exact in_D3 _ hIP hL (D ω) (List.mem_filter.1 hq).1
      (by simp [cI, (List.mem_filter.1 hq).2])
  have hdE := in_D1 (Sum.elim e s) hIP hL (D ω)
  have hdD : ∀ d ∈ iDs x g.pCore i₁ e₁, ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) d =
      dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    intro d hd α
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (liftA 1 x) (newA 0) _
      (plain_bas_lift hFb 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, in_D4] at h2
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, in_D5, h2, oSx, iGw, dv_cons,
      dv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hM : ((g.pCore.edgeIdx x .minus false).map fun j => T1 PF D e ω
      ⟨(iBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
        cm * cmb * g.pCore.coeff⟩ s).sum +
      ((g.pCore.edgeIdx x .minus false).map fun j => T1 PF D e ω
      ⟨(iBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s).sum =
      pv (D ω) (Sum.elim e s) g.pEnv * ((g.pCore.edgeIdx x .minus false).map fun j => ∑ α,
        msc A.z * g.pCore.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
          (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' (Sum.elim e s e₁.x) α *
            star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) *
          star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [PBMi A x g i₁ e₁ e ω hp j s, hdj j hj]
  have hL3 := PBL A x g e ω hp s
  have hE1 := PBE1i A x g i₁ e₁ e ω hp (is₂.isEmpty = true) is₂.length
    (fun h => by simpa using h) s
  rw [hdE] at hE1
  have hD := (PBD A x g e ω _ hUD s).trans (congrArg _ (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => by rw [hdD d hd α])))
  have hT0 : T0 PF D e ω g s = g.pCore.coeff.eval (msc A.z) *
      dv (D ω) (Sum.elim e s) g.pCore.comps * pv (D ω) (Sum.elim e s) g.pEnv *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) g.pCore.comps) ω := by
    rw [T0, termR_pform A hlab hp.labRand, m_eq A]
    rfl
  have hcore := in_core A hpl hIP hL hX (Sum.elim e s) (fun α => Sum.elim e (Fin.append s ![α]))
    (fun α => elim_append_comp_liftA e s ![α]) (fun α => by simp) ω
  rw [Q_apply'] at hcore
  linear_combination hM + hL3 + hE1 + hD - hT0 - pv (D ω) (Sum.elim e s) g.pEnv * hcore

end ValueEIn

/-! ## The value of [II, (4.24)] inside `P_x`, all cases -/

section ValueE

variable {k n : ℕ}

theorem mkC_ub {V : Type*} (κ : Kind) (u v : V) (hκ : ∀ ch, κ ≠ .inv ch)
    (hκ' : ∀ ch d, κ ≠ .wD ch d) : (mkC κ u v).label = none ∧ basB (mkC κ u v) = true := by
  refine ⟨rfl, ?_⟩
  unfold basB
  cases κ with
  | inv ch => exact absurd rfl (hκ ch)
  | wD ch d => exact absurd rfl (hκ' ch d)
  | _ => rfl

theorem dPieces_ub {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) :
    ∀ c' ∈ ps, c'.label = none ∧ basB c' = true := by
  rcases c with ⟨κ, a, b, mi, l⟩
  intro c' hc'
  cases κ with
  | G ch => cases ch <;> simp [Comp.dPieces] at h <;> subst h <;> simp at hc' <;>
      rcases hc' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
  | weight ch => cases ch <;> simp [Comp.dPieces] at h <;> subst h <;> simp at hc' <;>
      rcases hc' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
  | light ch => cases ch <;> simp [Comp.dPieces] at h <;> subst h <;> simp at hc' <;>
      rcases hc' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
  | _ => simp [Comp.dPieces] at h

theorem ShapeE.ub {x : Atom k n} {H : List (Comp (Atom k n))}
    {cs : List (Comp (Atom k (n + 1)))} (h : ShapeE x H cs)
    (hH : ∀ c ∈ H, c.label = none ∧ basB c = true) :
    ∀ c ∈ cs, c.label = none ∧ basB c = true := by
  have hl : ∀ B : List (Comp (Atom k n)), (∀ c ∈ B, c ∈ H) → ∀ c ∈ liftCs 1 B,
      c.label = none ∧ basB c = true := by
    intro B hB c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2⟩ := hH c' (hB c' hc')
    exact ⟨by simp [Comp.map, h1], by rw [basB_map]; exact h2⟩
  have hsx : (mkC (.waved .s) (liftA 1 x) (newA 0)).label = none ∧
      basB (mkC (.waved .s) (liftA 1 x) (newA 0)) = true := mkC_ub _ _ _ (by simp) (by simp)
  have hNew : ∀ {u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}, κ.isSolid = true →
      NewH u κ a → a.label = none ∧ basB a = true := by
    intro u κ a hκ ha
    obtain ⟨ch, rfl⟩ := Kind.isSolid_iff.1 hκ
    rcases ha with rfl | rfl <;> exact mkC_ub _ _ _ (by simp) (by simp)
  rcases h with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c h'
    · rcases List.mem_append.1 h' with h' | h'
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
        rcases h' with rfl | rfl | rfl
        · exact hsx
        · exact hNew hr₁.1 ha₁
        · exact hNew hr₂.1 ha₂
      · obtain ⟨ch, rfl⟩ := hX c h'
        exact mkC_ub _ _ _ (by simp) (by simp)
  · intro c hc
    rcases hcs with rfl | rfl <;> rcases List.mem_append.1 hc with h' | h'
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c h'
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
      rcases h' with rfl | rfl | rfl
      · exact hsx
      · exact hNew hr₁.1 ha₁
      · exact hNew rfl hb
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c h'
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
      rcases h' with rfl | rfl | rfl
      · exact hsx
      · exact hNew rfl hb
      · exact hNew hr₁.1 ha₁
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl H (fun c hc => hc) c h'
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
      rcases h' with rfl | rfl
      · exact hsx
      · exact mkC_ub _ _ _ (by simp) (by simp)
  · intro c' hc'
    rcases List.mem_append.1 hc' with h' | h'
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c' h'
    · rcases List.mem_append.1 h' with h' | h'
      · exact dPieces_ub hps c' h'
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
        rcases h' with rfl | rfl
        · exact hsx
        · exact hNew hr.1 he

theorem ok_pLiftT' {x : Atom k n} {g : Graph k n} {E : TExpansion k n}
    (hE : ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∀ c ∈ s.g.comps, c.label = none ∧ basB c = true) :
    ∀ t ∈ pLiftT x g E, OK t.g.comps := by
  intro t ht
  obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
  rcases hE s hs with ⟨c, hc, hl⟩ | hE'
  · exfalso
    have := List.any_eq_false.1 hq c hc
    simp [hl] at this
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨hl, hb⟩ := hE' d hd
    unfold rl
    split_ifs with hr
    · exact Or.inr ⟨hr, by simpa [basB] using hb⟩
    · exact Or.inl hl
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    left
    simp [Comp.map, pEnv_unl g d hd]

/-- The value of `Ô^{(x)}_multi-e` applied to `𝒢` inside `P_x`. -/
theorem valueE {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    (hNL : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {E : TExpansion k n} (hE : multiEHat x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  have hub : ∀ c ∈ g.conj.pCore.comps, c.label = none ∧ basB c = true := fun c hc =>
    ⟨pCore_unl _ c hc, pCore_basB hp.conj c hc⟩
  have hNL' : ∀ c ∈ g.conj.pCore.comps, c.kind.isSolid = true → c.x ≠ c.y := by
    intro c hc hs
    obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
    rw [Graph.conj_comps'] at hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact hNL d' hd' (by simpa [conjC, Kind.conj_isSolid'] using hs)
  unfold multiEHat at hE
  split_ifs at hE with h1 h2 h3 h4
  · exact valueEOut_plain hlab hp hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    rw [pLiftT_conj]
    refine valueEq_conj ?_ (okP hlab hp) ?_
    · refine valueEOut_plain (lab_conj hlab) hp.conj ?_
      rw [pCore_conj]; exact hE'
    · refine ok_pLiftT' fun s hs => ?_
      rcases shapesOut hNL' (by rw [pCore_conj]; exact hE') s hs with hq | ⟨cs, co, rfl, hsh⟩
      · exact Or.inl hq
      · exact Or.inr (hsh.ub hub)
  · exact valueEIn_plain hlab hp hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    rw [pLiftT_conj]
    refine valueEq_conj ?_ (okP hlab hp) ?_
    · refine valueEIn_plain (lab_conj hlab) hp.conj ?_
      rw [pCore_conj]; exact hE'
    · refine ok_pLiftT' fun s hs => ?_
      have hout : ∀ ch, g.conj.pCore.edgeIdx x ch true = [] := by
        intro ch
        simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2
        rw [pCore_conj, psteps_edgeIdx_conj]
        cases ch
        · exact h2
        · exact h1
      rcases shapesIn hNL' hout (by rw [pCore_conj]; exact hE') s hs with hq | ⟨cs, co, rfl, hsh⟩
      · exact Or.inl hq
      · exact Or.inr (hsh.ub hub)

end ValueE

/-! ## One round: an identity inside `P_x`, the normalization and the labelled components moved
to `x` -/

section Round

variable {k : ℕ}

theorem PStepsTermOK.mono {n C C' : ℕ} {x : Atom k n} {g : Graph k n} {t : Tracked k n}
    (h : PStepsTermOK C x g t) (hC : C ≤ C') : PStepsTermOK C' x g t :=
  { h with nn := h.nn.mono hC, bnd := h.bnd.trans hC }

theorem St.mono {n C C' : ℕ} {x : Atom k n} {g : Graph k n} (h : St C x g) (hC : C ≤ C') :
    St C' x g :=
  { h with nn := h.nn.mono hC }

theorem sum_map_le {α : Type*} (L : List α) (f : α → ℕ) (b : ℕ) (h : ∀ a ∈ L, f a ≤ b) :
    (L.map f).sum ≤ b * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (List.mem_cons_self ..)
    have := ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    nlinarith

open Classical in
theorem Graph.viol_le {n : ℕ} (g : Graph k n) (x : Atom k n) :
    g.viol x ≤ 2 * g.comps.length := by
  unfold Graph.viol
  refine sum_map_le _ _ 2 fun c _ => ?_
  unfold vP
  split_ifs <;> omega

open Classical in
private theorem wBP_le4 {n : ℕ} (B : Atom k n → Prop) (c : Comp (Atom k n)) : wBP B c ≤ 4 := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp only [wBP] <;> (try split_ifs) <;> omega

theorem Graph.pw_le {n : ℕ} (g : Graph k n) (x : Atom k n) :
    g.pw x ≤ 4 * g.comps.length := by
  unfold Graph.pw
  exact sum_map_le _ _ 4 fun c _ => wBP_le4 _ c

end Round

/-! ## The choice of the identity inside `P_x` -/

section OpTerms

variable {k : ℕ}

/-- Every solid edge has a `×`-dotted edge between its two atoms. -/
def XP {n : ℕ} (h : Graph k n) : Prop :=
  ∀ c ∈ h.comps, c.kind.isSolid = true → ∃ d ∈ h.comps, d.kind = .xdot ∧
    ((d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x))

theorem xdotsAt_of_XP {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    {is : List ℕ} (his : ∀ j ∈ is, ∃ hj : j < h.comps.length, h.comps[j].kind.isSolid = true ∧
      (h.comps[j].x = x ∨ h.comps[j].y = x)) : h.xdotsAt x is = true := by
  unfold Graph.xdotsAt
  rw [List.all_eq_true]
  intro j hj
  obtain ⟨hjl, hs, hx⟩ := his j hj
  rw [List.getElem?_eq_getElem hjl]
  simp only
  obtain ⟨d, hd, hdk, hdp⟩ := hXP _ (List.getElem_mem hjl) hs
  unfold Graph.hasXdot
  rw [List.any_eq_true]
  refine ⟨d, hd, ?_⟩
  by_cases hcx : h.comps[j].x = x
  · simp only [hcx, beq_self_eq_true, ite_true, hdk, beq_self_eq_true, Bool.true_and]
    rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2, hcx]
    · simp [h1, h2, hcx]
  · have hcy : h.comps[j].y = x := hx.resolve_left hcx
    simp only [hdk, beq_self_eq_true, Bool.true_and]
    rw [if_neg (by simpa using hcx)]
    rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2, hcy]
    · simp [h1, h2, hcy]

theorem ep_solid_at {n : ℕ} {x : Atom k n} {h : Graph k n} {ch : Charge} {out : Bool}
    {j : ℕ} (hj : j ∈ h.edgeIdx x ch out) : ∃ hjl : j < h.comps.length,
      h.comps[j].kind.isSolid = true ∧ (h.comps[j].x = x ∨ h.comps[j].y = x) := by
  obtain ⟨hjl, hep⟩ := edgeIdx_mem hj
  obtain ⟨hk, ho, hi⟩ := ep_spec x hep
  refine ⟨hjl, by simp only at hk; rw [hk]; rfl, ?_⟩
  cases out
  · exact Or.inr (hi rfl).1
  · exact Or.inl (ho rfl).1

theorem multiEOut_isSome {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    (hne : h.edgeIdx x .plus true ≠ []) : ∃ E, multiEOut x h = some E := by
  have hX : h.xdotsAt x (h.edgeIdx x .plus true ++ h.edgeIdx x .minus true ++
      h.edgeIdx x .plus false ++ h.edgeIdx x .minus false) = true := by
    refine xdotsAt_of_XP hXP fun j hj => ?_
    simp only [List.mem_append] at hj
    rcases hj with ((hj | hj) | hj) | hj <;> exact ep_solid_at hj
  unfold multiEOut
  rcases hOP : h.edgeIdx x .plus true with _ | ⟨i₁, is₂⟩
  · exact absurd hOP hne
  obtain ⟨hi, -⟩ := edgeIdx_mem (show i₁ ∈ h.edgeIdx x .plus true by rw [hOP]; simp)
  rw [hOP] at hX
  simp only [List.getElem?_eq_getElem hi]
  rw [if_neg (by rw [hX]; simp)]
  exact ⟨_, rfl⟩

theorem multiEIn_isSome {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    (hne : h.edgeIdx x .plus false ≠ []) : ∃ E, multiEIn x h = some E := by
  have hX : h.xdotsAt x (h.edgeIdx x .plus false ++ h.edgeIdx x .minus false) = true := by
    refine xdotsAt_of_XP hXP fun j hj => ?_
    simp only [List.mem_append] at hj
    rcases hj with hj | hj <;> exact ep_solid_at hj
  unfold multiEIn
  rcases hIP : h.edgeIdx x .plus false with _ | ⟨i₁, is₂⟩
  · exact absurd hIP hne
  obtain ⟨hi, -⟩ := edgeIdx_mem (show i₁ ∈ h.edgeIdx x .plus false by rw [hIP]; simp)
  rw [hIP] at hX
  simp only [List.getElem?_eq_getElem hi]
  rw [if_neg (by rw [hX]; simp)]
  exact ⟨_, rfl⟩

theorem XP.conj {n : ℕ} {h : Graph k n} (hXP : XP h) : XP h.conj := by
  intro c hc hs
  rw [Graph.conj_comps'] at hc ⊢
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨d, hd, hdk, hdp⟩ := hXP c' hc' (by simpa [conjC, Kind.conj_isSolid'] using hs)
  exact ⟨conjC d, List.mem_map_of_mem hd, by simp [conjC, hdk, Kind.conj], hdp⟩

theorem multiEHat_isSome {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    (hne : ∃ ch out, h.edgeIdx x ch out ≠ []) : ∃ E, multiEHat x h = some E := by
  unfold multiEHat
  split_ifs with h1 h2 h3 h4
  · exact multiEOut_isSome hXP (by simpa using h1)
  · obtain ⟨E, hE⟩ := multiEOut_isSome hXP.conj (by rw [psteps_edgeIdx_conj]; simpa [Charge.flip] using h2)
    exact ⟨_, by rw [hE]; rfl⟩
  · exact multiEIn_isSome hXP (by simpa using h3)
  · obtain ⟨E, hE⟩ := multiEIn_isSome hXP.conj (by rw [psteps_edgeIdx_conj]; simpa [Charge.flip] using h4)
    exact ⟨_, by rw [hE]; rfl⟩
  · exfalso
    obtain ⟨ch, out, hne⟩ := hne
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2 h3 h4
    cases ch <;> cases out <;> simp_all

theorem XP_core {n C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g) :
    XP g.pCore := by
  intro c hc hs
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  have hp : g.partB d = true := by
    by_contra hp
    have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hd, hs, by simpa using hp⟩
    rw [hS.unp] at this; simp at this
  obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 hp
  have hel : e.label = none := by
    by_contra hne
    have := hS.nn.plain.labRand e he (Option.isSome_iff_ne_none.2 hne)
    rw [hek] at this; simp [Kind.isRandom] at this
  refine ⟨{ e with label := none }, ?_, hek, hep⟩
  rw [pCore_comps]
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨he, by simp [coreP, hek, Kind.isRandom]⟩)

end OpTerms

section OpLengths

variable {k : ℕ}

theorem length_pLiftT_le {n : ℕ} (x : Atom k n) (g : Graph k n) (E : TExpansion k n) :
    (pLiftT x g E).length ≤ E.length := List.length_filterMap_le _ _

theorem splitRegular_length_le {V : Type*} [DecidableEq V] (x : V) (cs : List (Comp V)) :
    (splitRegular x cs).length ≤ 2 ^ cs.length := by
  induction cs with
  | nil => simp [splitRegular]
  | cons c cs ih =>
    rcases c with ⟨κ, a, b, mi, l⟩
    cases κ <;> simp only [splitRegular] <;> (try split_ifs) <;>
      simp only [List.length_append, List.length_map, List.length_cons, pow_succ] <;> omega

theorem dTerms_length_le {V : Type*} [DecidableEq V] (p q : V) (cs : List (Comp V)) :
    (dTerms p q cs).length ≤ cs.length :=
  (List.length_filterMap_le _ _).trans (by simp)

theorem edgeIdx_length_le {n : ℕ} (h : Graph k n) (x : Atom k n) (ch : Charge)
    (out : Bool) : (h.edgeIdx x ch out).length ≤ h.comps.length := by
  unfold Graph.edgeIdx
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem pCore_length_le {n : ℕ} (g : Graph k n) : g.pCore.comps.length ≤ g.comps.length := by
  rw [pCore_comps, List.length_map]; exact List.length_filter_le _ _

theorem eraseIdxs_length_le {α : Type*} (is : List ℕ) (l : List α) :
    (eraseIdxs is l).length ≤ l.length := by
  unfold eraseIdxs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem oWeightP2Pos_length {n : ℕ} {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hE : oWeightP2Pos x h = some E) : E.length ≤ h.comps.length + 2 := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i _
  simp only [Option.some.injEq] at hE
  subst hE
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
  have := dTerms_length_le (newA 0) (liftA 1 x) (liftCs 1 (h.comps.eraseIdx i))
  have h2 : (liftCs 1 (h.comps.eraseIdx i)).length ≤ h.comps.length := by
    simp only [liftCs, List.length_map, List.length_eraseIdx]
    split_ifs <;> omega
  omega

theorem oWeightP2T_length {n : ℕ} (x : Atom k n) (g : Graph k n) :
    (oWeightP2T x g).length ≤ g.comps.length + 2 := by
  have hc := pCore_length_le g
  unfold oWeightP2T
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · dsimp only
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E'
    · simp [Tracked.self]
    · dsimp only
      refine (length_pLiftT_le _ _ _).trans ?_
      have := oWeightP2Pos_length hE'
      simp only [TExpansion.conj, List.length_map, Graph.conj_comps'] at this ⊢
      omega
  · dsimp only
    have := oWeightP2Pos_length hE
    exact (length_pLiftT_le _ _ _).trans (by omega)

theorem oOut_length {n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : (psteps_oOut x Γ i₁ is₂ e₁).length ≤ 8 * Γ.comps.length + 8 := by
  have h1 := edgeIdx_length_le Γ x .minus true
  have h2 := edgeIdx_length_le Γ x .plus false
  have h3 : (oDs x Γ i₁ e₁).length ≤ Γ.comps.length := by
    unfold oDs
    rw [List.length_map]
    refine (dTerms_length_le _ _ _).trans ?_
    simp only [liftCs, List.length_map]
    exact eraseIdxs_length_le _ _
  unfold psteps_oOut
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega

theorem iOut_length {n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : (psteps_iOut x Γ i₁ is₂ e₁).length ≤ 8 * Γ.comps.length + 8 := by
  have h1 := edgeIdx_length_le Γ x .minus false
  have h3 : (iDs x Γ i₁ e₁).length ≤ Γ.comps.length := by
    unfold iDs
    rw [List.length_map]
    refine (dTerms_length_le _ _ _).trans ?_
    simp only [liftCs, List.length_map]
    exact eraseIdxs_length_le _ _
  unfold psteps_iOut
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega

theorem multiEHat_length {n : ℕ} {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hE : multiEHat x h = some E) : E.length ≤ 8 * h.comps.length + 8 := by
  unfold multiEHat at hE
  split_ifs at hE
  · obtain ⟨i₁, is₂, e₁, -, -, -, hEq⟩ := multiEOut_some x h hE
    rw [hEq]
    exact oOut_length x h i₁ is₂ e₁
  · obtain ⟨E', hE', hEq⟩ := Option.map_eq_some_iff.1 hE
    obtain ⟨i₁, is₂, e₁, -, -, -, hEq'⟩ := multiEOut_some x h.conj hE'
    rw [← hEq, hEq']
    have := oOut_length x h.conj i₁ is₂ e₁
    rw [TExpansion.conj, List.length_map]
    rw [Graph.conj_comps', List.length_map] at this
    exact this
  · obtain ⟨i₁, is₂, e₁, -, -, -, hEq⟩ := multiEIn_some x h hE
    rw [hEq]
    exact iOut_length x h i₁ is₂ e₁
  · obtain ⟨E', hE', hEq⟩ := Option.map_eq_some_iff.1 hE
    obtain ⟨i₁, is₂, e₁, -, -, -, hEq'⟩ := multiEIn_some x h.conj hE'
    rw [← hEq, hEq']
    have := iOut_length x h.conj i₁ is₂ e₁
    rw [TExpansion.conj, List.length_map]
    rw [Graph.conj_comps', List.length_map] at this
    exact this

end OpLengths

section RoundFull

variable {k : ℕ}

end RoundFull

section Iter

variable {k : ℕ}

end Iter

section InitMerge

variable {k n : ℕ}

end InitMerge

/-! ## [II, Lemma 4.13] -/

section Main

variable {k : ℕ}

/-- No weighted labelled weight or edge end at the block of `y`: no labelled weight or solid edge
is attached to that block. -/
theorem labelledFree_of_pw {n : ℕ} {g : Graph k n} {y : Atom k n} (hp : g.Plain)
    (h : g.pw y = 0) : g.LabelledFreeAtBlock y := by
  classical
  intro c hc hl hr
  unfold Graph.pw at h
  have h0 : wBP (fun u => g.SameBlock u y) c = 0 :=
    List.sum_eq_zero_iff.1 h _ (List.mem_map_of_mem hc)
  obtain ⟨-, hinv, hwD, -, hwf, -⟩ := hp c hc
  rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, d⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _
  · rw [wBP_G hk hl] at h0
    by_cases h1 : g.SameBlock c.x y <;> by_cases h2 : g.SameBlock c.y y <;> simp_all
  · rw [wBP_W hk hl] at h0
    have hy : c.y = c.x := hwf (by rw [hk]; rfl)
    by_cases h1 : g.SameBlock c.x y
    · simp [h1] at h0
    · exact ⟨h1, by rw [hy]; exact h1⟩
  · rw [wBP_L hk hl] at h0
    have hy : c.y = c.x := hwf (by rw [hk]; rfl)
    by_cases h1 : g.SameBlock c.x y
    · simp [h1] at h0
    · exact ⟨h1, by rw [hy]; exact h1⟩
  · exact absurd hk (hinv ch)
  · exact absurd hk (hwD ch d)
  all_goals (rw [hk] at hr; simp [Kind.isRandom] at hr)

end Main

/-! ## The components at an external atom -/

section OAt

variable {k : ℕ}

/-- The component has an end at the external atom `o`. -/
def atO {n : ℕ} (o : Fin k) (c : Comp (Atom k n)) : Bool :=
  decide (c.x = .inl o ∨ c.y = .inl o)

/-- Every component of `Γ` at the external atom `o` is a diffusive edge. -/
def ODiff {n : ℕ} (o : Fin k) (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl o ∨ c.y = .inl o) → c.kind.isDiffusive = true

/-- The components of `T` at the external atom `o` are, up to order, those of `Γ`. -/
def OKeep {n : ℕ} (o : Fin k) (Γ T : Graph k n) : Prop :=
  (T.comps.filter (atO o)).Perm (Γ.comps.filter (atO o))

/-- The components of the output graph `t` at the external atom `o` are, up to order, the images
of those of `Γ`. -/
def OOut {n : ℕ} (o : Fin k) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  (t.g.comps.filter (atO o)).Perm ((Γ.comps.filter (atO o)).map (Comp.map t.f))

/-- At every external atom at which all components of `Γ` are diffusive, the components of `T`
are, up to order, those of `Γ`. -/
def PStepsOK1 {n : ℕ} (Γ T : Graph k n) : Prop := ∀ o, ODiff o Γ → OKeep o Γ T

/-- At every external atom at which all components of `Γ` are diffusive, the components of the
output graph `t` are, up to order, the images of those of `Γ`. -/
def OO1 {n : ℕ} (Γ : Graph k n) (t : Tracked k n) : Prop := ∀ o, ODiff o Γ → OOut o Γ t

theorem psteps_atO_iff {n : ℕ} {o : Fin k} {c : Comp (Atom k n)} :
    atO o c = true ↔ (c.x = .inl o ∨ c.y = .inl o) := by
  simp [atO]

theorem ODiff.diff {n : ℕ} {o : Fin k} {Γ : Graph k n} (hO : ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (ho : atO o c = true) : c.kind.isDiffusive = true :=
  hO c hc (psteps_atO_iff.1 ho)

/-- A random component of a graph with only diffusive components at `o` is not at `o`. -/
theorem ODiff.random {n : ℕ} {o : Fin k} {Γ : Graph k n} (hO : ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) : atO o c = false := by
  cases ho : atO o c
  · rfl
  · have := hO.diff hc ho
    rw [Kind.not_isDiffusive_of_isRandom hr] at this
    cases this

theorem OKeep.diff {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T)
    (hO : ODiff o Γ) {c : Comp (Atom k n)} (hc : c ∈ T.comps) (ho : atO o c = true) :
    c.kind.isDiffusive = true :=
  hO.diff (List.mem_filter.1 (h.subset (List.mem_filter.2 ⟨hc, ho⟩))).1 ho

theorem ODiff.of_keep {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T)
    (hO : ODiff o Γ) : ODiff o T :=
  fun _ hc ho => h.diff hO hc (psteps_atO_iff.2 ho)

theorem OKeep.atO_false {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T)
    (hO : ODiff o Γ) {c : Comp (Atom k n)} (hc : c ∈ T.comps) (hd : c.kind.isDiffusive = false) :
    atO o c = false := by
  cases ho : atO o c
  · rfl
  · rw [h.diff hO hc ho] at hd
    cases hd

theorem OKeep.erase {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T) {i : ℕ}
    {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hco : atO o c = false) (co : Coeff) :
    OKeep o Γ ⟨T.comps.eraseIdx i, co⟩ := by
  have hp := (perm_cons_eraseIdx hc).filter (atO o)
  rw [List.filter_cons_of_neg (by simp [hco])] at hp
  exact hp.symm.trans h

theorem OKeep.append {n : ℕ} {o : Fin k} {Γ : Graph k n} {L : List (Comp (Atom k n))}
    (h : (L.filter (atO o)).Perm (Γ.comps.filter (atO o))) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, atO o d = false) (co : Coeff) : OKeep o Γ ⟨L ++ new, co⟩ := by
  have : new.filter (atO o) = [] := List.filter_eq_nil_iff.2 fun d hd => by simp [hnew d hd]
  change ((L ++ new).filter (atO o)).Perm _
  rw [List.filter_append, this, List.append_nil]
  exact h

private theorem Comp.map_id'' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

private theorem Comp.map_comp'' {U V W : Type*} (f : U → V) (g : V → W) (c : Comp U) :
    (c.map f).map g = c.map (g ∘ f) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map, Function.comp_def]

/-- Components mapped by an atom map that sends only `o` to `o`: those at `o` are the images of
those at `o`. -/
theorem filter_atO_map {n m : ℕ} {o : Fin k} (f : Atom k n → Atom k m)
    (hf : ∀ u, f u = .inl o ↔ u = .inl o) (L : List (Comp (Atom k n))) :
    (L.map (Comp.map f)).filter (atO o) = (L.filter (atO o)).map (Comp.map f) := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun c _ => ?_
  simp only [Function.comp_apply, atO, Comp.map, hf]

theorem atO_map {n m : ℕ} {o : Fin k} {f : Atom k n → Atom k m}
    (hf : ∀ u, f u = .inl o ↔ u = .inl o) (c : Comp (Atom k n)) : atO o (c.map f) = atO o c := by
  simp only [atO, Comp.map, hf]

theorem liftA_iff {n : ℕ} (o : Fin k) (u : Atom k n) :
    liftA 1 u = .inl o ↔ u = .inl o := by
  rcases u with a | a <;> simp [liftA]

theorem OOut.self {n : ℕ} (o : Fin k) (Γ : Graph k n) : OOut o Γ (Tracked.self Γ) := by
  unfold OOut
  have : (Γ.comps.filter (atO o)).map (Comp.map (Tracked.self Γ).f) = Γ.comps.filter (atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c
  rw [this]
  exact List.Perm.refl _

theorem PStepsOK1.refl {n : ℕ} (Γ : Graph k n) : PStepsOK1 Γ Γ := fun _ _ => List.Perm.refl _

theorem OO1.self {n : ℕ} (Γ : Graph k n) : OO1 Γ (Tracked.self Γ) :=
  fun o _ => OOut.self o Γ

theorem PStepsOK1.trans {n : ℕ} {Γ T T' : Graph k n} (h1 : PStepsOK1 Γ T) (h2 : PStepsOK1 T T') :
    PStepsOK1 Γ T' := fun o hO => (h2 o (ODiff.of_keep (h1 o hO) hO)).trans (h1 o hO)

/-- The graph `T` itself as an output keeps the components at the external atoms. -/
theorem OO1.of_keep {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) : OO1 Γ (Tracked.self T) := by
  intro o hO
  have hid : (Γ.comps.filter (atO o)).map (Comp.map (Tracked.self T).f) =
      Γ.comps.filter (atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c
  change (T.comps.filter (atO o)).Perm _
  rw [hid]
  exact h o hO

theorem OO1.of_ok {n : ℕ} {Γ T : Graph k n} {t : Tracked k n} (h1 : PStepsOK1 Γ T)
    (h2 : OO1 T t) : OO1 Γ t := by
  intro o hO
  have h1o := h1 o hO
  exact (h2 o (ODiff.of_keep h1o hO)).trans (List.Perm.map _ h1o)

theorem ODiff.of_oout {n : ℕ} {o : Fin k} {Γ : Graph k n} {t : Tracked k n}
    (h : OOut o Γ t) (hO : ODiff o Γ) : ODiff o t.g := by
  intro c hc ho
  have hc' : c ∈ (Γ.comps.filter (atO o)).map (Comp.map t.f) :=
    h.subset (List.mem_filter.2 ⟨hc, psteps_atO_iff.2 ho⟩)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨hdΓ, hdo⟩ := List.mem_filter.1 hd
  exact hO.diff hdΓ hdo

theorem OOut.comp {n : ℕ} {o : Fin k} {Γ : Graph k n} {t : Tracked k n}
    {s : Tracked k t.nOut} (h1 : OOut o Γ t) (h2 : OOut o t.g s) :
    OOut o Γ (t.comp s) := by
  change (s.g.comps.filter (atO o)).Perm ((Γ.comps.filter (atO o)).map (Comp.map (s.f ∘ t.f)))
  refine h2.trans ?_
  refine (List.Perm.map _ h1).trans ?_
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun c _ => ?_)
  exact Comp.map_comp'' t.f s.f c

theorem OO1.comp {n : ℕ} {Γ : Graph k n} {t : Tracked k n} {s : Tracked k t.nOut}
    (h1 : OO1 Γ t) (h2 : OO1 t.g s) : OO1 Γ (t.comp s) :=
  fun o hO => (h1 o hO).comp (h2 o (ODiff.of_oout (h1 o hO) hO))

/-- Removing a component that is not diffusive keeps the components at the external atoms. -/
theorem PStepsOK1.erase {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false) (co : Coeff) :
    PStepsOK1 Γ ⟨T.comps.eraseIdx i, co⟩ := fun o hO =>
  (h o hO).erase hc ((h o hO).atO_false hO (List.mem_of_getElem? hc) hcd) co

/-- Adding components that are not at the external atoms at which all components of `Γ` are
diffusive keeps the components there. -/
theorem PStepsOK1.append {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) (new : List (Comp (Atom k n)))
    (hnew : ∀ o, ODiff o Γ → ∀ d ∈ new, atO o d = false) (co : Coeff) :
    PStepsOK1 Γ ⟨T.comps ++ new, co⟩ := fun o hO => OKeep.append (h o hO) new (hnew o hO) co

/-- The components at `o` under `O_merge`, when `o` is the only atom with image `o` and every
component at `o` is diffusive. -/
theorem filter_atO_merge {n m : ℕ} (o : Fin k) (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (hf : ∀ u, f u = .inl o ↔ u = .inl o) :
    ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, atO o c = true → c.kind.isDiffusive = true) →
      (L.filterMap (psteps_mergeComp rep f)).filter (atO o) = (L.filter (atO o)).map (Comp.map f)
  | [], _ => rfl
  | c :: L, hL => by
    have ih := filter_atO_merge o rep f hf L fun d hd => hL d (List.mem_cons_of_mem _ hd)
    rw [List.filterMap_cons]
    by_cases ho : atO o c = true
    · have hdf := hL c (List.mem_cons_self ..) ho
      have hnd : c.kind ≠ .dot := fun h => by rw [h] at hdf; cases hdf
      have hns : c.kind.isSolid = false := by
        cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
      rw [mergeComp_other hnd hns, List.filter_cons_of_pos ho]
      have ho' : atO o (c.map f) = true := by
        rw [psteps_atO_iff] at ho ⊢
        simp only [Comp.map]
        rcases ho with h | h
        · exact Or.inl ((hf _).2 h)
        · exact Or.inr ((hf _).2 h)
      rw [List.filter_cons_of_pos ho', ih, List.map_cons]
    · have ho2 : ¬ (c.x = .inl o ∨ c.y = .inl o) := fun h => ho (psteps_atO_iff.2 h)
      push Not at ho2
      obtain ⟨hx, hy⟩ := ho2
      have hx' : f c.x ≠ .inl o := fun h => hx ((hf _).1 h)
      have hy' : f c.y ≠ .inl o := fun h => hy ((hf _).1 h)
      rw [List.filter_cons_of_neg ho]
      rcases hm : psteps_mergeComp rep f c with _ | c'
      · exact ih
      · have hc' : atO o c' = false := by
          unfold psteps_mergeComp at hm
          split_ifs at hm
          · obtain rfl := Option.some.inj hm
            simp [atO, Comp.map, hx']
          · obtain rfl := Option.some.inj hm
            simp [atO, Comp.map, hx', hy']
        simp only
        rw [List.filter_cons_of_neg (by simp [hc']), ih]

/-- The atom map of `O_merge` sends only `o` to `o`. -/
theorem PStepsMergeSpec.f_iff {n : ℕ} {Γ : Graph k n} {t : Tracked k n} (hs : PStepsMergeSpec Γ t)
    (o : Fin k) (u : Atom k n) : t.f u = .inl o ↔ u = .inl o := by
  obtain ⟨φ, hφ, -⟩ := hs.f_inr
  rcases u with a | i
  · simp [hs.f_inl]
  · rw [hφ]
    simp

theorem filter_atO_nd {n : ℕ} {o : Fin k} {L : List (Comp (Atom k n))}
    (hL : ∀ c ∈ L, atO o c = true → c.kind ≠ .dot) :
    L.filter (atO o) = (L.filter fun c => decide (c.kind ≠ .dot)).filter (atO o) := by
  rw [List.filter_filter]
  refine List.filter_congr fun c hc => ?_
  by_cases ho : atO o c = true
  · simp [ho, hL c hc ho]
  · simp [ho]

/-- The output of `O_merge` followed by the removal of redundant dotted edges keeps the components
at `o`. -/
theorem merge_oout {n : ℕ} {o : Fin k} {Γ T : Graph k n} {t : Tracked k n}
    (hs : PStepsMergeSpec T t) (hO : ODiff o Γ) (hK : OKeep o Γ T) {g' : Graph k t.nOut}
    (hsub : g'.comps.Sublist t.g.comps)
    (hnd : (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
      (t.g.comps.filter fun c => decide (c.kind ≠ .dot))) :
    OOut o Γ ⟨t.nOut, g', t.f⟩ := by
  have hT : ∀ c ∈ T.comps, atO o c = true → c.kind.isDiffusive = true :=
    fun c hc ho => hK.diff hO hc ho
  have hm := filter_atO_merge o T.psteps_mrep t.f (hs.f_iff o) T.comps hT
  rw [← hs.comps_eq] at hm
  have hnd1 : ∀ c ∈ t.g.comps, atO o c = true → c.kind ≠ .dot := by
    intro c hc ho h
    have hc' : c ∈ (T.comps.filter (atO o)).map (Comp.map t.f) := by
      rw [← hm]
      exact List.mem_filter.2 ⟨hc, ho⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨hdT, hdo⟩ := List.mem_filter.1 hd
    have := hT d hdT hdo
    simp only [Comp.map] at h
    rw [h] at this
    cases this
  have hnd2 : ∀ c ∈ g'.comps, atO o c = true → c.kind ≠ .dot :=
    fun c hc ho => hnd1 c (hsub.subset hc) ho
  change (g'.comps.filter (atO o)).Perm ((Γ.comps.filter (atO o)).map (Comp.map t.f))
  rw [filter_atO_nd hnd2]
  refine (hnd.filter (atO o)).trans ?_
  rw [← filter_atO_nd hnd1, hm]
  exact List.Perm.map _ hK

end OAt

/-! ## The components at an external atom in the terms of the steps inside `P_x` -/

section OTerms

variable {k n : ℕ}

theorem rl_atO {m : ℕ} {o : Fin k} (y : Atom k m) (c : Comp (Atom k m)) :
    atO o (rl y c) = atO o c := by
  unfold rl
  split <;> rfl

theorem solidC_atO {m : ℕ} {o : Fin k} (ch : Charge) {u v : Atom k m}
    (hu : u ≠ .inl o) (hv : v ≠ .inl o) : atO o (solidC ch u v) = false := by
  unfold solidC
  split_ifs <;> simp [atO, mkC, hu, hv]

/-- The factors of `-∂_{h_{pq}}` of a component not at `o`, with `p, q ≠ o`, are not at `o`. -/
theorem dPieces_atO {m : ℕ} {o : Fin k} {p q : Atom k m} {c : Comp (Atom k m)}
    {ps : List (Comp (Atom k m))} (h : c.dPieces p q = some ps) (hp : p ≠ .inl o)
    (hq : q ≠ .inl o) (hc : atO o c = false) : ∀ a ∈ ps, atO o a = false := by
  have hcx : c.x ≠ .inl o := fun e => by simp [atO, e] at hc
  have hcy : c.y ≠ .inl o := fun e => by simp [atO, e] at hc
  have hb : (if c.kind.isWeight then c.x else c.y) ≠ .inl o := by
    split
    · exact hcx
    · exact hcy
  intro a ha
  rcases c with ⟨κ, cx, cy, mi, l⟩
  simp only at hcx hcy hb
  cases κ with
  | G ch =>
    cases ch <;> simp only [Comp.dPieces, Option.some.injEq] at h <;> subst h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;> exact solidC_atO _ (by assumption) (by assumption)
  | weight ch =>
    cases ch <;> simp only [Comp.dPieces, Option.some.injEq] at h <;> subst h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;> exact solidC_atO _ (by assumption) (by assumption)
  | light ch =>
    cases ch <;> simp only [Comp.dPieces, Option.some.injEq] at h <;> subst h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;> exact solidC_atO _ (by assumption) (by assumption)
  | _ => simp [Comp.dPieces] at h

/-- The random components of `g.pCore` are not at an external atom at which all components of `g`
are diffusive. -/
theorem core_random {o : Fin k} {g : Graph k n} (hO : ODiff o g) {c : Comp (Atom k n)}
    (hc : c ∈ g.pCore.comps) (hr : c.kind.isRandom = true) : atO o c = false := by
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  change atO o d = false
  exact hO.random hd hr

/-- The components of `g.pCore` at `o` are those of `g`. -/
theorem core_filter {o : Fin k} {g : Graph k n} (hO : ODiff o g) (hlr : g.LabRand) :
    g.pCore.comps.filter (atO o) = g.comps.filter (atO o) := by
  rw [pCore_comps]
  rw [show ((g.comps.filter coreP).map fun c => { c with label := none }).filter (atO o) =
      ((g.comps.filter coreP).filter (atO o)).map fun c => { c with label := none } by
    rw [List.filter_map]
    rfl]
  rw [List.filter_filter]
  have e1 : (g.comps.filter fun c => atO o c && coreP c) = g.comps.filter (atO o) := by
    refine List.filter_congr fun c hc => ?_
    by_cases ho : atO o c = true
    · have hd := hO.diff hc ho
      have hr : c.kind.isRandom = false := by
        cases hk : c.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
      simp [ho, coreP, hr]
    · simp [ho]
  rw [e1]
  conv_rhs => rw [← List.map_id (g.comps.filter (atO o))]
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨hcg, ho⟩ := List.mem_filter.1 hc
  have hd := hO.diff hcg ho
  have hl : c.label = none := by
    by_contra hne
    have hr := hlr c hcg (Option.isSome_iff_ne_none.2 hne)
    rw [Kind.not_isDiffusive_of_isRandom hr] at hd
    cases hd
  obtain ⟨κ, a, b, mi, l⟩ := c
  simp only at hl
  subst hl
  rfl

/-- A term `s` of an identity applied to `g.pCore` that keeps the components at `o`, read inside
`P_x` (`pLiftT`), keeps the components of `g` at `o`. -/
theorem pLift_oout {o : Fin k} {x : Atom k n} {g : Graph k n} (hO : ODiff o g)
    (hlr : g.LabRand) {s : Tracked k n} (hf : ∀ u, s.f u = .inl o ↔ u = .inl o)
    (hs : OOut o g.pCore s) :
    OOut o g ⟨s.nOut, ⟨s.g.comps.map (rl (s.f x)) ++ g.pEnv.map (Comp.map s.f), s.g.coeff⟩,
      s.f⟩ := by
  change ((s.g.comps.map (rl (s.f x)) ++ g.pEnv.map (Comp.map s.f)).filter (atO o)).Perm
    ((g.comps.filter (atO o)).map (Comp.map s.f))
  have hE : (g.pEnv.map (Comp.map s.f)).filter (atO o) = [] := by
    rw [filter_atO_map _ hf, List.filter_eq_nil_iff.2 (fun c hc => ?_), List.map_nil]
    have hc' : c ∈ g.comps ∧ c.label.isNone = true ∧ c.kind.isRandom = true := by
      unfold Graph.pEnv at hc
      simpa using hc
    simp [hO.random hc'.1 hc'.2.2]
  rw [List.filter_append, hE, List.append_nil, List.filter_map]
  have e1 : s.g.comps.filter (atO o ∘ rl (s.f x)) = s.g.comps.filter (atO o) :=
    List.filter_congr fun c _ => by rw [Function.comp_apply, rl_atO]
  rw [e1]
  have hO' : ∀ c ∈ s.g.comps.filter (atO o), c.kind.isRandom = false := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (hs.subset hc)
    obtain ⟨hdc, hdo⟩ := List.mem_filter.1 hd
    rw [core_filter hO hlr] at hd
    have := hO.diff (List.mem_filter.1 hd).1 hdo
    simp only [Comp.map]
    cases hk : d.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
  have e2 : (s.g.comps.filter (atO o)).map (rl (s.f x)) = s.g.comps.filter (atO o) := by
    conv_rhs => rw [← List.map_id (s.g.comps.filter (atO o))]
    refine List.map_congr_left fun c hc => ?_
    unfold rl
    simp [hO' c hc]
  rw [e2, ← core_filter hO hlr]
  exact hs

/-- The terms of `O^{(x),1}_weight` keep the components at `o`, if no regular weight is at `o`. -/
theorem w1_oout {o : Fin k} {x : Atom k n} {h : Graph k n}
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false) :
    ∀ s ∈ oWeight1T x h, OOut o h s := by
  intro s hs
  unfold oWeight1T at hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
  obtain ⟨W₁, W₂, rest, h1, h2, h3, -⟩ := splitRegular_dec x h.comps p hp
  have hW : ∀ c ∈ W₁ ++ W₂, atO o c = false := by
    intro c hc
    obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 (h3 c hc)
    exact hR c (h1.symm.subset (List.mem_append_left _ hc)) (by rw [hk]; rfl)
  change (p.1.filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map id))
  rw [map_comp_id]
  refine (h2.filter _).trans ?_
  refine List.Perm.trans ?_ (h1.filter _).symm
  rw [List.filter_append, List.filter_append, List.filter_append]
  have e1 : (W₁.map toLight).filter (atO o) = [] := List.filter_eq_nil_iff.2 fun c hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    have : atO o (toLight d) = false := hW d (List.mem_append_left _ hd)
    simp [this]
  have e2 : W₁.filter (atO o) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simp [hW c (List.mem_append_left _ hc)]
  have e3 : W₂.filter (atO o) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simp [hW c (List.mem_append_right _ hc)]
  rw [e1, e2, e3]
  simp

/-- The terms of [II, (4.23)] keep the components at `o`, if no random component is at `o`. -/
theorem p2_oout {o : Fin k} {x : Atom k n} {h : Graph k n} (hx : x.isRight = true)
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false)
    {E : TExpansion k n} (hE : oWeightP2Pos x h = some E) : ∀ s ∈ E, OOut o h s := by
  intro s hs
  obtain ⟨i, hi, hk, hxi, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
  have hxo : liftA 1 x ≠ (.inl o : Atom k (n + 1)) := by
    rw [Ne, liftA_iff]
    rintro rfl
    cases hx
  have hno : newA 0 ≠ (.inl o : Atom k (n + 1)) := by simp [newA]
  have hci : atO o h.comps[i] = false := hR _ (List.getElem_mem hi) (by rw [hk]; rfl)
  have hperm : (h.comps.filter (atO o)).Perm ((h.comps.eraseIdx i).filter (atO o)) := by
    have := (List.getElem_cons_eraseIdx_perm hi).filter (atO o)
    rw [List.filter_cons_of_neg (by simp [hci])] at this
    exact this.symm
  have hsx : atO o (mkC (.waved .s) (liftA 1 x) (newA 0)) = false := by simp [atO, mkC, hxo, hno]
  change (cs.filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map (liftA 1)))
  rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
  · rw [List.filter_append, liftCs, filter_atO_map _ (liftA_iff o)]
    have : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)] :
        List (Comp (Atom k (n + 1)))).filter (atO o) = [] := by simp [atO, mkC, hxo, hno]
    rw [this, List.append_nil]
    exact List.Perm.map _ hperm.symm
  · rw [List.filter_append, liftCs, filter_atO_map _ (liftA_iff o)]
    have : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)] :
        List (Comp (Atom k (n + 1)))).filter (atO o) = [] := by simp [atO, mkC, hxo, hno]
    rw [this, List.append_nil]
  · have hc₀ : (h.comps.eraseIdx i)[j] ∈ h.comps :=
      List.mem_of_mem_eraseIdx (List.getElem_mem hj)
    have hr₀ : ((h.comps.eraseIdx i)[j]).kind.isRandom = true := by
      have := dPieces_random hps
      simpa [Comp.map] using this
    have hc₀o : atO o (h.comps.eraseIdx i)[j] = false := hR _ hc₀ hr₀
    have hc₀o' : atO o (((h.comps.eraseIdx i)[j]).map (liftA 1)) = false :=
      (atO_map (liftA_iff o) _).trans hc₀o
    have hps' := dPieces_atO hps hno hxo hc₀o'
    have hperm2 : ((h.comps.eraseIdx i).filter (atO o)).Perm
        (((h.comps.eraseIdx i).eraseIdx j).filter (atO o)) := by
      have := (List.getElem_cons_eraseIdx_perm hj).filter (atO o)
      rw [List.filter_cons_of_neg (by simp [hc₀o])] at this
      exact this.symm
    rw [List.filter_append, List.filter_append, liftCs, filter_atO_map _ (liftA_iff o)]
    have e1 : ps.filter (atO o) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by simp [hps' c hc]
    have e2 : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)] :
        List (Comp (Atom k (n + 1)))).filter (atO o) = [] := by simp [atO, mkC, hxo, hno]
    rw [e1, e2, List.append_nil, List.append_nil]
    exact List.Perm.map _ (hperm.trans hperm2).symm

/-- The terms of [II, (4.24)] other than those with the label `Q_x` keep the components at `o`, if
no random component is at `o`. -/
theorem me_oout {o : Fin k} {x : Atom k n} {h : Graph k n} (hx : x.isRight = true)
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false)
    {E : TExpansion k n} (hE : multiEHat x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨ OOut o h s := by
  intro s hs
  rcases shapes_multiEHat hNL hE s hs with hq | ⟨cs, co, rfl, hsh⟩
  · exact Or.inl hq
  right
  have hxo : liftA 1 x ≠ (.inl o : Atom k (n + 1)) := by
    rw [Ne, liftA_iff]
    rintro rfl
    cases hx
  have hno : newA 0 ≠ (.inl o : Atom k (n + 1)) := by simp [newA]
  have hxo' : x ≠ .inl o := by
    rintro rfl
    cases hx
  -- an edge at `x` of `h` has its other end away from `o`
  have hedge : ∀ r u, r ∈ h.comps → EdgeH x u r → u ≠ .inl o := by
    intro r u hr he hu
    have := hR r hr (Kind.isRandom_of_isSolid he.1)
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [atO, h2, hu] at this
    · simp [atO, h1, hu] at this
  have hnew : ∀ (u : Atom k n) (κ : Kind) (a : Comp (Atom k (n + 1))), u ≠ .inl o →
      NewH u κ a → atO o a = false := by
    intro u κ a hu ha
    have hu' : liftA 1 u ≠ (.inl o : Atom k (n + 1)) := by rw [Ne, liftA_iff]; exact hu
    rcases ha with rfl | rfl <;> simp [atO, mkC, hno, hu']
  have hsx : atO o (mkC (.waved .s) (liftA 1 x) (newA 0)) = false := by simp [atO, mkC, hxo, hno]
  -- the general form
  have key : ∀ (R B : List (Comp (Atom k n))) (A : List (Comp (Atom k (n + 1)))),
      h.comps.Perm (R ++ B) → (∀ r ∈ R, atO o r = false) → (∀ a ∈ A, atO o a = false) →
      ((liftCs 1 B ++ A).filter (atO o)).Perm
        ((h.comps.filter (atO o)).map (Comp.map (liftA 1))) := by
    intro R B A hRB hRo hAo
    have hA0 : A.filter (atO o) = [] := List.filter_eq_nil_iff.2 (fun a ha => by simp [hAo a ha])
    rw [List.filter_append, liftCs, filter_atO_map _ (liftA_iff o), hA0, List.append_nil]
    refine List.Perm.map _ ?_
    have := hRB.filter (atO o)
    have hR0 : R.filter (atO o) = [] := List.filter_eq_nil_iff.2 (fun r hr => by simp [hRo r hr])
    rw [List.filter_append, hR0, List.nil_append] at this
    exact this.symm
  change (cs.filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map (liftA 1)))
  rcases hsh with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hP, he₁, he₂, hn₁, hn₂, hX, -, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hP, he₁, hn₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hP, he, hcr, -, hpq, hps, hn, rfl⟩
  · have hr₁ := hP.symm.subset (by simp : r₁ ∈ [r₁, r₂] ++ B)
    have hr₂ := hP.symm.subset (by simp : r₂ ∈ [r₁, r₂] ++ B)
    refine key [r₁, r₂] B _ hP ?_ ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR _ hr₁ (Kind.isRandom_of_isSolid he₁.1)
      · exact hR _ hr₂ (Kind.isRandom_of_isSolid he₂.1)
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl) | ha
      · exact hsx
      · exact hnew _ _ _ (hedge _ _ hr₁ he₁) hn₁
      · exact hnew _ _ _ (hedge _ _ hr₂ he₂) hn₂
      · obtain ⟨ch, rfl⟩ := hX a ha
        simp [atO, mkC, hxo]
  · have hr₁ := hP.symm.subset (by simp : r₁ ∈ [r₁] ++ B)
    have hbo : atO o b = false := hnew _ _ _ hxo' hb
    have ha₁ : atO o a₁ = false := hnew _ _ _ (hedge _ _ hr₁ he₁) hn₁
    have hRo : ∀ r ∈ [r₁], atO o r = false := by
      intro r hr
      rw [List.mem_singleton.1 hr]
      exact hR _ hr₁ (Kind.isRandom_of_isSolid he₁.1)
    rcases hcs with rfl | rfl
    · refine key [r₁] B _ hP hRo ?_
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hsx
      · exact ha₁
      · exact hbo
    · refine key [r₁] B _ hP hRo ?_
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hsx
      · exact hbo
      · exact ha₁
  · refine key [] h.comps _ (by simp) (by simp) ?_
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hsx
    · simp [atO, mkC, hno]
  · have hr := hP.symm.subset (by simp : r ∈ [r, c] ++ B)
    have hc := hP.symm.subset (by simp : c ∈ [r, c] ++ B)
    have hco : atO o c = false := hR _ hc hcr
    have hco' : atO o (c.map (liftA 1)) = false := (atO_map (liftA_iff o) _).trans hco
    have hpo : p ≠ .inl o := by rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hqo : q ≠ .inl o := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hps' := dPieces_atO hps hpo hqo hco'
    refine key [r, c] B _ hP ?_ ?_
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hR _ hr (Kind.isRandom_of_isSolid he.1)
      · exact hco
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact hps' a ha
      · exact hsx
      · exact hnew _ _ _ (hedge _ _ hr he) hn

theorem filter_conjC {m : ℕ} {o : Fin k} (L : List (Comp (Atom k m))) :
    (L.map conjC).filter (atO o) = (L.filter (atO o)).map conjC := by
  rw [List.filter_map]
  rfl

/-- The terms of the complex conjugate of an identity applied to `h.conj`. -/
theorem conj_oout {o : Fin k} {h : Graph k n} {E : TExpansion k n}
    (hE : ∀ s ∈ E, OOut o h.conj s) : ∀ s ∈ E.conj, OOut o h s := by
  intro s hs
  obtain ⟨s₀, hs₀, rfl⟩ := mem_TExpansion_conj.1 hs
  have h0 := hE s₀ hs₀
  change ((s₀.g.conj.comps).filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map s₀.f))
  change (s₀.g.comps.filter (atO o)).Perm ((h.conj.comps.filter (atO o)).map (Comp.map s₀.f)) at h0
  rw [Graph.conj_comps'] at h0 ⊢
  rw [filter_conjC] at h0 ⊢
  refine (List.Perm.map conjC h0).trans (List.Perm.of_eq ?_)
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply]
  rw [conjC_map, conjC_conjC]

/-- The random components of `h.conj` are not at `o` if those of `h` are not. -/
theorem conj_random {o : Fin k} {h : Graph k n}
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false) :
    ∀ c ∈ h.conj.comps, c.kind.isRandom = true → atO o c = false := by
  intro c hc hr
  rw [Graph.conj_comps'] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  refine hR d hd ?_
  have hk : ∀ κ : Kind, κ.conj.isRandom = κ.isRandom := by
    intro κ
    cases κ with
    | waved w => cases w <;> rfl
    | _ => rfl
  rw [← hk]
  exact hr

/-- The terms of one step inside `P_x` (`O^{(x),1}_weight`, [II, (4.23)], [II, (4.24)]) keep the
components at the external atoms. -/
theorem opTerms_oo1 {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g) :
    (∀ t ∈ pLiftT x g (oWeight1T x g.pCore), OO1 g t) ∧ (∀ t ∈ oWeightP2T x g, OO1 g t) ∧
    (∀ E, multiEHat x g.pCore = some E → ∀ t ∈ pLiftT x g E, OO1 g t) := by
  have hN := hS.nn
  have hlr := hN.plain.labRand
  have hid : ∀ o (u : Atom k n), (id u : Atom k n) = .inl o ↔ u = .inl o := fun _ _ => Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht o hO
    obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
    have hso := w1_oout (fun c hc hr => core_random hO hc hr) s hs
    have hs' := hs
    unfold oWeight1T at hs'
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs'
    exact pLift_oout hO hlr (fun u => hid o u) hso
  · intro t ht o hO
    have hR : ∀ c ∈ g.pCore.comps, c.kind.isRandom = true → atO o c = false :=
      fun c hc hr => core_random hO hc hr
    unfold oWeightP2T at ht
    rcases hE : oWeightP2Pos x g.pCore with _ | E
    · rw [hE] at ht
      dsimp only at ht
      rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E
      · rw [hE'] at ht
        dsimp only at ht
        rw [List.mem_singleton.1 ht]
        exact OOut.self o g
      · rw [hE'] at ht
        dsimp only at ht
        obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
        have hso := conj_oout (p2_oout hN.hx (conj_random hR) hE') s hs
        obtain ⟨s₀, hs₀, rfl⟩ := mem_TExpansion_conj.1 hs
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := mem_oWeightP2Pos hE' hs₀
        exact pLift_oout hO hlr (fun u => liftA_iff o u) hso
    · rw [hE] at ht
      dsimp only at ht
      obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
      have hso := p2_oout hN.hx hR hE s hs
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := mem_oWeightP2Pos hE hs
      exact pLift_oout hO hlr (fun u => liftA_iff o u) hso
  · intro E hE t ht o hO
    have hR : ∀ c ∈ g.pCore.comps, c.kind.isRandom = true → atO o c = false :=
      fun c hc hr => core_random hO hc hr
    obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
    rcases me_oout hN.hx (noLoop_core hS) hR hE s hs with ⟨c, hc, hl⟩ | hso
    · exfalso
      have := List.any_eq_false.1 hq c hc
      simp [hl] at this
    · rcases shapes_multiEHat (noLoop_core hS) hE s hs with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, -⟩
      · exfalso
        have := List.any_eq_false.1 hq c hc
        simp [hl] at this
      · exact pLift_oout hO hlr (fun u => liftA_iff o u) hso

end OTerms


section OSteps

variable {k : ℕ}

/-- Replacing a component that is not diffusive by a component at an external atom only if the
replaced one is keeps the components at the external atoms. -/
theorem PStepsOK1.set {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false) (c' : Comp (Atom k n))
    (hc' : ∀ o : Fin k, atO o c' = true → atO o c = true) (co : Coeff) :
    PStepsOK1 Γ ⟨T.comps.set i c', co⟩ := by
  intro o hO
  have hi : i < T.comps.length := (List.getElem?_eq_some_iff.1 hc).1
  have hp₁ : (T.comps.set i c').Perm (c' :: T.comps.eraseIdx i) := by
    have h1 : (T.comps.set i c')[i]? = some c' := by simp [hi]
    have := perm_cons_eraseIdx h1
    rwa [List.eraseIdx_set_eq] at this
  have hco : atO o c = false := (h o hO).atO_false hO (List.mem_of_getElem? hc) hcd
  have hco' : atO o c' = false := by
    cases e : atO o c'
    · rfl
    · rw [hc' o e] at hco
      cases hco
  change ((T.comps.set i c').filter (atO o)).Perm _
  refine (hp₁.filter _).trans ?_
  rw [List.filter_cons_of_neg (by simp [hco'])]
  exact (h o hO).erase hc hco T.coeff

/-- A component that is not diffusive of a graph with only diffusive components at `o` has no end
at `o`. -/
theorem ends_off {n : ℕ} {o : Fin k} {g : Graph k n} (hO : ODiff o g)
    {c : Comp (Atom k n)} (hc : c ∈ g.comps) (hd : c.kind.isDiffusive = false) :
    c.x ≠ .inl o ∧ c.y ≠ .inl o := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hO c hc (Or.inl h)] at hd
    cases hd
  · rw [hO c hc (Or.inr h)] at hd
    cases hd

theorem OOut.of_keep {n : ℕ} {o : Fin k} {g g₁ : Graph k n} {s : Tracked k n}
    (h : OOut o g₁ s) (hk : OKeep o g g₁) : OOut o g s :=
  h.trans (List.Perm.map _ hk)

end OSteps


section ORebase

variable {k n : ℕ}

end ORebase

section ORebaseAll

variable {k n : ℕ}

end ORebaseAll

section OIdentify

variable {k n : ℕ}

end OIdentify

section ONormalize

variable {k : ℕ}

end ONormalize

section OInit

variable {k n : ℕ}

end OInit

section ORound

variable {k : ℕ}

end ORound

end RBM8D.Graphs
