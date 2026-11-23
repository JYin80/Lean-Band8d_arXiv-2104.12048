module

public import RBM8D.Graph.MolMerge
public import RBM8D.Graph.Standard

@[expose] public section

/-!
# Splitting an edge through a molecule

[II, Lemma 5.10 (B)], [II, Lemma 5.12], and the failure of [II, Lemma 5.10] at a dotted edge to `⊖`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

variable {V E : Type}

/-! ## Comparing molecular graphs -/

/-- Two pairs of vertices are equal up to order. -/
def SameEnds (p q : V × V) : Prop := p = q ∨ p = q.swap

/-- The edge `x` is present, has internal ends and is not a loop. -/
private def MGraph.Pres (X : MGraph V E) (x : E) : Prop :=
  X.cls x ≠ none ∧ (X.ends x).1 ∈ X.int ∧ (X.ends x).2 ∈ X.int ∧ (X.ends x).1 ≠ (X.ends x).2

/-- The graph `Y` contains the edges of `X` relabelled by `σ`: same internal vertices, and every
present edge of `X` with internal ends that is not a loop is, after relabelling, an edge of `Y` with
the same ends (up to order) and the same class, or a `Θ` edge if it is a blue solid edge of `X`. -/
private def LeS (σ : E → E) (X Y : MGraph V E) : Prop :=
  X.int = Y.int ∧ ∀ x, X.Pres x →
    (Y.cls (σ x) = X.cls x ∨ (X.cls x = some .plus ∧ Y.cls (σ x) = some .diff)) ∧
      SameEnds (Y.ends (σ x)) (X.ends x)

private theorem sameEnds_refl (p : V × V) : SameEnds p p := Or.inl rfl

private theorem sameEnds_swap (p : V × V) : SameEnds p.swap p := Or.inr rfl

private theorem SameEnds.symm {p q : V × V} (h : SameEnds p q) : SameEnds q p := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Prod.swap_swap _).symm

private theorem SameEnds.trans {p q r : V × V} (h : SameEnds p q) (h' : SameEnds q r) : SameEnds p r := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (Prod.swap_swap _)

/-- Same ends up to order: the two ends are each other's, or swapped. -/
private theorem sameEnds_iff {p q : V × V} : SameEnds p q ↔
    (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp [SameEnds, Prod.swap]

private theorem SameEnds.mem {p q : V × V} {S : Finset V} (h : SameEnds p q) :
    (p.1 ∈ S ∧ p.2 ∈ S) ↔ (q.1 ∈ S ∧ q.2 ∈ S) := by
  rcases sameEnds_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

private theorem SameEnds.ne {p q : V × V} (h : SameEnds p q) : p.1 ≠ p.2 ↔ q.1 ≠ q.2 := by
  rcases sameEnds_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact ne_comm

private theorem SameEnds.cut {p q : V × V} {S : Finset V} (h : SameEnds p q) :
    ((p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.1 ∉ S ∧ p.2 ∈ S)) ↔
      ((q.1 ∈ S ∧ q.2 ∉ S) ∨ (q.1 ∉ S ∧ q.2 ∈ S)) := by
  rcases sameEnds_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

/-- A doubly connected graph keeps the property in every graph containing its edges. -/
private theorem dc_leS {σ : E → E} (hσ : Function.Injective σ) {X Y : MGraph V E} (hX : X.DC)
    (h : LeS σ X Y) : Y.DC := by
  classical
  obtain ⟨hint, hle⟩ := h
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hX
  refine ⟨(K.filter X.Pres).image σ, (L.filter X.Pres).image σ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨x', hx', hxx⟩ := Finset.mem_image.1 hy'
    rw [hσ hxx] at hx'
    exact Finset.disjoint_left.1 hd (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hxK, hxP⟩ := Finset.mem_filter.1 hx
    rcases (hle x hxP).1 with h | ⟨h, -⟩
    · rw [h]; exact hK x hxK
    · rw [hK x hxK] at h; cases h
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hxL, hxP⟩ := Finset.mem_filter.1 hx
    rcases (hle x hxP).1 with h | ⟨-, h⟩
    · rw [h]; exact hL x hxL
    · exact Or.inl h
  all_goals
    intro S h1 h2 h3
    rw [← hint] at h1 h3
  · obtain ⟨x, hx, hc, hx1, hx2, hcut⟩ := hsK S h1 h2 h3
    have hP : X.Pres x := ⟨hc, hx1, hx2, fun h => by
      simp only [MGraph.Cut, h] at hcut; tauto⟩
    obtain ⟨hcl, hse⟩ := hle x hP
    refine ⟨σ x, Finset.mem_image_of_mem σ (Finset.mem_filter.2 ⟨hx, hP⟩), ?_, ?_, ?_, ?_⟩
    · rcases hcl with h | ⟨-, h⟩ <;> rw [h]
      · exact hc
      · simp
    · rw [← hint]; exact ((hse.mem (S := X.int)).2 ⟨hx1, hx2⟩).1
    · rw [← hint]; exact ((hse.mem (S := X.int)).2 ⟨hx1, hx2⟩).2
    · exact (hse.cut (S := S)).2 hcut
  · obtain ⟨x, hx, hc, hx1, hx2, hcut⟩ := hsL S h1 h2 h3
    have hP : X.Pres x := ⟨hc, hx1, hx2, fun h => by
      simp only [MGraph.Cut, h] at hcut; tauto⟩
    obtain ⟨hcl, hse⟩ := hle x hP
    refine ⟨σ x, Finset.mem_image_of_mem σ (Finset.mem_filter.2 ⟨hx, hP⟩), ?_, ?_, ?_, ?_⟩
    · rcases hcl with h | ⟨-, h⟩ <;> rw [h]
      · exact hc
      · simp
    · rw [← hint]; exact ((hse.mem (S := X.int)).2 ⟨hx1, hx2⟩).1
    · rw [← hint]; exact ((hse.mem (S := X.int)).2 ⟨hx1, hx2⟩).2
    · exact (hse.cut (S := S)).2 hcut

/-- The graph `Y` contains the edges of `X` (no relabelling). -/
private abbrev Le (X Y : MGraph V E) : Prop := LeS id X Y

private theorem dc_le {X Y : MGraph V E} (hX : X.DC) (h : Le X Y) : Y.DC :=
  dc_leS (σ := id) Function.injective_id hX h

/-- The classes after changing blue solid edges into `Θ` edges. -/
private theorem convert_cls [DecidableEq E] (X : MGraph V E) (l : List E) (x : E) :
    (X.convert l).cls x = if x ∈ l ∧ X.cls x = some .plus then some .diff else X.cls x := rfl

private theorem convert_ends [DecidableEq E] (X : MGraph V E) (l : List E) :
    (X.convert l).ends = X.ends := rfl

private theorem convert_int [DecidableEq E] (X : MGraph V E) (l : List E) :
    (X.convert l).int = X.int := rfl

private theorem erase_cls [DecidableEq E] (X : MGraph V E) (y x : E) :
    (X.erase y).cls x = if x = y then none else X.cls x := by
  by_cases h : x = y
  · subst h; simp [MGraph.erase]
  · simp [MGraph.erase, h]

private theorem erase_ends [DecidableEq E] (X : MGraph V E) (y : E) : (X.erase y).ends = X.ends := rfl

private theorem erase_int [DecidableEq E] (X : MGraph V E) (y : E) : (X.erase y).int = X.int := rfl

/-- A graph is contained in the graph with some blue solid edges changed into `Θ` edges. -/
private theorem le_convert [DecidableEq E] (X : MGraph V E) (l : List E) : Le X (X.convert l) := by
  refine ⟨rfl, fun x _ => ⟨?_, sameEnds_refl _⟩⟩
  change (X.convert l).cls x = X.cls x ∨ (X.cls x = some .plus ∧ (X.convert l).cls x = some .diff)
  rw [convert_cls]
  split_ifs with h
  · exact Or.inr ⟨h.2, rfl⟩
  · exact Or.inl rfl

private theorem convert_ne_none [DecidableEq E] {X : MGraph V E} {l : List E} {x : E} :
    (X.convert l).cls x ≠ none ↔ X.cls x ≠ none := by
  rw [convert_cls]
  split_ifs with h
  · rw [h.2]; simp
  · exact Iff.rfl

private theorem convert_append_ne [DecidableEq E] (X : MGraph V E) (l : List E) {x y : E} (h : x ≠ y) :
    (X.convert (l ++ [y])).cls x = (X.convert l).cls x := by
  rw [convert_cls, convert_cls]
  simp [h]

private theorem convert_erase_convert [DecidableEq E] (X : MGraph V E) (l₁ l₂ : List E) (y : E) :
    ((X.convert l₁).erase y).convert l₂ = (X.convert (l₁ ++ y :: l₂)).erase y := by
  unfold MGraph.convert MGraph.erase
  congr 1
  funext f
  by_cases hf : f = y
  · subst hf; simp
  · by_cases h1 : f ∈ l₁ <;> by_cases h2 : f ∈ l₂ <;> by_cases hp : X.cls f = some .plus <;>
      simp [hf, h1, h2, hp]

private theorem pres_convert [DecidableEq E] {X : MGraph V E} {l : List E} {x : E} :
    (X.convert l).Pres x ↔ X.Pres x := by
  unfold MGraph.Pres
  rw [convert_cls, convert_ends, convert_int]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 ?_, h2⟩
    rw [h]; simp
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 ?_, h2⟩
    split_ifs at h with h'
    exact h

/-- Containment is kept when the same blue solid edges are changed into `Θ` edges, if the
relabelling fixes the blue solid edges. -/
private theorem leS_convert [DecidableEq E] {σ : E → E} {X Y : MGraph V E} (h : LeS σ X Y)
    (hσ : ∀ x, X.Pres x → X.cls x = some .plus → σ x = x) (l : List E) :
    LeS σ (X.convert l) (Y.convert l) := by
  obtain ⟨hint, hle⟩ := h
  refine ⟨hint, fun x hx => ?_⟩
  have hx' := pres_convert.1 hx
  obtain ⟨hcl, hse⟩ := hle x hx'
  refine ⟨?_, hse⟩
  rw [convert_cls, convert_cls]
  by_cases hp : X.cls x = some .plus
  · rw [hσ x hx' hp] at hcl ⊢
    rcases hcl with h | ⟨-, h⟩
    · rw [h]
      by_cases hl : x ∈ l
      · simp [hl, hp]
      · simp [hl, hp]
    · rw [h]
      by_cases hl : x ∈ l
      · simp [hl, hp]
      · simp [hl, hp]
  · rcases hcl with h | ⟨h, -⟩
    · rw [h]; simp [hp]
    · exact absurd h hp

/-- Containment is kept when the same edge is removed, if the relabelling fixes it. -/
private theorem leS_erase [DecidableEq E] {σ : E → E} {X Y : MGraph V E} (h : LeS σ X Y)
    (hσi : Function.Injective σ) (y : E) (hy : σ y = y) :
    LeS σ (X.erase y) (Y.erase y) := by
  obtain ⟨hint, hle⟩ := h
  refine ⟨hint, fun x hx => ?_⟩
  have hxy : x ≠ y := by
    rintro rfl
    exact hx.1 (by rw [erase_cls]; simp)
  have hx' : X.Pres x := by
    obtain ⟨h1, h2⟩ := hx
    refine ⟨?_, h2⟩
    rw [erase_cls, if_neg hxy] at h1
    exact h1
  obtain ⟨hcl, hse⟩ := hle x hx'
  have hσx : σ x ≠ y := fun h => hxy (hσi (h.trans hy.symm))
  refine ⟨?_, hse⟩
  rw [erase_cls, erase_cls, if_neg hxy, if_neg hσx]
  exact hcl

/-- Redundancy is kept in a graph containing the edges, if the relabelling fixes the edge. -/
private theorem red_leS [DecidableEq E] {σ : E → E} (hσi : Function.Injective σ) {X Y : MGraph V E}
    {x : E} (h : X.IsRedundant x) (hle : LeS σ X Y) (hσ : σ x = x)
    (hY : Y.cls x = some .plus) : Y.IsRedundant x :=
  ⟨hY, dc_leS hσi h.2.1 hle, dc_leS hσi h.2.2 (leS_erase hle hσi x hσ)⟩

private theorem red_le [DecidableEq E] {X Y : MGraph V E} {x : E} (h : X.IsRedundant x) (hle : Le X Y)
    (hY : Y.cls x = some .plus) : Y.IsRedundant x :=
  red_leS (σ := id) Function.injective_id h hle rfl hY

/-- Containment is transitive. -/
private theorem le_trans' {X Y Z : MGraph V E} (h₁ : Le X Y) (h₂ : Le Y Z) : Le X Z := by
  obtain ⟨i1, l1⟩ := h₁
  obtain ⟨i2, l2⟩ := h₂
  refine ⟨i1.trans i2, fun x hx => ?_⟩
  obtain ⟨c1, s1⟩ := l1 x hx
  have hy : Y.Pres x := by
    refine ⟨?_, ?_⟩
    · rcases c1 with h | ⟨-, h⟩ <;> simp only [id] at h <;> rw [h]
      · exact hx.1
      · simp
    · have hm := s1.mem (S := Y.int)
      have hn := s1.ne
      simp only [id] at hm hn
      rw [← i1] at hm ⊢
      exact ⟨(hm.2 ⟨hx.2.1, hx.2.2.1⟩).1, (hm.2 ⟨hx.2.1, hx.2.2.1⟩).2, hn.2 hx.2.2.2⟩
  obtain ⟨c2, s2⟩ := l2 x hy
  simp only [id] at c1 c2 s1 s2 ⊢
  refine ⟨?_, s2.trans s1⟩
  rcases c1 with h | ⟨h1, h⟩ <;> rcases c2 with h' | ⟨h1', h'⟩
  · exact Or.inl (h'.trans h)
  · rw [h] at h1'; exact Or.inr ⟨h1', h'⟩
  · rw [h'.trans h]; exact Or.inr ⟨h1, rfl⟩
  · rw [h] at h1'; cases h1'

/-! ## Redundancy steps -/

/-- The redundancy steps of a list of edges. -/
private def Steps [DecidableEq E] (X : MGraph V E) (l : List E) : Prop :=
  ∀ (t : ℕ) (ht : t < l.length), (X.convert (l.take t)).IsRedundant l[t]

private theorem convert_convert' [DecidableEq E] (X : MGraph V E) (l₁ l₂ : List E) :
    (X.convert l₁).convert l₂ = X.convert (l₁ ++ l₂) := by
  unfold MGraph.convert
  congr 1
  funext e
  by_cases h1 : e ∈ l₁ <;> by_cases h2 : e ∈ l₂ <;> by_cases hp : X.cls e = some .plus <;>
    simp [h1, h2, hp]

private theorem convert_nil' [DecidableEq E] (X : MGraph V E) : X.convert [] = X := by
  unfold MGraph.convert
  simp

/-- Changing the same blue solid edges gives the same graph. -/
private theorem convert_congr [DecidableEq E] (X : MGraph V E) {l₁ l₂ : List E}
    (h : ∀ x, X.cls x = some .plus → (x ∈ l₁ ↔ x ∈ l₂)) : X.convert l₁ = X.convert l₂ := by
  unfold MGraph.convert
  congr 1
  funext e
  by_cases hp : X.cls e = some .plus
  · simp [hp, h e hp]
  · simp [hp]

private theorem steps_nil [DecidableEq E] (X : MGraph V E) : Steps X [] := fun t ht => absurd ht (by simp)

private theorem steps_cons [DecidableEq E] {X : MGraph V E} {y : E} {l : List E} :
    Steps X (y :: l) ↔ X.IsRedundant y ∧ Steps (X.convert [y]) l := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    rw [List.take_zero, convert_nil'] at h0
    refine ⟨h0, fun t ht => ?_⟩
    have := h (t + 1) (by simp; omega)
    simpa [convert_convert'] using this
  · rintro ⟨h0, h⟩ t ht
    rcases t with _ | t
    · simpa [convert_nil'] using h0
    · have := h t (by simp at ht; omega)
      simpa [convert_convert'] using this

private theorem steps_append [DecidableEq E] {X : MGraph V E} {l₁ l₂ : List E} :
    Steps X (l₁ ++ l₂) ↔ Steps X l₁ ∧ Steps (X.convert l₁) l₂ := by
  induction l₁ generalizing X with
  | nil => simp [steps_nil, convert_nil']
  | cons y l ih =>
    rw [List.cons_append, steps_cons, steps_cons, ih, convert_convert']
    simp [and_assoc]

private theorem steps_single [DecidableEq E] {X : MGraph V E} {y : E} :
    Steps X [y] ↔ X.IsRedundant y := by
  rw [steps_cons]
  simp [steps_nil]

/-- The edges of the steps are blue solid edges. -/
private theorem steps_plus [DecidableEq E] {X : MGraph V E} {l : List E} (h : Steps X l) :
    ∀ y ∈ l, X.cls y = some .plus := by
  induction l generalizing X with
  | nil => simp
  | cons z l ih =>
    rw [steps_cons] at h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1.1
    · have := ih h.2 y hy
      rw [convert_cls] at this
      by_cases h' : y ∈ [z] ∧ X.cls y = some .plus
      · exact h'.2
      · rw [if_neg h'] at this; exact this

/-- The edges of the steps are distinct. -/
private theorem steps_nodup [DecidableEq E] {X : MGraph V E} {l : List E} (h : Steps X l) : l.Nodup := by
  induction l generalizing X with
  | nil => simp
  | cons z l ih =>
    rw [steps_cons] at h
    refine List.nodup_cons.2 ⟨fun hz => ?_, ih h.2⟩
    have := steps_plus h.2 z hz
    rw [convert_cls, if_pos ⟨List.mem_singleton_self _, h.1.1⟩] at this
    cases this

/-- Redundancy is kept when more blue solid edges are changed into `Θ` edges. -/
private theorem red_convert [DecidableEq E] {X : MGraph V E} {y : E} (h : X.IsRedundant y) {m : List E}
    (hm : y ∉ m) : (X.convert m).IsRedundant y := by
  refine ⟨by rw [convert_cls, if_neg (fun h' => hm h'.1)]; exact h.1,
    MGraph.DC_convert _ _ _ _ h.2.1, ?_⟩
  have : (X.convert m).erase y = (X.erase y).convert m := by
    unfold MGraph.erase MGraph.convert
    congr 1
    funext e
    by_cases he : e = y
    · subst he; simp
    · simp [he]
  rw [this]
  exact MGraph.DC_convert _ _ _ _ h.2.2

/-- The steps of a list, with the edges in `m` changed beforehand and removed from the list. -/
private theorem steps_filter [DecidableEq E] {X : MGraph V E} {l : List E} (h : Steps X l)
    (p : E → Prop) [DecidablePred p] {m : List E} (hm1 : ∀ y ∈ l, ¬ p y → y ∈ m)
    (hm2 : ∀ y ∈ l, p y → y ∉ m) : Steps (X.convert m) (l.filter (fun y => p y)) := by
  induction l generalizing X with
  | nil => simp [steps_nil]
  | cons z l ih =>
    rw [steps_cons] at h
    have hcomm : (X.convert m).convert [z] = (X.convert [z]).convert m := by
      rw [convert_convert', convert_convert']
      exact convert_congr _ (fun x _ => by simp [or_comm])
    by_cases hz : p z
    · rw [List.filter_cons_of_pos (by simpa using hz), steps_cons]
      refine ⟨red_convert h.1 (hm2 z (List.mem_cons_self) hz), ?_⟩
      rw [hcomm]
      exact ih h.2 (fun y hy => hm1 y (List.mem_cons_of_mem _ hy))
        (fun y hy => hm2 y (List.mem_cons_of_mem _ hy))
    · rw [List.filter_cons_of_neg (by simpa using hz)]
      have hzm := hm1 z List.mem_cons_self hz
      have := ih h.2 (fun y hy => hm1 y (List.mem_cons_of_mem _ hy))
        (fun y hy => hm2 y (List.mem_cons_of_mem _ hy))
      rwa [convert_convert', convert_congr X (l₂ := m) (fun x _ => by
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (rfl | h); exacts [hzm, h]
        · exact Or.inr)] at this

/-- A pre-deterministic graph from a doubly connected graph and the redundancy steps of a list of
all its internal blue solid edges. -/
private theorem preDet_of_steps [DecidableEq E] {X : MGraph V E} {l : List E} (hX : X.DC)
    (h : Steps X l) (hmem : ∀ x, x ∈ l ↔ X.IsIntPlus x) : X.PreDet :=
  ⟨hX, l, steps_nodup h, hmem, h⟩

/-- A pre-deterministic graph stays pre-deterministic when blue solid edges are changed into `Θ`
edges. -/
private theorem preDet_convert [DecidableEq E] {X : MGraph V E} (h : X.PreDet) (m : List E) :
    (X.convert m).PreDet := by
  classical
  obtain ⟨hdc, l, -, hmem, hst⟩ := h
  refine preDet_of_steps (MGraph.DC_convert _ _ _ _ hdc)
    (steps_filter hst (fun y => y ∉ m) (fun y _ h => not_not.1 h) (fun y _ h => h)) ?_
  intro x
  rw [List.mem_filter, hmem]
  unfold MGraph.IsIntPlus
  rw [convert_cls, convert_ends, convert_int]
  by_cases hx : x ∈ m
  · simp only [hx, not_true_eq_false, decide_false, Bool.false_eq_true, and_false, false_iff]
    rintro ⟨h1, -⟩
    by_cases h' : X.cls x = some .plus
    · simp [h'] at h1
    · simp [h'] at h1
  · simp [hx]

/-- A pre-deterministic graph from the steps of a list of internal blue solid edges and the
pre-deterministic property after they are changed into `Θ` edges. -/
private theorem preDet_prefix [DecidableEq E] {X : MGraph V E} {p : List E} (hp : Steps X p)
    (hpi : ∀ y ∈ p, X.IsIntPlus y) (hX : X.DC) (h : (X.convert p).PreDet) : X.PreDet := by
  obtain ⟨-, l, -, hmem, hst⟩ := h
  refine preDet_of_steps hX (steps_append.2 ⟨hp, hst⟩) fun x => ?_
  rw [List.mem_append, hmem]
  unfold MGraph.IsIntPlus
  rw [convert_cls, convert_ends, convert_int]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact hpi x h
    · by_cases h' : x ∈ p ∧ X.cls x = some .plus
      · rw [if_pos h'] at h1; cases h1
      · rw [if_neg h'] at h1; exact ⟨h1, h2⟩
  · intro hx
    by_cases hxp : x ∈ p
    · exact Or.inl hxp
    · exact Or.inr (by rw [if_neg (fun h => hxp h.1)]; exact hx)

/-- Steps transfer to a graph containing the edges, with the same internal blue solid edges. -/
private theorem steps_transfer [DecidableEq E] {σ : E → E} (hσi : Function.Injective σ) :
    ∀ {X Y : MGraph V E} {l : List E}, Steps X l → LeS σ X Y →
      (∀ x, X.cls x = some .plus → σ x = x) → (∀ x, X.IsIntPlus x ↔ Y.IsIntPlus x) →
      (∀ y ∈ l, X.IsIntPlus y) → Steps Y l := by
  intro X Y l
  induction l generalizing X Y with
  | nil => intros; exact steps_nil _
  | cons y l ih =>
    intro h hle hσ hip hl
    rw [steps_cons] at h ⊢
    have hy := hl y List.mem_cons_self
    refine ⟨red_leS hσi h.1 hle (hσ y hy.1) ((hip y).1 hy).1, ?_⟩
    refine ih h.2 (leS_convert hle (fun x _ hx => hσ x hx) [y]) (fun x hx => ?_) (fun x => ?_)
      (fun z hz => ?_)
    · rw [convert_cls] at hx
      by_cases h' : x ∈ [y] ∧ X.cls x = some .plus
      · exact hσ x h'.2
      · rw [if_neg h'] at hx; exact hσ x hx
    · unfold MGraph.IsIntPlus
      rw [convert_cls, convert_cls, convert_ends, convert_ends, convert_int, convert_int]
      have := hip x
      unfold MGraph.IsIntPlus at this
      by_cases hx : x = y
      · subst hx
        simp only [List.mem_singleton, true_and]
        constructor
        · rintro ⟨h1, -⟩; split_ifs at h1 <;> simp_all
        · rintro ⟨h1, -⟩; split_ifs at h1 <;> simp_all
      · simp only [List.mem_singleton, hx, false_and, if_false]
        exact this
    · have hz' := hl z (List.mem_cons_of_mem _ hz)
      have hzy : z ≠ y := by
        rintro rfl
        exact (List.nodup_cons.1 (steps_nodup (steps_cons.2 h))).1 hz
      unfold MGraph.IsIntPlus
      rw [convert_cls, if_neg (by simp [hzy])]
      exact hz'

/-- The pre-deterministic property transfers to a graph containing the edges, with the same
internal blue solid edges. -/
private theorem preDet_transfer [DecidableEq E] {σ : E → E} (hσi : Function.Injective σ)
    {X Y : MGraph V E} (h : X.PreDet) (hle : LeS σ X Y) (hσ : ∀ x, X.cls x = some .plus → σ x = x)
    (hip : ∀ x, X.IsIntPlus x ↔ Y.IsIntPlus x) : Y.PreDet := by
  obtain ⟨hdc, l, -, hmem, hst⟩ := h
  exact preDet_of_steps (dc_leS hσi hdc hle)
    (steps_transfer hσi hst hle hσ hip (fun y hy => (hmem y).1 hy)) fun x => (hmem x).trans (hip x)

/-- An edge that is absent, has an end outside the internal vertices or is a loop can be removed
without changing the edges compared. -/
private theorem le_erase_of_not_pres [DecidableEq E] {X : MGraph V E} {y : E} (hy : ¬ X.Pres y) :
    Le X (X.erase y) := by
  refine ⟨rfl, fun x hx => ⟨Or.inl ?_, sameEnds_refl _⟩⟩
  have hxy : x ≠ y := by rintro rfl; exact hy hx
  simp only [id]
  rw [erase_cls, if_neg hxy]

/-- The edges of a graph without blue solid edges, contained in `X`, are kept when blue solid edges
of `X` are changed into `Θ` edges or removed. -/
private theorem le_convert_erase [DecidableEq E] {Z X : MGraph V E} (hle : Le Z X)
    (hZ : ∀ f, Z.Pres f → Z.cls f ≠ some .plus) (p : List E) {y : E}
    (hy : X.cls y = some .plus) : Le Z (X.convert p) ∧ Le Z ((X.convert p).erase y) := by
  obtain ⟨hint, hl⟩ := hle
  have key : ∀ f, Z.Pres f → X.cls f = Z.cls f := fun f hf => by
    rcases (hl f hf).1 with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hZ f hf)
  refine ⟨⟨hint, fun f hf => ⟨Or.inl ?_, (hl f hf).2⟩⟩, ⟨hint, fun f hf => ⟨Or.inl ?_, (hl f hf).2⟩⟩⟩
  · simp only [id]
    rw [convert_cls, key f hf, if_neg (fun h => hZ f hf h.2)]
  · have hfy : f ≠ y := by
      rintro rfl
      exact hZ f hf ((key f hf).symm.trans hy)
    simp only [id]
    rw [erase_cls, if_neg hfy, convert_cls, key f hf, if_neg (fun h => hZ f hf h.2)]

/-- A graph containing a doubly connected graph without blue solid edges is pre-deterministic, if
its internal blue solid edges lie in a list. -/
private theorem preDet_of_base [DecidableEq E] {Z X : MGraph V E} (hZ : Z.DC) (hle : Le Z X)
    (hZp : ∀ f, Z.Pres f → Z.cls f ≠ some .plus) {m : List E}
    (hm : ∀ x, X.IsIntPlus x → x ∈ m) : X.PreDet := by
  classical
  have key : ∀ l : List E, l.Nodup → (∀ y ∈ l, X.IsIntPlus y) → ∀ p : List E,
      (∀ y ∈ l, y ∉ p) → Steps (X.convert p) l := by
    intro l
    induction l with
    | nil => intros; exact steps_nil _
    | cons y l ih =>
      intro hnd hl p hp
      rw [steps_cons, convert_convert']
      have hy := hl y List.mem_cons_self
      have hyp : (X.convert p).cls y = some .plus := by
        rw [convert_cls, if_neg (fun h => hp y List.mem_cons_self h.1)]; exact hy.1
      obtain ⟨h1, h2⟩ := le_convert_erase hle hZp p hy.1
      refine ⟨⟨hyp, dc_le hZ h1, dc_le hZ h2⟩, ih (List.nodup_cons.1 hnd).2
        (fun z hz => hl z (List.mem_cons_of_mem _ hz)) _ fun z hz hz' => ?_⟩
      · rcases List.mem_append.1 hz' with h | h
        · exact hp z (List.mem_cons_of_mem _ hz) h
        · rw [List.mem_singleton] at h
          subst h
          exact (List.nodup_cons.1 hnd).1 hz
  have hl := key ((m.filter (fun x => decide (X.IsIntPlus x))).dedup) (List.nodup_dedup _)
    (fun y hy => by simpa using (List.mem_filter.1 (List.mem_dedup.1 hy)).2) [] (by simp)
  rw [convert_nil'] at hl
  refine preDet_of_steps (dc_le hZ hle) hl fun x => ?_
  rw [List.mem_dedup, List.mem_filter]
  exact ⟨fun h => by simpa using h.2, fun h => ⟨hm x h, by simpa using h⟩⟩

/-! ## Quotient graphs ([II, Claim A.1]) -/

private theorem collapse_int [DecidableEq V] (X : MGraph V E) (S : Finset V) (s₀ : V) :
    (X.collapse S s₀).int = X.int.image (fun v => if v ∈ S then s₀ else v) := rfl

private theorem collapse_cls [DecidableEq V] (X : MGraph V E) (S : Finset V) (s₀ : V) :
    (X.collapse S s₀).cls = X.cls := rfl

private theorem collapse_ends [DecidableEq V] (X : MGraph V E) (S : Finset V) (s₀ : V) (x : E) :
    (X.collapse S s₀).ends x = (if (X.ends x).1 ∈ S then s₀ else (X.ends x).1,
      if (X.ends x).2 ∈ S then s₀ else (X.ends x).2) := rfl

private theorem collapse_convert [DecidableEq V] [DecidableEq E] (X : MGraph V E) (S : Finset V) (s₀ : V)
    (l : List E) : (X.convert l).collapse S s₀ = (X.collapse S s₀).convert l := rfl

private theorem collapse_erase [DecidableEq V] [DecidableEq E] (X : MGraph V E) (S : Finset V) (s₀ : V)
    (y : E) : (X.erase y).collapse S s₀ = (X.collapse S s₀).erase y := rfl

/-- The internal vertices of the quotient graph: `s₀` and the internal vertices outside `S`. -/
private theorem mem_collapse_int [DecidableEq V] {X : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ X.int) (hs : s₀ ∈ S) (v : V) :
    v ∈ (X.collapse S s₀).int ↔ v = s₀ ∨ (v ∈ X.int ∧ v ∉ S) := by
  rw [collapse_int, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_cases h : u ∈ S
    · simp [h]
    · simp [h, hu]
  · rintro (h | ⟨h1, h2⟩)
    · rw [h]; exact ⟨s₀, hS hs, by simp [hs]⟩
    · exact ⟨v, h1, by simp [h2]⟩

/-- The image of a vertex is internal in the quotient graph exactly when the vertex is internal. -/
private theorem image_mem_collapse_int [DecidableEq V] {X : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ X.int) (hs : s₀ ∈ S) (v : V) :
    (if v ∈ S then s₀ else v) ∈ (X.collapse S s₀).int ↔ v ∈ X.int := by
  rw [mem_collapse_int hS hs]
  by_cases h : v ∈ S
  · simp [h, hS h]
  · simp only [h, if_false, not_false_eq_true, and_true]
    constructor
    · rintro (rfl | h')
      · exact absurd hs h
      · exact h'
    · exact Or.inr

private theorem induce_convert' [DecidableEq V] [DecidableEq E] (X : MGraph V E) (S : Finset V)
    (l : List E) : (X.convert l).induce S = (X.induce S).convert l := by
  unfold MGraph.induce MGraph.convert
  congr 1
  funext e
  by_cases h : (X.ends e).1 ∈ S ∧ (X.ends e).2 ∈ S <;> simp [h]

private theorem induce_erase' [DecidableEq V] [DecidableEq E] (X : MGraph V E) (S : Finset V) (y : E) :
    (X.erase y).induce S = (X.induce S).erase y := by
  unfold MGraph.induce MGraph.erase
  congr 1
  funext e
  by_cases h : (X.ends e).1 ∈ S ∧ (X.ends e).2 ∈ S <;> by_cases he : e = y <;> simp [h, he]

private theorem induce_erase_out [DecidableEq V] [DecidableEq E] (X : MGraph V E) (S : Finset V) {y : E}
    (hy : ¬ ((X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S)) : (X.erase y).induce S = X.induce S := by
  unfold MGraph.induce MGraph.erase
  congr 1
  funext e
  by_cases h : (X.ends e).1 ∈ S ∧ (X.ends e).2 ∈ S
  · have : e ≠ y := by rintro rfl; exact hy h
    simp [h, this]
  · simp [h]

/-- An edge with both ends in `S` is a loop of the quotient graph. -/
private theorem not_pres_collapse [DecidableEq V] {X : MGraph V E} {S : Finset V} {s₀ : V} {y : E}
    (hy : (X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S) : ¬ (X.collapse S s₀).Pres y := by
  rintro ⟨-, -, -, h⟩
  rw [collapse_ends] at h
  simp [hy.1, hy.2] at h

/-- [II, Claim A.1]: the doubly connected property from the subgraph induced on `S` and the
quotient graph. -/
private theorem dc_glue [DecidableEq V] {X : MGraph V E} {S : Finset V} {s₀ : V} (hS : S ⊆ X.int)
    (hs : s₀ ∈ S) (hI : (X.induce S).DC) (hQ : (X.collapse S s₀).DC) : X.DC :=
  (MGraph.claimA1 V E X S s₀ hS hs hI).2 hQ

/-- Redundancy of an edge with both ends in `S` from its redundancy in the subgraph induced on
`S`. -/
private theorem red_lift [DecidableEq V] [DecidableEq E] {X : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ X.int) (hs : s₀ ∈ S) {x : E} (hx : (X.ends x).1 ∈ S ∧ (X.ends x).2 ∈ S)
    (hr : (X.induce S).IsRedundant x) (hQ : (X.collapse S s₀).DC) : X.IsRedundant x := by
  refine ⟨?_, dc_glue hS hs hr.2.1 hQ, ?_⟩
  · have := hr.1
    simp only [MGraph.induce, hx, and_self, if_true] at this
    exact this
  · refine dc_glue (X := X.erase x) hS hs (by rw [induce_erase']; exact hr.2.2) ?_
    rw [collapse_erase]
    exact dc_le hQ (le_erase_of_not_pres (not_pres_collapse hx))

/-- Redundancy of an edge not inside `S` from its redundancy in the quotient graph. -/
private theorem red_quot [DecidableEq V] [DecidableEq E] {X : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ X.int) (hs : s₀ ∈ S) {x : E} (hx : ¬ ((X.ends x).1 ∈ S ∧ (X.ends x).2 ∈ S))
    (hI : (X.induce S).DC) (hr : (X.collapse S s₀).IsRedundant x) : X.IsRedundant x := by
  refine ⟨hr.1, dc_glue hS hs hI hr.2.1, ?_⟩
  refine dc_glue (X := X.erase x) hS hs (by rw [induce_erase_out X S hx]; exact hI) ?_
  rw [collapse_erase]
  exact hr.2.2

private theorem steps_lift [DecidableEq V] [DecidableEq E] {S : Finset V} {s₀ : V} :
    ∀ {X : MGraph V E} {l : List E}, S ⊆ X.int → s₀ ∈ S →
      (∀ y ∈ l, (X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S) → Steps (X.induce S) l →
      (X.collapse S s₀).DC → Steps X l := by
  intro X l
  induction l generalizing X with
  | nil => intros; exact steps_nil _
  | cons y l ih =>
    intro hS hs hl h hQ
    rw [steps_cons] at h ⊢
    refine ⟨red_lift hS hs (hl y List.mem_cons_self) h.1 hQ, ih hS hs
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (by rw [induce_convert']; exact h.2) ?_⟩
    rw [collapse_convert]
    exact MGraph.DC_convert _ _ _ _ hQ

private theorem steps_quot [DecidableEq V] [DecidableEq E] {S : Finset V} {s₀ : V} :
    ∀ {X : MGraph V E} {l : List E}, S ⊆ X.int → s₀ ∈ S →
      (∀ y ∈ l, ¬ ((X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S)) → Steps (X.collapse S s₀) l →
      (X.induce S).DC → Steps X l := by
  intro X l
  induction l generalizing X with
  | nil => intros; exact steps_nil _
  | cons y l ih =>
    intro hS hs hl h hI
    rw [steps_cons] at h ⊢
    refine ⟨red_quot hS hs (hl y List.mem_cons_self) hI h.1, ih hS hs
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (by rw [collapse_convert]; exact h.2) ?_⟩
    rw [induce_convert']
    exact MGraph.DC_convert _ _ _ _ hI

/-- Internal blue solid edges of the quotient graph: those of the graph. -/
private theorem intPlus_collapse [DecidableEq V] {X : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ X.int) (hs : s₀ ∈ S) (x : E) :
    (X.collapse S s₀).IsIntPlus x ↔ X.IsIntPlus x := by
  unfold MGraph.IsIntPlus
  rw [collapse_cls, collapse_ends, image_mem_collapse_int hS hs, image_mem_collapse_int hS hs]

/-- [II, Claim A.1] for pre-deterministic graphs: if the subgraph induced on `S` and the quotient
graph are pre-deterministic, so is the graph. -/
private theorem preDet_glue [DecidableEq V] [DecidableEq E] {X : MGraph V E} {S : Finset V} {s₀ : V}
    (hS : S ⊆ X.int) (hs : s₀ ∈ S) (hI : (X.induce S).PreDet) (hQ : (X.collapse S s₀).PreDet) :
    X.PreDet := by
  classical
  obtain ⟨hIdc, lS, -, hmS, hstS⟩ := hI
  obtain ⟨hQdc, lQ, -, hmQ, hstQ⟩ := hQ
  have inS : ∀ y, (X.induce S).IsIntPlus y → (X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S := by
    intro y hy
    by_contra h
    have := hy.1
    simp [MGraph.induce, h] at this
  have ipS : ∀ y, (X.induce S).IsIntPlus y ↔ X.IsIntPlus y ∧ (X.ends y).1 ∈ S ∧
      (X.ends y).2 ∈ S := by
    intro y
    constructor
    · intro hy
      have h := inS y hy
      have := hy.1
      simp only [MGraph.induce, h, and_self, if_true] at this
      exact ⟨⟨this, hS h.1, hS h.2⟩, h⟩
    · rintro ⟨⟨h1, -, -⟩, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      simp only [MGraph.induce, h2, h3, and_self, if_true]
      exact h1
  refine preDet_of_steps (dc_glue hS hs hIdc hQdc)
    (l := lS ++ lQ.filter (fun y => ¬ ((X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S)))
    (steps_append.2 ⟨steps_lift hS hs (fun y hy => inS y ((hmS y).1 hy)) hstS hQdc, ?_⟩) ?_
  · have hI' : ((X.convert lS).induce S).DC := by
      rw [induce_convert']
      exact MGraph.DC_convert _ _ _ _ hIdc
    refine steps_quot (X := X.convert lS) hS hs
      (fun y hy => of_decide_eq_true (List.mem_filter.1 hy).2) ?_ hI'
    rw [collapse_convert]
    refine steps_filter hstQ _ (fun y hy h => ?_) (fun y _ h h' => h (inS y ((hmS y).1 h')))
    rw [not_not] at h
    exact (hmS y).2 ((ipS y).2 ⟨(intPlus_collapse hS hs y).1 ((hmQ y).1 hy), h⟩)
  · intro x
    rw [List.mem_append, List.mem_filter, hmS, hmQ, intPlus_collapse hS hs, ipS]
    by_cases h : (X.ends x).1 ∈ S ∧ (X.ends x).2 ∈ S
    · simp [h]
    · simp [h]

/-- The quotient graph of a pre-deterministic graph by a set `S` whose induced subgraph is doubly
connected is pre-deterministic. -/
private theorem preDet_quot [DecidableEq V] [DecidableEq E] {W : MGraph V E} {S : Finset V} {s₀ : V}
    (hW : W.PreDet) (hS : S ⊆ W.int) (hs : s₀ ∈ S) (hI : (W.induce S).DC) :
    (W.collapse S s₀).PreDet := by
  obtain ⟨hdc, l, -, hmem, hst⟩ := hW
  have key : ∀ (l : List E) (X : MGraph V E), S ⊆ X.int → Steps X l → (X.induce S).DC →
      Steps (X.collapse S s₀) l := by
    intro l
    induction l with
    | nil => intros; exact steps_nil _
    | cons y l ih =>
      intro X hS h hI'
      rw [steps_cons] at h ⊢
      refine ⟨⟨h.1.1, (MGraph.claimA1 V E X S s₀ hS hs hI').1 h.1.2.1, ?_⟩, ?_⟩
      · rw [← collapse_erase]
        by_cases hy : (X.ends y).1 ∈ S ∧ (X.ends y).2 ∈ S
        · rw [collapse_erase]
          exact dc_le ((MGraph.claimA1 V E X S s₀ hS hs hI').1 h.1.2.1)
            (le_erase_of_not_pres (not_pres_collapse hy))
        · exact (MGraph.claimA1 V E (X.erase y) S s₀ hS hs
            (by rw [induce_erase_out X S hy]; exact hI')).1 h.1.2.2
      · rw [← collapse_convert]
        refine ih _ (by rw [convert_int]; exact hS) h.2 ?_
        rw [induce_convert']
        exact MGraph.DC_convert _ _ _ _ hI'
  refine preDet_of_steps ((MGraph.claimA1 V E W S s₀ hS hs hI).1 hdc)
    (key l W hS hst hI) fun x => (hmem x).trans (intPlus_collapse hS hs x).symm

/-! ## Replacing an edge of the nets by a path -/

private theorem mem_ite_pair [DecidableEq E] {P : Prop} [Decidable P] {x a b : E} :
    x ∈ (if P then ({a, b} : Finset E) else ∅) ↔ P ∧ (x = a ∨ x = b) := by
  split_ifs with h <;> simp [h]

private theorem mem_ite_single [DecidableEq E] {P : Prop} [Decidable P] {x a : E} :
    x ∈ (if P then (∅ : Finset E) else {a}) ↔ ¬ P ∧ x = a := by
  split_ifs with h <;> simp [h]

/-- A spanning set of `R` gives a spanning set of `Z`, whose internal vertices are those of `R`
and `N`: an edge `g` of the set is replaced by the path `g₁`, `g₂` through `N`, the other edges are
kept, and `N` is joined to `R` by `y` if it is not a vertex of `R`. -/
private theorem spans_path [DecidableEq V] [DecidableEq E] {R Z : MGraph V E} {N : V}
    (hint : Z.int = insert N R.int)
    {B : Finset E} (hB : ∀ f ∈ B, R.Pres f) (hsp : R.Spans B) {g g₁ g₂ y : E} {m : V}
    (hZc : ∀ f ∈ B, f ≠ g → Z.cls f ≠ none ∧ SameEnds (Z.ends f) (R.ends f))
    (hg : g ∈ B → Z.cls g₁ ≠ none ∧ Z.cls g₂ ≠ none ∧ SameEnds (Z.ends g₁) ((R.ends g).1, N) ∧
      SameEnds (Z.ends g₂) (N, (R.ends g).2))
    (hy : N ∉ R.int → Z.cls y ≠ none ∧ SameEnds (Z.ends y) (N, m) ∧ m ∈ R.int) :
    Z.Spans (B.erase g ∪ (if g ∈ B then {g₁, g₂} else ∅) ∪ (if N ∈ R.int then ∅ else {y})) := by
  classical
  intro S hS hne hnot
  have hRZ : ∀ v, v ∈ R.int → v ∈ Z.int := fun v hv => by
    rw [hint]; exact Finset.mem_insert_of_mem hv
  have hNZ : N ∈ Z.int := by rw [hint]; exact Finset.mem_insert_self _ _
  have memB : ∀ x, x ∈ B.erase g ∪ (if g ∈ B then {g₁, g₂} else ∅) ∪
      (if N ∈ R.int then ∅ else {y}) ↔ (x ≠ g ∧ x ∈ B) ∨ (g ∈ B ∧ (x = g₁ ∨ x = g₂)) ∨
        (N ∉ R.int ∧ x = y) := by
    intro x
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_erase, mem_ite_pair, mem_ite_single]
    tauto
  -- an edge with ends `p` (internal in `Z`) and `q` (a vertex of `R`) cutting `S`
  have use : ∀ x (p q : V), (x ≠ g ∧ x ∈ B) ∨ (g ∈ B ∧ (x = g₁ ∨ x = g₂)) ∨
      (N ∉ R.int ∧ x = y) → Z.cls x ≠ none → SameEnds (Z.ends x) (p, q) → p ∈ Z.int →
      q ∈ Z.int → ((p ∈ S ∧ q ∉ S) ∨ (p ∉ S ∧ q ∈ S)) →
      ∃ e ∈ B.erase g ∪ (if g ∈ B then {g₁, g₂} else ∅) ∪ (if N ∈ R.int then ∅ else {y}),
        Z.cls e ≠ none ∧ (Z.ends e).1 ∈ Z.int ∧ (Z.ends e).2 ∈ Z.int ∧ Z.Cut S e := by
    intro x p q hx hc hse hp hq hcut
    have hm := (hse.mem (S := Z.int)).2 ⟨hp, hq⟩
    exact ⟨x, (memB x).2 hx, hc, hm.1, hm.2, (hse.cut (S := S)).2 hcut⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset V, T = S.filter (· ∈ R.int) := ⟨_, rfl⟩
  have memT : ∀ v, v ∈ T ↔ v ∈ S ∧ v ∈ R.int := fun v => by rw [hT, Finset.mem_filter]
  have hTsub : T ⊆ R.int := fun v hv => ((memT v).1 hv).2
  by_cases hTne : T.Nonempty
  · by_cases hTall : R.int ⊆ T
    · have hN : N ∉ R.int := fun hN => hnot (by
        rw [hint]; intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact ((memT _).1 (hTall hN)).1
        · exact ((memT _).1 (hTall hv)).1)
      have hNS : N ∉ S := fun hNS => hnot (by
        rw [hint]; intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hNS
        · exact ((memT _).1 (hTall hv)).1)
      obtain ⟨h1, h2, h3⟩ := hy hN
      exact use y N m (Or.inr (Or.inr ⟨hN, rfl⟩)) h1 h2 hNZ (hRZ m h3)
        (Or.inr ⟨hNS, ((memT _).1 (hTall h3)).1⟩)
    · obtain ⟨f, hf, hc, hf1, hf2, hcut⟩ := hsp T hTsub hTne hTall
      have hcut' : ((R.ends f).1 ∈ S ∧ (R.ends f).2 ∉ S) ∨
          ((R.ends f).1 ∉ S ∧ (R.ends f).2 ∈ S) := by
        have e1 : (R.ends f).1 ∈ T ↔ (R.ends f).1 ∈ S := by rw [memT]; simp [hf1]
        have e2 : (R.ends f).2 ∈ T ↔ (R.ends f).2 ∈ S := by rw [memT]; simp [hf2]
        unfold MGraph.Cut at hcut
        rw [e1, e2] at hcut
        exact hcut
      by_cases hfg : f = g
      · subst hfg
        obtain ⟨c1, c2, s1, s2⟩ := hg hf
        have u1 := use g₁ (R.ends f).1 N (Or.inr (Or.inl ⟨hf, Or.inl rfl⟩)) c1 s1 (hRZ _ hf1) hNZ
        have u2 := use g₂ N (R.ends f).2 (Or.inr (Or.inl ⟨hf, Or.inr rfl⟩)) c2 s2 hNZ (hRZ _ hf2)
        by_cases hNS : N ∈ S
        · rcases hcut' with ⟨a, b⟩ | ⟨a, b⟩
          · exact u2 (Or.inl ⟨hNS, b⟩)
          · exact u1 (Or.inr ⟨a, hNS⟩)
        · rcases hcut' with ⟨a, b⟩ | ⟨a, b⟩
          · exact u1 (Or.inl ⟨a, hNS⟩)
          · exact u2 (Or.inr ⟨hNS, b⟩)
      · obtain ⟨c, se⟩ := hZc f hf hfg
        exact use f (R.ends f).1 (R.ends f).2 (Or.inl ⟨hfg, hf⟩) c se (hRZ _ hf1) (hRZ _ hf2)
          hcut'
  · -- `S` contains no vertex of `R`
    obtain ⟨s, hs⟩ := hne
    have hsR : s ∉ R.int := fun h => hTne ⟨s, (memT s).2 ⟨hs, h⟩⟩
    have hsN : s = N := by
      have := hS hs
      rw [hint] at this
      rcases Finset.mem_insert.1 this with h | h
      · exact h
      · exact absurd h hsR
    subst hsN
    obtain ⟨h1, h2, h3⟩ := hy hsR
    exact use y s m (Or.inr (Or.inr ⟨hsR, rfl⟩)) h1 h2 hNZ (hRZ m h3)
      (Or.inl ⟨hs, fun hm => hTne ⟨m, (memT m).2 ⟨hm, h3⟩⟩⟩)

/-- [II, Claims A.2, A.3] in net form: a doubly connected graph `R` gives a doubly connected graph
`Z`, whose internal vertices are those of `R` and `N`, if the present edges of `R` other than `g`
are edges of `Z`, the edge `g` is replaced by a path `g₁`, `g₂` through `N` of its class, and, if
`N` is not a vertex of `R`, it is joined to `R` by a `Θ` edge `y₁` and a `Θ` or blue solid edge
`y₂`. -/
private theorem dc_path [DecidableEq V] [DecidableEq E] {R Z : MGraph V E} (hR : R.DC) {N : V}
    (hint : Z.int = insert N R.int) {g g₁ g₂ y₁ y₂ : E} {m₁ m₂ : V}
    (h1 : ∀ f, R.Pres f → f ≠ g → (Z.cls f = R.cls f ∨
      (R.cls f = some .plus ∧ Z.cls f = some .diff)) ∧ SameEnds (Z.ends f) (R.ends f))
    (h2 : R.Pres g → Z.cls g₁ = R.cls g ∧ Z.cls g₂ = R.cls g ∧
      SameEnds (Z.ends g₁) ((R.ends g).1, N) ∧ SameEnds (Z.ends g₂) (N, (R.ends g).2) ∧
      ∀ f, R.Pres f → f ≠ g → f ≠ g₁ ∧ f ≠ g₂)
    (h3 : N ∉ R.int → Z.cls y₁ = some .diff ∧ (Z.cls y₂ = some .diff ∨ Z.cls y₂ = some .plus) ∧
      SameEnds (Z.ends y₁) (N, m₁) ∧ SameEnds (Z.ends y₂) (N, m₂) ∧ m₁ ∈ R.int ∧ m₂ ∈ R.int ∧
      y₁ ≠ y₂ ∧ (∀ f, R.Pres f → f ≠ g → f ≠ y₁ ∧ f ≠ y₂) ∧
      (R.Pres g → y₁ ≠ g₁ ∧ y₁ ≠ g₂ ∧ y₂ ≠ g₁ ∧ y₂ ≠ g₂)) : Z.DC := by
  classical
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hR
  have fil : ∀ B : Finset E, R.Spans B → R.Spans (B.filter R.Pres) := by
    intro B hB S h1 h2 h3
    obtain ⟨f, hf, hc, hf1, hf2, hcut⟩ := hB S h1 h2 h3
    refine ⟨f, Finset.mem_filter.2 ⟨hf, hc, hf1, hf2, fun h => ?_⟩, hc, hf1, hf2, hcut⟩
    simp only [MGraph.Cut, h] at hcut; tauto
  obtain ⟨K₀, hK₀, pK, hKK⟩ : ∃ K₀ : Finset E, R.Spans K₀ ∧ (∀ f ∈ K₀, R.Pres f) ∧ K₀ ⊆ K :=
    ⟨_, fil K hsK, fun f hf => (Finset.mem_filter.1 hf).2, Finset.filter_subset _ _⟩
  obtain ⟨L₀, hL₀, pL, hLL⟩ : ∃ L₀ : Finset E, R.Spans L₀ ∧ (∀ f ∈ L₀, R.Pres f) ∧ L₀ ⊆ L :=
    ⟨_, fil L hsL, fun f hf => (Finset.mem_filter.1 hf).2, Finset.filter_subset _ _⟩
  have hd₀ : ∀ x, x ∈ K₀ → x ∉ L₀ := fun x hx hx' =>
    Finset.disjoint_left.1 hd (hKK hx) (hLL hx')
  have zc : ∀ f, R.Pres f → f ≠ g → Z.cls f ≠ none ∧ SameEnds (Z.ends f) (R.ends f) := by
    intro f hf hfg
    obtain ⟨hc, hs⟩ := h1 f hf hfg
    refine ⟨?_, hs⟩
    rcases hc with h | ⟨-, h⟩ <;> rw [h]
    · exact hf.1
    · simp
  have zg : R.Pres g → Z.cls g₁ ≠ none ∧ Z.cls g₂ ≠ none ∧
      SameEnds (Z.ends g₁) ((R.ends g).1, N) ∧ SameEnds (Z.ends g₂) (N, (R.ends g).2) := by
    intro hg
    obtain ⟨a, b, c, d, -⟩ := h2 hg
    exact ⟨by rw [a]; exact hg.1, by rw [b]; exact hg.1, c, d⟩
  have zy₁ : N ∉ R.int → Z.cls y₁ ≠ none ∧ SameEnds (Z.ends y₁) (N, m₁) ∧ m₁ ∈ R.int := by
    intro hN
    obtain ⟨a, -, c, -, e, -⟩ := h3 hN
    exact ⟨by rw [a]; simp, c, e⟩
  have zy₂ : N ∉ R.int → Z.cls y₂ ≠ none ∧ SameEnds (Z.ends y₂) (N, m₂) ∧ m₂ ∈ R.int := by
    intro hN
    obtain ⟨-, b, -, d, -, f, -⟩ := h3 hN
    exact ⟨by rcases b with b | b <;> rw [b] <;> simp, d, f⟩
  have sK := spans_path (g₁ := g₁) (g₂ := g₂) hint pK hK₀
    (fun f hf hfg => zc f (pK f hf) hfg) (fun hg => zg (pK g hg)) zy₁
  have sL := spans_path (g₁ := g₁) (g₂ := g₂) hint pL hL₀
    (fun f hf hfg => zc f (pL f hf) hfg) (fun hg => zg (pL g hg)) zy₂
  have memS : ∀ (B : Finset E) (y x : E), x ∈ B.erase g ∪ (if g ∈ B then {g₁, g₂} else ∅) ∪
      (if N ∈ R.int then ∅ else {y}) ↔ (x ≠ g ∧ x ∈ B) ∨ (g ∈ B ∧ (x = g₁ ∨ x = g₂)) ∨
        (N ∉ R.int ∧ x = y) := by
    intro B y x
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_erase, mem_ite_pair, mem_ite_single,
      or_assoc]
  refine ⟨K₀.erase g ∪ (if g ∈ K₀ then {g₁, g₂} else ∅) ∪ (if N ∈ R.int then ∅ else {y₁}),
    L₀.erase g ∪ (if g ∈ L₀ then {g₁, g₂} else ∅) ∪ (if N ∈ R.int then ∅ else {y₂}),
    ?_, ?_, ?_, sK, sL⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [memS] at hx hx'
    rcases hx with ⟨hxg, hxK⟩ | ⟨hgK, hx⟩ | ⟨hN, rfl⟩ <;>
      rcases hx' with ⟨hxg', hxL⟩ | ⟨hgL, hx'⟩ | ⟨hN', hx'⟩
    · exact hd₀ x hxK hxL
    · obtain ⟨a, b⟩ := (h2 (pL g hgL)).2.2.2.2 x (pK x hxK) hxg
      rcases hx' with rfl | rfl
      · exact a rfl
      · exact b rfl
    · exact ((h3 hN').2.2.2.2.2.2.2.1 x (pK x hxK) hxg).2 hx'
    · obtain ⟨a, b⟩ := (h2 (pK g hgK)).2.2.2.2 x (pL x hxL) hxg'
      rcases hx with rfl | rfl
      · exact a rfl
      · exact b rfl
    · exact hd₀ g hgK hgL
    · obtain ⟨-, -, a, b⟩ := (h3 hN').2.2.2.2.2.2.2.2 (pK g hgK)
      rcases hx with rfl | rfl
      · exact a hx'.symm
      · exact b hx'.symm
    · exact ((h3 hN).2.2.2.2.2.2.2.1 _ (pL _ hxL) hxg').1 rfl
    · obtain ⟨a, b, -, -⟩ := (h3 hN).2.2.2.2.2.2.2.2 (pL g hgL)
      rcases hx' with h | h
      · exact a h
      · exact b h
    · exact (h3 hN).2.2.2.2.2.2.1 hx'
  · intro x hx
    rw [memS] at hx
    rcases hx with ⟨hxg, hxK⟩ | ⟨hgK, hx⟩ | ⟨hN, rfl⟩
    · rcases (h1 x (pK x hxK) hxg).1 with h | ⟨-, h⟩
      · rw [h]; exact hK x (hKK hxK)
      · exact h
    · obtain ⟨a, b, -⟩ := h2 (pK g hgK)
      have := hK g (hKK hgK)
      rcases hx with rfl | rfl
      · rw [a, this]
      · rw [b, this]
    · exact (h3 hN).1
  · intro x hx
    rw [memS] at hx
    rcases hx with ⟨hxg, hxL⟩ | ⟨hgL, hx⟩ | ⟨hN, rfl⟩
    · rcases (h1 x (pL x hxL) hxg).1 with h | ⟨-, h⟩
      · rw [h]; exact hL x (hLL hxL)
      · exact Or.inl h
    · obtain ⟨a, b, -⟩ := h2 (pL g hgL)
      have := hL g (hLL hgL)
      rcases hx with rfl | rfl
      · rw [a]; exact this
      · rw [b]; exact this
    · rcases (h3 hN).2.1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- The graph with its blue solid edges removed. -/
private def MGraph.dropPlus (X : MGraph V E) : MGraph V E :=
  { X with cls := fun x => if X.cls x = some .plus then none else X.cls x }

private theorem dropPlus_cls (X : MGraph V E) (x : E) :
    X.dropPlus.cls x = if X.cls x = some .plus then none else X.cls x := rfl

private theorem dropPlus_ends (X : MGraph V E) : X.dropPlus.ends = X.ends := rfl

private theorem dropPlus_int (X : MGraph V E) : X.dropPlus.int = X.int := rfl

private theorem le_dropPlus (X : MGraph V E) : Le X.dropPlus X := by
  refine ⟨rfl, fun x hx => ⟨Or.inl ?_, sameEnds_refl _⟩⟩
  have := hx.1
  rw [dropPlus_cls] at this ⊢
  simp only [id]
  split_ifs at this ⊢ with h
  · exact absurd rfl this
  · rfl

private theorem dropPlus_not_plus (X : MGraph V E) (x : E) : X.dropPlus.cls x ≠ some .plus := by
  rw [dropPlus_cls]; split_ifs with h
  · simp
  · exact h

/-- A graph is pre-deterministic if its blue solid edges, in a list, can be removed keeping the
doubly connected property. -/
private theorem preDet_of_dropPlus [DecidableEq E] {X : MGraph V E} (hX : X.dropPlus.DC) {m : List E}
    (hm : ∀ x, X.IsIntPlus x → x ∈ m) : X.PreDet :=
  preDet_of_base hX (le_dropPlus X) (fun f _ => dropPlus_not_plus X f) hm

/-! ## The chain of isolated subsets -/

/-- The data of a chain of proper isolated subsets of a sequentially pre-deterministic graph
without ghost edges: the chain `P` with `k` members, the component `lev v` of each vertex, and the
two crossing edges `cc l` (diffusive) and `cc' l` (diffusive or blue solid) of `P (l + 1)`. -/
structure SplitCtx [DecidableEq V] [DecidableEq E] (G : MGraph V E) where
  k : ℕ
  P : ℕ → Finset V
  lev : V → ℕ
  cc : ℕ → E
  cc' : ℕ → E
  spd : G.SPD
  chain : G.IsChain k P
  lev_le : ∀ v, lev v ≤ k
  memP : ∀ v ∈ G.int, ∀ m ≤ k, (v ∈ P m ↔ m ≤ lev v)
  Psub : ∀ m ≤ k, P m ⊆ G.int
  cc_ne : ∀ l < k, cc l ≠ cc' l
  cc_diff : ∀ l < k, G.cls (cc l) = some .diff
  cc'_cls : ∀ l < k, G.cls (cc' l) = some .diff ∨ G.cls (cc' l) = some .plus
  cross : ∀ l < k, ∀ e, G.Crosses (P (l + 1)) e ↔ e = cc l ∨ e = cc' l
  cc_ends : ∀ l < k, ∀ x, (x = cc l ∨ x = cc' l) → ∃ w, w ∈ G.int ∧ lev w = l + 1 ∧
    G.outer (P (l + 1)) x ∈ G.int ∧ lev (G.outer (P (l + 1)) x) = l ∧
    (G.ends x = (G.outer (P (l + 1)) x, w) ∨ G.ends x = (w, G.outer (P (l + 1)) x))
  jump : ∀ e, G.cls e ≠ none → G.cls e ≠ some .minus → (G.ends e).1 ∈ G.int →
    (G.ends e).2 ∈ G.int → lev (G.ends e).1 ≠ lev (G.ends e).2 →
    ∃ l < k, e = cc l ∨ e = cc' l

/-- The members of a chain decrease. -/
private theorem chain_anti {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V} (hc : G.IsChain k P)
    {a b : ℕ} (hab : a ≤ b) (hbk : b ≤ k) : P b ⊆ P a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (hc.2.1 (a + n) (by omega)).1.2.1.trans (ih (by omega) (by omega))

/-- A member of a chain is the set of all internal vertices or an isolated subset. -/
private theorem chain_isoOrTop {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V} (hc : G.IsChain k P)
    {l : ℕ} (hl : l ≤ k) : G.IsoOrTop (P l) := by
  rcases l with _ | l
  · exact Or.inl hc.1
  · exact Or.inr (hc.2.1 l (by omega)).1.1

/-- The ends of an edge cutting `P`: the outer end and an end in `P`. -/
private theorem ends_of_cut [DecidableEq V] {G : MGraph V E} {P : Finset V} {e : E}
    (h : G.Cut P e) : G.outer P e ∉ P ∧ ∃ w ∈ P,
      (G.ends e = (G.outer P e, w) ∨ G.ends e = (w, G.outer P e)) := by
  unfold MGraph.outer
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ite_eq_left h1]
    exact ⟨h2, _, h1, Or.inr rfl⟩
  · rw [ite_eq_right h1]
    exact ⟨h1, _, h2, Or.inl rfl⟩

/-- The chain data of a sequentially pre-deterministic graph without ghost edges. -/
private theorem ctx_exists [DecidableEq V] [DecidableEq E] [Nonempty E] {G : MGraph V E} {k : ℕ}
    {P : ℕ → Finset V} (hs : G.SPD) (hc : G.IsChain k P) (hng : ∀ e, G.cls e ≠ some .ghost) :
    ∃ C : SplitCtx G, C.k = k ∧ C.P = P := by
  classical
  have hdc := hs.1
  have Pint : ∀ m ≤ k, P m ⊆ G.int := fun m hm => hc.1 ▸ chain_anti hc (Nat.zero_le m) hm
  have hex : ∀ v, ∃ l, k ≤ l ∨ v ∉ P (l + 1) := fun _ => ⟨k, Or.inl le_rfl⟩
  let lev : V → ℕ := fun v => Nat.find (hex v)
  have lev_le : ∀ v, lev v ≤ k := fun v => Nat.find_min' _ (Or.inl le_rfl)
  have lev_spec : ∀ v, k ≤ lev v ∨ v ∉ P (lev v + 1) := fun v => Nat.find_spec (hex v)
  have lev_min : ∀ v l, l < lev v → v ∈ P (l + 1) := fun v l hl => by
    have := Nat.find_min (hex v) hl
    simp only [not_or, not_not] at this
    exact this.2
  have memP : ∀ v ∈ G.int, ∀ m ≤ k, (v ∈ P m ↔ m ≤ lev v) := by
    intro v hv m hm
    constructor
    · intro hvm
      by_contra hlt
      rw [not_le] at hlt
      rcases lev_spec v with h | h
      · exact absurd (lev_le v) (by omega)
      · exact h (chain_anti hc (by omega) hm hvm)
    · intro hml
      rcases m with _ | m
      · rw [hc.1]; exact hv
      · exact lev_min v m (by omega)
  have hcr : ∀ l, l < k → ∃ c c', c ≠ c' ∧ G.cls c = some .diff ∧
      (G.cls c' = some .diff ∨ G.cls c' = some .plus) ∧
      ∀ e, G.Crosses (P (l + 1)) e ↔ e = c ∨ e = c' := by
    intro l hl
    obtain ⟨⟨⟨-, e₁, e₂, hne, hx⟩, hss⟩, -⟩ := hc.2.1 l hl
    have hsub := Pint (l + 1) (by omega)
    obtain ⟨a, b, hab, ha, hb, hca, hcb⟩ := MGraph.claim51 V E G hdc (P (l + 1)) hsub
      (by
        obtain ⟨-, -, -, -, h⟩ := (hx e₁).2 (Or.inl rfl)
        rcases h with ⟨h, -⟩ | ⟨-, h⟩
        exacts [⟨_, h⟩, ⟨_, h⟩])
      (fun h => hss.2 (h.trans' (Pint l (by omega))))
    refine ⟨a, b, hab, hca, ?_, fun e => ?_⟩
    · rcases hcb with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hng b)
    · rw [hx e]
      rcases (hx a).1 ha with rfl | rfl <;> rcases (hx b).1 hb with rfl | rfl
      · exact absurd rfl hab
      · rfl
      · exact or_comm
      · exact absurd rfl hab
  choose! cc cc' hcc using hcr
  have cross : ∀ l < k, ∀ e, G.Crosses (P (l + 1)) e ↔ e = cc l ∨ e = cc' l :=
    fun l hl => (hcc l hl).2.2.2
  have levP : ∀ v ∈ G.int, ∀ m ≤ k, v ∈ P m → v ∉ P (m + 1) → lev v = m := by
    intro v hv m hm h1 h2
    have := (memP v hv m hm).1 h1
    by_cases hmk : m + 1 ≤ k
    · have := mt (memP v hv (m + 1) hmk).2 h2; omega
    · have := lev_le v; omega
  refine ⟨⟨k, P, lev, cc, cc', hs, hc, lev_le, memP, Pint, fun l hl => (hcc l hl).1,
    fun l hl => (hcc l hl).2.1, fun l hl => (hcc l hl).2.2.1, cross, ?_, ?_⟩, rfl, rfl⟩
  · intro l hl x hx
    have hxc : G.Crosses (P (l + 1)) x := (cross l hl x).2 hx
    have hpp : G.IsProperIso (P l) (P (l + 1)) := (hc.2.1 l hl).1
    have ho := MGraph.replace_ends V E G hdc (P l) (P (l + 1)) x (chain_isoOrTop hc hl.le) hpp hxc
    obtain ⟨ho1, ho2⟩ := Finset.mem_sdiff.1 ho
    have hoi := Pint l hl.le ho1
    obtain ⟨-, w, hw, hends⟩ := ends_of_cut hxc.2.2.2.2
    have hwi := Pint (l + 1) (by omega) hw
    refine ⟨w, hwi, ?_, hoi, levP _ hoi l hl.le ho1 ho2, hends⟩
    have h1 := (memP w hwi (l + 1) (by omega)).1 hw
    by_contra hne
    have h2 : l + 2 ≤ lev w := by omega
    have hk2 : l + 2 ≤ k := (lev_le w).trans' h2
    have hw2 : w ∈ P (l + 2) := (memP w hwi (l + 2) hk2).2 h2
    have ho2' : G.outer (P (l + 1)) x ∉ P (l + 2) := fun h => ho2 (chain_anti hc (by omega) hk2 h)
    have hcut2 : G.Cut (P (l + 2)) x := by
      rcases hends with h | h <;> simp only [MGraph.Cut, h] <;> tauto
    have hxc2 : G.Crosses (P (l + 2)) x := ⟨hxc.1, hxc.2.1, hxc.2.2.1, hxc.2.2.2.1, hcut2⟩
    have ho' := MGraph.replace_ends V E G hdc (P (l + 1)) (P (l + 2)) x
      (chain_isoOrTop hc (by omega)) (hc.2.1 (l + 1) (by omega)).1 hxc2
    have heq : G.outer (P (l + 2)) x = G.outer (P (l + 1)) x := by
      unfold MGraph.outer at ho2' ⊢
      rcases hends with h | h
      · rw [h] at ho2' ⊢
        simp only at ho2' ⊢
        split_ifs at ho2' ⊢ <;> simp_all
      · rw [h] at ho2' ⊢
        simp only at ho2' ⊢
        split_ifs at ho2' ⊢
        simp_all
    rw [heq] at ho'
    exact ho2 (Finset.mem_sdiff.1 ho').1
  · intro e hc1 hc2 h1 h2 hne
    have key : ∀ a b, (a = (G.ends e).1 ∧ b = (G.ends e).2 ∨ a = (G.ends e).2 ∧ b = (G.ends e).1) →
        lev a < lev b → ∃ l < k, e = cc l ∨ e = cc' l := by
      intro a b hab hlt
      have ha : a ∈ G.int := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
      have hb : b ∈ G.int := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
      have hlk : lev a < k := lt_of_lt_of_le hlt (lev_le b)
      refine ⟨lev a, hlk, (cross (lev a) hlk e).1 ⟨hc1, hc2, Or.inl h1, Or.inl h2, ?_⟩⟩
      have haP : a ∉ P (lev a + 1) := fun h => by
        have := (memP a ha _ (by omega)).1 h; omega
      have hbP : b ∈ P (lev a + 1) := (memP b hb _ (by omega)).2 (by omega)
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨haP, hbP⟩
      · exact Or.inl ⟨hbP, haP⟩
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key _ _ (Or.inl ⟨rfl, rfl⟩) h
    · exact key _ _ (Or.inr ⟨rfl, rfl⟩) h

/-! ## Induced subgraphs on parts of the chain -/

/-- A net `N` of a doubly connected graph, restricted to the edges inside `Q`, spans the subgraph
induced on `Q` if at most two edges with internal ends leave `Q`: otherwise `N` has two edges
leaving `Q` and the other net `N'` a third one. -/
private theorem spans_induce_of_cut2 [DecidableEq V] {X : MGraph V E} {N N' : Finset E}
    (hd : Disjoint N N') (hN : X.Spans N) (hN' : X.Spans N')
    (hNc : ∀ e ∈ N, X.cls e ≠ some .minus) (hN'c : ∀ e ∈ N', X.cls e ≠ some .minus)
    {Q : Finset V} (hQ : Q ⊆ X.int) (s : Finset E) (hs : s.card ≤ 2)
    (hcut : ∀ e, X.cls e ≠ none → X.cls e ≠ some .minus → (X.ends e).1 ∈ X.int →
      (X.ends e).2 ∈ X.int → X.Cut Q e → e ∈ s) :
    (X.induce Q).Spans (N.filter fun e => (X.ends e).1 ∈ Q ∧ (X.ends e).2 ∈ Q) := by
  classical
  intro S hS hne hnot
  by_contra hno
  have hin : ∀ e ∈ N, X.cls e ≠ none → (X.ends e).1 ∈ Q → (X.ends e).2 ∈ Q → ¬ X.Cut S e := by
    intro e he hc h1 h2 hcut'
    refine hno ⟨e, Finset.mem_filter.2 ⟨he, h1, h2⟩, ?_, h1, h2, hcut'⟩
    simp [MGraph.induce, h1, h2, hc]
  obtain ⟨v, hvQ, hvS⟩ := Finset.not_subset.1 hnot
  obtain ⟨w, hwS⟩ := hne
  have out : ∀ T : Finset V, T ⊆ Q → T.Nonempty → ¬ X.int ⊆ T → (∀ e ∈ N, X.cls e ≠ none →
      (X.ends e).1 ∈ Q → (X.ends e).2 ∈ Q → ¬ X.Cut T e) →
      ∃ e ∈ N, e ∈ s ∧ (X.ends e).1 ∈ X.int ∧ (X.ends e).2 ∈ X.int ∧
        (((X.ends e).1 ∈ T ∧ (X.ends e).2 ∉ Q) ∨ ((X.ends e).2 ∈ T ∧ (X.ends e).1 ∉ Q)) := by
    intro T hT hTne hTnot hTin
    obtain ⟨e, he, hc, h1, h2, hcut'⟩ := hN T (hT.trans hQ) hTne hTnot
    have := hTin e he hc
    simp only [MGraph.Cut] at this hcut'
    have hpos : ((X.ends e).1 ∈ T ∧ (X.ends e).2 ∉ Q) ∨ ((X.ends e).2 ∈ T ∧ (X.ends e).1 ∉ Q) := by
      rcases hcut' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨ha, fun hq => this (hT ha) hq (Or.inl ⟨ha, hb⟩)⟩
      · exact Or.inr ⟨hb, fun hq => this hq (hT hb) (Or.inr ⟨ha, hb⟩)⟩
    refine ⟨e, he, hcut e hc (hNc e he) h1 h2 ?_, h1, h2, hpos⟩
    simp only [MGraph.Cut]
    rcases hpos with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨hT ha, hb⟩
    · exact Or.inr ⟨hb, hT ha⟩
  have hin' : ∀ e ∈ N, X.cls e ≠ none → (X.ends e).1 ∈ Q → (X.ends e).2 ∈ Q →
      ¬ X.Cut (Q \ S) e := by
    intro e he hc h1 h2 hcut'
    refine hin e he hc h1 h2 ?_
    simp only [MGraph.Cut, Finset.mem_sdiff] at hcut' ⊢
    tauto
  obtain ⟨e₁, he₁, hs₁, -, -, hp₁⟩ := out S hS ⟨w, hwS⟩ (fun h => hvS (h (hQ hvQ))) hin
  obtain ⟨e₂, he₂, hs₂, -, -, hp₂⟩ := out (Q \ S) Finset.sdiff_subset
    ⟨v, Finset.mem_sdiff.2 ⟨hvQ, hvS⟩⟩
    (fun h => (Finset.mem_sdiff.1 (h (hQ (hS hwS)))).2 hwS) hin'
  have h12 : e₁ ≠ e₂ := by
    rintro rfl
    simp only [Finset.mem_sdiff] at hp₂
    rcases hp₁ with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hp₂ with ⟨c, d⟩ | ⟨c, d⟩
    · exact c.2 a
    · exact b c.1
    · exact d (hS a)
    · exact c.2 a
  -- the other net leaves `Q` too
  have hQnot : ¬ X.int ⊆ Q := by
    intro h
    obtain ⟨e, he, hc, h1, h2, hcut'⟩ := hN S (hS.trans hQ) ⟨w, hwS⟩ (fun h' => hvS (h' (hQ hvQ)))
    exact hin e he hc (h h1) (h h2) hcut'
  obtain ⟨f, hf, hfc, hf1, hf2, hfcut⟩ := hN' Q hQ ⟨v, hvQ⟩ hQnot
  have hfs := hcut f hfc (hN'c f hf) hf1 hf2 hfcut
  have h1f : e₁ ≠ f := fun h => Finset.disjoint_left.1 hd he₁ (h ▸ hf)
  have h2f : e₂ ≠ f := fun h => Finset.disjoint_left.1 hd he₂ (h ▸ hf)
  have hsub : ({e₁, e₂, f} : Finset E) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_eq_three.2 ⟨e₁, e₂, f, h12, h1f, h2f, rfl⟩] at this
  omega

/-- The subgraph induced on a set `Q` of internal vertices of a doubly connected graph, left by
at most two edges with internal ends, is doubly connected. -/
private theorem dc_induce_of_cut2 [DecidableEq V] {X : MGraph V E} (hX : X.DC) {Q : Finset V}
    (hQ : Q ⊆ X.int) (s : Finset E) (hs : s.card ≤ 2)
    (hcut : ∀ e, X.cls e ≠ none → X.cls e ≠ some .minus → (X.ends e).1 ∈ X.int →
      (X.ends e).2 ∈ X.int → X.Cut Q e → e ∈ s) : (X.induce Q).DC := by
  classical
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := hX
  have hKm : ∀ e ∈ K, X.cls e ≠ some .minus := fun e he => by rw [hK e he]; simp
  have hLm : ∀ e ∈ L, X.cls e ≠ some .minus := fun e he => by
    rcases hL e he with h | h | h <;> rw [h] <;> simp
  refine ⟨K.filter fun e => (X.ends e).1 ∈ Q ∧ (X.ends e).2 ∈ Q,
    L.filter fun e => (X.ends e).1 ∈ Q ∧ (X.ends e).2 ∈ Q,
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_, ?_,
    spans_induce_of_cut2 hd hsK hsL hKm hLm hQ s hs hcut,
    spans_induce_of_cut2 hd.symm hsL hsK hLm hKm hQ s hs hcut⟩
  · intro e he
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he
    simp only [MGraph.induce, h1, h2, and_self, ↓reduceIte]
    exact hK e he
  · intro e he
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he
    simp only [MGraph.induce, h1, h2, and_self, ↓reduceIte]
    exact hL e he

/-- Inducing twice. -/
private theorem induce_induce [DecidableEq V] (X : MGraph V E) {A B : Finset V} (h : B ⊆ A) :
    (X.induce A).induce B = X.induce B := by
  unfold MGraph.induce
  congr 1
  funext e
  by_cases hb : (X.ends e).1 ∈ B ∧ (X.ends e).2 ∈ B
  · simp [hb, h hb.1, h hb.2]
  · simp [hb]

/-- The vertices of the components `a, …, b - 1` of the chain. -/
def SplitCtx.Lvl [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : SplitCtx G) (a b : ℕ) :
    Finset V :=
  G.int.filter fun v => a ≤ C.lev v ∧ C.lev v < b

/-- Membership in the components `a, …, b - 1`. -/
private theorem SplitCtx.mem_Lvl [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : SplitCtx G)
    {a b : ℕ} {v : V} : v ∈ C.Lvl a b ↔ v ∈ G.int ∧ a ≤ C.lev v ∧ C.lev v < b := by
  unfold SplitCtx.Lvl
  rw [Finset.mem_filter]

/-- The subgraph induced on the components `a, …, b - 1` of the chain is doubly connected. -/
private theorem SplitCtx.dc_Lvl [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : SplitCtx G)
    {a : ℕ} (b : ℕ) (ha : a ≤ C.k) : (G.induce (C.Lvl a b)).DC := by
  classical
  have hdc := C.spd.1
  -- the subgraph induced on `P a`
  have h1 : (G.induce (C.P a)).DC := by
    rcases a with _ | a
    · refine dc_induce_of_cut2 hdc (C.Psub 0 ha) ∅ (by simp) fun e _ _ h1 h2 hc => ?_
      rw [C.chain.1] at hc
      simp only [MGraph.Cut] at hc
      tauto
    · obtain ⟨-, e₁, e₂, -, hx⟩ := (C.chain.2.1 a (by omega)).1.1
      refine dc_induce_of_cut2 hdc (C.Psub _ ha) {e₁, e₂} (Finset.card_le_two)
        fun e hc hm h1 h2 hcut => ?_
      rcases (hx e).1 ⟨hc, hm, Or.inl h1, Or.inl h2, hcut⟩ with rfl | rfl <;> simp
  have hsub : C.Lvl a b ⊆ C.P a := by
    intro v hv
    obtain ⟨hv, hav, -⟩ := C.mem_Lvl.1 hv
    exact (C.memP v hv a ha).2 hav
  rw [← induce_induce G hsub]
  by_cases hb : b ≤ C.k ∧ a < b
  · obtain ⟨hbk, hab⟩ := hb
    obtain ⟨-, e₁, e₂, -, hx⟩ := (C.chain.2.1 (b - 1) (by omega)).1.1
    refine dc_induce_of_cut2 h1 hsub {e₁, e₂} (Finset.card_le_two)
      fun e hc hm h1' h2' hcut => ?_
    have hcG : G.cls e ≠ none ∧ (G.ends e).1 ∈ C.P a ∧ (G.ends e).2 ∈ C.P a := by
      by_cases hin : (G.ends e).1 ∈ C.P a ∧ (G.ends e).2 ∈ C.P a
      · simp only [MGraph.induce, hin, and_self, ↓reduceIte] at hc
        exact ⟨hc, hin⟩
      · simp [MGraph.induce, hin] at hc
    obtain ⟨hcG, ha1, ha2⟩ := hcG
    have hmG : G.cls e ≠ some .minus := by
      simpa [MGraph.induce, ha1, ha2] using hm
    have hi1 := C.Psub a ha ha1
    have hi2 := C.Psub a ha ha2
    have hcut' : G.Cut (C.P (b - 1 + 1)) e := by
      have e1 := (C.memP _ hi1 a ha).1 ha1
      have e2 := (C.memP _ hi2 a ha).1 ha2
      have f1 := C.memP _ hi1 (b - 1 + 1) (by omega)
      have f2 := C.memP _ hi2 (b - 1 + 1) (by omega)
      simp only [MGraph.Cut, MGraph.induce, C.mem_Lvl] at hcut
      simp only [MGraph.Cut, f1, f2]
      rcases hcut with ⟨⟨-, -, h⟩, h'⟩ | ⟨h', ⟨-, -, h⟩⟩
      · refine Or.inr ⟨by omega, ?_⟩
        by_contra h''; exact h' ⟨hi2, e2, by omega⟩
      · refine Or.inl ⟨?_, by omega⟩
        by_contra h''; exact h' ⟨hi1, e1, by omega⟩
    rcases (hx e).1 ⟨hcG, hmG, Or.inl hi1, Or.inl hi2, hcut'⟩ with rfl | rfl <;> simp
  · refine dc_induce_of_cut2 h1 hsub ∅ (by simp) fun e hc _ h1' h2' hcut => ?_
    exfalso
    simp only [MGraph.induce] at h1' h2'
    simp only [MGraph.Cut, MGraph.induce, C.mem_Lvl] at hcut
    have e1 := (C.memP _ (C.Psub a ha h1') a ha).1 h1'
    have e2 := (C.memP _ (C.Psub a ha h2') a ha).1 h2'
    have l1 := C.lev_le (G.ends e).1
    have l2 := C.lev_le (G.ends e).2
    rcases hcut with ⟨⟨-, -, h⟩, h'⟩ | ⟨h', ⟨-, -, h⟩⟩
    · exact h' ⟨C.Psub a ha h2', e2, by omega⟩
    · exact h' ⟨C.Psub a ha h1', e1, by omega⟩

/-! ## The components of the chain -/

/-- The ends of the crossing edges of `P (l + 1)`: internal, in the components `l` and `l + 1`. -/
private theorem SplitCtx.cc_lev [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : SplitCtx G) {l : ℕ}
    (hl : l < C.k) {x : E} (hx : x = C.cc l ∨ x = C.cc' l) :
    (G.ends x).1 ∈ G.int ∧ (G.ends x).2 ∈ G.int ∧
      ((C.lev (G.ends x).1 = l ∧ C.lev (G.ends x).2 = l + 1) ∨
        (C.lev (G.ends x).1 = l + 1 ∧ C.lev (G.ends x).2 = l)) := by
  obtain ⟨w, hw, hlw, ho, hlo, hends⟩ := C.cc_ends l hl x hx
  rcases hends with h | h <;> rw [h]
  · exact ⟨ho, hw, Or.inl ⟨hlo, hlw⟩⟩
  · exact ⟨hw, ho, Or.inr ⟨hlw, hlo⟩⟩


/-- The subgraph induced on the components `a, …, b - 1` of the chain is doubly connected, also
when it is empty. -/
private theorem SplitCtx.dc_Lvl' [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : SplitCtx G)
    (a b : ℕ) : (G.induce (C.Lvl a b)).DC := by
  by_cases ha : a ≤ C.k
  · exact C.dc_Lvl b ha
  · have he : C.Lvl a b = ∅ := by
      ext v
      simp only [C.mem_Lvl, Finset.notMem_empty, iff_false, not_and]
      intro _ h; have := C.lev_le v; omega
    refine ⟨∅, ∅, disjoint_bot_left, by simp, by simp, ?_, ?_⟩ <;>
    · intro S hS ⟨v, hv⟩
      have := hS hv
      simp [MGraph.induce, he] at this

/-- A proper isolated subset of the set of all internal vertices is a member of the chain. -/
private theorem chain_iso_eq {G : MGraph V E} {k : ℕ} {P : ℕ → Finset V}
    (hc : G.IsChain k P) (hio : G.IsoChain) {Q : Finset V} (hQ : G.IsProperIso G.int Q) :
    ∃ l, 1 ≤ l ∧ l ≤ k ∧ Q = P l := by
  classical
  set l := Nat.findGreatest (fun l => Q ⊆ P l) k with hl
  have hlk : l ≤ k := Nat.findGreatest_le k
  have hQl : Q ⊆ P l := Nat.findGreatest_spec (P := fun l => Q ⊆ P l) (Nat.zero_le k)
    (by rw [hc.1]; exact hQ.2.1)
  by_cases heq : Q = P l
  · refine ⟨l, ?_, hlk, heq⟩
    by_contra h0
    have : l = 0 := by omega
    rw [this, hc.1] at heq
    exact hQ.2.ne heq
  · have hss : Q ⊂ P l := Finset.ssubset_iff_subset_ne.2 ⟨hQl, heq⟩
    rcases Nat.lt_or_ge l k with hlt | hge
    · have hmax := hc.2.1 l hlt
      have hPint : P (l + 1) ⊂ G.int := by
        refine Finset.ssubset_of_ssubset_of_subset hmax.1.2 ?_
        rw [← hc.1]; exact chain_anti hc (Nat.zero_le l) hlt.le
      have hng : ¬ Q ⊆ P (l + 1) :=
        Nat.findGreatest_is_greatest (P := fun l => Q ⊆ P l) (n := k) (by omega) (by omega)
      exfalso
      rcases hio _ _ hQ ⟨hmax.1.1, hPint⟩ with h | h
      · exact hng h
      · by_cases h' : P (l + 1) = Q
        · exact hng (h' ▸ Finset.Subset.refl _)
        · exact hmax.2 Q ⟨hQ.1, hss⟩ (Finset.ssubset_iff_subset_ne.2 ⟨h, h'⟩)
    · have : l = k := le_antisymm hlk hge
      rw [this] at hss
      exact absurd ⟨hQ.1, hss⟩ (hc.2.2 Q)

/-- A sequentially pre-deterministic graph has a chain of proper isolated subsets: each member
after the first is a maximal isolated subset of the previous one, and the last one has no proper
isolated subset. -/
private theorem exists_chain {G : MGraph V E} :
    ∃ k P, G.IsChain k P := by
  classical
  have hmax : ∀ S, (∃ Q, G.IsProperIso S Q) → ∃ Q, G.IsMaximalIso S Q := by
    intro S ⟨Q₀, hQ₀⟩
    obtain ⟨Q, hQ, hmx⟩ := Finset.exists_max_image (S.powerset.filter fun Q => G.IsProperIso S Q)
      Finset.card ⟨Q₀, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hQ₀.2.1, hQ₀⟩⟩
    obtain ⟨-, hQ⟩ := Finset.mem_filter.1 hQ
    refine ⟨Q, hQ, fun Q' hQ' hlt => ?_⟩
    have := hmx Q' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hQ'.2.1, hQ'⟩)
    have := Finset.card_lt_card hlt
    omega
  let nxt : Finset V → Finset V := fun S =>
    if h : ∃ Q, G.IsProperIso S Q then Classical.choose (hmax S h) else S
  have hnxt : ∀ S (h : ∃ Q, G.IsProperIso S Q), G.IsMaximalIso S (nxt S) := fun S h => by
    simp only [nxt, h, ↓reduceDIte]; exact Classical.choose_spec (hmax S h)
  let P : ℕ → Finset V := fun l => nxt^[l] G.int
  have hP : ∀ l, P (l + 1) = nxt (P l) := fun l => Function.iterate_succ_apply' _ _ _
  have hex : ∃ l, ¬ ∃ Q, G.IsProperIso (P l) Q := by
    by_contra hn
    push Not at hn
    have key : ∀ l, (P l).card + l ≤ (P 0).card := by
      intro l
      induction l with
      | zero => simp
      | succ n ih =>
        have := Finset.card_lt_card (hnxt (P n) (hn n)).1.2
        rw [hP]; omega
    have := key ((P 0).card + 1)
    omega
  refine ⟨Nat.find hex, P, rfl, fun l hl => ?_, not_exists.1 (Nat.find_spec hex)⟩
  have := Nat.find_min hex hl
  rw [not_not] at this
  rw [hP]
  exact hnxt _ this


/-- Membership in the members of the chain. -/
private theorem SplitCtx.mem_P [DecidableEq V] [DecidableEq E] {G : MGraph V E} (C : SplitCtx G) {m : ℕ}
    (hm : m ≤ C.k) (v : V) : v ∈ C.P m ↔ v ∈ G.int ∧ m ≤ C.lev v :=
  ⟨fun h => ⟨C.Psub m hm h, (C.memP v (C.Psub m hm h) m hm).1 h⟩,
    fun ⟨h1, h2⟩ => (C.memP v h1 m hm).2 h2⟩

/-! ## The graph with an edge replaced by a path -/

section Split

variable [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V)

private theorem split_int : (G.split e e' w).int = G.int := rfl

private theorem split_ext : (G.split e e' w).ext = G.ext := rfl

private theorem split_cls (x : E) :
    (G.split e e' w).cls x = if x = e' then G.cls e else G.cls x := rfl

private theorem split_ends (x : E) : (G.split e e' w).ends x =
    if x = e then ((G.ends e).1, w) else if x = e' then (w, (G.ends e).2) else G.ends x := rfl

private theorem split_cls_e' : (G.split e e' w).cls e' = G.cls e := by simp [split_cls]

variable {G e e' w}

private theorem split_cls_of (hne : e ≠ e') : (G.split e e' w).cls e = G.cls e := by
  simp [split_cls, hne]

private theorem split_cls_ne {x : E} (hx : x ≠ e') : (G.split e e' w).cls x = G.cls x := by
  simp [split_cls, hx]

private theorem split_ends_e : (G.split e e' w).ends e = ((G.ends e).1, w) := by simp [split_ends]

private theorem split_ends_e' (hne : e ≠ e') : (G.split e e' w).ends e' = (w, (G.ends e).2) := by
  simp [split_ends, hne.symm]

private theorem split_ends_ne {x : E} (hx : x ≠ e) (hx' : x ≠ e') : (G.split e e' w).ends x = G.ends x := by
  simp [split_ends, hx, hx']

private theorem split_crosses_ne {Q : Finset V} {x : E} (hx : x ≠ e) (hx' : x ≠ e') :
    (G.split e e' w).Crosses Q x ↔ G.Crosses Q x := by
  unfold MGraph.Crosses MGraph.Cut MGraph.IsVtx
  rw [split_cls_ne hx', split_ends_ne hx hx', split_int, split_ext]

/-- The crossings of the path `e`, `e'` and of the edge `e`: replacing `e` by the path changes
the number of edges crossing `Q` by `0` or `2` ([II, §5.4]). -/
private theorem split_crosses_e (hne : e ≠ e') (hw : w ∈ G.int) (he : G.cls e = some .plus)
    (ha : G.IsVtx (G.ends e).1) (hb : G.IsVtx (G.ends e).2) (Q : Finset V) :
    ((G.split e e' w).Crosses Q e ↔ ((G.ends e).1 ∈ Q ↔ w ∉ Q)) ∧
    ((G.split e e' w).Crosses Q e' ↔ (w ∈ Q ↔ (G.ends e).2 ∉ Q)) ∧
    (G.Crosses Q e ↔ ((G.ends e).1 ∈ Q ↔ (G.ends e).2 ∉ Q)) := by
  unfold MGraph.Crosses MGraph.Cut MGraph.IsVtx at *
  rw [split_cls_of hne, split_cls_e', split_ends_e, split_ends_e' hne, split_int, split_ext, he]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  have hw' : w ∈ G.int ∨ w ∈ G.ext := Or.inl hw
  refine ⟨?_, ?_, ?_⟩ <;> constructor
  all_goals first
    | (rintro ⟨-, -, h⟩; tauto)
    | (intro h; refine ⟨by tauto, by tauto, by tauto⟩)

section Logic

variable {A B W : Prop}

private theorem lg_sep1 (h1 : A ↔ ¬ W) (h2 : W ↔ ¬ B) (hs : ¬ ((A ∧ B ∧ ¬ W) ∨ (¬ A ∧ ¬ B ∧ W))) :
    False := by tauto

private theorem lg_sep2 (h1 : A ↔ ¬ W) (hs : ¬ ((A ∧ B ∧ ¬ W) ∨ (¬ A ∧ ¬ B ∧ W))) : A ↔ ¬ B := by
  tauto

private theorem lg_sep3 (h2 : W ↔ ¬ B) (hs : ¬ ((A ∧ B ∧ ¬ W) ∨ (¬ A ∧ ¬ B ∧ W))) : A ↔ ¬ B := by
  tauto

private theorem lg_sep4 (h3 : A ↔ ¬ B) (h1 : ¬ (A ↔ ¬ W)) : W ↔ ¬ B := by tauto

private theorem lg_sep5 (hs : (A ∧ B ∧ ¬ W) ∨ (¬ A ∧ ¬ B ∧ W)) :
    (A ↔ ¬ W) ∧ (W ↔ ¬ B) ∧ ¬ (A ↔ ¬ B) := by tauto

end Logic

/-- `Q` separates the ends of `e` (on one side) from `w` (on the other). -/
private def Sep (G : MGraph V E) (e : E) (w : V) (Q : Finset V) : Prop :=
  ((G.ends e).1 ∈ Q ∧ (G.ends e).2 ∈ Q ∧ w ∉ Q) ∨ ((G.ends e).1 ∉ Q ∧ (G.ends e).2 ∉ Q ∧ w ∈ Q)

omit [DecidableEq V] in
private theorem two_of_two {p q : E → Prop} {e e' : E} (hne : e ≠ e')
    (h₁ : ∀ x, x ≠ e → x ≠ e' → (p x ↔ q x)) (h₂ : ¬ q e') (h₃ : p e ∨ p e' ↔ q e)
    (h₄ : ¬ (p e ∧ p e')) :
    (∃ x₁ x₂, x₁ ≠ x₂ ∧ ∀ x, p x ↔ x = x₁ ∨ x = x₂) →
      (∃ x₁ x₂, x₁ ≠ x₂ ∧ ∀ x, q x ↔ x = x₁ ∨ x = x₂) := by
  rintro ⟨x₁, x₂, hx, hp⟩
  have pe := hp e
  have pe' := hp e'
  refine ⟨if x₁ = e' then e else x₁, if x₂ = e' then e else x₂, ?_, fun x => ?_⟩
  · by_cases h1 : x₁ = e' <;> by_cases h2 : x₂ = e' <;> simp only [h1, h2, ite_true, ite_false]
    · exact absurd (h1.trans h2.symm) hx
    · intro h; subst h1; subst h
      exact h₄ ⟨pe.2 (Or.inr rfl), pe'.2 (Or.inl rfl)⟩
    · intro h; subst h2; subst h
      exact h₄ ⟨pe.2 (Or.inl rfl), pe'.2 (Or.inr rfl)⟩
    · exact hx
  · by_cases hxe : x = e
    · rw [hxe, ← h₃, pe, pe']
      by_cases h1 : x₁ = e' <;> by_cases h2 : x₂ = e' <;> simp only [h1, h2, ite_true, ite_false] <;>
        aesop
    · by_cases hxe' : x = e'
      · rw [hxe']
        simp only [h₂, false_iff]
        by_cases h1 : x₁ = e' <;> by_cases h2 : x₂ = e' <;> simp only [h1, h2, ite_true, ite_false] <;>
          aesop
      · rw [← h₁ x hxe hxe', hp]
        by_cases h1 : x₁ = e' <;> by_cases h2 : x₂ = e' <;> simp only [h1, h2, ite_true, ite_false] <;>
          aesop

private theorem two_of_two' {p q : E → Prop} {e e' : E} (hne : e ≠ e')
    (h₁ : ∀ x, x ≠ e → x ≠ e' → (p x ↔ q x)) (h₂ : ¬ q e') (h₃ : p e ∨ p e' ↔ q e)
    (h₄ : ¬ (p e ∧ p e')) :
    (∃ x₁ x₂, x₁ ≠ x₂ ∧ ∀ x, q x ↔ x = x₁ ∨ x = x₂) →
      (∃ x₁ x₂, x₁ ≠ x₂ ∧ ∀ x, p x ↔ x = x₁ ∨ x = x₂) := by
  classical
  rintro ⟨y₁, y₂, hy, hq⟩
  have hy₁ : y₁ ≠ e' := fun h => h₂ (h ▸ (hq y₁).2 (Or.inl rfl))
  have hy₂ : y₂ ≠ e' := fun h => h₂ (h ▸ (hq y₂).2 (Or.inr rfl))
  have qe := hq e
  let t : E := if p e then e else e'
  refine ⟨if y₁ = e then t else y₁, if y₂ = e then t else y₂, ?_, fun x => ?_⟩
  · by_cases h1 : y₁ = e <;> by_cases h2 : y₂ = e <;> by_cases hpe : p e <;>
      simp only [t, h1, h2, hpe, ite_true, ite_false] <;> aesop
  · by_cases hxe : x = e
    · rw [hxe]
      by_cases hpe : p e
      · have : q e := h₃.1 (Or.inl hpe)
        rw [qe] at this
        by_cases h1 : y₁ = e <;> by_cases h2 : y₂ = e <;> simp only [t, h1, h2, hpe, ite_true, ite_false] <;> aesop
      · by_cases h1 : y₁ = e <;> by_cases h2 : y₂ = e <;> simp only [t, h1, h2, hpe, ite_true, ite_false] <;> aesop
    · by_cases hxe' : x = e'
      · rw [hxe']
        by_cases hpe : p e
        · have : ¬ p e' := fun h => h₄ ⟨hpe, h⟩
          by_cases h1 : y₁ = e <;> by_cases h2 : y₂ = e <;> simp only [t, h1, h2, hpe, ite_true, ite_false] <;> aesop
        · by_cases h1 : y₁ = e <;> by_cases h2 : y₂ = e <;> simp only [t, h1, h2, hpe, ite_true, ite_false] <;> aesop
      · rw [h₁ x hxe hxe', hq]
        by_cases h1 : y₁ = e <;> by_cases h2 : y₂ = e <;> by_cases hpe : p e <;> simp only [t, h1, h2, hpe, ite_true, ite_false] <;> aesop

/-- A set that does not separate the ends of `e` from `w` is isolated after the operation exactly
when it is isolated before. -/
private theorem iso_split_iff (hne : e ≠ e') (hw : w ∈ G.int) (he : G.cls e = some .plus)
    (he' : G.cls e' = none) (ha : G.IsVtx (G.ends e).1) (hb : G.IsVtx (G.ends e).2)
    {Q : Finset V} (hsep : ¬ Sep G e w Q) :
    (G.split e e' w).IsIsolated Q ↔ G.IsIsolated Q := by
  obtain ⟨c1, c2, c3⟩ := split_crosses_e hne hw he ha hb (e' := e') Q
  have h0 : ¬ G.Crosses Q e' := fun h => h.1 he'
  unfold Sep at hsep
  have key1 : ¬ ((G.split e e' w).Crosses Q e ∧ (G.split e e' w).Crosses Q e') :=
    fun ⟨h1, h2⟩ => lg_sep1 (c1.1 h1) (c2.1 h2) hsep
  have key2 : (G.split e e' w).Crosses Q e ∨ (G.split e e' w).Crosses Q e' ↔ G.Crosses Q e := by
    constructor
    · rintro (h | h)
      · exact c3.2 (lg_sep2 (c1.1 h) hsep)
      · exact c3.2 (lg_sep3 (c2.1 h) hsep)
    · intro h
      by_cases h' : (G.ends e).1 ∈ Q ↔ w ∉ Q
      · exact Or.inl (c1.2 h')
      · exact Or.inr (c2.2 (lg_sep4 (c3.1 h) h'))
  have h₁ : ∀ x, x ≠ e → x ≠ e' → ((G.split e e' w).Crosses Q x ↔ G.Crosses Q x) :=
    fun x hx hx' => split_crosses_ne hx hx'
  unfold MGraph.IsIsolated
  rw [split_int]
  exact and_congr_right fun _ => ⟨two_of_two hne h₁ h0 key2 key1, two_of_two' hne h₁ h0 key2 key1⟩

/-- A set that separates the ends of `e` from `w` is not isolated after the operation: it is
crossed by `e`, `e'` and an edge of the black net. -/
private theorem not_iso_split (hne : e ≠ e') (hw : w ∈ G.int) (he : G.cls e = some .plus)
    (he' : G.cls e' = none) (ha : G.IsVtx (G.ends e).1) (hb : G.IsVtx (G.ends e).2)
    (hab : (G.ends e).1 ∈ G.int ∨ (G.ends e).2 ∈ G.int) (hG : G.DC)
    {Q : Finset V} (hQ : Q ⊆ G.int) (hsep : Sep G e w Q) : ¬ (G.split e e' w).IsIsolated Q := by
  obtain ⟨c1, c2, c3⟩ := split_crosses_e hne hw he ha hb (e' := e') Q
  have hl := lg_sep5 hsep
  have p1 : (G.split e e' w).Crosses Q e := c1.2 hl.1
  have p2 : (G.split e e' w).Crosses Q e' := c2.2 hl.2.1
  have nq : ¬ G.Crosses Q e := fun h => hl.2.2 (c3.1 h)
  obtain ⟨K, -, -, hK, -, hsK, -⟩ := hG
  have hne' : Q.Nonempty := by
    unfold Sep at hsep
    rcases hsep with ⟨h, -, -⟩ | ⟨-, -, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have hnot : ¬ G.int ⊆ Q := by
    unfold Sep at hsep
    rcases hsep with ⟨-, -, h⟩ | ⟨h1, h2, -⟩
    · exact fun h' => h (h' hw)
    · rcases hab with h | h
      · exact fun h' => h1 (h' h)
      · exact fun h' => h2 (h' h)
  obtain ⟨f, hf, hc, hf1, hf2, hcut⟩ := hsK Q hQ hne' hnot
  have hfd := hK f hf
  have qf : G.Crosses Q f := ⟨hc, by rw [hfd]; simp, Or.inl hf1, Or.inl hf2, hcut⟩
  have hfe : f ≠ e := fun h => nq (h ▸ qf)
  have hfe' : f ≠ e' := fun h => by rw [h, he'] at hfd; cases hfd
  rintro ⟨-, x₁, x₂, -, hx⟩
  have a1 := (hx e).1 p1
  have a2 := (hx e').1 p2
  have a3 := (hx f).1 ((split_crosses_ne hfe hfe').2 qf)
  rcases a1 with rfl | rfl <;> rcases a2 with h | h <;> rcases a3 with h' | h'
  all_goals first
    | exact hne (h.symm ▸ rfl)
    | exact hne h.symm
    | exact hfe h'
    | exact hfe' (h'.trans h.symm)
    | exact hfe (h'.trans h.symm)
    | exact hne rfl
    | skip
  all_goals subst_vars; simp_all

end Split

/-! ## The setting of operation (B) on a chain -/

/-- The setting of [II, Lemma 5.12]: the chain data of a sequentially pre-deterministic graph
without ghost edges, a blue solid edge `e`, an absent edge `e'` and an internal vertex `w`. -/
structure SC [DecidableEq V] [DecidableEq E] (G : MGraph V E) extends SplitCtx G where
  e : E
  e' : E
  w : V
  noGhost : ∀ x, G.cls x ≠ some .ghost
  ce : G.cls e = some .plus
  hne : e ≠ e'
  ce' : G.cls e' = none
  hw : w ∈ G.int

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} (S : SC G)

/-- The graph after operation (B). -/
abbrev Gt : MGraph V E := G.split S.e S.e' S.w

/-- The outer end of the diffusive crossing edge of `P (l + 1)`. -/
private abbrev u (l : ℕ) : V := G.outer (S.P (l + 1)) (S.cc l)

/-- The outer end of the other crossing edge of `P (l + 1)`. -/
private abbrev u' (l : ℕ) : V := G.outer (S.P (l + 1)) (S.cc' l)

private theorem mem_P {m : ℕ} (hm : m ≤ S.k) (v : V) : v ∈ S.P m ↔ v ∈ G.int ∧ m ≤ S.lev v :=
  S.toSplitCtx.mem_P hm v

private theorem mem_Lvl {a b : ℕ} {v : V} : v ∈ S.Lvl a b ↔ v ∈ G.int ∧ a ≤ S.lev v ∧ S.lev v < b :=
  S.toSplitCtx.mem_Lvl

private theorem e_ne_cc {l : ℕ} (hl : l < S.k) : S.e ≠ S.cc l := fun h => by
  have := S.cc_diff l hl
  rw [← h, S.ce] at this
  cases this

private theorem e'_ne_cc {l : ℕ} (hl : l < S.k) : S.e' ≠ S.cc l := fun h => by
  have := S.cc_diff l hl
  rw [← h, S.ce'] at this
  cases this

private theorem e'_ne_cc' {l : ℕ} (hl : l < S.k) : S.e' ≠ S.cc' l := fun h => by
  have := S.cc'_cls l hl
  rw [← h, S.ce'] at this
  rcases this with h | h <;> cases h

/-- The ends of the crossing edges of `P (l + 1)`: the outer end in the component `l`, the other
end in the component `l + 1`. -/
private theorem cc_ends' {l : ℕ} (hl : l < S.k) {x : E} (hx : x = S.cc l ∨ x = S.cc' l) :
    ∃ v, v ∈ G.int ∧ S.lev v = l + 1 ∧ G.outer (S.P (l + 1)) x ∈ G.int ∧
      S.lev (G.outer (S.P (l + 1)) x) = l ∧
      SameEnds (G.ends x) (G.outer (S.P (l + 1)) x, v) := by
  obtain ⟨v, hv, hlv, ho, hlo, hends⟩ := S.cc_ends l hl x hx
  refine ⟨v, hv, hlv, ho, hlo, ?_⟩
  rcases hends with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem u_mem {l : ℕ} (hl : l < S.k) : S.u l ∈ G.int ∧ S.lev (S.u l) = l := by
  obtain ⟨-, -, -, h1, h2, -⟩ := S.cc_ends' hl (Or.inl rfl)
  exact ⟨h1, h2⟩

private theorem u'_mem {l : ℕ} (hl : l < S.k) : S.u' l ∈ G.int ∧ S.lev (S.u' l) = l := by
  obtain ⟨-, -, -, h1, h2, -⟩ := S.cc_ends' hl (Or.inr (rfl : S.cc' l = S.cc' l))
  exact ⟨h1, h2⟩

/-- An edge between two internal vertices of different components is a crossing edge of the
chain, between the components `l` and `l + 1`. -/
private theorem jump' {x : E} (hc : G.cls x ≠ none) (hm : G.cls x ≠ some .minus)
    (h1 : (G.ends x).1 ∈ G.int) (h2 : (G.ends x).2 ∈ G.int)
    (hne : S.lev (G.ends x).1 ≠ S.lev (G.ends x).2) :
    ∃ l < S.k, (x = S.cc l ∨ x = S.cc' l) ∧
      ((S.lev (G.ends x).1 = l ∧ S.lev (G.ends x).2 = l + 1) ∨
        (S.lev (G.ends x).1 = l + 1 ∧ S.lev (G.ends x).2 = l)) := by
  obtain ⟨l, hl, hx⟩ := S.jump x hc hm h1 h2 hne
  obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hl hx
  exact ⟨l, hl, hx, h⟩

/-- A blue solid edge between internal vertices joins vertices of one component or of two
consecutive components. -/
private theorem lev_plus {x : E} (hx : G.cls x = some .plus) (h1 : (G.ends x).1 ∈ G.int)
    (h2 : (G.ends x).2 ∈ G.int) :
    S.lev (G.ends x).1 = S.lev (G.ends x).2 ∨ ∃ l < S.k, x = S.cc' l ∧
      ((S.lev (G.ends x).1 = l ∧ S.lev (G.ends x).2 = l + 1) ∨
        (S.lev (G.ends x).1 = l + 1 ∧ S.lev (G.ends x).2 = l)) := by
  by_cases h : S.lev (G.ends x).1 = S.lev (G.ends x).2
  · exact Or.inl h
  · obtain ⟨l, hl, hx', hlv⟩ := S.jump' (by rw [hx]; simp) (by rw [hx]; simp) h1 h2 h
    refine Or.inr ⟨l, hl, ?_, hlv⟩
    rcases hx' with rfl | rfl
    · rw [S.cc_diff l hl] at hx; cases hx
    · rfl

/-- The crossing edges of different members of the chain are different. -/
private theorem cc_inj {l l' : ℕ} (hl : l < S.k) (hl' : l' < S.k) {x : E} (hx : x = S.cc l ∨ x = S.cc' l)
    (hx' : x = S.cc l' ∨ x = S.cc' l') : l = l' := by
  obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hl hx
  obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hl' hx'
  omega

/-! ### The graphs of the components -/

/-- The graph of the component `l` of the chain: `P (l + 1)` and its two external edges replaced
by one `Θ` edge carrying the index `cc l`. -/
private abbrev R (l : ℕ) : MGraph V E := G.replace (S.P l) (S.P (l + 1)) (S.cc l) (S.cc' l)

/-- The graph of the last component, or of the component `b` with `P (b + 1)` and its two
external edges `x₁`, `x₂` replaced by one `Θ` edge: its internal vertices are those of the
component, its edges those of `G` inside the component and the `Θ` edge. -/
structure IsB (Z : MGraph V E) (b : ℕ) (x₁ x₂ : E) : Prop where
  int : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ S.lev v = b
  pres : ∀ x, Z.cls x ≠ none → (b < S.k ∧ x = x₁ ∧ Z.cls x = some .diff ∧
      Z.ends x = (G.outer (S.P (b + 1)) x₁, G.outer (S.P (b + 1)) x₂)) ∨
    ((b < S.k → x ≠ x₁ ∧ x ≠ x₂) ∧ (G.ends x).1 ∈ G.int ∧ S.lev (G.ends x).1 = b ∧
      (G.ends x).2 ∈ G.int ∧ S.lev (G.ends x).2 = b ∧ Z.cls x = G.cls x ∧ Z.ends x = G.ends x)
  ip : ∀ x, Z.IsIntPlus x ↔ G.cls x = some .plus ∧ (G.ends x).1 ∈ G.int ∧
    S.lev (G.ends x).1 = b ∧ (G.ends x).2 ∈ G.int ∧ S.lev (G.ends x).2 = b
  x12 : b < S.k → (x₁ = S.cc b ∨ x₁ = S.cc' b) ∧ (x₂ = S.cc b ∨ x₂ = S.cc' b) ∧ x₁ ≠ x₂

private theorem mem_sdiff_P {a b : ℕ} (hab : a ≤ b) (hb : b < S.k) (v : V) :
    v ∈ S.P a \ S.P (b + 1) ↔ v ∈ G.int ∧ a ≤ S.lev v ∧ S.lev v ≤ b := by
  rw [Finset.mem_sdiff, S.mem_P (by omega), S.mem_P hb]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, by by_contra h; exact h3 ⟨h1, by omega⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun ⟨_, h⟩ => by omega⟩

private theorem isB_replace {b : ℕ} (hb : b < S.k) {x₁ x₂ : E} (hx₁ : x₁ = S.cc b ∨ x₁ = S.cc' b)
    (hx₂ : x₂ = S.cc b ∨ x₂ = S.cc' b) (hne : x₁ ≠ x₂) :
    S.IsB (G.replace (S.P b) (S.P (b + 1)) x₁ x₂) b x₁ x₂ := by
  have hint : ∀ v, v ∈ S.P b \ S.P (b + 1) ↔ v ∈ G.int ∧ S.lev v = b := by
    intro v
    rw [S.mem_sdiff_P le_rfl hb]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, by omega⟩
  have hcl : ∀ x, x ≠ x₁ → x ≠ x₂ → (G.replace (S.P b) (S.P (b + 1)) x₁ x₂).cls x =
      if (G.ends x).1 ∈ S.P b \ S.P (b + 1) ∧ (G.ends x).2 ∈ S.P b \ S.P (b + 1) then
        G.cls x else none := by
    intro x h1 h2
    simp [MGraph.replace, MGraph.induce, h1, h2]
  have hen : ∀ x, x ≠ x₁ → (G.replace (S.P b) (S.P (b + 1)) x₁ x₂).ends x = G.ends x := by
    intro x h1
    simp [MGraph.replace, h1]
  refine ⟨hint, fun x hx => ?_, fun x => ?_, fun _ => ⟨hx₁, hx₂, hne⟩⟩
  · by_cases h1 : x = x₁
    · subst h1
      exact Or.inl ⟨hb, rfl, by simp [MGraph.replace], by simp [MGraph.replace]⟩
    · by_cases h2 : x = x₂
      · subst h2; simp [MGraph.replace, h1] at hx
      · rw [hcl x h1 h2] at hx
        split_ifs at hx with hin
        · obtain ⟨a1, a2⟩ := (hint _).1 hin.1
          obtain ⟨b1, b2⟩ := (hint _).1 hin.2
          refine Or.inr ⟨fun _ => ⟨h1, h2⟩, a1, a2, b1, b2, ?_, hen x h1⟩
          rw [hcl x h1 h2, if_pos hin]
        · exact absurd rfl hx
  · have hcr : ∀ y, (y = S.cc b ∨ y = S.cc' b) → ¬ (S.lev (G.ends y).1 = b ∧
        S.lev (G.ends y).2 = b) := by
      intro y hy ⟨h1, h2⟩
      obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hb hy
      omega
    unfold MGraph.IsIntPlus
    rw [MGraph.replace]
    simp only
    by_cases h1 : x = x₁
    · subst h1
      simp only [if_true]
      constructor
      · rintro ⟨h, -⟩; cases h
      · exact fun ⟨_, _, a, _, b'⟩ => absurd ⟨a, b'⟩ (hcr x hx₁)
    · by_cases h2 : x = x₂
      · subst h2
        simp only [h1, if_false, if_true]
        constructor
        · rintro ⟨h, -⟩; cases h
        · exact fun ⟨_, _, a, _, b'⟩ => absurd ⟨a, b'⟩ (hcr x hx₂)
      · simp only [h1, h2, if_false, MGraph.induce, hint]
        constructor
        · rintro ⟨h, -, -⟩
          split_ifs at h with hin
          · exact ⟨h, hin.1.1, hin.1.2, hin.2.1, hin.2.2⟩
        · rintro ⟨h, a1, a2, b1, b2⟩
          rw [if_pos ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩]
          exact ⟨h, ⟨a1, a2⟩, ⟨b1, b2⟩⟩

private theorem isB_induce (x₁ x₂ : E) : S.IsB (G.induce (S.P S.k)) S.k x₁ x₂ := by
  have hint : ∀ v, v ∈ S.P S.k ↔ v ∈ G.int ∧ S.lev v = S.k := by
    intro v
    rw [S.mem_P le_rfl]
    have := S.lev_le v
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  refine ⟨hint, fun x hx => ?_, fun x => ?_, fun h => absurd h (lt_irrefl _)⟩
  · by_cases hin : (G.ends x).1 ∈ S.P S.k ∧ (G.ends x).2 ∈ S.P S.k
    · obtain ⟨a1, a2⟩ := (hint _).1 hin.1
      obtain ⟨b1, b2⟩ := (hint _).1 hin.2
      exact Or.inr ⟨fun h => absurd h (lt_irrefl _), a1, a2, b1, b2,
        by simp [MGraph.induce, hin], rfl⟩
    · simp [MGraph.induce, hin] at hx
  · unfold MGraph.IsIntPlus
    simp only [MGraph.induce, hint]
    constructor
    · rintro ⟨h, -, -⟩
      split_ifs at h with hin
      exact ⟨h, hin.1.1, hin.1.2, hin.2.1, hin.2.2⟩
    · rintro ⟨h, a1, a2, b1, b2⟩
      rw [if_pos ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩]
      exact ⟨h, ⟨a1, a2⟩, ⟨b1, b2⟩⟩

private theorem isB_R {c : ℕ} (hc : c < S.k) : S.IsB (S.R c) c (S.cc c) (S.cc' c) :=
  S.isB_replace hc (Or.inl rfl) (Or.inr rfl) (S.cc_ne c hc)

/-- The graph of the component `c < k`, with any order of the two crossing edges, is
pre-deterministic ([II, Def 5.9 (iii)]). -/
private theorem preDet_replace {c : ℕ} (hc : c < S.k) {x₁ x₂ : E} (hx₁ : x₁ = S.cc c ∨ x₁ = S.cc' c)
    (hx₂ : x₂ = S.cc c ∨ x₂ = S.cc' c) (hne : x₁ ≠ x₂) :
    (G.replace (S.P c) (S.P (c + 1)) x₁ x₂).PreDet :=
  S.spd.2.2.2 _ _ _ _ (chain_isoOrTop S.chain hc.le) (S.chain.2.1 c hc) hne
    ((S.cross c hc x₁).2 hx₁) ((S.cross c hc x₂).2 hx₂)

private theorem preDet_R {c : ℕ} (hc : c < S.k) : (S.R c).PreDet :=
  S.preDet_replace hc (Or.inl rfl) (Or.inr rfl) (S.cc_ne c hc)

/-- The subgraph induced on the last member of the chain is pre-deterministic. -/
private theorem preDet_last : (G.induce (S.P S.k)).PreDet :=
  S.spd.2.2.1 _ (chain_isoOrTop S.chain le_rfl) S.chain.2.2

/-- A pre-deterministic order of the graph of the component `c < k`. -/
private def ordR (c : ℕ) : List E :=
  if h : c < S.k then Classical.choose (S.preDet_R h).2 else []

private theorem ordR_spec {c : ℕ} (hc : c < S.k) : (S.R c).IsPDOrder (S.ordR c) := by
  have := Classical.choose_spec (S.preDet_R hc).2
  simp only [ordR, hc, dif_pos]
  exact this

/-- The edges of the order of the component `c`: the blue solid edges inside the component. -/
private theorem mem_ordR {c : ℕ} (hc : c < S.k) (x : E) : x ∈ S.ordR c ↔ G.cls x = some .plus ∧
    (G.ends x).1 ∈ G.int ∧ S.lev (G.ends x).1 = c ∧ (G.ends x).2 ∈ G.int ∧
      S.lev (G.ends x).2 = c :=
  ((S.ordR_spec hc).2.1 x).trans ((S.isB_R hc).ip x)

/-! ### The graphs of [II, Lemma 5.12] after operation (B) -/

/-- The graph on the components `a, …, b` after operation (B): the subgraph induced on `P a`
(for `b = k`), or the graph with `P (b + 1)` and its two external edges `x₁`, `x₂` replaced by one
`Θ` edge (for `b < k`). -/
structure IsX (Z : MGraph V E) (a b : ℕ) (x₁ x₂ : E) : Prop where
  int : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ a ≤ S.lev v ∧ S.lev v ≤ b
  gen : ∀ x, (b < S.k → x ≠ x₁ ∧ x ≠ x₂) → Z.ends x = S.Gt.ends x ∧
    Z.cls x = if (S.Gt.ends x).1 ∈ Z.int ∧ (S.Gt.ends x).2 ∈ Z.int then S.Gt.cls x else none
  th : b < S.k → x₁ ≠ x₂ ∧ Z.cls x₁ = some .diff ∧ Z.cls x₂ = none ∧
    Z.ends x₁ = (S.Gt.outer (S.P (b + 1)) x₁, S.Gt.outer (S.P (b + 1)) x₂) ∧
    S.Gt.Crosses (S.P (b + 1)) x₁ ∧ S.Gt.Crosses (S.P (b + 1)) x₂

private theorem isX_replace {a b : ℕ} (hab : a ≤ b) (hb : b < S.k) {x₁ x₂ : E} (hne : x₁ ≠ x₂)
    (h₁ : S.Gt.Crosses (S.P (b + 1)) x₁) (h₂ : S.Gt.Crosses (S.P (b + 1)) x₂) :
    S.IsX (S.Gt.replace (S.P a) (S.P (b + 1)) x₁ x₂) a b x₁ x₂ := by
  refine ⟨fun v => S.mem_sdiff_P hab hb v, fun x hx => ?_, fun _ => ⟨hne, ?_, ?_, ?_, h₁, h₂⟩⟩
  · obtain ⟨n1, n2⟩ := hx hb
    simp [MGraph.replace, MGraph.induce, n1, n2]
  · simp [MGraph.replace]
  · simp [MGraph.replace, hne.symm]
  · simp [MGraph.replace]

private theorem isX_induce {a : ℕ} (ha : a ≤ S.k) (x₁ x₂ : E) :
    S.IsX (S.Gt.induce (S.P a)) a S.k x₁ x₂ := by
  refine ⟨fun v => ?_, fun x _ => ⟨rfl, rfl⟩, fun h => absurd h (lt_irrefl _)⟩
  change v ∈ S.P a ↔ _
  rw [S.mem_P ha]
  have := S.lev_le v
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, this⟩
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩

variable {S}

/-- An edge of `G` other than `e`, `e'` between internal vertices of the components `a, …, b`, not
crossing `P (b + 1)`, is an edge of the graph after operation (B) with its class and ends. -/
private theorem IsX.edge {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂) {x : E}
    (hxe : x ≠ S.e) (hxe' : x ≠ S.e') (h1 : (G.ends x).1 ∈ G.int) (h1a : a ≤ S.lev (G.ends x).1)
    (h1b : S.lev (G.ends x).1 ≤ b) (h2 : (G.ends x).2 ∈ G.int) (h2a : a ≤ S.lev (G.ends x).2)
    (h2b : S.lev (G.ends x).2 ≤ b) : Z.ends x = G.ends x ∧ Z.cls x = G.cls x := by
  have hn : b < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
    intro hb
    obtain ⟨-, -, -, -, c1, c2⟩ := hZ.th hb
    have nc : ¬ S.Gt.Crosses (S.P (b + 1)) x := by
      rintro ⟨-, -, -, -, hcut⟩
      unfold MGraph.Cut at hcut
      rw [split_ends_ne hxe hxe', S.mem_P hb, S.mem_P hb] at hcut
      omega
    exact ⟨fun h => nc (h ▸ c1), fun h => nc (h ▸ c2)⟩
  obtain ⟨he, hc⟩ := hZ.gen x hn
  rw [split_ends_ne hxe hxe'] at he
  refine ⟨he, ?_⟩
  rw [hc, split_ends_ne hxe hxe', split_cls_ne hxe', if_pos ⟨(hZ.int _).2 ⟨h1, h1a, h1b⟩,
    (hZ.int _).2 ⟨h2, h2a, h2b⟩⟩]

/-- The subgraph induced on the components `c + 1, …, b` of the graph after operation (B), with
blue solid edges changed into `Θ` edges, is doubly connected, if `e` does not join two of these
components. -/
private theorem IsX.dc_lower {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂) {c : ℕ}
    (hac : a ≤ c) (hcb : c < b) (hbk : b ≤ S.k)
    (he : ¬ ((G.ends S.e).1 ∈ S.Lvl (c + 1) (b + 1) ∧ (G.ends S.e).2 ∈ S.Lvl (c + 1) (b + 1)))
    (l : List E) : ((Z.convert l).induce (S.Lvl (c + 1) (b + 1))).DC := by
  refine dc_le (S.toSplitCtx.dc_Lvl (b + 1) (by omega)) ⟨rfl, fun x hx => ?_⟩
  obtain ⟨hc, h1, h2, -⟩ := hx
  have hin : (G.ends x).1 ∈ S.Lvl (c + 1) (b + 1) ∧ (G.ends x).2 ∈ S.Lvl (c + 1) (b + 1) := by
    by_contra hn
    simp [MGraph.induce, hn] at hc
  have hG : (G.induce (S.Lvl (c + 1) (b + 1))).cls x = G.cls x := by
    simp [MGraph.induce, hin]
  rw [hG] at hc ⊢
  have hxe : x ≠ S.e := fun h => he (h ▸ hin)
  have hxe' : x ≠ S.e' := fun h => hc (h ▸ S.ce')
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  obtain ⟨hze, hzc⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
  have hzin : (Z.ends x).1 ∈ S.Lvl (c + 1) (b + 1) ∧ (Z.ends x).2 ∈ S.Lvl (c + 1) (b + 1) := by
    rw [hze]; exact hin
  refine ⟨?_, ?_⟩
  · simp only [id, MGraph.induce, convert_ends, hzin, and_self, if_true]
    rw [convert_cls, hzc]
    split_ifs with h
    · exact Or.inr ⟨h.2, rfl⟩
    · exact Or.inl rfl
  · simp only [id, MGraph.induce, convert_ends, hze]
    exact sameEnds_refl _

end SC

/-! ## The graphs of [II, Claims A.3–A.7] -/

section Claims

variable [DecidableEq V] [DecidableEq E]

private theorem addInt_cls (X : MGraph V E) (N : V) : (X.addInt N).cls = X.cls := rfl
private theorem addInt_ends (X : MGraph V E) (N : V) : (X.addInt N).ends = X.ends := rfl

private theorem setEdge_cls (X : MGraph V E) (f : E) (u v : V) (c : Option MClass) (x : E) :
    (X.setEdge f u v c).cls x = if x = f then c else X.cls x := by
  simp [MGraph.setEdge, Function.update_apply]

private theorem setEdge_ends (X : MGraph V E) (f : E) (u v : V) (c : Option MClass) (x : E) :
    (X.setEdge f u v c).ends x = if x = f then (u, v) else X.ends x := rfl

/-- The graph of [II, Claim A.3]. -/
private abbrev gA3 (X : MGraph V E) (N M₁ M₂ : V) (b b₁ b₂ b₄ : E) : MGraph V E :=
  (((X.addInt N).split b b₄ N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂ (some .plus)

/-- The graph of [II, Claim A.6]. -/
private abbrev gA6 (X : MGraph V E) (N M₁ M₂ M₃ : V) (b₁ b₂ b₃ : E) : MGraph V E :=
  (((X.addInt N).setEdge b₁ N M₁ (some .diff)).setEdge b₂ N M₂ (some .plus)).setEdge b₃ N M₃
    (some .plus)

/-- The graph of [II, Claim A.7]. -/
private abbrev gA7 (X : MGraph V E) (N M₃ : V) (b₀ b₂ b₃ : E) : MGraph V E :=
  ((X.addInt N).split b₀ b₂ N).setEdge b₃ N M₃ (some .diff)

private theorem twoSplit_int (X : MGraph V E) (N : V) (b₀ b₂ b b₄ : E) :
    (X.twoSplit N b₀ b₂ b b₄).int = insert N X.int := rfl

private theorem twoSplit_cls (X : MGraph V E) (N : V) (b₀ b₂ b b₄ : E) (x : E) :
    (X.twoSplit N b₀ b₂ b b₄).cls x = if x = b₄ then (if b = b₂ then X.cls b₀ else X.cls b) else
      if x = b₂ then X.cls b₀ else X.cls x := by
  simp only [MGraph.twoSplit, split_cls, addInt_cls]

private theorem twoSplit_ends (X : MGraph V E) (N : V) (b₀ b₂ b b₄ : E) (x : E) :
    (X.twoSplit N b₀ b₂ b b₄).ends x =
      if x = b then ((if b = b₀ then ((X.ends b₀).1, N) else if b = b₂ then (N, (X.ends b₀).2)
        else X.ends b).1, N) else
      if x = b₄ then (N, (if b = b₀ then ((X.ends b₀).1, N) else if b = b₂ then
        (N, (X.ends b₀).2) else X.ends b).2) else
      if x = b₀ then ((X.ends b₀).1, N) else if x = b₂ then (N, (X.ends b₀).2) else X.ends x := by
  simp only [MGraph.twoSplit, split_ends, addInt_ends]

section TwoSplit

variable {X : MGraph V E} {N : V} {b₀ b₂ b b₄ : E} (h02 : b₀ ≠ b₂) (h0b : b₀ ≠ b) (h04 : b₀ ≠ b₄)
  (h2b : b₂ ≠ b) (h24 : b₂ ≠ b₄) (hb4 : b ≠ b₄)
include h02 h0b h04 h2b h24 hb4

private theorem ts_cls_b₂ : (X.twoSplit N b₀ b₂ b b₄).cls b₂ = X.cls b₀ := by
  rw [twoSplit_cls, if_neg h24, if_pos rfl]

private theorem ts_cls_b₄ : (X.twoSplit N b₀ b₂ b b₄).cls b₄ = X.cls b := by
  rw [twoSplit_cls, if_pos rfl, if_neg h2b.symm]

private theorem ts_cls_of {x : E} (hx2 : x ≠ b₂) (hx4 : x ≠ b₄) :
    (X.twoSplit N b₀ b₂ b b₄).cls x = X.cls x := by
  rw [twoSplit_cls, if_neg hx4, if_neg hx2]

private theorem ts_ends_b₀ : (X.twoSplit N b₀ b₂ b b₄).ends b₀ = ((X.ends b₀).1, N) := by
  rw [twoSplit_ends, if_neg h0b, if_neg h04, if_pos rfl]

private theorem ts_ends_b₂ : (X.twoSplit N b₀ b₂ b b₄).ends b₂ = (N, (X.ends b₀).2) := by
  rw [twoSplit_ends, if_neg h2b, if_neg h24, if_neg h02.symm, if_pos rfl]

private theorem ts_ends_b : (X.twoSplit N b₀ b₂ b b₄).ends b = ((X.ends b).1, N) := by
  rw [twoSplit_ends, if_pos rfl, if_neg h0b.symm, if_neg h2b.symm]

private theorem ts_ends_b₄ : (X.twoSplit N b₀ b₂ b b₄).ends b₄ = (N, (X.ends b).2) := by
  rw [twoSplit_ends, if_neg hb4.symm, if_pos rfl, if_neg h0b.symm, if_neg h2b.symm]

private theorem ts_ends_of {x : E} (hx0 : x ≠ b₀) (hx2 : x ≠ b₂) (hxb : x ≠ b) (hx4 : x ≠ b₄) :
    (X.twoSplit N b₀ b₂ b b₄).ends x = X.ends x := by
  rw [twoSplit_ends, if_neg hxb, if_neg hx4, if_neg hx0, if_neg hx2]

end TwoSplit

section GA67

variable (X : MGraph V E) (N M₁ M₂ M₃ : V) {b₀ b₁ b₂ b₃ : E}

private theorem gA6_int : (gA6 X N M₁ M₂ M₃ b₁ b₂ b₃).int = insert N X.int := rfl

private theorem gA6_cls (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃) (x : E) :
    (gA6 X N M₁ M₂ M₃ b₁ b₂ b₃).cls x = if x = b₃ then some .plus else if x = b₂ then some .plus
      else if x = b₁ then some .diff else X.cls x := by
  simp only [gA6, setEdge_cls, addInt_cls]

private theorem gA6_ends (x : E) :
    (gA6 X N M₁ M₂ M₃ b₁ b₂ b₃).ends x = if x = b₃ then (N, M₃) else if x = b₂ then (N, M₂)
      else if x = b₁ then (N, M₁) else X.ends x := by
  simp only [gA6, setEdge_ends, addInt_ends]

private theorem gA7_int : (gA7 X N M₃ b₀ b₂ b₃).int = insert N X.int := rfl

private theorem gA7_cls (x : E) :
    (gA7 X N M₃ b₀ b₂ b₃).cls x = if x = b₃ then some .diff else if x = b₂ then X.cls b₀
      else X.cls x := by
  simp only [gA7, setEdge_cls, split_cls, addInt_cls]

private theorem gA7_ends (x : E) :
    (gA7 X N M₃ b₀ b₂ b₃).ends x = if x = b₃ then (N, M₃) else if x = b₀ then ((X.ends b₀).1, N)
      else if x = b₂ then (N, (X.ends b₀).2) else X.ends x := by
  simp only [gA7, setEdge_ends, split_ends, addInt_ends]

end GA67

end Claims

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-- An edge of the graph after operation (B) between internal vertices of the components
`a, …, b` keeps its class and ends. -/
private theorem IsX.gedge {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂) {x : E}
    (h1 : (S.Gt.ends x).1 ∈ G.int) (h1a : a ≤ S.lev (S.Gt.ends x).1)
    (h1b : S.lev (S.Gt.ends x).1 ≤ b) (h2 : (S.Gt.ends x).2 ∈ G.int)
    (h2a : a ≤ S.lev (S.Gt.ends x).2) (h2b : S.lev (S.Gt.ends x).2 ≤ b) :
    Z.ends x = S.Gt.ends x ∧ Z.cls x = S.Gt.cls x := by
  have hn : b < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
    intro hb
    obtain ⟨-, -, -, -, c1, c2⟩ := hZ.th hb
    have nc : ¬ S.Gt.Crosses (S.P (b + 1)) x := by
      rintro ⟨-, -, -, -, hcut⟩
      unfold MGraph.Cut at hcut
      rw [S.mem_P hb, S.mem_P hb] at hcut
      omega
    exact ⟨fun h => nc (h ▸ c1), fun h => nc (h ▸ c2)⟩
  obtain ⟨he, hc⟩ := hZ.gen x hn
  refine ⟨he, ?_⟩
  rw [hc, if_pos ⟨(hZ.int _).2 ⟨h1, h1a, h1b⟩, (hZ.int _).2 ⟨h2, h2a, h2b⟩⟩]

/-- The internal vertices of the graph after operation (B) on the components `a, …, b`, with the
components `c + 1, …, b` collapsed to `w`. -/
private theorem IsX.collapse_int {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂)
    {c : ℕ} (hac : a ≤ c) (hcb : c < b) (hw1 : c + 1 ≤ S.lev S.w) (hw2 : S.lev S.w ≤ b) :
    (Z.collapse (S.Lvl (c + 1) (b + 1)) S.w).int = insert S.w (S.Lvl a (c + 1)) := by
  have hL : S.Lvl (c + 1) (b + 1) ⊆ Z.int := fun v hv => by
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    exact (hZ.int v).2 ⟨h1, by omega, by omega⟩
  have hwL : S.w ∈ S.Lvl (c + 1) (b + 1) := S.mem_Lvl.2 ⟨S.hw, hw1, by omega⟩
  ext v
  rw [mem_collapse_int hL hwL, Finset.mem_insert, S.mem_Lvl, hZ.int, S.mem_Lvl]
  constructor
  · rintro (h | ⟨⟨h1, h2, h3⟩, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, by by_contra h; exact h4 ⟨h1, by omega, by omega⟩⟩
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨h1, h2, by omega⟩, fun ⟨_, h, _⟩ => by omega⟩

private theorem collapse_convert_ends (Z : MGraph V E) (l : List E) (L : Finset V) (w : V) (x : E) :
    ((Z.convert l).collapse L w).ends x =
      (if (Z.ends x).1 ∈ L then w else (Z.ends x).1, if (Z.ends x).2 ∈ L then w else (Z.ends x).2) :=
  rfl

/-- An edge not among `l` keeps its class when the edges of `l` are changed into `Θ` edges. -/
private theorem convert_cls_of_not_mem {X : MGraph V E} {l : List E} {x : E} (h : x ∉ l) :
    (X.convert l).cls x = X.cls x := by
  rw [convert_cls, if_neg (fun h' => h h'.1)]

/-- The setting of case (i) of [II, Lemma 5.12]: the ends of `e` in the component `i`, `w` in the
component `j > i`. -/
structure CaseI (S : SC G) (i j : ℕ) : Prop where
  hij : i < j
  hjk : j ≤ S.k
  ha : (G.ends S.e).1 ∈ G.int
  hla : S.lev (G.ends S.e).1 = i
  hb : (G.ends S.e).2 ∈ G.int
  hlb : S.lev (G.ends S.e).2 = i
  hlw : S.lev S.w = j

private theorem CaseI.e_ne_cc' {i j : ℕ} (hC : S.CaseI i j) {l : ℕ} (hl : l < S.k) : S.e ≠ S.cc' l := by
  intro h
  obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hl (Or.inr h)
  have := hC.hla
  have := hC.hlb
  omega

/-- The ends of a crossing edge of `P (l + 1)` after the components from `l + 1` on are collapsed
to `w`: the outer end and `w`. -/
private theorem cc_collapse {l b : ℕ} (hl : l < S.k) (hlb : l < b) {x : E}
    (hx : x = S.cc l ∨ x = S.cc' l) :
    SameEnds ((if (G.ends x).1 ∈ S.Lvl (l + 1) (b + 1) then S.w else (G.ends x).1,
      if (G.ends x).2 ∈ S.Lvl (l + 1) (b + 1) then S.w else (G.ends x).2))
      (S.w, G.outer (S.P (l + 1)) x) := by
  obtain ⟨v, hv, hlv, ho, hlo, hse⟩ := S.cc_ends' hl hx
  have hvL : v ∈ S.Lvl (l + 1) (b + 1) := S.mem_Lvl.2 ⟨hv, by omega, by omega⟩
  have hoL : G.outer (S.P (l + 1)) x ∉ S.Lvl (l + 1) (b + 1) := fun h => by
    have := (S.mem_Lvl.1 h).2.1; omega
  rcases sameEnds_iff.1 hse with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · rw [if_pos hvL, if_neg hoL]; exact Or.inr rfl
  · rw [if_pos hvL, if_neg hoL]; exact Or.inl rfl

/-- The quotient graph at the component `c` of case (i) contains the graph of [II, Claim A.3]
built on the subgraph induced on the components `i, …, c`. -/
private theorem CaseI.le_A3 {i j : ℕ} (hC : S.CaseI i j) {Z : MGraph V E} {x₁ x₂ : E}
    (hZ : S.IsX Z i j x₁ x₂) {c : ℕ} (hic : i ≤ c) (hcj : c < j) {l : List E}
    (hl : ∀ y ∈ l, (Z.ends y).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (c + 1) (j + 1))
    (hp : G.cls (S.cc' c) = some .plus) :
    Le (gA3 (G.induce (S.Lvl i (c + 1))) S.w (S.u c) (S.u' c) S.e (S.cc c) (S.cc' c) S.e')
      ((Z.convert l).collapse (S.Lvl (c + 1) (j + 1)) S.w) := by
  have hck : c < S.k := by have := hC.hjk; omega
  set L := S.Lvl (c + 1) (j + 1) with hLdef
  have notL : ∀ v, S.lev v ≤ c → v ∉ L := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have nl : ∀ y, ¬ ((Z.ends y).1 ∈ L ∧ (Z.ends y).2 ∈ L) → y ∉ l := fun y h h' => h (hl y h')
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have ec := S.e_ne_cc hck
  have ec' := hC.e_ne_cc' hck
  have e'c := S.e'_ne_cc hck
  have e'c' := S.e'_ne_cc' hck
  have cc := S.cc_ne c hck
  refine ⟨?_, fun x hx => ?_⟩
  · change insert S.w (S.Lvl i (c + 1)) = _
    rw [collapse_convert, convert_int, hZ.collapse_int hic hcj (by omega) (by omega)]
  -- the crossing edges of `P (c + 1)`
  have hcross : ∀ y, (y = S.cc c ∨ y = S.cc' c) → Z.ends y = G.ends y ∧ Z.cls y = G.cls y ∧
      y ∉ l := by
    intro y hy
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hck hy
    have hye : y ≠ S.e := by rcases hy with rfl | rfl; exacts [ec.symm, ec'.symm]
    have hye' : y ≠ S.e' := by rcases hy with rfl | rfl; exacts [e'c.symm, e'c'.symm]
    obtain ⟨h1, h2⟩ := hZ.edge hye hye' g1 (by omega) (by omega) g2 (by omega) (by omega)
    refine ⟨h1, h2, nl y ?_⟩
    rw [h1]
    rintro ⟨a1, a2⟩
    rcases g3 with ⟨g3, -⟩ | ⟨-, g3⟩
    · exact notL _ (by omega) a1
    · exact notL _ (by omega) a2
  simp only [id]
  rw [collapse_cls, collapse_convert_ends]
  by_cases h1 : x = S.cc' c
  · subst h1
    obtain ⟨e1, e2, e3⟩ := hcross _ (Or.inr rfl)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls_of_not_mem e3, e2, hp, setEdge_cls, if_pos rfl]
    · rw [e1, setEdge_ends, if_pos rfl]
      exact cc_collapse hck hcj (Or.inr rfl)
  by_cases h2 : x = S.cc c
  · subst h2
    obtain ⟨e1, e2, e3⟩ := hcross _ (Or.inl rfl)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls_of_not_mem e3, e2, S.cc_diff c hck, setEdge_cls, if_neg cc, setEdge_cls,
        if_pos rfl]
    · rw [e1, setEdge_ends, if_neg cc, setEdge_ends, if_pos rfl]
      exact cc_collapse hck hcj (Or.inl rfl)
  have hT : ∀ y, y ≠ S.cc' c → y ≠ S.cc c →
      (gA3 (G.induce (S.Lvl i (c + 1))) S.w (S.u c) (S.u' c) S.e (S.cc c) (S.cc' c) S.e').cls y =
        ((G.induce (S.Lvl i (c + 1))).split S.e S.e' S.w).cls y ∧
      (gA3 (G.induce (S.Lvl i (c + 1))) S.w (S.u c) (S.u' c) S.e (S.cc c) (S.cc' c) S.e').ends y =
        ((G.induce (S.Lvl i (c + 1))).split S.e S.e' S.w).ends y := by
    intro y n1 n2
    rw [setEdge_cls, if_neg n1, setEdge_cls, if_neg n2, setEdge_ends, if_neg n1, setEdge_ends,
      if_neg n2]
    exact ⟨rfl, rfl⟩
  obtain ⟨t1, t2⟩ := hT x h1 h2
  rw [t1, t2]
  have aL : (G.ends S.e).1 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.ha, by omega, by omega⟩
  have bL : (G.ends S.e).2 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.hb, by omega, by omega⟩
  have hGe : (G.induce (S.Lvl i (c + 1))).cls S.e = some .plus := by
    simp [MGraph.induce, aL, bL, S.ce]
  -- the edges `e`, `e'` of the path through `w`
  have hpath : ∀ y, (y = S.e ∨ y = S.e') → Z.ends y = S.Gt.ends y ∧ Z.cls y = some .plus ∧
      y ∉ l := by
    intro y hy
    have hge : S.Gt.ends S.e = ((G.ends S.e).1, S.w) := split_ends_e
    have hge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
    have hgc : S.Gt.cls y = some .plus := by
      rcases hy with rfl | rfl
      · rw [split_cls_of S.hne, S.ce]
      · rw [split_cls_e', S.ce]
    rcases hy with rfl | rfl
    · obtain ⟨z1, z2⟩ := hZ.gedge (x := S.e) (by rw [hge]; exact hC.ha) (by rw [hge]; dsimp only; omega)
        (by rw [hge]; dsimp only; omega) (by rw [hge]; exact S.hw) (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega)
      refine ⟨z1, z2.trans hgc, nl _ ?_⟩
      rw [z1, hge]; dsimp only; exact fun h => notL _ (by omega) h.1
    · obtain ⟨z1, z2⟩ := hZ.gedge (x := S.e') (by rw [hge']; exact S.hw) (by rw [hge']; dsimp only; omega)
        (by rw [hge']; dsimp only; omega) (by rw [hge']; exact hC.hb) (by rw [hge']; dsimp only; omega)
        (by rw [hge']; dsimp only; omega)
      refine ⟨z1, z2.trans hgc, nl _ ?_⟩
      rw [z1, hge']; dsimp only; exact fun h => notL _ (by omega) h.2
  have hwL : S.w ∈ L := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  have haL : (G.ends S.e).1 ∉ L := notL _ (by omega)
  have hbL : (G.ends S.e).2 ∉ L := notL _ (by omega)
  by_cases h3 : x = S.e
  · subst h3
    obtain ⟨z1, z2, z3⟩ := hpath _ (Or.inl rfl)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls_of_not_mem z3, z2, split_cls_of S.hne, hGe]
    · rw [z1, split_ends_e, split_ends_e]
      simp only [MGraph.induce, haL, hwL, ↓reduceIte]
      exact sameEnds_refl _
  by_cases h4 : x = S.e'
  · subst h4
    obtain ⟨z1, z2, z3⟩ := hpath _ (Or.inr rfl)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls_of_not_mem z3, z2, split_cls_e', hGe]
    · rw [z1, split_ends_e' S.hne, split_ends_e' S.hne]
      simp only [MGraph.induce, hbL, hwL, ↓reduceIte]
      exact sameEnds_refl _
  -- the other edges: those of `G` between the components `i, …, c`
  rw [split_cls_ne h4, split_ends_ne h3 h4]
  have hc : (G.induce (S.Lvl i (c + 1))).cls x ≠ none := by
    obtain ⟨hc, -⟩ := hx
    rw [hT x h1 h2 |>.1, split_cls_ne h4] at hc
    exact hc
  have hin : (G.ends x).1 ∈ S.Lvl i (c + 1) ∧ (G.ends x).2 ∈ S.Lvl i (c + 1) := by
    by_contra hn; simp [MGraph.induce, hn] at hc
  have hGx : (G.induce (S.Lvl i (c + 1))).cls x = G.cls x := by simp [MGraph.induce, hin]
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  obtain ⟨z1, z2⟩ := hZ.edge h3 h4 a1 a2 (by omega) b1 b2 (by omega)
  have z3 : x ∉ l := nl x (by rw [z1]; exact fun h => notL _ (by omega) h.1)
  refine ⟨Or.inl ?_, ?_⟩
  · rw [convert_cls_of_not_mem z3, z2, hGx]
  · simp only [MGraph.induce]
    rw [z1, if_neg (notL _ (by omega)), if_neg (notL _ (by omega))]
    exact sameEnds_refl _

/-- The internal vertices of the graph of the components `a, …, b`. -/
private theorem sdiff_P_eq_Lvl (S : SC G) {a b : ℕ} (hab : a ≤ b) (hb : b < S.k) :
    S.P a \ S.P (b + 1) = S.Lvl a (b + 1) := by
  ext v
  rw [S.mem_sdiff_P hab hb, S.mem_Lvl]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩

/-- The quotient graph at the component `c` of case (i) contains the graph of
[II, Claims A.4, A.5] built on the components `i, …, c` with `P (c + 1)` replaced by a `Θ` edge
(with the blue solid edges of `m` changed into `Θ` edges). -/
private theorem CaseI.le_A4 {i j : ℕ} (hC : S.CaseI i j) {Z : MGraph V E} {x₁ x₂ : E}
    (hZ : S.IsX Z i j x₁ x₂) {c : ℕ} (hic : i ≤ c) (hcj : c < j) {l m : List E}
    (hl : ∀ y ∈ l, ((Z.ends y).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (c + 1) (j + 1)) ∨
      y = S.cc' c ∨ y ∈ m ∨ y = S.e')
    (hml : ∀ y ∈ m, y ∈ l) (he' : S.e' ∈ l ↔ S.e ∈ m)
    (hc' : G.cls (S.cc' c) = some .diff ∨ S.cc' c ∈ l) :
    Le (((G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).convert m).twoSplit S.w (S.cc c)
      (S.cc' c) S.e S.e') ((Z.convert l).collapse (S.Lvl (c + 1) (j + 1)) S.w) := by
  have hck : c < S.k := by have := hC.hjk; omega
  have notL : ∀ v, S.lev v ≤ c → v ∉ S.Lvl (c + 1) (j + 1) := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have ec := S.e_ne_cc hck
  have ec' := hC.e_ne_cc' hck
  have e'c := S.e'_ne_cc hck
  have e'c' := S.e'_ne_cc' hck
  have cc := S.cc_ne c hck
  have hne := S.hne
  have hRint : (G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).int = S.Lvl i (c + 1) :=
    sdiff_P_eq_Lvl S hic hck
  have hRc : ∀ y, y ≠ S.cc c → y ≠ S.cc' c →
      (G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).cls y =
      if (G.ends y).1 ∈ S.Lvl i (c + 1) ∧ (G.ends y).2 ∈ S.Lvl i (c + 1) then G.cls y else none := by
    intro y h1 h2
    rw [← hRint]
    simp [MGraph.replace, MGraph.induce, h1, h2]
  have hRe : ∀ y, y ≠ S.cc c →
      (G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).ends y = G.ends y := by
    intro y h1
    simp [MGraph.replace, h1]
  have aL : (G.ends S.e).1 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.ha, by omega, by omega⟩
  have bL : (G.ends S.e).2 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.hb, by omega, by omega⟩
  have hRce : (G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).cls S.e = some .plus := by
    rw [hRc _ ec ec', if_pos ⟨aL, bL⟩, S.ce]
  have hθ : (G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).ends (S.cc c) =
      (S.u c, S.u' c) := by simp [MGraph.replace]
  have hθc : ((G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).convert m).cls (S.cc c) =
      some .diff := by
    rw [convert_cls]; simp [MGraph.replace]
  -- distinctness of the four edges
  have d02 : S.cc c ≠ S.cc' c := cc
  have d0b : S.cc c ≠ S.e := ec.symm
  have d04 : S.cc c ≠ S.e' := e'c.symm
  have d2b : S.cc' c ≠ S.e := ec'.symm
  have d24 : S.cc' c ≠ S.e' := e'c'.symm
  have db4 : S.e ≠ S.e' := hne
  refine ⟨?_, fun x hx => ?_⟩
  · rw [twoSplit_int, convert_int, hRint, collapse_convert, convert_int,
      hZ.collapse_int hic hcj (by omega) (by omega)]
  simp only [id]
  rw [collapse_cls, collapse_convert_ends]
  -- the crossing edges of `P (c + 1)`
  have hcross : ∀ y, (y = S.cc c ∨ y = S.cc' c) → Z.ends y = G.ends y ∧ Z.cls y = G.cls y := by
    intro y hy
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hck hy
    have hye : y ≠ S.e := by rcases hy with rfl | rfl; exacts [ec.symm, ec'.symm]
    have hye' : y ≠ S.e' := by rcases hy with rfl | rfl; exacts [e'c.symm, e'c'.symm]
    exact hZ.edge hye hye' g1 (by omega) (by omega) g2 (by omega) (by omega)
  by_cases h1 : x = S.cc' c
  · subst h1
    rw [ts_cls_b₂ d02 d0b d04 d2b d24 db4, ts_ends_b₂ d02 d0b d04 d2b d24 db4, convert_ends, hθ]
    obtain ⟨z1, z2⟩ := hcross _ (Or.inr rfl)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [hθc, convert_cls, z2]
      rcases S.cc'_cls c hck with h | h
      · rw [h]; simp
      · rcases hc' with h' | h'
        · rw [h] at h'; cases h'
        · rw [h]; simp [h']
    · rw [z1]
      exact cc_collapse hck hcj (Or.inr rfl)
  by_cases h2 : x = S.cc c
  · subst h2
    rw [ts_cls_of d02 d0b d04 d2b d24 db4 h1 d04, ts_ends_b₀ d02 d0b d04 d2b d24 db4,
      convert_ends, hθ]
    obtain ⟨z1, z2⟩ := hcross _ (Or.inl rfl)
    refine ⟨Or.inl ?_, ?_⟩
    · rw [hθc, convert_cls, z2, S.cc_diff c hck]; simp
    · rw [z1]
      exact (cc_collapse hck hcj (Or.inl rfl)).trans (Or.inr rfl)
  -- the edges `e`, `e'`
  have hge : S.Gt.ends S.e = ((G.ends S.e).1, S.w) := split_ends_e
  have hge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
  have hwL : S.w ∈ S.Lvl (c + 1) (j + 1) := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  have haL : (G.ends S.e).1 ∉ S.Lvl (c + 1) (j + 1) := notL _ (by omega)
  have hbL : (G.ends S.e).2 ∉ S.Lvl (c + 1) (j + 1) := notL _ (by omega)
  obtain ⟨ze1, ze2⟩ := hZ.gedge (x := S.e) (by rw [hge]; exact hC.ha)
    (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega) (by rw [hge]; exact S.hw)
    (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega)
  obtain ⟨ze1', ze2'⟩ := hZ.gedge (x := S.e') (by rw [hge']; exact S.hw)
    (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
    (by rw [hge']; exact hC.hb) (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
  rw [split_cls_of S.hne, S.ce] at ze2
  rw [split_cls_e', S.ce] at ze2'
  have hel : S.e ∈ l ↔ S.e ∈ m := by
    constructor
    · intro h
      rcases hl _ h with h' | h' | h' | h'
      · rw [ze1, hge] at h'; exact absurd h'.1 haL
      · exact absurd h' ec'
      · exact h'
      · exact absurd h' hne
    · exact hml _
  by_cases h3 : x = S.e
  · subst h3
    rw [ts_cls_of d02 d0b d04 d2b d24 db4 h1 db4, ts_ends_b d02 d0b d04 d2b d24 db4,
      convert_ends, hRe _ ec]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, ze2, convert_cls, hRce]
      simp only [hel]
    · rw [ze1, hge]
      simp only [haL, hwL, ↓reduceIte]
      exact sameEnds_refl _
  by_cases h4 : x = S.e'
  · subst h4
    rw [ts_cls_b₄ d02 d0b d04 d2b d24 db4, ts_ends_b₄ d02 d0b d04 d2b d24 db4, convert_ends,
      hRe _ ec]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, ze2', convert_cls, hRce]
      simp only [he']
    · rw [ze1', hge']
      simp only [hbL, hwL, ↓reduceIte]
      exact sameEnds_refl _
  -- the other edges
  rw [ts_cls_of d02 d0b d04 d2b d24 db4 h1 h4, ts_ends_of d02 d0b d04 d2b d24 db4 h2 h1 h3 h4,
    convert_ends, hRe x h2]
  have hc : (G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)).cls x ≠ none := by
    obtain ⟨hc, -⟩ := hx
    rw [ts_cls_of d02 d0b d04 d2b d24 db4 h1 h4, convert_cls] at hc
    intro h; rw [h] at hc; simp at hc
  rw [hRc x h2 h1] at hc
  have hin : (G.ends x).1 ∈ S.Lvl i (c + 1) ∧ (G.ends x).2 ∈ S.Lvl i (c + 1) := by
    by_contra hn; rw [if_neg hn] at hc; exact hc rfl
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  obtain ⟨z1, z2⟩ := hZ.edge h3 h4 a1 a2 (by omega) b1 b2 (by omega)
  have hxl : x ∈ l ↔ x ∈ m := by
    constructor
    · intro h
      rcases hl _ h with h' | h' | h' | h'
      · rw [z1] at h'; exact absurd h'.1 (notL _ (by omega))
      · exact absurd h' h1
      · exact h'
      · exact absurd h' h4
    · exact hml _
  refine ⟨Or.inl ?_, ?_⟩
  · rw [convert_cls, z2, convert_cls, hRc x h2 h1, if_pos hin]
    simp only [hxl]
  · rw [z1, if_neg (notL _ (by omega)), if_neg (notL _ (by omega))]
    exact sameEnds_refl _

/-! ### The graphs of the components `i, …, c` with `P (c + 1)` replaced by a `Θ` edge -/

variable (S) in
/-- The graph of the components `i, …, c` of `G`, with `P (c + 1)` and its two external edges
replaced by one `Θ` edge carrying the index `cc c`. -/
private abbrev Rep (i c : ℕ) : MGraph V E := G.replace (S.P i) (S.P (c + 1)) (S.cc c) (S.cc' c)

private theorem Rep_int {i c : ℕ} (hic : i ≤ c) (hck : c < S.k) : (S.Rep i c).int = S.Lvl i (c + 1) :=
  sdiff_P_eq_Lvl S hic hck

private theorem Rep_cls {i c : ℕ} (hic : i ≤ c) (hck : c < S.k) {y : E} (h1 : y ≠ S.cc c)
    (h2 : y ≠ S.cc' c) : (S.Rep i c).cls y =
      if (G.ends y).1 ∈ S.Lvl i (c + 1) ∧ (G.ends y).2 ∈ S.Lvl i (c + 1) then G.cls y else none := by
  rw [← Rep_int hic hck]
  simp [MGraph.replace, MGraph.induce, h1, h2]

private theorem Rep_ends {i c : ℕ} {y : E} (h1 : y ≠ S.cc c) : (S.Rep i c).ends y = G.ends y := by
  simp [MGraph.replace, h1]

private theorem Rep_θ {i c : ℕ} (hck : c < S.k) : (S.Rep i c).ends (S.cc c) = (S.u c, S.u' c) ∧
    (S.Rep i c).cls (S.cc c) = some .diff ∧ (S.Rep i c).cls (S.cc' c) = none := by
  refine ⟨by simp [MGraph.replace], by simp [MGraph.replace], ?_⟩
  simp [MGraph.replace, (S.cc_ne c hck).symm]

/-- The graph of the component `c` is contained in the subgraph induced on it of the graph of the
components `i, …, c`. -/
private theorem le_R_Rep {i c : ℕ} (hic : i ≤ c) (hck : c < S.k) :
    Le (S.R c) ((S.Rep i c).induce (S.Lvl c (c + 1))) := by
  have hcc := S.cc_ne c hck
  refine ⟨sdiff_P_eq_Lvl S le_rfl hck, fun x hx => ?_⟩
  simp only [id]
  rcases (S.isB_R hck).pres x hx.1 with ⟨-, rfl, hc, he⟩ | ⟨hn, a1, a2, b1, b2, hc, he⟩
  · obtain ⟨t1, t2, -⟩ := Rep_θ (S := S) (i := i) hck
    have hin : ((S.Rep i c).ends (S.cc c)).1 ∈ S.Lvl c (c + 1) ∧
        ((S.Rep i c).ends (S.cc c)).2 ∈ S.Lvl c (c + 1) := by
      rw [t1]
      obtain ⟨h1, h2⟩ := S.u_mem hck
      obtain ⟨h3, h4⟩ := S.u'_mem hck
      have m1 : S.u c ∈ S.Lvl c (c + 1) := S.mem_Lvl.2 ⟨h1, by omega, by omega⟩
      have m2 : S.u' c ∈ S.Lvl c (c + 1) := S.mem_Lvl.2 ⟨h3, by omega, by omega⟩
      exact ⟨m1, m2⟩
    refine ⟨Or.inl ?_, ?_⟩
    · simp only [MGraph.induce, hin, and_self, ↓reduceIte]
      rw [t2, hc]
    · simp only [MGraph.induce]
      rw [t1, he]
      exact sameEnds_refl _
  · obtain ⟨n1, n2⟩ := hn hck
    have hin : (G.ends x).1 ∈ S.Lvl c (c + 1) ∧ (G.ends x).2 ∈ S.Lvl c (c + 1) :=
      ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
    have hin' : (G.ends x).1 ∈ S.Lvl i (c + 1) ∧ (G.ends x).2 ∈ S.Lvl i (c + 1) :=
      ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
    refine ⟨Or.inl ?_, ?_⟩
    · simp only [MGraph.induce]
      rw [Rep_ends n1, if_pos hin, Rep_cls hic hck n1 n2, if_pos hin', hc]
    · simp only [MGraph.induce]
      rw [Rep_ends n1, he]
      exact sameEnds_refl _

/-- The graph of the components `i, …, c`, `i < c`, with the component `c` collapsed to the
outer end of `cc c`, is doubly connected: the subgraph induced on the components `i, …, c - 1` is
doubly connected, and the collapsed vertex is joined to it by `cc (c - 1)` and `cc' (c - 1)`. -/
private theorem dc_Rep_quot {i c : ℕ} (hic : i < c) (hck : c < S.k) (m : List E) :
    (((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).DC := by
  have hc1 : c - 1 < S.k := by omega
  have hcm : c - 1 + 1 = c := by omega
  obtain ⟨hu, hlu⟩ := S.u_mem hck
  have huΓ : S.u c ∈ S.Lvl c (c + 1) := S.mem_Lvl.2 ⟨hu, by omega, by omega⟩
  have hΓ : S.Lvl c (c + 1) ⊆ ((S.Rep i c).convert m).int := by
    rw [convert_int, Rep_int hic.le hck]
    intro v hv
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    exact S.mem_Lvl.2 ⟨h1, by omega, h3⟩
  have notΓ : ∀ v, S.lev v < c → v ∉ S.Lvl c (c + 1) := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have hy : ∀ y, (y = S.cc (c - 1) ∨ y = S.cc' (c - 1)) →
      (((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).cls y ≠ none ∧
      (((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).cls y ≠ some .minus ∧
      SameEnds ((((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).ends y)
        (S.u c, G.outer (S.P (c - 1 + 1)) y) ∧
      ((((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).cls y = some .diff ∨
        (((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).cls y = some .plus) ∧
      (y = S.cc (c - 1) → (((S.Rep i c).convert m).collapse (S.Lvl c (c + 1)) (S.u c)).cls y =
        some .diff) := by
    intro y hy
    obtain ⟨v, hv, hlv, ho, hlo, hse⟩ := S.cc_ends' hc1 hy
    have n1 : y ≠ S.cc c := fun h => by
      have := S.cc_inj hc1 hck hy (Or.inl h); omega
    have n2 : y ≠ S.cc' c := fun h => by
      have := S.cc_inj hc1 hck hy (Or.inr h); omega
    have mo : G.outer (S.P (c - 1 + 1)) y ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨ho, by omega, by omega⟩
    have mv : v ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hv, by omega, by omega⟩
    have hin : (G.ends y).1 ∈ S.Lvl i (c + 1) ∧ (G.ends y).2 ∈ S.Lvl i (c + 1) :=
      (hse.mem (S := S.Lvl i (c + 1))).2 ⟨mo, mv⟩
    have hcl : (S.Rep i c).cls y = G.cls y := by rw [Rep_cls hic.le hck n1 n2, if_pos hin]
    have hG : G.cls y = some .diff ∨ G.cls y = some .plus := by
      rcases hy with rfl | rfl
      · exact Or.inl (S.cc_diff _ hc1)
      · exact S.cc'_cls _ hc1
    have hcls : ((S.Rep i c).convert m).cls y = some .diff ∨
        ((S.Rep i c).convert m).cls y = some .plus := by
      rw [convert_cls, hcl]
      rcases hG with h | h <;> rw [h] <;> split_ifs <;> simp
    refine ⟨?_, ?_, ?_, hcls, ?_⟩
    · rw [collapse_cls]; rcases hcls with h | h <;> rw [h] <;> simp
    · rw [collapse_cls]; rcases hcls with h | h <;> rw [h] <;> simp
    · rw [collapse_ends, convert_ends, Rep_ends n1]
      have hvΓ : v ∈ S.Lvl c (c + 1) := S.mem_Lvl.2 ⟨hv, by omega, by omega⟩
      have hoΓ : G.outer (S.P (c - 1 + 1)) y ∉ S.Lvl c (c + 1) := notΓ _ (by omega)
      rcases sameEnds_iff.1 hse with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        simp only [hvΓ, hoΓ, ↓reduceIte]
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro rfl
      rw [collapse_cls, convert_cls, hcl, S.cc_diff _ hc1]; simp
  obtain ⟨y1, -, y3, -, y5⟩ := hy _ (Or.inl rfl)
  obtain ⟨z1, -, z3, z4, -⟩ := hy _ (Or.inr rfl)
  obtain ⟨hu1, hlu1⟩ := S.u_mem hc1
  obtain ⟨hu2, hlu2⟩ := S.u'_mem hc1
  have hRp : ∀ f, (G.induce (S.Lvl i c)).Pres f → (G.ends f).1 ∈ S.Lvl i c ∧
      (G.ends f).2 ∈ S.Lvl i c ∧ (G.induce (S.Lvl i c)).cls f = G.cls f := by
    intro f hf
    have hin : (G.ends f).1 ∈ S.Lvl i c ∧ (G.ends f).2 ∈ S.Lvl i c := by
      by_contra hn; exact hf.1 (by simp [MGraph.induce, hn])
    exact ⟨hin.1, hin.2, by simp [MGraph.induce, hin]⟩
  have hnotR : ∀ y, (y = S.cc (c - 1) ∨ y = S.cc' (c - 1)) → ¬ (G.induce (S.Lvl i c)).Pres y := by
    intro y hy hp
    obtain ⟨h1, h2, -⟩ := hRp y hp
    obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hc1 hy
    have := (S.mem_Lvl.1 h1).2.2
    have := (S.mem_Lvl.1 h2).2.2
    omega
  refine dc_path (R := G.induce (S.Lvl i c)) (N := S.u c) (g := S.cc (c - 1))
    (g₁ := S.cc (c - 1)) (g₂ := S.cc' (c - 1)) (y₁ := S.cc (c - 1)) (y₂ := S.cc' (c - 1))
    (m₁ := S.u (c - 1)) (m₂ := S.u' (c - 1)) (S.toSplitCtx.dc_Lvl c (by omega)) ?_ ?_ ?_ ?_
  · ext v
    rw [mem_collapse_int hΓ huΓ, Finset.mem_insert, convert_int, Rep_int hic.le hck]
    change _ ↔ v = S.u c ∨ v ∈ S.Lvl i c
    rw [S.mem_Lvl, S.mem_Lvl, S.mem_Lvl]
    constructor
    · rintro (h | ⟨⟨h1, h2, h3⟩, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, by by_contra h; exact h4 ⟨h1, by omega, h3⟩⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨h1, h2, by omega⟩, fun ⟨_, h, _⟩ => by omega⟩
  · intro f hf hfg
    obtain ⟨a1, a2, hcl⟩ := hRp f hf
    obtain ⟨a1i, a1a, a1b⟩ := S.mem_Lvl.1 a1
    obtain ⟨a2i, a2a, a2b⟩ := S.mem_Lvl.1 a2
    have n1 : f ≠ S.cc c := fun h => by
      obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hck (Or.inl h); omega
    have n2 : f ≠ S.cc' c := fun h => by
      obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hck (Or.inr h); omega
    have hin' : (G.ends f).1 ∈ S.Lvl i (c + 1) ∧ (G.ends f).2 ∈ S.Lvl i (c + 1) :=
      ⟨S.mem_Lvl.2 ⟨a1i, a1a, by omega⟩, S.mem_Lvl.2 ⟨a2i, a2a, by omega⟩⟩
    refine ⟨?_, ?_⟩
    · rw [collapse_cls, convert_cls, Rep_cls hic.le hck n1 n2, if_pos hin', hcl]
      split_ifs with h
      · exact Or.inr ⟨h.2, rfl⟩
      · exact Or.inl rfl
    · rw [collapse_ends, convert_ends, Rep_ends n1, if_neg (notΓ _ (by omega)),
        if_neg (notΓ _ (by omega))]
      exact sameEnds_refl _
  · intro h; exact absurd h (hnotR _ (Or.inl rfl))
  · intro _
    refine ⟨y5 rfl, z4, y3, z3, S.mem_Lvl.2 ⟨hu1, by omega, by omega⟩,
      S.mem_Lvl.2 ⟨hu2, by omega, by omega⟩, S.cc_ne _ hc1, fun f hf _ => ⟨?_, ?_⟩,
      fun h => absurd h (hnotR _ (Or.inl rfl))⟩
    · rintro rfl; exact hnotR _ (Or.inl rfl) hf
    · rintro rfl; exact hnotR _ (Or.inr rfl) hf

/-- The order of the component `c` is a sequence of redundant edges in the graph of the
components `i, …, c` ([II, Claim A.1]). -/
private theorem red_Rep {i c : ℕ} (hic : i ≤ c) (hck : c < S.k) {t : ℕ} (ht : t < (S.ordR c).length) :
    ((S.Rep i c).convert ((S.ordR c).take t)).IsRedundant (S.ordR c)[t] := by
  have hR := (S.ordR_spec hck).2.2 t ht
  rcases Nat.lt_or_ge i c with hlt | hge
  · have hx := ((S.mem_ordR hck _).1 (List.getElem_mem ht))
    obtain ⟨hp, a1, a2, b1, b2⟩ := hx
    obtain ⟨hu, hlu⟩ := S.u_mem hck
    have huΓ : S.u c ∈ S.Lvl c (c + 1) := S.mem_Lvl.2 ⟨hu, by omega, by omega⟩
    have hΓ : S.Lvl c (c + 1) ⊆ ((S.Rep i c).convert ((S.ordR c).take t)).int := by
      rw [convert_int, Rep_int hic hck]
      intro v hv
      obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
      exact S.mem_Lvl.2 ⟨h1, by omega, h3⟩
    have n1 : (S.ordR c)[t] ≠ S.cc c := fun h => by
      obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hck (Or.inl h); omega
    have hin : (((S.Rep i c).convert ((S.ordR c).take t)).ends (S.ordR c)[t]).1 ∈ S.Lvl c (c + 1) ∧
        (((S.Rep i c).convert ((S.ordR c).take t)).ends (S.ordR c)[t]).2 ∈ S.Lvl c (c + 1) := by
      rw [convert_ends, Rep_ends n1]
      exact ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
    refine red_lift hΓ huΓ hin ?_ (dc_Rep_quot hlt hck _)
    rw [induce_convert']
    refine red_le hR (leS_convert (le_R_Rep hic hck) (fun _ _ _ => rfl) _) ?_
    have hnd := (S.ordR_spec hck).1
    have hnt : (S.ordR c)[t] ∉ (S.ordR c).take t := by
      intro hm
      have h' := List.take_append_drop t (S.ordR c)
      rw [← h', List.nodup_append] at hnd
      exact hnd.2.2 _ hm _ (by rw [List.drop_eq_getElem_cons ht]; exact List.mem_cons_self) rfl
    have hinG : (G.ends (S.ordR c)[t]).1 ∈ S.Lvl c (c + 1) ∧
        (G.ends (S.ordR c)[t]).2 ∈ S.Lvl c (c + 1) :=
      ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
    have hinG' : (G.ends (S.ordR c)[t]).1 ∈ S.Lvl i (c + 1) ∧
        (G.ends (S.ordR c)[t]).2 ∈ S.Lvl i (c + 1) :=
      ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
    have n2 : (S.ordR c)[t] ≠ S.cc' c := fun h => by
      obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hck (Or.inr h); omega
    rw [convert_cls_of_not_mem hnt]
    simp only [MGraph.induce]
    rw [Rep_ends n1, if_pos hinG, Rep_cls hic hck n1 n2, if_pos hinG', hp]
  · have : i = c := le_antisymm hic hge
    subst this
    exact hR

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

variable (S) in
/-- The crossing edge `cc' c`, if it is a blue solid edge. -/
private def J (c : ℕ) : List E := if G.cls (S.cc' c) = some .plus then [S.cc' c] else []

private theorem mem_J {c : ℕ} {y : E} (h : y ∈ S.J c) : y = S.cc' c ∧ G.cls (S.cc' c) = some .plus := by
  unfold J at h
  split_ifs at h with hp
  · exact ⟨List.mem_singleton.1 h, hp⟩
  · simp at h

private theorem J_or {c : ℕ} (hck : c < S.k) : G.cls (S.cc' c) = some .diff ∨ S.cc' c ∈ S.J c := by
  unfold J
  split_ifs with hp
  · exact Or.inr (List.mem_singleton_self _)
  · rcases S.cc'_cls c hck with h | h
    · exact Or.inl h
    · exact absurd h hp

/-- An edge of the induced subgraph on the components `i, …, c` crossing `P (c + 1)` is absent. -/
private theorem induce_cls_cross {i c : ℕ} (hck : c < S.k) {y : E} (hy : y = S.cc c ∨ y = S.cc' c) :
    (G.induce (S.Lvl i (c + 1))).cls y = none := by
  obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hck hy
  have : ¬ ((G.ends y).1 ∈ S.Lvl i (c + 1) ∧ (G.ends y).2 ∈ S.Lvl i (c + 1)) := by
    rintro ⟨h1, h2⟩
    have := (S.mem_Lvl.1 h1).2.2
    have := (S.mem_Lvl.1 h2).2.2
    omega
  simp [MGraph.induce, this]

private theorem induce_cls_e' {T : Finset V} : (G.induce T).cls S.e' = none := by
  simp [MGraph.induce, S.ce']

/-- An entry of a list without repetition is not among the entries before it. -/
private theorem getElem_not_mem_take {α : Type} {l : List α} (h : l.Nodup) {t : ℕ} (ht : t < l.length) :
    l[t] ∉ l.take t := by
  intro hm
  have h' := List.take_append_drop t l
  rw [← h', List.nodup_append] at h
  exact h.2.2 _ hm _ (by rw [List.drop_eq_getElem_cons ht]; exact List.mem_cons_self) rfl

private theorem take_mid {α : Type} (a : α) (l₁ l₂ : List α) (t : ℕ) :
    (l₁ ++ a :: l₂).take (l₁.length + 1 + t) = l₁ ++ a :: l₂.take t := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm 1 t, List.take_succ_cons]

private theorem getElem_mid {α : Type} (a : α) (l₁ l₂ : List α) (t : ℕ) (ht : t < l₂.length)
    (h : l₁.length + 1 + t < (l₁ ++ a :: l₂).length) :
    (l₁ ++ a :: l₂)[l₁.length + 1 + t] = l₂[t] := by
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm 1 t, List.getElem_cons_succ]

/-- The concatenation of the lists `pl (j - 1), …, pl (j - d)`. -/
private def midL (pl : ℕ → List E) (j : ℕ) : ℕ → List E
  | 0 => []
  | d + 1 => midL pl j d ++ pl (j - 1 - d)

omit [DecidableEq V] [DecidableEq E] in
private theorem mem_midL {pl : ℕ → List E} {j d : ℕ} {y : E} :
    y ∈ midL pl j d ↔ ∃ d' < d, y ∈ pl (j - 1 - d') := by
  induction d with
  | zero => simp [midL]
  | succ d ih =>
    rw [midL, List.mem_append, ih]
    constructor
    · rintro (⟨d', h1, h2⟩ | h)
      · exact ⟨d', by omega, h2⟩
      · exact ⟨d, by omega, h⟩
    · rintro ⟨d', h1, h2⟩
      by_cases h : d' < d
      · exact Or.inl ⟨d', h, h2⟩
      · have : d' = d := by omega
        subst this; exact Or.inr h2

omit [DecidableEq V] in
/-- The steps of the components `j, j - 1, …, i + 1`, assembled from the steps of each component
after the deeper ones. -/
private theorem steps_tiers {Z : MGraph V E} {i j : ℕ} (hij : i < j) (pl : ℕ → List E) (ℓB : List E)
    (ins : ℕ → E → Prop) (hmono : ∀ c c' y, c' ≤ c → ins c y → ins c' y)
    (hbot : Steps Z ℓB) (hbotin : ∀ y ∈ ℓB, ins j y)
    (htier : ∀ c, i < c → c < j → ∀ pre : List E, (∀ y ∈ pre, ins (c + 1) y) →
      Steps (Z.convert pre) (pl c))
    (hin : ∀ c, i < c → c < j → ∀ y ∈ pl c, ins c y) :
    Steps Z (ℓB ++ midL pl j (j - 1 - i)) ∧ ∀ y ∈ ℓB ++ midL pl j (j - 1 - i), ins (i + 1) y := by
  have key : ∀ d, d ≤ j - 1 - i → Steps Z (ℓB ++ midL pl j d) ∧
      ∀ y ∈ ℓB ++ midL pl j d, ins (j - d) y := by
    intro d
    induction d with
    | zero => intro _; simpa [midL] using ⟨hbot, hbotin⟩
    | succ d ih =>
      intro hd
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hc : j - 1 - d + 1 = j - d := by omega
      rw [midL, ← List.append_assoc, steps_append]
      refine ⟨⟨h1, htier (j - 1 - d) (by omega) (by omega) _ (fun y hy => by
        rw [hc]; exact h2 y hy)⟩, fun y hy => ?_⟩
      rcases List.mem_append.1 hy with h | h
      · exact hmono _ _ y (by omega) (h2 y h)
      · have := hin (j - 1 - d) (by omega) (by omega) y h
        rwa [show j - (d + 1) = j - 1 - d by omega]
  obtain ⟨h1, h2⟩ := key (j - 1 - i) le_rfl
  exact ⟨h1, fun y hy => by have := h2 y hy; rwa [show j - (j - 1 - i) = i + 1 by omega] at this⟩

omit [DecidableEq V] in
/-- The steps of the components `j - 1, …, lo`, after the steps of a list `ℓ0`, assembled from
the steps of each component after the deeper ones. -/
private theorem steps_tiers' {Z : MGraph V E} {lo j : ℕ} (hlo : lo ≤ j) (pl : ℕ → List E) (ℓ0 : List E)
    (ins : ℕ → E → Prop) (hmono : ∀ c c' y, c' ≤ c → ins c y → ins c' y)
    (hbot : Steps Z ℓ0) (hbotin : ∀ y ∈ ℓ0, ins j y)
    (htier : ∀ c, lo ≤ c → c < j → ∀ pre : List E, (∀ y ∈ pre, ins (c + 1) y) →
      (∀ y ∈ ℓ0, y ∈ pre) → Steps (Z.convert pre) (pl c))
    (hin : ∀ c, lo ≤ c → c < j → ∀ y ∈ pl c, ins c y) :
    Steps Z (ℓ0 ++ midL pl j (j - lo)) ∧ ∀ y ∈ ℓ0 ++ midL pl j (j - lo), ins lo y := by
  have key : ∀ d, d ≤ j - lo → Steps Z (ℓ0 ++ midL pl j d) ∧
      ∀ y ∈ ℓ0 ++ midL pl j d, ins (j - d) y := by
    intro d
    induction d with
    | zero => intro _; simpa [midL] using ⟨hbot, hbotin⟩
    | succ d ih =>
      intro hd
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hc : j - 1 - d + 1 = j - d := by omega
      rw [midL, ← List.append_assoc, steps_append]
      refine ⟨⟨h1, htier (j - 1 - d) (by omega) (by omega) _ (fun y hy => by
        rw [hc]; exact h2 y hy) (fun y hy => List.mem_append_left _ hy)⟩, fun y hy => ?_⟩
      rcases List.mem_append.1 hy with h | h
      · exact hmono _ _ y (by omega) (h2 y h)
      · have := hin (j - 1 - d) (by omega) (by omega) y h
        rwa [show j - (d + 1) = j - 1 - d by omega]
  obtain ⟨h1, h2⟩ := key (j - lo) le_rfl
  exact ⟨h1, fun y hy => by have := h2 y hy; rwa [show j - (j - lo) = lo by omega] at this⟩

private theorem steps_dc {X : MGraph V E} {l : List E} (h : Steps X l) (hl : l ≠ []) : X.DC := by
  obtain ⟨y, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact (steps_cons.1 h).1.2.1

/-- The graph of the last component `b` of the graph after operation (B) on the components
`a, …, b` contains the graph `B` of the component `b` of `G`. -/
private theorem IsX.le_bot {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂) (hab : a ≤ b)
    {B : MGraph V E} (hB : S.IsB B b x₁ x₂)
    (hx12 : b < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (he : ¬ ((G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = b ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = b)) :
    Le B (Z.induce (S.Lvl b (b + 1))) := by
  refine ⟨?_, fun x hx => ?_⟩
  · ext v
    rw [hB.int]
    change _ ↔ v ∈ S.Lvl b (b + 1)
    rw [S.mem_Lvl]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, by omega⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega⟩
  simp only [id]
  rcases hB.pres x hx.1 with ⟨hb, rfl, hc, hen⟩ | ⟨hn, a1, a2, b1, b2, hc, hen⟩
  · obtain ⟨-, z1, -, z2, -, -⟩ := hZ.th hb
    obtain ⟨n1, n2, n3, n4⟩ := hx12 hb
    obtain ⟨hx₁, hx₂, -⟩ := hB.x12 hb
    have o1 : S.Gt.outer (S.P (b + 1)) x = G.outer (S.P (b + 1)) x := by
      unfold MGraph.outer; rw [split_ends_ne n1 n2]
    have o2 : S.Gt.outer (S.P (b + 1)) x₂ = G.outer (S.P (b + 1)) x₂ := by
      unfold MGraph.outer; rw [split_ends_ne n3 n4]
    obtain ⟨-, -, -, g1, g2, -⟩ := S.cc_ends' hb hx₁
    obtain ⟨-, -, -, g3, g4, -⟩ := S.cc_ends' hb hx₂
    have hin : (Z.ends x).1 ∈ S.Lvl b (b + 1) ∧ (Z.ends x).2 ∈ S.Lvl b (b + 1) := by
      rw [z2, o1, o2]
      have m1 : G.outer (S.P (b + 1)) x ∈ S.Lvl b (b + 1) := S.mem_Lvl.2 ⟨g1, by omega, by omega⟩
      have m2 : G.outer (S.P (b + 1)) x₂ ∈ S.Lvl b (b + 1) := S.mem_Lvl.2 ⟨g3, by omega, by omega⟩
      exact ⟨m1, m2⟩
    refine ⟨Or.inl ?_, ?_⟩
    · simp only [MGraph.induce, hin, and_self, ↓reduceIte]
      rw [z1, hc]
    · simp only [MGraph.induce]
      rw [z2, o1, o2, hen]
      exact sameEnds_refl _
  · have hxe : x ≠ S.e := by rintro rfl; exact he ⟨a1, a2, b1, b2⟩
    have hxe' : x ≠ S.e' := by rintro rfl; exact hx.1 (by rw [hc, S.ce'])
    obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
    have hin : (Z.ends x).1 ∈ S.Lvl b (b + 1) ∧ (Z.ends x).2 ∈ S.Lvl b (b + 1) := by
      rw [z1]
      exact ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
    refine ⟨Or.inl ?_, ?_⟩
    · simp only [MGraph.induce, hin, and_self, ↓reduceIte]
      rw [z2, hc]
    · simp only [MGraph.induce]
      rw [z1, hen]
      exact sameEnds_refl _

/-- The steps of the order of the last component `b` of the graph after operation (B), given
that the quotient graphs by this component are doubly connected ([II, Claim A.1]). -/
private theorem IsX.tier_bot {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂)
    (hab : a ≤ b) (hlw : S.lev S.w = b) {B : MGraph V E} (hB : S.IsB B b x₁ x₂) {ℓ : List E}
    (hℓ : B.IsPDOrder ℓ) (hx12 : b < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (he : ¬ ((G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = b ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = b))
    (hQ : ∀ t, ((Z.convert (ℓ.take t)).collapse (S.Lvl b (b + 1)) S.w).DC) : Steps Z ℓ := by
  intro t ht
  have hx := (hℓ.2.1 _).1 (List.getElem_mem ht)
  obtain ⟨hp, a1, a2, b1, b2⟩ := (hB.ip _).1 hx
  have hxe : ℓ[t] ≠ S.e := by intro h; rw [h] at a1 a2 b1 b2; exact he ⟨a1, a2, b1, b2⟩
  have hxe' : ℓ[t] ≠ S.e' := by intro h; rw [h, S.ce'] at hp; cases hp
  obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
  have hin : ((Z.convert (ℓ.take t)).ends ℓ[t]).1 ∈ S.Lvl b (b + 1) ∧
      ((Z.convert (ℓ.take t)).ends ℓ[t]).2 ∈ S.Lvl b (b + 1) := by
    rw [convert_ends, z1]
    exact ⟨S.mem_Lvl.2 ⟨a1, by omega, by omega⟩, S.mem_Lvl.2 ⟨b1, by omega, by omega⟩⟩
  have hsub : S.Lvl b (b + 1) ⊆ (Z.convert (ℓ.take t)).int := fun v hv => by
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    rw [convert_int]; exact (hZ.int v).2 ⟨h1, by omega, by omega⟩
  have hwΓ : S.w ∈ S.Lvl b (b + 1) := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  refine red_lift hsub hwΓ hin ?_ (hQ _)
  rw [induce_convert']
  refine red_le (hℓ.2.2 t ht) (leS_convert (hZ.le_bot hab hB hx12 he) (fun _ _ _ => rfl) _) ?_
  rw [convert_cls_of_not_mem (getElem_not_mem_take hℓ.1 ht)]
  have hin' : (Z.ends ℓ[t]).1 ∈ S.Lvl b (b + 1) ∧ (Z.ends ℓ[t]).2 ∈ S.Lvl b (b + 1) := by
    rw [convert_ends] at hin; exact hin
  simp only [MGraph.induce, hin', and_self, ↓reduceIte]
  rw [z2, hp]

/-- The internal blue solid edges of the graph after operation (B) on the components `a, …, b`:
`e`, `e'` if their ends are internal vertices of it, and the blue solid edges of `G` between
internal vertices of these components. -/
private theorem IsX.intPlus {Z : MGraph V E} {x₁ x₂ : E} {a b : ℕ} (hZa : S.IsX Z a b x₁ x₂) (x : E) (hx : x ≠ S.e) (hx' : x ≠ S.e') :
    Z.IsIntPlus x ↔ G.cls x = some .plus ∧ (G.ends x).1 ∈ G.int ∧ a ≤ S.lev (G.ends x).1 ∧
      S.lev (G.ends x).1 ≤ b ∧ (G.ends x).2 ∈ G.int ∧ a ≤ S.lev (G.ends x).2 ∧
      S.lev (G.ends x).2 ≤ b := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hn : b < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
      intro hb
      obtain ⟨-, t1, t2, -⟩ := hZa.th hb
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [h, t1] at h1; cases h1
      · rw [h, t2] at h1; cases h1
    obtain ⟨g1, g2⟩ := hZa.gen x hn
    rw [g2] at h1
    split_ifs at h1 with hin
    rw [split_cls_ne hx'] at h1
    rw [split_ends_ne hx hx'] at hin
    obtain ⟨a1, a2, a3⟩ := (hZa.int _).1 hin.1
    obtain ⟨b1, b2, b3⟩ := (hZa.int _).1 hin.2
    exact ⟨h1, a1, a2, a3, b1, b2, b3⟩
  · rintro ⟨h1, a1, a2, a3, b1, b2, b3⟩
    obtain ⟨z1, z2⟩ := hZa.edge hx hx' a1 a2 a3 b1 b2 b3
    refine ⟨z2.trans h1, ?_, ?_⟩ <;> rw [z1]
    · exact (hZa.int _).2 ⟨a1, a2, a3⟩
    · exact (hZa.int _).2 ⟨b1, b2, b3⟩

/-! ### Case (i) of [II, Lemma 5.12] -/

section CaseI

variable {i j : ℕ} (hC : S.CaseI i j) {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z i j x₁ x₂)
include hC hZ

/-- The components `c + 1, …, j` of the graph of case (i). -/
private theorem CaseI.lower {c : ℕ} (hic : i ≤ c) (hcj : c < j) :
    (∀ l : List E, S.Lvl (c + 1) (j + 1) ⊆ (Z.convert l).int) ∧ S.w ∈ S.Lvl (c + 1) (j + 1) ∧
      (∀ l : List E, ((Z.convert l).induce (S.Lvl (c + 1) (j + 1))).DC) := by
  have hlw := hC.hlw
  refine ⟨fun l v hv => ?_, S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩, fun l => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    rw [convert_int]
    exact (hZ.int v).2 ⟨h1, by omega, by omega⟩
  · refine hZ.dc_lower hic hcj hC.hjk (fun h => ?_) l
    have := (S.mem_Lvl.1 h.1).2.1
    have := hC.hla
    omega

/-- The step of the crossing edge `cc' c` in case (i): [II, Claim A.3]. -/
private theorem CaseI.stepJ {c : ℕ} (hic : i ≤ c) (hcj : c < j) {pre : List E}
    (hpre : ∀ y ∈ pre, (Z.ends y).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (c + 1) (j + 1)) :
    Steps (Z.convert pre) (S.J c) := by
  have hck : c < S.k := by have := hC.hjk; omega
  obtain ⟨hL, hwL, hI⟩ := hC.lower hZ hic hcj
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  unfold J
  split_ifs with hp
  · rw [steps_single]
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hck (Or.inr rfl)
    obtain ⟨z1, z2⟩ := hZ.edge (hC.e_ne_cc' hck).symm (S.e'_ne_cc' hck).symm g1 (by omega)
      (by omega) g2 (by omega) (by omega)
    have hx : ¬ (((Z.convert pre).ends (S.cc' c)).1 ∈ S.Lvl (c + 1) (j + 1) ∧
        ((Z.convert pre).ends (S.cc' c)).2 ∈ S.Lvl (c + 1) (j + 1)) := by
      rw [convert_ends, z1]
      rintro ⟨a1, a2⟩
      have := (S.mem_Lvl.1 a1).2.1
      have := (S.mem_Lvl.1 a2).2.1
      omega
    have hxp : S.cc' c ∉ pre := fun h => hx (by rw [convert_ends]; exact hpre _ h)
    refine red_quot (hL pre) hwL hx (hI pre) (red_le ?_ (hC.le_A3 hZ hic hcj hpre hp) ?_)
    · have aL : (G.ends S.e).1 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.ha, by omega, by omega⟩
      have bL : (G.ends S.e).2 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.hb, by omega, by omega⟩
      obtain ⟨hu, hlu⟩ := S.u_mem hck
      obtain ⟨hu', hlu'⟩ := S.u'_mem hck
      refine MGraph.claimA3 V E _ S.w (S.u c) (S.u' c) S.e (S.cc c) (S.cc' c) S.e'
        (S.toSplitCtx.dc_Lvl (c + 1) (by omega)) (fun h => by
          have := (S.mem_Lvl.1 h).2.2; omega) (by simp [MGraph.induce])
        (S.mem_Lvl.2 ⟨hu, by omega, by omega⟩) (S.mem_Lvl.2 ⟨hu', by omega, by omega⟩)
        (by simp [MGraph.induce, aL, bL, S.ce]) aL bL ?_ (induce_cls_cross hck (Or.inl rfl))
        (induce_cls_cross hck (Or.inr rfl)) induce_cls_e'
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true]
      exact ⟨⟨S.e_ne_cc hck, hC.e_ne_cc' hck, S.hne⟩, ⟨S.cc_ne c hck, (S.e'_ne_cc hck).symm⟩,
        (S.e'_ne_cc' hck).symm, by simp⟩
    · rw [collapse_cls, convert_cls_of_not_mem hxp, z2, hp]
  · exact steps_nil _

omit hZ in
/-- The hypotheses of [II, Claims A.4, A.5] for the graph of the components `i, …, c`. -/
private theorem CaseI.rep_hyps {c : ℕ} (hic : i ≤ c) (hcj : c < j) (m : List E) :
    S.w ∉ ((S.Rep i c).convert m).int ∧ S.w ∉ ((S.Rep i c).convert m).ext ∧
    ((S.Rep i c).convert m).cls (S.cc c) = some .diff ∧
    (((S.Rep i c).convert m).ends (S.cc c)).1 ∈ ((S.Rep i c).convert m).int ∧
    (((S.Rep i c).convert m).ends (S.cc c)).2 ∈ ((S.Rep i c).convert m).int ∧
    (((S.Rep i c).convert m).ends S.e).1 ∈ ((S.Rep i c).convert m).int ∧
    (((S.Rep i c).convert m).ends S.e).2 ∈ ((S.Rep i c).convert m).int ∧
    [S.cc c, S.cc' c, S.e, S.e'].Nodup ∧ ((S.Rep i c).convert m).cls (S.cc' c) = none ∧
    ((S.Rep i c).convert m).cls S.e' = none ∧
    ((S.Rep i c).convert m).cls S.e = (if S.e ∈ m then some .diff else some .plus) := by
  have hck : c < S.k := by have := hC.hjk; omega
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  obtain ⟨t1, t2, t3⟩ := Rep_θ (S := S) (i := i) hck
  obtain ⟨hu, hlu⟩ := S.u_mem hck
  obtain ⟨hu', hlu'⟩ := S.u'_mem hck
  have ec := S.e_ne_cc hck
  have ec' := hC.e_ne_cc' hck
  have aL : (G.ends S.e).1 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.ha, by omega, by omega⟩
  have bL : (G.ends S.e).2 ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hC.hb, by omega, by omega⟩
  have mu : S.u c ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hu, by omega, by omega⟩
  have mu' : S.u' c ∈ S.Lvl i (c + 1) := S.mem_Lvl.2 ⟨hu', by omega, by omega⟩
  rw [convert_int, Rep_int hic hck, convert_ends, t1, Rep_ends ec]
  refine ⟨fun h => by have := (S.mem_Lvl.1 h).2.2; omega, by simp [MGraph.replace, MGraph.convert],
    by rw [convert_cls, t2]; simp, mu, mu', aL, bL, ?_, by rw [convert_cls, t3]; simp, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true]
    exact ⟨⟨S.cc_ne c hck, ec.symm, (S.e'_ne_cc hck).symm⟩, ⟨ec'.symm, (S.e'_ne_cc' hck).symm⟩,
      S.hne, by simp⟩
  · rw [convert_cls, Rep_cls hic hck (S.e'_ne_cc hck) (S.e'_ne_cc' hck), S.ce']
    simp
  · have hRe : (S.Rep i c).cls S.e = some .plus := by
      rw [Rep_cls hic hck ec ec', if_pos ⟨aL, bL⟩, S.ce]
    rw [convert_cls, hRe]
    by_cases h : S.e ∈ m <;> simp [h]

/-- A redundancy step in case (i) at the component `c` for an edge other than `e`, `e'`:
[II, Claims A.4 (i), A.5]. -/
private theorem CaseI.stepA {c : ℕ} (hic : i ≤ c) (hcj : c < j) {l m : List E} {x : E}
    (hl : ∀ y ∈ l, ((Z.ends y).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (c + 1) (j + 1)) ∨
      y = S.cc' c ∨ y ∈ m ∨ y = S.e')
    (hml : ∀ y ∈ m, y ∈ l) (he' : S.e' ∈ l ↔ S.e ∈ m)
    (hc' : G.cls (S.cc' c) = some .diff ∨ S.cc' c ∈ l)
    (hx : ¬ ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1)))
    (hxe : x ≠ S.e) (hr : ((S.Rep i c).convert m).IsRedundant x)
    (hxc : (Z.convert l).cls x = some .plus) : (Z.convert l).IsRedundant x := by
  obtain ⟨hL, hwL, hI⟩ := hC.lower hZ hic hcj
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hC.rep_hyps hic hcj m
  have hT : (((S.Rep i c).convert m).twoSplit S.w (S.cc c) (S.cc' c) S.e S.e').IsRedundant x := by
    by_cases hem : S.e ∈ m
    · rw [if_pos hem] at h11
      exact MGraph.claimA5 V E _ S.w (S.cc c) (S.cc' c) S.e S.e' hr.2.1 h1 h2 h3 h11 h4 h5 h6 h7
        h8 h9 h10 x hr
    · rw [if_neg hem] at h11
      exact (MGraph.claimA4 V E _ S.w (S.cc c) (S.cc' c) S.e S.e' hr.2.1 h1 h2 h3 h11 h4 h5 h6 h7
        h8 h9 h10).1 x hxe hr
  exact red_quot (hL l) hwL (by rw [convert_ends]; exact hx) (hI l)
    (red_le hT (hC.le_A4 hZ hic hcj hl hml he' hc') hxc)

/-- The steps of the order of the component `c`, `i < c < j`, in case (i). -/
private theorem CaseI.tier_mid {c : ℕ} (hic : i < c) (hcj : c < j) {pre : List E}
    (hpre : ∀ y ∈ pre, (Z.ends y).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (c + 1) (j + 1)) :
    Steps (Z.convert pre) (S.J c ++ S.ordR c) := by
  have hck : c < S.k := by have := hC.hjk; omega
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  rw [steps_append]
  refine ⟨hC.stepJ hZ hic.le hcj hpre, fun t ht => ?_⟩
  rw [convert_convert', convert_convert', ← List.append_assoc]
  have hx := (S.mem_ordR hck _).1 (List.getElem_mem ht)
  obtain ⟨hp, a1, a2, b1, b2⟩ := hx
  have hxe : (S.ordR c)[t] ≠ S.e := fun h => by rw [h] at a2; omega
  have hxe' : (S.ordR c)[t] ≠ S.e' := fun h => by rw [h, S.ce'] at hp; cases hp
  obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
  have hxL : ¬ ((Z.ends (S.ordR c)[t]).1 ∈ S.Lvl (c + 1) (j + 1) ∧
      (Z.ends (S.ordR c)[t]).2 ∈ S.Lvl (c + 1) (j + 1)) := by
    rw [z1]; rintro ⟨h, -⟩; have := (S.mem_Lvl.1 h).2.1; omega
  have hnd := (S.ordR_spec hck).1
  have hxl : (S.ordR c)[t] ∉ pre ++ S.J c ++ (S.ordR c).take t := by
    simp only [List.mem_append, not_or]
    refine ⟨⟨fun h => hxL (hpre _ h), fun h => ?_⟩, getElem_not_mem_take hnd ht⟩
    obtain ⟨h, -⟩ := mem_J h
    obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hck (Or.inr h)
    omega
  refine hC.stepA hZ hic.le hcj (m := (S.ordR c).take t) (fun y hy => ?_) (fun y hy => by
    simp [hy]) ?_ ?_ hxL hxe (red_Rep hic.le hck ht) (by rw [convert_cls_of_not_mem hxl, z2, hp])
  · simp only [List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact Or.inl (hpre y h)
    · exact Or.inr (Or.inl (mem_J h).1)
    · exact Or.inr (Or.inr (Or.inl h))
  · have ne : S.e ∉ (S.ordR c).take t := fun h => by
      have := ((S.mem_ordR hck _).1 (List.mem_of_mem_take h)).2.2.1
      omega
    have ne' : S.e' ∉ pre ++ S.J c ++ (S.ordR c).take t := by
      simp only [List.mem_append, not_or]
      refine ⟨⟨fun h => ?_, fun h => S.e'_ne_cc' hck (mem_J h).1⟩, fun h => ?_⟩
      · have := hpre _ h
        have hge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
        obtain ⟨z1', -⟩ := hZ.gedge (x := S.e') (by rw [hge']; exact S.hw)
          (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
          (by rw [hge']; exact hC.hb) (by rw [hge']; dsimp only; omega)
          (by rw [hge']; dsimp only; omega)
        rw [z1', hge'] at this
        dsimp only at this
        have := (S.mem_Lvl.1 this.2).2.1
        omega
      · have := ((S.mem_ordR hck _).1 (List.mem_of_mem_take h)).1
        rw [S.ce'] at this; cases this
    exact iff_of_false ne' ne
  · rcases S.J_or hck with h | h
    · exact Or.inl h
    · exact Or.inr (by simp [h])

/-- The edges `e`, `e'` in the graph of case (i): the path through `w`, blue solid edges, not
inside the components `i + 1, …, j`. -/
private theorem CaseI.path {x : E} (hx : x = S.e ∨ x = S.e') :
    Z.cls x = some .plus ∧ (Z.ends x = ((G.ends S.e).1, S.w) ∨ Z.ends x = (S.w, (G.ends S.e).2)) ∧
    ¬ ((Z.ends x).1 ∈ S.Lvl (i + 1) (j + 1) ∧ (Z.ends x).2 ∈ S.Lvl (i + 1) (j + 1)) := by
  have hij := hC.hij
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have hge : S.Gt.ends S.e = ((G.ends S.e).1, S.w) := split_ends_e
  have hge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
  rcases hx with rfl | rfl
  · obtain ⟨z1, z2⟩ := hZ.gedge (x := S.e) (by rw [hge]; exact hC.ha)
      (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega) (by rw [hge]; exact S.hw)
      (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega)
    refine ⟨by rw [z2, split_cls_of S.hne, S.ce], Or.inl (z1.trans hge), ?_⟩
    rw [z1, hge]; dsimp only
    rintro ⟨h, -⟩; have := (S.mem_Lvl.1 h).2.1; omega
  · obtain ⟨z1, z2⟩ := hZ.gedge (x := S.e') (by rw [hge']; exact S.hw)
      (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
      (by rw [hge']; exact hC.hb) (by rw [hge']; dsimp only; omega)
      (by rw [hge']; dsimp only; omega)
    refine ⟨by rw [z2, split_cls_e', S.ce], Or.inr (z1.trans hge'), ?_⟩
    rw [z1, hge']; dsimp only
    rintro ⟨-, h⟩; have := (S.mem_Lvl.1 h).2.1; omega

/-- A step of `e` or `e'` in case (i) at the component `i`: [II, Claim A.4 (ii)]. -/
private theorem CaseI.stepE {l : List E} {T : MGraph V E} {x : E} (hx : x = S.e ∨ x = S.e')
    (hxl : x ∉ l) (hT : T.IsRedundant x)
    (hle : Le T ((Z.convert l).collapse (S.Lvl (i + 1) (j + 1)) S.w)) :
    (Z.convert l).IsRedundant x := by
  obtain ⟨hL, hwL, hI⟩ := hC.lower hZ le_rfl hC.hij
  obtain ⟨p1, -, p3⟩ := hC.path hZ hx
  refine red_quot (hL l) hwL (by rw [convert_ends]; exact p3) (hI l) (red_le hT hle ?_)
  rw [collapse_cls, convert_cls_of_not_mem hxl, p1]

/-- The steps of the component `i` in case (i): the order of the graph of the component, with
`e` replaced by `e`, `e'` in the order given by [II, Claim A.4 (ii)]. -/
private theorem CaseI.tier_top {pre : List E}
    (hpre : ∀ y ∈ pre, (Z.ends y).1 ∈ S.Lvl (i + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (i + 1) (j + 1))
    {α β : List E} (hord : S.ordR i = α ++ S.e :: β) :
    ∃ γ : List E, (γ = [S.e, S.e'] ∨ γ = [S.e', S.e]) ∧
      Steps (Z.convert pre) (S.J i ++ α ++ γ ++ β) := by
  have hik : i < S.k := lt_of_lt_of_le hC.hij hC.hjk
  have hij := hC.hij
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have hnd := (S.ordR_spec hik).1
  rw [hord] at hnd
  have hlen : α.length < (S.ordR i).length := by rw [hord]; simp
  have hre : ((S.Rep i i).convert α).IsRedundant S.e := by
    have := red_Rep (S := S) le_rfl hik hlen
    simp only [hord, List.take_left', List.getElem_append_right le_rfl, Nat.sub_self,
      List.getElem_cons_zero] at this
    exact this
  -- the facts on the edges of the lists
  have memα : ∀ y ∈ α, y ∈ S.ordR i := fun y hy => by rw [hord]; simp [hy]
  have memβ : ∀ y ∈ β, y ∈ S.ordR i := fun y hy => by rw [hord]; simp [hy]
  have lev_ord : ∀ y ∈ S.ordR i, G.cls y = some .plus ∧ (G.ends y).1 ∈ G.int ∧
      S.lev (G.ends y).1 = i ∧ (G.ends y).2 ∈ G.int ∧ S.lev (G.ends y).2 = i :=
    fun y hy => (S.mem_ordR hik y).1 hy
  have eα : S.e ∉ α := fun h => (List.nodup_append.1 hnd).2.2 _ h _ List.mem_cons_self rfl
  have eβ : S.e ∉ β := fun h => (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 h
  have e'ord : ∀ y ∈ S.ordR i, y ≠ S.e' := fun y hy h => by
    have := (lev_ord y hy).1; rw [h, S.ce'] at this; cases this
  have c'ord : ∀ y ∈ S.ordR i, y ≠ S.cc' i := fun y hy h => by
    obtain ⟨-, -, a, -, b⟩ := lev_ord y hy
    obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hik (Or.inr h)
    omega
  have notpre : ∀ y, ¬ ((Z.ends y).1 ∈ S.Lvl (i + 1) (j + 1) ∧
      (Z.ends y).2 ∈ S.Lvl (i + 1) (j + 1)) → y ∉ pre := fun y h h' => h (hpre y h')
  have ordL : ∀ y ∈ S.ordR i, y ≠ S.e → y ∉ pre ∧ Z.cls y = some .plus ∧
      ¬ ((Z.ends y).1 ∈ S.Lvl (i + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (i + 1) (j + 1)) := by
    intro y hy hye
    obtain ⟨hp, a1, a2, b1, b2⟩ := lev_ord y hy
    obtain ⟨z1, z2⟩ := hZ.edge hye (e'ord y hy) a1 (by omega) (by omega) b1 (by omega) (by omega)
    have hn : ¬ ((Z.ends y).1 ∈ S.Lvl (i + 1) (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl (i + 1) (j + 1)) := by
      rw [z1]; rintro ⟨h, -⟩; have := (S.mem_Lvl.1 h).2.1; omega
    exact ⟨notpre y hn, z2.trans hp, hn⟩
  obtain ⟨-, -, pe3⟩ := hC.path hZ (Or.inl rfl)
  obtain ⟨-, -, pe3'⟩ := hC.path hZ (Or.inr rfl)
  have epre : S.e ∉ pre := notpre _ pe3
  have e'pre : S.e' ∉ pre := notpre _ pe3'
  have eJ : S.e ∉ S.J i := fun h => hC.e_ne_cc' hik (mem_J h).1
  have e'J : S.e' ∉ S.J i := fun h => S.e'_ne_cc' hik (mem_J h).1
  have hJ := S.J_or hik
  -- the graph of [II, Claim A.4 (ii)]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hC.rep_hyps le_rfl hij α
  rw [if_neg eα] at h11
  have hA4 := (MGraph.claimA4 V E _ S.w (S.cc i) (S.cc' i) S.e S.e' hre.2.1 h1 h2 h3 h11 h4 h5 h6 h7
    h8 h9 h10).2 hre
  have hleα := hC.le_A4 hZ le_rfl hij (l := pre ++ S.J i ++ α) (m := α) (fun y hy => by
      simp only [List.mem_append] at hy
      rcases hy with (h | h) | h
      · exact Or.inl (hpre y h)
      · exact Or.inr (Or.inl (mem_J h).1)
      · exact Or.inr (Or.inr (Or.inl h)))
    (fun y hy => by simp [hy])
    (iff_of_false (by simp only [List.mem_append, not_or]; exact ⟨⟨e'pre, e'J⟩, fun h =>
      e'ord _ (memα _ h) rfl⟩) eα)
    (hJ.imp id (fun h => by simp [h]))
  have hlα : ∀ y ∈ pre ++ S.J i ++ α, y ≠ S.e ∧ y ≠ S.e' := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with (h | h) | h
    · exact ⟨fun h' => epre (h' ▸ h), fun h' => e'pre (h' ▸ h)⟩
    · exact ⟨fun h' => eJ (h' ▸ h), fun h' => e'J (h' ▸ h)⟩
    · exact ⟨fun h' => eα (h' ▸ h), e'ord y (memα y h)⟩
  have hndα : α.Nodup := (List.nodup_append.1 hnd).1
  have hndβ : β.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
  have hαβ : ∀ y ∈ α, y ∉ β := fun y hy hy' =>
    (List.nodup_append.1 hnd).2.2 _ hy _ (List.mem_cons_of_mem _ hy') rfl
  -- the steps of `α`
  have stα : Steps ((Z.convert pre).convert (S.J i)) α := by
    intro t ht
    rw [convert_convert', convert_convert', ← List.append_assoc]
    have ht' : t < (S.ordR i).length := by rw [hord]; simp; omega
    have hr := red_Rep (S := S) le_rfl hik ht'
    simp only [hord, List.take_append_of_le_length ht.le, List.getElem_append_left ht] at hr
    have hxα : α[t] ∈ α := List.getElem_mem ht
    have hxe : α[t] ≠ S.e := fun h => eα (h ▸ hxα)
    obtain ⟨xp, xc, xL⟩ := ordL _ (memα _ hxα) hxe
    refine hC.stepA hZ le_rfl hij (m := α.take t) (fun y hy => ?_)
      (fun y hy => List.mem_append_right _ hy)
      (iff_of_false ?_ ?_) (hJ.imp id (fun h => by simp [h])) xL hxe hr ?_
    · simp only [List.mem_append] at hy
      rcases hy with (h | h) | h
      · exact Or.inl (hpre y h)
      · exact Or.inr (Or.inl (mem_J h).1)
      · exact Or.inr (Or.inr (Or.inl h))
    · simp only [List.mem_append, not_or]
      exact ⟨⟨e'pre, e'J⟩, fun h => e'ord _ (memα _ (List.mem_of_mem_take h)) rfl⟩
    · exact fun h => eα (List.mem_of_mem_take h)
    · rw [convert_cls_of_not_mem, xc]
      simp only [List.mem_append, not_or]
      exact ⟨⟨xp, fun h => c'ord _ (memα _ hxα) (mem_J h).1⟩,
        getElem_not_mem_take hndα ht⟩
  -- the steps of `β`
  have stβ : ∀ γ : List E, (γ = [S.e, S.e'] ∨ γ = [S.e', S.e]) →
      Steps ((Z.convert pre).convert (S.J i ++ α ++ γ)) β := by
    intro γ hγ t ht
    have mγ : ∀ y, y ∈ γ ↔ y = S.e ∨ y = S.e' := by
      intro y; rcases hγ with rfl | rfl <;> simp [or_comm]
    rw [convert_convert', convert_convert']
    have ht' : α.length + 1 + t < (S.ordR i).length := by rw [hord]; simp; omega
    have hr := red_Rep (S := S) le_rfl hik ht'
    have hg : (S.ordR i)[α.length + 1 + t] = β[t] := by
      simp only [hord]; exact getElem_mid S.e α β t ht _
    rw [hg] at hr
    simp only [hord, take_mid] at hr
    have hxβ : β[t] ∈ β := List.getElem_mem ht
    have hxe : β[t] ≠ S.e := fun h => eβ (h ▸ hxβ)
    obtain ⟨xp, xc, xL⟩ := ordL _ (memβ _ hxβ) hxe
    have toL : ∀ y, y ∈ pre ∨ y ∈ S.J i ∨ y ∈ α ∨ y ∈ γ ∨ y ∈ β.take t →
        y ∈ pre ++ (S.J i ++ α ++ γ ++ β.take t) := by
      intro y h; simpa only [List.mem_append, or_assoc] using h
    have ofL : ∀ y, y ∈ pre ++ (S.J i ++ α ++ γ ++ β.take t) →
        y ∈ pre ∨ y ∈ S.J i ∨ y ∈ α ∨ y ∈ γ ∨ y ∈ β.take t := by
      intro y h; simpa only [List.mem_append, or_assoc] using h
    refine hC.stepA hZ le_rfl hij (m := α ++ S.e :: β.take t) (fun y hy => ?_) (fun y hy => ?_)
      (iff_of_true (toL _ (Or.inr (Or.inr (Or.inr (Or.inl ((mγ _).2 (Or.inr rfl))))))) (by simp))
      (hJ.imp id (fun h => toL _ (Or.inr (Or.inl h)))) xL hxe hr ?_
    · rcases ofL y hy with h | h | h | h | h
      · exact Or.inl (hpre y h)
      · exact Or.inr (Or.inl (mem_J h).1)
      · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ h)))
      · rcases (mγ y).1 h with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl (by simp)))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (by simp [h])))
    · have hy' : y ∈ α ∨ y = S.e ∨ y ∈ β.take t := by
        simpa only [List.mem_append, List.mem_cons] using hy
      apply toL
      rcases hy' with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((mγ y).2 (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rw [convert_cls_of_not_mem, xc]
      intro h
      rcases ofL _ h with h | h | h | h | h
      · exact xp h
      · exact c'ord _ (memβ _ hxβ) (mem_J h).1
      · exact hαβ _ h hxβ
      · rcases (mγ _).1 h with h | h
        · exact hxe h
        · exact e'ord _ (memβ _ hxβ) h
      · exact getElem_not_mem_take hndβ ht h
  have hlα' : S.e ∉ pre ++ S.J i ++ α ∧ S.e' ∉ pre ++ S.J i ++ α := by
    simp only [List.mem_append, not_or]
    exact ⟨⟨⟨epre, eJ⟩, eα⟩, ⟨⟨e'pre, e'J⟩, fun h => e'ord _ (memα _ h) rfl⟩⟩
  have ne1 : S.e' ∉ pre ++ S.J i ++ α ++ [S.e] := by
    rw [List.mem_append, List.mem_singleton, not_or]; exact ⟨hlα'.2, S.hne.symm⟩
  have ne2 : S.e ∉ pre ++ S.J i ++ α ++ [S.e'] := by
    rw [List.mem_append, List.mem_singleton, not_or]; exact ⟨hlα'.1, S.hne⟩
  refine hA4.elim (fun ⟨r1, r2⟩ => ⟨[S.e, S.e'], Or.inl rfl, ?_⟩)
    (fun ⟨r1, r2⟩ => ⟨[S.e', S.e], Or.inr rfl, ?_⟩)
  · rw [steps_append, steps_append, steps_append]
    refine ⟨⟨⟨hC.stepJ hZ le_rfl hij hpre, stα⟩, ?_⟩, stβ _ (Or.inl rfl)⟩
    rw [convert_convert', ← List.append_assoc, steps_cons, steps_single, convert_convert']
    refine ⟨hC.stepE hZ (Or.inl rfl) hlα'.1 r1 hleα, ?_⟩
    refine hC.stepE hZ (Or.inr rfl) ne1 r2 ?_
    rw [← convert_convert', collapse_convert]
    exact leS_convert hleα (fun _ _ _ => rfl) [S.e]
  · rw [steps_append, steps_append, steps_append]
    refine ⟨⟨⟨hC.stepJ hZ le_rfl hij hpre, stα⟩, ?_⟩, stβ _ (Or.inr rfl)⟩
    rw [convert_convert', ← List.append_assoc, steps_cons, steps_single, convert_convert']
    refine ⟨hC.stepE hZ (Or.inr rfl) hlα'.2 r1 hleα, ?_⟩
    refine hC.stepE hZ (Or.inl rfl) ne2 r2 ?_
    rw [← convert_convert', collapse_convert]
    exact leS_convert hleα (fun _ _ _ => rfl) [S.e']

/-- The quotient graph by the last component in case (i) is doubly connected: the subgraph induced
on the components `i, …, j - 1`, with `e` replaced by the path through `w`, and `w` joined to it by
`cc (j - 1)` and `cc' (j - 1)`. -/
private theorem CaseI.botQ {l : List E} (hel : S.e ∉ l) (hel' : S.e' ∉ l) :
    ((Z.convert l).collapse (S.Lvl j (j + 1)) S.w).DC := by
  have hij := hC.hij
  have hjk := hC.hjk
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have hj1 : j - 1 < S.k := by omega
  have hjj : j - 1 + 1 = j := by omega
  have notΓ : ∀ v, S.lev v < j → v ∉ S.Lvl j (j + 1) := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have hwΓ : S.w ∈ S.Lvl j (j + 1) := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  obtain ⟨p1, p2, -⟩ := hC.path hZ (Or.inl rfl)
  obtain ⟨p1', p2', -⟩ := hC.path hZ (Or.inr rfl)
  have ze : Z.ends S.e = ((G.ends S.e).1, S.w) := by
    rcases p2 with h | h
    · exact h
    · have := hZ.gedge (x := S.e) (by rw [split_ends_e]; exact hC.ha)
        (by rw [split_ends_e]; dsimp only; omega) (by rw [split_ends_e]; dsimp only; omega)
        (by rw [split_ends_e]; exact S.hw) (by rw [split_ends_e]; dsimp only; omega)
        (by rw [split_ends_e]; dsimp only; omega)
      rw [this.1, split_ends_e]
  have ze' : Z.ends S.e' = (S.w, (G.ends S.e).2) := by
    have := hZ.gedge (x := S.e') (by rw [split_ends_e' S.hne]; exact S.hw)
      (by rw [split_ends_e' S.hne]; dsimp only; omega)
      (by rw [split_ends_e' S.hne]; dsimp only; omega)
      (by rw [split_ends_e' S.hne]; exact hC.hb) (by rw [split_ends_e' S.hne]; dsimp only; omega)
      (by rw [split_ends_e' S.hne]; dsimp only; omega)
    rw [this.1, split_ends_e' S.hne]
  have hRp : ∀ f, (G.induce (S.Lvl i j)).Pres f → (G.ends f).1 ∈ S.Lvl i j ∧
      (G.ends f).2 ∈ S.Lvl i j ∧ (G.induce (S.Lvl i j)).cls f = G.cls f := by
    intro f hf
    have hin : (G.ends f).1 ∈ S.Lvl i j ∧ (G.ends f).2 ∈ S.Lvl i j := by
      by_contra hn; exact hf.1 (by simp [MGraph.induce, hn])
    exact ⟨hin.1, hin.2, by simp [MGraph.induce, hin]⟩
  have hcr : ∀ y, (y = S.cc (j - 1) ∨ y = S.cc' (j - 1)) → ¬ (G.induce (S.Lvl i j)).Pres y ∧
      (Z.convert l).cls y = G.cls y ∧ Z.ends y = G.ends y ∨ True := fun _ _ => Or.inr trivial
  have hnotR : ∀ y, (y = S.cc (j - 1) ∨ y = S.cc' (j - 1)) → ¬ (G.induce (S.Lvl i j)).Pres y := by
    intro y hy hp
    obtain ⟨h1, h2, -⟩ := hRp y hp
    obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hj1 hy
    have := (S.mem_Lvl.1 h1).2.2
    have := (S.mem_Lvl.1 h2).2.2
    omega
  have hy : ∀ y, (y = S.cc (j - 1) ∨ y = S.cc' (j - 1)) →
      Z.ends y = G.ends y ∧ Z.cls y = G.cls y := by
    intro y hy
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hj1 hy
    have hye : y ≠ S.e := by
      rcases hy with rfl | rfl
      · exact (S.e_ne_cc hj1).symm
      · exact (hC.e_ne_cc' hj1).symm
    have hye' : y ≠ S.e' := by
      rcases hy with rfl | rfl
      · exact (S.e'_ne_cc hj1).symm
      · exact (S.e'_ne_cc' hj1).symm
    exact hZ.edge hye hye' g1 (by omega) (by omega) g2 (by omega) (by omega)
  obtain ⟨y1e, y1c⟩ := hy _ (Or.inl rfl)
  obtain ⟨y2e, y2c⟩ := hy _ (Or.inr rfl)
  have cy1 := cc_collapse (S := S) (b := j) hj1 (by omega) (Or.inl rfl)
  have cy2 := cc_collapse (S := S) (b := j) hj1 (by omega) (Or.inr rfl)
  have hLL : S.Lvl (j - 1 + 1) (j + 1) = S.Lvl j (j + 1) := by rw [hjj]
  rw [hLL] at cy1 cy2
  obtain ⟨hu1, hlu1⟩ := S.u_mem hj1
  obtain ⟨hu2, hlu2⟩ := S.u'_mem hj1
  have aL : (G.ends S.e).1 ∈ S.Lvl i j := S.mem_Lvl.2 ⟨hC.ha, by omega, by omega⟩
  have bL : (G.ends S.e).2 ∈ S.Lvl i j := S.mem_Lvl.2 ⟨hC.hb, by omega, by omega⟩
  have hRe : (G.induce (S.Lvl i j)).cls S.e = some .plus := by simp [MGraph.induce, aL, bL, S.ce]
  refine dc_path (R := G.induce (S.Lvl i j)) (N := S.w) (g := S.e) (g₁ := S.e) (g₂ := S.e')
    (y₁ := S.cc (j - 1)) (y₂ := S.cc' (j - 1)) (m₁ := S.u (j - 1)) (m₂ := S.u' (j - 1))
    (S.toSplitCtx.dc_Lvl j (by omega)) ?_ ?_ ?_ ?_
  · rw [collapse_convert, convert_int]
    have := hZ.collapse_int (c := j - 1) (by omega) (by omega) (by omega) (by omega)
    rw [hjj] at this
    exact this
  · intro f hf hfe
    obtain ⟨a1, a2, hcl⟩ := hRp f hf
    obtain ⟨a1i, a1a, a1b⟩ := S.mem_Lvl.1 a1
    obtain ⟨a2i, a2a, a2b⟩ := S.mem_Lvl.1 a2
    have hfe' : f ≠ S.e' := by rintro rfl; exact hf.1 (by rw [hcl, S.ce'])
    obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1i a1a (by omega) a2i a2a (by omega)
    refine ⟨?_, ?_⟩
    · rw [collapse_cls, convert_cls, z2, hcl]
      split_ifs with h
      · exact Or.inr ⟨h.2, rfl⟩
      · exact Or.inl rfl
    · rw [collapse_convert_ends, z1, if_neg (notΓ _ (by omega)), if_neg (notΓ _ (by omega))]
      exact sameEnds_refl _
  · intro _
    refine ⟨?_, ?_, ?_, ?_, fun f hf hfe => ⟨hfe, ?_⟩⟩
    · rw [collapse_cls, convert_cls_of_not_mem hel, p1, hRe]
    · rw [collapse_cls, convert_cls_of_not_mem hel', p1', hRe]
    · rw [collapse_convert_ends, ze]
      simp only [notΓ _ (show S.lev (G.ends S.e).1 < j by omega), hwΓ, ↓reduceIte]
      exact sameEnds_refl _
    · rw [collapse_convert_ends, ze']
      simp only [notΓ _ (show S.lev (G.ends S.e).2 < j by omega), hwΓ, ↓reduceIte]
      exact sameEnds_refl _
    · rintro rfl
      obtain ⟨-, -, hcl⟩ := hRp _ hf
      exact hf.1 (by rw [hcl, S.ce'])
  · intro _
    refine ⟨?_, ?_, ?_, ?_, S.mem_Lvl.2 ⟨hu1, by omega, by omega⟩,
      S.mem_Lvl.2 ⟨hu2, by omega, by omega⟩, S.cc_ne _ hj1, fun f hf _ => ⟨?_, ?_⟩,
      fun _ => ⟨(S.e_ne_cc hj1).symm, (S.e'_ne_cc hj1).symm, (hC.e_ne_cc' hj1).symm,
        (S.e'_ne_cc' hj1).symm⟩⟩
    · rw [collapse_cls, convert_cls, y1c, S.cc_diff _ hj1]; simp
    · rw [collapse_cls, convert_cls, y2c]
      rcases S.cc'_cls _ hj1 with h | h <;> rw [h] <;> split_ifs <;> simp
    · rw [collapse_convert_ends, y1e]; exact cy1
    · rw [collapse_convert_ends, y2e]; exact cy2
    · rintro rfl; exact hnotR _ (Or.inl rfl) hf
    · rintro rfl; exact hnotR _ (Or.inr rfl) hf

/-- **Case (i) of [II, Lemma 5.12]**: the graph after operation (B) on the components `i, …, j`,
with the ends of `e` in the component `i` and `w` in the component `j`, is pre-deterministic. -/
private theorem CaseI.preDet {B : MGraph V E} (hB : S.IsB B j x₁ x₂) (hBpd : B.PreDet)
    (hx12 : j < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e') : Z.PreDet := by
  obtain ⟨-, ℓB, hℓ⟩ := hBpd
  have hij := hC.hij
  have hjk := hC.hjk
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have hik : i < S.k := by omega
  have ℓB_lev : ∀ y ∈ ℓB, G.cls y = some .plus ∧ (G.ends y).1 ∈ G.int ∧ S.lev (G.ends y).1 = j ∧
      (G.ends y).2 ∈ G.int ∧ S.lev (G.ends y).2 = j := fun y hy => (hB.ip y).1 ((hℓ.2.1 y).1 hy)
  have ℓBe : ∀ y ∈ ℓB, y ≠ S.e ∧ y ≠ S.e' := by
    intro y hy
    obtain ⟨hp, -, h1, -, -⟩ := ℓB_lev y hy
    exact ⟨by rintro rfl; omega, by rintro rfl; rw [S.ce'] at hp; cases hp⟩
  have hbot : Steps Z ℓB := hZ.tier_bot hij.le hlw hB hℓ hx12 (fun ⟨_, h, _⟩ => by omega)
    (fun t => hC.botQ hZ (fun h => (ℓBe _ (List.mem_of_mem_take h)).1 rfl)
      (fun h => (ℓBe _ (List.mem_of_mem_take h)).2 rfl))
  -- the components of the edges
  let ins : ℕ → E → Prop := fun c y => (Z.ends y).1 ∈ S.Lvl c (j + 1) ∧
    (Z.ends y).2 ∈ S.Lvl c (j + 1)
  have hmono : ∀ c c' y, c' ≤ c → ins c y → ins c' y := by
    intro c c' y h ⟨h1, h2⟩
    obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 h1
    obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 h2
    exact ⟨S.mem_Lvl.2 ⟨a1, by omega, a3⟩, S.mem_Lvl.2 ⟨b1, by omega, b3⟩⟩
  have insG : ∀ y c, y ≠ S.e → y ≠ S.e' → (G.ends y).1 ∈ G.int → (G.ends y).2 ∈ G.int →
      c ≤ S.lev (G.ends y).1 → S.lev (G.ends y).1 ≤ j → c ≤ S.lev (G.ends y).2 →
      S.lev (G.ends y).2 ≤ j → i ≤ c → ins c y := by
    intro y c h1 h2 a1 b1 a2 a3 b2 b3 hc
    obtain ⟨z1, -⟩ := hZ.edge h1 h2 a1 (by omega) a3 b1 (by omega) b3
    show (Z.ends y).1 ∈ S.Lvl c (j + 1) ∧ (Z.ends y).2 ∈ S.Lvl c (j + 1)
    rw [z1]
    exact ⟨S.mem_Lvl.2 ⟨a1, a2, by omega⟩, S.mem_Lvl.2 ⟨b1, b2, by omega⟩⟩
  have hbotin : ∀ y ∈ ℓB, ins j y := by
    intro y hy
    obtain ⟨-, a1, a2, b1, b2⟩ := ℓB_lev y hy
    exact insG y j (ℓBe y hy).1 (ℓBe y hy).2 a1 b1 (by omega) (by omega) (by omega) (by omega)
      hij.le
  -- the edges of the components `c`, `i < c < j`
  have Jlev : ∀ c, c < S.k → ∀ y ∈ S.J c, G.cls y = some .plus ∧ y ≠ S.e ∧ y ≠ S.e' ∧
      (G.ends y).1 ∈ G.int ∧ (G.ends y).2 ∈ G.int ∧ ((S.lev (G.ends y).1 = c ∧
        S.lev (G.ends y).2 = c + 1) ∨ (S.lev (G.ends y).1 = c + 1 ∧ S.lev (G.ends y).2 = c)) := by
    intro c hc y hy
    obtain ⟨rfl, hp⟩ := mem_J hy
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hc (Or.inr rfl)
    exact ⟨hp, (hC.e_ne_cc' hc).symm, (S.e'_ne_cc' hc).symm, g1, g2, g3⟩
  have ordlev : ∀ c, c < S.k → ∀ y ∈ S.ordR c, G.cls y = some .plus ∧ (G.ends y).1 ∈ G.int ∧
      S.lev (G.ends y).1 = c ∧ (G.ends y).2 ∈ G.int ∧ S.lev (G.ends y).2 = c :=
    fun c hc y hy => (S.mem_ordR hc y).1 hy
  have hin : ∀ c, i < c → c < j → ∀ y ∈ S.J c ++ S.ordR c, ins c y := by
    intro c h1 h2 y hy
    have hc : c < S.k := by omega
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨-, n1, n2, a1, b1, hl⟩ := Jlev c hc y h
      rcases hl with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;>
        exact insG y c n1 n2 a1 b1 (by omega) (by omega) (by omega) (by omega) h1.le
    · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev c hc y h
      exact insG y c (by rintro rfl; omega) (by rintro rfl; rw [S.ce'] at hp; cases hp) a1 b1
        (by omega) (by omega) (by omega) (by omega) h1.le
  obtain ⟨hst, hins⟩ := steps_tiers hij (fun c => S.J c ++ S.ordR c) ℓB ins hmono hbot hbotin
    (fun c h1 h2 pre hpre => hC.tier_mid hZ h1 h2 hpre) hin
  -- the component `i`
  have he_ord : S.e ∈ S.ordR i := (S.mem_ordR hik _).2 ⟨S.ce, hC.ha, hla, hC.hb, hlb⟩
  obtain ⟨α, β, hord⟩ := List.append_of_mem he_ord
  obtain ⟨γ, hγ, hsγ⟩ := hC.tier_top hZ hins hord
  have hq := steps_append.2 ⟨hst, hsγ⟩
  have mγ : ∀ y, y ∈ γ ↔ y = S.e ∨ y = S.e' := by
    intro y; rcases hγ with rfl | rfl <;> simp [or_comm]
  refine preDet_of_steps (steps_dc hq (List.ne_nil_of_mem (a := S.e) (by simp [mγ]))) hq
    fun x => ?_
  -- the internal blue solid edges
  have mα : ∀ y ∈ α, y ∈ S.ordR i := fun y hy => by rw [hord]; simp [hy]
  have mβ : ∀ y ∈ β, y ∈ S.ordR i := fun y hy => by rw [hord]; simp [hy]
  by_cases hxe : x = S.e ∨ x = S.e'
  · have hxq : x ∈ (ℓB ++ midL (fun c => S.J c ++ S.ordR c) j (j - 1 - i)) ++
        (S.J i ++ α ++ γ ++ β) := by simp [(mγ x).2 hxe]
    refine iff_of_true hxq ?_
    obtain ⟨p1, p2, -⟩ := hC.path hZ hxe
    have ma : (G.ends S.e).1 ∈ Z.int := (hZ.int _).2 ⟨hC.ha, by omega, by omega⟩
    have mb : (G.ends S.e).2 ∈ Z.int := (hZ.int _).2 ⟨hC.hb, by omega, by omega⟩
    have mw : S.w ∈ Z.int := (hZ.int _).2 ⟨S.hw, by omega, by omega⟩
    refine ⟨p1, ?_⟩
    rcases p2 with h | h <;> rw [h]
    · exact ⟨ma, mw⟩
    · exact ⟨mw, mb⟩
  rw [not_or] at hxe
  rw [hZ.intPlus x hxe.1 hxe.2]
  simp only [List.mem_append, mem_midL, mγ, hxe.1, hxe.2, or_false]
  constructor
  · rintro ((h | ⟨d', hd, h⟩) | ((h | h) | h))
    · obtain ⟨hp, a1, a2, b1, b2⟩ := ℓB_lev x h
      exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
    · have hc : j - 1 - d' < S.k := by omega
      rcases h with h | h
      · obtain ⟨hp, -, -, a1, b1, hl⟩ := Jlev _ hc x h
        rcases hl with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;>
          exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
      · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev _ hc x h
        exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
    · obtain ⟨hp, -, -, a1, b1, hl⟩ := Jlev _ hik x h
      rcases hl with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;>
        exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
    · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev _ hik x (mα x h)
      exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
    · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev _ hik x (mβ x h)
      exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
  · rintro ⟨hp, a1, a2, a3, b1, b2, b3⟩
    rcases S.lev_plus hp a1 b1 with hl | ⟨l, hl, rfl, hlv⟩
    · -- inside one component
      by_cases hcj : S.lev (G.ends x).1 = j
      · exact Or.inl (Or.inl ((hℓ.2.1 x).2 ((hB.ip x).2 ⟨hp, a1, hcj, b1, by omega⟩)))
      by_cases hci : S.lev (G.ends x).1 = i
      · have hx : x ∈ S.ordR i := (S.mem_ordR hik x).2 ⟨hp, a1, hci, b1, by omega⟩
        rw [hord] at hx
        rcases List.mem_append.1 hx with h | h
        · exact Or.inr (Or.inl (Or.inr h))
        · rcases List.mem_cons.1 h with h | h
          · exact absurd h hxe.1
          · exact Or.inr (Or.inr h)
      · refine Or.inl (Or.inr ⟨j - 1 - S.lev (G.ends x).1, by omega, ?_⟩)
        rw [show j - 1 - (j - 1 - S.lev (G.ends x).1) = S.lev (G.ends x).1 by omega]
        exact Or.inr ((S.mem_ordR (by omega) x).2 ⟨hp, a1, rfl, b1, by omega⟩)
    · -- the crossing edge `cc' l`
      have hJ : S.cc' l ∈ S.J l := by unfold J; rw [if_pos hp]; exact List.mem_singleton_self _
      by_cases hli : l = i
      · subst hli; exact Or.inr (Or.inl (Or.inl hJ))
      · refine Or.inl (Or.inr ⟨j - 1 - l, by omega, ?_⟩)
        rw [show j - 1 - (j - 1 - l) = l by omega]
        exact Or.inl hJ

end CaseI

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-! ### Cases (iii) and (v) of [II, Lemma 5.12] -/

/-- The setting of cases (iii) and (v) of [II, Lemma 5.12]: `e` joins the vertex `t` of the
component `s` to a vertex `v` outside `P s` (in the component `s - 1`, or external); `w` lies in
the component `j > s`; after the operation, `y` joins `w` to `t` and `z` joins `w` to `v`. -/
structure CaseT (S : SC G) (s j : ℕ) (y z : E) (t v : V) : Prop where
  hsj : s < j
  hjk : j ≤ S.k
  hyz : (y = S.e ∧ z = S.e') ∨ (y = S.e' ∧ z = S.e)
  ht : t ∈ G.int
  hlt : S.lev t = s
  hlw : S.lev S.w = j
  hy : SameEnds (S.Gt.ends y) (S.w, t)
  hz : SameEnds (S.Gt.ends z) (S.w, v)
  hv : v ∉ G.int ∨ S.lev v < s
  hev : SameEnds (G.ends S.e) (t, v)

variable {s j : ℕ} {y z : E} {t v : V}

private theorem CaseT.y_ne (hT : S.CaseT s j y z t v) : y ≠ z := by
  rcases hT.hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact S.hne
  · exact S.hne.symm

/-- The edge `e` does not join two internal vertices of the components from `s` on. -/
private theorem CaseT.e_out (hT : S.CaseT s j y z t v) {a : ℕ} (hsa : s ≤ a) :
    ¬ ((G.ends S.e).1 ∈ G.int ∧ a ≤ S.lev (G.ends S.e).1 ∧ (G.ends S.e).2 ∈ G.int ∧
      a ≤ S.lev (G.ends S.e).2) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases sameEnds_iff.1 hT.hev with ⟨-, h⟩ | ⟨h, -⟩
  · rw [h] at h3 h4; dsimp only at h3 h4
    rcases hT.hv with h' | h' <;> [exact h' h3; omega]
  · rw [h] at h1 h2; dsimp only at h1 h2
    rcases hT.hv with h' | h' <;> [exact h' h1; omega]

private theorem CaseT.e_ne_cc (hT : S.CaseT s j y z t v) {l : ℕ} (hl : l < S.k) (hsl : s ≤ l) {x : E}
    (hx : x = S.cc l ∨ x = S.cc' l) : S.e ≠ x := by
  rintro rfl
  obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hl hx
  exact hT.e_out hsl ⟨g1, by omega, g2, by omega⟩

/-- The edge `y`: a blue solid edge between `w` and `t`. -/
private theorem CaseT.y_cls (hT : S.CaseT s j y z t v) : S.Gt.cls y = some .plus := by
  rcases hT.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [split_cls_of S.hne, S.ce]
  · rw [split_cls_e', S.ce]

/-- The edge `y` is absent from the subgraphs of `G` induced on sets of internal vertices of the
components from `s` on. -/
private theorem CaseT.induce_y (hT : S.CaseT s j y z t v) {a b : ℕ} (hsa : s ≤ a) :
    (G.induce (S.Lvl a b)).cls y = none := by
  rcases hT.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · have : ¬ ((G.ends S.e).1 ∈ S.Lvl a b ∧ (G.ends S.e).2 ∈ S.Lvl a b) := by
      rintro ⟨h1, h2⟩
      obtain ⟨a1, a2, -⟩ := S.mem_Lvl.1 h1
      obtain ⟨b1, b2, -⟩ := S.mem_Lvl.1 h2
      exact hT.e_out hsa ⟨a1, a2, b1, b2⟩
    simp [MGraph.induce, this]
  · exact induce_cls_e'

section CaseT

variable (hT : S.CaseT s j y z t v) {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z s j x₁ x₂)
include hT hZ

/-- The edge `y` in the graph of cases (iii), (v): a blue solid edge from `w` to `t`. -/
private theorem CaseT.yZ : Z.cls y = some .plus ∧ SameEnds (Z.ends y) (S.w, t) := by
  have hsj := hT.hsj
  have hlt := hT.hlt
  have hlw := hT.hlw
  have hp : (S.Gt.ends y).1 ∈ G.int ∧ s ≤ S.lev (S.Gt.ends y).1 ∧ S.lev (S.Gt.ends y).1 ≤ j ∧
      (S.Gt.ends y).2 ∈ G.int ∧ s ≤ S.lev (S.Gt.ends y).2 ∧ S.lev (S.Gt.ends y).2 ≤ j := by
    rcases sameEnds_iff.1 hT.hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> dsimp only
    · exact ⟨S.hw, by omega, by omega, hT.ht, by omega, by omega⟩
    · exact ⟨hT.ht, by omega, by omega, S.hw, by omega, by omega⟩
  obtain ⟨a1, a2, a3, b1, b2, b3⟩ := hp
  obtain ⟨z1, z2⟩ := hZ.gedge a1 a2 a3 b1 b2 b3
  exact ⟨z2.trans hT.y_cls, by rw [z1]; exact hT.hy⟩

/-- The components `c + 1, …, j` of the graph of cases (iii), (v). -/
private theorem CaseT.lower {c : ℕ} (hsc : s ≤ c) (hcj : c < j) :
    (∀ l : List E, S.Lvl (c + 1) (j + 1) ⊆ (Z.convert l).int) ∧ S.w ∈ S.Lvl (c + 1) (j + 1) ∧
      (∀ l : List E, ((Z.convert l).induce (S.Lvl (c + 1) (j + 1))).DC) ∧
      (∀ x, SameEnds (Z.ends x) (S.w, t) →
        ¬ ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1))) := by
  have hlw := hT.hlw
  have hlt := hT.hlt
  refine ⟨fun l v hv => ?_, S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩, fun l => ?_, fun x hx => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    rw [convert_int]
    exact (hZ.int v).2 ⟨h1, by omega, by omega⟩
  · refine hZ.dc_lower hsc hcj hT.hjk (fun h => ?_) l
    obtain ⟨a1, a2, -⟩ := S.mem_Lvl.1 h.1
    obtain ⟨b1, b2, -⟩ := S.mem_Lvl.1 h.2
    exact hT.e_out (a := c + 1) (by omega) ⟨a1, a2, b1, b2⟩
  · have htL : t ∉ S.Lvl (c + 1) (j + 1) := fun h => by have := (S.mem_Lvl.1 h).2.1; omega
    rcases sameEnds_iff.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact fun h => htL h.2
    · exact fun h => htL h.1

/-- The step of `y` in cases (iii), (v): `y` is redundant, the graph being doubly connected
without it. -/
private theorem CaseT.stepY {l : List E} (hyl : y ∉ l) : (Z.convert l).IsRedundant y := by
  have hsj := hT.hsj
  have hjk := hT.hjk
  obtain ⟨yc, -⟩ := hT.yZ hZ
  have hle : Le (G.induce (S.Lvl s (j + 1))) Z := by
    refine ⟨?_, fun x hx => ?_⟩
    · ext v
      change v ∈ S.Lvl s (j + 1) ↔ _
      rw [S.mem_Lvl, hZ.int]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by omega⟩
    have hin : (G.ends x).1 ∈ S.Lvl s (j + 1) ∧ (G.ends x).2 ∈ S.Lvl s (j + 1) := by
      by_contra hn; exact hx.1 (by simp [MGraph.induce, hn])
    obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
    obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
    have hxe : x ≠ S.e := by rintro rfl; exact hT.e_out le_rfl ⟨a1, a2, b1, b2⟩
    have hxe' : x ≠ S.e' := by rintro rfl; exact hx.1 induce_cls_e'
    obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 a2 (by omega) b1 b2 (by omega)
    simp only [id, MGraph.induce, hin, and_self, ↓reduceIte]
    rw [z1, z2]
    exact ⟨Or.inl rfl, sameEnds_refl _⟩
  have hdc := S.toSplitCtx.dc_Lvl (j + 1) (a := s) (by omega)
  have hle' := le_trans' hle (le_convert Z l)
  refine ⟨by rw [convert_cls_of_not_mem hyl]; exact yc, dc_le hdc hle',
    dc_le hdc ⟨hle'.1, fun x hx => ?_⟩⟩
  have hxy : x ≠ y := fun h => hx.1 (h ▸ hT.induce_y le_rfl)
  obtain ⟨c1, c2⟩ := hle'.2 x hx
  refine ⟨?_, c2⟩
  simp only [id] at c1 ⊢
  rw [erase_cls, if_neg hxy]
  exact c1

/-- The distinctness of the edges of the claims at the component `c ≥ s`. -/
private theorem CaseT.dist {c : ℕ} (hsc : s ≤ c) (hck : c < S.k) :
    S.cc c ≠ S.cc' c ∧ y ≠ S.cc c ∧ y ≠ S.cc' c ∧ y ≠ S.e' ∨ y = S.e' ∧ y ≠ S.cc c ∧
      y ≠ S.cc' c := by
  rcases hT.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl ⟨S.cc_ne c hck, hT.e_ne_cc hck hsc (Or.inl rfl), hT.e_ne_cc hck hsc (Or.inr rfl),
      S.hne⟩
  · exact Or.inr ⟨rfl, S.e'_ne_cc hck, S.e'_ne_cc' hck⟩

private theorem CaseT.y_ne_cc {c : ℕ} (hsc : s ≤ c) (hck : c < S.k) : y ≠ S.cc c ∧ y ≠ S.cc' c := by
  rcases hT.dist hZ hsc hck with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩

/-- The crossing edges of `P (c + 1)` in the graph of cases (iii), (v). -/
private theorem CaseT.cross {c : ℕ} (hsc : s ≤ c) (hcj : c < j) {x : E}
    (hx : x = S.cc c ∨ x = S.cc' c) : Z.ends x = G.ends x ∧ Z.cls x = G.cls x ∧
      ¬ ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1)) := by
  have hck : c < S.k := by have := hT.hjk; omega
  obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hck hx
  have hxe : x ≠ S.e := fun h => hT.e_ne_cc hck hsc hx h.symm
  have hxe' : x ≠ S.e' := by
    rcases hx with rfl | rfl
    · exact (S.e'_ne_cc hck).symm
    · exact (S.e'_ne_cc' hck).symm
  obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' g1 (by omega) (by omega) g2 (by omega) (by omega)
  refine ⟨z1, z2, ?_⟩
  rw [z1]
  rintro ⟨a1, a2⟩
  have := (S.mem_Lvl.1 a1).2.1
  have := (S.mem_Lvl.1 a2).2.1
  omega

/-- The quotient graph at the component `c` of cases (iii), (v) contains the graph of
[II, Claim A.6] built on the subgraph induced on the components `s, …, c`, with `y` changed into a
`Θ` edge. -/
private theorem CaseT.le_A6 {c : ℕ} (hsc : s ≤ c) (hcj : c < j) {l : List E}
    (hl : ∀ x ∈ l, ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1)) ∨
      x = y) (hyl : y ∈ l) :
    Le ((gA6 (G.induce (S.Lvl s (c + 1))) S.w (S.u c) (S.u' c) t (S.cc c) (S.cc' c) y).convert [y])
      ((Z.convert l).collapse (S.Lvl (c + 1) (j + 1)) S.w) := by
  have hck : c < S.k := by have := hT.hjk; omega
  have hlt := hT.hlt
  have hlw := hT.hlw
  obtain ⟨yc1, yc2⟩ := hT.y_ne_cc hZ hsc hck
  have cc := S.cc_ne c hck
  obtain ⟨yZc, yZe⟩ := hT.yZ hZ
  obtain ⟨-, -, -, hyL⟩ := hT.lower hZ hsc hcj
  have notL : ∀ v, S.lev v ≤ c → v ∉ S.Lvl (c + 1) (j + 1) := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have hwL : S.w ∈ S.Lvl (c + 1) (j + 1) := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  have htL : t ∉ S.Lvl (c + 1) (j + 1) := notL _ (by omega)
  have nl : ∀ x, x ≠ y → ¬ ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧
      (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1)) → x ∉ l := by
    intro x hxy hx hx'
    rcases hl x hx' with h | h
    · exact hx h
    · exact hxy h
  refine ⟨?_, fun x hx => ?_⟩
  · rw [convert_int, gA6_int, collapse_convert, convert_int,
      hZ.collapse_int hsc hcj (by omega) (by omega)]
    rfl
  have Tcls : ((gA6 (G.induce (S.Lvl s (c + 1))) S.w (S.u c) (S.u' c) t (S.cc c) (S.cc' c)
      y).convert [y]).cls x = if x = y then some .diff else if x = S.cc' c then some .plus else
        if x = S.cc c then some .diff else (G.induce (S.Lvl s (c + 1))).cls x := by
    rw [convert_cls, gA6_cls _ _ _ _ _ cc yc1.symm yc2.symm]
    by_cases h : x = y
    · simp [h]
    · simp [h]
  simp only [id]
  rw [collapse_cls, collapse_convert_ends, Tcls, convert_ends, gA6_ends]
  by_cases h1 : x = y
  · subst h1
    simp only [if_true]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, if_pos ⟨hyl, yZc⟩]
    · rcases sameEnds_iff.1 yZe with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;>
        simp only [hwL, htL, ↓reduceIte]
      · exact Or.inl rfl
      · exact Or.inr rfl
  simp only [h1, if_false]
  by_cases h2 : x = S.cc' c
  · subst h2
    obtain ⟨z1, z2, z3⟩ := hT.cross hZ hsc hcj (Or.inr rfl)
    simp only [if_true]
    refine ⟨?_, ?_⟩
    · rw [convert_cls_of_not_mem (nl _ h1 z3), z2]
      rcases S.cc'_cls c hck with h | h
      · exact Or.inr ⟨by simp, h⟩
      · exact Or.inl h
    · rw [z1]; exact cc_collapse hck hcj (Or.inr rfl)
  simp only [h2, if_false]
  by_cases h3 : x = S.cc c
  · subst h3
    obtain ⟨z1, z2, z3⟩ := hT.cross hZ hsc hcj (Or.inl rfl)
    simp only [if_true]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls_of_not_mem (nl _ h1 z3), z2, S.cc_diff c hck]
    · rw [z1]; exact cc_collapse hck hcj (Or.inl rfl)
  simp only [h3, if_false]
  -- the edges of `G` between the components `s, …, c`
  have hc : (G.induce (S.Lvl s (c + 1))).cls x ≠ none := by
    have := hx.1
    rw [Tcls, if_neg h1, if_neg h2, if_neg h3] at this
    exact this
  have hin : (G.ends x).1 ∈ S.Lvl s (c + 1) ∧ (G.ends x).2 ∈ S.Lvl s (c + 1) := by
    by_contra hn; simp [MGraph.induce, hn] at hc
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  have hxe : x ≠ S.e := by rintro rfl; exact hT.e_out le_rfl ⟨a1, a2, b1, b2⟩
  have hxe' : x ≠ S.e' := by rintro rfl; exact hc induce_cls_e'
  obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 a2 (by omega) b1 b2 (by omega)
  have hxl : x ∉ l := nl x h1 (by rw [z1]; exact fun h => notL _ (by omega) h.1)
  refine ⟨Or.inl ?_, ?_⟩
  · rw [convert_cls_of_not_mem hxl, z2]
    simp [MGraph.induce, hin]
  · simp only [MGraph.induce]
    rw [z1, if_neg (notL _ (by omega)), if_neg (notL _ (by omega))]
    exact sameEnds_refl _

/-- The quotient graph at the component `c` of cases (iii), (v) contains the graph of
[II, Claim A.7] built on the components `s, …, c` with `P (c + 1)` replaced by a `Θ` edge
(with the blue solid edges of `m` changed into `Θ` edges). -/
private theorem CaseT.le_A7 {c : ℕ} (hsc : s ≤ c) (hcj : c < j) {l m : List E}
    (hl : ∀ x ∈ l, ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧ (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1)) ∨
      x = y ∨ x = S.cc' c ∨ x ∈ m) (hml : ∀ x ∈ m, x ∈ l) (hyl : y ∈ l)
    (hc' : G.cls (S.cc' c) = some .diff ∨ S.cc' c ∈ l) :
    Le (gA7 ((S.Rep s c).convert m) S.w t (S.cc c) (S.cc' c) y)
      ((Z.convert l).collapse (S.Lvl (c + 1) (j + 1)) S.w) := by
  have hck : c < S.k := by have := hT.hjk; omega
  have hlt := hT.hlt
  have hlw := hT.hlw
  obtain ⟨yc1, yc2⟩ := hT.y_ne_cc hZ hsc hck
  have cc := S.cc_ne c hck
  obtain ⟨yZc, yZe⟩ := hT.yZ hZ
  have notL : ∀ v, S.lev v ≤ c → v ∉ S.Lvl (c + 1) (j + 1) := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have hwL : S.w ∈ S.Lvl (c + 1) (j + 1) := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  have htL : t ∉ S.Lvl (c + 1) (j + 1) := notL _ (by omega)
  obtain ⟨t1, t2, t3⟩ := Rep_θ (S := S) (i := s) hck
  refine ⟨?_, fun x hx => ?_⟩
  · rw [gA7_int, convert_int, Rep_int hsc hck, collapse_convert, convert_int,
      hZ.collapse_int hsc hcj (by omega) (by omega)]
  simp only [id]
  rw [collapse_cls, collapse_convert_ends, gA7_cls, gA7_ends, convert_ends, t1]
  by_cases h1 : x = y
  · subst h1
    simp only [if_true]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, if_pos ⟨hyl, yZc⟩]
    · rcases sameEnds_iff.1 yZe with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;>
        simp only [hwL, htL, ↓reduceIte]
      · exact Or.inl rfl
      · exact Or.inr rfl
  simp only [h1, if_false]
  by_cases h2 : x = S.cc' c
  · subst h2
    obtain ⟨z1, z2, z3⟩ := hT.cross hZ hsc hcj (Or.inr rfl)
    simp only [if_true, if_neg cc.symm]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, z2, convert_cls, t2]
      rcases S.cc'_cls c hck with h | h
      · rw [h]; simp
      · rcases hc' with h' | h'
        · rw [h] at h'; cases h'
        · rw [h]; simp [h']
    · rw [z1]; exact cc_collapse hck hcj (Or.inr rfl)
  simp only [h2, if_false]
  by_cases h3 : x = S.cc c
  · subst h3
    obtain ⟨z1, z2, z3⟩ := hT.cross hZ hsc hcj (Or.inl rfl)
    simp only [if_true]
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, z2, convert_cls, t2, S.cc_diff c hck]; simp
    · rw [z1]; exact (cc_collapse hck hcj (Or.inl rfl)).trans (Or.inr rfl)
  simp only [h3, if_false]
  -- the edges of `G` between the components `s, …, c`
  have hc : (S.Rep s c).cls x ≠ none := by
    have := hx.1
    rw [gA7_cls, if_neg h1, if_neg h2, convert_cls] at this
    intro h; rw [h] at this; simp at this
  rw [Rep_cls hsc hck h3 h2] at hc
  have hin : (G.ends x).1 ∈ S.Lvl s (c + 1) ∧ (G.ends x).2 ∈ S.Lvl s (c + 1) := by
    by_contra hn; rw [if_neg hn] at hc; exact hc rfl
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  have hxe : x ≠ S.e := by rintro rfl; exact hT.e_out le_rfl ⟨a1, a2, b1, b2⟩
  have hxe' : x ≠ S.e' := by rintro rfl; rw [if_pos hin, S.ce'] at hc; exact hc rfl
  obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 a2 (by omega) b1 b2 (by omega)
  have hxl : x ∈ l ↔ x ∈ m := by
    constructor
    · intro h
      rcases hl x h with h' | h' | h' | h'
      · rw [z1] at h'; exact absurd h'.1 (notL _ (by omega))
      · exact absurd h' h1
      · exact absurd h' h2
      · exact h'
    · exact hml x
  refine ⟨Or.inl ?_, ?_⟩
  · rw [convert_cls, z2, convert_cls, Rep_cls hsc hck h3 h2, if_pos hin]
    simp only [hxl]
  · rw [Rep_ends h3, z1, if_neg (notL _ (by omega)), if_neg (notL _ (by omega))]
    exact sameEnds_refl _

/-- The steps of the component `c`, `s ≤ c < j`, in cases (iii), (v), after `y` and the deeper
components: [II, Claims A.6, A.7]. -/
private theorem CaseT.tier {c : ℕ} (hsc : s ≤ c) (hcj : c < j) {pre : List E}
    (hpre : ∀ x ∈ pre, ((Z.ends x).1 ∈ S.Lvl (c + 1) (j + 1) ∧
      (Z.ends x).2 ∈ S.Lvl (c + 1) (j + 1)) ∨ x = y) (hyp : y ∈ pre) :
    Steps (Z.convert pre) (S.J c ++ S.ordR c) := by
  have hck : c < S.k := by have := hT.hjk; omega
  have hlt := hT.hlt
  have hlw := hT.hlw
  obtain ⟨yc1, yc2⟩ := hT.y_ne_cc hZ hsc hck
  have cc := S.cc_ne c hck
  obtain ⟨hL, hwL, hI, hyL⟩ := hT.lower hZ hsc hcj
  obtain ⟨hu, hlu⟩ := S.u_mem hck
  obtain ⟨hu', hlu'⟩ := S.u'_mem hck
  have hnd3 : [S.cc c, S.cc' c, y].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true]
    exact ⟨⟨cc, yc1.symm⟩, yc2.symm, by simp⟩
  rw [steps_append]
  constructor
  · unfold J
    split_ifs with hp
    · rw [steps_single]
      obtain ⟨z1, z2, z3⟩ := hT.cross hZ hsc hcj (Or.inr rfl)
      have hxp : S.cc' c ∉ pre := by
        intro h
        rcases hpre _ h with h' | h'
        · exact z3 h'
        · exact yc2 h'.symm
      obtain ⟨-, -, -, hA6⟩ := MGraph.claimA6 V E (G.induce (S.Lvl s (c + 1))) S.w (S.u c)
        (S.u' c) t (S.cc c) (S.cc' c) y (S.toSplitCtx.dc_Lvl (c + 1) (by omega))
        (fun h => by have := (S.mem_Lvl.1 h).2.2; omega) (by simp [MGraph.induce])
        (S.mem_Lvl.2 ⟨hu, by omega, by omega⟩) (S.mem_Lvl.2 ⟨hu', by omega, by omega⟩)
        (S.mem_Lvl.2 ⟨hT.ht, by omega, by omega⟩) hnd3 (induce_cls_cross hck (Or.inl rfl))
        (induce_cls_cross hck (Or.inr rfl)) (hT.induce_y le_rfl)
      refine red_quot (hL pre) hwL (by rw [convert_ends]; exact z3) (hI pre)
        (red_le hA6 (hT.le_A6 hZ hsc hcj hpre hyp) ?_)
      rw [collapse_cls, convert_cls_of_not_mem hxp, z2, hp]
    · exact steps_nil _
  · intro t' ht'
    rw [convert_convert', convert_convert', ← List.append_assoc]
    have hx := (S.mem_ordR hck _).1 (List.getElem_mem ht')
    obtain ⟨hp, a1, a2, b1, b2⟩ := hx
    have hxe : (S.ordR c)[t'] ≠ S.e := by
      intro h; rw [h] at a1 a2 b1 b2; exact hT.e_out hsc ⟨a1, by omega, b1, by omega⟩
    have hxe' : (S.ordR c)[t'] ≠ S.e' := fun h => by rw [h, S.ce'] at hp; cases hp
    have hxy : (S.ordR c)[t'] ≠ y := by
      rcases hT.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hxe
      · exact hxe'
    obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
    have hxL : ¬ ((Z.ends (S.ordR c)[t']).1 ∈ S.Lvl (c + 1) (j + 1) ∧
        (Z.ends (S.ordR c)[t']).2 ∈ S.Lvl (c + 1) (j + 1)) := by
      rw [z1]; rintro ⟨h, -⟩; have := (S.mem_Lvl.1 h).2.1; omega
    have hnd := (S.ordR_spec hck).1
    have hxl : (S.ordR c)[t'] ∉ pre ++ S.J c ++ (S.ordR c).take t' := by
      simp only [List.mem_append, not_or]
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, getElem_not_mem_take hnd ht'⟩
      · rcases hpre _ h with h' | h'
        · exact hxL h'
        · exact hxy h'
      · obtain ⟨h, -⟩ := mem_J h
        obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hck (Or.inr h)
        omega
    have hr := red_Rep (S := S) hsc hck ht'
    obtain ⟨t1, t2, t3⟩ := Rep_θ (S := S) (i := s) hck
    have hRy : ((S.Rep s c).convert ((S.ordR c).take t')).cls y = none := by
      rw [convert_cls, Rep_cls hsc hck yc1 yc2]
      rcases hT.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · have : ¬ ((G.ends S.e).1 ∈ S.Lvl s (c + 1) ∧ (G.ends S.e).2 ∈ S.Lvl s (c + 1)) := by
          rintro ⟨h1, h2⟩
          obtain ⟨c1, c2, -⟩ := S.mem_Lvl.1 h1
          obtain ⟨d1, d2, -⟩ := S.mem_Lvl.1 h2
          exact hT.e_out le_rfl ⟨c1, c2, d1, d2⟩
        simp [this]
      · simp [S.ce']
    set R' := (S.Rep s c).convert ((S.ordR c).take t') with hR'
    have q1 : S.w ∉ R'.int := by
      rw [hR', convert_int, Rep_int hsc hck]
      intro h; have := (S.mem_Lvl.1 h).2.2; omega
    have q2 : S.w ∉ R'.ext := by simp [hR', MGraph.replace, MGraph.convert]
    have q3 : R'.cls (S.cc c) = some .diff := by rw [hR', convert_cls, t2]; simp
    have mu : S.u c ∈ S.Lvl s (c + 1) := S.mem_Lvl.2 ⟨hu, by omega, by omega⟩
    have mu' : S.u' c ∈ S.Lvl s (c + 1) := S.mem_Lvl.2 ⟨hu', by omega, by omega⟩
    have mt : t ∈ S.Lvl s (c + 1) := S.mem_Lvl.2 ⟨hT.ht, by omega, by omega⟩
    have q4 : (R'.ends (S.cc c)).1 ∈ R'.int := by
      rw [hR', convert_ends, t1, convert_int, Rep_int hsc hck]; exact mu
    have q5 : (R'.ends (S.cc c)).2 ∈ R'.int := by
      rw [hR', convert_ends, t1, convert_int, Rep_int hsc hck]; exact mu'
    have q6 : t ∈ R'.int := by rw [hR', convert_int, Rep_int hsc hck]; exact mt
    have q7 : R'.cls (S.cc' c) = none := by rw [hR', convert_cls, t3]; simp
    have hA7 := MGraph.claimA7 V E R' S.w t (S.cc c) (S.cc' c) y hr.2.1 q1 q2 q3 q4 q5 q6 hnd3
      q7 hRy _ hr
    refine red_quot (hL _) hwL (by rw [convert_ends]; exact hxL) (hI _)
      (red_le hA7 (hT.le_A7 hZ hsc hcj (m := (S.ordR c).take t') (fun x hx => ?_)
        (fun x hx => List.mem_append_right _ hx) (by simp [hyp]) ?_) ?_)
    · simp only [List.mem_append] at hx
      rcases hx with (h | h) | h
      · rcases hpre x h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl (mem_J h).1))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases S.J_or hck with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · rw [collapse_cls, convert_cls_of_not_mem hxl, z2, hp]

/-- The quotient graph by the last component in cases (iii), (v) is doubly connected: the subgraph
induced on the components `s, …, j - 1`, and `w` joined to it by `cc (j - 1)` and
`cc' (j - 1)`. -/
private theorem CaseT.botQ (l : List E) : ((Z.convert l).collapse (S.Lvl j (j + 1)) S.w).DC := by
  have hsj := hT.hsj
  have hjk := hT.hjk
  have hlw := hT.hlw
  have hj1 : j - 1 < S.k := by omega
  have hjj : j - 1 + 1 = j := by omega
  have notΓ : ∀ v, S.lev v < j → v ∉ S.Lvl j (j + 1) := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.1; omega
  have hRp : ∀ f, (G.induce (S.Lvl s j)).Pres f → (G.ends f).1 ∈ S.Lvl s j ∧
      (G.ends f).2 ∈ S.Lvl s j ∧ (G.induce (S.Lvl s j)).cls f = G.cls f := by
    intro f hf
    have hin : (G.ends f).1 ∈ S.Lvl s j ∧ (G.ends f).2 ∈ S.Lvl s j := by
      by_contra hn; exact hf.1 (by simp [MGraph.induce, hn])
    exact ⟨hin.1, hin.2, by simp [MGraph.induce, hin]⟩
  have hnotR : ∀ x, (x = S.cc (j - 1) ∨ x = S.cc' (j - 1)) → ¬ (G.induce (S.Lvl s j)).Pres x := by
    intro x hx hp
    obtain ⟨h1, h2, -⟩ := hRp x hp
    obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hj1 hx
    have := (S.mem_Lvl.1 h1).2.2
    have := (S.mem_Lvl.1 h2).2.2
    omega
  obtain ⟨y1e, y1c, -⟩ := hT.cross hZ (c := j - 1) (by omega) (by omega) (Or.inl rfl)
  obtain ⟨y2e, y2c, -⟩ := hT.cross hZ (c := j - 1) (by omega) (by omega) (Or.inr rfl)
  have cy1 := cc_collapse (S := S) (b := j) hj1 (by omega) (Or.inl rfl)
  have cy2 := cc_collapse (S := S) (b := j) hj1 (by omega) (Or.inr rfl)
  have hLL : S.Lvl (j - 1 + 1) (j + 1) = S.Lvl j (j + 1) := by rw [hjj]
  rw [hLL] at cy1 cy2
  obtain ⟨hu1, hlu1⟩ := S.u_mem hj1
  obtain ⟨hu2, hlu2⟩ := S.u'_mem hj1
  refine dc_path (R := G.induce (S.Lvl s j)) (N := S.w) (g := S.cc (j - 1))
    (g₁ := S.cc (j - 1)) (g₂ := S.cc' (j - 1)) (y₁ := S.cc (j - 1)) (y₂ := S.cc' (j - 1))
    (m₁ := S.u (j - 1)) (m₂ := S.u' (j - 1)) (S.toSplitCtx.dc_Lvl j (by omega)) ?_ ?_ ?_ ?_
  · rw [collapse_convert, convert_int]
    have := hZ.collapse_int (c := j - 1) (by omega) (by omega) (by omega) (by omega)
    rw [hjj] at this
    exact this
  · intro f hf hfe
    obtain ⟨a1, a2, hcl⟩ := hRp f hf
    obtain ⟨a1i, a1a, a1b⟩ := S.mem_Lvl.1 a1
    obtain ⟨a2i, a2a, a2b⟩ := S.mem_Lvl.1 a2
    have hfe1 : f ≠ S.e := by rintro rfl; exact hT.e_out le_rfl ⟨a1i, a1a, a2i, a2a⟩
    have hfe' : f ≠ S.e' := by rintro rfl; exact hf.1 (by rw [hcl, S.ce'])
    obtain ⟨z1, z2⟩ := hZ.edge hfe1 hfe' a1i a1a (by omega) a2i a2a (by omega)
    refine ⟨?_, ?_⟩
    · rw [collapse_cls, convert_cls, z2, hcl]
      split_ifs with h
      · exact Or.inr ⟨h.2, rfl⟩
      · exact Or.inl rfl
    · rw [collapse_convert_ends, z1, if_neg (notΓ _ (by omega)), if_neg (notΓ _ (by omega))]
      exact sameEnds_refl _
  · intro h; exact absurd h (hnotR _ (Or.inl rfl))
  · intro _
    refine ⟨?_, ?_, ?_, ?_, S.mem_Lvl.2 ⟨hu1, by omega, by omega⟩,
      S.mem_Lvl.2 ⟨hu2, by omega, by omega⟩, S.cc_ne _ hj1, fun f hf _ => ⟨?_, ?_⟩,
      fun h => absurd h (hnotR _ (Or.inl rfl))⟩
    · rw [collapse_cls, convert_cls, y1c, S.cc_diff _ hj1]; simp
    · rw [collapse_cls, convert_cls, y2c]
      rcases S.cc'_cls _ hj1 with h | h <;> rw [h] <;> split_ifs <;> simp
    · rw [collapse_convert_ends, y1e]; exact cy1
    · rw [collapse_convert_ends, y2e]; exact cy2
    · rintro rfl; exact hnotR _ (Or.inl rfl) hf
    · rintro rfl; exact hnotR _ (Or.inr rfl) hf

/-- **Cases (iii) and (v) of [II, Lemma 5.12]**: the graph after operation (B) on the components
`s, …, j`, with `y` joining `w` (in the component `j`) to `t` (in the component `s`), is
pre-deterministic. -/
private theorem CaseT.preDet {B : MGraph V E} (hB : S.IsB B j x₁ x₂) (hBpd : B.PreDet)
    (hx12 : j < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e') : Z.PreDet := by
  obtain ⟨-, ℓB, hℓ⟩ := hBpd
  have hsj := hT.hsj
  have hjk := hT.hjk
  have hlt := hT.hlt
  have hlw := hT.hlw
  have ℓB_lev : ∀ x ∈ ℓB, G.cls x = some .plus ∧ (G.ends x).1 ∈ G.int ∧ S.lev (G.ends x).1 = j ∧
      (G.ends x).2 ∈ G.int ∧ S.lev (G.ends x).2 = j := fun x hx => (hB.ip x).1 ((hℓ.2.1 x).1 hx)
  have hey : ∀ x, x ≠ S.e → x ≠ S.e' → x ≠ y := by
    intro x h1 h2
    rcases hT.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact h1
    · exact h2
  have ℓBe : ∀ x ∈ ℓB, x ≠ S.e ∧ x ≠ S.e' := by
    intro x hx
    obtain ⟨hp, a1, a2, b1, b2⟩ := ℓB_lev x hx
    exact ⟨by rintro rfl; exact hT.e_out (a := j) hsj.le ⟨a1, by omega, b1, by omega⟩,
      by rintro rfl; rw [S.ce'] at hp; cases hp⟩
  have hbot : Steps Z ℓB := hZ.tier_bot hsj.le hlw hB hℓ hx12
    (fun ⟨a1, a2, b1, b2⟩ => hT.e_out (a := j) hsj.le ⟨a1, by omega, b1, by omega⟩)
    (fun t => hT.botQ hZ _)
  have hyℓ : y ∉ ℓB := fun h => hey y (ℓBe y h).1 (ℓBe y h).2 rfl
  have h0 : Steps Z (ℓB ++ [y]) := steps_append.2 ⟨hbot, steps_single.2 (hT.stepY hZ hyℓ)⟩
  let ins : ℕ → E → Prop := fun c x => ((Z.ends x).1 ∈ S.Lvl c (j + 1) ∧
    (Z.ends x).2 ∈ S.Lvl c (j + 1)) ∨ x = y
  have hmono : ∀ c c' x, c' ≤ c → ins c x → ins c' x := by
    intro c c' x h hx
    rcases hx with ⟨h1, h2⟩ | h
    · obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 h1
      obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 h2
      exact Or.inl ⟨S.mem_Lvl.2 ⟨a1, by omega, a3⟩, S.mem_Lvl.2 ⟨b1, by omega, b3⟩⟩
    · exact Or.inr h
  have insG : ∀ x c, x ≠ S.e → x ≠ S.e' → (G.ends x).1 ∈ G.int → (G.ends x).2 ∈ G.int →
      c ≤ S.lev (G.ends x).1 → S.lev (G.ends x).1 ≤ j → c ≤ S.lev (G.ends x).2 →
      S.lev (G.ends x).2 ≤ j → s ≤ c → ins c x := by
    intro x c h1 h2 a1 b1 a2 a3 b2 b3 hc
    obtain ⟨z1, -⟩ := hZ.edge h1 h2 a1 (by omega) a3 b1 (by omega) b3
    left
    rw [z1]
    exact ⟨S.mem_Lvl.2 ⟨a1, a2, by omega⟩, S.mem_Lvl.2 ⟨b1, b2, by omega⟩⟩
  have hbotin : ∀ x ∈ ℓB ++ [y], ins j x := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨-, a1, a2, b1, b2⟩ := ℓB_lev x h
      exact insG x j (ℓBe x h).1 (ℓBe x h).2 a1 b1 (by omega) (by omega) (by omega) (by omega)
        hsj.le
    · exact Or.inr (List.mem_singleton.1 h)
  have Jlev : ∀ c, c < S.k → s ≤ c → ∀ x ∈ S.J c, G.cls x = some .plus ∧ x ≠ S.e ∧ x ≠ S.e' ∧
      (G.ends x).1 ∈ G.int ∧ (G.ends x).2 ∈ G.int ∧ ((S.lev (G.ends x).1 = c ∧
        S.lev (G.ends x).2 = c + 1) ∨ (S.lev (G.ends x).1 = c + 1 ∧ S.lev (G.ends x).2 = c)) := by
    intro c hc hsc x hx
    obtain ⟨rfl, hp⟩ := mem_J hx
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hc (Or.inr rfl)
    exact ⟨hp, fun h => hT.e_ne_cc hc hsc (Or.inr rfl) h.symm, (S.e'_ne_cc' hc).symm, g1, g2, g3⟩
  have ordlev : ∀ c, c < S.k → ∀ x ∈ S.ordR c, G.cls x = some .plus ∧ (G.ends x).1 ∈ G.int ∧
      S.lev (G.ends x).1 = c ∧ (G.ends x).2 ∈ G.int ∧ S.lev (G.ends x).2 = c :=
    fun c hc x hx => (S.mem_ordR hc x).1 hx
  have hin : ∀ c, s ≤ c → c < j → ∀ x ∈ S.J c ++ S.ordR c, ins c x := by
    intro c h1 h2 x hx
    have hc : c < S.k := by omega
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨-, n1, n2, a1, b1, hl⟩ := Jlev c hc h1 x h
      rcases hl with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;>
        exact insG x c n1 n2 a1 b1 (by omega) (by omega) (by omega) (by omega) h1
    · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev c hc x h
      exact insG x c (by rintro rfl; exact hT.e_out h1 ⟨a1, by omega, b1, by omega⟩)
        (by rintro rfl; rw [S.ce'] at hp; cases hp) a1 b1 (by omega) (by omega) (by omega)
        (by omega) h1
  obtain ⟨hq, -⟩ := steps_tiers' hsj.le (fun c => S.J c ++ S.ordR c) (ℓB ++ [y]) ins hmono h0
    hbotin (fun c h1 h2 pre hpre hpre' => hT.tier hZ h1 h2 hpre (hpre' y (by simp))) hin
  refine preDet_of_steps (steps_dc hq (List.ne_nil_of_mem (a := y) (by simp))) hq fun x => ?_
  -- the internal blue solid edges
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨yc, ye⟩ := hT.yZ hZ
    refine iff_of_true (by simp) ⟨yc, ?_⟩
    have mt : t ∈ Z.int := (hZ.int _).2 ⟨hT.ht, by omega, by omega⟩
    have mw : S.w ∈ Z.int := (hZ.int _).2 ⟨S.hw, by omega, by omega⟩
    rcases sameEnds_iff.1 ye with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨mw, mt⟩
    · exact ⟨mt, mw⟩
  by_cases hxz : x = z
  · subst hxz
    refine iff_of_false ?_ ?_
    · simp only [List.mem_append, List.mem_singleton, mem_midL, not_or]
      refine ⟨⟨fun h => ?_, fun h => hT.y_ne h.symm⟩, ?_⟩
      · obtain ⟨n1, n2⟩ := ℓBe x h
        rcases hT.hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact n2 rfl
        · exact n1 rfl
      · rintro ⟨d', hd, h⟩
        rcases h with h | h
        · obtain ⟨-, n1, n2, -⟩ := Jlev _ (by omega) (by omega) x h
          rcases hT.hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact n2 rfl
          · exact n1 rfl
        · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev _ (by omega) x h
          rcases hT.hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · rw [S.ce'] at hp; cases hp
          · exact hT.e_out (a := j - 1 - d') (by omega) ⟨a1, by omega, b1, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      have hn : j < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
        intro hb
        obtain ⟨-, t1, t2, -⟩ := hZ.th hb
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [h, t1] at h1; cases h1
        · rw [h, t2] at h1; cases h1
      obtain ⟨g1, -⟩ := hZ.gen x hn
      rw [g1] at h2 h3
      have hvZ : v ∉ Z.int := fun h => by
        obtain ⟨a1, a2, -⟩ := (hZ.int v).1 h
        rcases hT.hv with h' | h'
        · exact h' a1
        · omega
      rcases sameEnds_iff.1 hT.hz with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e2] at h3; exact hvZ h3
      · rw [e1] at h2; exact hvZ h2
  have hxe : x ≠ S.e := by
    rintro rfl
    rcases hT.hyz with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact hxy rfl
    · exact hxz rfl
  have hxe' : x ≠ S.e' := by
    rintro rfl
    rcases hT.hyz with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hxz rfl
    · exact hxy rfl
  rw [hZ.intPlus x hxe hxe']
  simp only [List.mem_append, List.mem_singleton, mem_midL, hxy, or_false]
  constructor
  · rintro (h | ⟨d', hd, h⟩)
    · obtain ⟨hp, a1, a2, b1, b2⟩ := ℓB_lev x h
      exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
    · have hc : j - 1 - d' < S.k := by omega
      rcases h with h | h
      · obtain ⟨hp, -, -, a1, b1, hl⟩ := Jlev _ hc (by omega) x h
        rcases hl with ⟨l1, l2⟩ | ⟨l1, l2⟩ <;>
          exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
      · obtain ⟨hp, a1, a2, b1, b2⟩ := ordlev _ hc x h
        exact ⟨hp, a1, by omega, by omega, b1, by omega, by omega⟩
  · rintro ⟨hp, a1, a2, a3, b1, b2, b3⟩
    rcases S.lev_plus hp a1 b1 with hl | ⟨l, hl, rfl, hlv⟩
    · by_cases hcj : S.lev (G.ends x).1 = j
      · exact Or.inl ((hℓ.2.1 x).2 ((hB.ip x).2 ⟨hp, a1, hcj, b1, by omega⟩))
      · refine Or.inr ⟨j - 1 - S.lev (G.ends x).1, by omega, ?_⟩
        rw [show j - 1 - (j - 1 - S.lev (G.ends x).1) = S.lev (G.ends x).1 by omega]
        exact Or.inr ((S.mem_ordR (by omega) x).2 ⟨hp, a1, rfl, b1, by omega⟩)
    · have hJ : S.cc' l ∈ S.J l := by unfold J; rw [if_pos hp]; exact List.mem_singleton_self _
      refine Or.inr ⟨j - 1 - l, by omega, ?_⟩
      rw [show j - 1 - (j - 1 - l) = l by omega]
      exact Or.inl hJ

end CaseT

end SC

/-! ## Mapping vertices -/

/-- Mapping the vertices keeps the doubly connected property: a set of internal vertices of the
graph with mapped vertices is left by the image of an edge of a net leaving its preimage. -/
private theorem dc_mapV' [DecidableEq V] {X : MGraph V E} (f : V → V) (h : X.DC) : (X.mapV f).DC := by
  classical
  obtain ⟨K, L, hd, hK, hL, hsK, hsL⟩ := h
  have sp : ∀ B : Finset E, X.Spans B → (X.mapV f).Spans B := by
    intro B hB S hS hne hnot
    obtain ⟨s, hs⟩ := hne
    obtain ⟨x, hx, hxs⟩ := Finset.mem_image.1 (hS hs)
    obtain ⟨y, hy, hyS⟩ := Finset.not_subset.1 hnot
    obtain ⟨x', hx', hx's⟩ := Finset.mem_image.1 hy
    obtain ⟨e, he, hc, h1, h2, hcut⟩ := hB (X.int.filter fun v => f v ∈ S)
      (Finset.filter_subset _ _) ⟨x, Finset.mem_filter.2 ⟨hx, hxs ▸ hs⟩⟩
      (fun h' => hyS (hx's ▸ (Finset.mem_filter.1 (h' hx')).2))
    refine ⟨e, he, hc, Finset.mem_image_of_mem f h1, Finset.mem_image_of_mem f h2, ?_⟩
    simp only [MGraph.Cut, Finset.mem_filter, h1, h2, true_and] at hcut
    exact hcut
  exact ⟨K, L, hd, hK, hL, sp K hsK, sp L hsL⟩

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-! ### All blue solid edges -/

variable (S) in
/-- A pre-deterministic order of the graph of the component `i`: the order of `S.R i` for `i < k`,
of the subgraph induced on `P k` for `i = k`. -/
private def ordB (i : ℕ) : List E :=
  if i < S.k then S.ordR i else Classical.choose S.preDet_last.2

private theorem ordB_spec_last : (G.induce (S.P S.k)).IsPDOrder (S.ordB S.k) := by
  simp only [ordB, lt_irrefl, if_false]
  exact Classical.choose_spec S.preDet_last.2

/-- The edges of the order of the component `i`: the blue solid edges inside the component. -/
private theorem mem_ordB {i : ℕ} (hi : i ≤ S.k) (x : E) : x ∈ S.ordB i ↔ G.cls x = some .plus ∧
    (G.ends x).1 ∈ G.int ∧ S.lev (G.ends x).1 = i ∧ (G.ends x).2 ∈ G.int ∧
      S.lev (G.ends x).2 = i := by
  rcases Nat.lt_or_ge i S.k with h | h
  · simp only [ordB, h, if_true]; exact S.mem_ordR h x
  · have : i = S.k := le_antisymm hi h
    subst this
    exact (ordB_spec_last.2.1 x).trans ((S.isB_induce x x).ip x)

variable (S) in
/-- A list of all blue solid edges between internal vertices. -/
private def allPlus : List E := (List.range (S.k + 1)).flatMap fun l => S.ordB l ++ [S.cc' l]

private theorem mem_allPlus {x : E} (hx : G.cls x = some .plus) (h1 : (G.ends x).1 ∈ G.int)
    (h2 : (G.ends x).2 ∈ G.int) : x ∈ S.allPlus := by
  unfold allPlus
  rw [List.mem_flatMap]
  rcases S.lev_plus hx h1 h2 with hl | ⟨l, hl, rfl, -⟩
  · have := S.lev_le (G.ends x).1
    exact ⟨S.lev (G.ends x).1, List.mem_range.2 (by omega),
      List.mem_append_left _ ((S.mem_ordB this x).2 ⟨hx, h1, rfl, h2, hl.symm⟩)⟩
  · exact ⟨l, List.mem_range.2 (by omega), by simp⟩

/-! ### The graph of [II, Lemma 5.11] for a vertex of the component `i` identified with `w` -/

section Merge

variable {j i : ℕ} {vv : V}

variable (S) in
/-- The map of operation (A) identifying `vv` with `w`. -/
abbrev fm (vv : V) : V → V := fun v => if v = vv then S.w else v

/-- The image of a vertex lies in the image of a member `P a` of the chain, `a ≤ j`, exactly when
the vertex lies in `P a`, if `vv` and `w` lie in `P a`. -/
private theorem fm_mem_P {a : ℕ} (hvv : vv ∈ S.P a) (hwP : S.w ∈ S.P a) (u : V) :
    S.fm vv u ∈ (S.P a).image (S.fm vv) ↔ u ∈ S.P a := by
  constructor
  · rintro hu
    obtain ⟨u', hu', he⟩ := Finset.mem_image.1 hu
    by_cases h : u = vv
    · rw [h]; exact hvv
    · simp only [fm, h, if_false] at he
      by_cases h' : u' = vv
      · simp only [h', if_true] at he; rw [← he]; exact hwP
      · simp only [h', if_false] at he; rw [← he]; exact hu'
  · exact fun h => Finset.mem_image_of_mem _ h

/-- The image of a vertex lies in the image of a member `P a` of the chain not containing `vv` and
`w` exactly when the vertex lies in `P a`. -/
private theorem fm_mem_P' {a : ℕ} (hvv : vv ∉ S.P a) (hwP : S.w ∉ S.P a) (u : V) :
    S.fm vv u ∈ (S.P a).image (S.fm vv) ↔ u ∈ S.P a := by
  constructor
  · rintro hu
    obtain ⟨u', hu', he⟩ := Finset.mem_image.1 hu
    have hu'v : u' ≠ vv := fun h => hvv (h ▸ hu')
    simp only [fm, hu'v, if_false] at he
    by_cases h : u = vv
    · simp only [fm, h, if_true] at he; exact absurd (he ▸ hu') hwP
    · simp only [fm, h, if_false] at he; rw [← he]; exact hu'
  · exact fun h => Finset.mem_image_of_mem _ h

/-- The image of a vertex lies in the image of the component `i ∋ vv` exactly when the vertex lies
in the component or is `w`. -/
private theorem fm_mem_Γ (hvv : vv ∈ S.Lvl i (i + 1)) (u : V) :
    S.fm vv u ∈ (S.Lvl i (i + 1)).image (S.fm vv) ↔ u ∈ S.Lvl i (i + 1) ∨ u = S.w := by
  constructor
  · rintro hu
    obtain ⟨u', hu', he⟩ := Finset.mem_image.1 hu
    by_cases h : u = vv
    · rw [h]; exact Or.inl hvv
    · simp only [fm, h, if_false] at he
      by_cases h' : u' = vv
      · simp only [h', if_true] at he; exact Or.inr he.symm
      · simp only [h', if_false] at he; rw [← he]; exact Or.inl hu'
  · rintro (h | rfl)
    · exact Finset.mem_image_of_mem _ h
    · exact Finset.mem_image.2 ⟨vv, hvv, by simp⟩

/-- The graph of [II, Lemma 5.11] on the components `j, …, i` with `vv` (in the component `i`)
identified with `w` (in the component `j`): its internal vertices, edges and the `Θ` edge replacing
`P (i + 1)`, and the pre-deterministic property. -/
structure IsW (W : MGraph V E) (j i : ℕ) (vv : V) : Prop where
  int : ∀ u, S.fm vv u ∈ W.int ↔ u ∈ G.int ∧ j ≤ S.lev u ∧ S.lev u ≤ i
  int' : ∀ u, u ∈ W.int → ∃ u', u' ∈ G.int ∧ j ≤ S.lev u' ∧ S.lev u' ≤ i ∧ S.fm vv u' = u
  gen : ∀ x, (i < S.k → x ≠ S.cc i ∧ x ≠ S.cc' i) →
    W.ends x = (S.fm vv (G.ends x).1, S.fm vv (G.ends x).2) ∧
    W.cls x = if ((G.ends x).1 ∈ G.int ∧ j ≤ S.lev (G.ends x).1 ∧ S.lev (G.ends x).1 ≤ i) ∧
      ((G.ends x).2 ∈ G.int ∧ j ≤ S.lev (G.ends x).2 ∧ S.lev (G.ends x).2 ≤ i) then G.cls x else none
  th : i < S.k → W.cls (S.cc i) = some .diff ∧ W.cls (S.cc' i) = none ∧
    (W.ends (S.cc i)).1 ∈ (S.Lvl i (i + 1)).image (S.fm vv) ∧
    (W.ends (S.cc i)).2 ∈ (S.Lvl i (i + 1)).image (S.fm vv)
  pd : W.PreDet

/-- The membership facts of the merge map for `vv` in the component `i`, `w` in the component
`j < i`. -/
private theorem fm_facts (hji : j < i) (hik : i ≤ S.k) (hvv : vv ∈ G.int) (hlv : S.lev vv = i)
    (hlw : S.lev S.w = j) :
    (∀ u, S.fm vv u ∈ (S.P j).image (S.fm vv) ↔ u ∈ S.P j) ∧
    (i < S.k → ∀ u, S.fm vv u ∈ (S.P (i + 1)).image (S.fm vv) ↔ u ∈ S.P (i + 1)) := by
  refine ⟨fm_mem_P ((S.mem_P (by omega) vv).2 ⟨hvv, by omega⟩)
    ((S.mem_P (by omega) S.w).2 ⟨S.hw, by omega⟩), fun hik' => fm_mem_P' ?_ ?_⟩
  · intro h; have := ((S.mem_P hik' vv).1 h).2; omega
  · intro h; have := ((S.mem_P hik' S.w).1 h).2; omega

private theorem isW_replace (hji : j < i) (hik : i < S.k) (hvv : vv ∈ G.int) (hlv : S.lev vv = i)
    (hlw : S.lev S.w = j) :
    S.IsW ((G.merge S.w vv).replace ((S.P j).image (S.fm vv)) ((S.P (i + 1)).image (S.fm vv))
      (S.cc i) (S.cc' i)) j i vv := by
  obtain ⟨fj, fi⟩ := fm_facts hji hik.le hvv hlv hlw
  have fi' := fi hik
  have hint : ∀ u, S.fm vv u ∈ (S.P j).image (S.fm vv) \ (S.P (i + 1)).image (S.fm vv) ↔
      u ∈ G.int ∧ j ≤ S.lev u ∧ S.lev u ≤ i := by
    intro u
    rw [Finset.mem_sdiff, fj, fi', S.mem_P (by omega), S.mem_P hik]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by by_contra h; exact h3 ⟨h1, by omega⟩⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun ⟨_, h⟩ => by omega⟩
  have hmerge : G.merge S.w vv = G.mapV (S.fm vv) := rfl
  have hne := S.cc_ne i hik
  have outer : ∀ x, (G.merge S.w vv).outer ((S.P (i + 1)).image (S.fm vv)) x =
      S.fm vv (G.outer (S.P (i + 1)) x) := by
    intro x
    unfold MGraph.outer
    rw [hmerge]
    simp only [MGraph.mapV, fi']
    split_ifs <;> rfl
  refine ⟨fun u => hint u, fun u hu => ?_, fun x hx => ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hu
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 h1
    have h2' : u' ∉ S.P (i + 1) := fun h => h2 (Finset.mem_image_of_mem _ h)
    rw [S.mem_P (by omega)] at hu'
    rw [S.mem_P hik] at h2'
    exact ⟨u', hu'.1, hu'.2, by by_contra h; exact h2' ⟨hu'.1, by omega⟩, rfl⟩
  · obtain ⟨n1, n2⟩ := hx hik
    simp only [MGraph.replace, n1, n2, if_false, MGraph.induce, hmerge]
    simp only [MGraph.mapV, hint]
    simp
  · simp [MGraph.replace]
  · simp [MGraph.replace, hne.symm]
  · simp only [MGraph.replace, if_true]
    rw [outer]
    obtain ⟨-, -, -, h1, h2, -⟩ := S.cc_ends' hik (Or.inl rfl)
    exact Finset.mem_image_of_mem _ (S.mem_Lvl.2 ⟨h1, by omega, by omega⟩)
  · simp only [MGraph.replace, if_true]
    rw [outer]
    obtain ⟨-, -, -, h1, h2, -⟩ := S.cc_ends' hik (Or.inr (rfl : S.cc' i = S.cc' i))
    exact Finset.mem_image_of_mem _ (S.mem_Lvl.2 ⟨h1, by omega, by omega⟩)
  · -- [II, Lemma 5.11]
    have hM : MGraph.InComp S.k S.P j S.w :=
      ⟨(S.mem_P (by omega) _).2 ⟨S.hw, by omega⟩,
        fun _ h => by have := ((S.mem_P (by omega) _).1 h).2; omega⟩
    have hM' : MGraph.InComp S.k S.P i vv :=
      ⟨(S.mem_P (by omega) _).2 ⟨hvv, by omega⟩,
        fun _ h => by have := ((S.mem_P (by omega) _).1 h).2; omega⟩
    have := MGraph.merge_chain V E G S.k S.P j i S.w vv S.noGhost S.spd S.chain hji hik.le hM hM'
    simp only [chainNext, hik, if_true, Option.map_some, MGraph.ClauseIII] at this
    refine this.2 _ _ hne ?_ ?_
    all_goals
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hmerge]; simp only [MGraph.mapV]; rw [S.cc_diff i hik]; simp
    · rw [hmerge]; simp only [MGraph.mapV]; rw [S.cc_diff i hik]; simp
    · obtain ⟨g1, -, -⟩ := S.toSplitCtx.cc_lev hik (Or.inl rfl)
      exact Or.inl (by rw [hmerge]; exact Finset.mem_image_of_mem _ g1)
    · obtain ⟨-, g2, -⟩ := S.toSplitCtx.cc_lev hik (Or.inl rfl)
      exact Or.inl (by rw [hmerge]; exact Finset.mem_image_of_mem _ g2)
    · have := ((S.cross i hik (S.cc i)).2 (Or.inl rfl)).2.2.2.2
      rw [hmerge]
      simp only [MGraph.Cut, MGraph.mapV, fi'] at this ⊢
      exact this
    · rw [hmerge]; simp only [MGraph.mapV]
      rcases S.cc'_cls i hik with h | h <;> rw [h] <;> simp
    · rw [hmerge]; simp only [MGraph.mapV]
      rcases S.cc'_cls i hik with h | h <;> rw [h] <;> simp
    · obtain ⟨g1, -, -⟩ := S.toSplitCtx.cc_lev hik (Or.inr rfl)
      exact Or.inl (by rw [hmerge]; exact Finset.mem_image_of_mem _ g1)
    · obtain ⟨-, g2, -⟩ := S.toSplitCtx.cc_lev hik (Or.inr rfl)
      exact Or.inl (by rw [hmerge]; exact Finset.mem_image_of_mem _ g2)
    · have := ((S.cross i hik (S.cc' i)).2 (Or.inr rfl)).2.2.2.2
      rw [hmerge]
      simp only [MGraph.Cut, MGraph.mapV, fi'] at this ⊢
      exact this

private theorem isW_induce (hji : j < i) (hik : i = S.k) (hvv : vv ∈ G.int) (hlv : S.lev vv = i)
    (hlw : S.lev S.w = j) :
    S.IsW ((G.merge S.w vv).induce ((S.P j).image (S.fm vv))) j i vv := by
  subst hik
  obtain ⟨fj, -⟩ := fm_facts hji le_rfl hvv hlv hlw
  have hint : ∀ u, S.fm vv u ∈ (S.P j).image (S.fm vv) ↔
      u ∈ G.int ∧ j ≤ S.lev u ∧ S.lev u ≤ S.k := by
    intro u
    rw [fj, S.mem_P (by omega)]
    have := S.lev_le u
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, this⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
  have hmerge : G.merge S.w vv = G.mapV (S.fm vv) := rfl
  refine ⟨fun u => hint u, fun u hu => ?_, fun x _ => ?_, fun h => absurd h (lt_irrefl _), ?_⟩
  · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
    rw [S.mem_P (by omega)] at hu'
    exact ⟨u', hu'.1, hu'.2, S.lev_le u', rfl⟩
  · simp only [MGraph.induce, hmerge]
    simp only [MGraph.mapV, hint]
    simp
  · have hM : MGraph.InComp S.k S.P j S.w :=
      ⟨(S.mem_P (by omega) _).2 ⟨S.hw, by omega⟩,
        fun _ h => by have := ((S.mem_P (by omega) _).1 h).2; omega⟩
    have hM' : MGraph.InComp S.k S.P S.k vv :=
      ⟨(S.mem_P le_rfl _).2 ⟨hvv, by omega⟩, fun h => absurd h (lt_irrefl _)⟩
    have := MGraph.merge_chain V E G S.k S.P j S.k S.w vv S.noGhost S.spd S.chain hji le_rfl hM
      hM'
    simp only [chainNext, lt_irrefl, if_false, Option.map_none, MGraph.ClauseIII] at this
    exact this

/-- The image under the merge map of the component `i ∋ vv`, collapsed to `w`, is the collapse of
the component and `w`. -/
private theorem g_fm (hvv : vv ∈ S.Lvl i (i + 1)) (u : V) :
    (if S.fm vv u ∈ (S.Lvl i (i + 1)).image (S.fm vv) then S.w else S.fm vv u) =
      (if u ∈ insert S.w (S.Lvl i (i + 1)) then S.w else u) := by
  by_cases h : u ∈ S.Lvl i (i + 1) ∨ u = S.w
  · rw [if_pos ((fm_mem_Γ hvv u).2 h), if_pos (by rw [Finset.mem_insert]; tauto)]
  · rw [if_neg (fun h' => h ((fm_mem_Γ hvv u).1 h')),
      if_neg (by rw [Finset.mem_insert]; tauto)]
    have : u ≠ vv := fun h' => h (Or.inl (h' ▸ hvv))
    simp [fm, this]

/-- The graph of [II, Lemma 5.11] collapsed: the subgraph induced on the image of the component
`i` is doubly connected, and the quotient graph, with the blue solid edges of the component
changed into `Θ` edges, is pre-deterministic. -/
private theorem IsW.quot {W : MGraph V E} (hW : S.IsW W j i vv) (hji : j < i) (hik : i ≤ S.k)
    (hvv : vv ∈ G.int) (hlv : S.lev vv = i) :
    ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).PreDet := by
  have hΓ : (S.Lvl i (i + 1)).image (S.fm vv) ⊆ W.int := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hu
    exact (hW.int u).2 ⟨h1, by omega, by omega⟩
  have hvvΓ : vv ∈ S.Lvl i (i + 1) := S.mem_Lvl.2 ⟨hvv, by omega, by omega⟩
  have hwΓ : S.w ∈ (S.Lvl i (i + 1)).image (S.fm vv) :=
    Finset.mem_image.2 ⟨vv, hvvΓ, by simp [fm]⟩
  refine preDet_convert (preDet_quot hW.pd hΓ hwΓ ?_) _
  refine dc_le (dc_mapV' (S.fm vv) (S.toSplitCtx.dc_Lvl (i + 1) hik)) ⟨rfl, fun x hx => ?_⟩
  obtain ⟨hc, -, -, -⟩ := hx
  have hin : (G.ends x).1 ∈ S.Lvl i (i + 1) ∧ (G.ends x).2 ∈ S.Lvl i (i + 1) := by
    by_contra hn
    exact hc (by simp [MGraph.mapV, MGraph.induce, hn])
  have hcl : ((G.induce (S.Lvl i (i + 1))).mapV (S.fm vv)).cls x = G.cls x := by
    simp [MGraph.mapV, MGraph.induce, hin]
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  have hn : i < S.k → x ≠ S.cc i ∧ x ≠ S.cc' i := by
    intro hk
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h
    · obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hk (Or.inl rfl); omega
    · obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hk (Or.inr rfl); omega
  obtain ⟨w1, w2⟩ := hW.gen x hn
  have hin' : (W.ends x).1 ∈ (S.Lvl i (i + 1)).image (S.fm vv) ∧
      (W.ends x).2 ∈ (S.Lvl i (i + 1)).image (S.fm vv) := by
    rw [w1]; exact ⟨Finset.mem_image_of_mem _ hin.1, Finset.mem_image_of_mem _ hin.2⟩
  simp only [id]
  rw [hcl]
  refine ⟨Or.inl ?_, ?_⟩
  · simp only [MGraph.induce, hin', and_self, ↓reduceIte]
    rw [w2, if_pos ⟨⟨a1, by omega, by omega⟩, ⟨b1, by omega, by omega⟩⟩]
  · simp only [MGraph.induce, MGraph.mapV]
    rw [w1]
    exact sameEnds_refl _

/-- Two graphs with the same internal vertices, in which every edge has the same class and ends,
or is in neither a present non-loop edge with internal ends nor an internal blue solid edge. -/
private theorem le_ip_of_agree {X Y : MGraph V E} (hint : X.int = Y.int)
    (h : ∀ x, (X.cls x = Y.cls x ∧ X.ends x = Y.ends x) ∨
      (¬ X.Pres x ∧ ¬ X.IsIntPlus x ∧ ¬ Y.Pres x ∧ ¬ Y.IsIntPlus x)) :
    Le X Y ∧ ∀ x, X.IsIntPlus x ↔ Y.IsIntPlus x := by
  refine ⟨⟨hint, fun x hx => ?_⟩, fun x => ?_⟩
  · rcases h x with ⟨h1, h2⟩ | ⟨h1, -⟩
    · simp only [id]; rw [h1, h2]; exact ⟨Or.inl rfl, sameEnds_refl _⟩
    · exact absurd hx h1
  · rcases h x with ⟨h1, h2⟩ | ⟨-, h1, -, h2⟩
    · unfold MGraph.IsIntPlus; rw [h1, h2, hint]
    · exact iff_of_false h1 h2

/-- **The top part of cases (ii), (iv) of [II, Lemma 5.12]**: the graph after operation (B) on the
components `j, …, i`, with the blue solid edges of the component `i` changed into `Θ` edges, and
the component `i` and `w` collapsed to `w`, is pre-deterministic: it is the graph of
[II, Lemma 5.11] for a vertex of the component `i` identified with `w`, collapsed. -/
private theorem Qtop {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z j i x₁ x₂) (hji : j < i)
    (hik : i ≤ S.k) (hlw : S.lev S.w = j) (hvv : vv ∈ G.int) (hlv : S.lev vv = i) {p : List E}
    (hx12 : i < S.k → (x₁ = S.cc i ∨ x₁ = S.cc' i ∨ x₁ = S.e ∨ x₁ = S.e') ∧
      (x₂ = S.cc i ∨ x₂ = S.cc' i ∨ x₂ = S.e ∨ x₂ = S.e'))
    (hp : ∀ x, x ≠ S.e → x ≠ S.e' → (i < S.k → x ≠ S.cc i ∧ x ≠ S.cc' i) →
      G.cls x = some .plus → (G.ends x).1 ∈ G.int → j ≤ S.lev (G.ends x).1 →
      S.lev (G.ends x).1 ≤ i → (G.ends x).2 ∈ G.int → j ≤ S.lev (G.ends x).2 →
      S.lev (G.ends x).2 ≤ i → (x ∈ p ↔ (S.lev (G.ends x).1 = i ∧ S.lev (G.ends x).2 = i)))
    (he : (i < S.k → S.e ≠ S.cc' i) → (G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = i ∧
      (G.ends S.e).2 ∈ G.int ∧ S.lev (G.ends S.e).2 = i)
    (hspec : ∀ x, (x = S.e ∨ x = S.e' ∨ (i < S.k ∧ (x = S.cc i ∨ x = S.cc' i))) →
      ¬ ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).Pres x ∧
      ¬ ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).IsIntPlus x) :
    ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).PreDet := by
  have hvvΓ : vv ∈ S.Lvl i (i + 1) := S.mem_Lvl.2 ⟨hvv, by omega, by omega⟩
  obtain ⟨W, hW⟩ : ∃ W, S.IsW W j i vv := by
    rcases Nat.lt_or_ge i S.k with h | h
    · exact ⟨_, isW_replace hji h hvv hlv hlw⟩
    · exact ⟨_, isW_induce hji (le_antisymm hik h) hvv hlv hlw⟩
  have hΓsub : (S.Lvl i (i + 1)).image (S.fm vv) ⊆ W.int := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hu
    exact (hW.int u).2 ⟨h1, by omega, by omega⟩
  have hwΓ : S.w ∈ (S.Lvl i (i + 1)).image (S.fm vv) :=
    Finset.mem_image.2 ⟨vv, hvvΓ, by simp [fm]⟩
  have hSSsub : insert S.w (S.Lvl i (i + 1)) ⊆ Z.int := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact (hZ.int _).2 ⟨S.hw, by omega, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
      exact (hZ.int _).2 ⟨h1, by omega, by omega⟩
  have hwSS : S.w ∈ insert S.w (S.Lvl i (i + 1)) := Finset.mem_insert_self _ _
  -- the internal vertices
  have hint : ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).int =
      ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).int := by
    ext v
    rw [convert_int, mem_collapse_int hΓsub hwΓ, collapse_convert, convert_int,
      mem_collapse_int hSSsub hwSS, hZ.int]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · obtain ⟨u, hu1, hu2, hu3, rfl⟩ := hW.int' _ h1
        have hui : S.lev u ≠ i := fun h => h2 (Finset.mem_image_of_mem _
          (S.mem_Lvl.2 ⟨hu1, by omega, by omega⟩))
        have huv : u ≠ vv := fun h => hui (h ▸ hlv)
        simp only [fm, huv, if_false] at h2 ⊢
        by_cases huw : u = S.w
        · exact Or.inl huw
        · refine Or.inr ⟨⟨hu1, hu2, hu3⟩, ?_⟩
          rw [Finset.mem_insert, not_or]
          exact ⟨huw, fun h => hui (by have := (S.mem_Lvl.1 h).2; omega)⟩
    · rintro (h | ⟨⟨h1, h2, h3⟩, h4⟩)
      · exact Or.inl h
      · rw [Finset.mem_insert, not_or] at h4
        have hvi : S.lev v ≠ i := fun h => h4.2 (S.mem_Lvl.2 ⟨h1, by omega, by omega⟩)
        have hvv' : v ≠ vv := fun h => hvi (h ▸ hlv)
        have hfv : S.fm vv v = v := by simp [fm, hvv']
        refine Or.inr ⟨by rw [← hfv]; exact (hW.int v).2 ⟨h1, h2, h3⟩, ?_⟩
        rw [← hfv, fm_mem_Γ hvvΓ]
        rintro (h | h)
        · exact hvi (by have := (S.mem_Lvl.1 h).2; omega)
        · exact h4.1 h
  -- the edges
  have hW'trivial : ∀ x, ((S.ordB i).Nodup → True) →
      ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).cls x ≠
        some .plus → ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
          (S.ordB i)).ends x = (S.w, S.w) →
      ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).Pres x ∧
      ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).IsIntPlus x := by
    intro x _ h1 h2
    exact ⟨fun h => h.2.2.2 (by rw [h2]), fun h => h1 h.1⟩
  have hagree : ∀ x, (((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
      (S.ordB i)).cls x = ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).cls x ∧
      ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).ends x =
        ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).ends x) ∨
      (¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).Pres x ∧
        ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).IsIntPlus x ∧
        ¬ ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).Pres x ∧
        ¬ ((Z.convert p).collapse (insert S.w (S.Lvl i (i + 1))) S.w).IsIntPlus x) := by
    intro x
    by_cases hsp : x = S.e ∨ x = S.e' ∨ (i < S.k ∧ (x = S.cc i ∨ x = S.cc' i))
    · -- the special edges are absent or `Θ` loops at `w`
      have none_case : ∀ y, ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
          (S.ordB i)).cls y = none → ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
            (S.ordB i)).Pres y ∧ ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
              (S.ordB i)).IsIntPlus y := by
        intro y h
        exact ⟨fun h' => h'.1 h, fun h' => by have := h'.1; rw [h] at this; cases this⟩
      have loop_case : ∀ y, ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
          (S.ordB i)).cls y = some .diff → (W.ends y).1 ∈ (S.Lvl i (i + 1)).image (S.fm vv) →
          (W.ends y).2 ∈ (S.Lvl i (i + 1)).image (S.fm vv) →
          ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert (S.ordB i)).Pres y ∧
          ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
            (S.ordB i)).IsIntPlus y := by
        intro y h1 h2 h3
        refine hW'trivial y (fun _ => trivial) (by rw [h1]; simp) ?_
        rw [convert_ends, collapse_ends, if_pos h2, if_pos h3]
      have hWsp : ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
            (S.ordB i)).Pres x ∧ ¬ ((W.collapse ((S.Lvl i (i + 1)).image (S.fm vv)) S.w).convert
              (S.ordB i)).IsIntPlus x := by
        rcases hsp with rfl | rfl | ⟨hk, rfl | rfl⟩
        · by_cases hk : i < S.k ∧ S.e = S.cc' i
          · obtain ⟨-, t2, -, -⟩ := hW.th hk.1
            refine none_case _ ?_
            rw [convert_cls, collapse_cls, hk.2, t2]; simp
          · have hn : i < S.k → S.e ≠ S.cc i ∧ S.e ≠ S.cc' i :=
              fun h => ⟨S.e_ne_cc h, fun h' => hk ⟨h, h'⟩⟩
            obtain ⟨a1, a2, b1, b2⟩ := he (fun h => (hn h).2)
            obtain ⟨w1, w2⟩ := hW.gen _ hn
            have hmem : S.e ∈ S.ordB i := (S.mem_ordB hik _).2 ⟨S.ce, a1, a2, b1, b2⟩
            have w2' : W.cls S.e = some .plus := by
              rw [w2, if_pos ⟨⟨a1, by omega, by omega⟩, ⟨b1, by omega, by omega⟩⟩, S.ce]
            refine loop_case _ ?_ ?_ ?_
            · rw [convert_cls, collapse_cls, w2']
              simp [hmem]
            · rw [w1]; exact Finset.mem_image_of_mem _ (S.mem_Lvl.2 ⟨a1, by omega, by omega⟩)
            · rw [w1]; exact Finset.mem_image_of_mem _ (S.mem_Lvl.2 ⟨b1, by omega, by omega⟩)
        · have hn : i < S.k → S.e' ≠ S.cc i ∧ S.e' ≠ S.cc' i :=
            fun h => ⟨S.e'_ne_cc h, S.e'_ne_cc' h⟩
          obtain ⟨-, w2⟩ := hW.gen _ hn
          have w2' : W.cls S.e' = none := by rw [w2, S.ce']; split_ifs <;> rfl
          refine none_case _ ?_
          rw [convert_cls, collapse_cls, w2']
          simp
        · obtain ⟨t1, -, t3, t4⟩ := hW.th hk
          exact loop_case _ (by rw [convert_cls, collapse_cls, t1]; simp) t3 t4
        · obtain ⟨-, t2, -, -⟩ := hW.th hk
          exact none_case _ (by rw [convert_cls, collapse_cls, t2]; simp)
      exact Or.inr ⟨hWsp.1, hWsp.2, hspec x hsp⟩
    · -- the other edges: the same class and ends
      rw [not_or, not_or, not_and_or] at hsp
      obtain ⟨n1, n2, n3⟩ := hsp
      have hn : i < S.k → x ≠ S.cc i ∧ x ≠ S.cc' i := by
        intro h
        rcases n3 with h' | h'
        · exact absurd h h'
        · rw [not_or] at h'; exact h'
      have hnx : i < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
        intro h
        obtain ⟨c1, c2⟩ := hx12 h
        obtain ⟨m1, m2⟩ := hn h
        refine ⟨fun hx => ?_, fun hx => ?_⟩ <;> subst hx
        · rcases c1 with c | c | c | c
          · exact m1 c
          · exact m2 c
          · exact n1 c
          · exact n2 c
        · rcases c2 with c | c | c | c
          · exact m1 c
          · exact m2 c
          · exact n1 c
          · exact n2 c
      obtain ⟨w1, w2⟩ := hW.gen x hn
      obtain ⟨z1, z2⟩ := hZ.gen x hnx
      rw [split_ends_ne n1 n2] at z1 z2
      rw [split_cls_ne n2] at z2
      left
      constructor
      · rw [convert_cls, collapse_cls, w2, collapse_cls, convert_cls, z2]
        by_cases hc : ((G.ends x).1 ∈ G.int ∧ j ≤ S.lev (G.ends x).1 ∧ S.lev (G.ends x).1 ≤ i) ∧
            ((G.ends x).2 ∈ G.int ∧ j ≤ S.lev (G.ends x).2 ∧ S.lev (G.ends x).2 ≤ i)
        · have hc' : (G.ends x).1 ∈ Z.int ∧ (G.ends x).2 ∈ Z.int :=
            ⟨(hZ.int _).2 hc.1, (hZ.int _).2 hc.2⟩
          rw [if_pos hc, if_pos hc']
          by_cases hpl : G.cls x = some .plus
          · obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := hc
            have h1 := hp x n1 n2 hn hpl a1 a2 a3 b1 b2 b3
            have h2 : x ∈ S.ordB i ↔ (S.lev (G.ends x).1 = i ∧ S.lev (G.ends x).2 = i) := by
              rw [S.mem_ordB hik]
              exact ⟨fun ⟨_, _, h, _, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨hpl, a1, h, b1, h'⟩⟩
            by_cases hm : S.lev (G.ends x).1 = i ∧ S.lev (G.ends x).2 = i
            · rw [if_pos ⟨h2.2 hm, hpl⟩, if_pos ⟨h1.2 hm, hpl⟩]
            · rw [if_neg (fun h => hm (h2.1 h.1)), if_neg (fun h => hm (h1.1 h.1))]
          · rw [if_neg (fun h => hpl h.2), if_neg (fun h => hpl h.2)]
        · have hc' : ¬ ((G.ends x).1 ∈ Z.int ∧ (G.ends x).2 ∈ Z.int) :=
            fun h => hc ⟨(hZ.int _).1 h.1, (hZ.int _).1 h.2⟩
          rw [if_neg hc, if_neg hc']
          simp
      · rw [convert_ends, collapse_ends, w1, collapse_convert_ends, z1, g_fm hvvΓ, g_fm hvvΓ]
  obtain ⟨hle, hip⟩ := le_ip_of_agree hint hagree
  exact preDet_transfer (σ := id) Function.injective_id (hW.quot hji hik hvv hlv) hle
    (fun _ _ => rfl) hip

end Merge

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-- The subgraph induced on the components `a', …, c' - 1` of the graph after operation (B) on the
components `a, …, b`, with blue solid edges changed into `Θ` edges, is doubly connected, if `e`
does not join two of these components. -/
private theorem IsX.dc_part {Z : MGraph V E} {a b : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z a b x₁ x₂) {a' c' : ℕ}
    (ha : a ≤ a') (hc : c' ≤ b + 1) (hk : a' ≤ S.k)
    (he : ¬ ((G.ends S.e).1 ∈ S.Lvl a' c' ∧ (G.ends S.e).2 ∈ S.Lvl a' c'))
    (l : List E) : ((Z.convert l).induce (S.Lvl a' c')).DC := by
  refine dc_le (S.toSplitCtx.dc_Lvl c' hk) ⟨rfl, fun x hx => ?_⟩
  obtain ⟨hc', h1, h2, -⟩ := hx
  have hin : (G.ends x).1 ∈ S.Lvl a' c' ∧ (G.ends x).2 ∈ S.Lvl a' c' := by
    by_contra hn
    simp [MGraph.induce, hn] at hc'
  have hG : (G.induce (S.Lvl a' c')).cls x = G.cls x := by
    simp [MGraph.induce, hin]
  rw [hG] at hc' ⊢
  have hxe : x ≠ S.e := fun h => he (h ▸ hin)
  have hxe' : x ≠ S.e' := fun h => hc' (h ▸ S.ce')
  obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
  obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
  obtain ⟨hze, hzc⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
  have hzin : (Z.ends x).1 ∈ S.Lvl a' c' ∧ (Z.ends x).2 ∈ S.Lvl a' c' := by
    rw [hze]; exact hin
  refine ⟨?_, ?_⟩
  · simp only [id, MGraph.induce, convert_ends, hzin, and_self, if_true]
    rw [convert_cls, hzc]
    split_ifs with h
    · exact Or.inr ⟨h.2, rfl⟩
    · exact Or.inl rfl
  · simp only [id, MGraph.induce, convert_ends, hze]
    exact sameEnds_refl _

/-- The quotient graph by the components `j, …, i - 1` (containing `w`) of a graph `Y` on the
components `j, …, i` is doubly connected, given a doubly connected graph `R` on the component `i`
whose edges other than `g` are edges of `Y`, `g` replaced by a path `g₁`, `g₂` through `w`, the
collapsed vertex being joined to the component `i` by `cc (i - 1)` and `cc' (i - 1)`
([II, Claims A.1, A.3]). -/
private theorem pathU {Z Y R : MGraph V E} {j i : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z j i x₁ x₂) (hji : j < i)
    (hik : i ≤ S.k) (hlw : S.lev S.w = j) (hYi : Y.int = Z.int) (hR : R.DC)
    (hRi : ∀ v, v ∈ R.int ↔ v ∈ G.int ∧ S.lev v = i) {g g₁ g₂ : E}
    (hg : g ≠ S.cc (i - 1) ∧ g ≠ S.cc' (i - 1))
    (h1 : ∀ f, R.Pres f → f ≠ g → (Y.cls f = R.cls f ∨
      (R.cls f = some .plus ∧ Y.cls f = some .diff)) ∧ SameEnds (Y.ends f) (R.ends f))
    (h2 : R.Pres g → Y.cls g₁ = R.cls g ∧ Y.cls g₂ = R.cls g ∧
      SameEnds (Y.ends g₁) ((R.ends g).1, S.w) ∧ SameEnds (Y.ends g₂) (S.w, (R.ends g).2) ∧
      (∀ f, R.Pres f → f ≠ g → f ≠ g₁ ∧ f ≠ g₂) ∧
      g₁ ≠ S.cc (i - 1) ∧ g₂ ≠ S.cc (i - 1) ∧ g₁ ≠ S.cc' (i - 1) ∧ g₂ ≠ S.cc' (i - 1))
    (h3 : Y.cls (S.cc (i - 1)) = some .diff ∧
      (Y.cls (S.cc' (i - 1)) = some .diff ∨ Y.cls (S.cc' (i - 1)) = some .plus) ∧
      Y.ends (S.cc (i - 1)) = G.ends (S.cc (i - 1)) ∧
      Y.ends (S.cc' (i - 1)) = G.ends (S.cc' (i - 1))) :
    (Y.collapse (S.Lvl j i) S.w).DC := by
  have hi1 : i - 1 < S.k := by omega
  have hii : i - 1 + 1 = i := by omega
  have hRint : ∀ v, v ∈ R.int → v ∉ S.Lvl j i := fun v hv h => by
    have := (hRi v).1 hv
    have := (S.mem_Lvl.1 h).2.2
    omega
  have hwU : S.w ∈ S.Lvl j i := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  have hUsub : S.Lvl j i ⊆ Y.int := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    rw [hYi]; exact (hZ.int v).2 ⟨h1, h2, by omega⟩
  -- the ends of an edge with ends in `R`
  have mapR : ∀ f, SameEnds (Y.ends f) (R.ends f) → (R.ends f).1 ∈ R.int → (R.ends f).2 ∈ R.int →
      SameEnds ((Y.collapse (S.Lvl j i) S.w).ends f) (R.ends f) := by
    intro f hf a b
    rw [collapse_ends]
    rcases sameEnds_iff.1 hf with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · rw [if_neg (hRint _ a), if_neg (hRint _ b)]; exact sameEnds_refl _
    · rw [if_neg (hRint _ b), if_neg (hRint _ a)]; exact Or.inr rfl
  -- the crossing edges of `P i`
  have hcr : ∀ y, (y = S.cc (i - 1) ∨ y = S.cc' (i - 1)) → Y.ends y = G.ends y →
      ∃ v, v ∈ R.int ∧ SameEnds ((Y.collapse (S.Lvl j i) S.w).ends y) (S.w, v) ∧
        ¬ R.Pres y := by
    intro y hy hye
    obtain ⟨v, hv, hlv, ho, hlo, hse⟩ := S.cc_ends' hi1 hy
    rw [hii] at hlv
    have hoU : G.outer (S.P (i - 1 + 1)) y ∈ S.Lvl j i := S.mem_Lvl.2 ⟨ho, by omega, by omega⟩
    have hvU : v ∉ S.Lvl j i := fun h => by have := (S.mem_Lvl.1 h).2.2; omega
    refine ⟨v, (hRi v).2 ⟨hv, hlv⟩, ?_, fun hp => ?_⟩
    · rw [collapse_ends, hye]
      rcases sameEnds_iff.1 hse with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;>
        simp only [hoU, hvU, ↓reduceIte]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · have hyg : y ≠ g := by rcases hy with rfl | rfl; exacts [hg.1.symm, hg.2.symm]
      obtain ⟨-, hf⟩ := h1 y hp hyg
      obtain ⟨-, a, b, -⟩ := hp
      have hm := (hf.mem (S := R.int)).2 ⟨a, b⟩
      rw [hye] at hm
      have hm' := (hse.mem (S := R.int)).1 hm
      exact hRint _ hm'.1 hoU
  obtain ⟨v₁, hv₁, s₁, n₁⟩ := hcr _ (Or.inl rfl) h3.2.2.1
  obtain ⟨v₂, hv₂, s₂, n₂⟩ := hcr _ (Or.inr rfl) h3.2.2.2
  refine dc_path (R := R) (N := S.w) (g := g) (g₁ := g₁) (g₂ := g₂) (y₁ := S.cc (i - 1))
    (y₂ := S.cc' (i - 1)) (m₁ := v₁) (m₂ := v₂) hR ?_ ?_ ?_ ?_
  · ext v
    rw [mem_collapse_int hUsub hwU, hYi, hZ.int, Finset.mem_insert, hRi, S.mem_Lvl]
    constructor
    · rintro (h | ⟨⟨h1, h2, h3⟩, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, by by_contra h; exact h4 ⟨h1, h2, by omega⟩⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨h1, by omega, by omega⟩, fun ⟨_, _, h⟩ => by omega⟩
  · intro f hf hfg
    obtain ⟨c, se⟩ := h1 f hf hfg
    exact ⟨c, mapR f se hf.2.1 hf.2.2.1⟩
  · intro hp
    obtain ⟨c1, c2, s1, s2, d, -⟩ := h2 hp
    refine ⟨c1, c2, ?_, ?_, d⟩
    · rw [collapse_ends]
      rcases sameEnds_iff.1 s1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> dsimp only <;>
        simp only [hRint _ hp.2.1, hwU, ↓reduceIte]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [collapse_ends]
      rcases sameEnds_iff.1 s2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> dsimp only <;>
        simp only [hRint _ hp.2.2.1, hwU, ↓reduceIte]
      · exact Or.inl rfl
      · exact Or.inr rfl
  · intro _
    refine ⟨by rw [collapse_cls]; exact h3.1, by rw [collapse_cls]; exact h3.2.1, s₁, s₂, hv₁, hv₂,
      S.cc_ne _ hi1, fun f hf _ => ⟨fun h => n₁ (h ▸ hf), fun h => n₂ (h ▸ hf)⟩, fun hp => ?_⟩
    obtain ⟨-, -, -, -, -, a, b, c, d⟩ := h2 hp
    exact ⟨a.symm, b.symm, c.symm, d.symm⟩

/-- The hypotheses of `pathU` are kept when the same edge `x`, other than the edges of the path
and the crossing edges of `P i`, is removed from both graphs. -/
private theorem pathU_erase {Y R : MGraph V E} {i : ℕ} {g g₁ g₂ x : E}
    (h1 : ∀ f, R.Pres f → f ≠ g → (Y.cls f = R.cls f ∨
      (R.cls f = some .plus ∧ Y.cls f = some .diff)) ∧ SameEnds (Y.ends f) (R.ends f))
    (h2 : R.Pres g → Y.cls g₁ = R.cls g ∧ Y.cls g₂ = R.cls g ∧
      SameEnds (Y.ends g₁) ((R.ends g).1, S.w) ∧ SameEnds (Y.ends g₂) (S.w, (R.ends g).2) ∧
      (∀ f, R.Pres f → f ≠ g → f ≠ g₁ ∧ f ≠ g₂) ∧
      g₁ ≠ S.cc (i - 1) ∧ g₂ ≠ S.cc (i - 1) ∧ g₁ ≠ S.cc' (i - 1) ∧ g₂ ≠ S.cc' (i - 1))
    (h3 : Y.cls (S.cc (i - 1)) = some .diff ∧
      (Y.cls (S.cc' (i - 1)) = some .diff ∨ Y.cls (S.cc' (i - 1)) = some .plus) ∧
      Y.ends (S.cc (i - 1)) = G.ends (S.cc (i - 1)) ∧
      Y.ends (S.cc' (i - 1)) = G.ends (S.cc' (i - 1)))
    (hxg : x ≠ g) (hx1 : x ≠ g₁) (hx2 : x ≠ g₂) (hxc : x ≠ S.cc (i - 1))
    (hxc' : x ≠ S.cc' (i - 1)) :
    (∀ f, (R.erase x).Pres f → f ≠ g → ((Y.erase x).cls f = (R.erase x).cls f ∨
      ((R.erase x).cls f = some .plus ∧ (Y.erase x).cls f = some .diff)) ∧
      SameEnds ((Y.erase x).ends f) ((R.erase x).ends f)) ∧
    ((R.erase x).Pres g → (Y.erase x).cls g₁ = (R.erase x).cls g ∧
      (Y.erase x).cls g₂ = (R.erase x).cls g ∧
      SameEnds ((Y.erase x).ends g₁) (((R.erase x).ends g).1, S.w) ∧
      SameEnds ((Y.erase x).ends g₂) (S.w, ((R.erase x).ends g).2) ∧
      (∀ f, (R.erase x).Pres f → f ≠ g → f ≠ g₁ ∧ f ≠ g₂) ∧
      g₁ ≠ S.cc (i - 1) ∧ g₂ ≠ S.cc (i - 1) ∧ g₁ ≠ S.cc' (i - 1) ∧ g₂ ≠ S.cc' (i - 1)) ∧
    ((Y.erase x).cls (S.cc (i - 1)) = some .diff ∧
      ((Y.erase x).cls (S.cc' (i - 1)) = some .diff ∨
        (Y.erase x).cls (S.cc' (i - 1)) = some .plus) ∧
      (Y.erase x).ends (S.cc (i - 1)) = G.ends (S.cc (i - 1)) ∧
      (Y.erase x).ends (S.cc' (i - 1)) = G.ends (S.cc' (i - 1))) := by
  have pres : ∀ f, (R.erase x).Pres f → R.Pres f ∧ f ≠ x := by
    intro f hf
    have hfx : f ≠ x := by rintro rfl; exact hf.1 (by rw [erase_cls]; simp)
    obtain ⟨c, h⟩ := hf
    rw [erase_cls, if_neg hfx] at c
    exact ⟨⟨c, h⟩, hfx⟩
  refine ⟨fun f hf hfg => ?_, fun hp => ?_, ?_⟩
  · obtain ⟨hp, hfx⟩ := pres f hf
    rw [erase_cls, erase_cls, if_neg hfx, if_neg hfx, erase_ends, erase_ends]
    exact h1 f hp hfg
  · obtain ⟨hp, -⟩ := pres g hp
    obtain ⟨c1, c2, s1, s2, d, r⟩ := h2 hp
    rw [erase_cls, erase_cls, erase_cls, if_neg hx1.symm, if_neg hx2.symm, if_neg hxg.symm]
    simp only [erase_ends]
    exact ⟨c1, c2, s1, s2, fun f hf hfg => d f (pres f hf).1 hfg, r⟩
  · rw [erase_cls, erase_cls, if_neg hxc.symm, if_neg hxc'.symm, erase_ends]
    exact h3

/-- A redundancy step of the component `i` of the graph on the components `j, …, i`, from the
doubly connected property of the quotient graphs by the components `j, …, i - 1`
([II, Claim A.1]). -/
private theorem IsX.stepU {Z : MGraph V E} {j i : ℕ} {x₁ x₂ : E} (hZ : S.IsX Z j i x₁ x₂) (hji : j < i)
    (hik : i ≤ S.k) (hlw : S.lev S.w = j)
    (he : ¬ ((G.ends S.e).1 ∈ S.Lvl j i ∧ (G.ends S.e).2 ∈ S.Lvl j i)) {l : List E} {x : E}
    (hx : ¬ ((Z.ends x).1 ∈ S.Lvl j i ∧ (Z.ends x).2 ∈ S.Lvl j i))
    (hxc : (Z.convert l).cls x = some .plus)
    (hQ1 : ((Z.convert l).collapse (S.Lvl j i) S.w).DC)
    (hQ2 : (((Z.convert l).erase x).collapse (S.Lvl j i) S.w).DC) :
    (Z.convert l).IsRedundant x := by
  have hUsub : S.Lvl j i ⊆ (Z.convert l).int := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
    rw [convert_int]; exact (hZ.int v).2 ⟨h1, h2, by omega⟩
  have hwU : S.w ∈ S.Lvl j i := S.mem_Lvl.2 ⟨S.hw, by omega, by omega⟩
  have hI := hZ.dc_part (a' := j) (c' := i) le_rfl (by omega) (by omega) he l
  refine ⟨hxc, dc_glue hUsub hwU hI hQ1, dc_glue (X := (Z.convert l).erase x) hUsub hwU ?_ hQ2⟩
  rw [induce_erase_out _ _ (by rw [convert_ends]; exact hx)]
  exact hI

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-! ### Case (ii) of [II, Lemma 5.12] -/

/-- The setting of case (ii) of [II, Lemma 5.12]: the ends of `e` in the component `i`, `w` in the
component `j < i`. -/
structure CaseII (S : SC G) (j i : ℕ) : Prop where
  hji : j < i
  hik : i ≤ S.k
  ha : (G.ends S.e).1 ∈ G.int
  hla : S.lev (G.ends S.e).1 = i
  hb : (G.ends S.e).2 ∈ G.int
  hlb : S.lev (G.ends S.e).2 = i
  hlw : S.lev S.w = j

section CaseII

variable {j i : ℕ} (hC : S.CaseII j i) {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z j i x₁ x₂)
  {B : MGraph V E} (hB : S.IsB B i x₁ x₂)
include hC hZ hB

/-- The edges `e`, `e'` in the graph of case (ii): the path from the component `i` to `w`. -/
private theorem CaseII.path :
    Z.cls S.e = some .plus ∧ Z.ends S.e = ((G.ends S.e).1, S.w) ∧
    Z.cls S.e' = some .plus ∧ Z.ends S.e' = (S.w, (G.ends S.e).2) := by
  have hji := hC.hji
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have hge : S.Gt.ends S.e = ((G.ends S.e).1, S.w) := split_ends_e
  have hge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
  obtain ⟨z1, z2⟩ := hZ.gedge (x := S.e) (by rw [hge]; exact hC.ha)
    (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega) (by rw [hge]; exact S.hw)
    (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega)
  obtain ⟨z1', z2'⟩ := hZ.gedge (x := S.e') (by rw [hge']; exact S.hw)
    (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
    (by rw [hge']; exact hC.hb) (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
  exact ⟨by rw [z2, split_cls_of S.hne, S.ce], z1.trans hge, by rw [z2', split_cls_e', S.ce],
    z1'.trans hge'⟩

/-- The `Θ` edge replacing `P (i + 1)` is not `e` or `e'`. -/
private theorem CaseII.x12 (hb : i < S.k) : x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e' := by
  obtain ⟨h1, h2, -⟩ := hB.x12 hb
  have hla := hC.hla
  have hlb := hC.hlb
  have ne : ∀ x, (x = S.cc i ∨ x = S.cc' i) → x ≠ S.e ∧ x ≠ S.e' := by
    intro x hx
    obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hb hx
    refine ⟨by rintro rfl; omega, ?_⟩
    rintro rfl
    rcases hx with h' | h'
    · exact S.e'_ne_cc hb h'
    · exact S.e'_ne_cc' hb h'
  exact ⟨(ne _ h1).1, (ne _ h1).2, (ne _ h2).1, (ne _ h2).2⟩

/-- The hypotheses of `pathU` for the graph of case (ii) with the blue solid edges of `l` changed
into `Θ` edges and the graph of the component `i` with those of `m`. -/
private theorem CaseII.hyps {l m : List E}
    (hlm : ∀ f, f ≠ S.e → G.cls f = some .plus → f ∈ m → f ∈ l)
    (he1 : S.e ∈ l ↔ S.e ∈ m) (he2 : S.e' ∈ l ↔ S.e ∈ m) :
    (∀ f, (B.convert m).Pres f → f ≠ S.e → ((Z.convert l).cls f = (B.convert m).cls f ∨
      ((B.convert m).cls f = some .plus ∧ (Z.convert l).cls f = some .diff)) ∧
      SameEnds ((Z.convert l).ends f) ((B.convert m).ends f)) ∧
    ((B.convert m).Pres S.e → (Z.convert l).cls S.e = (B.convert m).cls S.e ∧
      (Z.convert l).cls S.e' = (B.convert m).cls S.e ∧
      SameEnds ((Z.convert l).ends S.e) (((B.convert m).ends S.e).1, S.w) ∧
      SameEnds ((Z.convert l).ends S.e') (S.w, ((B.convert m).ends S.e).2) ∧
      (∀ f, (B.convert m).Pres f → f ≠ S.e → f ≠ S.e ∧ f ≠ S.e') ∧
      S.e ≠ S.cc (i - 1) ∧ S.e' ≠ S.cc (i - 1) ∧ S.e ≠ S.cc' (i - 1) ∧ S.e' ≠ S.cc' (i - 1)) ∧
    ((Z.convert l).cls (S.cc (i - 1)) = some .diff ∧
      ((Z.convert l).cls (S.cc' (i - 1)) = some .diff ∨
        (Z.convert l).cls (S.cc' (i - 1)) = some .plus) ∧
      (Z.convert l).ends (S.cc (i - 1)) = G.ends (S.cc (i - 1)) ∧
      (Z.convert l).ends (S.cc' (i - 1)) = G.ends (S.cc' (i - 1))) := by
  have hji := hC.hji
  have hik := hC.hik
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  have hi1 : i - 1 < S.k := by omega
  obtain ⟨p1, p2, p3, p4⟩ := hC.path hZ hB
  have hBe : B.cls S.e = some .plus ∧ B.ends S.e = G.ends S.e := by
    have hp : B.IsIntPlus S.e := (hB.ip _).2 ⟨S.ce, hC.ha, hla, hC.hb, hlb⟩
    rcases hB.pres _ (by rw [hp.1]; simp) with ⟨hb, h, -⟩ | ⟨-, -, -, -, -, hc, he⟩
    · exact absurd h.symm (hC.x12 hZ hB hb).1
    · exact ⟨hc ▸ hp.1, he⟩
  have hcc : ∀ y, (y = S.cc (i - 1) ∨ y = S.cc' (i - 1)) → Z.ends y = G.ends y ∧
      Z.cls y = G.cls y ∧ y ≠ S.e ∧ y ≠ S.e' := by
    intro y hy
    obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hi1 hy
    have hye : y ≠ S.e := by rintro rfl; omega
    have hye' : y ≠ S.e' := by
      rcases hy with rfl | rfl
      · exact (S.e'_ne_cc hi1).symm
      · exact (S.e'_ne_cc' hi1).symm
    obtain ⟨z1, z2⟩ := hZ.edge hye hye' g1 (by omega) (by omega) g2 (by omega) (by omega)
    exact ⟨z1, z2, hye, hye'⟩
  obtain ⟨c1, c2, c3, c4⟩ := hcc _ (Or.inl rfl)
  obtain ⟨d1, d2, d3, d4⟩ := hcc _ (Or.inr rfl)
  refine ⟨fun f hf hfe => ?_, fun _ => ?_, ?_⟩
  · rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨hb, rfl, hc, hen⟩ |
      ⟨hn, a1, a2, b1, b2, hc, hen⟩
    · obtain ⟨-, t1, -, t2, -, -⟩ := hZ.th hb
      obtain ⟨n1, n2, n3, n4⟩ := hC.x12 hZ hB hb
      refine ⟨Or.inl ?_, ?_⟩
      · rw [convert_cls, convert_cls, t1, hc]; simp
      · rw [convert_ends, convert_ends, t2, hen]
        unfold MGraph.outer
        rw [split_ends_ne n1 n2, split_ends_ne n3 n4]
        exact sameEnds_refl _
    · have hfe' : f ≠ S.e' := by
        rintro rfl; exact (convert_ne_none.1 hf.1) (by rw [hc, S.ce'])
      obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1 (by omega) (by omega) b1 (by omega) (by omega)
      refine ⟨?_, by rw [convert_ends, convert_ends, z1, hen]; exact sameEnds_refl _⟩
      have hZf : (Z.convert l).cls f =
          if f ∈ l ∧ G.cls f = some .plus then some .diff else G.cls f := by
        rw [convert_cls, z2]
      have hBf : (B.convert m).cls f =
          if f ∈ m ∧ G.cls f = some .plus then some .diff else G.cls f := by
        rw [convert_cls, hc]
      rw [hZf, hBf]
      by_cases hp : G.cls f = some .plus
      · by_cases hm : f ∈ m
        · rw [if_pos (show f ∈ l ∧ G.cls f = some .plus from ⟨hlm f hfe hp hm, hp⟩),
            if_pos (show f ∈ m ∧ G.cls f = some .plus from ⟨hm, hp⟩)]
          exact Or.inl rfl
        · rw [if_neg (show ¬ (f ∈ m ∧ G.cls f = some .plus) from fun h => hm h.1)]
          by_cases hl : f ∈ l
          · rw [if_pos (show f ∈ l ∧ G.cls f = some .plus from ⟨hl, hp⟩)]
            exact Or.inr ⟨hp, rfl⟩
          · rw [if_neg (show ¬ (f ∈ l ∧ G.cls f = some .plus) from fun h => hl h.1)]
            exact Or.inl rfl
      · rw [if_neg (show ¬ (f ∈ l ∧ G.cls f = some .plus) from fun h => hp h.2),
          if_neg (show ¬ (f ∈ m ∧ G.cls f = some .plus) from fun h => hp h.2)]
        exact Or.inl rfl
  · refine ⟨?_, ?_, ?_, ?_, fun f hf hfe => ⟨hfe, ?_⟩, c3.symm, c4.symm, d3.symm, d4.symm⟩
    · rw [convert_cls, convert_cls, p1, hBe.1]; simp only [he1]
    · rw [convert_cls, convert_cls, p3, hBe.1]; simp only [he2]
    · rw [convert_ends, convert_ends, p2, hBe.2]; exact sameEnds_refl _
    · rw [convert_ends, convert_ends, p4, hBe.2]; exact sameEnds_refl _
    · rintro rfl
      obtain ⟨hc, -⟩ := hf
      rcases hB.pres _ (fun h => hc (by rw [convert_cls, h]; simp)) with
        ⟨hb, h, -⟩ | ⟨-, -, -, -, -, h, -⟩
      · exact (hC.x12 hZ hB hb).2.1 h.symm
      · exact hc (by rw [convert_cls, h, S.ce']; simp)
  · refine ⟨?_, ?_, by rw [convert_ends, c1], by rw [convert_ends, d1]⟩
    · rw [convert_cls, c2, S.cc_diff _ hi1]; simp
    · rw [convert_cls, d2]
      rcases S.cc'_cls _ hi1 with h | h <;> rw [h] <;> split_ifs <;> simp

/-- The facts on the component `i` in case (ii): the edges of `G` inside it are not inside the
components `j, …, i - 1`, nor are `e`, `e'`, and `e` does not join two of these components. -/
private theorem CaseII.facts :
    (∀ f, (G.ends f).1 ∈ G.int → S.lev (G.ends f).1 = i → (G.ends f).2 ∈ G.int →
      S.lev (G.ends f).2 = i → f ≠ S.e → f ≠ S.e' →
      Z.ends f = G.ends f ∧ Z.cls f = G.cls f ∧
      ¬ ((Z.ends f).1 ∈ S.Lvl j i ∧ (Z.ends f).2 ∈ S.Lvl j i)) ∧
    ¬ ((G.ends S.e).1 ∈ S.Lvl j i ∧ (G.ends S.e).2 ∈ S.Lvl j i) ∧
    ¬ ((Z.ends S.e).1 ∈ S.Lvl j i ∧ (Z.ends S.e).2 ∈ S.Lvl j i) ∧
    ¬ ((Z.ends S.e').1 ∈ S.Lvl j i ∧ (Z.ends S.e').2 ∈ S.Lvl j i) ∧
    S.e ≠ S.cc (i - 1) ∧ S.e ≠ S.cc' (i - 1) ∧ S.e' ≠ S.cc (i - 1) ∧ S.e' ≠ S.cc' (i - 1) := by
  have hji := hC.hji
  have hik := hC.hik
  have hla := hC.hla
  have hlb := hC.hlb
  have hi1 : i - 1 < S.k := by omega
  obtain ⟨-, p2, -, p4⟩ := hC.path hZ hB
  have notU : ∀ v, S.lev v = i → v ∉ S.Lvl j i := fun v h h' => by
    have := (S.mem_Lvl.1 h').2.2; omega
  refine ⟨fun f a1 a2 b1 b2 hfe hfe' => ?_, fun h => notU _ hla h.1,
    by rw [p2]; exact fun h => notU _ hla h.1, by rw [p4]; exact fun h => notU _ hlb h.2, ?_, ?_,
    S.e'_ne_cc hi1, S.e'_ne_cc' hi1⟩
  · obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1 (by omega) (by omega) b1 (by omega) (by omega)
    exact ⟨z1, z2, by rw [z1]; exact fun h => notU _ a2 h.1⟩
  · intro h; obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hi1 (Or.inl h); omega
  · intro h; obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev hi1 (Or.inr h); omega

/-- The internal vertices of the graph of the component `i`. -/
private theorem CaseII.Bint (m : List E) : ∀ v, v ∈ (B.convert m).int ↔ v ∈ G.int ∧ S.lev v = i := by
  intro v; rw [convert_int]; exact hB.int v

/-- A redundancy step in case (ii) for an edge `x` inside the component `i` other than `e`
([II, Claim A.2]): the redundancy of `x` in the graph of the component, with the blue solid edges of
`m` changed into `Θ` edges, and `e` replaced by the path through `w`. -/
private theorem CaseII.stepX {l m : List E} {x : E}
    (hlm : ∀ f, f ≠ S.e → G.cls f = some .plus → f ∈ m → f ∈ l)
    (he1 : S.e ∈ l ↔ S.e ∈ m) (he2 : S.e' ∈ l ↔ S.e ∈ m)
    (hr : (B.convert m).IsRedundant x) (hxe : x ≠ S.e) (hxe' : x ≠ S.e')
    (hx1 : (G.ends x).1 ∈ G.int) (hx2 : S.lev (G.ends x).1 = i) (hx3 : (G.ends x).2 ∈ G.int)
    (hx4 : S.lev (G.ends x).2 = i) (hxl : x ∉ l) : (Z.convert l).IsRedundant x := by
  obtain ⟨F, he, -, -, ce, ce', c'e, c'e'⟩ := hC.facts hZ hB
  obtain ⟨z1, z2, z3⟩ := F x hx1 hx2 hx3 hx4 hxe hxe'
  obtain ⟨h1, h2, h3⟩ := hC.hyps hZ hB hlm he1 he2
  have hxc : x ≠ S.cc (i - 1) := by
    intro h; obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev (by have := hC.hik; have := hC.hji; omega)
      (Or.inl h); omega
  have hxc' : x ≠ S.cc' (i - 1) := by
    intro h; obtain ⟨-, -, h'⟩ := S.toSplitCtx.cc_lev (by have := hC.hik; have := hC.hji; omega)
      (Or.inr h); omega
  obtain ⟨h1', h2', h3'⟩ := pathU_erase h1 h2 h3 hxe hxe hxe' hxc hxc'
  refine hZ.stepU hC.hji hC.hik hC.hlw he z3 ?_ ?_ ?_
  · rw [convert_cls_of_not_mem hxl, z2]
    have hBp : B.cls x = some .plus := by
      have := hr.1
      rw [convert_cls] at this
      split_ifs at this with h
      · exact h.2
      · exact this
    rcases hB.pres x (by rw [hBp]; simp) with ⟨-, -, hc, -⟩ | ⟨-, -, -, -, -, hc, -⟩
    · rw [hc] at hBp; cases hBp
    · rw [← hc]; exact hBp
  · exact pathU hZ hC.hji hC.hik hC.hlw rfl hr.2.1 (hC.Bint hZ hB m) ⟨ce, ce'⟩ h1 h2 h3
  · exact pathU hZ hC.hji hC.hik hC.hlw rfl hr.2.2 (fun v => by rw [erase_int]; exact hC.Bint hZ hB m v)
      ⟨ce, ce'⟩ h1' h2' h3'

/-- The step of `e` in case (ii): [II, Claim A.3]. -/
private theorem CaseII.stepE {α : List E} (hα : S.e ∉ α) (hα' : S.e' ∉ α)
    (hr : (B.convert α).IsRedundant S.e) : (Z.convert α).IsRedundant S.e := by
  obtain ⟨-, he, ze, -, ce, ce', c'e, c'e'⟩ := hC.facts hZ hB
  obtain ⟨p1, -, -, -⟩ := hC.path hZ hB
  obtain ⟨h1, h2, h3⟩ := hC.hyps hZ hB (l := α) (m := α) (fun _ _ _ h => h) Iff.rfl
    (iff_of_false hα' hα)
  refine hZ.stepU hC.hji hC.hik hC.hlw he ze (by rw [convert_cls_of_not_mem hα, p1]) ?_ ?_
  · exact pathU hZ hC.hji hC.hik hC.hlw rfl hr.2.1 (hC.Bint hZ hB α) ⟨ce, ce'⟩ h1 h2 h3
  · refine pathU hZ hC.hji hC.hik hC.hlw rfl hr.2.2
      (fun v => by rw [erase_int]; exact hC.Bint hZ hB α v) ⟨ce, ce'⟩ (g := S.e) (g₁ := S.e)
      (g₂ := S.e') (fun f hf hfe => ?_) (fun hp => absurd hp.1 (by rw [erase_cls]; simp)) ?_
    · have hp : (B.convert α).Pres f := by
        obtain ⟨c, h⟩ := hf; rw [erase_cls, if_neg hfe] at c; exact ⟨c, h⟩
      rw [erase_cls, erase_cls, if_neg hfe, if_neg hfe, erase_ends, erase_ends]
      exact h1 f hp hfe
    · rw [erase_cls, erase_cls, if_neg ce.symm, if_neg ce'.symm, erase_ends]
      exact h3

/-- The step of `e'` in case (ii), after `e`: the graph of the component without `e`. -/
private theorem CaseII.stepE' {α : List E} (hα : S.e ∉ α) (hα' : S.e' ∉ α)
    (hdc : ((B.convert α).erase S.e).DC) : (Z.convert (α ++ [S.e])).IsRedundant S.e' := by
  obtain ⟨-, he, -, ze', ce, ce', c'e, c'e'⟩ := hC.facts hZ hB
  obtain ⟨-, -, p3, -⟩ := hC.path hZ hB
  obtain ⟨h1, h2, h3⟩ := hC.hyps hZ hB (l := α) (m := α) (fun _ _ _ h => h) Iff.rfl
    (iff_of_false hα' hα)
  have hl' : S.e' ∉ α ++ [S.e] := by
    simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hα', S.hne.symm⟩
  have hR : ∀ f, ((B.convert α).erase S.e).Pres f → f ≠ S.e ∧ f ≠ S.e' ∧ (B.convert α).Pres f := by
    intro f hf
    have hfe : f ≠ S.e := by rintro rfl; exact hf.1 (by rw [erase_cls]; simp)
    obtain ⟨c, h⟩ := hf
    rw [erase_cls, if_neg hfe] at c
    refine ⟨hfe, ?_, ⟨c, h⟩⟩
    rintro rfl
    rcases hB.pres _ (convert_ne_none.1 c) with ⟨hb, h', -⟩ | ⟨-, -, -, -, -, h', -⟩
    · exact (hC.x12 hZ hB hb).2.1 h'.symm
    · exact convert_ne_none.1 c (by rw [h', S.ce'])
  have key : ∀ Y : MGraph V E, Y.int = Z.int → Y.ends = Z.ends →
      (∀ f, f ≠ S.e → f ≠ S.e' → Y.cls f = (Z.convert α).cls f) →
      (Y.collapse (S.Lvl j i) S.w).DC := by
    intro Y hYi hYe hYc
    refine pathU hZ hC.hji hC.hik hC.hlw hYi hdc
      (fun v => by rw [erase_int]; exact hC.Bint hZ hB α v) ⟨ce, ce'⟩ (g := S.e) (g₁ := S.e)
      (g₂ := S.e') (fun f hf hfe => ?_) (fun hp => absurd hp.1 (by rw [erase_cls]; simp)) ?_
    · obtain ⟨-, hfe', hp⟩ := hR f hf
      rw [hYc f hfe hfe', erase_cls, if_neg hfe, hYe, erase_ends]
      exact h1 f hp hfe
    · rw [hYc _ ce.symm c'e.symm, hYc _ ce'.symm c'e'.symm, hYe]
      exact h3
  refine hZ.stepU hC.hji hC.hik hC.hlw he ze' (by rw [convert_cls_of_not_mem hl', p3]) ?_ ?_
  · exact key _ rfl rfl (fun f hfe _ => convert_append_ne _ _ hfe)
  · exact key _ rfl rfl (fun f hfe hfe' => by
      rw [erase_cls, if_neg hfe', convert_append_ne _ _ hfe])

/-- The steps of the component `i` in case (ii): the order of the graph of the component, with
`e` replaced by `e`, `e'`. -/
private theorem CaseII.bottom {ℓ : List E} (hℓ : B.IsPDOrder ℓ) {α β : List E}
    (hord : ℓ = α ++ S.e :: β) : Steps Z (α ++ [S.e, S.e'] ++ β) := by
  have hnd := hℓ.1
  rw [hord] at hnd
  have hndα : α.Nodup := (List.nodup_append.1 hnd).1
  have hndβ : β.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).2
  have eα : S.e ∉ α := fun h => (List.nodup_append.1 hnd).2.2 _ h _ List.mem_cons_self rfl
  have eβ : S.e ∉ β := fun h => (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 h
  have hαβ : ∀ y ∈ α, y ∉ β := fun y hy hy' =>
    (List.nodup_append.1 hnd).2.2 _ hy _ (List.mem_cons_of_mem _ hy') rfl
  have mem : ∀ y ∈ ℓ, G.cls y = some .plus ∧ (G.ends y).1 ∈ G.int ∧ S.lev (G.ends y).1 = i ∧
      (G.ends y).2 ∈ G.int ∧ S.lev (G.ends y).2 = i := fun y hy => (hB.ip y).1 ((hℓ.2.1 y).1 hy)
  have ne' : ∀ y ∈ ℓ, y ≠ S.e' := fun y hy h => by
    have := (mem y hy).1; rw [h, S.ce'] at this; cases this
  have mα : ∀ y ∈ α, y ∈ ℓ := fun y hy => by rw [hord]; simp [hy]
  have mβ : ∀ y ∈ β, y ∈ ℓ := fun y hy => by rw [hord]; simp [hy]
  have e'α : S.e' ∉ α := fun h => ne' _ (mα _ h) rfl
  have hlen : α.length < ℓ.length := by rw [hord]; simp
  have hre : (B.convert α).IsRedundant S.e := by
    have := hℓ.2.2 α.length hlen
    simp only [hord, List.take_left', List.getElem_append_right le_rfl, Nat.sub_self,
      List.getElem_cons_zero] at this
    exact this
  rw [steps_append, steps_append]
  refine ⟨⟨fun t ht => ?_, ?_⟩, fun t ht => ?_⟩
  · -- the steps of `α`
    have ht' : t < ℓ.length := by omega
    have hr := hℓ.2.2 t ht'
    simp only [hord, List.take_append_of_le_length ht.le, List.getElem_append_left ht] at hr
    have hx := mem _ (mα _ (List.getElem_mem ht))
    exact hC.stepX hZ hB (m := α.take t) (fun _ _ _ h => h) (iff_of_false
      (fun h => eα (List.mem_of_mem_take h)) (fun h => eα (List.mem_of_mem_take h)))
      (iff_of_false (fun h => e'α (List.mem_of_mem_take h)) (fun h => eα (List.mem_of_mem_take h)))
      hr (fun h => eα (h ▸ List.getElem_mem ht)) (ne' _ (mα _ (List.getElem_mem ht))) hx.2.1
      hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2 (getElem_not_mem_take hndα ht)
  · -- the steps of `e`, `e'`
    rw [steps_cons, steps_single, convert_convert']
    exact ⟨hC.stepE hZ hB eα e'α hre, hC.stepE' hZ hB eα e'α hre.2.2⟩
  · -- the steps of `β`
    rw [convert_convert']
    have ht' : α.length + 1 + t < ℓ.length := by rw [hord]; simp; omega
    have hr := hℓ.2.2 _ ht'
    have hg : ℓ[α.length + 1 + t] = β[t] := by
      simp only [hord]; exact getElem_mid S.e α β t ht _
    rw [hg] at hr
    simp only [hord, take_mid] at hr
    have hxβ : β[t] ∈ β := List.getElem_mem ht
    have hx := mem _ (mβ _ hxβ)
    have hxe : β[t] ≠ S.e := fun h => eβ (h ▸ hxβ)
    have hxe' := ne' _ (mβ _ hxβ)
    refine hC.stepX hZ hB (m := α ++ S.e :: β.take t) (fun f hfe _ hf => ?_) ?_ ?_ hr hxe hxe'
      hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2 ?_
    · have hf' : f ∈ α ∨ f = S.e ∨ f ∈ β.take t := by
        simpa only [List.mem_append, List.mem_cons] using hf
      have goal : f ∈ α ∨ f ∈ β.take t → f ∈ α ++ [S.e, S.e'] ++ β.take t := by
        intro h; simp only [List.mem_append, List.mem_cons, List.mem_singleton]; tauto
      rcases hf' with h | h | h
      · exact goal (Or.inl h)
      · exact absurd h hfe
      · exact goal (Or.inr h)
    · exact iff_of_true (by simp) (by simp)
    · exact iff_of_true (by simp) (by simp)
    · intro h
      have h' : β[t] ∈ α ∨ β[t] = S.e ∨ β[t] = S.e' ∨ β[t] ∈ β.take t := by
        simpa only [List.append_assoc, List.mem_append, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false, or_assoc] using h
      rcases h' with h | h | h | h
      · exact hαβ _ h hxβ
      · exact hxe h
      · exact hxe' h
      · exact getElem_not_mem_take hndβ ht h

/-- **Case (ii) of [II, Lemma 5.12]**: the graph after operation (B) on the components `j, …, i`,
with the ends of `e` in the component `i` and `w` in the component `j < i`, is pre-deterministic:
the component `i` first, with `e` replaced by `e`, `e'`; then the component `i` and `w` collapsed
give the graph of [II, Lemma 5.11]. -/
private theorem CaseII.preDet (hBpd : B.PreDet) : Z.PreDet := by
  have hji := hC.hji
  have hik := hC.hik
  have hla := hC.hla
  have hlb := hC.hlb
  have hlw := hC.hlw
  obtain ⟨-, ℓ, hℓ⟩ := hBpd
  have mem : ∀ y, y ∈ ℓ ↔ G.cls y = some .plus ∧ (G.ends y).1 ∈ G.int ∧
      S.lev (G.ends y).1 = i ∧ (G.ends y).2 ∈ G.int ∧ S.lev (G.ends y).2 = i :=
    fun y => (hℓ.2.1 y).trans (hB.ip y)
  obtain ⟨α, β, hord⟩ := List.append_of_mem ((mem _).2 ⟨S.ce, hC.ha, hla, hC.hb, hlb⟩)
  have hnd := hℓ.1
  rw [hord] at hnd
  have eα : S.e ∉ α := fun h => (List.nodup_append.1 hnd).2.2 _ h _ List.mem_cons_self rfl
  have eβ : S.e ∉ β := fun h => (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 h
  have mα : ∀ y ∈ α, y ∈ ℓ := fun y hy => by rw [hord]; simp [hy]
  have mβ : ∀ y ∈ β, y ∈ ℓ := fun y hy => by rw [hord]; simp [hy]
  have ne' : ∀ y ∈ ℓ, y ≠ S.e' := fun y hy h => by
    have := ((mem y).1 hy).1; rw [h, S.ce'] at this; cases this
  have hp := hC.bottom hZ hB hℓ hord
  have hre_dc : ((B.convert α).erase S.e).DC := by
    have hlen : α.length < ℓ.length := by rw [hord]; simp
    have := hℓ.2.2 α.length hlen
    simp only [hord, List.take_left', List.getElem_append_right le_rfl, Nat.sub_self,
      List.getElem_cons_zero] at this
    exact this.2.2
  -- the internal blue solid edges of the list
  obtain ⟨F, -, -, -, -, -, -, -⟩ := hC.facts hZ hB
  obtain ⟨p1, p2, p3, p4⟩ := hC.path hZ hB
  have memp : ∀ y, y ∈ α ++ [S.e, S.e'] ++ β ↔ y = S.e ∨ y = S.e' ∨ (y ∈ ℓ ∧ y ≠ S.e) := by
    intro y
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · rintro ((h | h | h) | h)
      · exact Or.inr (Or.inr ⟨mα y h, fun h' => eα (h' ▸ h)⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨mβ y h, fun h' => eβ (h' ▸ h)⟩)
    · rintro (h | h | ⟨h, h'⟩)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr h))
      · rw [hord] at h
        rcases List.mem_append.1 h with h | h
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 h with h | h
          · exact absurd h h'
          · exact Or.inr h
  have mZ : ∀ v, S.lev v ≤ i → j ≤ S.lev v → v ∈ G.int → v ∈ Z.int :=
    fun v h1 h2 h3 => (hZ.int v).2 ⟨h3, h2, h1⟩
  have ma : (G.ends S.e).1 ∈ Z.int := mZ _ (by omega) (by omega) hC.ha
  have mb : (G.ends S.e).2 ∈ Z.int := mZ _ (by omega) (by omega) hC.hb
  have mw : S.w ∈ Z.int := mZ _ (by omega) (by omega) S.hw
  have hpi : ∀ y ∈ α ++ [S.e, S.e'] ++ β, Z.IsIntPlus y := by
    intro y hy
    rcases (memp y).1 hy with rfl | rfl | ⟨h, h'⟩
    · rw [MGraph.IsIntPlus, p1, p2]
      exact ⟨rfl, ma, mw⟩
    · rw [MGraph.IsIntPlus, p3, p4]
      exact ⟨rfl, mw, mb⟩
    · obtain ⟨hpl, a1, a2, b1, b2⟩ := (mem y).1 h
      obtain ⟨z1, z2, -⟩ := F y a1 a2 b1 b2 h' (ne' y h)
      rw [MGraph.IsIntPlus, z1, z2]
      exact ⟨hpl, mZ _ (by omega) (by omega) a1, mZ _ (by omega) (by omega) b1⟩
  refine preDet_prefix hp hpi (steps_dc hp (List.ne_nil_of_mem (a := S.e) (by simp))) ?_
  -- the component `i` and `w` collapsed
  have hvv : (G.ends S.e).1 ∈ S.Lvl i (i + 1) := S.mem_Lvl.2 ⟨hC.ha, by omega, by omega⟩
  have hSS : insert S.w (S.Lvl i (i + 1)) ⊆ (Z.convert (α ++ [S.e, S.e'] ++ β)).int := by
    intro v hv
    rw [convert_int]
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact mZ _ (by omega) (by omega) S.hw
    · obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
      exact mZ _ (by omega) (by omega) h1
  have hBint : B.int = S.Lvl i (i + 1) := by
    ext v; rw [hB.int, S.mem_Lvl]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩⟩
  -- the class of an edge of `G` inside the component `i` after the conversion
  have genc : ∀ f, f ≠ S.e → f ≠ S.e' → (G.ends f).1 ∈ G.int → S.lev (G.ends f).1 = i →
      (G.ends f).2 ∈ G.int → S.lev (G.ends f).2 = i →
      (Z.convert (α ++ [S.e, S.e'] ++ β)).cls f =
        if G.cls f = some .plus then some .diff else G.cls f := by
    intro f h1 h2 a1 a2 b1 b2
    obtain ⟨z1, z2, -⟩ := F f a1 a2 b1 b2 h1 h2
    rw [convert_cls, z2]
    by_cases hpl : G.cls f = some .plus
    · rw [if_pos hpl, if_pos ⟨(memp f).2 (Or.inr (Or.inr ⟨(mem f).2 ⟨hpl, a1, a2, b1, b2⟩, h1⟩)),
        hpl⟩]
    · rw [if_neg hpl, if_neg (fun h => hpl h.2)]
  refine preDet_glue hSS (Finset.mem_insert_self _ _) ?_ ?_
  · -- the component `i` with `w`: doubly connected without blue solid edges
    refine preDet_of_dropPlus ?_ (m := S.allPlus ++ [S.e']) ?_
    · have hR : ((B.convert ℓ).erase S.e).DC := by
        have := MGraph.DC_convert _ _ ((B.convert α).erase S.e) β hre_dc
        rw [convert_erase_convert, ← hord] at this
        exact this
      have hRp : ∀ f, ((B.convert ℓ).erase S.e).Pres f → f ≠ S.e ∧ B.cls f ≠ none ∧
          ((B.convert ℓ).erase S.e).cls f = (B.convert ℓ).cls f := by
        intro f hf
        have hfe : f ≠ S.e := by rintro rfl; exact hf.1 (by rw [erase_cls]; simp)
        have c := hf.1
        rw [erase_cls, if_neg hfe] at c
        exact ⟨hfe, convert_ne_none.1 c, by rw [erase_cls, if_neg hfe]⟩
      have hinS : ∀ v, S.lev v = i → v ∈ G.int → v ∈ insert S.w (S.Lvl i (i + 1)) :=
        fun v h1 h2 => Finset.mem_insert_of_mem (S.mem_Lvl.2 ⟨h2, by omega, by omega⟩)
      have hwS : S.w ∈ insert S.w (S.Lvl i (i + 1)) := Finset.mem_insert_self _ _
      have dpc : ∀ f, (Z.ends f).1 ∈ insert S.w (S.Lvl i (i + 1)) →
          (Z.ends f).2 ∈ insert S.w (S.Lvl i (i + 1)) →
          (Z.convert (α ++ [S.e, S.e'] ++ β)).cls f ≠ some .plus →
          (((Z.convert (α ++ [S.e, S.e'] ++ β)).induce (insert S.w (S.Lvl i (i + 1)))).dropPlus).cls f
            = (Z.convert (α ++ [S.e, S.e'] ++ β)).cls f := by
        intro f h1 h2 h3
        rw [dropPlus_cls]
        simp only [MGraph.induce, convert_ends, h1, h2, and_self, ↓reduceIte, h3]
      have hpe : (Z.convert (α ++ [S.e, S.e'] ++ β)).cls S.e = some .diff := by
        rw [convert_cls, if_pos ⟨by simp, p1⟩]
      have hpe' : (Z.convert (α ++ [S.e, S.e'] ++ β)).cls S.e' = some .diff := by
        rw [convert_cls, if_pos ⟨by simp, p3⟩]
      refine dc_path (R := (B.convert ℓ).erase S.e) (N := S.w) (g := S.e) (g₁ := S.e)
        (g₂ := S.e') (y₁ := S.e) (y₂ := S.e') (m₁ := (G.ends S.e).1) (m₂ := (G.ends S.e).2) hR
        ?_ ?_ (fun hp => absurd hp.1 (by rw [erase_cls]; simp)) ?_
      · rw [dropPlus_int, erase_int, convert_int, hBint]; rfl
      · intro f hf hfe
        obtain ⟨-, hBn, hRc⟩ := hRp f hf
        rcases hB.pres f hBn with ⟨hb, rfl, hc, hen⟩ | ⟨hn, a1, a2, b1, b2, hc, hen⟩
        · obtain ⟨-, t1, -, t2, -, -⟩ := hZ.th hb
          obtain ⟨n1, n2, n3, n4⟩ := hC.x12 hZ hB hb
          obtain ⟨hx₁, hx₂, -⟩ := hB.x12 hb
          obtain ⟨-, -, -, g1, g2, -⟩ := S.cc_ends' hb hx₁
          obtain ⟨-, -, -, g3, g4, -⟩ := S.cc_ends' hb hx₂
          have o1 : S.Gt.outer (S.P (i + 1)) f = G.outer (S.P (i + 1)) f := by
            unfold MGraph.outer; rw [split_ends_ne n1 n2]
          have o2 : S.Gt.outer (S.P (i + 1)) x₂ = G.outer (S.P (i + 1)) x₂ := by
            unfold MGraph.outer; rw [split_ends_ne n3 n4]
          have hZe : Z.ends f = (G.outer (S.P (i + 1)) f, G.outer (S.P (i + 1)) x₂) := by
            rw [t2, o1, o2]
          rw [dpc f (by rw [hZe]; exact hinS _ g2 g1) (by rw [hZe]; exact hinS _ g4 g3)
            (by rw [convert_cls, t1]; simp), hRc, convert_cls, convert_cls, t1, hc]
          refine ⟨Or.inl (by simp), ?_⟩
          rw [dropPlus_ends, erase_ends]
          simp only [MGraph.induce, convert_ends]
          rw [hZe, hen]
          exact sameEnds_refl _
        · have hfe' : f ≠ S.e' := by rintro rfl; exact hBn (by rw [hc, S.ce'])
          obtain ⟨z1, -, -⟩ := F f a1 a2 b1 b2 hfe hfe'
          have hgen := genc f hfe hfe' a1 a2 b1 b2
          have hnp : (Z.convert (α ++ [S.e, S.e'] ++ β)).cls f ≠ some .plus := by
            rw [hgen]; split_ifs with h <;> [simp; exact h]
          rw [dpc f (by rw [z1]; exact hinS _ a2 a1) (by rw [z1]; exact hinS _ b2 b1) hnp, hRc,
            hgen, convert_cls, hc]
          refine ⟨Or.inl ?_, ?_⟩
          · by_cases hpl : G.cls f = some .plus
            · rw [if_pos hpl, if_pos ⟨(mem f).2 ⟨hpl, a1, a2, b1, b2⟩, hpl⟩]
            · rw [if_neg hpl, if_neg (fun h => hpl h.2)]
          · rw [dropPlus_ends, erase_ends]
            simp only [MGraph.induce, convert_ends]
            rw [z1, hen]
            exact sameEnds_refl _
      · intro hwR
        refine ⟨?_, Or.inl ?_, ?_, ?_, ?_, ?_, S.hne, fun f hf _ => ⟨(hRp f hf).1, ?_⟩,
          fun hp => absurd hp.1 (by rw [erase_cls]; simp)⟩
        · rw [dpc _ (by rw [p2]; exact hinS _ hla hC.ha) (by rw [p2]; exact hwS)
            (by rw [hpe]; simp), hpe]
        · rw [dpc _ (by rw [p4]; exact hwS) (by rw [p4]; exact hinS _ hlb hC.hb)
            (by rw [hpe']; simp), hpe']
        · rw [dropPlus_ends]; simp only [MGraph.induce, convert_ends]; rw [p2]; exact Or.inr rfl
        · rw [dropPlus_ends]; simp only [MGraph.induce, convert_ends]; rw [p4]; exact Or.inl rfl
        · rw [erase_int, convert_int, hB.int]; exact ⟨hC.ha, hla⟩
        · rw [erase_int, convert_int, hB.int]; exact ⟨hC.hb, hlb⟩
        · rintro rfl
          obtain ⟨-, hBn, -⟩ := hRp _ hf
          rcases hB.pres _ hBn with ⟨hb, h', -⟩ | ⟨-, -, -, -, -, h', -⟩
          · exact (hC.x12 hZ hB hb).2.1 h'.symm
          · exact hBn (by rw [h', S.ce'])
    · intro x hx
      obtain ⟨h1, -, -⟩ := hx
      have hin : (Z.ends x).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
          (Z.ends x).2 ∈ insert S.w (S.Lvl i (i + 1)) := by
        by_contra hn
        have h0 : ((Z.convert (α ++ [S.e, S.e'] ++ β)).induce
            (insert S.w (S.Lvl i (i + 1)))).cls x = none := by
          simp only [MGraph.induce, convert_ends]; exact if_neg hn
        rw [h0] at h1; cases h1
      have h1' : (Z.convert (α ++ [S.e, S.e'] ++ β)).cls x = some .plus := by
        have h0 : ((Z.convert (α ++ [S.e, S.e'] ++ β)).induce
            (insert S.w (S.Lvl i (i + 1)))).cls x = (Z.convert (α ++ [S.e, S.e'] ++ β)).cls x := by
          simp only [MGraph.induce, convert_ends]; exact if_pos hin
        rw [← h0]; exact h1
      clear h1
      have h1 := h1'
      have hz : Z.cls x = some .plus := by
        rw [convert_cls] at h1
        split_ifs at h1 with h
        · exact h.2
        · exact h1
      have hn : i < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
        intro hb
        obtain ⟨-, t1, t2, -⟩ := hZ.th hb
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [h, t1] at hz; cases hz
        · rw [h, t2] at hz; cases hz
      obtain ⟨g1, g2⟩ := hZ.gen x hn
      rw [hz] at g2
      split_ifs at g2 with hg
      by_cases hxe' : x = S.e'
      · simp [hxe']
      · rw [split_cls_ne hxe'] at g2
        refine List.mem_append_left _ (mem_allPlus g2.symm ?_ ?_)
        · by_cases hxe : x = S.e
          · rw [hxe]; exact hC.ha
          · rw [split_ends_ne hxe hxe'] at hg; exact ((hZ.int _).1 hg.1).1
        · by_cases hxe : x = S.e
          · rw [hxe]; exact hC.hb
          · rw [split_ends_ne hxe hxe'] at hg; exact ((hZ.int _).1 hg.2).1
  · -- the graph of [II, Lemma 5.11] collapsed
    have trivQ : ∀ x, (Z.convert (α ++ [S.e, S.e'] ++ β)).cls x = none ∨
        ((Z.convert (α ++ [S.e, S.e'] ++ β)).cls x = some .diff ∧
          (Z.ends x).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
          (Z.ends x).2 ∈ insert S.w (S.Lvl i (i + 1))) →
        ¬ ((Z.convert (α ++ [S.e, S.e'] ++ β)).collapse (insert S.w (S.Lvl i (i + 1))) S.w).Pres x ∧
        ¬ ((Z.convert (α ++ [S.e, S.e'] ++ β)).collapse (insert S.w (S.Lvl i (i + 1))) S.w).IsIntPlus
          x := by
      intro x h
      rcases h with h | ⟨h, a, b⟩
      · exact ⟨fun h' => h'.1 h, fun h' => by have := h'.1; rw [collapse_cls, h] at this; cases this⟩
      · refine ⟨fun h' => h'.2.2.2 ?_, fun h' => by
          have := h'.1; rw [collapse_cls, h] at this; cases this⟩
        rw [collapse_convert_ends, if_pos a, if_pos b]
    refine Qtop hZ hji hik hlw hC.ha hla (fun hb => ?_) (fun f hfe hfe' _ hpl a1 _ _ b1 _ _ => ?_)
      (fun _ => ⟨hC.ha, hla, hC.hb, hlb⟩) (fun x hx => trivQ x ?_)
    · obtain ⟨h1, h2, -⟩ := hB.x12 hb
      exact ⟨h1.elim Or.inl (fun h => Or.inr (Or.inl h)), h2.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    · rw [memp, mem]
      constructor
      · rintro (h | h | ⟨⟨-, -, h1, -, h2⟩, -⟩)
        · exact absurd h hfe
        · exact absurd h hfe'
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact Or.inr (Or.inr ⟨⟨hpl, a1, h1, b1, h2⟩, hfe⟩)
    · have hinS : ∀ v, S.lev v = i → v ∈ G.int → v ∈ insert S.w (S.Lvl i (i + 1)) :=
        fun v h1 h2 => Finset.mem_insert_of_mem (S.mem_Lvl.2 ⟨h2, by omega, by omega⟩)
      have hwS : S.w ∈ insert S.w (S.Lvl i (i + 1)) := Finset.mem_insert_self _ _
      rcases hx with rfl | rfl | ⟨hb, hx⟩
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · rw [convert_cls, if_pos ⟨by simp, p1⟩]
        · rw [p2]; exact hinS _ hla hC.ha
        · rw [p2]; exact hwS
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · rw [convert_cls, if_pos ⟨by simp, p3⟩]
        · rw [p4]; exact hwS
        · rw [p4]; exact hinS _ hlb hC.hb
      · obtain ⟨-, t1, t2, t3, -, -⟩ := hZ.th hb
        obtain ⟨h1, h2, hne⟩ := hB.x12 hb
        obtain ⟨n1, n2, n3, n4⟩ := hC.x12 hZ hB hb
        have hxx : x = x₁ ∨ x = x₂ := by
          rcases hx with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          all_goals first
            | exact Or.inl h1.symm
            | exact Or.inr h2.symm
            | exact absurd (h1.trans h2.symm) hne
        rcases hxx with rfl | rfl
        · refine Or.inr ⟨by rw [convert_cls, t1]; simp, ?_, ?_⟩ <;> rw [t3]
          · obtain ⟨-, -, -, g1, g2, -⟩ := S.cc_ends' hb h1
            have : S.Gt.outer (S.P (i + 1)) x = G.outer (S.P (i + 1)) x := by
              unfold MGraph.outer; rw [split_ends_ne n1 n2]
            rw [this]; exact hinS _ g2 g1
          · obtain ⟨-, -, -, g1, g2, -⟩ := S.cc_ends' hb h2
            have : S.Gt.outer (S.P (i + 1)) x₂ = G.outer (S.P (i + 1)) x₂ := by
              unfold MGraph.outer; rw [split_ends_ne n3 n4]
            rw [this]; exact hinS _ g2 g1
        · exact Or.inl (by rw [convert_cls, t2]; simp)

end CaseII

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-! ### Case (iv) of [II, Lemma 5.12] -/

/-- The setting of case (iv) of [II, Lemma 5.12]: `e` joins `p` (component `i`) to `q` (component
`i + 1`), `w` lies in the component `j < i`; after the operation `y` joins `p` to `w` and `z` joins
`w` to `q`. -/
structure CaseIV (S : SC G) (j i : ℕ) (y z : E) (p q : V) : Prop where
  hji : j < i
  hik : i < S.k
  hyz : (y = S.e ∧ z = S.e') ∨ (y = S.e' ∧ z = S.e)
  hp : p ∈ G.int
  hlp : S.lev p = i
  hq : q ∈ G.int
  hlq : S.lev q = i + 1
  hy : SameEnds (S.Gt.ends y) (p, S.w)
  hz : SameEnds (S.Gt.ends z) (S.w, q)
  hev : SameEnds (G.ends S.e) (p, q)
  hlw : S.lev S.w = j

section CaseIV

variable {j i : ℕ} {y z : E} {p q : V} (hC : S.CaseIV j i y z p q)
include hC

/-- In case (iv), `e` is the crossing edge `cc' i` of `G`. -/
private theorem CaseIV.e_eq : S.e = S.cc' i := by
  have hik := hC.hik
  have hlp := hC.hlp
  have hlq := hC.hlq
  have hc : G.Crosses (S.P (i + 1)) S.e := by
    refine ⟨by rw [S.ce]; simp, by rw [S.ce]; simp, ?_, ?_, ?_⟩
    · rcases sameEnds_iff.1 hC.hev with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      exacts [Or.inl hC.hp, Or.inl hC.hq]
    · rcases sameEnds_iff.1 hC.hev with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
      exacts [Or.inl hC.hq, Or.inl hC.hp]
    · have hpP : p ∉ S.P (i + 1) := fun h => by have := ((S.mem_P hik _).1 h).2; omega
      have hqP : q ∈ S.P (i + 1) := (S.mem_P hik _).2 ⟨hC.hq, by omega⟩
      rcases sameEnds_iff.1 hC.hev with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [MGraph.Cut, h1, h2] <;> dsimp only
      · exact Or.inr ⟨hpP, hqP⟩
      · exact Or.inl ⟨hqP, hpP⟩
  rcases (S.cross i hik S.e).1 hc with h | h
  · exact absurd h (S.e_ne_cc hik)
  · exact h

private theorem CaseIV.y_cls : S.Gt.cls y = some .plus ∧ S.Gt.cls z = some .plus := by
  rcases hC.hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by rw [split_cls_of S.hne, S.ce], by rw [split_cls_e', S.ce]⟩
  · exact ⟨by rw [split_cls_e', S.ce], by rw [split_cls_of S.hne, S.ce]⟩

private theorem CaseIV.yz_ne : y ≠ z ∧ (∀ x, x = y ∨ x = z ↔ x = S.e ∨ x = S.e') := by
  rcases hC.hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨S.hne, fun x => Iff.rfl⟩
  · exact ⟨S.hne.symm, fun x => or_comm⟩

/-- The crossing edges of `P (i + 1)` after the operation: `cc i` and `z`. -/
private theorem CaseIV.cross (x : E) : S.Gt.Crosses (S.P (i + 1)) x ↔ x = S.cc i ∨ x = z := by
  have hik := hC.hik
  have hlp := hC.hlp
  have hlq := hC.hlq
  have hlw := hC.hlw
  have hji := hC.hji
  have hpP : p ∉ S.P (i + 1) := fun h => by have := ((S.mem_P hik _).1 h).2; omega
  have hqP : q ∈ S.P (i + 1) := (S.mem_P hik _).2 ⟨hC.hq, by omega⟩
  have hwP : S.w ∉ S.P (i + 1) := fun h => by have := ((S.mem_P hik _).1 h).2; omega
  obtain ⟨yc, zc⟩ := hC.y_cls
  obtain ⟨hyz, hmem⟩ := hC.yz_ne
  constructor
  · intro hx
    by_cases hxy : x = y ∨ x = z
    · rcases hxy with rfl | rfl
      · exfalso
        obtain ⟨-, -, -, -, hcut⟩ := hx
        unfold MGraph.Cut at hcut
        rcases sameEnds_iff.1 hC.hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hcut <;>
          dsimp only at hcut <;> tauto
      · exact Or.inr rfl
    · rw [not_or] at hxy
      have hxe : x ≠ S.e ∧ x ≠ S.e' := by
        constructor <;> intro h <;> exact (hmem x).2 (by tauto) |>.elim hxy.1 hxy.2
      rcases (S.cross i hik x).1 ((split_crosses_ne hxe.1 hxe.2).1 hx) with h | h
      · exact Or.inl h
      · exact absurd (h.trans hC.e_eq.symm) hxe.1
  · rintro (rfl | rfl)
    · have hne : S.cc i ≠ S.e ∧ S.cc i ≠ S.e' :=
        ⟨(S.e_ne_cc hik).symm, (S.e'_ne_cc hik).symm⟩
      exact (split_crosses_ne hne.1 hne.2).2 ((S.cross i hik _).2 (Or.inl rfl))
    · refine ⟨by rw [zc]; simp, by rw [zc]; simp, ?_, ?_, ?_⟩
      · rcases sameEnds_iff.1 hC.hz with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
        exacts [Or.inl S.hw, Or.inl hC.hq]
      · rcases sameEnds_iff.1 hC.hz with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
        exacts [Or.inl hC.hq, Or.inl S.hw]
      · unfold MGraph.Cut
        rcases sameEnds_iff.1 hC.hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> dsimp only
        · exact Or.inr ⟨hwP, hqP⟩
        · exact Or.inl ⟨hqP, hwP⟩

variable {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z j i x₁ x₂)
  (hx12 : (x₁ = S.cc i ∧ x₂ = z) ∨ (x₁ = z ∧ x₂ = S.cc i))
include hZ hx12

/-- The facts on the graph of case (iv): the edges of `G` inside the component `i`, the edge `y`
from `p` to `w`, the `Θ` edge `x₁` between `w` and the outer end of `cc i`, and the crossing edges
of `P i`. -/
private theorem CaseIV.facts :
    (∀ f, G.cls f ≠ none → (G.ends f).1 ∈ G.int → S.lev (G.ends f).1 = i →
      (G.ends f).2 ∈ G.int → S.lev (G.ends f).2 = i → f ≠ S.e ∧ f ≠ S.e' ∧ f ≠ S.cc i ∧ f ≠ y ∧
      f ≠ z ∧ Z.ends f = G.ends f ∧ Z.cls f = G.cls f) ∧
    Z.cls y = some .plus ∧ SameEnds (Z.ends y) (p, S.w) ∧
    Z.cls x₁ = some .diff ∧ SameEnds (Z.ends x₁) (S.u i, S.w) ∧ Z.cls x₂ = none ∧
    G.outer (S.P (i + 1)) (S.cc' i) = p ∧
    y ≠ S.cc i ∧ y ≠ x₁ ∧ y ≠ x₂ ∧
    (∀ x, (x = S.cc (i - 1) ∨ x = S.cc' (i - 1)) → x ≠ S.e ∧ x ≠ S.e' ∧ x ≠ S.cc i ∧
      x ≠ x₁ ∧ x ≠ x₂ ∧ Z.ends x = G.ends x ∧ Z.cls x = G.cls x) := by
  have hji := hC.hji
  have hik := hC.hik
  have hlp := hC.hlp
  have hlq := hC.hlq
  have hlw := hC.hlw
  have hi1 : i - 1 < S.k := by omega
  have he := hC.e_eq
  obtain ⟨yc, zc⟩ := hC.y_cls
  obtain ⟨hyz, hmem⟩ := hC.yz_ne
  have hyne : y ≠ S.cc i := fun h => by
    rcases hC.hyz with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact S.e_ne_cc hik h
    · exact S.e'_ne_cc hik h
  have hzne : z ≠ S.cc i := fun h => by
    rcases hC.hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact S.e'_ne_cc hik h
    · exact S.e_ne_cc hik h
  obtain ⟨n12, t1, t2, t3, -, -⟩ := hZ.th hik
  have hyx : y ≠ x₁ ∧ y ≠ x₂ := by
    rcases hx12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hyne, hyz⟩
    · exact ⟨hyz, hyne⟩
  -- the outer ends
  have hwP : S.w ∉ S.P (i + 1) := fun h => by have := ((S.mem_P hik _).1 h).2; omega
  have hqP : q ∈ S.P (i + 1) := (S.mem_P hik _).2 ⟨hC.hq, by omega⟩
  have hpP : p ∉ S.P (i + 1) := fun h => by have := ((S.mem_P hik _).1 h).2; omega
  have oz : S.Gt.outer (S.P (i + 1)) z = S.w := by
    unfold MGraph.outer
    rcases sameEnds_iff.1 hC.hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · simp [hwP]
    · simp [hqP]
  have oc : S.Gt.outer (S.P (i + 1)) (S.cc i) = S.u i := by
    unfold MGraph.outer; rw [split_ends_ne (S.e_ne_cc hik).symm (S.e'_ne_cc hik).symm]; rfl
  have oe : G.outer (S.P (i + 1)) (S.cc' i) = p := by
    rw [← he]; unfold MGraph.outer
    rcases sameEnds_iff.1 hC.hev with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · simp [hpP]
    · simp [hqP]
  -- the edge `y`
  have hyZ : Z.ends y = S.Gt.ends y ∧ Z.cls y = S.Gt.cls y := by
    have hp : (S.Gt.ends y).1 ∈ G.int ∧ j ≤ S.lev (S.Gt.ends y).1 ∧ S.lev (S.Gt.ends y).1 ≤ i ∧
        (S.Gt.ends y).2 ∈ G.int ∧ j ≤ S.lev (S.Gt.ends y).2 ∧ S.lev (S.Gt.ends y).2 ≤ i := by
      rcases sameEnds_iff.1 hC.hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> dsimp only
      · exact ⟨hC.hp, by omega, by omega, S.hw, by omega, by omega⟩
      · exact ⟨S.hw, by omega, by omega, hC.hp, by omega, by omega⟩
    obtain ⟨a1, a2, a3, b1, b2, b3⟩ := hp
    exact hZ.gedge a1 a2 a3 b1 b2 b3
  refine ⟨fun f hf a1 a2 b1 b2 => ?_, hyZ.2.trans yc, hyZ.1 ▸ hC.hy, t1, ?_, t2, oe, hyne, hyx.1,
    hyx.2, fun x hx => ?_⟩
  · have hfe : f ≠ S.e := by
      rintro rfl; rw [he] at a2 b2
      obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hik (Or.inr rfl); omega
    have hfe' : f ≠ S.e' := by rintro rfl; exact hf S.ce'
    have hfc : f ≠ S.cc i := by
      rintro rfl; obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hik (Or.inl rfl); omega
    have hfyz : f ≠ y ∧ f ≠ z := by
      constructor <;> intro h <;> rcases (hmem f).1 (by tauto) with h' | h'
      all_goals first | exact hfe h' | exact hfe' h'
    obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1 (by omega) (by omega) b1 (by omega) (by omega)
    exact ⟨hfe, hfe', hfc, hfyz.1, hfyz.2, z1, z2⟩
  · rw [t3]
    rcases hx12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [oc, oz]; exact Or.inl rfl
    · rw [oz, oc]; exact Or.inr rfl
  · obtain ⟨g1, g2, g3⟩ := S.toSplitCtx.cc_lev hi1 hx
    have hxe : x ≠ S.e := by
      rintro rfl; rw [he] at hx; have := S.cc_inj hi1 hik hx (Or.inr rfl); omega
    have hxe' : x ≠ S.e' := by
      rcases hx with rfl | rfl
      · exact (S.e'_ne_cc hi1).symm
      · exact (S.e'_ne_cc' hi1).symm
    have hxc : x ≠ S.cc i := by
      rintro rfl; have := S.cc_inj hi1 hik hx (Or.inl rfl); omega
    have hxz : x ≠ z := fun h => by
      rcases (hmem x).1 (Or.inr h) with h' | h'
      · exact hxe h'
      · exact hxe' h'
    have hx12' : x ≠ x₁ ∧ x ≠ x₂ := by
      rcases hx12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hxc, hxz⟩
      · exact ⟨hxz, hxc⟩
    obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' g1 (by omega) (by omega) g2 (by omega) (by omega)
    exact ⟨hxe, hxe', hxc, hx12'.1, hx12'.2, z1, z2⟩

/-- The step of `y` in case (iv): the graph is doubly connected without `y`
([II, Claim A.1]). -/
private theorem CaseIV.stepY : Z.IsRedundant y := by
  have hji := hC.hji
  have hik := hC.hik
  have hlp := hC.hlp
  have hlq := hC.hlq
  have hlw := hC.hlw
  have hi1 : i - 1 < S.k := by omega
  obtain ⟨F, yc, ye, -, -, -, -, -, -, -, X⟩ := hC.facts hZ hx12
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := X _ (Or.inl rfl)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := X _ (Or.inr rfl)
  have hyc : y ≠ S.cc (i - 1) ∧ y ≠ S.cc' (i - 1) := by
    constructor <;> intro h <;> rcases (hC.yz_ne.2 y).1 (Or.inl rfl) with h' | h'
    · exact c1 (h.symm.trans h')
    · exact c2 (h.symm.trans h')
    · exact d1 (h.symm.trans h')
    · exact d2 (h.symm.trans h')
  have hpU : p ∉ S.Lvl j i := fun h => by have := (S.mem_Lvl.1 h).2.2; omega
  have he : ¬ ((G.ends S.e).1 ∈ S.Lvl j i ∧ (G.ends S.e).2 ∈ S.Lvl j i) := by
    rintro ⟨h1, h2⟩
    rcases sameEnds_iff.1 hC.hev with ⟨e1, -⟩ | ⟨-, e2⟩
    · rw [e1] at h1; exact hpU h1
    · rw [e2] at h2; exact hpU h2
  have hyU : ¬ ((Z.ends y).1 ∈ S.Lvl j i ∧ (Z.ends y).2 ∈ S.Lvl j i) := by
    rcases sameEnds_iff.1 ye with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> dsimp only
    · exact fun h => hpU h.1
    · exact fun h => hpU h.2
  have hRi : ∀ v, v ∈ (G.induce (S.Lvl i (i + 1))).int ↔ v ∈ G.int ∧ S.lev v = i := by
    intro v; change v ∈ S.Lvl i (i + 1) ↔ _; rw [S.mem_Lvl]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
  have hRp : ∀ f, (G.induce (S.Lvl i (i + 1))).Pres f → G.cls f ≠ none ∧ (G.ends f).1 ∈ G.int ∧
      S.lev (G.ends f).1 = i ∧ (G.ends f).2 ∈ G.int ∧ S.lev (G.ends f).2 = i ∧
      (G.induce (S.Lvl i (i + 1))).cls f = G.cls f := by
    intro f hf
    have hin : (G.ends f).1 ∈ S.Lvl i (i + 1) ∧ (G.ends f).2 ∈ S.Lvl i (i + 1) := by
      by_contra hn; exact hf.1 (by simp [MGraph.induce, hn])
    obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
    obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
    have hc : (G.induce (S.Lvl i (i + 1))).cls f = G.cls f := by simp [MGraph.induce, hin]
    exact ⟨hc ▸ hf.1, a1, by omega, b1, by omega, hc⟩
  have hnP : ¬ (G.induce (S.Lvl i (i + 1))).Pres y := fun hp => by
    obtain ⟨hc, a1, a2, b1, b2, -⟩ := hRp y hp
    obtain ⟨h1, -⟩ := F y hc a1 a2 b1 b2
    obtain ⟨-, -, -, h, -⟩ := F y hc a1 a2 b1 b2
    exact h rfl
  have hdc := S.toSplitCtx.dc_Lvl (i + 1) (a := i) (by omega)
  have key : ∀ Y : MGraph V E, Y.int = Z.int → Y.ends = Z.ends →
      (∀ f, f ≠ y → Y.cls f = Z.cls f) → (Y.collapse (S.Lvl j i) S.w).DC := by
    intro Y hYi hYe hYc
    refine pathU hZ hji hik.le hlw hYi hdc hRi (g := y) (g₁ := y) (g₂ := y) hyc
      (fun f hf hfy => ?_) (fun hp => absurd hp hnP) ?_
    · obtain ⟨hc, a1, a2, b1, b2, hcl⟩ := hRp f hf
      obtain ⟨-, -, -, -, -, z1, z2⟩ := F f hc a1 a2 b1 b2
      rw [hYc f hfy, z2, hcl, hYe, z1]
      exact ⟨Or.inl rfl, sameEnds_refl _⟩
    · rw [hYc _ (Ne.symm hyc.1), hYc _ (Ne.symm hyc.2), hYe, c7, d7, c6, d6, S.cc_diff _ hi1]
      exact ⟨rfl, S.cc'_cls _ hi1, rfl, rfl⟩
  have := hZ.stepU hji hik.le hlw he (l := []) hyU (by rw [convert_nil']; exact yc)
    (key _ rfl rfl (fun f _ => by rw [convert_nil']))
    (key _ rfl rfl (fun f hf => by rw [erase_cls, if_neg hf, convert_nil']))
  rwa [convert_nil'] at this

/-- A redundancy step of the component `i` in case (iv), after `y`: [II, Claim A.2] for the `Θ`
edge `x₁'` of the graph of the component replaced by the path through `w`. -/
private theorem CaseIV.stepB {x₁' x₂' : E}
    (hx' : (x₁ = S.cc i ∧ x₁' = S.cc i ∧ x₂' = S.cc' i) ∨ (x₁ = z ∧ x₁' = S.cc' i ∧ x₂' = S.cc i))
    {m : List E} {x : E}
    (hr : ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).IsRedundant x)
    (hxp : G.cls x = some .plus) (a1 : (G.ends x).1 ∈ G.int) (a2 : S.lev (G.ends x).1 = i)
    (b1 : (G.ends x).2 ∈ G.int) (b2 : S.lev (G.ends x).2 = i) (hxm : x ∉ m) :
    (Z.convert (y :: m)).IsRedundant x := by
  have hji := hC.hji
  have hik := hC.hik
  have hlp := hC.hlp
  have hlw := hC.hlw
  have hi1 : i - 1 < S.k := by omega
  obtain ⟨F, yc, ye, t1, t1e, -, oe, hyne, hyx1, -, X⟩ := hC.facts hZ hx12
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := X _ (Or.inl rfl)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := X _ (Or.inr rfl)
  obtain ⟨xe, xe', xc, xy, xz, zx1, zx2⟩ := F x (by rw [hxp]; simp) a1 a2 b1 b2
  have hx₁' : x₁' = S.cc i ∨ x₁' = S.cc' i := by
    rcases hx' with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hx₂' : x₂' = S.cc i ∨ x₂' = S.cc' i := by
    rcases hx' with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hne' : x₁' ≠ x₂' := by
    rcases hx' with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2]
    · exact S.cc_ne i hik
    · exact (S.cc_ne i hik).symm
  have hB := S.isB_replace hik hx₁' hx₂' hne'
  have hpU : p ∉ S.Lvl j i := fun h => by have := (S.mem_Lvl.1 h).2.2; omega
  have he : ¬ ((G.ends S.e).1 ∈ S.Lvl j i ∧ (G.ends S.e).2 ∈ S.Lvl j i) := by
    rintro ⟨h1, h2⟩
    rcases sameEnds_iff.1 hC.hev with ⟨e1, -⟩ | ⟨-, e2⟩
    · rw [e1] at h1; exact hpU h1
    · rw [e2] at h2; exact hpU h2
  have hxU : ¬ ((Z.ends x).1 ∈ S.Lvl j i ∧ (Z.ends x).2 ∈ S.Lvl j i) := by
    rw [zx1]; exact fun h => by have := (S.mem_Lvl.1 h.1).2.2; omega
  have hxg : x ≠ x₁' := by
    rintro rfl; obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hik hx₁'; omega
  have hxcc : x ≠ S.cc (i - 1) ∧ x ≠ S.cc' (i - 1) := by
    constructor <;> rintro rfl
    · obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hi1 (Or.inl rfl); omega
    · obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hi1 (Or.inr rfl); omega
  have hgc : x₁' ≠ S.cc (i - 1) ∧ x₁' ≠ S.cc' (i - 1) := by
    constructor <;> intro h
    · have := S.cc_inj hik hi1 hx₁' (Or.inl h); omega
    · have := S.cc_inj hik hi1 hx₁' (Or.inr h); omega
  have hBint := (S.isB_replace hik hx₁' hx₂' hne').int
  have hRi : ∀ v, v ∈ ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).int ↔
      v ∈ G.int ∧ S.lev v = i := fun v => by rw [convert_int]; exact hBint v
  have hyl : y ∈ y :: m := List.mem_cons_self
  have hYy : (Z.convert (y :: m)).cls y = some .diff := by rw [convert_cls, if_pos ⟨hyl, yc⟩]
  have hYc : ∀ f, f ≠ y → (Z.convert (y :: m)).cls f = (Z.convert m).cls f := by
    intro f hf; rw [convert_cls, convert_cls]; simp [hf]
  -- the hypotheses of `pathU`
  have hRx₁ : ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).cls x₁' = some .diff ∧
      ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).ends x₁' =
        (G.outer (S.P (i + 1)) x₁', G.outer (S.P (i + 1)) x₂') := by
    refine ⟨?_, by simp [MGraph.replace, MGraph.convert]⟩
    rw [convert_cls]; simp [MGraph.replace]
  have H1 : ∀ f, ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).Pres f → f ≠ x₁' →
      ((Z.convert (y :: m)).cls f = ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).cls f ∨
        (((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).cls f = some .plus ∧
          (Z.convert (y :: m)).cls f = some .diff)) ∧
      SameEnds ((Z.convert (y :: m)).ends f)
        (((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).ends f) := by
    intro f hf hfg
    rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨-, h, -⟩ | ⟨hn, f1, f2, f3, f4, hc, hen⟩
    · exact absurd h hfg
    · obtain ⟨-, -, -, hfy, -, z1, z2⟩ := F f (by rw [← hc]; exact convert_ne_none.1 hf.1) f1 f2
        f3 f4
      rw [hYc f hfy, convert_cls, convert_cls, z2, hc, convert_ends, convert_ends, z1, hen]
      exact ⟨Or.inl rfl, sameEnds_refl _⟩
  have H3 : (Z.convert (y :: m)).cls (S.cc (i - 1)) = some .diff ∧
      ((Z.convert (y :: m)).cls (S.cc' (i - 1)) = some .diff ∨
        (Z.convert (y :: m)).cls (S.cc' (i - 1)) = some .plus) ∧
      (Z.convert (y :: m)).ends (S.cc (i - 1)) = G.ends (S.cc (i - 1)) ∧
      (Z.convert (y :: m)).ends (S.cc' (i - 1)) = G.ends (S.cc' (i - 1)) := by
    have ycc : y ≠ S.cc (i - 1) ∧ y ≠ S.cc' (i - 1) := by
      constructor <;> intro h <;> rcases (hC.yz_ne.2 y).1 (Or.inl rfl) with h' | h'
      · exact c1 (h.symm.trans h')
      · exact c2 (h.symm.trans h')
      · exact d1 (h.symm.trans h')
      · exact d2 (h.symm.trans h')
    rw [hYc _ (Ne.symm ycc.1), hYc _ (Ne.symm ycc.2), convert_cls, convert_cls, convert_ends,
      c7, d7, c6, d6, S.cc_diff _ hi1]
    refine ⟨by simp, ?_, rfl, rfl⟩
    rcases S.cc'_cls _ hi1 with h | h <;> rw [h] <;> split_ifs <;> simp
  have ycc : y ≠ S.cc (i - 1) ∧ y ≠ S.cc' (i - 1) := by
    constructor <;> intro h <;> rcases (hC.yz_ne.2 y).1 (Or.inl rfl) with h' | h'
    · exact c1 (h.symm.trans h')
    · exact c2 (h.symm.trans h')
    · exact d1 (h.symm.trans h')
    · exact d2 (h.symm.trans h')
  have zcc : z ≠ S.cc (i - 1) ∧ z ≠ S.cc' (i - 1) := by
    constructor <;> intro h <;> rcases (hC.yz_ne.2 z).1 (Or.inr rfl) with h' | h'
    · exact c1 (h.symm.trans h')
    · exact c2 (h.symm.trans h')
    · exact d1 (h.symm.trans h')
    · exact d2 (h.symm.trans h')
  have hRpres : ∀ f, ((G.replace (S.P i) (S.P (i + 1)) x₁' x₂').convert m).Pres f → f ≠ x₁' →
      f ≠ S.cc i ∧ f ≠ y ∧ f ≠ z := by
    intro f hf hfg
    rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨-, h, -⟩ | ⟨hn, f1, f2, f3, f4, hc, -⟩
    · exact absurd h hfg
    · obtain ⟨-, -, hfc, hfy, hfz, -, -⟩ := F f (by rw [← hc]; exact convert_ne_none.1 hf.1) f1 f2
        f3 f4
      exact ⟨hfc, hfy, hfz⟩
  have hYx₁ : (Z.convert (y :: m)).cls x₁ = some .diff := by
    rw [hYc _ (Ne.symm hyx1), convert_cls, t1]; simp
  rcases hx' with ⟨hx1, rfl, rfl⟩ | ⟨hx1, rfl, rfl⟩
  · -- the `Θ` edge `cc i`: the path `cc i`, `y` through `w`
    subst hx1
    have H2 : ((G.replace (S.P i) (S.P (i + 1)) (S.cc i) (S.cc' i)).convert m).Pres (S.cc i) →
        (Z.convert (y :: m)).cls (S.cc i) =
          ((G.replace (S.P i) (S.P (i + 1)) (S.cc i) (S.cc' i)).convert m).cls (S.cc i) ∧
        (Z.convert (y :: m)).cls y =
          ((G.replace (S.P i) (S.P (i + 1)) (S.cc i) (S.cc' i)).convert m).cls (S.cc i) ∧
        SameEnds ((Z.convert (y :: m)).ends (S.cc i))
          ((((G.replace (S.P i) (S.P (i + 1)) (S.cc i) (S.cc' i)).convert m).ends (S.cc i)).1,
            S.w) ∧
        SameEnds ((Z.convert (y :: m)).ends y)
          (S.w, (((G.replace (S.P i) (S.P (i + 1)) (S.cc i) (S.cc' i)).convert m).ends
            (S.cc i)).2) ∧
        (∀ f, ((G.replace (S.P i) (S.P (i + 1)) (S.cc i) (S.cc' i)).convert m).Pres f →
          f ≠ S.cc i → f ≠ S.cc i ∧ f ≠ y) ∧
        S.cc i ≠ S.cc (i - 1) ∧ y ≠ S.cc (i - 1) ∧ S.cc i ≠ S.cc' (i - 1) ∧
        y ≠ S.cc' (i - 1) := by
      intro _
      refine ⟨by rw [hYx₁, hRx₁.1], by rw [hYy, hRx₁.1], ?_, ?_,
        fun f hf hfg => ⟨hfg, (hRpres f hf hfg).2.1⟩, hgc.1, ycc.1, hgc.2, ycc.2⟩
      · rw [convert_ends, hRx₁.2]; exact t1e
      · rw [convert_ends, hRx₁.2, oe]; exact ye.trans (Or.inr rfl)
    refine hZ.stepU hji hik.le hlw he hxU (by rw [convert_cls_of_not_mem (by simp [xy, hxm]), zx2,
      hxp]) (pathU hZ hji hik.le hlw rfl hr.2.1 hRi hgc H1 H2 H3) ?_
    obtain ⟨h1', h2', h3'⟩ := pathU_erase H1 H2 H3 hxg xc xy hxcc.1 hxcc.2
    exact pathU hZ hji hik.le hlw rfl hr.2.2 (fun v => by rw [erase_int]; exact hRi v) hgc h1' h2'
      h3'
  · -- the `Θ` edge `cc' i = e`: the path `y`, `z` through `w`
    rw [hx1] at hYx₁ t1e
    have H2 : ((G.replace (S.P i) (S.P (i + 1)) (S.cc' i) (S.cc i)).convert m).Pres (S.cc' i) →
        (Z.convert (y :: m)).cls y =
          ((G.replace (S.P i) (S.P (i + 1)) (S.cc' i) (S.cc i)).convert m).cls (S.cc' i) ∧
        (Z.convert (y :: m)).cls z =
          ((G.replace (S.P i) (S.P (i + 1)) (S.cc' i) (S.cc i)).convert m).cls (S.cc' i) ∧
        SameEnds ((Z.convert (y :: m)).ends y)
          ((((G.replace (S.P i) (S.P (i + 1)) (S.cc' i) (S.cc i)).convert m).ends (S.cc' i)).1,
            S.w) ∧
        SameEnds ((Z.convert (y :: m)).ends z)
          (S.w, (((G.replace (S.P i) (S.P (i + 1)) (S.cc' i) (S.cc i)).convert m).ends
            (S.cc' i)).2) ∧
        (∀ f, ((G.replace (S.P i) (S.P (i + 1)) (S.cc' i) (S.cc i)).convert m).Pres f →
          f ≠ S.cc' i → f ≠ y ∧ f ≠ z) ∧
        y ≠ S.cc (i - 1) ∧ z ≠ S.cc (i - 1) ∧ y ≠ S.cc' (i - 1) ∧ z ≠ S.cc' (i - 1) := by
      intro _
      refine ⟨by rw [hYy, hRx₁.1], by rw [hYx₁, hRx₁.1], ?_, ?_,
        fun f hf hfg => ⟨(hRpres f hf hfg).2.1, (hRpres f hf hfg).2.2⟩, ycc.1, zcc.1, ycc.2, zcc.2⟩
      · rw [convert_ends, hRx₁.2, oe]; exact ye
      · rw [convert_ends, hRx₁.2]; exact t1e.trans (sameEnds_swap (S.w, S.u i))
    refine hZ.stepU hji hik.le hlw he hxU (by rw [convert_cls_of_not_mem (by simp [xy, hxm]), zx2,
      hxp]) (pathU hZ hji hik.le hlw rfl hr.2.1 hRi hgc H1 H2 H3) ?_
    obtain ⟨h1', h2', h3'⟩ := pathU_erase H1 H2 H3 hxg xy xz hxcc.1 hxcc.2
    exact pathU hZ hji hik.le hlw rfl hr.2.2 (fun v => by rw [erase_int]; exact hRi v) hgc h1' h2'
      h3'

/-- **Case (iv) of [II, Lemma 5.12]**: the graph after operation (B) on the components `j, …, i`,
with `e` joining the components `i` and `i + 1` and `w` in the component `j < i`, is
pre-deterministic: `y` first, then the component `i` with its `Θ` edge replaced by the path through
`w`; then the component `i` and `w` collapsed give the graph of [II, Lemma 5.11]. -/
private theorem CaseIV.preDet : Z.PreDet := by
  have hji := hC.hji
  have hik := hC.hik
  have hlp := hC.hlp
  have hlw := hC.hlw
  obtain ⟨F, yc, ye, t1, t1e, t2, oe, hyne, hyx1, hyx2, X⟩ := hC.facts hZ hx12
  -- the graph of the component `i` with the `Θ` edge `x₁'`
  obtain ⟨x₁', x₂', hx'⟩ : ∃ x₁' x₂', (x₁ = S.cc i ∧ x₁' = S.cc i ∧ x₂' = S.cc' i) ∨
      (x₁ = z ∧ x₁' = S.cc' i ∧ x₂' = S.cc i) := by
    rcases hx12 with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr ⟨h, rfl, rfl⟩⟩
  have hx₁' : x₁' = S.cc i ∨ x₁' = S.cc' i := by
    rcases hx' with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hx₂' : x₂' = S.cc i ∨ x₂' = S.cc' i := by
    rcases hx' with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hne' : x₁' ≠ x₂' := by
    rcases hx' with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [h1, h2]
    · exact S.cc_ne i hik
    · exact (S.cc_ne i hik).symm
  have hB := S.isB_replace hik hx₁' hx₂' hne'
  obtain ⟨-, ℓ, hℓ⟩ := S.preDet_replace hik hx₁' hx₂' hne'
  have mem : ∀ f, f ∈ ℓ ↔ G.cls f = some .plus ∧ (G.ends f).1 ∈ G.int ∧
      S.lev (G.ends f).1 = i ∧ (G.ends f).2 ∈ G.int ∧ S.lev (G.ends f).2 = i :=
    fun f => (hℓ.2.1 f).trans (hB.ip f)
  have Fℓ : ∀ f ∈ ℓ, f ≠ S.e ∧ f ≠ S.e' ∧ f ≠ S.cc i ∧ f ≠ y ∧ f ≠ z ∧ Z.ends f = G.ends f ∧
      Z.cls f = G.cls f := by
    intro f hf
    obtain ⟨hp, a1, a2, b1, b2⟩ := (mem f).1 hf
    exact F f (by rw [hp]; simp) a1 a2 b1 b2
  have hyℓ : y ∉ ℓ := fun h => (Fℓ y h).2.2.2.1 rfl
  -- the steps
  have hp : Steps Z (y :: ℓ) := by
    rw [steps_cons]
    refine ⟨hC.stepY hZ hx12, fun t ht => ?_⟩
    rw [convert_convert', List.singleton_append]
    obtain ⟨hpl, a1, a2, b1, b2⟩ := (mem _).1 (List.getElem_mem ht)
    exact hC.stepB hZ hx12 hx' (hℓ.2.2 t ht) hpl a1 a2 b1 b2 (getElem_not_mem_take hℓ.1 ht)
  have mZ : ∀ v, S.lev v ≤ i → j ≤ S.lev v → v ∈ G.int → v ∈ Z.int :=
    fun v h1 h2 h3 => (hZ.int v).2 ⟨h3, h2, h1⟩
  have mp : p ∈ Z.int := mZ _ (by omega) (by omega) hC.hp
  have mw : S.w ∈ Z.int := mZ _ (by omega) (by omega) S.hw
  have hpi : ∀ f ∈ y :: ℓ, Z.IsIntPlus f := by
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · refine ⟨yc, ?_⟩
      rcases sameEnds_iff.1 ye with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
      · exact ⟨mp, mw⟩
      · exact ⟨mw, mp⟩
    · obtain ⟨hpl, a1, a2, b1, b2⟩ := (mem f).1 hf
      obtain ⟨-, -, -, -, -, z1, z2⟩ := Fℓ f hf
      rw [MGraph.IsIntPlus, z1, z2]
      exact ⟨hpl, mZ _ (by omega) (by omega) a1, mZ _ (by omega) (by omega) b1⟩
  refine preDet_prefix hp hpi (steps_dc hp (List.cons_ne_nil _ _)) ?_
  -- the component `i` and `w` collapsed
  have hinS : ∀ v, S.lev v = i → v ∈ G.int → v ∈ insert S.w (S.Lvl i (i + 1)) :=
    fun v h1 h2 => Finset.mem_insert_of_mem (S.mem_Lvl.2 ⟨h2, by omega, by omega⟩)
  have hwS : S.w ∈ insert S.w (S.Lvl i (i + 1)) := Finset.mem_insert_self _ _
  have hSS : insert S.w (S.Lvl i (i + 1)) ⊆ (Z.convert (y :: ℓ)).int := by
    intro v hv
    rw [convert_int]
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact mw
    · obtain ⟨h1, h2, h3⟩ := S.mem_Lvl.1 hv
      exact mZ _ (by omega) (by omega) h1
  obtain ⟨hu, hlu⟩ := S.u_mem hik
  have hx₁e : (Z.ends x₁).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
      (Z.ends x₁).2 ∈ insert S.w (S.Lvl i (i + 1)) := by
    rcases sameEnds_iff.1 t1e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨hinS _ hlu hu, hwS⟩
    · exact ⟨hwS, hinS _ hlu hu⟩
  have hye : (Z.ends y).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
      (Z.ends y).2 ∈ insert S.w (S.Lvl i (i + 1)) := by
    rcases sameEnds_iff.1 ye with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨hinS _ hlp hC.hp, hwS⟩
    · exact ⟨hwS, hinS _ hlp hC.hp⟩
  have hcx₁ : (Z.convert (y :: ℓ)).cls x₁ = some .diff := by rw [convert_cls, t1]; simp
  have hcy : (Z.convert (y :: ℓ)).cls y = some .diff := by
    rw [convert_cls, if_pos ⟨List.mem_cons_self, yc⟩]
  have dpc : ∀ f, (Z.ends f).1 ∈ insert S.w (S.Lvl i (i + 1)) →
      (Z.ends f).2 ∈ insert S.w (S.Lvl i (i + 1)) →
      (Z.convert (y :: ℓ)).cls f ≠ some .plus →
      (((Z.convert (y :: ℓ)).induce (insert S.w (S.Lvl i (i + 1)))).dropPlus).cls f
        = (Z.convert (y :: ℓ)).cls f := by
    intro f h1 h2 h3
    rw [dropPlus_cls]
    simp only [MGraph.induce, convert_ends, h1, h2, and_self, ↓reduceIte, h3]
  have hRi : (G.induce (S.Lvl i (i + 1))).int = S.Lvl i (i + 1) := rfl
  have hRp : ∀ f, (G.induce (S.Lvl i (i + 1))).Pres f → G.cls f ≠ none ∧ (G.ends f).1 ∈ G.int ∧
      S.lev (G.ends f).1 = i ∧ (G.ends f).2 ∈ G.int ∧ S.lev (G.ends f).2 = i ∧
      (G.induce (S.Lvl i (i + 1))).cls f = G.cls f := by
    intro f hf
    have hin : (G.ends f).1 ∈ S.Lvl i (i + 1) ∧ (G.ends f).2 ∈ S.Lvl i (i + 1) := by
      by_contra hn; exact hf.1 (by simp [MGraph.induce, hn])
    obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
    obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
    have hc : (G.induce (S.Lvl i (i + 1))).cls f = G.cls f := by simp [MGraph.induce, hin]
    exact ⟨hc ▸ hf.1, a1, by omega, b1, by omega, hc⟩
  have hx₁y : x₁ ≠ y := Ne.symm hyx1
  refine preDet_glue hSS hwS ?_ ?_
  · refine preDet_of_dropPlus ?_ (m := S.allPlus ++ [S.e']) ?_
    · refine dc_path (R := G.induce (S.Lvl i (i + 1))) (N := S.w) (g := y) (g₁ := y) (g₂ := y)
        (y₁ := x₁) (y₂ := y) (m₁ := S.u i) (m₂ := p) (S.toSplitCtx.dc_Lvl (i + 1) (by omega)) ?_ ?_
        (fun hP => ?_) ?_
      · rw [dropPlus_int]; change insert S.w (S.Lvl i (i + 1)) = insert S.w (S.Lvl i (i + 1)); rfl
      · intro f hf hfy
        obtain ⟨hc, a1, a2, b1, b2, hcl⟩ := hRp f hf
        obtain ⟨-, -, -, -, -, z1, z2⟩ := F f hc a1 a2 b1 b2
        have hconv : (Z.convert (y :: ℓ)).cls f =
            if G.cls f = some .plus then some .diff else G.cls f := by
          rw [convert_cls, z2]
          by_cases hpl : G.cls f = some .plus
          · rw [if_pos hpl, if_pos ⟨List.mem_cons_of_mem _ ((mem f).2 ⟨hpl, a1, a2, b1, b2⟩), hpl⟩]
          · rw [if_neg hpl, if_neg (fun h => hpl h.2)]
        have hnp : (Z.convert (y :: ℓ)).cls f ≠ some .plus := by
          rw [hconv]; split_ifs with h <;> [simp; exact h]
        rw [dpc f (by rw [z1]; exact hinS _ a2 a1) (by rw [z1]; exact hinS _ b2 b1) hnp, hconv,
          hcl]
        refine ⟨?_, ?_⟩
        · by_cases hpl : G.cls f = some .plus
          · rw [if_pos hpl]; exact Or.inr ⟨hpl, rfl⟩
          · rw [if_neg hpl]; exact Or.inl rfl
        · rw [dropPlus_ends]; simp only [MGraph.induce, convert_ends]; rw [z1]
          exact sameEnds_refl _
      · obtain ⟨hc, a1, a2, b1, b2, -⟩ := hRp y hP
        exact absurd rfl (F y hc a1 a2 b1 b2).2.2.2.1
      · intro _
        refine ⟨?_, Or.inl ?_, ?_, ?_, S.mem_Lvl.2 ⟨hu, by omega, by omega⟩,
          S.mem_Lvl.2 ⟨hC.hp, by omega, by omega⟩, hx₁y, fun f hf hfy => ⟨?_, hfy⟩,
          fun hP => ?_⟩
        · rw [dpc _ hx₁e.1 hx₁e.2 (by rw [hcx₁]; simp), hcx₁]
        · rw [dpc _ hye.1 hye.2 (by rw [hcy]; simp), hcy]
        · rw [dropPlus_ends]; simp only [MGraph.induce, convert_ends]
          exact t1e.trans (sameEnds_swap (S.w, S.u i))
        · rw [dropPlus_ends]; simp only [MGraph.induce, convert_ends]
          exact ye.trans (sameEnds_swap (S.w, p))
        · rintro rfl
          obtain ⟨hc, a1, a2, b1, b2, -⟩ := hRp _ hf
          obtain ⟨-, -, hfc, -, hfz, -, -⟩ := F _ hc a1 a2 b1 b2
          rcases hx12 with ⟨h, -⟩ | ⟨h, -⟩
          · exact hfc h
          · exact hfz h
        · obtain ⟨hc, a1, a2, b1, b2, -⟩ := hRp y hP
          exact absurd rfl (F y hc a1 a2 b1 b2).2.2.2.1
    · intro x hx
      obtain ⟨h1, -, -⟩ := hx
      have hin : (Z.ends x).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
          (Z.ends x).2 ∈ insert S.w (S.Lvl i (i + 1)) := by
        by_contra hn
        have h0 : ((Z.convert (y :: ℓ)).induce (insert S.w (S.Lvl i (i + 1)))).cls x = none := by
          simp only [MGraph.induce, convert_ends]; exact if_neg hn
        rw [h0] at h1; cases h1
      have h1' : (Z.convert (y :: ℓ)).cls x = some .plus := by
        have h0 : ((Z.convert (y :: ℓ)).induce (insert S.w (S.Lvl i (i + 1)))).cls x =
            (Z.convert (y :: ℓ)).cls x := by
          simp only [MGraph.induce, convert_ends]; exact if_pos hin
        rw [← h0]; exact h1
      have hz : Z.cls x = some .plus := by
        rw [convert_cls] at h1'
        split_ifs at h1' with h
        · exact h.2
        · exact h1'
      have hn : i < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
        intro _
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [h, t1] at hz; cases hz
        · rw [h, t2] at hz; cases hz
      obtain ⟨g1, g2⟩ := hZ.gen x hn
      rw [hz] at g2
      split_ifs at g2 with hg
      by_cases hxe' : x = S.e'
      · simp [hxe']
      · rw [split_cls_ne hxe'] at g2
        refine List.mem_append_left _ (mem_allPlus g2.symm ?_ ?_)
        · by_cases hxe : x = S.e
          · rw [hxe]
            rcases sameEnds_iff.1 hC.hev with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1]
            exacts [hC.hp, hC.hq]
          · rw [split_ends_ne hxe hxe'] at hg; exact ((hZ.int _).1 hg.1).1
        · by_cases hxe : x = S.e
          · rw [hxe]
            rcases sameEnds_iff.1 hC.hev with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2]
            exacts [hC.hq, hC.hp]
          · rw [split_ends_ne hxe hxe'] at hg; exact ((hZ.int _).1 hg.2).1
  · -- the graph of [II, Lemma 5.11] collapsed
    have trivQ : ∀ x, (Z.convert (y :: ℓ)).cls x = none ∨
        ((Z.convert (y :: ℓ)).cls x = some .diff ∧
          (Z.ends x).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
          (Z.ends x).2 ∈ insert S.w (S.Lvl i (i + 1))) →
        ¬ ((Z.convert (y :: ℓ)).collapse (insert S.w (S.Lvl i (i + 1))) S.w).Pres x ∧
        ¬ ((Z.convert (y :: ℓ)).collapse (insert S.w (S.Lvl i (i + 1))) S.w).IsIntPlus x := by
      intro x h
      rcases h with h | ⟨h, a, b⟩
      · exact ⟨fun h' => h'.1 h, fun h' => by have := h'.1; rw [collapse_cls, h] at this; cases this⟩
      · refine ⟨fun h' => h'.2.2.2 ?_, fun h' => by
          have := h'.1; rw [collapse_cls, h] at this; cases this⟩
        rw [collapse_convert_ends, if_pos a, if_pos b]
    have hx₁T : ∀ x, x = x₁ ∨ x = x₂ → (Z.convert (y :: ℓ)).cls x = none ∨
        ((Z.convert (y :: ℓ)).cls x = some .diff ∧
          (Z.ends x).1 ∈ insert S.w (S.Lvl i (i + 1)) ∧
          (Z.ends x).2 ∈ insert S.w (S.Lvl i (i + 1))) := by
      rintro x (rfl | rfl)
      · exact Or.inr ⟨hcx₁, hx₁e⟩
      · exact Or.inl (by rw [convert_cls, t2]; simp)
    refine Qtop hZ hji hik.le hlw hC.hp hlp (fun _ => ?_) (fun f hfe hfe' _ hpl a1 _ _ b1 _ _ => ?_)
      (fun h => absurd hC.e_eq (h hik)) (fun x hx => trivQ x ?_)
    · rcases hx12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨Or.inl rfl, Or.inr (Or.inr ?_)⟩
        rcases hC.hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
      · refine ⟨Or.inr (Or.inr ?_), Or.inl rfl⟩
        rcases hC.hyz with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl rfl
    · have hfy : f ≠ y := by
        intro h; rcases (hC.yz_ne.2 f).1 (Or.inl h) with h' | h'
        · exact hfe h'
        · exact hfe' h'
      rw [List.mem_cons, mem]
      constructor
      · rintro (h | ⟨-, -, h1, -, h2⟩)
        · exact absurd h hfy
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨hpl, a1, h1, b1, h2⟩
    · have hyz := hC.yz_ne
      rcases hx with h | h | ⟨-, h | h⟩
      · rcases (hyz.2 x).2 (Or.inl h) with rfl | rfl
        · exact Or.inr ⟨hcy, hye⟩
        · rcases hx12 with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact hx₁T _ (Or.inr rfl)
          · exact hx₁T _ (Or.inl rfl)
      · rcases (hyz.2 x).2 (Or.inr h) with rfl | rfl
        · exact Or.inr ⟨hcy, hye⟩
        · rcases hx12 with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact hx₁T _ (Or.inr rfl)
          · exact hx₁T _ (Or.inl rfl)
      · rcases hx12 with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact hx₁T _ (Or.inl (h.trans h1.symm))
        · exact hx₁T _ (Or.inr (h.trans h1.symm))
      · rw [← hC.e_eq] at h
        rcases (hyz.2 x).2 (Or.inl h) with rfl | rfl
        · exact Or.inr ⟨hcy, hye⟩
        · rcases hx12 with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact hx₁T _ (Or.inr rfl)
          · exact hx₁T _ (Or.inl rfl)

end CaseIV

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E}

/-- The setting of operation (B) on a chain, from the hypotheses of [II, Lemma 5.12]. -/
private theorem exists_SC {k : ℕ} {P : ℕ → Finset V} {e e' : E} {w : V}
    (hng : ∀ x : E, G.cls x ≠ some .ghost) (hs : G.SPD) (hc : G.IsChain k P)
    (he : G.cls e = some .plus) (hne : e ≠ e') (he' : G.cls e' = none) (hw : w ∈ G.int) :
    ∃ S : SC G, S.k = k ∧ S.P = P ∧ S.e = e ∧ S.e' = e' ∧ S.w = w := by
  have : Nonempty E := ⟨e⟩
  obtain ⟨C, hk, hP⟩ := ctx_exists hs hc hng
  exact ⟨SC.mk C e e' w hng he hne he' hw, hk, hP, rfl, rfl, rfl⟩

variable {S : SC G}

/-- A member `P t` of the chain that does not separate the ends of `e` from `w` is isolated after
operation (B). -/
private theorem iso_P {t : ℕ} (h1 : 1 ≤ t) (ht : t ≤ S.k) (hsep : ¬ Sep G S.e S.w (S.P t))
    (ha : G.IsVtx (G.ends S.e).1) (hb : G.IsVtx (G.ends S.e).2) :
    S.Gt.IsIsolated (S.P t) := by
  have := (S.chain.2.1 (t - 1) (by omega)).1.1
  rw [Nat.sub_add_cancel h1] at this
  exact (iso_split_iff S.hne S.hw S.ce S.ce' ha hb hsep).2 this

/-- The maximal isolated subset of `P s` after operation (B) is `P t`, if `P t` does not separate
the ends of `e` from `w` and every member strictly between does ([II, Lemma 5.12]). -/
private theorem maxIso {s t : ℕ} (hst : s < t) (ht : t ≤ S.k) (hsep : ¬ Sep G S.e S.w (S.P t))
    (hbetween : ∀ l, s < l → l < t → Sep G S.e S.w (S.P l))
    (ha : G.IsVtx (G.ends S.e).1) (hb : G.IsVtx (G.ends S.e).2)
    (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int) :
    S.Gt.IsMaximalIso (S.P s) (S.P t) := by
  have hPt := chain_anti S.chain hst.le ht
  have hss : S.P t ⊂ S.P s := Finset.ssubset_of_subset_of_ssubset (chain_anti S.chain
    (by omega : s + 1 ≤ t) ht) (S.chain.2.1 s (by omega)).1.2
  refine ⟨⟨iso_P (by omega) ht hsep ha hb, hss⟩, fun Q hQ hlt => ?_⟩
  have hQint : Q ⊆ G.int := hQ.1.1
  have hsint : S.P s ⊆ G.int := S.Psub s (by omega)
  by_cases hsepQ : Sep G S.e S.w Q
  · exact not_iso_split S.hne S.hw S.ce S.ce' ha hb hab S.spd.1 hQint hsepQ hQ.1
  · have hQG := (iso_split_iff S.hne S.hw S.ce S.ce' ha hb hsepQ).1 hQ.1
    have hQp : G.IsProperIso G.int Q :=
      ⟨hQG, Finset.ssubset_of_ssubset_of_subset hQ.2 hsint⟩
    obtain ⟨l, hl1, hlk, rfl⟩ := chain_iso_eq S.chain S.spd.2.1 hQp
    have hlt' : t > l := by
      by_contra h
      exact hlt.2 (chain_anti S.chain (not_lt.1 h) hlk)
    have hls : s < l := by
      by_contra h
      exact hQ.2.2 (chain_anti S.chain (not_lt.1 h) (by omega))
    exact hsepQ (hbetween l hls hlt')

/-- The crossing edges of `P (b + 1)` after operation (B), if the ends of `e` and `w` lie outside
`P (b + 1)`: those of `G`. -/
private theorem cross_out {b : ℕ} (hb : b < S.k) (ha : (G.ends S.e).1 ∉ S.P (b + 1))
    (hb' : (G.ends S.e).2 ∉ S.P (b + 1)) (hw : S.w ∉ S.P (b + 1)) (x : E)
    (hx : S.Gt.Crosses (S.P (b + 1)) x) :
    (x = S.cc b ∨ x = S.cc' b) ∧ x ≠ S.e ∧ x ≠ S.e' := by
  have hxe : x ≠ S.e := by
    rintro rfl
    obtain ⟨-, -, -, -, hcut⟩ := hx
    unfold MGraph.Cut at hcut
    rw [split_ends_e] at hcut
    dsimp only at hcut
    tauto
  have hxe' : x ≠ S.e' := by
    rintro rfl
    obtain ⟨-, -, -, -, hcut⟩ := hx
    unfold MGraph.Cut at hcut
    rw [split_ends_e' S.hne] at hcut
    dsimp only at hcut
    tauto
  exact ⟨(S.cross b hb x).1 ((split_crosses_ne hxe hxe').1 hx), hxe, hxe'⟩

/-- The pre-deterministic clause of [II, Def 5.9 (iii)] for `P s` and the member after `P b`, from
the maximality and the pre-deterministic property of every graph after operation (B) on the
components `s, …, b`. -/
private theorem clause_of_core {s b : ℕ} (hsb : s ≤ b) (hbk : b ≤ S.k)
    (hmax : b < S.k → S.Gt.IsMaximalIso (S.P s) (S.P (b + 1)))
    (hcr : b < S.k → ∀ x, S.Gt.Crosses (S.P (b + 1)) x →
      (x = S.cc b ∨ x = S.cc' b) ∧ x ≠ S.e ∧ x ≠ S.e')
    (core : ∀ (Z : MGraph V E) (x₁ x₂ : E) (B : MGraph V E), S.IsX Z s b x₁ x₂ →
      S.IsB B b x₁ x₂ → B.PreDet → (b < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e') →
      Z.PreDet) :
    S.Gt.ClauseIII (S.P s) (chainNext S.k S.P b) := by
  by_cases hb : b < S.k
  · simp only [chainNext, hb, if_true, MGraph.ClauseIII]
    refine ⟨hmax hb, fun x₁ x₂ hne h1 h2 => ?_⟩
    obtain ⟨c1, n1, n2⟩ := hcr hb x₁ h1
    obtain ⟨c2, n3, n4⟩ := hcr hb x₂ h2
    exact core _ x₁ x₂ _ (S.isX_replace hsb hb hne h1 h2) (S.isB_replace hb c1 c2 hne)
      (S.preDet_replace hb c1 c2 hne) (fun _ => ⟨n1, n2, n3, n4⟩)
  · have hbk' : b = S.k := le_antisymm hbk (not_lt.1 hb)
    simp only [chainNext, hb, if_false, MGraph.ClauseIII]
    subst hbk'
    exact core _ S.e S.e _ (S.isX_induce (by omega) S.e S.e) (S.isB_induce S.e S.e)
      S.preDet_last (fun h => absurd h (lt_irrefl _))

/-- Membership in a member of the chain by the component. -/
private theorem mem_P_lev {m : ℕ} (hm : m ≤ S.k) {v : V} (hv : v ∈ G.int) :
    v ∈ S.P m ↔ m ≤ S.lev v := by rw [S.mem_P hm]; exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩

private theorem not_mem_P_of_not_int {m : ℕ} (hm : m ≤ S.k) {v : V} (hv : v ∉ G.int) : v ∉ S.P m :=
  fun h => hv ((S.mem_P hm v).1 h).1

/-- **Case (i) of [II, Lemma 5.12]**. -/
private theorem conj_i {i j : ℕ} (hij : i < j) (hjk : j ≤ S.k) (hlw : S.lev S.w = j)
    (ha : (G.ends S.e).1 ∈ G.int) (hla : S.lev (G.ends S.e).1 = i)
    (hb : (G.ends S.e).2 ∈ G.int) (hlb : S.lev (G.ends S.e).2 = i) :
    S.Gt.ClauseIII (S.P i) (chainNext S.k S.P j) := by
  have hC : S.CaseI i j := ⟨hij, hjk, ha, hla, hb, hlb, hlw⟩
  refine clause_of_core hij.le hjk (fun hk => maxIso (by omega) hk ?_ (fun l h1 h2 => ?_)
      (Or.inl ha) (Or.inl hb) (Or.inl ha)) (fun hk => cross_out hk ?_ ?_ ?_)
    (fun Z x₁ x₂ B hZ hB hBpd hx12 => hC.preDet hZ hB hBpd hx12)
  · simp only [Sep]; rw [mem_P_lev hk ha, mem_P_lev hk hb, mem_P_lev hk S.hw]; omega
  · simp only [Sep]
    rw [mem_P_lev (by omega) ha, mem_P_lev (by omega) hb, mem_P_lev (by omega) S.hw]; omega
  · rw [mem_P_lev hk ha]; omega
  · rw [mem_P_lev hk hb]; omega
  · rw [mem_P_lev hk S.hw]; omega

/-- **Case (ii) of [II, Lemma 5.12]**. -/
private theorem conj_ii {i j : ℕ} (hji : j < i) (hik : i ≤ S.k) (hlw : S.lev S.w = j)
    (ha : (G.ends S.e).1 ∈ G.int) (hla : S.lev (G.ends S.e).1 = i)
    (hb : (G.ends S.e).2 ∈ G.int) (hlb : S.lev (G.ends S.e).2 = i) :
    S.Gt.ClauseIII (S.P j) (chainNext S.k S.P i) := by
  have hC : S.CaseII j i := ⟨hji, hik, ha, hla, hb, hlb, hlw⟩
  refine clause_of_core hji.le hik (fun hk => maxIso (by omega) hk ?_ (fun l h1 h2 => ?_)
      (Or.inl ha) (Or.inl hb) (Or.inl ha)) (fun hk => cross_out hk ?_ ?_ ?_)
    (fun Z x₁ x₂ B hZ hB hBpd _ => hC.preDet hZ hB hBpd)
  · simp only [Sep]; rw [mem_P_lev hk ha, mem_P_lev hk hb, mem_P_lev hk S.hw]; omega
  · simp only [Sep]
    rw [mem_P_lev (by omega) ha, mem_P_lev (by omega) hb, mem_P_lev (by omega) S.hw]; omega
  · rw [mem_P_lev hk ha]; omega
  · rw [mem_P_lev hk hb]; omega
  · rw [mem_P_lev hk S.hw]; omega

/-- **Cases (iii) and (v) of [II, Lemma 5.12]**: the end `t` of `e` in the component `s`, the
other end `v` outside `P s`, `w` in the component `j > s`. -/
private theorem conj_t {s j : ℕ} {t v : V} (hsj : s < j) (hjk : j ≤ S.k) (hlw : S.lev S.w = j)
    (ht : t ∈ G.int) (hlt : S.lev t = s) (hv : v ∉ G.int ∨ S.lev v < s) (hvtx : G.IsVtx v)
    (hev : G.ends S.e = (t, v) ∨ G.ends S.e = (v, t)) :
    S.Gt.ClauseIII (S.P s) (chainNext S.k S.P j) := by
  have hvP : ∀ m, s ≤ m → m ≤ S.k → v ∉ S.P m := by
    intro m h1 h2 h
    obtain ⟨h3, h4⟩ := (S.mem_P h2 v).1 h
    rcases hv with h' | h'
    · exact h' h3
    · omega
  have hvtx' : G.IsVtx (G.ends S.e).1 ∧ G.IsVtx (G.ends S.e).2 := by
    rcases hev with h | h <;> rw [h]
    · exact ⟨Or.inl ht, hvtx⟩
    · exact ⟨hvtx, Or.inl ht⟩
  have hint : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int := by
    rcases hev with h | h <;> rw [h]
    · exact Or.inl ht
    · exact Or.inr ht
  -- the edges `y` (from `w` to `t`) and `z` (from `w` to `v`)
  obtain ⟨y, z, hC⟩ : ∃ y z, S.CaseT s j y z t v := by
    rcases hev with h | h
    · refine ⟨S.e, S.e', hsj, hjk, Or.inl ⟨rfl, rfl⟩, ht, hlt, hlw, ?_, ?_, hv, ?_⟩
      · rw [split_ends_e, h]; exact Or.inr rfl
      · rw [split_ends_e' S.hne, h]; exact Or.inl rfl
      · rw [h]; exact Or.inl rfl
    · refine ⟨S.e', S.e, hsj, hjk, Or.inr ⟨rfl, rfl⟩, ht, hlt, hlw, ?_, ?_, hv, ?_⟩
      · rw [split_ends_e' S.hne, h]; exact Or.inl rfl
      · rw [split_ends_e, h]; exact Or.inr rfl
      · rw [h]; exact Or.inr rfl
  have key : ∀ m, s < m → m ≤ S.k → (G.ends S.e).1 ∉ S.P m ∧ (G.ends S.e).2 ∉ S.P m := by
    intro m h1 h2
    have htP : t ∉ S.P m := by rw [mem_P_lev h2 ht]; omega
    rcases hev with h | h <;> rw [h]
    · exact ⟨htP, hvP m (by omega) h2⟩
    · exact ⟨hvP m (by omega) h2, htP⟩
  refine clause_of_core hsj.le hjk (fun hk => maxIso (by omega) hk ?_ (fun l h1 h2 => ?_)
      hvtx'.1 hvtx'.2 hint) (fun hk => cross_out hk (key _ (by omega) hk).1
        (key _ (by omega) hk).2 (by rw [mem_P_lev hk S.hw]; omega))
    (fun Z x₁ x₂ B hZ hB hBpd hx12 => hC.preDet hZ hB hBpd hx12)
  · obtain ⟨k1, k2⟩ := key _ (by omega) hk
    simp only [Sep, k1, k2, false_and, false_or, mem_P_lev hk S.hw]
    omega
  · obtain ⟨k1, k2⟩ := key l h1 (by omega)
    simp only [Sep, k1, k2, false_and, false_or, not_false_eq_true, true_and]
    rw [mem_P_lev (by omega) S.hw]; omega

/-- The maximal isolated subset of `P i` after operation (B), when `e` crosses `P (i + 1)`. -/
private theorem maxIso_cross {i : ℕ} (hik : i < S.k) {p q : V} (hp : p ∈ G.int) (hlp : S.lev p = i)
    (hq : q ∈ G.int) (hlq : S.lev q = i + 1) (hev : G.ends S.e = (p, q) ∨ G.ends S.e = (q, p))
    {s : ℕ} (hs : s ≤ i) (hw : ∀ l, s < l → l ≤ i → S.w ∉ S.P l) :
    S.Gt.IsMaximalIso (S.P s) (S.P (i + 1)) := by
  have hvtx : G.IsVtx (G.ends S.e).1 ∧ G.IsVtx (G.ends S.e).2 := by
    rcases hev with h | h <;> rw [h]
    · exact ⟨Or.inl hp, Or.inl hq⟩
    · exact ⟨Or.inl hq, Or.inl hp⟩
  have hpP : p ∉ S.P (i + 1) := by rw [mem_P_lev hik hp]; omega
  have hqP : q ∈ S.P (i + 1) := by rw [mem_P_lev hik hq]; omega
  refine maxIso (by omega) hik ?_ (fun l h1 h2 => ?_) hvtx.1 hvtx.2 (by
    rcases hev with h | h <;> rw [h]
    · exact Or.inl hp
    · exact Or.inr hp)
  · simp only [Sep]
    rcases hev with h | h <;> rw [h] <;> dsimp only <;> tauto
  · have hpl : p ∈ S.P l := by rw [mem_P_lev (by omega) hp]; omega
    have hql : q ∈ S.P l := by rw [mem_P_lev (by omega) hq]; omega
    simp only [Sep]
    rcases hev with h | h <;> rw [h] <;> dsimp only
    · exact Or.inl ⟨hpl, hql, hw l h1 (by omega)⟩
    · exact Or.inl ⟨hql, hpl, hw l h1 (by omega)⟩

/-- **Case (iii) of [II, Lemma 5.12]**. -/
private theorem conj_iii {i j : ℕ} (hij : i + 1 < j) (hjk : j ≤ S.k) (hlw : S.lev S.w = j) {p q : V}
    (hp : p ∈ G.int) (hlp : S.lev p = i) (hq : q ∈ G.int) (hlq : S.lev q = i + 1)
    (hev : G.ends S.e = (p, q) ∨ G.ends S.e = (q, p)) :
    S.Gt.IsMaximalIso (S.P i) (S.P (i + 1)) ∧
      S.Gt.ClauseIII (S.P (i + 1)) (chainNext S.k S.P j) := by
  refine ⟨maxIso_cross (by omega) hp hlp hq hlq hev le_rfl (fun l h1 h2 => by omega), ?_⟩
  exact conj_t (t := q) (v := p) hij hjk hlw hq hlq (Or.inr (by omega)) (Or.inl hp)
    (hev.elim (fun h => Or.inr h) (fun h => Or.inl h))

/-- **Case (iv) of [II, Lemma 5.12]**. -/
private theorem conj_iv {i j : ℕ} (hji : j < i) (hik : i < S.k) (hlw : S.lev S.w = j) {p q : V}
    (hp : p ∈ G.int) (hlp : S.lev p = i) (hq : q ∈ G.int) (hlq : S.lev q = i + 1)
    (hev : G.ends S.e = (p, q) ∨ G.ends S.e = (q, p)) :
    S.Gt.ClauseIII (S.P j) (some (S.P (i + 1))) := by
  refine ⟨maxIso_cross hik hp hlp hq hlq hev hji.le (fun l h1 h2 => by
    rw [mem_P_lev (by omega) S.hw]; omega), fun x₁ x₂ hne h1 h2 => ?_⟩
  obtain ⟨y, z, hC⟩ : ∃ y z, S.CaseIV j i y z p q := by
    rcases hev with h | h
    · refine ⟨S.e, S.e', hji, hik, Or.inl ⟨rfl, rfl⟩, hp, hlp, hq, hlq, ?_, ?_, ?_, hlw⟩
      · rw [split_ends_e, h]; exact Or.inl rfl
      · rw [split_ends_e' S.hne, h]; exact Or.inl rfl
      · rw [h]; exact Or.inl rfl
    · refine ⟨S.e', S.e, hji, hik, Or.inr ⟨rfl, rfl⟩, hp, hlp, hq, hlq, ?_, ?_, ?_, hlw⟩
      · rw [split_ends_e' S.hne, h]; exact Or.inr rfl
      · rw [split_ends_e, h]; exact Or.inr rfl
      · rw [h]; exact Or.inr rfl
  have c1 := (hC.cross x₁).1 h1
  have c2 := (hC.cross x₂).1 h2
  have hx12 : (x₁ = S.cc i ∧ x₂ = z) ∨ (x₁ = z ∧ x₂ = S.cc i) := by
    rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
    · exact absurd (c1.trans c2.symm) hne
    · exact Or.inl ⟨c1, c2⟩
    · exact Or.inr ⟨c1, c2⟩
    · exact absurd (c1.trans c2.symm) hne
  exact hC.preDet (S.isX_replace hji.le hik hne h1 h2) hx12

end SC

/-! ## [II, Lemma 5.10 (B)] -/

/-- [II, Claim A.2] in net form, for a vertex `w` of `R`: a doubly connected graph `R` gives a
doubly connected graph `X` on the same internal vertices, if the present edges of `R` other than
`g` are edges of `X` and `g` is replaced by a path `g₁`, `g₂` through `w` of its class. -/
private theorem dc_pathE [DecidableEq V] [DecidableEq E] {R X : MGraph V E} (hR : R.DC) {w : V}
    (hw : w ∈ R.int) (hint : X.int = R.int) {g g₁ g₂ : E}
    (h1 : ∀ f, R.Pres f → f ≠ g → (X.cls f = R.cls f ∨
      (R.cls f = some .plus ∧ X.cls f = some .diff)) ∧ SameEnds (X.ends f) (R.ends f))
    (h2 : R.Pres g → X.cls g₁ = R.cls g ∧ X.cls g₂ = R.cls g ∧
      SameEnds (X.ends g₁) ((R.ends g).1, w) ∧ SameEnds (X.ends g₂) (w, (R.ends g).2) ∧
      ∀ f, R.Pres f → f ≠ g → f ≠ g₁ ∧ f ≠ g₂) : X.DC :=
  dc_path (N := w) (y₁ := g) (y₂ := g) (m₁ := w) (m₂ := w) hR
    (by rw [hint, Finset.insert_eq_of_mem hw]) h1 h2 (fun h => absurd hw h)

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-! ### Adjacent members of the chain after operation (B) -/

section Adjacent

variable {s : ℕ} {Z : MGraph V E} {x₁ x₂ : E}

/-- The graph of the component `s` of `G` is contained in the graph of the component after the
operation, if `e` is not an edge inside the component and the `Θ` edge is not `e` or `e'`. -/
private theorem adj_le (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (he : ¬ ((G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = s ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = s)) :
    Le B Z ∧ (∀ x, x = S.e ∨ x = S.e' → ¬ B.Pres x ∧ ¬ B.IsIntPlus x) := by
  have hint : B.int = Z.int := by
    ext v; rw [hB.int, hZ.int]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩⟩
  have hBe : ∀ x, x = S.e ∨ x = S.e' → B.cls x ≠ none → False := by
    intro x hx hc
    rcases hB.pres x hc with ⟨hk, rfl, -⟩ | ⟨-, a1, a2, b1, b2, h, -⟩
    · obtain ⟨n1, n2, -⟩ := hx12 hk
      rcases hx with h | h
      · exact n1 h
      · exact n2 h
    · rcases hx with rfl | rfl
      · exact he ⟨a1, a2, b1, b2⟩
      · exact hc (by rw [h, S.ce'])
  refine ⟨⟨hint, fun x hx => ?_⟩, fun x hx => ⟨fun h => hBe x hx h.1, fun h => ?_⟩⟩
  swap
  · exact hBe x hx (by rw [h.1]; simp)
  simp only [id]
  rcases hB.pres x hx.1 with ⟨hk, rfl, hc, hen⟩ | ⟨hn, a1, a2, b1, b2, hc, hen⟩
  · obtain ⟨-, t1, -, t2, -, -⟩ := hZ.th hk
    obtain ⟨n1, n2, n3, n4⟩ := hx12 hk
    refine ⟨Or.inl (by rw [t1, hc]), ?_⟩
    rw [t2, hen]
    unfold MGraph.outer
    rw [split_ends_ne n1 n2, split_ends_ne n3 n4]
    exact sameEnds_refl _
  · have hxe : x ≠ S.e := by rintro rfl; exact he ⟨a1, a2, b1, b2⟩
    have hxe' : x ≠ S.e' := by rintro rfl; exact hx.1 (by rw [hc, S.ce'])
    obtain ⟨z1, z2⟩ := hZ.edge hxe hxe' a1 (by omega) (by omega) b1 (by omega) (by omega)
    exact ⟨Or.inl (by rw [z2, hc]), by rw [z1, hen]; exact sameEnds_refl _⟩

/-- The internal blue solid edges other than `e`, `e'` of the graphs of the component `s` before
and after the operation. -/
private theorem adj_ip (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂) (x : E)
    (hxe : x ≠ S.e) (hxe' : x ≠ S.e') : B.IsIntPlus x ↔ Z.IsIntPlus x := by
  rw [hB.ip, hZ.intPlus x hxe hxe']
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, by omega, by omega, h4, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨h1, h2, by omega, h5, by omega⟩

/-- The edge `x ∈ {e, e'}` is not an internal blue solid edge after the operation if its ends are
not internal vertices of the component. -/
private theorem adj_not_ip (hZ : S.IsX Z s s x₁ x₂)
    (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e') {x : E}
    (hx : x = S.e ∨ x = S.e') (hgt : ¬ ((S.Gt.ends x).1 ∈ Z.int ∧ (S.Gt.ends x).2 ∈ Z.int)) :
    ¬ Z.IsIntPlus x ∧ ¬ Z.Pres x := by
  have hn : s < S.k → x ≠ x₁ ∧ x ≠ x₂ := by
    intro hk
    obtain ⟨n1, n2, n3, n4⟩ := hx12 hk
    rcases hx with rfl | rfl
    · exact ⟨Ne.symm n1, Ne.symm n3⟩
    · exact ⟨Ne.symm n2, Ne.symm n4⟩
  obtain ⟨g1, g2⟩ := hZ.gen x hn
  rw [if_neg hgt] at g2
  refine ⟨fun h => ?_, fun h => h.1 g2⟩
  have := h.1
  rw [g2] at this
  cases this

/-- Adjacent members, case (α): `e`, `e'` are not edges of the graph of the component `s` after the
operation, `e` is not an edge of the graph of the component before it, and the `Θ` edge is not
`e` or `e'`: the two graphs have the same edges. -/
private theorem adj_alpha (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hBpd : B.PreDet) (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (he : ¬ ((G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = s ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = s))
    (hgt : ∀ x, (x = S.e ∨ x = S.e') → ¬ ((S.Gt.ends x).1 ∈ Z.int ∧ (S.Gt.ends x).2 ∈ Z.int)) :
    Z.PreDet := by
  obtain ⟨hle, hBe⟩ := adj_le hZ hB hx12 he
  refine preDet_transfer (σ := id) Function.injective_id hBpd hle (fun _ _ => rfl) (fun x => ?_)
  by_cases hxe : x = S.e ∨ x = S.e'
  · exact iff_of_false (hBe x hxe).2 (adj_not_ip hZ hx12 hxe (hgt x hxe)).1
  · rw [not_or] at hxe
    exact adj_ip hZ hB x hxe.1 hxe.2

/-- Adjacent members, case (δ): one of `e`, `e'` is an edge inside the component `s` after the
operation, the other is not, `e` is not an edge of the graph of the component before it: the
graph is that of the component with one blue solid edge added, which is redundant first. -/
private theorem adj_delta (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hBpd : B.PreDet) (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (he : ¬ ((G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = s ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = s)) {ε : E} (hε : ε = S.e ∨ ε = S.e')
    (hεin : (S.Gt.ends ε).1 ∈ Z.int ∧ (S.Gt.ends ε).2 ∈ Z.int)
    (hother : ∀ x, (x = S.e ∨ x = S.e') → x ≠ ε →
      ¬ ((S.Gt.ends x).1 ∈ Z.int ∧ (S.Gt.ends x).2 ∈ Z.int)) : Z.PreDet := by
  obtain ⟨hle, hBe⟩ := adj_le hZ hB hx12 he
  have hn : s < S.k → ε ≠ x₁ ∧ ε ≠ x₂ := by
    intro hk
    obtain ⟨n1, n2, n3, n4⟩ := hx12 hk
    rcases hε with rfl | rfl
    · exact ⟨Ne.symm n1, Ne.symm n3⟩
    · exact ⟨Ne.symm n2, Ne.symm n4⟩
  obtain ⟨g1, g2⟩ := hZ.gen ε hn
  have hεc : Z.cls ε = some .plus := by
    rw [g2, if_pos hεin]
    rcases hε with rfl | rfl
    · rw [split_cls_of S.hne, S.ce]
    · rw [split_cls_e', S.ce]
  have hεp : Z.IsIntPlus ε := ⟨hεc, by rw [g1]; exact hεin.1, by rw [g1]; exact hεin.2⟩
  have hdc := dc_le hBpd.1 hle
  have hle' : Le B (Z.erase ε) := by
    refine ⟨hle.1, fun x hx => ?_⟩
    have hxε : x ≠ ε := fun h => (hBe x (h ▸ hε)).1 hx
    obtain ⟨c, se⟩ := hle.2 x hx
    refine ⟨?_, se⟩
    simp only [id] at c ⊢
    rw [erase_cls, if_neg hxε]; exact c
  refine preDet_prefix (steps_single.2 ⟨hεc, hdc, dc_le hBpd.1 hle'⟩) (by simpa using hεp) hdc ?_
  refine preDet_transfer (σ := id) Function.injective_id hBpd (le_trans' hle (le_convert Z [ε]))
    (fun _ _ => rfl) (fun x => ?_)
  by_cases hxe : x = S.e ∨ x = S.e'
  · refine iff_of_false (hBe x hxe).2 ?_
    by_cases hxε : x = ε
    · subst hxε
      rintro ⟨h, -⟩
      rw [convert_cls, if_pos ⟨List.mem_singleton_self _, hεc⟩] at h
      cases h
    · intro h
      have hc : Z.cls x = some .plus := by
        have := h.1
        rw [convert_cls] at this
        split_ifs at this with h'
        · cases this
        · exact this
      exact (adj_not_ip hZ hx12 hxe (hother x hxe hxε)).1 ⟨hc, h.2⟩
  · rw [not_or] at hxe
    have hxε : x ≠ ε := by rintro rfl; rcases hε with h | h; exacts [hxe.1 h, hxe.2 h]
    rw [adj_ip hZ hB x hxe.1 hxe.2]
    unfold MGraph.IsIntPlus
    rw [convert_cls, if_neg (by simp [hxε]), convert_ends, convert_int]

section Beta

variable (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
  (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
  (ha : (G.ends S.e).1 ∈ G.int) (hla : S.lev (G.ends S.e).1 = s)
  (hb : (G.ends S.e).2 ∈ G.int) (hlb : S.lev (G.ends S.e).2 = s) (hlw : S.lev S.w = s)
include hZ hB hx12 ha hla hb hlb hlw

/-- Adjacent members, case (β): the edges `e`, `e'` of the path, inside the component. -/
private theorem beta_path :
    Z.cls S.e = some .plus ∧ Z.ends S.e = ((G.ends S.e).1, S.w) ∧
    Z.cls S.e' = some .plus ∧ Z.ends S.e' = (S.w, (G.ends S.e).2) ∧
    B.cls S.e = some .plus ∧ B.ends S.e = G.ends S.e ∧ B.int = Z.int := by
  have hge : S.Gt.ends S.e = ((G.ends S.e).1, S.w) := split_ends_e
  have hge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
  obtain ⟨z1, z2⟩ := hZ.gedge (x := S.e) (by rw [hge]; exact ha)
    (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega) (by rw [hge]; exact S.hw)
    (by rw [hge]; dsimp only; omega) (by rw [hge]; dsimp only; omega)
  obtain ⟨z1', z2'⟩ := hZ.gedge (x := S.e') (by rw [hge']; exact S.hw)
    (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
    (by rw [hge']; exact hb) (by rw [hge']; dsimp only; omega) (by rw [hge']; dsimp only; omega)
  have hBe : B.cls S.e = some .plus ∧ B.ends S.e = G.ends S.e := by
    have hp : B.IsIntPlus S.e := (hB.ip _).2 ⟨S.ce, ha, hla, hb, hlb⟩
    rcases hB.pres _ (by rw [hp.1]; simp) with ⟨hk, h, -⟩ | ⟨-, -, -, -, -, hc, he⟩
    · exact absurd h.symm (hx12 hk).1
    · exact ⟨hc ▸ hp.1, he⟩
  refine ⟨by rw [z2, split_cls_of S.hne, S.ce], z1.trans hge, by rw [z2', split_cls_e', S.ce],
    z1'.trans hge', hBe.1, hBe.2, ?_⟩
  ext v; rw [hB.int, hZ.int]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩⟩

/-- The hypotheses of `dc_pathE` in case (β). -/
private theorem beta_hyps {l m : List E}
    (hlm : ∀ f, f ≠ S.e → G.cls f = some .plus → f ∈ m → f ∈ l)
    (he1 : S.e ∈ l ↔ S.e ∈ m) (he2 : S.e' ∈ l ↔ S.e ∈ m) :
    (∀ f, (B.convert m).Pres f → f ≠ S.e → ((Z.convert l).cls f = (B.convert m).cls f ∨
      ((B.convert m).cls f = some .plus ∧ (Z.convert l).cls f = some .diff)) ∧
      SameEnds ((Z.convert l).ends f) ((B.convert m).ends f)) ∧
    ((B.convert m).Pres S.e → (Z.convert l).cls S.e = (B.convert m).cls S.e ∧
      (Z.convert l).cls S.e' = (B.convert m).cls S.e ∧
      SameEnds ((Z.convert l).ends S.e) (((B.convert m).ends S.e).1, S.w) ∧
      SameEnds ((Z.convert l).ends S.e') (S.w, ((B.convert m).ends S.e).2) ∧
      ∀ f, (B.convert m).Pres f → f ≠ S.e → f ≠ S.e ∧ f ≠ S.e') := by
  obtain ⟨p1, p2, p3, p4, hBe, hBen, -⟩ := beta_path hZ hB hx12 ha hla hb hlb hlw
  refine ⟨fun f hf hfe => ?_, fun _ => ⟨?_, ?_, ?_, ?_, fun f hf hfe => ⟨hfe, ?_⟩⟩⟩
  · rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨hk, rfl, hc, hen⟩ |
      ⟨hn, a1, a2, b1, b2, hc, hen⟩
    · obtain ⟨-, t1, -, t2, -, -⟩ := hZ.th hk
      obtain ⟨n1, n2, n3, n4⟩ := hx12 hk
      refine ⟨Or.inl ?_, ?_⟩
      · rw [convert_cls, convert_cls, t1, hc]; simp
      · rw [convert_ends, convert_ends, t2, hen]
        unfold MGraph.outer
        rw [split_ends_ne n1 n2, split_ends_ne n3 n4]
        exact sameEnds_refl _
    · have hfe' : f ≠ S.e' := by
        rintro rfl; exact (convert_ne_none.1 hf.1) (by rw [hc, S.ce'])
      obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1 (by omega) (by omega) b1 (by omega) (by omega)
      refine ⟨?_, by rw [convert_ends, convert_ends, z1, hen]; exact sameEnds_refl _⟩
      have hZf : (Z.convert l).cls f =
          if f ∈ l ∧ G.cls f = some .plus then some .diff else G.cls f := by
        rw [convert_cls, z2]
      have hBf : (B.convert m).cls f =
          if f ∈ m ∧ G.cls f = some .plus then some .diff else G.cls f := by
        rw [convert_cls, hc]
      rw [hZf, hBf]
      by_cases hp : G.cls f = some .plus
      · by_cases hm : f ∈ m
        · rw [if_pos (show f ∈ l ∧ G.cls f = some .plus from ⟨hlm f hfe hp hm, hp⟩),
            if_pos (show f ∈ m ∧ G.cls f = some .plus from ⟨hm, hp⟩)]
          exact Or.inl rfl
        · rw [if_neg (show ¬ (f ∈ m ∧ G.cls f = some .plus) from fun h => hm h.1)]
          by_cases hl : f ∈ l
          · rw [if_pos (show f ∈ l ∧ G.cls f = some .plus from ⟨hl, hp⟩)]
            exact Or.inr ⟨hp, rfl⟩
          · rw [if_neg (show ¬ (f ∈ l ∧ G.cls f = some .plus) from fun h => hl h.1)]
            exact Or.inl rfl
      · rw [if_neg (show ¬ (f ∈ l ∧ G.cls f = some .plus) from fun h => hp h.2),
          if_neg (show ¬ (f ∈ m ∧ G.cls f = some .plus) from fun h => hp h.2)]
        exact Or.inl rfl
  · rw [convert_cls, convert_cls, p1, hBe]; simp only [he1]
  · rw [convert_cls, convert_cls, p3, hBe]; simp only [he2]
  · rw [convert_ends, convert_ends, p2, hBen]; exact sameEnds_refl _
  · rw [convert_ends, convert_ends, p4, hBen]; exact sameEnds_refl _
  · rintro rfl
    obtain ⟨hc, -⟩ := hf
    rcases hB.pres _ (convert_ne_none.1 hc) with ⟨hk, h', -⟩ | ⟨-, -, -, -, -, h', -⟩
    · exact (hx12 hk).2.1 h'.symm
    · exact (convert_ne_none.1 hc) (by rw [h', S.ce'])

end Beta

end Adjacent

end SC

/-- The hypotheses of `dc_pathE`: the present edges of `R` other than `g` are edges of `X`, and
`g` is replaced by a path `g₁`, `g₂` through `w` of its class. -/
private def PathE (R X : MGraph V E) (w : V) (g g₁ g₂ : E) : Prop :=
  (∀ f, R.Pres f → f ≠ g → (X.cls f = R.cls f ∨
      (R.cls f = some .plus ∧ X.cls f = some .diff)) ∧ SameEnds (X.ends f) (R.ends f)) ∧
  (R.Pres g → X.cls g₁ = R.cls g ∧ X.cls g₂ = R.cls g ∧
      SameEnds (X.ends g₁) ((R.ends g).1, w) ∧ SameEnds (X.ends g₂) (w, (R.ends g).2) ∧
      ∀ f, R.Pres f → f ≠ g → f ≠ g₁ ∧ f ≠ g₂)

private theorem le_erase_self [DecidableEq E] (X : MGraph V E) (y : E) : Le (X.erase y) X := by
  refine ⟨rfl, fun f hf => ⟨Or.inl ?_, sameEnds_refl _⟩⟩
  have hfy : f ≠ y := by rintro rfl; exact hf.1 (by rw [erase_cls]; simp)
  simp only [id]
  rw [erase_cls, if_neg hfy]

/-- The hypotheses of `dc_pathE` are kept when the same edge `x`, other than the edges of the
path, is removed from both graphs. -/
private theorem pathE_erase [DecidableEq E] {R X : MGraph V E} {w : V} {g g₁ g₂ : E}
    (h : PathE R X w g g₁ g₂) {x : E} (hxg : x ≠ g) (hx1 : x ≠ g₁) (hx2 : x ≠ g₂) :
    PathE (R.erase x) (X.erase x) w g g₁ g₂ := by
  have pres : ∀ f, (R.erase x).Pres f → R.Pres f ∧ f ≠ x := by
    intro f hf
    have hfx : f ≠ x := by rintro rfl; exact hf.1 (by rw [erase_cls]; simp)
    obtain ⟨c, h⟩ := hf
    rw [erase_cls, if_neg hfx] at c
    exact ⟨⟨c, h⟩, hfx⟩
  refine ⟨fun f hf hfg => ?_, fun hp => ?_⟩
  · obtain ⟨hp, hfx⟩ := pres f hf
    rw [erase_cls, erase_cls, if_neg hfx, if_neg hfx, erase_ends, erase_ends]
    exact h.1 f hp hfg
  · obtain ⟨hp, -⟩ := pres g hp
    obtain ⟨c1, c2, s1, s2, d⟩ := h.2 hp
    rw [erase_cls, erase_cls, erase_cls, if_neg hx1.symm, if_neg hx2.symm, if_neg hxg.symm]
    simp only [erase_ends]
    exact ⟨c1, c2, s1, s2, fun f hf hfg => d f (pres f hf).1 hfg⟩

/-- The graph `R` with an edge `g` removed is contained in `X` with an edge `y` removed, if the
present edges of `R` other than `g` are edges of `X` other than `y`. -/
private theorem le_erase_path [DecidableEq E] {R X : MGraph V E} (hint : X.int = R.int) {g y : E}
    (h1 : ∀ f, R.Pres f → f ≠ g → (X.cls f = R.cls f ∨
      (R.cls f = some .plus ∧ X.cls f = some .diff)) ∧ SameEnds (X.ends f) (R.ends f))
    (hy : ∀ f, R.Pres f → f ≠ g → f ≠ y) : Le (R.erase g) (X.erase y) := by
  refine ⟨by rw [erase_int, erase_int, hint], fun f hf => ?_⟩
  have hfg : f ≠ g := by rintro rfl; exact hf.1 (by rw [erase_cls]; simp)
  obtain ⟨c, hh⟩ := hf
  rw [erase_cls, if_neg hfg] at c
  have hp : R.Pres f := ⟨c, hh⟩
  have hfy := hy f hp hfg
  simp only [id]
  rw [erase_cls, erase_cls, if_neg hfg, if_neg hfy, erase_ends, erase_ends]
  exact h1 f hp hfg

/-- Redundancy steps of `R` give redundancy steps of `X`, if at each step the hypotheses of
`dc_pathE` hold for the graphs with the edges before changed into `Θ` edges. -/
private theorem steps_pathE [DecidableEq V] [DecidableEq E] {R X : MGraph V E} {w : V} (hw : w ∈ R.int)
    (hint : X.int = R.int) {g g₁ g₂ : E} {L : List E} (hR : Steps R L)
    (hL : ∀ y ∈ L, y ≠ g ∧ y ≠ g₁ ∧ y ≠ g₂ ∧ X.cls y = R.cls y)
    (H : ∀ t ≤ L.length, PathE (R.convert (L.take t)) (X.convert (L.take t)) w g g₁ g₂) :
    Steps X L := by
  intro t ht
  obtain ⟨c, d1, d2⟩ := hR t ht
  have hy := hL _ (List.getElem_mem ht)
  have hH := H t ht.le
  have hw' : w ∈ (R.convert (L.take t)).int := by rw [convert_int]; exact hw
  have hint' : (X.convert (L.take t)).int = (R.convert (L.take t)).int := by
    rw [convert_int, convert_int, hint]
  refine ⟨?_, dc_pathE d1 hw' hint' hH.1 hH.2, ?_⟩
  · rw [convert_cls, hy.2.2.2, ← convert_cls]; exact c
  · have hE := pathE_erase hH hy.1 hy.2.1 hy.2.2.1
    exact dc_pathE d2 (by rw [erase_int]; exact hw')
      (by rw [erase_int, erase_int]; exact hint') hE.1 hE.2

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

section Beta

variable {s : ℕ} {Z : MGraph V E} {x₁ x₂ : E}

/-- Case (β): the present edges of the graph of the component before the operation other than
`e` are edges of the graph after it. -/
private theorem beta_h1 (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e') {l m : List E}
    (hlm : ∀ f, f ≠ S.e → G.cls f = some .plus → f ∈ m → f ∈ l) :
    ∀ f, (B.convert m).Pres f → f ≠ S.e → ((Z.convert l).cls f = (B.convert m).cls f ∨
      ((B.convert m).cls f = some .plus ∧ (Z.convert l).cls f = some .diff)) ∧
      SameEnds ((Z.convert l).ends f) ((B.convert m).ends f) := by
  intro f hf hfe
  rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨hk, rfl, hc, hen⟩ |
    ⟨hn, a1, a2, b1, b2, hc, hen⟩
  · obtain ⟨-, t1, -, t2, -, -⟩ := hZ.th hk
    obtain ⟨n1, n2, n3, n4⟩ := hx12 hk
    refine ⟨Or.inl ?_, ?_⟩
    · rw [convert_cls, convert_cls, t1, hc]; simp
    · rw [convert_ends, convert_ends, t2, hen]
      unfold MGraph.outer
      rw [split_ends_ne n1 n2, split_ends_ne n3 n4]
      exact sameEnds_refl _
  · have hfe' : f ≠ S.e' := by
      rintro rfl; exact (convert_ne_none.1 hf.1) (by rw [hc, S.ce'])
    obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1 (by omega) (by omega) b1 (by omega) (by omega)
    refine ⟨?_, by rw [convert_ends, convert_ends, z1, hen]; exact sameEnds_refl _⟩
    have hZf : (Z.convert l).cls f =
        if f ∈ l ∧ G.cls f = some .plus then some .diff else G.cls f := by
      rw [convert_cls, z2]
    have hBf : (B.convert m).cls f =
        if f ∈ m ∧ G.cls f = some .plus then some .diff else G.cls f := by
      rw [convert_cls, hc]
    rw [hZf, hBf]
    by_cases hp : G.cls f = some .plus
    · by_cases hm : f ∈ m
      · rw [if_pos (show f ∈ l ∧ G.cls f = some .plus from ⟨hlm f hfe hp hm, hp⟩),
          if_pos (show f ∈ m ∧ G.cls f = some .plus from ⟨hm, hp⟩)]
        exact Or.inl rfl
      · rw [if_neg (show ¬ (f ∈ m ∧ G.cls f = some .plus) from fun h => hm h.1)]
        by_cases hl : f ∈ l
        · rw [if_pos (show f ∈ l ∧ G.cls f = some .plus from ⟨hl, hp⟩)]
          exact Or.inr ⟨hp, rfl⟩
        · rw [if_neg (show ¬ (f ∈ l ∧ G.cls f = some .plus) from fun h => hl h.1)]
          exact Or.inl rfl
    · rw [if_neg (show ¬ (f ∈ l ∧ G.cls f = some .plus) from fun h => hp h.2),
        if_neg (show ¬ (f ∈ m ∧ G.cls f = some .plus) from fun h => hp h.2)]
      exact Or.inl rfl

/-- The edge `e'` is absent from the graph of the component before the operation. -/
private theorem isB_e' {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e') : B.cls S.e' = none := by
  by_contra hc
  rcases hB.pres _ hc with ⟨hk, h, -⟩ | ⟨-, -, -, -, -, h, -⟩
  · exact (hx12 hk).2.1 h.symm
  · exact hc (by rw [h, S.ce'])

/-- Adjacent members, case (β): `e` is an edge inside the component `s` and `w` lies in it. The
pre-deterministic order of the component before the operation, with `e` followed by `e'`, is one
after it. -/
private theorem adj_beta (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hBpd : B.PreDet) (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (ha : (G.ends S.e).1 ∈ G.int) (hla : S.lev (G.ends S.e).1 = s)
    (hb : (G.ends S.e).2 ∈ G.int) (hlb : S.lev (G.ends S.e).2 = s) (hlw : S.lev S.w = s) :
    Z.PreDet := by
  obtain ⟨p1, p2, p3, p4, hBe, hBen, hint⟩ := beta_path hZ hB hx12 ha hla hb hlb hlw
  have hBe' := isB_e' hB hx12
  obtain ⟨hdc, ℓ, hnd, hmem, hst⟩ := hBpd
  have hwB : S.w ∈ B.int := (hB.int _).2 ⟨S.hw, hlw⟩
  have hZint : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ S.lev v = s := fun v => by
    rw [hZ.int]; exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
  have heℓ : S.e ∈ ℓ := (hmem _).2 ((hB.ip _).2 ⟨S.ce, ha, hla, hb, hlb⟩)
  obtain ⟨α, β, rfl⟩ := List.append_of_mem heℓ
  have hnd' := hnd
  rw [List.nodup_append] at hnd'
  have heα : S.e ∉ α := fun h => hnd'.2.2 _ h _ List.mem_cons_self rfl
  have heβ : S.e ∉ β := (List.nodup_cons.1 hnd'.2.1).1
  have hmemℓ : ∀ y, y ∈ α ∨ y ∈ β → y ≠ S.e ∧ y ≠ S.e' ∧ B.IsIntPlus y := by
    intro y hy
    have hyℓ : y ∈ α ++ S.e :: β := by
      rcases hy with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hip := (hmem y).1 hyℓ
    refine ⟨?_, ?_, hip⟩
    · rintro rfl; rcases hy with h | h; exacts [heα h, heβ h]
    · rintro rfl; have := hip.1; rw [hBe'] at this; cases this
  have hcl : ∀ y, y ∈ α ∨ y ∈ β → Z.cls y = B.cls y := by
    intro y hy
    obtain ⟨n1, n2, hip⟩ := hmemℓ y hy
    rw [hip.1, ((adj_ip hZ hB y n1 n2).1 hip).1]
  have hint' : ∀ l m : List E, (Z.convert l).int = (B.convert m).int := fun l m => by
    rw [convert_int, convert_int, hint]
  have hBα : Steps B α := (steps_append.1 hst).1
  have hBeβ := (steps_append.1 hst).2
  rw [steps_cons, convert_convert'] at hBeβ
  obtain ⟨⟨-, hBαdc, hBαe⟩, hBβ⟩ := hBeβ
  -- the hypotheses of the rerouting for the two lists
  have rα : ∀ l : List E, (∀ y ∈ l, y ∈ α) → PathE (B.convert l) (Z.convert l) S.w S.e S.e S.e' :=
    fun l hl => beta_hyps hZ hB hx12 ha hla hb hlb hlw (fun _ _ _ h => h)
      (iff_of_eq rfl) (iff_of_false (fun h => (hmemℓ _ (Or.inl (hl _ h))).2.1 rfl)
        (fun h => heα (hl _ h)))
  have hZdc : Z.DC := by
    have h := rα [] (by simp)
    rw [convert_nil', convert_nil'] at h
    exact dc_pathE hdc hwB (by rw [hint]) h.1 h.2
  refine preDet_of_steps hZdc (l := α ++ S.e :: S.e' :: β) ?_ (fun x => ?_)
  · refine steps_append.2 ⟨?_, steps_cons.2 ⟨?_, ?_⟩⟩
    · refine steps_pathE (g := S.e) (g₁ := S.e) (g₂ := S.e') hwB (by rw [hint]) hBα (fun y hy => ?_) (fun t ht => ?_)
      · obtain ⟨n1, n2, -⟩ := hmemℓ y (Or.inl hy)
        exact ⟨n1, n1, n2, hcl y (Or.inl hy)⟩
      · exact rα _ (fun y hy => List.mem_of_mem_take hy)
    · have h := rα α (fun y hy => hy)
      refine ⟨by rw [convert_cls, if_neg (fun h => heα h.1)]; exact p1,
        dc_pathE hBαdc (by rw [convert_int]; exact hwB) (hint' _ _) h.1 h.2, ?_⟩
      exact dc_le hBαe (le_erase_path (hint' _ _) h.1 (fun f _ hfe => hfe))
    · rw [steps_cons, convert_convert']
      have hlα : ∀ f, f ≠ S.e → G.cls f = some .plus → f ∈ α → f ∈ α ++ [S.e] :=
        fun f _ _ h => List.mem_append_left _ h
      have h1 := beta_h1 hZ hB hx12 (l := α ++ [S.e]) (m := α) hlα
      have her : ((Z.convert (α ++ [S.e])).erase S.e').DC :=
        dc_le hBαe (le_erase_path (hint' _ _) h1 (fun f hf _ hfe => by
          rw [hfe] at hf
          exact (convert_ne_none.1 hf.1) hBe'))
      refine ⟨⟨?_, dc_le her (le_erase_self _ _), her⟩, ?_⟩
      · rw [convert_cls, if_neg (fun h => ?_)]
        · exact p3
        · rcases List.mem_append.1 h.1 with h' | h'
          · exact (hmemℓ _ (Or.inl h')).2.1 rfl
          · exact S.hne (List.mem_singleton.1 h').symm
      · rw [convert_convert', List.append_assoc, List.singleton_append]
        refine steps_pathE (R := B.convert (α ++ [S.e])) (g := S.e) (g₁ := S.e) (g₂ := S.e') (by rw [convert_int]; exact hwB)
          (hint' _ _) hBβ (fun y hy => ?_) (fun t ht => ?_)
        · obtain ⟨n1, n2, -⟩ := hmemℓ y (Or.inr hy)
          have hyα : y ∉ α := fun h => hnd'.2.2 _ h _ (List.mem_cons_of_mem _ hy) rfl
          refine ⟨n1, n1, n2, ?_⟩
          rw [convert_cls, convert_cls, hcl y (Or.inr hy)]
          simp [hyα, n1, n2]
        · rw [convert_convert', convert_convert']
          refine beta_hyps hZ hB hx12 ha hla hb hlb hlw (fun f hfe _ hf => ?_) ?_ ?_
          · simp only [List.mem_append, List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] at hf ⊢
            tauto
          · simp
          · simp
  · by_cases hxe : x = S.e
    · subst hxe
      refine iff_of_true (by simp) ⟨p1, ?_, ?_⟩ <;> rw [p2] <;> dsimp only
      · exact (hZint _).2 ⟨ha, hla⟩
      · exact (hZint _).2 ⟨S.hw, hlw⟩
    by_cases hxe' : x = S.e'
    · subst hxe'
      refine iff_of_true (by simp) ⟨p3, ?_, ?_⟩ <;> rw [p4] <;> dsimp only
      · exact (hZint _).2 ⟨S.hw, hlw⟩
      · exact (hZint _).2 ⟨hb, hlb⟩
    rw [← adj_ip hZ hB x hxe hxe', ← hmem]
    simp [hxe, hxe']

end Beta

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-- Adjacent members, case (γ): `e` joins `p` in the component `s` to `q` in the component
`s + 1`; after the operation `y` is the edge from `p` to `w` and `z` the edge from `w` to `q`. -/
structure CaseG (S : SC G) (s : ℕ) (y z : E) (p q : V) : Prop where
  hs : s < S.k
  hyz : (y = S.e ∧ z = S.e') ∨ (y = S.e' ∧ z = S.e)
  hp : p ∈ G.int
  hlp : S.lev p = s
  hq : q ∈ G.int
  hlq : S.lev q = s + 1
  hy : SameEnds (S.Gt.ends y) (p, S.w)
  hz : SameEnds (S.Gt.ends z) (S.w, q)
  hev : SameEnds (G.ends S.e) (p, q)

section CaseG

variable {s : ℕ} {y z : E} {p q : V} (hC : S.CaseG s y z p q)
include hC

private theorem CaseG.pP : p ∉ S.P (s + 1) ∧ q ∈ S.P (s + 1) := by
  have hs := hC.hs
  have hlp := hC.hlp
  have hlq := hC.hlq
  exact ⟨fun h => by have := ((S.mem_P hs _).1 h).2; omega, (S.mem_P hs _).2 ⟨hC.hq, by omega⟩⟩

/-- In case (γ), `e` is the crossing edge `cc' s` of `G`. -/
private theorem CaseG.e_eq : S.e = S.cc' s := by
  have hs := hC.hs
  obtain ⟨hpP, hqP⟩ := hC.pP
  have hc : G.Crosses (S.P (s + 1)) S.e := by
    refine ⟨by rw [S.ce]; simp, by rw [S.ce]; simp, ?_, ?_, ?_⟩
    · rcases sameEnds_iff.1 hC.hev with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      exacts [Or.inl hC.hp, Or.inl hC.hq]
    · rcases sameEnds_iff.1 hC.hev with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
      exacts [Or.inl hC.hq, Or.inl hC.hp]
    · rcases sameEnds_iff.1 hC.hev with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [MGraph.Cut, h1, h2] <;>
        dsimp only
      · exact Or.inr ⟨hpP, hqP⟩
      · exact Or.inl ⟨hqP, hpP⟩
  rcases (S.cross s hs S.e).1 hc with h | h
  · exact absurd h (S.e_ne_cc hs)
  · exact h

private theorem CaseG.y_cls : S.Gt.cls y = some .plus ∧ S.Gt.cls z = some .plus := by
  rcases hC.hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by rw [split_cls_of S.hne, S.ce], by rw [split_cls_e', S.ce]⟩
  · exact ⟨by rw [split_cls_e', S.ce], by rw [split_cls_of S.hne, S.ce]⟩

private theorem CaseG.yz_ne : y ≠ z ∧ (∀ x, x = y ∨ x = z ↔ x = S.e ∨ x = S.e') := by
  rcases hC.hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨S.hne, fun x => Iff.rfl⟩
  · exact ⟨S.hne.symm, fun x => or_comm⟩

private theorem CaseG.ne_cc : y ≠ S.cc s ∧ z ≠ S.cc s := by
  have hs := hC.hs
  rcases hC.hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨S.e_ne_cc hs, S.e'_ne_cc hs⟩
  · exact ⟨S.e'_ne_cc hs, S.e_ne_cc hs⟩

/-- The outer ends of the crossing edges of `P (s + 1)`. -/
private theorem CaseG.outer : S.Gt.outer (S.P (s + 1)) (S.cc s) = S.u s ∧
    G.outer (S.P (s + 1)) (S.cc' s) = p := by
  have hs := hC.hs
  obtain ⟨hpP, hqP⟩ := hC.pP
  refine ⟨by unfold MGraph.outer; rw [split_ends_ne (S.e_ne_cc hs).symm (S.e'_ne_cc hs).symm]; rfl,
    ?_⟩
  rw [← hC.e_eq]; unfold MGraph.outer
  rcases sameEnds_iff.1 hC.hev with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · simp [hpP]
  · simp [hqP]

/-- The edges of `G` inside the component `s`. -/
private theorem CaseG.inner {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z s s x₁ x₂) {f : E}
    (hf : G.cls f ≠ none) (a1 : (G.ends f).1 ∈ G.int) (a2 : S.lev (G.ends f).1 = s)
    (b1 : (G.ends f).2 ∈ G.int) (b2 : S.lev (G.ends f).2 = s) :
    f ≠ S.e ∧ f ≠ S.e' ∧ f ≠ S.cc s ∧ f ≠ S.cc' s ∧ f ≠ y ∧ f ≠ z ∧ Z.ends f = G.ends f ∧
      Z.cls f = G.cls f := by
  have hs := hC.hs
  have he := hC.e_eq
  obtain ⟨-, hmem⟩ := hC.yz_ne
  have hfc' : f ≠ S.cc' s := by
    rintro rfl; obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hs (Or.inr rfl); omega
  have hfe : f ≠ S.e := by rw [he]; exact hfc'
  have hfe' : f ≠ S.e' := by rintro rfl; exact hf S.ce'
  have hfc : f ≠ S.cc s := by
    rintro rfl; obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hs (Or.inl rfl); omega
  have hfyz : f ≠ y ∧ f ≠ z := by
    constructor <;> intro h <;> rcases (hmem f).1 (by tauto) with h' | h'
    all_goals first | exact hfe h' | exact hfe' h'
  obtain ⟨z1, z2⟩ := hZ.edge hfe hfe' a1 (by omega) (by omega) b1 (by omega) (by omega)
  exact ⟨hfe, hfe', hfc, hfc', hfyz.1, hfyz.2, z1, z2⟩

/-- The internal blue solid edges of a graph of the component `s` before the operation: not `e`,
`e'`. -/
private theorem CaseG.ipB {B : MGraph V E} {x₁ x₂ : E} (hB : S.IsB B s x₁ x₂) (x : E)
    (hx : x = S.e ∨ x = S.e') : ¬ B.IsIntPlus x := by
  have hs := hC.hs
  intro h
  obtain ⟨c, a1, a2, b1, b2⟩ := (hB.ip x).1 h
  rcases hx with rfl | rfl
  · rw [hC.e_eq] at a2 b2
    obtain ⟨-, -, h⟩ := S.toSplitCtx.cc_lev hs (Or.inr rfl); omega
  · rw [S.ce'] at c; cases c

/-- The graph of the component `s` before the operation with the crossing edge `x₁` of `P (s + 1)`
carrying the `Θ` edge. -/
private theorem CaseG.repl {x₁ x₂ : E} (hx : (x₁ = S.cc s ∧ x₂ = S.cc' s) ∨ (x₁ = S.cc' s ∧ x₂ = S.cc s)) :
    S.IsB (G.replace (S.P s) (S.P (s + 1)) x₁ x₂) s x₁ x₂ ∧
      (G.replace (S.P s) (S.P (s + 1)) x₁ x₂).PreDet := by
  have hs := hC.hs
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨S.isB_replace hs (Or.inl rfl) (Or.inr rfl) (S.cc_ne s hs),
      S.preDet_replace hs (Or.inl rfl) (Or.inr rfl) (S.cc_ne s hs)⟩
  · exact ⟨S.isB_replace hs (Or.inr rfl) (Or.inl rfl) (S.cc_ne s hs).symm,
      S.preDet_replace hs (Or.inr rfl) (Or.inl rfl) (S.cc_ne s hs).symm⟩

/-- The internal blue solid edges of the graphs of the component `s` before and after the
operation agree, except for the edges `e`, `e'`. -/
private theorem CaseG.ip {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E}
    {x₁' x₂' : E} (hB : S.IsB B s x₁' x₂') (x : E) (hxe : x ≠ S.e) (hxe' : x ≠ S.e') :
    B.IsIntPlus x ↔ Z.IsIntPlus x := by
  rw [hB.ip, hZ.intPlus x hxe hxe']
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, by omega, by omega, h4, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨h1, h2, by omega, h5, by omega⟩

/-- Case (γ) with `w` in `P (s + 1)`: the graph of the component `s` after the operation is that
before it, with `y` in place of `cc' s`. -/
private theorem CaseG.preDet2 (hlw : s + 1 ≤ S.lev S.w) {Z : MGraph V E} {x₁ x₂ : E}
    (hZ : S.IsX Z s s x₁ x₂) (hx12 : (x₁ = S.cc s ∧ x₂ = y) ∨ (x₁ = y ∧ x₂ = S.cc s)) :
    Z.PreDet := by
  have hs := hC.hs
  obtain ⟨hpP, hqP⟩ := hC.pP
  have wP : S.w ∈ S.P (s + 1) := (S.mem_P hs _).2 ⟨S.hw, hlw⟩
  have wZ : S.w ∉ Z.int := fun h => by have := ((hZ.int _).1 h).2.2; omega
  have oy : S.Gt.outer (S.P (s + 1)) y = p := by
    unfold MGraph.outer
    rcases sameEnds_iff.1 hC.hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · simp [hpP]
    · simp [wP]
  obtain ⟨oc, oe⟩ := hC.outer
  obtain ⟨hyz, hmem⟩ := hC.yz_ne
  obtain ⟨ync, znc⟩ := hC.ne_cc
  obtain ⟨n12, t1, t2, t3, -, -⟩ := hZ.th hs
  -- `z` is not an edge of the graph
  have hzZ : ¬ Z.IsIntPlus z := by
    have hn : s < S.k → z ≠ x₁ ∧ z ≠ x₂ := fun _ => by
      rcases hx12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨znc, hyz.symm⟩
      · exact ⟨hyz.symm, znc⟩
    obtain ⟨g1, -⟩ := hZ.gen z hn
    rintro ⟨-, h1, h2⟩
    rw [g1] at h1 h2
    rcases sameEnds_iff.1 hC.hz with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1] at h1; exact wZ h1
    · rw [e2] at h2; exact wZ h2
  have hyZ : ¬ Z.IsIntPlus y := by
    rintro ⟨h, -⟩
    rcases hx12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [t2] at h; cases h
    · rw [t1] at h; cases h
  have hipZ : ∀ x, x = S.e ∨ x = S.e' → ¬ Z.IsIntPlus x := by
    intro x hx
    rcases (hmem x).2 hx with rfl | rfl
    · exact hyZ
    · exact hzZ
  have hint : ∀ {B : MGraph V E} {x₁' x₂' : E}, S.IsB B s x₁' x₂' → B.int = Z.int := by
    intro B x₁' x₂' hB
    ext v; rw [hB.int, hZ.int]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩⟩
  rcases hx12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst x₁; subst x₂
    obtain ⟨hB, hBpd⟩ := hC.repl (Or.inl ⟨rfl, rfl⟩)
    refine preDet_transfer (σ := id) Function.injective_id hBpd ⟨hint hB, fun f hf => ?_⟩
      (fun _ _ => rfl) (fun x => ?_)
    · simp only [id]
      rcases hB.pres f hf.1 with ⟨-, rfl, hc, hen⟩ | ⟨-, a1, a2, b1, b2, hc, hen⟩
      · refine ⟨Or.inl (t1.trans hc.symm), ?_⟩
        rw [t3, hen, oc, oy, oe]; exact sameEnds_refl _
      · obtain ⟨-, -, -, -, -, -, z1, z2⟩ := hC.inner hZ (by rw [← hc]; exact hf.1) a1 a2 b1 b2
        exact ⟨Or.inl (z2.trans hc.symm), by rw [z1, hen]; exact sameEnds_refl _⟩
    · by_cases hx : x = S.e ∨ x = S.e'
      · exact iff_of_false (hC.ipB hB x hx) (hipZ x hx)
      · rw [not_or] at hx; exact hC.ip hZ hB x hx.1 hx.2
  · subst x₁; subst x₂
    obtain ⟨hB, hBpd⟩ := hC.repl (Or.inr ⟨rfl, rfl⟩)
    have he := hC.e_eq
    have hσ : ∀ f, f ≠ S.e → f ≠ y → Equiv.swap S.e y f = f :=
      fun f h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
    refine preDet_transfer (σ := Equiv.swap S.e y) (Equiv.injective _) hBpd
      ⟨hint hB, fun f hf => ?_⟩ (fun f hf => ?_) (fun x => ?_)
    · rcases hB.pres f hf.1 with ⟨-, rfl, hc, hen⟩ | ⟨-, a1, a2, b1, b2, hc, hen⟩
      · rw [← he, Equiv.swap_apply_left]
        refine ⟨Or.inl (t1.trans (by rw [he]; exact hc.symm)), ?_⟩
        rw [t3, oc, oy, he, hen, oe]; exact sameEnds_refl _
      · obtain ⟨n1, -, -, -, n2, -, z1, z2⟩ :=
          hC.inner hZ (by rw [← hc]; exact hf.1) a1 a2 b1 b2
        rw [hσ f n1 n2]
        exact ⟨Or.inl (z2.trans hc.symm), by rw [z1, hen]; exact sameEnds_refl _⟩
    · rcases hB.pres f (by rw [hf]; simp) with ⟨-, -, hc, -⟩ | ⟨-, a1, a2, b1, b2, hc, -⟩
      · rw [hc] at hf; cases hf
      · obtain ⟨n1, -, -, -, n2, -, -⟩ :=
          hC.inner hZ (by rw [← hc, hf]; simp) a1 a2 b1 b2
        exact hσ f n1 n2
    · by_cases hx : x = S.e ∨ x = S.e'
      · exact iff_of_false (hC.ipB hB x hx) (hipZ x hx)
      · rw [not_or] at hx; exact hC.ip hZ hB x hx.1 hx.2

/-- Case (γ) with `w` in the component `s`: the edges of the graph of the component `s` before the
operation, other than its `Θ` edge, are edges after it. -/
private theorem CaseG.pathRel {Z : MGraph V E} {x₁ x₂ : E} (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E}
    {x₁' x₂' : E} (hB : S.IsB B s x₁' x₂') (m : List E) :
    ∀ f, (B.convert m).Pres f → f ≠ x₁' → ((Z.convert ([y] ++ m)).cls f = (B.convert m).cls f ∨
      ((B.convert m).cls f = some .plus ∧ (Z.convert ([y] ++ m)).cls f = some .diff)) ∧
      SameEnds ((Z.convert ([y] ++ m)).ends f) ((B.convert m).ends f) := by
  intro f hf hfx
  rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨-, h, -⟩ | ⟨-, a1, a2, b1, b2, hc, hen⟩
  · exact absurd h hfx
  · obtain ⟨-, -, -, -, n, -, z1, z2⟩ :=
      hC.inner hZ (by rw [← hc]; exact convert_ne_none.1 hf.1) a1 a2 b1 b2
    refine ⟨Or.inl ?_, by rw [convert_ends, convert_ends, z1, hen]; exact sameEnds_refl _⟩
    rw [convert_cls, convert_cls, z2, hc]
    simp [n]

/-- Case (γ) with `w` in the component `s`: the edge `y` inside the component is redundant first,
then the pre-deterministic order of the component before the operation follows, its `Θ` edge
replaced by the path through `w`. -/
private theorem CaseG.preDet1 (hlw : S.lev S.w = s) {Z : MGraph V E} {x₁ x₂ : E}
    (hZ : S.IsX Z s s x₁ x₂) (hx12 : (x₁ = S.cc s ∧ x₂ = z) ∨ (x₁ = z ∧ x₂ = S.cc s)) :
    Z.PreDet := by
  have hs := hC.hs
  have hlp := hC.hlp
  obtain ⟨hpP, hqP⟩ := hC.pP
  have wP : S.w ∉ S.P (s + 1) := fun h => by have := ((S.mem_P hs _).1 h).2; omega
  have oz : S.Gt.outer (S.P (s + 1)) z = S.w := by
    unfold MGraph.outer
    rcases sameEnds_iff.1 hC.hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · simp [wP]
    · simp [hqP]
  obtain ⟨oc, oe⟩ := hC.outer
  obtain ⟨hyz, hmem⟩ := hC.yz_ne
  obtain ⟨ync, znc⟩ := hC.ne_cc
  obtain ⟨yc, -⟩ := hC.y_cls
  obtain ⟨n12, t1, t2, t3, -, -⟩ := hZ.th hs
  have hZint : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ S.lev v = s := fun v => by
    rw [hZ.int]; exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
  -- the edge `y`
  have hyZ : Z.ends y = S.Gt.ends y ∧ Z.cls y = S.Gt.cls y := by
    have hp : (S.Gt.ends y).1 ∈ G.int ∧ s ≤ S.lev (S.Gt.ends y).1 ∧ S.lev (S.Gt.ends y).1 ≤ s ∧
        (S.Gt.ends y).2 ∈ G.int ∧ s ≤ S.lev (S.Gt.ends y).2 ∧ S.lev (S.Gt.ends y).2 ≤ s := by
      rcases sameEnds_iff.1 hC.hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> dsimp only
      · exact ⟨hC.hp, by omega, by omega, S.hw, by omega, by omega⟩
      · exact ⟨S.hw, by omega, by omega, hC.hp, by omega, by omega⟩
    obtain ⟨a1, a2, a3, b1, b2, b3⟩ := hp
    exact hZ.gedge a1 a2 a3 b1 b2 b3
  have yZc : Z.cls y = some .plus := hyZ.2.trans yc
  have yZe : SameEnds (Z.ends y) (p, S.w) := hyZ.1 ▸ hC.hy
  have yip : Z.IsIntPlus y := by
    refine ⟨yZc, ?_⟩
    rcases sameEnds_iff.1 yZe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact ⟨(hZint _).2 ⟨hC.hp, hlp⟩, (hZint _).2 ⟨S.hw, hlw⟩⟩
    · exact ⟨(hZint _).2 ⟨S.hw, hlw⟩, (hZint _).2 ⟨hC.hp, hlp⟩⟩
  have hzZ : ¬ Z.IsIntPlus z := by
    rintro ⟨h, -⟩
    rcases hx12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h2, t2] at h; cases h
    · rw [← h1, t1] at h; cases h
  -- the subgraph induced on the component `s`
  have hle : Le (G.induce (S.Lvl s (s + 1))) (Z.erase y) := by
    refine ⟨?_, fun f hf => ?_⟩
    · ext v
      change v ∈ S.Lvl s (s + 1) ↔ v ∈ (Z.erase y).int
      rw [erase_int, S.mem_Lvl, hZint]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
    · obtain ⟨hc, -⟩ := hf
      have hin : (G.ends f).1 ∈ S.Lvl s (s + 1) ∧ (G.ends f).2 ∈ S.Lvl s (s + 1) := by
        by_contra hn
        simp [MGraph.induce, hn] at hc
      have hG : (G.induce (S.Lvl s (s + 1))).cls f = G.cls f := by
        simp [MGraph.induce, hin]
      rw [hG] at hc
      obtain ⟨a1, a2, a3⟩ := S.mem_Lvl.1 hin.1
      obtain ⟨b1, b2, b3⟩ := S.mem_Lvl.1 hin.2
      obtain ⟨-, -, -, -, n, -, z1, z2⟩ := hC.inner hZ hc a1 (by omega) b1 (by omega)
      simp only [id]
      rw [erase_cls, if_neg n, hG, erase_ends, z1]
      exact ⟨Or.inl z2, sameEnds_refl _⟩
  have hD := S.toSplitCtx.dc_Lvl' s (s + 1)
  have hZdc : Z.DC := dc_le hD (le_trans' hle (le_erase_self Z y))
  have stepY : Z.IsRedundant y := ⟨yZc, hZdc, dc_le hD hle⟩
  -- the graph before the operation
  obtain ⟨x₁', x₂', hx', hg⟩ : ∃ x₁' x₂' : E,
      ((x₁' = S.cc s ∧ x₂' = S.cc' s) ∨ (x₁' = S.cc' s ∧ x₂' = S.cc s)) ∧
      ∃ g₁ g₂ : E, ((g₁ = x₁ ∧ g₂ = y) ∨ (g₁ = y ∧ g₂ = x₁)) ∧
        SameEnds (Z.ends g₁) (G.outer (S.P (s + 1)) x₁', S.w) ∧
        SameEnds (Z.ends g₂) (S.w, G.outer (S.P (s + 1)) x₂') := by
    rcases hx12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst x₁; subst x₂
      refine ⟨S.cc s, S.cc' s, Or.inl ⟨rfl, rfl⟩, S.cc s, y, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [t3, oc, oz]; exact sameEnds_refl _
      · rw [oe]; exact yZe.trans (sameEnds_swap (S.w, p) : SameEnds (p, S.w) (S.w, p))
    · subst x₁; subst x₂
      refine ⟨S.cc' s, S.cc s, Or.inr ⟨rfl, rfl⟩, y, z, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [oe]; exact yZe
      · rw [t3, oz, oc]; exact sameEnds_refl _
  obtain ⟨g₁, g₂, hg12, s1, s2⟩ := hg
  obtain ⟨hB, hBpd⟩ := hC.repl hx'
  obtain ⟨-, ℓ, -, hmemℓ, hst⟩ := hBpd
  have hBint : (G.replace (S.P s) (S.P (s + 1)) x₁' x₂').int = Z.int := by
    ext v; rw [hB.int, hZint]
  have hBx : (G.replace (S.P s) (S.P (s + 1)) x₁' x₂').cls x₁' = some .diff ∧
      (G.replace (S.P s) (S.P (s + 1)) x₁' x₂').ends x₁' =
        (G.outer (S.P (s + 1)) x₁', G.outer (S.P (s + 1)) x₂') := by
    simp [MGraph.replace]
  have hx1c : Z.cls x₁ = some .diff := t1
  have hgc : ∀ m : List E, (Z.convert ([y] ++ m)).cls g₁ = some .diff ∧
      (Z.convert ([y] ++ m)).cls g₂ = some .diff := by
    intro m
    have hy' : (Z.convert ([y] ++ m)).cls y = some .diff := by
      rw [convert_cls, if_pos ⟨by simp, yZc⟩]
    have hx' : (Z.convert ([y] ++ m)).cls x₁ = some .diff := by
      rw [convert_cls, hx1c]; simp
    rcases hg12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx', hy'⟩
    · exact ⟨hy', hx'⟩
  -- the internal blue solid edges of the graph before the operation
  have hℓ : ∀ f ∈ ℓ, f ≠ S.e ∧ f ≠ S.e' ∧ f ≠ S.cc s ∧ f ≠ S.cc' s ∧ f ≠ y ∧ f ≠ z ∧
      Z.cls f = some .plus ∧ (G.replace (S.P s) (S.P (s + 1)) x₁' x₂').cls f = some .plus := by
    intro f hf
    have hip := (hmemℓ f).1 hf
    obtain ⟨c, a1, a2, b1, b2⟩ := (hB.ip f).1 hip
    obtain ⟨n1, n2, n3, n4, n5, n6, -, z2⟩ := hC.inner hZ (by rw [c]; simp) a1 a2 b1 b2
    exact ⟨n1, n2, n3, n4, n5, n6, z2.trans c, hip.1⟩
  have hgx : ∀ f, f ≠ S.cc s → f ≠ S.cc' s → f ≠ y → f ≠ z → f ≠ x₁' ∧ f ≠ g₁ ∧ f ≠ g₂ := by
    intro f h1 h2 h3 h4
    have hx1 : f ≠ x₁ := by
      rcases hx12 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [h1, h4]
    refine ⟨?_, ?_, ?_⟩
    · rcases hx' with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [h1, h2]
    · rcases hg12 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [hx1, h3]
    · rcases hg12 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]; exacts [h3, hx1]
  refine preDet_of_steps hZdc (l := y :: ℓ) (steps_cons.2 ⟨stepY, ?_⟩) (fun x => ?_)
  · refine steps_pathE (R := G.replace (S.P s) (S.P (s + 1)) x₁' x₂') (X := Z.convert [y])
      (w := S.w) (g := x₁') (g₁ := g₁) (g₂ := g₂) (by rw [hBint, hZint]; exact ⟨S.hw, hlw⟩)
      (by rw [convert_int, hBint]) (fun t ht => hst t ht) (fun f hf => ?_) (fun t _ => ?_)
    · obtain ⟨n1, n2, n3, n4, n5, n6, c1, c2⟩ := hℓ f hf
      obtain ⟨m1, m2, m3⟩ := hgx f n3 n4 n5 n6
      refine ⟨m1, m2, m3, ?_⟩
      rw [convert_cls, if_neg (by simp [n5]), c1, c2]
    · rw [convert_convert']
      refine ⟨hC.pathRel hZ hB _, fun hp => ⟨?_, ?_, ?_, ?_, fun f hf hfx => ?_⟩⟩
      · rw [(hgc _).1, convert_cls, hBx.1]; simp
      · rw [(hgc _).2, convert_cls, hBx.1]; simp
      · rw [convert_ends, convert_ends, hBx.2]; exact s1
      · rw [convert_ends, convert_ends, hBx.2]; exact s2
      · rcases hB.pres f (convert_ne_none.1 hf.1) with ⟨-, h, -⟩ | ⟨-, a1, a2, b1, b2, hc, -⟩
        · exact absurd h hfx
        · obtain ⟨-, -, n3, n4, n5, n6, -⟩ :=
            hC.inner hZ (by rw [← hc]; exact convert_ne_none.1 hf.1) a1 a2 b1 b2
          exact (hgx f n3 n4 n5 n6).2
  · rw [List.mem_cons]
    by_cases hxy : x = y
    · subst hxy; exact iff_of_true (Or.inl rfl) yip
    by_cases hxz : x = z
    · subst hxz
      refine iff_of_false (fun h => ?_) hzZ
      rcases h with h | h
      · exact hyz h.symm
      · exact (hℓ x h).2.2.2.2.2.1 rfl
    have hx : x ≠ S.e ∧ x ≠ S.e' := by
      constructor <;> intro h <;> rcases (hmem x).2 (by tauto) with h' | h'
      all_goals first | exact hxy h' | exact hxz h'
    rw [← hC.ip hZ hB x hx.1 hx.2, ← hmemℓ]
    simp [hxy]

end CaseG

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-- The positions of the ends of `e` in the chain: one component, two consecutive components, or
an end that is not internal and the other end in the component `0`. -/
private theorem e_class (hva : G.IsVtx (G.ends S.e).1) (hvb : G.IsVtx (G.ends S.e).2)
    (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int) :
    ((G.ends S.e).1 ∈ G.int ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).1 = S.lev (G.ends S.e).2) ∨
    ((G.ends S.e).1 ∈ G.int ∧ (G.ends S.e).2 ∈ G.int ∧ ∃ i < S.k,
      (S.lev (G.ends S.e).1 = i ∧ S.lev (G.ends S.e).2 = i + 1) ∨
      (S.lev (G.ends S.e).1 = i + 1 ∧ S.lev (G.ends S.e).2 = i)) ∨
    ((G.ends S.e).1 ∉ G.int ∧ (G.ends S.e).2 ∈ G.int ∧ S.lev (G.ends S.e).2 = 0) ∨
    ((G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = 0 ∧ (G.ends S.e).2 ∉ G.int) := by
  -- an internal end outside the component `0` and an end that is not internal: `e` crosses `P 1`
  have key : ∀ t v : V, t ∈ G.int → v ∉ G.int → SameEnds (G.ends S.e) (t, v) → S.lev t = 0 := by
    intro t v ht hv hse
    by_contra h0
    have hk : 0 < S.k := by have := S.lev_le t; omega
    have htP : t ∈ S.P (0 + 1) := (S.mem_P hk _).2 ⟨ht, by omega⟩
    have hvP : v ∉ S.P (0 + 1) := fun h => hv ((S.mem_P hk _).1 h).1
    have hc : G.Crosses (S.P (0 + 1)) S.e := by
      refine ⟨by rw [S.ce]; simp, by rw [S.ce]; simp, hva, hvb, ?_⟩
      unfold MGraph.Cut
      rcases sameEnds_iff.1 hse with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> dsimp only
      · exact Or.inl ⟨htP, hvP⟩
      · exact Or.inr ⟨hvP, htP⟩
    obtain ⟨u, hu, -, ho, -, hse'⟩ := S.cc_ends' hk ((S.cross 0 hk S.e).1 hc)
    have hm := (hse'.mem (S := G.int)).2 ⟨ho, hu⟩
    have hm' := (hse.mem (S := G.int)).1 hm
    exact hv hm'.2
  by_cases ha : (G.ends S.e).1 ∈ G.int <;> by_cases hb : (G.ends S.e).2 ∈ G.int
  · rcases S.lev_plus S.ce ha hb with h | ⟨i, hi, -, h⟩
    · exact Or.inl ⟨ha, hb, h⟩
    · exact Or.inr (Or.inl ⟨ha, hb, i, hi, h⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨ha, key _ _ ha hb (sameEnds_refl _), hb⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, key _ _ hb ha (sameEnds_swap (G.ends S.e)).symm⟩))
  · rcases hab with h | h
    · exact absurd h ha
    · exact absurd h hb

/-- The crossing edges of `P (b + 1)` after operation (B), if the ends of `e` lie on one side of
`P (b + 1)` and `P (b + 1)` does not separate them from `w`: those of `G`. -/
private theorem cross_same {b : ℕ} (hb : b < S.k)
    (hab : (G.ends S.e).1 ∈ S.P (b + 1) ↔ (G.ends S.e).2 ∈ S.P (b + 1))
    (hsep : ¬ Sep G S.e S.w (S.P (b + 1))) (x : E) (hx : S.Gt.Crosses (S.P (b + 1)) x) :
    (x = S.cc b ∨ x = S.cc' b) ∧ x ≠ S.e ∧ x ≠ S.e' := by
  unfold Sep at hsep
  have hxe : x ≠ S.e := by
    rintro rfl
    obtain ⟨-, -, -, -, hcut⟩ := hx
    unfold MGraph.Cut at hcut
    rw [split_ends_e] at hcut
    dsimp only at hcut
    tauto
  have hxe' : x ≠ S.e' := by
    rintro rfl
    obtain ⟨-, -, -, -, hcut⟩ := hx
    unfold MGraph.Cut at hcut
    rw [split_ends_e' S.hne] at hcut
    dsimp only at hcut
    tauto
  exact ⟨(S.cross b hb x).1 ((split_crosses_ne hxe hxe').1 hx), hxe, hxe'⟩

section Adj

variable {s : ℕ} {Z : MGraph V E} {x₁ x₂ : E}

/-- Adjacent members: the graph of the component `s` after the operation is pre-deterministic, if
`w` lies in the component `s` when both ends of `e` do (cases (α), (β), (δ)). -/
private theorem adj_core (hZ : S.IsX Z s s x₁ x₂) {B : MGraph V E} (hB : S.IsB B s x₁ x₂)
    (hBpd : B.PreDet) (hx12 : s < S.k → x₁ ≠ S.e ∧ x₁ ≠ S.e' ∧ x₂ ≠ S.e ∧ x₂ ≠ S.e')
    (hβ : (G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = s ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = s → S.lev S.w = s) : Z.PreDet := by
  by_cases he : (G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = s ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = s
  · exact adj_beta hZ hB hBpd hx12 he.1 he.2.1 he.2.2.1 he.2.2.2 (hβ he)
  have hZi : ∀ v, v ∈ Z.int ↔ v ∈ G.int ∧ S.lev v = s := fun v => by
    rw [hZ.int]; exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
  have ge : S.Gt.ends S.e = ((G.ends S.e).1, S.w) := split_ends_e
  have ge' : S.Gt.ends S.e' = (S.w, (G.ends S.e).2) := split_ends_e' S.hne
  have both : ¬ (((S.Gt.ends S.e).1 ∈ Z.int ∧ (S.Gt.ends S.e).2 ∈ Z.int) ∧
      ((S.Gt.ends S.e').1 ∈ Z.int ∧ (S.Gt.ends S.e').2 ∈ Z.int)) := by
    rw [ge, ge']
    dsimp only
    simp only [hZi]
    rintro ⟨⟨⟨a1, a2⟩, -⟩, -, ⟨b1, b2⟩⟩
    exact he ⟨a1, a2, b1, b2⟩
  by_cases h1 : (S.Gt.ends S.e).1 ∈ Z.int ∧ (S.Gt.ends S.e).2 ∈ Z.int
  · refine adj_delta hZ hB hBpd hx12 he (Or.inl rfl) h1 (fun x hx hxε => ?_)
    rcases hx with rfl | rfl
    · exact absurd rfl hxε
    · exact fun h2 => both ⟨h1, h2⟩
  by_cases h2 : (S.Gt.ends S.e').1 ∈ Z.int ∧ (S.Gt.ends S.e').2 ∈ Z.int
  · refine adj_delta hZ hB hBpd hx12 he (Or.inr rfl) h2 (fun x hx hxε => ?_)
    rcases hx with rfl | rfl
    · exact h1
    · exact absurd rfl hxε
  exact adj_alpha hZ hB hBpd hx12 he (fun x hx => by rcases hx with rfl | rfl; exacts [h1, h2])

/-- Adjacent members, cases (α), (β), (δ): the clause of [II, Def 5.9 (iii)] for `P s`. -/
private theorem adj_clause (hs : s ≤ S.k) (hva : G.IsVtx (G.ends S.e).1) (hvb : G.IsVtx (G.ends S.e).2)
    (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int)
    (hsep : s < S.k → ¬ Sep G S.e S.w (S.P (s + 1)))
    (hsame : s < S.k → ((G.ends S.e).1 ∈ S.P (s + 1) ↔ (G.ends S.e).2 ∈ S.P (s + 1)))
    (hβ : (G.ends S.e).1 ∈ G.int ∧ S.lev (G.ends S.e).1 = s ∧ (G.ends S.e).2 ∈ G.int ∧
      S.lev (G.ends S.e).2 = s → S.lev S.w = s) :
    S.Gt.ClauseIII (S.P s) (chainNext S.k S.P s) :=
  clause_of_core le_rfl hs
    (fun hk => maxIso (Nat.lt_succ_self s) hk (hsep hk) (fun l h1 h2 => absurd h2 (by omega))
      hva hvb hab)
    (fun hk => cross_same hk (hsame hk) (hsep hk))
    (fun _ _ _ _ hZ hB hBpd hx12 => adj_core hZ hB hBpd hx12 hβ)

end Adj

section CaseG

variable {s : ℕ} {y z : E} {p q : V} (hC : S.CaseG s y z p q)
include hC

/-- The crossing edges of `P (s + 1)` in case (γ): `cc s` and the edge `r` of the path crossing
it. -/
private theorem CaseG.cross {r r' : E} (hrr : (r = y ∧ r' = z) ∨ (r = z ∧ r' = y))
    (hr : S.Gt.Cut (S.P (s + 1)) r) (hr' : ¬ S.Gt.Cut (S.P (s + 1)) r') (x : E) :
    S.Gt.Crosses (S.P (s + 1)) x ↔ x = S.cc s ∨ x = r := by
  have hs := hC.hs
  obtain ⟨yc, zc⟩ := hC.y_cls
  obtain ⟨-, hmem⟩ := hC.yz_ne
  have hrm : ∀ x, x = r ∨ x = r' ↔ x = y ∨ x = z := fun x => by
    rcases hrr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact or_comm
  constructor
  · intro hx
    by_cases hxyz : x = y ∨ x = z
    · rcases (hrm x).2 hxyz with h | h
      · exact Or.inr h
      · subst h; exact absurd hx.2.2.2.2 hr'
    · rw [not_or] at hxyz
      have hxe : x ≠ S.e ∧ x ≠ S.e' := by
        constructor <;> intro h <;> exact (hmem x).2 (by tauto) |>.elim hxyz.1 hxyz.2
      rcases (S.cross s hs x).1 ((split_crosses_ne hxe.1 hxe.2).1 hx) with h | h
      · exact Or.inl h
      · exact absurd (h.trans hC.e_eq.symm) hxe.1
  · rintro (rfl | rfl)
    · have hne : S.cc s ≠ S.e ∧ S.cc s ≠ S.e' :=
        ⟨(S.e_ne_cc hs).symm, (S.e'_ne_cc hs).symm⟩
      exact (split_crosses_ne hne.1 hne.2).2 ((S.cross s hs _).2 (Or.inl rfl))
    · have hc : S.Gt.cls x = some .plus := by
        rcases (hrm x).1 (Or.inl rfl) with h | h <;> rw [h]; exacts [yc, zc]
      have hin : (S.Gt.ends x).1 ∈ G.int ∧ (S.Gt.ends x).2 ∈ G.int := by
        rcases (hrm x).1 (Or.inl rfl) with h | h <;> rw [h]
        · exact (hC.hy.mem (S := G.int)).2 ⟨hC.hp, S.hw⟩
        · exact (hC.hz.mem (S := G.int)).2 ⟨S.hw, hC.hq⟩
      exact ⟨by rw [hc]; simp, by rw [hc]; simp, Or.inl hin.1, Or.inl hin.2, hr⟩

/-- **Case (γ)**: the clause of [II, Def 5.9 (iii)] for `P s`, with `e` crossing `P (s + 1)` and
`w` outside `P s \ P (s + 1)` only above it. -/
private theorem CaseG.clause (hlw : s ≤ S.lev S.w) (hva : G.IsVtx (G.ends S.e).1)
    (hvb : G.IsVtx (G.ends S.e).2) (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int) :
    S.Gt.ClauseIII (S.P s) (chainNext S.k S.P s) := by
  have hs := hC.hs
  obtain ⟨hpP, hqP⟩ := hC.pP
  have hsep : ¬ Sep G S.e S.w (S.P (s + 1)) := by
    unfold Sep
    rcases sameEnds_iff.1 hC.hev with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> dsimp only
    · rintro (⟨h1, -, -⟩ | ⟨-, h2, -⟩)
      exacts [hpP h1, h2 hqP]
    · rintro (⟨-, h1, -⟩ | ⟨h2, -, -⟩)
      exacts [hpP h1, h2 hqP]
  simp only [chainNext, hs, if_true, MGraph.ClauseIII]
  refine ⟨maxIso (Nat.lt_succ_self s) hs hsep (fun l h1 h2 => absurd h2 (by omega)) hva hvb hab,
    fun x₁ x₂ hne h1 h2 => ?_⟩
  have hZ := S.isX_replace le_rfl hs hne h1 h2
  have pair : ∀ r, (∀ x, S.Gt.Crosses (S.P (s + 1)) x ↔ x = S.cc s ∨ x = r) →
      (x₁ = S.cc s ∧ x₂ = r) ∨ (x₁ = r ∧ x₂ = S.cc s) := by
    intro r hcr
    rcases (hcr x₁).1 h1 with c1 | c1 <;> rcases (hcr x₂).1 h2 with c2 | c2
    · exact absurd (c1.trans c2.symm) hne
    · exact Or.inl ⟨c1, c2⟩
    · exact Or.inr ⟨c1, c2⟩
    · exact absurd (c1.trans c2.symm) hne
  by_cases hw : S.lev S.w = s
  · have wP : S.w ∉ S.P (s + 1) := fun h => by have := ((S.mem_P hs _).1 h).2; omega
    have hr : S.Gt.Cut (S.P (s + 1)) z := hC.hz.cut.2 (Or.inr ⟨wP, hqP⟩)
    have hr' : ¬ S.Gt.Cut (S.P (s + 1)) y := fun h => by
      rcases hC.hy.cut.1 h with ⟨h1, -⟩ | ⟨-, h2⟩
      exacts [hpP h1, wP h2]
    exact hC.preDet1 hw hZ (pair z (hC.cross (Or.inr ⟨rfl, rfl⟩) hr hr'))
  · have wP : S.w ∈ S.P (s + 1) := (S.mem_P hs _).2 ⟨S.hw, by omega⟩
    have hr : S.Gt.Cut (S.P (s + 1)) y := hC.hy.cut.2 (Or.inr ⟨hpP, wP⟩)
    have hr' : ¬ S.Gt.Cut (S.P (s + 1)) z := fun h => by
      rcases hC.hz.cut.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
      exacts [h2 hqP, h1 wP]
    exact hC.preDet2 (by omega) hZ (pair y (hC.cross (Or.inl ⟨rfl, rfl⟩) hr hr'))

end CaseG

/-- The separation property of the members of the chain by their components. -/
private theorem sep_P {l : ℕ} (hl : l ≤ S.k) : Sep G S.e S.w (S.P l) ↔
    (((G.ends S.e).1 ∈ G.int ∧ l ≤ S.lev (G.ends S.e).1) ∧
      ((G.ends S.e).2 ∈ G.int ∧ l ≤ S.lev (G.ends S.e).2) ∧ S.lev S.w < l) ∨
    (¬ ((G.ends S.e).1 ∈ G.int ∧ l ≤ S.lev (G.ends S.e).1) ∧
      ¬ ((G.ends S.e).2 ∈ G.int ∧ l ≤ S.lev (G.ends S.e).2) ∧ l ≤ S.lev S.w) := by
  unfold Sep
  rw [S.mem_P hl, S.mem_P hl, S.mem_P hl]
  simp only [S.hw, true_and, not_le]

end SC

namespace SC

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S : SC G}

/-- The clause of [II, Def 5.9 (iii)] after operation (B) for `P s` (with `s = 0` or `P s` not
separating the ends of `e` from `w`) and the member after `P b`, where `P (s + 1), …, P b` separate
the ends of `e` from `w` and `P (b + 1)` does not. -/
private theorem clause_main (hva : G.IsVtx (G.ends S.e).1) (hvb : G.IsVtx (G.ends S.e).2)
    (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int) {s b : ℕ} (hsb : s ≤ b)
    (hbk : b ≤ S.k) (h0 : s = 0 ∨ ¬ Sep G S.e S.w (S.P s))
    (hbet : ∀ l, s < l → l ≤ b → Sep G S.e S.w (S.P l))
    (hnext : b < S.k → ¬ Sep G S.e S.w (S.P (b + 1))) :
    S.Gt.ClauseIII (S.P s) (chainNext S.k S.P b) := by
  have hlwk := S.lev_le S.w
  have hlak := S.lev_le (G.ends S.e).1
  have hlbk := S.lev_le (G.ends S.e).2
  have F0 : 1 ≤ s → ¬ Sep G S.e S.w (S.P s) := fun h1 => h0.resolve_left (by omega)
  rcases e_class hva hvb hab with ⟨ha, hb, hl⟩ | ⟨ha, hb, i, hik, hl⟩ | ⟨ha, hb, hlb⟩ |
    ⟨ha, hla, hb⟩
  · -- both ends in one component
    have sepE : ∀ l ≤ S.k, (Sep G S.e S.w (S.P l) ↔
        (l ≤ S.lev (G.ends S.e).1 ∧ S.lev S.w < l) ∨
          (S.lev (G.ends S.e).1 < l ∧ l ≤ S.lev S.w)) := by
      intro l hl'
      rw [sep_P hl']
      simp only [ha, hb, true_and, not_le]
      rw [← hl]
      constructor <;> intro h <;> omega
    by_cases hbs : b = s
    · rw [hbs] at hnext hbk ⊢
      refine adj_clause hbk hva hvb hab hnext (fun hk => ?_) (fun ⟨_, h1, _, h2⟩ => ?_)
      · rw [mem_P_lev hk ha, mem_P_lev hk hb, hl]
      · by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := F0 (by omega); rw [sepE _ hbk] at this; omega
        · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
    · have hb1 := hbet (s + 1) (by omega) (by omega)
      rw [sepE _ (by omega)] at hb1
      rcases hb1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hlw : S.lev S.w = s := by
          by_contra hne
          have := F0 (by omega); rw [sepE _ (by omega)] at this; omega
        have hbe : b = S.lev (G.ends S.e).1 := by
          rcases lt_trichotomy b (S.lev (G.ends S.e).1) with h | h | h
          · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
          · exact h
          · have := hbet (S.lev (G.ends S.e).1 + 1) (by omega) (by omega)
            rw [sepE _ (by omega)] at this; omega
        rw [hbe]
        exact conj_ii (by omega) hlak hlw ha rfl hb hl.symm
      · have hla : S.lev (G.ends S.e).1 = s := by
          by_contra hne
          have := F0 (by omega); rw [sepE _ (by omega)] at this; omega
        have hbe : b = S.lev S.w := by
          rcases lt_trichotomy b (S.lev S.w) with h | h | h
          · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
          · exact h
          · have := hbet (S.lev S.w + 1) (by omega) (by omega)
            rw [sepE _ (by omega)] at this; omega
        rw [hbe]
        exact conj_i (by omega) hlwk rfl ha hla hb (hl ▸ hla)
  · -- the ends in two consecutive components
    have sepE : ∀ l ≤ S.k, (Sep G S.e S.w (S.P l) ↔
        (l ≤ S.lev (G.ends S.e).1 ∧ l ≤ S.lev (G.ends S.e).2 ∧ S.lev S.w < l) ∨
          (S.lev (G.ends S.e).1 < l ∧ S.lev (G.ends S.e).2 < l ∧ l ≤ S.lev S.w)) := by
      intro l hl'
      rw [sep_P hl']
      simp only [ha, hb, true_and, not_le]
    by_cases hbs : b = s
    · rw [hbs] at hnext hbk ⊢
      by_cases his : i = s
      · have hlw : s ≤ S.lev S.w := by
          by_contra hne
          have := F0 (by omega); rw [sepE _ hbk] at this; omega
        rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hC : S.CaseG s S.e S.e' (G.ends S.e).1 (G.ends S.e).2 :=
            ⟨by omega, Or.inl ⟨rfl, rfl⟩, ha, by omega, hb, by omega,
              by rw [split_ends_e]; exact sameEnds_refl _,
              by rw [split_ends_e' S.hne]; exact sameEnds_refl _, sameEnds_refl _⟩
          exact hC.clause hlw hva hvb hab
        · have hC : S.CaseG s S.e' S.e (G.ends S.e).2 (G.ends S.e).1 :=
            ⟨by omega, Or.inr ⟨rfl, rfl⟩, hb, by omega, ha, by omega,
              by rw [split_ends_e' S.hne]; exact sameEnds_swap ((G.ends S.e).2, S.w),
              by rw [split_ends_e]; exact sameEnds_swap (S.w, (G.ends S.e).1),
              (sameEnds_swap (G.ends S.e)).symm⟩
          exact hC.clause hlw hva hvb hab
      · refine adj_clause hbk hva hvb hab hnext (fun hk => ?_) (fun ⟨_, h1, _, h2⟩ => by omega)
        rw [mem_P_lev hk ha, mem_P_lev hk hb]
        constructor <;> intro h <;> omega
    · have hb1 := hbet (s + 1) (by omega) (by omega)
      rw [sepE _ (by omega)] at hb1
      rcases hb1 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · have hlw : S.lev S.w = s := by
          by_contra hne
          have := F0 (by omega); rw [sepE _ (by omega)] at this; omega
        have hbe : b = i := by
          rcases lt_trichotomy b i with h | h | h
          · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
          · exact h
          · have := hbet (i + 1) (by omega) (by omega)
            rw [sepE _ (by omega)] at this; omega
        have hcn : chainNext S.k S.P i = some (S.P (i + 1)) := by simp [chainNext, hik]
        rw [hbe, hcn]
        rcases hl with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact conj_iv (by omega) hik hlw ha e1 hb e2 (Or.inl rfl)
        · exact conj_iv (by omega) hik hlw hb e2 ha e1 (Or.inr rfl)
      · have hs' : s = i + 1 := by
          by_contra hne
          have := F0 (by omega); rw [sepE _ (by omega)] at this; omega
        have hbe : b = S.lev S.w := by
          rcases lt_trichotomy b (S.lev S.w) with h | h | h
          · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
          · exact h
          · have := hbet (S.lev S.w + 1) (by omega) (by omega)
            rw [sepE _ (by omega)] at this; omega
        rw [hbe, hs']
        rcases hl with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact (conj_iii (by omega) hlwk rfl ha e1 hb e2 (Or.inl rfl)).2
        · exact (conj_iii (by omega) hlwk rfl hb e2 ha e1 (Or.inr rfl)).2
  · -- the first end not internal
    have sepE : ∀ l ≤ S.k, (Sep G S.e S.w (S.P l) ↔ 1 ≤ l ∧ l ≤ S.lev S.w) := by
      intro l hl'
      rw [sep_P hl']
      simp only [ha, hb, false_and, true_and, not_false_eq_true, false_or, not_le, hlb]
      constructor <;> intro h <;> omega
    by_cases hbs : b = s
    · rw [hbs] at hnext hbk ⊢
      refine adj_clause hbk hva hvb hab hnext (fun hk => ?_) (fun ⟨h, _⟩ => absurd h ha)
      exact iff_of_false (not_mem_P_of_not_int hk ha) (by rw [mem_P_lev hk hb]; omega)
    · have hb1 := hbet (s + 1) (by omega) (by omega)
      rw [sepE _ (by omega)] at hb1
      have hs0 : s = 0 := by
        by_contra hne
        have := F0 (by omega); rw [sepE _ (by omega)] at this; omega
      have hbe : b = S.lev S.w := by
        rcases lt_trichotomy b (S.lev S.w) with h | h | h
        · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
        · exact h
        · have := hbet (S.lev S.w + 1) (by omega) (by omega)
          rw [sepE _ (by omega)] at this; omega
      rw [hbe, hs0]
      exact conj_t (t := (G.ends S.e).2) (v := (G.ends S.e).1) (by omega) hlwk rfl hb hlb
        (Or.inl ha) hva (Or.inr rfl)
  · -- the second end not internal
    have sepE : ∀ l ≤ S.k, (Sep G S.e S.w (S.P l) ↔ 1 ≤ l ∧ l ≤ S.lev S.w) := by
      intro l hl'
      rw [sep_P hl']
      simp only [ha, hb, false_and, true_and, not_false_eq_true, and_false, false_or, not_le, hla]
      constructor <;> intro h <;> omega
    by_cases hbs : b = s
    · rw [hbs] at hnext hbk ⊢
      refine adj_clause hbk hva hvb hab hnext (fun hk => ?_) (fun ⟨_, _, h, _⟩ => absurd h hb)
      exact iff_of_false (by rw [mem_P_lev hk ha]; omega) (not_mem_P_of_not_int hk hb)
    · have hb1 := hbet (s + 1) (by omega) (by omega)
      rw [sepE _ (by omega)] at hb1
      have hs0 : s = 0 := by
        by_contra hne
        have := F0 (by omega); rw [sepE _ (by omega)] at this; omega
      have hbe : b = S.lev S.w := by
        rcases lt_trichotomy b (S.lev S.w) with h | h | h
        · have := hnext (by omega); rw [sepE _ (by omega)] at this; omega
        · exact h
        · have := hbet (S.lev S.w + 1) (by omega) (by omega)
          rw [sepE _ (by omega)] at this; omega
      rw [hbe, hs0]
      exact conj_t (t := (G.ends S.e).1) (v := (G.ends S.e).2) (by omega) hlwk rfl ha hla
        (Or.inl hb) hvb (Or.inl rfl)

/-- The last member of a run of members separating the ends of `e` from `w` after `P s`. -/
private theorem exists_last {s : ℕ} (hs : s ≤ S.k) : ∃ b, s ≤ b ∧ b ≤ S.k ∧
    (∀ l, s < l → l ≤ b → Sep G S.e S.w (S.P l)) ∧
    (b < S.k → ¬ Sep G S.e S.w (S.P (b + 1))) := by
  classical
  have hex : ∃ l, s < l ∧ (S.k < l ∨ ¬ Sep G S.e S.w (S.P l)) :=
    ⟨S.k + 1, by omega, Or.inl (by omega)⟩
  have spec := Nat.find_spec hex
  have hle : Nat.find hex ≤ S.k + 1 := Nat.find_min' hex ⟨by omega, Or.inl (by omega)⟩
  refine ⟨Nat.find hex - 1, by omega, by omega, fun l h1 h2 => ?_, fun hb => ?_⟩
  · by_contra hn
    have := Nat.find_min' hex ⟨h1, Or.inr hn⟩
    omega
  · have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [he]
    rcases spec.2 with h | h
    · omega
    · exact h

/-- The isolated subsets after operation (B): the set of all internal vertices, or a member `P t`
of the chain with `t ≥ 1` not separating the ends of `e` from `w`. -/
private theorem iso_classify (hva : G.IsVtx (G.ends S.e).1) (hvb : G.IsVtx (G.ends S.e).2)
    (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int) {Q : Finset V}
    (hQ : S.Gt.IsIsolated Q) :
    Q = G.int ∨ ∃ t, 1 ≤ t ∧ t ≤ S.k ∧ Q = S.P t ∧ ¬ Sep G S.e S.w (S.P t) := by
  have hQint : Q ⊆ G.int := hQ.1
  by_cases hsep : Sep G S.e S.w Q
  · exact absurd hQ (not_iso_split S.hne S.hw S.ce S.ce' hva hvb hab S.spd.1 hQint hsep)
  · have hQG := (iso_split_iff S.hne S.hw S.ce S.ce' hva hvb hsep).1 hQ
    by_cases hQe : Q = G.int
    · exact Or.inl hQe
    · have hQp : G.IsProperIso G.int Q := ⟨hQG, Finset.ssubset_iff_subset_ne.2 ⟨hQint, hQe⟩⟩
      obtain ⟨l, hl1, hlk, rfl⟩ := chain_iso_eq S.chain S.spd.2.1 hQp
      exact Or.inr ⟨l, hl1, hlk, rfl, hsep⟩

/-- The sets of the clauses of [II, Def 5.9 (iii)] after operation (B): members `P s` of the chain
with `s = 0` or not separating the ends of `e` from `w`. -/
private theorem isoOrTop_P (hva : G.IsVtx (G.ends S.e).1) (hvb : G.IsVtx (G.ends S.e).2)
    (hab : (G.ends S.e).1 ∈ G.int ∨ (G.ends S.e).2 ∈ G.int) {T : Finset V}
    (hT : S.Gt.IsoOrTop T) :
    ∃ s, s ≤ S.k ∧ T = S.P s ∧ (s = 0 ∨ ¬ Sep G S.e S.w (S.P s)) := by
  have h0 : G.int = S.P 0 := S.chain.1.symm
  rcases hT with h | h
  · exact ⟨0, Nat.zero_le _, h.trans h0, Or.inl rfl⟩
  · rcases iso_classify hva hvb hab h with h' | ⟨t, -, htk, rfl, hsep⟩
    · exact ⟨0, Nat.zero_le _, h'.trans h0, Or.inl rfl⟩
    · exact ⟨t, htk, rfl, Or.inr hsep⟩

end SC

/-- **[II, Lemma 5.10 (B)]**, without ghost edges: operation (B) on a sequentially
pre-deterministic graph, the blue solid edge `e` between two vertices, at least one internal,
replaced by a path of two blue solid edges `e`, `e'` through an internal vertex `w`, gives a
sequentially pre-deterministic graph. -/
theorem MGraph.spd_split :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V),
    (∀ e₀ : E, G.cls e₀ ≠ some .ghost) → G.SPD → G.cls e = some .plus →
    G.IsVtx (G.ends e).1 → G.IsVtx (G.ends e).2 →
    ((G.ends e).1 ∈ G.int ∨ (G.ends e).2 ∈ G.int) → e ≠ e' → G.cls e' = none → w ∈ G.int →
    (G.split e e' w).SPD := by
  intro V E _ _ G e e' w hng hs he hva hvb hab hne he' hw
  obtain ⟨k, P, hc⟩ := exists_chain (G := G)
  obtain ⟨S, rfl, rfl, rfl, rfl, rfl⟩ := SC.exists_SC hng hs hc he hne he' hw
  have hP0 : S.P 0 = G.int := S.chain.1
  refine ⟨?_, fun Q₁ Q₂ h₁ h₂ => ?_, fun T hT hno => ?_, fun T Q e₁ e₂ hT hmax hne' c₁ c₂ => ?_⟩
  · -- doubly connected
    refine dc_pathE (g := S.e) (g₁ := S.e) (g₂ := S.e') S.spd.1 hw rfl (fun f hf hfe => ?_)
      (fun _ => ⟨split_cls_of S.hne, split_cls_e' G S.e S.e' S.w, by rw [split_ends_e]; exact sameEnds_refl _,
        by rw [split_ends_e' S.hne]; exact sameEnds_refl _, fun f hf hfe => ⟨hfe, ?_⟩⟩)
    · have hfe' : f ≠ S.e' := by rintro rfl; exact hf.1 S.ce'
      exact ⟨Or.inl (split_cls_ne hfe'), by rw [split_ends_ne hfe hfe']; exact sameEnds_refl _⟩
    · rintro rfl; exact hf.1 S.ce'
  · -- the proper isolated subsets form a chain
    have mem : ∀ Q, S.Gt.IsProperIso S.Gt.int Q → ∃ t, t ≤ S.k ∧ Q = S.P t := by
      intro Q hQ
      rcases SC.iso_classify hva hvb hab hQ.1 with h | ⟨t, -, htk, rfl, -⟩
      · exact absurd h hQ.2.ne
      · exact ⟨t, htk, rfl⟩
    obtain ⟨t₁, ht₁, rfl⟩ := mem Q₁ h₁
    obtain ⟨t₂, ht₂, rfl⟩ := mem Q₂ h₂
    rcases le_total t₁ t₂ with h | h
    · exact Or.inr (chain_anti S.chain h ht₂)
    · exact Or.inl (chain_anti S.chain h ht₁)
  · -- the subgraph induced on the minimal isolated subset
    obtain ⟨s, hsk, rfl, h0⟩ := SC.isoOrTop_P hva hvb hab hT
    obtain ⟨b, hsb, hbk, hbet, hnext⟩ := SC.exists_last (S := S) hsk
    have hcl := SC.clause_main hva hvb hab hsb hbk h0 hbet hnext
    by_cases hb : b < S.k
    · simp only [chainNext, hb, if_true, MGraph.ClauseIII] at hcl
      exact absurd hcl.1.1 (hno _)
    · simpa [chainNext, hb, MGraph.ClauseIII] using hcl
  · -- the replacements of the maximal isolated subsets
    obtain ⟨s, hsk, rfl, h0⟩ := SC.isoOrTop_P hva hvb hab hT
    obtain ⟨b, hsb, hbk, hbet, hnext⟩ := SC.exists_last (S := S) hsk
    have hcl := SC.clause_main hva hvb hab hsb hbk h0 hbet hnext
    rcases SC.iso_classify hva hvb hab hmax.1.1 with h | ⟨t, ht1, htk, rfl, hsep⟩
    · exfalso
      have := hmax.1.2
      rw [h] at this
      exact this.2 (by rw [← hP0]; exact chain_anti S.chain (Nat.zero_le s) hsk)
    have hst : s < t := by
      by_contra hn
      exact (Finset.ssubset_iff_subset_ne.1 hmax.1.2).2
        (Finset.Subset.antisymm hmax.1.2.1 (chain_anti S.chain (by omega) hsk))
    have hbt : b < t := by
      by_contra hn
      exact hsep (hbet t hst (by omega))
    have hb : b < S.k := by omega
    simp only [chainNext, hb, if_true, MGraph.ClauseIII] at hcl
    have hsub : S.P t ⊆ S.P (b + 1) := chain_anti S.chain (by omega) htk
    have heq : S.P t = S.P (b + 1) := by
      by_contra hn
      exact hmax.2 _ hcl.1.1 (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hn⟩)
    rw [heq] at c₁ c₂ ⊢
    exact hcl.2 e₁ e₂ hne' c₁ c₂

section Instances

end Instances

end RBM8D.Graphs
