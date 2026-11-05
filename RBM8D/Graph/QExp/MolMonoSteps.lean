import RBM8D.Graph.QExp.MolMono
import RBM8D.Graph.QExp.MainB
import RBM8D.Graph.Local.Strategy
import RBM8D.Graph.DotBlocks

/-!
# Crossing counts along the steps of the `Q`-expansions that change the blocks or add atoms

The steps of the construction of the `Q`-expansions of [II, §4.4] that change the blocks of
dotted edges or add an atom keep the molecular graph of the block reading (`Graph.toMG'`,
[II, Def 2.11]) from losing crossings, in the sense of `Graph.MolMono`:

* the dotted terms of `1 = 1_{u = v} + 1_{u ≠ v}`, of `1_{u ≠ v} = 1 - 1_{u = v}` and of the
  choices of `O_dot` ([II, Def 4.2]): molecules are joined, or an external atom is identified with
  an internal atom; the edges at that external atom then end at the molecule of its block, and the
  edge from that molecule to the external atom is added. Under the charge pattern of the block
  normal form, the clause on the external atoms and without ghost edges, the number of crossing
  edges with each external vertex counted once and the number of red crossing edges do not drop;
* `O_merge` ([II, Def 4.1]): the blocks are reindexed and the solid edges inside a block become
  weights; the molecular graph is kept, up to the edges between two external atoms of a block
  without internal atom;
* `O^{(x),1}_weight` ([I, Def 3.6 (i)]), [II, (4.23)] and [II, (4.24)] = [I, (3.13), (3.14)]
  inside `P_x` ([II, §4.4, Steps 2, 3]): the new atom is joined to `x` by a waved edge, ends of
  edges move inside the molecule of `x`, and the derivative terms replace an edge by a path through
  the molecule of `x`.

With the steps that keep the blocks this gives `Graph.MolMono` for every elementary step
`QElemStep` of a graph with the invariant `Graph.InvB'`, and along chains of such steps. This is
the observation in the proof of [II, Lemma 6.5 (4)] that the `Q`-expansions create no new
molecule and keep or subdivide the edges between molecules.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Comparison of lists of present edges -/

section ListTools

variable {V : Type} [DecidableEq V] (I X S : Finset V)

private theorem MolMonoSteps_tExtL_append (A B : List (V × V × MClass)) :
    MolMono_tExtL I X S (A ++ B) = MolMono_tExtL I X S A ∪ MolMono_tExtL I X S B := by
  ext a
  simp only [MolMono_mem_tExtL, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨ha, t, ht | ht, hc⟩
    · exact Or.inl ⟨ha, t, ht, hc⟩
    · exact Or.inr ⟨ha, t, ht, hc⟩
  · rintro (⟨ha, t, ht, hc⟩ | ⟨ha, t, ht, hc⟩)
    · exact ⟨ha, t, Or.inl ht, hc⟩
    · exact ⟨ha, t, Or.inr ht, hc⟩

private theorem MolMonoSteps_tExtL_perm {L L' : List (V × V × MClass)} (h : L.Perm L') :
    MolMono_tExtL I X S L = MolMono_tExtL I X S L' := by
  ext a
  simp only [MolMono_mem_tExtL, h.mem_iff]

/-- `MolMono_Local` is additive. -/
private theorem MolMonoSteps_local_append {A₁ A₂ B₁ B₂ : List (V × V × MClass)}
    (hA : MolMono_Local I X S A₁ A₂) (hB : MolMono_Local I X S B₁ B₂) :
    MolMono_Local I X S (A₁ ++ B₁) (A₂ ++ B₂) := by
  obtain ⟨hA₁, hA₂⟩ := hA
  obtain ⟨hB₁, hB₂⟩ := hB
  refine ⟨?_, ?_⟩
  · unfold MolMono_cIntL at *
    rw [List.countP_append, List.countP_append, MolMonoSteps_tExtL_append,
      MolMonoSteps_tExtL_append]
    have hsub : (MolMono_tExtL I X S A₁ ∪ MolMono_tExtL I X S B₁) \
        (MolMono_tExtL I X S A₂ ∪ MolMono_tExtL I X S B₂) ⊆
        (MolMono_tExtL I X S A₁ \ MolMono_tExtL I X S A₂) ∪
          (MolMono_tExtL I X S B₁ \ MolMono_tExtL I X S B₂) := by
      intro a ha
      simp only [Finset.mem_union, Finset.mem_sdiff] at ha ⊢
      tauto
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  · unfold MolMono_redL at *
    rw [List.countP_append, List.countP_append]
    omega

/-- `MolMono_Local` is invariant under permutations. -/
private theorem MolMonoSteps_local_perm {B₁ B₂ B₁' B₂' : List (V × V × MClass)}
    (h : MolMono_Local I X S B₁ B₂) (h₁ : B₁.Perm B₁') (h₂ : B₂.Perm B₂') :
    MolMono_Local I X S B₁' B₂' := by
  obtain ⟨ha, hb⟩ := h
  unfold MolMono_Local MolMono_cIntL MolMono_redL at *
  rw [← h₁.countP_eq, ← h₂.countP_eq, ← MolMonoSteps_tExtL_perm I X S h₁,
    ← MolMonoSteps_tExtL_perm I X S h₂, ← h₁.countP_eq, ← h₂.countP_eq]
  exact ⟨ha, hb⟩

private theorem MolMonoSteps_local_nil (B : List (V × V × MClass)) : MolMono_Local I X S [] B := by
  simp [MolMono_Local, MolMono_cIntL, MolMono_redL, MolMono_tExtL]

/-- An edge without exactly one end in `S` may be removed. -/
private theorem MolMonoSteps_local_nocut (t : V × V × MClass)
    (h : ¬ ((t.1 ∈ S ∧ t.2.1 ∉ S) ∨ (t.1 ∉ S ∧ t.2.1 ∈ S))) : MolMono_Local I X S [t] [] := by
  have h1 : ¬ MolMono_crossT I X S t := fun hc => h hc.2.2.2
  have h2 : ¬ MolMono_redT I X S t := fun hc => h hc.2.2.2
  have hT : MolMono_tExtL I X S [t] = ∅ := by
    ext a
    simp only [MolMono_mem_tExtL, List.mem_singleton, exists_eq_left, Finset.notMem_empty,
      iff_false]
    exact fun h' => h1 h'.2.1
  refine ⟨?_, ?_⟩
  · rw [hT]
    simp [MolMono_cIntL, h1]
  · simp [MolMono_redL, h2]

/-- The exchange of the classes `plus` and `minus` (the complex conjugation of solid edges). -/
private def MolMonoSteps_sw : MClass → MClass
  | .plus => .minus
  | .minus => .plus
  | m => m

private theorem MolMonoSteps_sw_sw (m : MClass) : MolMonoSteps_sw (MolMonoSteps_sw m) = m := by
  cases m <;> rfl

/-- The exchange of the classes `plus` and `minus` on a present edge. -/
private def MolMonoSteps_swT (t : V × V × MClass) : V × V × MClass :=
  (t.1, t.2.1, MolMonoSteps_sw t.2.2)

private theorem MolMonoSteps_opt_sw (u v : V) (m : MClass) :
    (MolMono_opt u v m).map MolMonoSteps_swT = MolMono_opt u v (MolMonoSteps_sw m) := by
  unfold MolMono_opt
  split_ifs <;> rfl

/-- The replacements of lists of present edges built from: keeping an edge, adding edges,
replacing an edge by a path of two edges of its class through an internal vertex, and removing
an edge that is a loop or joins two vertices that are not internal. The replacement does not
lower `MGraph.cHat` and the red crossing count (`MolMonoSteps_R.local`), and it does not depend
on the classes, so it is kept by the exchange of `plus` and `minus`. -/
private inductive MolMonoSteps_R (I : Finset V) :
    List (V × V × MClass) → List (V × V × MClass) → Prop
  | nil (B : List (V × V × MClass)) : MolMonoSteps_R I [] B
  | keep (t : V × V × MClass) {B₁ B₂ : List (V × V × MClass)} :
      MolMonoSteps_R I B₁ B₂ → MolMonoSteps_R I (t :: B₁) (t :: B₂)
  | path (u v x : V) (m : MClass) {B₁ B₂ : List (V × V × MClass)} : x ∈ I →
      MolMonoSteps_R I B₁ B₂ →
      MolMonoSteps_R I ((u, v, m) :: B₁) (MolMono_opt u x m ++ MolMono_opt x v m ++ B₂)
  | drop (t : V × V × MClass) {B₁ B₂ : List (V × V × MClass)} :
      (t.1 = t.2.1 ∨ (t.1 ∉ I ∧ t.2.1 ∉ I)) →
      MolMonoSteps_R I B₁ B₂ → MolMonoSteps_R I (t :: B₁) B₂
  | perm {B₁ B₂ B₁' B₂' : List (V × V × MClass)} : MolMonoSteps_R I B₁ B₂ →
      B₁.Perm B₁' → B₂.Perm B₂' → MolMonoSteps_R I B₁' B₂'

variable {I}

private theorem MolMonoSteps_R.local {B₁ B₂ : List (V × V × MClass)} (h : MolMonoSteps_R I B₁ B₂)
    (hS : S ⊆ I) : MolMono_Local I X S B₁ B₂ := by
  induction h with
  | nil B => exact MolMonoSteps_local_nil I X S B
  | keep t _ ih =>
    exact MolMonoSteps_local_append I X S (A₁ := [t]) (A₂ := [t]) (by simp [MolMono_Local]) ih
  | @path u v x m B₁ B₂ hx _ ih =>
    have hp := MolMono_local_path I X S hS hx (u := u) (v := v) m
    by_cases huv : u = v
    · subst huv
      have h0 : MolMono_Local I X S [(u, u, m)] [] :=
        MolMonoSteps_local_nocut I X S _ (by simp)
      have := MolMonoSteps_local_append I X S
        (MolMonoSteps_local_append I X S h0 (MolMonoSteps_local_nil I X S
          (MolMono_opt u x m ++ MolMono_opt x u m))) ih
      simpa using this
    · rw [show MolMono_opt u v m = [(u, v, m)] by simp [MolMono_opt, huv]] at hp
      exact MolMonoSteps_local_append I X S hp ih
  | @drop t B₁ B₂ ht _ ih =>
    have h0 : MolMono_Local I X S [t] [] := by
      refine MolMonoSteps_local_nocut I X S t ?_
      rcases ht with h | ⟨h1, h2⟩
      · rw [h]; tauto
      · have h1' : t.1 ∉ S := fun h => h1 (hS h)
        have h2' : t.2.1 ∉ S := fun h => h2 (hS h)
        tauto
    simpa using MolMonoSteps_local_append I X S h0 ih
  | perm _ h₁ h₂ ih => exact MolMonoSteps_local_perm I X S ih h₁ h₂

private theorem MolMonoSteps_R.weaken {B₁ B₂ : List (V × V × MClass)}
    (h : MolMonoSteps_R I B₁ B₂) (A : List (V × V × MClass)) : MolMonoSteps_R I B₁ (A ++ B₂) := by
  induction h with
  | nil B => exact .nil _
  | keep t _ ih => exact .perm (.keep t ih) (List.Perm.refl _) List.perm_middle.symm
  | path u v x m hx _ ih =>
    refine .perm (.path u v x m hx ih) (List.Perm.refl _) ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _ |>.trans (by rw [List.append_assoc])
  | drop t ht _ ih => exact .drop t ht ih
  | perm _ h₁ h₂ ih => exact .perm ih h₁ (h₂.append_left A)

private theorem MolMonoSteps_R.append {A₁ A₂ B₁ B₂ : List (V × V × MClass)}
    (hA : MolMonoSteps_R I A₁ A₂) (hB : MolMonoSteps_R I B₁ B₂) :
    MolMonoSteps_R I (A₁ ++ B₁) (A₂ ++ B₂) := by
  induction hA with
  | nil A => exact hB.weaken A
  | keep t _ ih => exact .keep t ih
  | path u v x m hx _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .path u v x m hx ih
  | drop t ht _ ih => exact .drop t ht ih
  | perm _ h₁ h₂ ih => exact .perm ih (h₁.append_right _) (h₂.append_right _)

private theorem MolMonoSteps_R.refl (B : List (V × V × MClass)) : MolMonoSteps_R I B B := by
  induction B with
  | nil => exact .nil _
  | cons t B ih => exact .keep t ih

private theorem MolMonoSteps_R.sw {B₁ B₂ : List (V × V × MClass)} (h : MolMonoSteps_R I B₁ B₂) :
    MolMonoSteps_R I (B₁.map MolMonoSteps_swT) (B₂.map MolMonoSteps_swT) := by
  induction h with
  | nil B => exact .nil _
  | keep t _ ih => exact .keep _ ih
  | path u v x m hx _ ih =>
    rw [List.map_append, List.map_append, MolMonoSteps_opt_sw, MolMonoSteps_opt_sw]
    exact .path u v x _ hx ih
  | drop t ht _ ih => exact .drop _ ht ih
  | perm _ h₁ h₂ ih => exact .perm ih (h₁.map _) (h₂.map _)

/-- Per-element replacements give a replacement of the lists of present edges. -/
private theorem MolMonoSteps_R.filterMap {α : Type} (l : List α)
    (d₁ d₂ : α → Option (V × V × MClass))
    (h : ∀ c ∈ l, MolMonoSteps_R I (d₁ c).toList (d₂ c).toList) :
    MolMonoSteps_R I (l.filterMap d₁) (l.filterMap d₂) := by
  induction l with
  | nil => exact .nil _
  | cons c l ih =>
    have e : ∀ d : α → Option (V × V × MClass), (c :: l).filterMap d = (d c).toList ++
        l.filterMap d := fun d => by cases h : d c <;> simp [h]
    rw [e, e]
    exact (h c List.mem_cons_self).append (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

end ListTools

/-! ## Maps of the molecules -/

section Frame

variable {k n m : ℕ}

/-- A present edge of `Graph.toMG'` of `Γ₁` carried to the molecules of `Γ₂` along the atom map
`φ`. -/
private def MolMonoSteps_hat (Γ₂ : Graph k m) (φ : Atom k n → Atom k m)
    (t : Atom k n × Atom k n × MClass) : Atom k m × Atom k m × MClass :=
  (Γ₂.molRep (φ t.1), Γ₂.molRep (φ t.2.1), t.2.2)

private theorem MolMonoSteps_isRight_iff (u : Atom k n) :
    u.isRight = true ↔ ∃ b, u = .inr b := by
  rcases u with a | a <;> simp

/-- A vertex of `Graph.toMG'` of `Γ₁` and its image in the molecules of `Γ₂`. -/
private theorem MolMonoSteps_vtx {Γ₁ : Graph k n} {Γ₂ : Graph k m} {φ : Atom k n → Atom k m}
    (h0 : ∀ a, (φ (.inr a)).isRight = true) (h3 : ∀ a, φ (.inl a) = .inl a)
    {S₂ : Finset (Atom k m)} (hS : S₂ ⊆ Γ₂.toMG'.int) {u : Atom k n} (hu : Γ₁.toMG'.IsVtx u) :
    (u ∈ Γ₁.molPull Γ₂ φ S₂ ↔ Γ₂.molRep (φ u) ∈ S₂) ∧
      (u ∈ Γ₁.toMG'.int ↔ Γ₂.molRep (φ u) ∈ Γ₂.toMG'.int) ∧
      Γ₂.toMG'.IsVtx (Γ₂.molRep (φ u)) ∧ (∀ a, Γ₂.molRep (φ u) = .inl a ↔ u = .inl a) := by
  rcases hu with hi | he
  · obtain ⟨b, rfl, -⟩ := MolMono_of_mem_int Γ₁ hi
    obtain ⟨c, hc⟩ := (MolMonoSteps_isRight_iff _).1 (h0 b)
    have hci : Γ₂.molRep (φ (.inr b)) ∈ Γ₂.toMG'.int := by
      rw [hc]; exact MolMono_molRep_mem_int Γ₂ c
    refine ⟨?_, iff_of_true hi hci, Or.inl hci, fun a => ?_⟩
    · simp only [Graph.molPull, Finset.mem_filter, hi, true_and]
    · obtain ⟨d, hd, -⟩ := MolMono_molRep_inr Γ₂ c
      rw [hc, hd]
      simp
  · obtain ⟨a', rfl⟩ := (MolMono_mem_ext Γ₁ _).1 he
    have h1 : (Sum.inl a' : Atom k n) ∉ Γ₁.toMG'.int := MolMono_inl_not_mem_int Γ₁ a'
    have h2 : (Sum.inl a' : Atom k m) ∉ Γ₂.toMG'.int := MolMono_inl_not_mem_int Γ₂ a'
    have hr : Γ₂.molRep (φ (.inl a')) = .inl a' := by rw [h3]; rfl
    rw [hr]
    refine ⟨iff_of_false (fun h => h1 (Finset.mem_filter.1 h).1) (fun h => h2 (hS h)),
      iff_of_false h1 h2, Or.inr ((MolMono_mem_ext Γ₂ _).2 ⟨a', rfl⟩), fun a => by simp⟩

/-- The counts of a list of present edges at the pullback of `S₂` are those of its image at
`S₂`. -/
private theorem MolMonoSteps_transfer {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h0 : ∀ a, (φ (.inr a)).isRight = true)
    (h3 : ∀ a, φ (.inl a) = .inl a) {S₂ : Finset (Atom k m)} (hS : S₂ ⊆ Γ₂.toMG'.int)
    (L : List (Atom k n × Atom k n × MClass))
    (hL : ∀ t ∈ L, Γ₁.toMG'.IsVtx t.1 ∧ Γ₁.toMG'.IsVtx t.2.1) :
    MolMono_cHatL Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) L =
        MolMono_cHatL Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (L.map (MolMonoSteps_hat Γ₂ φ)) ∧
      MolMono_redL Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) L =
        MolMono_redL Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (L.map (MolMonoSteps_hat Γ₂ φ)) := by
  have key : ∀ t ∈ L,
      (MolMono_crossT Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) t ↔
        MolMono_crossT Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (MolMonoSteps_hat Γ₂ φ t)) ∧
      (MolMono_intT Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) t ↔
        MolMono_intT Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (MolMonoSteps_hat Γ₂ φ t)) ∧
      (MolMono_redT Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) t ↔
        MolMono_redT Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (MolMonoSteps_hat Γ₂ φ t)) ∧
      (∀ a, (t.1 = .inl a ∨ t.2.1 = .inl a) ↔
        ((MolMonoSteps_hat Γ₂ φ t).1 = .inl a ∨ (MolMonoSteps_hat Γ₂ φ t).2.1 = .inl a)) := by
    intro t ht
    obtain ⟨hv1, hv2⟩ := hL t ht
    obtain ⟨p1, i1, w1, e1⟩ := MolMonoSteps_vtx h0 h3 hS hv1
    obtain ⟨p2, i2, w2, e2⟩ := MolMonoSteps_vtx h0 h3 hS hv2
    have hc : MolMono_crossT Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) t ↔
        MolMono_crossT Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (MolMonoSteps_hat Γ₂ φ t) := by
      simp only [MolMono_crossT, MolMonoSteps_hat]
      constructor
      · rintro ⟨hm, -, -, hcut⟩
        exact ⟨hm, w1, w2, by simpa only [p1, p2] using hcut⟩
      · rintro ⟨hm, -, -, hcut⟩
        exact ⟨hm, hv1, hv2, by simpa only [p1, p2] using hcut⟩
    refine ⟨hc, ?_, ?_, fun a => ?_⟩
    · simp only [MolMono_intT, hc]
      simp only [MolMonoSteps_hat, i1, i2]
    · simp only [MolMono_redT, MolMonoSteps_hat]
      constructor
      · rintro ⟨hm, -, -, hcut⟩
        exact ⟨hm, w1, w2, by simpa only [p1, p2] using hcut⟩
      · rintro ⟨hm, -, -, hcut⟩
        exact ⟨hm, hv1, hv2, by simpa only [p1, p2] using hcut⟩
    · simp only [MolMonoSteps_hat, e1, e2]
  refine ⟨?_, ?_⟩
  · unfold MolMono_cHatL MolMono_cIntL
    congr 1
    · rw [List.countP_map]
      exact List.countP_congr fun t ht => by simpa using (key t ht).2.1
    · classical
      have himg : MolMono_tExtL Γ₂.toMG'.int Γ₂.toMG'.ext S₂ (L.map (MolMonoSteps_hat Γ₂ φ)) =
          (MolMono_tExtL Γ₁.toMG'.int Γ₁.toMG'.ext (Γ₁.molPull Γ₂ φ S₂) L).image
            (fun u => Γ₂.molRep (φ u)) := by
        ext a'
        simp only [MolMono_mem_tExtL, Finset.mem_image, List.mem_map]
        constructor
        · rintro ⟨⟨ha, hai⟩, t', ⟨t, ht, rfl⟩, hc, htt⟩
          obtain ⟨a, rfl⟩ := (MolMono_mem_ext Γ₂ _).1 ha
          refine ⟨.inl a, ⟨⟨(MolMono_mem_ext Γ₁ _).2 ⟨a, rfl⟩, MolMono_inl_not_mem_int Γ₁ a⟩,
            t, ht, (key t ht).1.2 hc, ((key t ht).2.2.2 a).2 htt⟩, ?_⟩
          rw [h3]; rfl
        · rintro ⟨u, ⟨⟨hu, hui⟩, t, ht, hc, htt⟩, rfl⟩
          obtain ⟨a, rfl⟩ := (MolMono_mem_ext Γ₁ _).1 hu
          have hr : Γ₂.molRep (φ (.inl a)) = .inl a := by rw [h3]; rfl
          rw [hr]
          exact ⟨⟨(MolMono_mem_ext Γ₂ _).2 ⟨a, rfl⟩, MolMono_inl_not_mem_int Γ₂ a⟩,
            MolMonoSteps_hat Γ₂ φ t, ⟨t, ht, rfl⟩, (key t ht).1.1 hc, ((key t ht).2.2.2 a).1 htt⟩
      rw [himg, Finset.card_image_of_injOn]
      intro u hu v hv huv
      obtain ⟨⟨hu', -⟩, -⟩ := (MolMono_mem_tExtL _ _ _ _ _).1 hu
      obtain ⟨⟨hv', -⟩, -⟩ := (MolMono_mem_tExtL _ _ _ _ _).1 hv
      obtain ⟨a, rfl⟩ := (MolMono_mem_ext Γ₁ _).1 hu'
      obtain ⟨b, rfl⟩ := (MolMono_mem_ext Γ₁ _).1 hv'
      simp only [h3] at huv
      have h' : (Sum.inl a : Atom k m) = .inl b := huv
      simp only [Sum.inl.injEq] at h'
      rw [h']
  · unfold MolMono_redL
    rw [List.countP_map]
    exact List.countP_congr fun t ht => by simpa using (key t ht).2.2.1

/-- The ends of the present edges of `Graph.toMG'` are vertices. -/
private theorem MolMonoSteps_edges_vtx (Γ : Graph k n) :
    ∀ t ∈ MolMono_edges Γ, Γ.toMG'.IsVtx t.1 ∧ Γ.toMG'.IsVtx t.2.1 := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨c, -, hct⟩ := List.mem_filterMap.1 ht
    unfold MolMono_edgeD at hct
    split_ifs at hct
    obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.1 hct
    exact ⟨MolMono_molRep_isVtx Γ _, MolMono_molRep_isVtx Γ _⟩
  · obtain ⟨a, -, hat⟩ := List.mem_filterMap.1 ht
    unfold MolMono_pinD at hat
    split at hat
    · cases hat
      exact ⟨MolMono_molRep_isVtx Γ (.inr _), Or.inr ((MolMono_mem_ext Γ _).2 ⟨a, rfl⟩)⟩
    · cases hat

/-- **`Graph.MolMono` from a comparison of the present edges.** If internal atoms go to internal
atoms, external atoms are fixed, molecules go into molecules, every internal molecule of `Γ₂` is
hit, and the present edges of `Γ₁` carried to the molecules of `Γ₂` are replaced by those of `Γ₂`
as in `MolMono_Local` at every set of internal molecules of `Γ₂`, then `φ` is
`Graph.MolMono`. -/
private theorem MolMonoSteps_of_local {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h0 : ∀ a, (φ (.inr a)).isRight = true)
    (h3 : ∀ a, φ (.inl a) = .inl a)
    (h1 : ∀ a b, Γ₁.molRep (.inr a) = Γ₁.molRep (.inr b) →
      Γ₂.molRep (φ (.inr a)) = Γ₂.molRep (φ (.inr b)))
    (h2 : ∀ v ∈ Γ₂.toMG'.int, ∃ a, Γ₂.molRep (φ (.inr a)) = v)
    (hl : ∀ S₂ ⊆ Γ₂.toMG'.int, MolMono_Local Γ₂.toMG'.int Γ₂.toMG'.ext S₂
      ((MolMono_edges Γ₁).map (MolMonoSteps_hat Γ₂ φ)) (MolMono_edges Γ₂)) :
    Γ₁.MolMono Γ₂ φ := by
  refine ⟨h0, h1, h2, fun S₂ hS => ?_, fun S₂ hS => ?_⟩
  · rw [MolMono_cHat_eq, MolMono_cHat_eq,
      (MolMonoSteps_transfer h0 h3 hS _ (MolMonoSteps_edges_vtx Γ₁)).1]
    simpa using (MolMono_append_le _ _ _ [] _ _ (hl S₂ hS)).1
  · rw [MolMono_redCount_eq, MolMono_redCount_eq,
      (MolMonoSteps_transfer h0 h3 hS _ (MolMonoSteps_edges_vtx Γ₁)).2]
    simpa using (MolMono_append_le _ _ _ [] _ _ (hl S₂ hS)).2

/-- `MolMonoSteps_of_local` with a replacement of the kind `MolMonoSteps_R`. -/
private theorem MolMonoSteps_of_R {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m} (h0 : ∀ a, (φ (.inr a)).isRight = true)
    (h3 : ∀ a, φ (.inl a) = .inl a)
    (h1 : ∀ a b, Γ₁.molRep (.inr a) = Γ₁.molRep (.inr b) →
      Γ₂.molRep (φ (.inr a)) = Γ₂.molRep (φ (.inr b)))
    (h2 : ∀ v ∈ Γ₂.toMG'.int, ∃ a, Γ₂.molRep (φ (.inr a)) = v)
    (hR : MolMonoSteps_R Γ₂.toMG'.int ((MolMono_edges Γ₁).map (MolMonoSteps_hat Γ₂ φ))
      (MolMono_edges Γ₂)) :
    Γ₁.MolMono Γ₂ φ :=
  MolMonoSteps_of_local h0 h3 h1 h2 fun _ hS => hR.local _ _ hS

/-- Reachability carried along a map sending every step to an equality or a step. -/
private theorem MolMonoSteps_reach_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    (φ : α → β) (h : ∀ a b, r a b → φ a = φ b ∨ r' (φ a) (φ b)) {a b : α}
    (hab : (SimpleGraph.fromRel r).Reachable a b) :
    (SimpleGraph.fromRel r').Reachable (φ a) (φ b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab ⊢
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' c' _ hadj ih =>
    rw [SimpleGraph.fromRel_adj] at hadj
    by_cases hne : φ b' = φ c'
    · rw [← hne]; exact ih
    · refine ih.tail ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, ?_⟩)
      rcases hadj.2 with h1 | h1
      · rcases h _ _ h1 with he | he
        · exact absurd he hne
        · exact Or.inl he
      · rcases h _ _ h1 with he | he
        · exact absurd he.symm hne
        · exact Or.inr he

/-- Molecules carried along a map of the atoms. -/
private theorem MolMonoSteps_sameMol_map {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    (φ : Atom k n → Atom k m) (hφ : ∀ u : Atom k n, u.isRight = true → (φ u).isRight = true)
    (hc : ∀ c ∈ Γ₁.comps, c.kind.joinsMol = true → φ c.x = φ c.y ∨
      ∃ c' ∈ Γ₂.comps, c'.kind.joinsMol = true ∧ c'.x = φ c.x ∧ c'.y = φ c.y)
    {u v : Atom k n} (h : Γ₁.SameMol u v) : Γ₂.SameMol (φ u) (φ v) := by
  rcases h with rfl | ⟨hu, hv, h⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hφ u hu, hφ v hv, ?_⟩
    unfold Graph.molGraph at h ⊢
    refine MolMonoSteps_reach_map φ (fun a b hab => ?_) h
    obtain ⟨c, hcm, hk, rfl, rfl⟩ := hab
    rcases hc c hcm hk with h' | ⟨c', hc', hk', hx', hy'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨c', hc', hk', hx', hy'⟩

/-- Blocks carried along a map of the atoms. -/
private theorem MolMonoSteps_sameBlock_map {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    (φ : Atom k n → Atom k m)
    (hc : ∀ c ∈ Γ₁.comps, c.kind = .dot → φ c.x = φ c.y ∨
      ∃ c' ∈ Γ₂.comps, c'.kind = .dot ∧ c'.x = φ c.x ∧ c'.y = φ c.y)
    {u v : Atom k n} (h : Γ₁.SameBlock u v) : Γ₂.SameBlock (φ u) (φ v) := by
  unfold Graph.SameBlock Graph.dotGraph at h ⊢
  refine MolMonoSteps_reach_map φ (fun a b hab => ?_) h
  obtain ⟨c, hcm, hk, rfl, rfl⟩ := hab
  rcases hc c hcm hk with h' | ⟨c', hc', hk', hx', hy'⟩
  · exact Or.inl h'
  · exact Or.inr ⟨c', hc', hk', hx', hy'⟩

/-- Atoms of one molecule have the same representative. -/
private theorem MolMonoSteps_molRep_of_sameMol (Γ : Graph k n) {u v : Atom k n}
    (h : Γ.SameMol u v) : Γ.molRep u = Γ.molRep v := by
  rcases h with rfl | ⟨hu, hv, h⟩
  · rfl
  · obtain ⟨a, rfl⟩ := (MolMonoSteps_isRight_iff u).1 hu
    obtain ⟨b, rfl⟩ := (MolMonoSteps_isRight_iff v).1 hv
    exact (MolMono_molRep_eq_iff Γ a b).2 (Or.inr ⟨rfl, rfl, h⟩)

/-- Atoms of one block are joined by a path of waved and dotted edges. -/
private theorem MolMonoSteps_mol_of_block (Γ : Graph k n) {u v : Atom k n}
    (h : Γ.SameBlock u v) : Γ.molGraph.Reachable u v := by
  unfold Graph.SameBlock Graph.dotGraph at h
  unfold Graph.molGraph
  refine MolMonoSteps_reach_map id (fun a b hab => Or.inr ?_) h
  obtain ⟨c, hc, hk, rfl, rfl⟩ := hab
  exact ⟨c, hc, by rw [hk]; rfl, rfl, rfl⟩

/-- Internal atoms of one block have the same representative. -/
private theorem MolMonoSteps_molRep_of_block (Γ : Graph k n) {a b : Fin n}
    (h : Γ.SameBlock (.inr a) (.inr b)) : Γ.molRep (.inr a) = Γ.molRep (.inr b) :=
  (MolMono_molRep_eq_iff Γ a b).2 (Or.inr ⟨rfl, rfl, MolMonoSteps_mol_of_block Γ h⟩)

/-- The anchor of an atom lies in its block. -/
private theorem MolMonoSteps_anchor_some (Γ : Graph k n) {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  classical
  rw [MolMono_anchor_eq_find] at h
  simpa using List.find?_some h

/-- An atom without anchor has no internal atom in its block. -/
private theorem MolMonoSteps_anchor_none (Γ : Graph k n) {u : Atom k n} :
    Γ.anchor u = none ↔ ∀ b : Fin n, ¬ Γ.SameBlock u (.inr b) := by
  classical
  rw [MolMono_anchor_eq_find, List.find?_eq_none]
  simp

/-- An atom with an internal atom in its block has an anchor. -/
private theorem MolMonoSteps_anchor_of (Γ : Graph k n) {u : Atom k n} {b : Fin n}
    (h : Γ.SameBlock u (.inr b)) : ∃ b', Γ.anchor u = some b' := by
  cases ha : Γ.anchor u with
  | none => exact absurd h ((MolMonoSteps_anchor_none Γ).1 ha b)
  | some b' => exact ⟨b', rfl⟩

/-- The image of the representative of an internal atom lies in the molecule of the image. -/
private theorem MolMonoSteps_rep_map {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {φ : Atom k n → Atom k m}
    (h1 : ∀ a b, Γ₁.molRep (.inr a) = Γ₁.molRep (.inr b) →
      Γ₂.molRep (φ (.inr a)) = Γ₂.molRep (φ (.inr b))) (a : Fin n) :
    Γ₂.molRep (φ (Γ₁.molRep (.inr a))) = Γ₂.molRep (φ (.inr a)) := by
  obtain ⟨b, hb, hab⟩ := MolMono_molRep_inr Γ₁ a
  rw [hb]
  exact h1 b a ((MolMono_molRep_eq_iff Γ₁ b a).2 (Γ₁.sameMol_equivalence.symm hab))

/-- The molecule, in the block normal form, of the image of an atom is the image of its
molecule, when blocks are carried forward and the atom is external without anchor only if its
image has none. -/
private theorem MolMonoSteps_good {Γ₁ : Graph k n} {Γ₂ : Graph k m} {φ : Atom k n → Atom k m}
    (h0 : ∀ a, (φ (.inr a)).isRight = true) (h3 : ∀ a, φ (.inl a) = .inl a)
    (h1 : ∀ a b, Γ₁.molRep (.inr a) = Γ₁.molRep (.inr b) →
      Γ₂.molRep (φ (.inr a)) = Γ₂.molRep (φ (.inr b)))
    (hF : ∀ u v, Γ₁.SameBlock u v → Γ₂.SameBlock (φ u) (φ v)) (u : Atom k n)
    (hB : ∀ a, u = .inl a → Γ₁.anchor (.inl a) = none → Γ₂.anchor (.inl a) = none) :
    Γ₂.molRep (Γ₂.flatAtom (φ u)) = Γ₂.molRep (φ (Γ₁.molRep (Γ₁.flatAtom u))) := by
  rcases u with a | a
  · rw [h3]
    cases h₁ : Γ₁.anchor (.inl a) with
    | none =>
      have h₂ := hB a rfl h₁
      simp only [Graph.flatAtom, h₁, h₂]
      show Γ₂.molRep (.inl a) = Γ₂.molRep (φ (.inl a))
      rw [h3]
    | some b =>
      have hb := MolMonoSteps_anchor_some Γ₁ h₁
      have hb₂ := hF _ _ hb
      rw [h3] at hb₂
      obtain ⟨c, hc⟩ := (MolMonoSteps_isRight_iff _).1 (h0 b)
      rw [hc] at hb₂
      obtain ⟨b', hb'⟩ := MolMonoSteps_anchor_of Γ₂ hb₂
      have hbb := MolMonoSteps_anchor_some Γ₂ hb'
      simp only [Graph.flatAtom, h₁, hb']
      rw [MolMonoSteps_rep_map h1 b, hc]
      exact MolMonoSteps_molRep_of_block Γ₂ (hbb.symm.trans hb₂)
  · obtain ⟨c, hc⟩ := (MolMonoSteps_isRight_iff _).1 (h0 a)
    simp only [Graph.flatAtom]
    rw [MolMonoSteps_rep_map h1 a, hc]

/-- The pin edge of an external atom is carried to the pin edge of its image. -/
private theorem MolMonoSteps_pin {Γ₁ : Graph k n} {Γ₂ : Graph k m} {φ : Atom k n → Atom k m}
    (h3 : ∀ a, φ (.inl a) = .inl a) (a : Fin k)
    (hA : Γ₁.anchor (.inl a) = none ↔ Γ₂.anchor (.inl a) = none)
    (hg : Γ₂.molRep (Γ₂.flatAtom (φ (.inl a))) =
      Γ₂.molRep (φ (Γ₁.molRep (Γ₁.flatAtom (.inl a))))) :
    MolMono_pinD Γ₂ a = (MolMono_pinD Γ₁ a).map (MolMonoSteps_hat Γ₂ φ) := by
  unfold MolMono_pinD
  cases h₁ : Γ₁.anchor (.inl a) with
  | none =>
    rw [hA.1 h₁]; rfl
  | some b =>
    cases h₂ : Γ₂.anchor (.inl a) with
    | none => exact absurd (hA.2 h₂) (by rw [h₁]; simp)
    | some b' =>
      simp only [Graph.flatAtom, h₁, h₂, h3] at hg
      simp only [Option.map_some, MolMonoSteps_hat, h3, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hg, rfl, trivial⟩

/-- **A component carried to a component of the same kind** whose ends lie in the images of the
molecules of its ends: its present edge is carried to the present edge of the image, or the
image edge lies inside one molecule. -/
private theorem MolMonoSteps_edge_R {Γ₁ : Graph k n} {Γ₂ : Graph k m} (φ : Atom k n → Atom k m)
    (I : Finset (Atom k m)) (c : Comp (Atom k n)) (c' : Comp (Atom k m)) (hk : c'.kind = c.kind)
    (hx : Γ₂.molRep (Γ₂.flatAtom c'.x) = Γ₂.molRep (φ (Γ₁.molRep (Γ₁.flatAtom c.x))))
    (hy : Γ₂.molRep (Γ₂.flatAtom c'.y) = Γ₂.molRep (φ (Γ₁.molRep (Γ₁.flatAtom c.y)))) :
    MolMonoSteps_R I ((MolMono_edgeD Γ₁ c).map (MolMonoSteps_hat Γ₂ φ)).toList
      (MolMono_edgeD Γ₂ c').toList := by
  unfold MolMono_edgeD
  rw [hk, hx, hy]
  by_cases hd : c.kind = .dot
  · simp only [hd, true_or, ite_true]
    exact .nil _
  by_cases he₁ : Γ₁.molRep (Γ₁.flatAtom c.x) = Γ₁.molRep (Γ₁.flatAtom c.y)
  · simp only [he₁, or_true, ite_true, Option.map_none, Option.toList_none]
    exact .nil _
  simp only [hd, he₁, false_or, ite_false]
  cases hm : c.kind.mclass with
  | none => simp only [Option.map_none, Option.toList_none]; split_ifs <;> exact .nil _
  | some mc =>
    simp only [Option.map_some, Option.toList_some, MolMonoSteps_hat]
    split_ifs with he₂
    · exact .drop _ (Or.inl he₂) (.nil _)
    · exact MolMonoSteps_R.refl _

end Frame

/-! ## Facts on the block normal form -/

section Flat

variable {k n : ℕ}

/-- An external atom without anchor is its own atom in the block normal form. -/
private theorem MolMonoSteps_flat_none (Γ : Graph k n) {a : Fin k}
    (h : Γ.anchor (.inl a) = none) : Γ.flatAtom (.inl a) = .inl a := by
  simp only [Graph.flatAtom, h]

/-- An external atom with anchor `b` is the atom `b` in the block normal form. -/
private theorem MolMonoSteps_flat_some (Γ : Graph k n) {a : Fin k} {b : Fin n}
    (h : Γ.anchor (.inl a) = some b) : Γ.flatAtom (.inl a) = .inr b := by
  simp only [Graph.flatAtom, h]

/-- The representative of an internal atom of the block normal form is an internal vertex. -/
private theorem MolMonoSteps_rep_int (Γ : Graph k n) {u : Atom k n} (h : u.isRight = true) :
    Γ.molRep u ∈ Γ.toMG'.int := by
  obtain ⟨b, rfl⟩ := (MolMonoSteps_isRight_iff u).1 h
  exact MolMono_molRep_mem_int Γ b

/-- The atom of the block normal form at an atom that is not an external atom without internal
atom in its block is internal. -/
private theorem MolMonoSteps_flat_isRight (Γ : Graph k n) {u : Atom k n} (h : ¬ Γ.Unpinned u) :
    (Γ.flatAtom u).isRight = true := by
  rcases u with a | a
  · cases ha : Γ.anchor (.inl a) with
    | none => exact absurd ⟨rfl, (MolMonoSteps_anchor_none Γ).1 ha⟩ h
    | some b => rw [MolMonoSteps_flat_some Γ ha]; rfl
  · rfl

private theorem MolMonoSteps_edgeD_some (Γ : Graph k n) {d : Comp (Atom k n)}
    {t : Atom k n × Atom k n × MClass} (h : MolMono_edgeD Γ d = some t) :
    d.kind ≠ .dot ∧ d.kind.mclass = some t.2.2 ∧ t.1 = Γ.molRep (Γ.flatAtom d.x) ∧
      t.2.1 = Γ.molRep (Γ.flatAtom d.y) ∧ t.1 ≠ t.2.1 := by
  unfold MolMono_edgeD at h
  split_ifs at h with h1
  simp only [not_or] at h1
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨h1.1, hm, rfl, rfl, h1.2⟩

private theorem MolMonoSteps_edgeD_mclass (Γ : Graph k n) {d : Comp (Atom k n)}
    (h : d.kind.mclass = none) : MolMono_edgeD Γ d = none := by
  unfold MolMono_edgeD
  split_ifs <;> simp [h]

private theorem MolMonoSteps_edgeD_dot (Γ : Graph k n) {d : Comp (Atom k n)}
    (h : d.kind = .dot) : MolMono_edgeD Γ d = none := by
  simp [MolMono_edgeD, h]

/-- The present edge of a component other than a dotted edge, with a class. -/
private theorem MolMonoSteps_edgeD_toList (Γ : Graph k n) {d : Comp (Atom k n)} {m : MClass}
    (hk : d.kind ≠ .dot) (hm : d.kind.mclass = some m) :
    (MolMono_edgeD Γ d).toList =
      MolMono_opt (Γ.molRep (Γ.flatAtom d.x)) (Γ.molRep (Γ.flatAtom d.y)) m := by
  unfold MolMono_edgeD MolMono_opt
  by_cases he : Γ.molRep (Γ.flatAtom d.x) = Γ.molRep (Γ.flatAtom d.y)
  · simp [he]
  · simp [he, hk, hm]

/-- The representative of the molecule of an internal atom is internal. -/
private theorem MolMonoSteps_molRep_isRight (Γ : Graph k n) {u : Atom k n}
    (h : u.isRight = true) : (Γ.molRep u).isRight = true := by
  obtain ⟨b, rfl⟩ := (MolMonoSteps_isRight_iff u).1 h
  obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ b
  rw [hc]; rfl

/-- The filter of the three external atoms. -/
private theorem MolMonoSteps_filterMap_fin3 {β : Type} (f : Fin 3 → Option β) :
    (List.finRange 3).filterMap f = (f 0).toList ++ (f 1).toList ++ (f 2).toList := by
  rw [show List.finRange 3 = [0, 1, 2] by decide]
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> simp [h0, h1, h2]

private theorem MolMonoSteps_length_filterMap_le {α β : Type} (l : List α) (d : α → Option β)
    (p : α → Bool) (h : ∀ c ∈ l, d c ≠ none → p c = true) :
    (l.filterMap d).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have ih' := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    cases hd : d c with
    | none =>
      rw [List.filterMap_cons_none hd]
      refine ih'.trans ?_
      by_cases hp : p c = true
      · rw [List.filter_cons_of_pos hp]; simp
      · rw [List.filter_cons_of_neg hp]
    | some b =>
      rw [List.filterMap_cons_some hd, List.filter_cons_of_pos (h c List.mem_cons_self
        (by rw [hd]; simp))]
      simpa using ih'

/-- The charge pattern of the block normal form at a random component. -/
private theorem MolMonoSteps_colour {n : ℕ} {Γ : Graph 3 n} (hI : Γ.ColourInvB)
    {c : Comp (Atom 3 n)} (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) (hk : c.kind ≠ .dot) :
    (Γ.flatAtom c.x).isRight = true ∧ Γ.flatAtom c.y ≠ .inl 0 ∧
      (Γ.flatAtom c.y = .inl 1 → c.kind = .G .plus) ∧
      (Γ.flatAtom c.y = .inl 2 → c.kind = .G .minus) := by
  have h := (hI (Γ.flatComp c) (List.mem_map_of_mem hc)).1
  simp only [Graph.flatComp, hk, ite_false] at h
  exact h hr

end Flat

/-! ## The dotted terms: molecules joined and external atoms identified -/

section Dots

variable {n : ℕ}

/-- **The edges at an external atom without internal atom in its block** (`⊗ = 0`, `⊕ = 1`,
`⊖ = 2`), under the charge pattern of the block normal form, the clause on the external atoms and
without ghost edges: a present edge at that atom has its other end internal in the block normal
form, and it is red exactly when the atom is `⊖`. -/
private theorem MolMonoSteps_ext_edge {Γ : Graph 3 n} (hC : Γ.ColourInvB) (hE : Γ.ExtClause)
    (hG : Γ.NoGhost) {a : Fin 3} (ha : Γ.anchor (.inl a) = none) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hk : c.kind ≠ .dot) {m : MClass} (hm : c.kind.mclass = some m)
    (hxy : c.x = .inl a ∨ c.y = .inl a) :
    (c.y = .inl a ∧ (Γ.flatAtom c.x).isRight = true ∨
        c.x = .inl a ∧ (Γ.flatAtom c.y).isRight = true) ∧ (m = .minus ↔ a = 2) := by
  have hU : Γ.Unpinned (.inl a) := ⟨rfl, (MolMonoSteps_anchor_none Γ).1 ha⟩
  have hfa := MolMonoSteps_flat_none Γ ha
  have hdiff : c.kind.isDiffusive = true → m = .diff ∧
      (c.x = .inl a → ¬ Γ.Unpinned c.y) ∧ (c.y = .inl a → ¬ Γ.Unpinned c.x) ∧ a ≠ 2 := by
    intro hd
    have hmd : m = .diff := by
      revert hm hd
      cases c.kind <;> simp [Kind.mclass, Kind.isDiffusive] <;> intros <;> simp_all
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
    · exact ⟨hmd, ((hE.2.2.1 hU).2 c hc hd).1, ((hE.2.2.1 hU).2 c hc hd).2, by decide⟩
    · exact ⟨hmd, ((hE.2.2.2.2 hU).2.1 c hc hd).1, ((hE.2.2.2.2 hU).2.1 c hc hd).2, by decide⟩
    · exfalso
      have := (hE.2.2.2.1 hU).1 c hc hd
      rcases hxy with h | h
      · exact this.1 h
      · exact this.2 h
  cases hκ : c.kind with
  | G ch =>
    have hr : c.kind.isRandom = true := by rw [hκ]; rfl
    obtain ⟨h1, h2, h3, h4⟩ := MolMonoSteps_colour hC hc hr hk
    have hcy : c.y = .inl a := by
      rcases hxy with h | h
      · rw [h, hfa] at h1; cases h1
      · exact h
    rw [hcy, hfa] at h2 h3 h4
    refine ⟨Or.inl ⟨hcy, h1⟩, ?_⟩
    rw [hκ] at hm h3 h4
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
    · exact absurd rfl h2
    · have := h3 rfl
      cases this
      simp only [Kind.mclass, Option.some.injEq] at hm
      subst hm
      decide
    · have := h4 rfl
      cases this
      simp only [Kind.mclass, Option.some.injEq] at hm
      subst hm
      decide
  | theta o =>
    obtain ⟨hmd, hx, hy, ha2⟩ := hdiff (by rw [hκ]; rfl)
    refine ⟨?_, by rw [hmd]; simp [ha2]⟩
    rcases hxy with h | h
    · exact Or.inr ⟨h, MolMonoSteps_flat_isRight Γ (hx h)⟩
    · exact Or.inl ⟨h, MolMonoSteps_flat_isRight Γ (hy h)⟩
  | thetaErr o D =>
    obtain ⟨hmd, hx, hy, ha2⟩ := hdiff (by rw [hκ]; rfl)
    refine ⟨?_, by rw [hmd]; simp [ha2]⟩
    rcases hxy with h | h
    · exact Or.inr ⟨h, MolMonoSteps_flat_isRight Γ (hx h)⟩
    · exact Or.inl ⟨h, MolMonoSteps_flat_isRight Γ (hy h)⟩
  | aux j r b =>
    cases b with
    | false => rw [hκ] at hm; simp [Kind.mclass] at hm
    | true =>
      obtain ⟨hmd, hx, hy, ha2⟩ := hdiff (by rw [hκ]; rfl)
      refine ⟨?_, by rw [hmd]; simp [ha2]⟩
      rcases hxy with h | h
      · exact Or.inr ⟨h, MolMonoSteps_flat_isRight Γ (hx h)⟩
      · exact Or.inl ⟨h, MolMonoSteps_flat_isRight Γ (hy h)⟩
  | ghost => exact absurd hκ (hG c hc)
  | dot => exact absurd hκ hk
  | _ => rw [hκ] at hm; simp [Kind.mclass] at hm

/-- **The edges at an identified external vertex.** The edges between `e` (external, not internal)
and internal vertices `M` are replaced by the edges between `M` and an internal vertex `V'`, and
the edge from `V'` to `e` of class `pc` is added. If none of these edges is red, or all are red
and there is at most one of them, `MGraph.cHat` and the red crossing count do not drop. -/
private theorem MolMonoSteps_local_pin {V α : Type} [DecidableEq V] (I X S : Finset V)
    (hS : S ⊆ I) {e V' : V} (heI : e ∉ I) (heX : e ∈ X) (hV : V' ∈ I) (pc : MClass)
    (G : List α) (d₁ d₂ : α → Option (V × V × MClass))
    (hd : ∀ c ∈ G, ∀ t, d₁ c = some t → ∃ M m, M ∈ I ∧
      ((t = (e, M, m) ∧ (d₂ c).toList = MolMono_opt V' M m) ∨
        (t = (M, e, m) ∧ (d₂ c).toList = MolMono_opt M V' m)))
    (hcl : (pc ≠ .minus ∧ ∀ c ∈ G, ∀ t, d₁ c = some t → t.2.2 ≠ .minus) ∨
      (pc = .minus ∧ (∀ c ∈ G, ∀ t, d₁ c = some t → t.2.2 = .minus) ∧
        (G.filterMap d₁).length ≤ 1)) :
    MolMono_Local I X S (G.filterMap d₁) (G.filterMap d₂ ++ [(V', e, pc)]) := by
  have heS : e ∉ S := fun h => heI (hS h)
  have hmem : ∀ t ∈ G.filterMap d₁, ∃ c ∈ G, ∃ M m, M ∈ I ∧
      ((t = (e, M, m) ∧ (d₂ c).toList = MolMono_opt V' M m) ∨
        (t = (M, e, m) ∧ (d₂ c).toList = MolMono_opt M V' m)) := by
    intro t ht
    obtain ⟨c, hc, hct⟩ := List.mem_filterMap.1 ht
    exact ⟨c, hc, hd c hc t hct⟩
  have hin : ∀ c ∈ G, ∀ t' ∈ (d₂ c).toList, t' ∈ G.filterMap d₂ ++ [(V', e, pc)] := by
    intro c hc t' ht'
    refine List.mem_append_left _ (List.mem_filterMap.2 ⟨c, hc, ?_⟩)
    cases h : d₂ c with
    | none => rw [h] at ht'; cases ht'
    | some u => rw [h] at ht'; simp at ht'; rw [ht']
  have hpin : (V', e, pc) ∈ G.filterMap d₂ ++ [(V', e, pc)] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hc0 : MolMono_cIntL I X S (G.filterMap d₁) = 0 := by
    unfold MolMono_cIntL
    rw [List.countP_eq_zero]
    intro t ht hi
    have hi' : MolMono_intT I X S t := by simpa using hi
    obtain ⟨c, -, M, m, -, (⟨rfl, -⟩ | ⟨rfl, -⟩)⟩ := hmem t ht
    · exact heI hi'.2.1
    · exact heI hi'.2.2
  have hcut : ∀ t ∈ G.filterMap d₁, ((t.1 ∈ S ∧ t.2.1 ∉ S) ∨ (t.1 ∉ S ∧ t.2.1 ∈ S)) →
      ∃ c ∈ G, ∃ M, M ∈ I ∧ M ∈ S ∧
        ((d₂ c).toList = MolMono_opt V' M t.2.2 ∨ (d₂ c).toList = MolMono_opt M V' t.2.2) := by
    intro t ht hct
    obtain ⟨c, hc, M, m, hM, (⟨rfl, h⟩ | ⟨rfl, h⟩)⟩ := hmem t ht
    · refine ⟨c, hc, M, hM, ?_, Or.inl h⟩
      rcases hct with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 heS
      · exact h2
    · refine ⟨c, hc, M, hM, ?_, Or.inr h⟩
      rcases hct with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 heS
  rcases hcl with ⟨hpc, hnr⟩ | ⟨hpc, hr, hlen⟩
  · have hT1 : MolMono_tExtL I X S (G.filterMap d₁) ⊆ {e} := by
      intro a ha
      obtain ⟨⟨-, hai⟩, t, ht, -, hta⟩ := (MolMono_mem_tExtL I X S _ a).1 ha
      obtain ⟨c, -, M, m, hM, (⟨rfl, -⟩ | ⟨rfl, -⟩)⟩ := hmem t ht
      · rcases hta with h | h
        · exact Finset.mem_singleton.2 h.symm
        · exact absurd (h ▸ hM) hai
      · rcases hta with h | h
        · exact absurd (h ▸ hM) hai
        · exact Finset.mem_singleton.2 h.symm
    refine ⟨?_, ?_⟩
    · rw [hc0, zero_add]
      by_cases hex : ∃ t ∈ G.filterMap d₁, MolMono_crossT I X S t
      · obtain ⟨t, ht, hct⟩ := hex
        obtain ⟨c, hc, M, hM, hMS, hdc⟩ := hcut t ht hct.2.2.2
        have hm : t.2.2 ≠ .minus := hct.1
        by_cases hVS : V' ∈ S
        · have : MolMono_tExtL I X S (G.filterMap d₁) \
              MolMono_tExtL I X S (G.filterMap d₂ ++ [(V', e, pc)]) = ∅ := by
            rw [Finset.sdiff_eq_empty_iff_subset]
            intro a ha
            have hae := Finset.mem_singleton.1 (hT1 ha)
            subst hae
            exact (MolMono_mem_tExtL I X S _ _).2 ⟨⟨heX, heI⟩, _, hpin,
              ⟨hpc, Or.inl hV, Or.inr heX, Or.inl ⟨hVS, heS⟩⟩, Or.inr rfl⟩
          rw [this]
          simp
        · have hMV : M ≠ V' := fun h => hVS (h ▸ hMS)
          have h1 : (Finset.card (MolMono_tExtL I X S (G.filterMap d₁) \
              MolMono_tExtL I X S (G.filterMap d₂ ++ [(V', e, pc)]))) ≤ 1 :=
            (Finset.card_le_card (Finset.sdiff_subset.trans hT1)).trans (by simp)
          refine h1.trans (List.countP_pos_iff.2 ?_)
          rcases hdc with h | h
          · refine ⟨(V', M, t.2.2), hin c hc _ (by rw [h]; simp [MolMono_opt, hMV.symm]), ?_⟩
            simpa using ⟨⟨hm, Or.inl hV, Or.inl hM, Or.inr ⟨hVS, hMS⟩⟩, hV, hM⟩
          · refine ⟨(M, V', t.2.2), hin c hc _ (by rw [h]; simp [MolMono_opt, hMV]), ?_⟩
            simpa using ⟨⟨hm, Or.inl hM, Or.inl hV, Or.inl ⟨hMS, hVS⟩⟩, hM, hV⟩
      · have : MolMono_tExtL I X S (G.filterMap d₁) = ∅ := by
          ext a
          simp only [MolMono_mem_tExtL, Finset.notMem_empty, iff_false, not_and]
          intro _ ⟨t, ht, hct, _⟩
          exact hex ⟨t, ht, hct⟩
        rw [this]
        simp
    · have : MolMono_redL I X S (G.filterMap d₁) = 0 := by
        unfold MolMono_redL
        rw [List.countP_eq_zero]
        intro t ht hrt
        obtain ⟨c, hc, hct⟩ := List.mem_filterMap.1 ht
        have hrt' : MolMono_redT I X S t := by simpa using hrt
        exact hnr c hc t hct hrt'.1
      rw [this]
      exact Nat.zero_le _
  · refine ⟨?_, ?_⟩
    · have : MolMono_tExtL I X S (G.filterMap d₁) = ∅ := by
        ext a
        simp only [MolMono_mem_tExtL, Finset.notMem_empty, iff_false, not_and]
        intro _ ⟨t, ht, hct, _⟩
        obtain ⟨c, hc, htc⟩ := List.mem_filterMap.1 ht
        exact hct.1 (hr c hc t htc)
      rw [hc0, this]
      simp
    · have h1 : MolMono_redL I X S (G.filterMap d₁) ≤ 1 :=
        (List.countP_le_length).trans hlen
      by_cases hz : MolMono_redL I X S (G.filterMap d₁) = 0
      · rw [hz]; exact Nat.zero_le _
      refine h1.trans (List.countP_pos_iff.2 ?_)
      obtain ⟨t, ht, hrt⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero hz)
      have hrt' : MolMono_redT I X S t := by simpa using hrt
      obtain ⟨c, hc, M, hM, hMS, hdc⟩ := hcut t ht hrt'.2.2.2
      have hm : t.2.2 = .minus := hrt'.1
      by_cases hVS : V' ∈ S
      · exact ⟨_, hpin, by simpa using ⟨hpc, Or.inl hV, Or.inr heX, Or.inl ⟨hVS, heS⟩⟩⟩
      · have hMV : M ≠ V' := fun h => hVS (h ▸ hMS)
        rcases hdc with h | h
        · refine ⟨(V', M, t.2.2), hin c hc _ (by rw [h]; simp [MolMono_opt, hMV.symm]), ?_⟩
          simpa using ⟨hm, Or.inl hV, Or.inl hM, Or.inr ⟨hVS, hMS⟩⟩
        · refine ⟨(M, V', t.2.2), hin c hc _ (by rw [h]; simp [MolMono_opt, hMV]), ?_⟩
          simpa using ⟨hm, Or.inl hM, Or.inl hV, Or.inl ⟨hMS, hVS⟩⟩

/-- **The edges at one external atom identified with an internal atom.** For the external atom
`a` without internal atom in its block in `Γ₁` and with anchor `b'` in `Γ₂`, and components of
`Γ₁` at `a`: their present edges, carried to the molecules of `Γ₂`, are replaced by those of
`Γ₂` together with the edge from the molecule of `b'` to `a`, as in `MolMono_Local`. -/
private theorem MolMonoSteps_dot_group {Γ₁ Γ₂ : Graph 3 n} (hC : Γ₁.ColourInvB)
    (hE : Γ₁.ExtClause) (hG : Γ₁.NoGhost)
    (hgood : ∀ u, (∀ a', u = .inl a' → ¬ (Γ₁.anchor (.inl a') = none ∧
        Γ₂.anchor (.inl a') ≠ none)) →
      Γ₂.molRep (Γ₂.flatAtom u) = Γ₂.molRep (id (Γ₁.molRep (Γ₁.flatAtom u))))
    {a : Fin 3} (h₁ : Γ₁.anchor (.inl a) = none) {b' : Fin n} (h₂ : Γ₂.anchor (.inl a) = some b')
    (G : List (Comp (Atom 3 n))) (hG₁ : ∀ c ∈ G, c ∈ Γ₁.comps)
    (hGt : ∀ c ∈ G, c.x = .inl a ∨ c.y = .inl a)
    (hGc : ∀ p : Comp (Atom 3 n) → Bool, (G.filter p).length ≤ (Γ₁.comps.filter p).length)
    (S : Finset (Atom 3 n)) (hS : S ⊆ Γ₂.toMG'.int) :
    MolMono_Local Γ₂.toMG'.int Γ₂.toMG'.ext S
      ((G.filterMap (MolMono_edgeD Γ₁)).map (MolMonoSteps_hat Γ₂ id))
      (G.filterMap (MolMono_edgeD Γ₂) ++ [(Γ₂.molRep (.inr b'), .inl a, pinClass a)]) := by
  have hU : Γ₁.Unpinned (.inl a) := ⟨rfl, (MolMonoSteps_anchor_none Γ₁).1 h₁⟩
  have hf₁ := MolMonoSteps_flat_none Γ₁ h₁
  have hf₂ := MolMonoSteps_flat_some Γ₂ h₂
  have hint : ∀ u, (Γ₁.flatAtom u).isRight = true →
      Γ₂.molRep (Γ₂.flatAtom u) = Γ₂.molRep (Γ₁.molRep (Γ₁.flatAtom u)) ∧
        Γ₂.molRep (Γ₁.molRep (Γ₁.flatAtom u)) ∈ Γ₂.toMG'.int := by
    intro u hu
    refine ⟨hgood u fun a' ha' hnw => ?_, MolMonoSteps_rep_int Γ₂
      (MolMonoSteps_molRep_isRight Γ₁ hu)⟩
    rw [ha', MolMonoSteps_flat_none Γ₁ hnw.1] at hu
    cases hu
  have hV : Γ₂.molRep (.inr b') ∈ Γ₂.toMG'.int := MolMono_molRep_mem_int Γ₂ b'
  rw [List.map_filterMap]
  refine MolMonoSteps_local_pin _ _ S hS (MolMono_inl_not_mem_int Γ₂ a)
    ((MolMono_mem_ext Γ₂ _).2 ⟨a, rfl⟩) hV (pinClass a) G _ _ ?_ ?_
  · intro c hc t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 ht
    obtain ⟨hk, hm, e1, e2, -⟩ := MolMonoSteps_edgeD_some Γ₁ ht₀
    obtain ⟨hF, -⟩ := MolMonoSteps_ext_edge hC hE hG h₁ (hG₁ c hc) hk hm (hGt c hc)
    rw [MolMonoSteps_edgeD_toList Γ₂ hk hm]
    rcases hF with ⟨hcy, hfx⟩ | ⟨hcx, hfy⟩
    · obtain ⟨hx, hxI⟩ := hint c.x hfx
      refine ⟨_, t₀.2.2, hxI, Or.inr ⟨?_, ?_⟩⟩
      · simp only [MolMonoSteps_hat, id, e1, e2, hcy, hf₁]
        rfl
      · rw [hx, hcy, hf₂]
    · obtain ⟨hy, hyI⟩ := hint c.y hfy
      refine ⟨_, t₀.2.2, hyI, Or.inl ⟨?_, ?_⟩⟩
      · simp only [MolMonoSteps_hat, id, e1, e2, hcx, hf₁]
        rfl
      · rw [hy, hcx, hf₂]
  · have hcls : ∀ c ∈ G, ∀ t, (MolMono_edgeD Γ₁ c).map (MolMonoSteps_hat Γ₂ id) = some t →
        (t.2.2 = .minus ↔ a = 2) := by
      intro c hc t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 ht
      obtain ⟨hk, hm, -, -, -⟩ := MolMonoSteps_edgeD_some Γ₁ ht₀
      exact (MolMonoSteps_ext_edge hC hE hG h₁ (hG₁ c hc) hk hm (hGt c hc)).2
    by_cases ha : a = 2
    · subst ha
      refine Or.inr ⟨rfl, fun c hc t ht => (hcls c hc t ht).2 rfl, ?_⟩
      have hdeg := (hE.2.2.2.1 hU).2
      unfold Graph.nonDotDeg at hdeg
      refine le_trans ?_ ((hGc _).trans hdeg)
      refine MolMonoSteps_length_filterMap_le _ _ _ fun c hc hne => ?_
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨t₀, ht₀, -⟩ := Option.map_eq_some_iff.1 ht
      obtain ⟨hk, hm, -, -, -⟩ := MolMonoSteps_edgeD_some Γ₁ ht₀
      have hxd : c.kind ≠ .xdot := fun h => by rw [h] at hm; cases hm
      simpa using ⟨hGt c hc, hk, hxd⟩
    · refine Or.inl ⟨?_, fun c hc t ht h => ha ((hcls c hc t ht).1 h)⟩
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
      · decide
      · decide
      · exact absurd rfl ha

/-- **Dotted and `×`-dotted edges added and `×`-dotted edges removed.** Let `Γ₂` be `Γ₁` with some
`×`-dotted edges removed and some dotted and `×`-dotted edges added. Under the charge pattern of
the block normal form, the clause on the external atoms and without ghost edges in `Γ₁`, the
identity map is `Graph.MolMono`: molecules are joined, and an external atom whose block gets an
internal atom has its edges moved to the molecule of that block, with the edge from that
molecule to the atom added. -/
private theorem MolMonoSteps_dotGen (Γ₁ Γ₂ : Graph 3 n) (hC : Γ₁.ColourInvB)
    (hE : Γ₁.ExtClause) (hG : Γ₁.NoGhost) (K X₁ D₂ : List (Comp (Atom 3 n)))
    (h₁ : Γ₁.comps.Perm (K ++ X₁)) (h₂ : Γ₂.comps.Perm (K ++ D₂))
    (hX : ∀ c ∈ X₁, c.kind = .xdot) (hD : ∀ c ∈ D₂, c.kind = .dot ∨ c.kind = .xdot) :
    Γ₁.MolMono Γ₂ id := by
  classical
  have hK₂ : ∀ c ∈ K, c ∈ Γ₂.comps := fun c hc => h₂.mem_iff.2 (List.mem_append_left _ hc)
  have hK₁ : ∀ c ∈ K, c ∈ Γ₁.comps := fun c hc => h₁.mem_iff.2 (List.mem_append_left _ hc)
  have hnx : ∀ c ∈ Γ₁.comps, c.kind ≠ .xdot → c ∈ K := by
    intro c hc hk
    rcases List.mem_append.1 (h₁.mem_iff.1 hc) with h | h
    · exact h
    · exact absurd (hX c h) hk
  have hF : ∀ u v, Γ₁.SameBlock u v → Γ₂.SameBlock (id u) (id v) := fun u v h =>
    MolMonoSteps_sameBlock_map id (fun c hc hk => Or.inr
      ⟨c, hK₂ c (hnx c hc (by rw [hk]; decide)), hk, rfl, rfl⟩) h
  have hMol : ∀ u v, Γ₁.SameMol u v → Γ₂.SameMol (id u) (id v) := fun u v h =>
    MolMonoSteps_sameMol_map id (fun _ h => h) (fun c hc hk => Or.inr
      ⟨c, hK₂ c (hnx c hc (fun h' => by rw [h'] at hk; cases hk)), hk, rfl, rfl⟩) h
  have h1 : ∀ a b, Γ₁.molRep (.inr a) = Γ₁.molRep (.inr b) →
      Γ₂.molRep (id (.inr a)) = Γ₂.molRep (id (.inr b)) := fun a b h =>
    MolMonoSteps_molRep_of_sameMol Γ₂ (hMol _ _ ((MolMono_molRep_eq_iff Γ₁ a b).1 h))
  have hgood : ∀ u, (∀ a', u = .inl a' → ¬ (Γ₁.anchor (.inl a') = none ∧
      Γ₂.anchor (.inl a') ≠ none)) →
      Γ₂.molRep (Γ₂.flatAtom u) = Γ₂.molRep (id (Γ₁.molRep (Γ₁.flatAtom u))) := by
    intro u hu
    exact MolMonoSteps_good (φ := id) (fun _ => rfl) (fun _ => rfl) h1 hF u
      fun a' ha' hn => by
        by_contra h'
        exact hu a' ha' ⟨hn, h'⟩
  set tag : Fin 3 → Comp (Atom 3 n) → Bool := fun a c =>
    decide ((Γ₁.anchor (.inl a) = none ∧ Γ₂.anchor (.inl a) ≠ none) ∧
      (c.x = .inl a ∨ c.y = .inl a)) with htag
  set K₁ := K.filter fun c => !tag 0 c
  set K₂ := K₁.filter fun c => !tag 1 c
  set G0 := K.filter (tag 0)
  set G1 := K₁.filter (tag 1)
  set G2 := K₂.filter (tag 2)
  set R := K₂.filter fun c => !tag 2 c
  have hKp : K.Perm (G0 ++ (G1 ++ (G2 ++ R))) :=
    (List.filter_append_perm _ K).symm.trans (List.Perm.append_left _
      ((List.filter_append_perm _ K₁).symm.trans (List.Perm.append_left _
        (List.filter_append_perm _ K₂).symm)))
  have hsub1 : K₁.Sublist K := List.filter_sublist
  have hsub2 : K₂.Sublist K := List.filter_sublist.trans hsub1
  have hX0 : X₁.filterMap (MolMono_edgeD Γ₁) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    exact MolMonoSteps_edgeD_mclass Γ₁ (by rw [hX c hc]; rfl)
  have hD0 : D₂.filterMap (MolMono_edgeD Γ₂) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    rcases hD c hc with h | h
    · exact MolMonoSteps_edgeD_dot Γ₂ h
    · exact MolMonoSteps_edgeD_mclass Γ₂ (by rw [h]; rfl)
  set hat := MolMonoSteps_hat Γ₂ (id : Atom 3 n → Atom 3 n) with hhat
  -- The parts of the comparison.
  have part : ∀ (a : Fin 3) (G : List (Comp (Atom 3 n))), G.Sublist K →
      (∀ c ∈ G, tag a c = true) → ∀ S ⊆ Γ₂.toMG'.int,
      MolMono_Local Γ₂.toMG'.int Γ₂.toMG'.ext S
        ((G.filterMap (MolMono_edgeD Γ₁)).map hat ++ ((MolMono_pinD Γ₁ a).map hat).toList)
        (G.filterMap (MolMono_edgeD Γ₂) ++ (MolMono_pinD Γ₂ a).toList) := by
    intro a G hGK hGt S hS
    by_cases hnw : Γ₁.anchor (.inl a) = none ∧ Γ₂.anchor (.inl a) ≠ none
    · obtain ⟨hn₁, hn₂⟩ := hnw
      obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 hn₂
      have hp₁ : MolMono_pinD Γ₁ a = none := by simp [MolMono_pinD, hn₁]
      have hp₂ : MolMono_pinD Γ₂ a = some (Γ₂.molRep (.inr b'), .inl a, pinClass a) := by
        simp [MolMono_pinD, hb']
      rw [hp₁, hp₂]
      simp only [Option.map_none, Option.toList_none, List.append_nil, Option.toList_some]
      refine MolMonoSteps_dot_group hC hE hG hgood hn₁ hb' G (fun c hc => hK₁ c (hGK.subset hc))
        (fun c hc => ?_) (fun p => ?_) S hS
      · have := hGt c hc
        simp only [htag, decide_eq_true_eq] at this
        exact this.2
      · refine ((hGK.filter p).length_le).trans ?_
        rw [(h₁.filter p).length_eq, List.filter_append, List.length_append]
        exact Nat.le_add_right _ _
    · have hG0 : G = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro c hc
        have := hGt c hc
        simp only [htag, decide_eq_true_eq] at this
        exact hnw this.1
      subst hG0
      have hA : Γ₁.anchor (.inl a) = none ↔ Γ₂.anchor (.inl a) = none := by
        constructor
        · intro h
          by_contra h'
          exact hnw ⟨h, h'⟩
        · intro h
          cases h' : Γ₁.anchor (.inl a) with
          | none => rfl
          | some b =>
            have := hF _ _ (MolMonoSteps_anchor_some Γ₁ h')
            exact absurd this ((MolMonoSteps_anchor_none Γ₂).1 h b)
      rw [MolMonoSteps_pin (φ := id) (fun _ => rfl) a hA
        (hgood _ fun a' ha' hn => by cases ha'; exact hnw hn)]
      simp only [List.filterMap_nil, List.map_nil, List.nil_append]
      exact (MolMonoSteps_R.refl _).local _ _ hS
  refine MolMonoSteps_of_local (fun _ => rfl) (fun _ => rfl) h1
    (fun v hv => (MolMono_mem_int Γ₂ v).1 hv) fun S hS => ?_
  have hR : MolMono_Local Γ₂.toMG'.int Γ₂.toMG'.ext S ((R.filterMap (MolMono_edgeD Γ₁)).map hat)
      (R.filterMap (MolMono_edgeD Γ₂)) := by
    rw [List.map_filterMap]
    refine (MolMonoSteps_R.filterMap R _ _ fun c hc => ?_).local _ _ hS
    have hc' : ∀ a, tag a c = false := by
      simp only [R, K₂, K₁, List.mem_filter, Bool.not_eq_true'] at hc
      intro a
      rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
      · exact hc.1.1.2
      · exact hc.1.2
      · exact hc.2
    have hend : ∀ u, (u = c.x ∨ u = c.y) → ∀ a', u = .inl a' →
        ¬ (Γ₁.anchor (.inl a') = none ∧ Γ₂.anchor (.inl a') ≠ none) := by
      intro u hu a' ha' hn
      have := hc' a'
      simp only [htag, decide_eq_false_iff_not, not_and] at this
      rcases hu with rfl | rfl
      · exact this hn (Or.inl ha')
      · exact this hn (Or.inr ha')
    exact MolMonoSteps_edge_R id _ c c rfl (hgood _ (hend _ (Or.inl rfl)))
      (hgood _ (hend _ (Or.inr rfl)))
  have h0 := part 0 G0 List.filter_sublist (fun c hc => (List.mem_filter.1 hc).2) S hS
  have h1' := part 1 G1 (List.filter_sublist.trans hsub1)
    (fun c hc => (List.mem_filter.1 hc).2) S hS
  have h2' := part 2 G2 (List.filter_sublist.trans hsub2)
    (fun c hc => (List.mem_filter.1 hc).2) S hS
  have hall := MolMonoSteps_local_append _ _ _ hR (MolMonoSteps_local_append _ _ _ h0
    (MolMonoSteps_local_append _ _ _ h1' h2'))
  refine MolMonoSteps_local_perm _ _ _ hall ?_ ?_
  · have hp : ((Γ₁.comps.filterMap (MolMono_edgeD Γ₁)).map hat).Perm
        ((G0.filterMap (MolMono_edgeD Γ₁)).map hat ++ ((G1.filterMap (MolMono_edgeD Γ₁)).map hat ++
          ((G2.filterMap (MolMono_edgeD Γ₁)).map hat ++
            (R.filterMap (MolMono_edgeD Γ₁)).map hat))) := by
      have := ((h₁.trans ((hKp.append_right X₁))).filterMap (MolMono_edgeD Γ₁)).map hat
      simpa only [List.filterMap_append, List.map_append, hX0, List.append_nil] using this
    unfold MolMono_edges
    rw [← hhat, List.map_append, MolMonoSteps_filterMap_fin3]
    simp only [List.map_append, Option.toList_map] at hp ⊢
    refine List.Perm.trans ?_ (hp.append_right _).symm
    exact List.perm_iff_count.2 fun x => by simp only [List.count_append]; omega
  · have hp : (Γ₂.comps.filterMap (MolMono_edgeD Γ₂)).Perm
        (G0.filterMap (MolMono_edgeD Γ₂) ++ (G1.filterMap (MolMono_edgeD Γ₂) ++
          (G2.filterMap (MolMono_edgeD Γ₂) ++ R.filterMap (MolMono_edgeD Γ₂)))) := by
      have := (h₂.trans ((hKp.append_right D₂))).filterMap (MolMono_edgeD Γ₂)
      simpa only [List.filterMap_append, hD0, List.append_nil] using this
    unfold MolMono_edges
    rw [MolMonoSteps_filterMap_fin3]
    refine List.Perm.trans ?_ (hp.append_right _).symm
    exact List.perm_iff_count.2 fun x => by simp only [List.count_append]; omega

private theorem MolMonoSteps_perm_eraseIdx {α : Type} {l : List α} {i : ℕ} {c : α}
    (h : l[i]? = some c) : l.Perm (l.eraseIdx i ++ [c]) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  conv_lhs => rw [← List.insertIdx_eraseIdx_getElem hi]
  exact (List.perm_insertIdx _ _ (by rw [List.length_eraseIdx_of_lt hi]; omega)).trans
    (List.perm_append_singleton _ _).symm

/-- **`1 = 1_{u = v} + 1_{u ≠ v}`** ([II, §4.4]): every term is `Graph.MolMono` with its atom
map, under the charge pattern of the block normal form, the clause on the external atoms and
without ghost edges. -/
theorem molMono_oSplitT (u v : Atom 3 n) (Γ : Graph 3 n) (hC : Γ.ColourInvB)
    (hE : Γ.ExtClause) (hG : Γ.NoGhost) (t : Tracked 3 n) (ht : t ∈ oSplitT u v Γ) :
    Γ.MolMono t.g t.f := by
  unfold oSplitT at ht
  split_ifs at ht
  · rw [List.mem_singleton.1 ht]; exact Graph.MolMono.refl Γ
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact MolMonoSteps_dotGen Γ _ hC hE hG Γ.comps [] [mkC .dot u v] (by simp)
        (List.Perm.refl _) (by simp) (by simp [mkC])
    · exact molMono_split_xdot u v Γ

/-- **`1_{u ≠ v} = 1 - 1_{u = v}`** at the `×`-dotted edge with index `i` ([II, §4.4]): every term,
under the charge pattern of the block normal form, the clause on the external atoms and without
ghost edges. -/
theorem molMono_oXdotT (i : ℕ) (Γ : Graph 3 n) (hC : Γ.ColourInvB) (hE : Γ.ExtClause)
    (hG : Γ.NoGhost) (t : Tracked 3 n) (ht : t ∈ oXdotT i Γ) : Γ.MolMono t.g t.f := by
  unfold oXdotT at ht
  split at ht
  · rename_i c hci
    split_ifs at ht with hcond
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact molMono_xdot_erase i Γ c hci hcond.1
      · exact MolMonoSteps_dotGen Γ _ hC hE hG (Γ.comps.eraseIdx i) [c] [mkC .dot c.x c.y]
          (MolMonoSteps_perm_eraseIdx hci) (List.Perm.refl _) (by simpa using hcond.1)
          (by simp [mkC])
    · rw [List.mem_singleton.1 ht]; exact Graph.MolMono.refl Γ
  · rw [List.mem_singleton.1 ht]; exact Graph.MolMono.refl Γ

/-- **A choice of `O_dot`** ([II, Def 4.2]) before `O_merge`, for any list `SP` of pairs and any
choice `A`: dotted edges at the pairs of `A`, `×`-dotted edges at the other pairs with a solid
edge, `×`-dotted edges of the pairs without solid edge removed. The identity map is
`Graph.MolMono` under the charge pattern of the block normal form, the clause on the external
atoms and without ghost edges. -/
theorem molMono_dotChoice (Γ : Graph 3 n) (hC : Γ.ColourInvB) (hE : Γ.ExtClause)
    (hG : Γ.NoGhost) (SP A : List (Atom 3 n × Atom 3 n × Bool)) :
    Γ.MolMono (Γ.dotChoice SP A) id := by
  unfold Graph.dotChoice
  refine MolMonoSteps_dotGen Γ _ hC hE hG _ _ _ (List.filter_append_perm _ _).symm
    (List.Perm.refl _) (fun c hc => ?_) (fun d hd => ?_)
  · have := (List.mem_filter.1 hc).2
    simp only [Bool.not_not, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hd
    split_ifs at hp
    · cases hp; exact Or.inl rfl
    · cases hp; exact Or.inr rfl

end Dots

/-! ## `O_merge` -/

section Merge

variable {k n : ℕ}

private theorem MolMonoSteps_blockRep_spec {V : Type*} [DecidableEq V] (P : List (List V)) (u : V)
    (h : ∃ B ∈ P, u ∈ B) : ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
  obtain ⟨B₀, hB₀, hu₀⟩ := h
  have hs : (P.find? fun B => B.contains u).isSome :=
    List.find?_isSome.2 ⟨B₀, hB₀, by simpa using hu₀⟩
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hs
  have huB : u ∈ B := by simpa using List.find?_some hB
  refine ⟨B, List.mem_of_find?_eq_some hB, huB, ?_⟩
  unfold blockRep
  rw [hB]
  cases B with
  | nil => cases huB
  | cons r rest => exact List.mem_cons_self

/-- An atom lies in the block of its representative of `O_merge`. -/
private theorem MolMonoSteps_sameBlock_mrep (Γ : Graph k n) (u : Atom k n) :
    Γ.SameBlock u (Γ.mrep u) := by
  have h := (Graph.sameBlock_iff_mem_dotBlocks Γ u u).1 (SimpleGraph.Reachable.refl u)
  obtain ⟨B, hB, hu, hr⟩ := MolMonoSteps_blockRep_spec _ u (by
    obtain ⟨B, hB, hu, -⟩ := h
    exact ⟨B, hB, hu⟩)
  exact (Graph.sameBlock_iff_mem_dotBlocks Γ u (Γ.mrep u)).2 ⟨B, hB, hu, hr⟩

/-- Atoms with the same image under `O_merge` lie in one block. -/
private theorem MolMonoSteps_sameBlock_of_f {Γ : Graph k n} {t : Tracked k n}
    (hs : MergeSpec Γ t) {u v : Atom k n} (h : t.f u = t.f v) : Γ.SameBlock u v := by
  by_cases hr : Γ.mrep u = Γ.mrep v
  · exact (MolMonoSteps_sameBlock_mrep Γ u).trans
      (hr ▸ (MolMonoSteps_sameBlock_mrep Γ v).symm)
  · exact absurd h (hs.f_ne u v hr)

/-- The three cases of `mergeComp`. -/
private theorem MolMonoSteps_mergeComp_cases {m : ℕ} (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (c : Comp (Atom k n)) :
    (mergeComp rep f c = none ∧ c.kind = .dot ∧ f c.x = f c.y) ∨
      (∃ ch, c.kind = .G ch ∧ rep c.x = rep c.y ∧
        mergeComp rep f c = some { c.map f with kind := .weight ch, y := f c.x }) ∨
      mergeComp rep f c = some (c.map f) := by
  unfold mergeComp
  split_ifs with h1 h2
  · simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact Or.inl ⟨rfl, h1.1, h1.2⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨hs, hr⟩ := h2
    cases hκ : c.kind with
    | G ch => exact Or.inr (Or.inl ⟨ch, rfl, hr, by simp [Kind.toWeight]⟩)
    | _ => rw [hκ] at hs; cases hs
  · exact Or.inr (Or.inr rfl)

/-- An atom in the block of the internal atom `b` has, in the block normal form, an atom of the
molecule of `b`. -/
private theorem MolMonoSteps_rep_flat_of_block (Γ : Graph k n) {w : Atom k n} {b : Fin n}
    (h : Γ.SameBlock w (.inr b)) : Γ.molRep (Γ.flatAtom w) = Γ.molRep (.inr b) := by
  rcases w with a | a
  · obtain ⟨b', hb'⟩ := MolMonoSteps_anchor_of Γ h
    rw [MolMonoSteps_flat_some Γ hb']
    exact MolMonoSteps_molRep_of_block Γ ((MolMonoSteps_anchor_some Γ hb').symm.trans h)
  · exact MolMonoSteps_molRep_of_block Γ h

/-- **`O_merge`** ([II, Def 4.1]): the atom map of `O_merge` is `Graph.MolMono`, with no
hypothesis on the graph. The molecular graph of the block reading is kept, up to the names of the
molecules, except for the edges between two external atoms of a block without internal atom,
which become weights. -/
theorem molMono_mergeT (Γ : Graph k n) (t : Tracked k n) (ht : Γ.mergeT = some t) :
    Γ.MolMono t.g t.f := by
  have hs := mergeT_spec ht
  have h3 : ∀ a, t.f (.inl a) = .inl a := hs.f_inl
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have h0 : ∀ a, (t.f (.inr a)).isRight = true := fun a => by rw [hg a]; rfl
  have hφ : ∀ u : Atom k n, u.isRight = true → (t.f u).isRight = true := by
    intro u hu
    obtain ⟨b, rfl⟩ := (MolMonoSteps_isRight_iff u).1 hu
    exact h0 b
  have hmem : ∀ c ∈ Γ.comps, ∀ c', mergeComp Γ.mrep t.f c = some c' → c' ∈ t.g.comps := by
    intro c hc c' h
    rw [hs.comps_eq]
    exact List.mem_filterMap.2 ⟨c, hc, h⟩
  have hF : ∀ u v, Γ.SameBlock u v → t.g.SameBlock (t.f u) (t.f v) := by
    intro u v h
    refine MolMonoSteps_sameBlock_map t.f (fun c hc hk => ?_) h
    rcases MolMonoSteps_mergeComp_cases Γ.mrep t.f c with ⟨-, -, he⟩ | ⟨ch, hκ, -, -⟩ | he
    · exact Or.inl he
    · rw [hκ] at hk; cases hk
    · exact Or.inr ⟨_, hmem c hc _ he, hk, rfl, rfl⟩
  have hMol : ∀ u v, Γ.SameMol u v → t.g.SameMol (t.f u) (t.f v) := by
    intro u v h
    refine MolMonoSteps_sameMol_map t.f hφ (fun c hc hk => ?_) h
    rcases MolMonoSteps_mergeComp_cases Γ.mrep t.f c with ⟨-, -, he⟩ | ⟨ch, hκ, -, -⟩ | he
    · exact Or.inl he
    · rw [hκ] at hk; cases hk
    · exact Or.inr ⟨_, hmem c hc _ he, hk, rfl, rfl⟩
  have h1 : ∀ a b, Γ.molRep (.inr a) = Γ.molRep (.inr b) →
      t.g.molRep (t.f (.inr a)) = t.g.molRep (t.f (.inr b)) := fun a b h =>
    MolMonoSteps_molRep_of_sameMol t.g (hMol _ _ ((MolMono_molRep_eq_iff Γ a b).1 h))
  -- Blocks of the image lift to blocks of `Γ`.
  have hlift : ∀ p q, t.g.SameBlock p q → ∀ w, t.f w = p → ∃ w', t.f w' = q ∧ Γ.SameBlock w w' := by
    intro p q hpq w hw
    unfold Graph.SameBlock at hpq
    rw [SimpleGraph.reachable_iff_reflTransGen] at hpq
    induction hpq with
    | refl => exact ⟨w, hw, SimpleGraph.Reachable.refl _⟩
    | @tail r q _ hadj ih =>
      obtain ⟨w₁, hw₁, hww₁⟩ := ih
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      have key : ∀ d ∈ t.g.comps, d.kind = .dot → ∃ c ∈ Γ.comps, c.kind = .dot ∧
          d.x = t.f c.x ∧ d.y = t.f c.y := by
        intro d hd hk
        rw [hs.comps_eq] at hd
        obtain ⟨c, hc, hcd⟩ := List.mem_filterMap.1 hd
        rcases MolMonoSteps_mergeComp_cases Γ.mrep t.f c with ⟨he, -, -⟩ | ⟨ch, -, -, he⟩ | he
        · rw [he] at hcd; cases hcd
        · rw [he] at hcd; cases hcd; cases hk
        · rw [he] at hcd; cases hcd
          exact ⟨c, hc, hk, rfl, rfl⟩
      have hdb : ∀ c ∈ Γ.comps, c.kind = .dot → Γ.SameBlock c.x c.y := fun c hc hk => by
        by_cases hxy : c.x = c.y
        · exact hxy ▸ SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
            ⟨hxy, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)
      rcases hadj.2 with ⟨d, hd, hk, rfl, rfl⟩ | ⟨d, hd, hk, rfl, rfl⟩
      · obtain ⟨c, hc, hck, hx, hy⟩ := key d hd hk
        refine ⟨c.y, hy.symm, hww₁.trans ?_⟩
        exact (MolMonoSteps_sameBlock_of_f hs (hw₁.trans hx)).trans (hdb c hc hck)
      · obtain ⟨c, hc, hck, hx, hy⟩ := key d hd hk
        refine ⟨c.x, hx.symm, hww₁.trans ?_⟩
        exact (MolMonoSteps_sameBlock_of_f hs (hw₁.trans hy)).trans (hdb c hc hck).symm
  have hB : ∀ a, Γ.anchor (.inl a) = none → t.g.anchor (.inl a) = none := by
    intro a ha
    rw [MolMonoSteps_anchor_none] at ha ⊢
    intro j hj
    obtain ⟨w', hw', hb⟩ := hlift _ _ hj (.inl a) (h3 a)
    rcases w' with a' | b
    · rw [h3] at hw'; cases hw'
    · exact ha b hb
  have hA : ∀ a, Γ.anchor (.inl a) = none ↔ t.g.anchor (.inl a) = none := by
    intro a
    refine ⟨hB a, fun h => ?_⟩
    cases h' : Γ.anchor (.inl a) with
    | none => rfl
    | some b =>
      have := hF _ _ (MolMonoSteps_anchor_some Γ h')
      rw [h3, hg b] at this
      exact absurd this ((MolMonoSteps_anchor_none t.g).1 h (g b))
  have hgood : ∀ u, t.g.molRep (t.g.flatAtom (t.f u)) =
      t.g.molRep (t.f (Γ.molRep (Γ.flatAtom u))) := fun u =>
    MolMonoSteps_good h0 h3 h1 hF u fun a _ => hB a
  refine MolMonoSteps_of_R h0 h3 h1 (fun v hv => ?_) ?_
  · obtain ⟨j, rfl⟩ := (MolMono_mem_int t.g v).1 hv
    obtain ⟨i, rfl⟩ := hgs j
    exact ⟨i, by rw [hg i]⟩
  have e : t.g.comps.filterMap (MolMono_edgeD t.g) =
      Γ.comps.filterMap fun c => (mergeComp Γ.mrep t.f c).bind (MolMono_edgeD t.g) := by
    rw [hs.comps_eq, List.filterMap_filterMap]
  unfold MolMono_edges
  rw [List.map_append, List.map_filterMap, List.map_filterMap, e]
  refine MolMonoSteps_R.append (MolMonoSteps_R.filterMap _ _ _ fun c hc => ?_)
    (MolMonoSteps_R.filterMap _ _ _ fun a _ => ?_)
  · rcases MolMonoSteps_mergeComp_cases Γ.mrep t.f c with ⟨he, hk, -⟩ | ⟨ch, hκ, hr, he⟩ | he
    · rw [he, MolMonoSteps_edgeD_dot Γ hk]
      exact .nil _
    · rw [he]
      simp only [Option.bind_some]
      rw [MolMonoSteps_edgeD_mclass t.g rfl]
      cases h₀ : MolMono_edgeD Γ c with
      | none => exact .nil _
      | some t₀ =>
        obtain ⟨-, -, e1, e2, hne⟩ := MolMonoSteps_edgeD_some Γ h₀
        have hxy : Γ.SameBlock c.x c.y := (MolMonoSteps_sameBlock_mrep Γ c.x).trans
          (hr ▸ (MolMonoSteps_sameBlock_mrep Γ c.y).symm)
        refine .drop _ (Or.inr ?_) (.nil _)
        by_cases hb : ∃ b, Γ.SameBlock c.x (.inr b)
        · obtain ⟨b, hb⟩ := hb
          exact absurd (e1.trans ((MolMonoSteps_rep_flat_of_block Γ hb).trans
            (MolMonoSteps_rep_flat_of_block Γ (hxy.symm.trans hb)).symm) |>.trans e2.symm) hne
        · push Not at hb
          have hext : ∀ w, Γ.SameBlock c.x w →
              Γ.molRep (Γ.flatAtom w) = w ∧ ∃ a, w = .inl a := by
            intro w hw
            rcases w with a | b
            · have ha : Γ.anchor (.inl a) = none := (MolMonoSteps_anchor_none Γ).2
                fun b h' => hb b (hw.trans h')
              rw [MolMonoSteps_flat_none Γ ha]
              exact ⟨rfl, a, rfl⟩
            · exact absurd hw (hb b)
          obtain ⟨hx1, a, hxa⟩ := hext c.x (SimpleGraph.Reachable.refl _)
          obtain ⟨hy1, a', hya⟩ := hext c.y hxy
          show t.g.molRep (t.f t₀.1) ∉ _ ∧ t.g.molRep (t.f t₀.2.1) ∉ _
          rw [e1, e2, hx1, hy1, hxa, hya, h3, h3]
          exact ⟨MolMono_inl_not_mem_int t.g a, MolMono_inl_not_mem_int t.g a'⟩
    · rw [he]
      simp only [Option.bind_some]
      exact MolMonoSteps_edge_R t.f _ c (c.map t.f) rfl (hgood c.x) (hgood c.y)
  · rw [MolMonoSteps_pin (Γ₁ := Γ) (Γ₂ := t.g) (φ := t.f) h3 a (hA a) (hgood _)]
    exact MolMonoSteps_R.refl _

/-- **`O_dot`** ([II, Def 4.2]): every term is `Graph.MolMono` with its atom map, on a graph with
the invariant `Graph.InvB'`: a choice of dotted and `×`-dotted edges followed by `O_merge`. -/
theorem molMono_oDotT {n : ℕ} (Γ : Graph 3 n) (hI : Γ.InvB') (t : Tracked 3 n)
    (ht : t ∈ oDotT Γ) : Γ.MolMono t.g t.f := by
  dsimp only [oDotT] at ht
  split_ifs at ht
  · rw [List.mem_singleton.1 ht]; exact Graph.MolMono.refl Γ
  · rw [List.mem_singleton.1 ht]; exact Graph.MolMono.refl Γ
  · obtain ⟨A, -, hA⟩ := List.mem_filterMap.1 ht
    have h := (molMono_dotChoice Γ hI.2.1 hI.2.2.1 hI.2.2.2.1 Γ.splitPairs A).comp
      (molMono_mergeT _ t hA)
    simpa using h

end Merge

/-! ## The steps inside `P_x` -/

section PLift

variable {k n m : ℕ}

private theorem MolMonoSteps_anchor_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) (u : Atom k n) :
    Γ₁.anchor u = Γ₂.anchor u := by
  classical
  rw [MolMono_anchor_eq_find, MolMono_anchor_eq_find]
  congr 1
  funext b
  exact decide_eq_decide.2 (hB _ _)

private theorem MolMonoSteps_flatAtom_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) (u : Atom k n) :
    Γ₁.flatAtom u = Γ₂.flatAtom u := by
  rcases u with a | a
  · simp only [Graph.flatAtom, MolMonoSteps_anchor_congr hB]
  · rfl

private theorem MolMonoSteps_molRep_congr {Γ₁ Γ₂ : Graph k n}
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) (u : Atom k n) :
    Γ₁.molRep u = Γ₂.molRep u := by
  classical
  rcases u with a | a
  · rfl
  · rw [MolMono_molRep_eq_find, MolMono_molRep_eq_find]
    congr 3
    funext b
    exact decide_eq_decide.2 (hM _ _)

private theorem MolMonoSteps_edgeD_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v)
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) : MolMono_edgeD Γ₁ = MolMono_edgeD Γ₂ := by
  funext c
  simp only [MolMono_edgeD, MolMonoSteps_flatAtom_congr hB, MolMonoSteps_molRep_congr hM]

private theorem MolMonoSteps_pinD_congr {Γ₁ Γ₂ : Graph k n}
    (hB : ∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v)
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) : MolMono_pinD Γ₁ = MolMono_pinD Γ₂ := by
  funext a
  simp only [MolMono_pinD, MolMonoSteps_anchor_congr hB, MolMonoSteps_molRep_congr hM]

private theorem MolMonoSteps_int_congr {Γ₁ Γ₂ : Graph k n}
    (hM : ∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) : Γ₁.toMG'.int = Γ₂.toMG'.int := by
  simp only [Graph.toMG', MolMonoSteps_molRep_congr hM]

/-- Every waved or dotted edge of `l₁` has a waved or dotted copy in `l₂` with the same ends,
dotted exactly when it is. -/
private def MolMonoSteps_JoinSub (l₁ l₂ : List (Comp (Atom k n))) : Prop :=
  ∀ c ∈ l₁, c.kind.joinsMol = true → ∃ d ∈ l₂, (d.kind = .dot ↔ c.kind = .dot) ∧
    d.kind.joinsMol = true ∧ d.x = c.x ∧ d.y = c.y

/-- Graphs whose waved and dotted edges correspond have the same blocks and molecules. -/
private theorem MolMonoSteps_same_of_join {Γ₁ Γ₂ : Graph k n}
    (h₁ : MolMonoSteps_JoinSub Γ₁.comps Γ₂.comps) (h₂ : MolMonoSteps_JoinSub Γ₂.comps Γ₁.comps) :
    (∀ u v, Γ₁.SameBlock u v ↔ Γ₂.SameBlock u v) ∧
      (∀ u v, Γ₁.SameMol u v ↔ Γ₂.SameMol u v) := by
  have hdot : ∀ κ : Kind, κ = .dot → κ.joinsMol = true := fun κ h => by rw [h]; rfl
  have hd : Γ₁.dotGraph = Γ₂.dotGraph := by
    unfold Graph.dotGraph
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, h1, -, h3, h4⟩ := h₁ c hc (hdot _ hk)
      exact ⟨d, hd, h1.2 hk, h3, h4⟩
    · rintro ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, h1, -, h3, h4⟩ := h₂ c hc (hdot _ hk)
      exact ⟨d, hd, h1.2 hk, h3, h4⟩
  have hm : Γ₁.molGraph = Γ₂.molGraph := by
    unfold Graph.molGraph
    congr 1
    funext u v
    apply propext
    constructor
    · rintro ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, -, h2, h3, h4⟩ := h₁ c hc hk
      exact ⟨d, hd, h2, h3, h4⟩
    · rintro ⟨c, hc, hk, rfl, rfl⟩
      obtain ⟨d, hd, -, h2, h3, h4⟩ := h₂ c hc hk
      exact ⟨d, hd, h2, h3, h4⟩
  refine ⟨fun u v => by unfold Graph.SameBlock; rw [hd], fun u v => ?_⟩
  unfold Graph.SameMol
  rw [hm]

/-- A copy with the same kind and ends. -/
private theorem MolMonoSteps_joinSub_of {l₁ l₂ : List (Comp (Atom k n))}
    (h : ∀ c ∈ l₁, c.kind.joinsMol = true → ∃ d ∈ l₂, d.kind = c.kind ∧ d.x = c.x ∧ d.y = c.y) :
    MolMonoSteps_JoinSub l₁ l₂ := by
  intro c hc hj
  obtain ⟨d, hd, h1, h2, h3⟩ := h c hc hj
  exact ⟨d, hd, by rw [h1], by rw [h1]; exact hj, h2, h3⟩

private theorem MolMonoSteps_random_join {κ : Kind} (h : κ.isRandom = true) :
    κ.joinsMol = false := by
  cases κ <;> simp_all [Kind.isRandom, Kind.joinsMol]

/-- `MolMono_edgeD` reads only the kind and the ends. -/
private theorem MolMonoSteps_edgeD_eq_of (Γ : Graph k n) {c d : Comp (Atom k n)}
    (h1 : d.kind = c.kind) (h2 : d.x = c.x) (h3 : d.y = c.y) :
    MolMono_edgeD Γ d = MolMono_edgeD Γ c := by
  simp only [MolMono_edgeD, h1, h2, h3]

/-- **A term of an expansion of a graph `C`, with the atom map `f`**: internal atoms go to internal
atoms, external atoms are fixed, molecules go into molecules, the internal molecules of `T` are
hit, the molecule in the block normal form of the image of an atom is the image of its molecule,
the pin edges are carried, and the present edges of the components of `C`, carried to the
molecules of `T`, are replaced by those of `T` as in `MolMonoSteps_R`. -/
private structure MolMonoSteps_Core (C : Graph k n) (T : Graph k m)
    (f : Atom k n → Atom k m) : Prop where
  isRight : ∀ a, (f (.inr a)).isRight = true
  inl : ∀ a, f (.inl a) = .inl a
  molRep_eq : ∀ a b, C.molRep (.inr a) = C.molRep (.inr b) →
    T.molRep (f (.inr a)) = T.molRep (f (.inr b))
  onto : ∀ v ∈ T.toMG'.int, ∃ a, T.molRep (f (.inr a)) = v
  good : ∀ u, T.molRep (T.flatAtom (f u)) = T.molRep (f (C.molRep (C.flatAtom u)))
  pin : ∀ a, MolMono_pinD T a = (MolMono_pinD C a).map (MolMonoSteps_hat T f)
  edges : MolMonoSteps_R T.toMG'.int
    ((C.comps.filterMap (MolMono_edgeD C)).map (MolMonoSteps_hat T f))
    (T.comps.filterMap (MolMono_edgeD T))

/-- **`P_x` of an expansion** ([II, §4.4, Steps 2, 3]): every term of `pLiftT x Γ E` is
`Graph.MolMono` with its atom map when every term of `E` is a term of `Γ.pCore` as in
`MolMonoSteps_Core`; the random factors without label of `Γ` are carried along the atom map. -/
private theorem MolMonoSteps_pLift {x : Atom k n} {Γ : Graph k n} {E : TExpansion k n}
    (hE : ∀ t ∈ E, MolMonoSteps_Core Γ.pCore t.g t.f) :
    ∀ t' ∈ pLiftT x Γ E, Γ.MolMono t'.g t'.f := by
  intro t' ht'
  obtain ⟨t, ht, hsome⟩ := List.mem_filterMap.1 ht'
  split_ifs at hsome
  cases hsome
  have hc := hE t ht
  set C := Γ.pCore with hCdef
  set rl : Comp (Atom k t.nOut) → Comp (Atom k t.nOut) := fun c =>
    if c.kind.isRandom then { c with label := some (.P, t.f x) } else c with hrl
  have hrl' : ∀ c, (rl c).kind = c.kind ∧ (rl c).x = c.x ∧ (rl c).y = c.y := by
    intro c; simp only [hrl]; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  set O : Graph k t.nOut := ⟨t.g.comps.map rl ++ Γ.pEnv.map (Comp.map t.f), t.g.coeff⟩ with hO
  -- `Γ` and `C` have the same blocks and molecules.
  have hq : ∀ c ∈ Γ.comps, c.kind.joinsMol = true →
      (c.label.isSome || !c.kind.isRandom) = true := by
    intro c _ hj
    have : c.kind.isRandom = false := by
      cases hr : c.kind.isRandom
      · rfl
      · rw [MolMonoSteps_random_join hr] at hj; cases hj
    simp [this]
  obtain ⟨hB₁, hM₁⟩ := MolMonoSteps_same_of_join (Γ₁ := Γ) (Γ₂ := C)
    (MolMonoSteps_joinSub_of fun c hc hj => ⟨{ c with label := none },
      List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hq c hc hj⟩, rfl⟩, rfl, rfl, rfl⟩)
    (MolMonoSteps_joinSub_of fun d hd _ => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
      exact ⟨c, (List.mem_filter.1 hc).1, rfl, rfl, rfl⟩)
  -- `t.g` and `O` have the same blocks and molecules.
  obtain ⟨hB₂, hM₂⟩ := MolMonoSteps_same_of_join (Γ₁ := t.g) (Γ₂ := O)
    (MolMonoSteps_joinSub_of fun c hc _ => ⟨rl c, List.mem_append_left _ (List.mem_map_of_mem hc),
      hrl' c⟩)
    (MolMonoSteps_joinSub_of fun d hd hj => by
      rcases List.mem_append.1 hd with hd | hd
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
        obtain ⟨h1, h2, h3⟩ := hrl' c
        exact ⟨c, hc, h1.symm, h2.symm, h3.symm⟩
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
        have hr : c.kind.isRandom = true := by
          have := (List.mem_filter.1 hc).2
          simp only [Bool.and_eq_true] at this
          exact this.2
        exact absurd hj (by rw [show (c.map t.f).kind = c.kind from rfl,
          MolMonoSteps_random_join hr]; simp))
  have hrepO : O.molRep = t.g.molRep := funext fun u => (MolMonoSteps_molRep_congr hM₂ u).symm
  have hhat : MolMonoSteps_hat O t.f = MolMonoSteps_hat t.g t.f := by
    funext p; simp only [MolMonoSteps_hat, hrepO]
  have hrepΓ : Γ.molRep = C.molRep := funext fun u => MolMonoSteps_molRep_congr hM₁ u
  have hintO : O.toMG'.int = t.g.toMG'.int := (MolMonoSteps_int_congr hM₂).symm
  refine MolMonoSteps_of_R hc.isRight hc.inl (fun a b h => ?_) (fun v hv => ?_) ?_
  · rw [hrepO]; rw [hrepΓ] at h; exact hc.molRep_eq a b h
  · rw [hintO] at hv; rw [hrepO]; exact hc.onto v hv
  -- The present edges.
  have hpE : Γ.pEnv = Γ.comps.filter fun c => !(c.label.isSome || !c.kind.isRandom) := by
    unfold Graph.pEnv
    congr 1
    funext c
    cases c.label <;> cases c.kind.isRandom <;> rfl
  have hE₁ : (MolMono_edges Γ).Perm (C.comps.filterMap (MolMono_edgeD C) ++
      Γ.pEnv.filterMap (MolMono_edgeD C) ++ (List.finRange k).filterMap (MolMono_pinD C)) := by
    unfold MolMono_edges
    rw [MolMonoSteps_edgeD_congr hB₁ hM₁, MolMonoSteps_pinD_congr hB₁ hM₁]
    refine List.Perm.append_right _ ?_
    have hCe : C.comps.filterMap (MolMono_edgeD C) =
        (Γ.comps.filter fun c => c.label.isSome || !c.kind.isRandom).filterMap
          (MolMono_edgeD C) := by
      simp only [hCdef, Graph.pCore, List.filterMap_map]
      congr 1
    rw [hCe, hpE, ← List.filterMap_append]
    exact ((List.filter_append_perm _ _).symm).filterMap _
  have hE₂ : MolMono_edges O = t.g.comps.filterMap (MolMono_edgeD t.g) ++
      (Γ.pEnv.map (Comp.map t.f)).filterMap (MolMono_edgeD t.g) ++
        (List.finRange k).filterMap (MolMono_pinD t.g) := by
    unfold MolMono_edges
    rw [← MolMonoSteps_edgeD_congr hB₂ hM₂, ← MolMonoSteps_pinD_congr hB₂ hM₂]
    simp only [hO, List.filterMap_append, List.filterMap_map]
    congr 2
    congr 1
    funext c
    exact MolMonoSteps_edgeD_eq_of t.g (hrl' c).1 (hrl' c).2.1 (hrl' c).2.2
  rw [hhat, hintO, hE₂]
  refine .perm ?_ ((hE₁.map _).symm) (List.Perm.refl _)
  simp only [List.map_append]
  refine MolMonoSteps_R.append (MolMonoSteps_R.append hc.edges ?_) ?_
  · rw [List.map_filterMap, List.filterMap_map]
    refine MolMonoSteps_R.filterMap _ _ _ fun c _ => ?_
    exact MolMonoSteps_edge_R t.f _ c (c.map t.f) rfl (hc.good c.x) (hc.good c.y)
  · rw [List.map_filterMap]
    refine MolMonoSteps_R.filterMap _ _ _ fun a _ => ?_
    rw [hc.pin a]
    exact MolMonoSteps_R.refl _

/-- A term with the same blocks, molecules and present edges as `C`, with the identity map. -/
private theorem MolMonoSteps_core_same {C T : Graph k n}
    (hB : ∀ u v, C.SameBlock u v ↔ T.SameBlock u v) (hM : ∀ u v, C.SameMol u v ↔ T.SameMol u v)
    (hE : (T.comps.filterMap (MolMono_edgeD C)).Perm (C.comps.filterMap (MolMono_edgeD C))) :
    MolMonoSteps_Core C T id := by
  have hrep : T.molRep = C.molRep := funext fun u => (MolMonoSteps_molRep_congr hM u).symm
  have hflat : T.flatAtom = C.flatAtom := funext fun u => (MolMonoSteps_flatAtom_congr hB u).symm
  have hhat : ∀ p : Atom k n × Atom k n × MClass, (∃ u v, p.1 = C.molRep u ∧ p.2.1 = C.molRep v) →
      MolMonoSteps_hat T id p = p := by
    rintro ⟨p1, p2, p3⟩ ⟨u, v, h1, h2⟩
    simp only at h1 h2
    simp only [MolMonoSteps_hat, id, hrep, h1, h2, MolMono_molRep_idem]
  refine ⟨fun _ => rfl, fun _ => rfl, fun a b h => ?_, fun v hv => ?_, fun u => ?_,
    fun a => ?_, ?_⟩
  · simp only [id, hrep]; exact h
  · rw [← MolMonoSteps_int_congr hM] at hv
    obtain ⟨a, ha⟩ := (MolMono_mem_int C v).1 hv
    exact ⟨a, by simp only [id, hrep]; exact ha⟩
  · simp only [id, hrep, hflat, MolMono_molRep_idem]
  · rw [← MolMonoSteps_pinD_congr hB hM]
    cases hp : MolMono_pinD C a with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [hhat p]
      unfold MolMono_pinD at hp
      split at hp
      · cases hp; exact ⟨.inr _, .inl a, rfl, rfl⟩
      · cases hp
  · rw [← MolMonoSteps_edgeD_congr hB hM]
    have hL : (C.comps.filterMap (MolMono_edgeD C)).map (MolMonoSteps_hat T id) =
        C.comps.filterMap (MolMono_edgeD C) := by
      rw [List.map_congr_left (g := id) (fun p hp => hhat p ?_), List.map_id]
      obtain ⟨c, -, hcp⟩ := List.mem_filterMap.1 hp
      obtain ⟨-, -, e1, e2, -⟩ := MolMonoSteps_edgeD_some C hcp
      exact ⟨_, _, e1, e2⟩
    rw [hL]
    exact .perm (MolMonoSteps_R.refl _) (List.Perm.refl _) hE.symm

private theorem MolMonoSteps_filterMap_cons {α β : Type} (D : α → Option β) (c : α) (l : List α) :
    (c :: l).filterMap D = (D c).toList ++ l.filterMap D := by
  cases h : D c <;> simp [h]

/-- The terms of `splitRegular` keep the present edges and the waved and dotted edges. -/
private theorem MolMonoSteps_splitRegular (Γ : Graph k n) (x : Atom k n) :
    ∀ (cs : List (Comp (Atom k n))), ∀ p ∈ splitRegular x cs,
      p.1.filterMap (MolMono_edgeD Γ) = cs.filterMap (MolMono_edgeD Γ) ∧
        ∀ d, (d ∈ p.1 ∧ d.kind.joinsMol = true) ↔ (d ∈ cs ∧ d.kind.joinsMol = true)
  | [], p, hp => by
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    simp
  | c :: cs, p, hp => by
    have ih := MolMonoSteps_splitRegular Γ x cs
    have keep : ∀ q ∈ splitRegular x cs,
        (c :: q.1).filterMap (MolMono_edgeD Γ) = (c :: cs).filterMap (MolMono_edgeD Γ) ∧
          ∀ d, (d ∈ c :: q.1 ∧ d.kind.joinsMol = true) ↔
            (d ∈ c :: cs ∧ d.kind.joinsMol = true) := by
      intro q hq
      obtain ⟨h1, h2⟩ := ih q hq
      refine ⟨by rw [MolMonoSteps_filterMap_cons, MolMonoSteps_filterMap_cons, h1], fun d => ?_⟩
      simp only [List.mem_cons]
      constructor
      · rintro ⟨h | h, hj⟩
        · exact ⟨Or.inl h, hj⟩
        · exact ⟨Or.inr ((h2 d).1 ⟨h, hj⟩).1, hj⟩
      · rintro ⟨h | h, hj⟩
        · exact ⟨Or.inl h, hj⟩
        · exact ⟨Or.inr ((h2 d).2 ⟨h, hj⟩).1, hj⟩
    simp only [splitRegular] at hp
    split at hp
    · rename_i ch hk
      have hD : MolMono_edgeD Γ c = none := MolMonoSteps_edgeD_mclass Γ (by rw [hk]; rfl)
      have hcj : c.kind.joinsMol = false := by rw [hk]; rfl
      split_ifs at hp
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          obtain ⟨h1, h2⟩ := ih q hq
          refine ⟨by rw [MolMonoSteps_filterMap_cons, hD, h1]; rfl, fun d => ?_⟩
          rw [h2 d, List.mem_cons]
          constructor
          · rintro ⟨h, hj⟩; exact ⟨Or.inr h, hj⟩
          · rintro ⟨rfl | h, hj⟩
            · rw [hcj] at hj; cases hj
            · exact ⟨h, hj⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          obtain ⟨h1, h2⟩ := ih q hq
          have hD' : MolMono_edgeD Γ { c with kind := .light ch } = none :=
            MolMonoSteps_edgeD_mclass Γ rfl
          refine ⟨by rw [MolMonoSteps_filterMap_cons, MolMonoSteps_filterMap_cons, hD, hD', h1],
            fun d => ?_⟩
          simp only [List.mem_cons]
          constructor
          · rintro ⟨rfl | h, hj⟩
            · cases hj
            · exact ⟨Or.inr ((h2 d).1 ⟨h, hj⟩).1, hj⟩
          · rintro ⟨rfl | h, hj⟩
            · rw [hcj] at hj; cases hj
            · exact ⟨Or.inr ((h2 d).2 ⟨h, hj⟩).1, hj⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact keep q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact keep q hq

/-- **`O^{(x),1}_weight` inside `P_x`** ([I, Def 3.6 (i)], [II, §4.4, Step 2]): every term is
`Graph.MolMono` with its atom map, with no hypothesis on the graph. -/
theorem molMono_pWeight1 (x : Atom k n) (Γ : Graph k n) (t : Tracked k n)
    (ht : t ∈ pLiftT x Γ (oWeight1T x Γ.pCore)) : Γ.MolMono t.g t.f := by
  refine MolMonoSteps_pLift (fun s hs => ?_) t ht
  unfold oWeight1T at hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
  obtain ⟨h1, h2⟩ := MolMonoSteps_splitRegular Γ.pCore x Γ.pCore.comps p hp
  obtain ⟨hB, hM⟩ := MolMonoSteps_same_of_join (Γ₁ := Γ.pCore) (Γ₂ := ⟨p.1, p.2 * Γ.pCore.coeff⟩)
    (MolMonoSteps_joinSub_of fun d hd hj => ⟨d, ((h2 d).2 ⟨hd, hj⟩).1, rfl, rfl, rfl⟩)
    (MolMonoSteps_joinSub_of fun d hd hj => ⟨d, ((h2 d).1 ⟨hd, hj⟩).1, rfl, rfl, rfl⟩)
  refine MolMonoSteps_core_same hB hM ?_
  change (p.1.filterMap (MolMono_edgeD Γ.pCore)).Perm _
  rw [h1]

/-! ### Complex conjugation -/

private theorem MolMonoSteps_mclass_conj (κ : Kind) :
    κ.conj.mclass = κ.mclass.map MolMonoSteps_sw := by
  cases κ with
  | G c => cases c <;> rfl
  | waved w => cases w <;> rfl
  | aux j r b => cases b <;> rfl
  | _ => rfl

private theorem MolMonoSteps_joins_conj (κ : Kind) : κ.conj.joinsMol = κ.joinsMol := by
  cases κ with
  | G c => cases c <;> rfl
  | weight c => cases c <;> rfl
  | light c => cases c <;> rfl
  | inv c => cases c <;> rfl
  | wD c d => cases c <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem MolMonoSteps_dot_conj (κ : Kind) : κ.conj = .dot ↔ κ = .dot := by
  cases κ with
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

/-- A graph and its complex conjugate have the same blocks and molecules. -/
private theorem MolMonoSteps_same_conj (Γ : Graph k n) :
    (∀ u v, Γ.SameBlock u v ↔ Γ.conj.SameBlock u v) ∧
      (∀ u v, Γ.SameMol u v ↔ Γ.conj.SameMol u v) := by
  refine MolMonoSteps_same_of_join (fun c hc hj => ⟨{ c with kind := c.kind.conj },
    List.mem_map_of_mem hc, MolMonoSteps_dot_conj _, by rw [MolMonoSteps_joins_conj]; exact hj,
    rfl, rfl⟩) (fun d hd hj => ?_)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  exact ⟨c, hc, (MolMonoSteps_dot_conj _).symm, by rw [← MolMonoSteps_joins_conj]; exact hj,
    rfl, rfl⟩

/-- The present edges of the complex conjugate graph: `plus` and `minus` exchanged. -/
private theorem MolMonoSteps_edges_conj (Γ : Graph k n) :
    Γ.conj.comps.filterMap (MolMono_edgeD Γ.conj) =
      (Γ.comps.filterMap (MolMono_edgeD Γ)).map MolMonoSteps_swT := by
  obtain ⟨hB, hM⟩ := MolMonoSteps_same_conj Γ
  rw [← MolMonoSteps_edgeD_congr hB hM, List.map_filterMap]
  show (Γ.comps.map fun c => { c with kind := c.kind.conj }).filterMap _ = _
  rw [List.filterMap_map]
  congr 1
  funext c
  simp only [Function.comp, MolMono_edgeD, MolMonoSteps_dot_conj, MolMonoSteps_mclass_conj]
  split_ifs
  · rfl
  · cases c.kind.mclass <;> rfl

/-- **Complex conjugation of a term** ([I, (3.6)]): a term of the conjugate of `C` gives, after
conjugation, a term of `C`. -/
private theorem MolMonoSteps_core_conj {C : Graph k n} {T : Graph k m} {f : Atom k n → Atom k m}
    (h : MolMonoSteps_Core C.conj T f) : MolMonoSteps_Core C T.conj f := by
  obtain ⟨hB₁, hM₁⟩ := MolMonoSteps_same_conj C
  obtain ⟨hB₂, hM₂⟩ := MolMonoSteps_same_conj T
  have r₁ : C.conj.molRep = C.molRep := funext fun u => (MolMonoSteps_molRep_congr hM₁ u).symm
  have r₂ : T.conj.molRep = T.molRep := funext fun u => (MolMonoSteps_molRep_congr hM₂ u).symm
  have f₁ : C.conj.flatAtom = C.flatAtom := funext fun u =>
    (MolMonoSteps_flatAtom_congr hB₁ u).symm
  have f₂ : T.conj.flatAtom = T.flatAtom := funext fun u =>
    (MolMonoSteps_flatAtom_congr hB₂ u).symm
  have hh : MolMonoSteps_hat T.conj f = MolMonoSteps_hat T f := by
    funext p; simp only [MolMonoSteps_hat, r₂]
  have hi : T.conj.toMG'.int = T.toMG'.int := (MolMonoSteps_int_congr hM₂).symm
  refine ⟨h.isRight, h.inl, fun a b hab => ?_, fun v hv => ?_, fun u => ?_, fun a => ?_, ?_⟩
  · rw [r₂]; rw [← r₁] at hab; exact h.molRep_eq a b hab
  · rw [hi] at hv; rw [r₂]; exact h.onto v hv
  · rw [r₂, f₂, ← r₁, ← f₁]; exact h.good u
  · rw [hh, ← MolMonoSteps_pinD_congr hB₂ hM₂, MolMonoSteps_pinD_congr hB₁ hM₁]; exact h.pin a
  · have he := h.edges.sw
    rw [MolMonoSteps_edges_conj, List.map_map, List.map_map] at he
    rw [hh, hi, MolMonoSteps_edges_conj]
    have hc : (MolMonoSteps_swT ∘ MolMonoSteps_hat T f) ∘ MolMonoSteps_swT =
        MolMonoSteps_hat T f := by
      funext p
      simp only [Function.comp, MolMonoSteps_swT, MolMonoSteps_hat, MolMonoSteps_sw_sw]
    rw [← hc]
    exact he

/-! ### Terms with a new atom joined to `x` -/

private theorem MolMonoSteps_liftA_inj : Function.Injective (liftA (k := k) (n := n) 1) :=
  Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective _ _⟩

/-- **A term with one new atom `α` joined to `x` by a waved edge** ([II, §4.4, Steps 2, 3]): the
components of `C` are the components `K` and `Rem`, those of `T` the lifted `K` and `X`; `Rem`
has no waved or dotted edge, `X` no dotted edge and the waved edge `s_{xα}`. If the present
edges of `Rem` are replaced by those of `X` as in `MolMonoSteps_R` (given that `α` lies in the
molecule of `x` and the molecules in the block normal form of lifted atoms are the lifted
molecules), then `T` is a term of `C` as in `MolMonoSteps_Core`. -/
private theorem MolMonoSteps_core_lift {C : Graph k n} {T : Graph k (n + 1)} {x : Atom k n}
    (hx : x.isRight = true) (K Rem : List (Comp (Atom k n))) (X : List (Comp (Atom k (n + 1))))
    (hC : C.comps.Perm (K ++ Rem)) (hT : T.comps.Perm (liftCs 1 K ++ X))
    (hRem : ∀ c ∈ Rem, c.kind.joinsMol = false) (hXd : ∀ d ∈ X, d.kind ≠ .dot)
    (hsx : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ X)
    (hR : T.molRep (newA 0) = T.molRep (liftA 1 x) →
      (∀ u, T.molRep (T.flatAtom (liftA 1 u)) = T.molRep (liftA 1 (C.molRep (C.flatAtom u)))) →
      MolMonoSteps_R T.toMG'.int ((Rem.filterMap (MolMono_edgeD C)).map
        (MolMonoSteps_hat T (liftA 1))) (X.filterMap (MolMono_edgeD T))) :
    MolMonoSteps_Core C T (liftA 1) := by
  have h3 : ∀ a, liftA (k := k) (n := n) 1 (.inl a) = .inl a := fun _ => rfl
  have h0 : ∀ a, (liftA (k := k) (n := n) 1 (.inr a)).isRight = true := fun _ => rfl
  have hKT : ∀ c ∈ K, c.map (liftA 1) ∈ T.comps := fun c hc =>
    hT.mem_iff.2 (List.mem_append_left _ (List.mem_map_of_mem hc))
  have hCK : ∀ c ∈ C.comps, c.kind.joinsMol = true → c ∈ K := by
    intro c hc hj
    rcases List.mem_append.1 (hC.mem_iff.1 hc) with h | h
    · exact h
    · rw [hRem c h] at hj; cases hj
  have hF : ∀ u v, C.SameBlock u v → T.SameBlock (liftA 1 u) (liftA 1 v) := fun u v h =>
    MolMonoSteps_sameBlock_map _ (fun c hc hk => Or.inr ⟨_, hKT c (hCK c hc (by rw [hk]; rfl)),
      hk, rfl, rfl⟩) h
  have hφ : ∀ u : Atom k n, u.isRight = true → (liftA 1 u).isRight = true := by
    intro u hu
    obtain ⟨b, rfl⟩ := (MolMonoSteps_isRight_iff u).1 hu
    rfl
  have h1 : ∀ a b, C.molRep (.inr a) = C.molRep (.inr b) →
      T.molRep (liftA 1 (.inr a)) = T.molRep (liftA 1 (.inr b)) := fun a b h =>
    MolMonoSteps_molRep_of_sameMol T (MolMonoSteps_sameMol_map _ hφ
      (fun c hc hk => Or.inr ⟨_, hKT c (hCK c hc hk), hk, rfl, rfl⟩)
      ((MolMono_molRep_eq_iff C a b).1 h))
  obtain ⟨i₀, rfl⟩ := (MolMonoSteps_isRight_iff x).1 hx
  have hα : T.molRep (newA 0) = T.molRep (liftA 1 (.inr i₀)) := by
    refine MolMonoSteps_molRep_of_sameMol T (Or.inr ⟨rfl, rfl, ?_⟩)
    refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨?_, Or.inr
      ⟨_, hT.mem_iff.2 (List.mem_append_right _ hsx), rfl, rfl, rfl⟩⟩)
    intro h
    simp only [newA, liftA, Sum.map_inr, Sum.inr.injEq, Fin.ext_iff, Fin.val_natAdd,
      Fin.val_castAdd] at h
    omega
  -- Blocks of `T` lift to blocks of `C`.
  have hlift : ∀ p q, T.SameBlock p q → ∀ w, liftA 1 w = p →
      ∃ w', liftA 1 w' = q ∧ C.SameBlock w w' := by
    intro p q hpq w hw
    unfold Graph.SameBlock at hpq
    rw [SimpleGraph.reachable_iff_reflTransGen] at hpq
    induction hpq with
    | refl => exact ⟨w, hw, SimpleGraph.Reachable.refl _⟩
    | @tail r q _ hadj ih =>
      obtain ⟨w₁, hw₁, hww₁⟩ := ih
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      have key : ∀ d ∈ T.comps, d.kind = .dot → ∃ c ∈ C.comps, c.kind = .dot ∧
          d.x = liftA 1 c.x ∧ d.y = liftA 1 c.y := by
        intro d hd hk
        rcases List.mem_append.1 (hT.mem_iff.1 hd) with h | h
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
          exact ⟨c, hC.mem_iff.2 (List.mem_append_left _ hc), hk, rfl, rfl⟩
        · exact absurd hk (hXd d h)
      have hdb : ∀ c ∈ C.comps, c.kind = .dot → C.SameBlock c.x c.y := fun c hc hk => by
        by_cases hxy : c.x = c.y
        · exact hxy ▸ SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
            ⟨hxy, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)
      rcases hadj.2 with ⟨d, hd, hk, rfl, rfl⟩ | ⟨d, hd, hk, rfl, rfl⟩
      · obtain ⟨c, hc, hck, hx', hy'⟩ := key d hd hk
        have := MolMonoSteps_liftA_inj (hw₁.trans hx')
        subst this
        exact ⟨c.y, hy'.symm, hww₁.trans (hdb c hc hck)⟩
      · obtain ⟨c, hc, hck, hx', hy'⟩ := key d hd hk
        have := MolMonoSteps_liftA_inj (hw₁.trans hy')
        subst this
        exact ⟨c.x, hx'.symm, hww₁.trans (hdb c hc hck).symm⟩
  have hB : ∀ a, C.anchor (.inl a) = none → T.anchor (.inl a) = none := by
    intro a ha
    rw [MolMonoSteps_anchor_none] at ha ⊢
    intro j hj
    obtain ⟨w', hw', hb⟩ := hlift _ _ hj (.inl a) rfl
    rcases w' with a' | b
    · cases hw'
    · exact ha b hb
  have hA : ∀ a, C.anchor (.inl a) = none ↔ T.anchor (.inl a) = none := by
    intro a
    refine ⟨hB a, fun h => ?_⟩
    cases h' : C.anchor (.inl a) with
    | none => rfl
    | some b =>
      exact (((MolMonoSteps_anchor_none T).1 h _) (hF _ _ (MolMonoSteps_anchor_some C h'))).elim
  have hgood : ∀ u, T.molRep (T.flatAtom (liftA 1 u)) =
      T.molRep (liftA 1 (C.molRep (C.flatAtom u))) := fun u =>
    MolMonoSteps_good h0 h3 h1 hF u fun a _ => hB a
  refine ⟨h0, h3, h1, fun v hv => ?_, hgood, fun a => MolMonoSteps_pin h3 a (hA a) (hgood _), ?_⟩
  · obtain ⟨j, rfl⟩ := (MolMono_mem_int T v).1 hv
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact ⟨i, rfl⟩
    · refine ⟨i₀, ?_⟩
      rw [← hα]
      congr 2
  · have hl : (C.comps.filterMap (MolMono_edgeD C)).map (MolMonoSteps_hat T (liftA 1)) |>.Perm
        ((K.filterMap (MolMono_edgeD C)).map (MolMonoSteps_hat T (liftA 1)) ++
          (Rem.filterMap (MolMono_edgeD C)).map (MolMonoSteps_hat T (liftA 1))) := by
      rw [← List.map_append, ← List.filterMap_append]
      exact (hC.filterMap _).map _
    have hr : (T.comps.filterMap (MolMono_edgeD T)).Perm
        ((liftCs 1 K).filterMap (MolMono_edgeD T) ++ X.filterMap (MolMono_edgeD T)) := by
      rw [← List.filterMap_append]
      exact hT.filterMap _
    refine .perm (MolMonoSteps_R.append ?_ (hR hα hgood)) hl.symm hr.symm
    rw [List.map_filterMap, liftCs, List.filterMap_map]
    exact MolMonoSteps_R.filterMap _ _ _ fun c _ =>
      MolMonoSteps_edge_R _ _ c (c.map (liftA 1)) rfl (hgood c.x) (hgood c.y)

/-- The class of the solid edge of charge `ch`. -/
private def MolMonoSteps_chClass : Charge → MClass
  | .plus => .plus
  | .minus => .minus

/-- The present edge of `solidC ch a b`. -/
private theorem MolMonoSteps_edgeD_solidC (Γ : Graph k n) (ch : Charge) (a b : Atom k n) :
    (MolMono_edgeD Γ (solidC ch a b)).toList =
      MolMono_opt (Γ.molRep (Γ.flatAtom a)) (Γ.molRep (Γ.flatAtom b))
        (MolMonoSteps_chClass ch) := by
  unfold solidC
  split_ifs with hab
  · subst hab
    rw [MolMonoSteps_edgeD_mclass Γ rfl]
    simp [MolMono_opt]
  · rw [MolMonoSteps_edgeD_toList Γ (by simp [mkC]) (m := MolMonoSteps_chClass ch)
      (by cases ch <;> rfl)]
    rfl

/-- **The derivative pieces through the molecule `V`** ([I, (3.8)]): a random component replaced
by its two factors `G_{ap} G_{qb}` (or `Ḡ_{aq} Ḡ_{pb}`), with `p`, `q` in the molecule `V`: the
edge is replaced by a path through `V`, and a weight (no edge) by two edges. -/
private theorem MolMonoSteps_dPieces_R {C : Graph k n} {T : Graph k (n + 1)}
    (I : Finset (Atom k (n + 1))) {V : Atom k (n + 1)} (hV : V ∈ I) {p q : Atom k (n + 1)}
    (hp : T.molRep (T.flatAtom p) = V) (hq : T.molRep (T.flatAtom q) = V)
    (hgood : ∀ u, T.molRep (T.flatAtom (liftA 1 u)) = T.molRep (liftA 1 (C.molRep (C.flatAtom u))))
    (c : Comp (Atom k n)) (ps : List (Comp (Atom k (n + 1))))
    (hps : (c.map (liftA 1)).dPieces p q = some ps) :
    MolMonoSteps_R I (((MolMono_edgeD C c).map (MolMonoSteps_hat T (liftA 1))).toList)
      (ps.filterMap (MolMono_edgeD T)) := by
  have hG : ∀ ch, c.kind = .G ch → ∀ u₁ u₂ : Atom k (n + 1),
      T.molRep (T.flatAtom u₁) = V → T.molRep (T.flatAtom u₂) = V →
      ps = [solidC ch (liftA 1 c.x) u₁, solidC ch u₂ (liftA 1 c.y)] →
      MolMonoSteps_R I (((MolMono_edgeD C c).map (MolMonoSteps_hat T (liftA 1))).toList)
        (ps.filterMap (MolMono_edgeD T)) := by
    intro ch hk u₁ u₂ h₁ h₂ hps'
    subst hps'
    rw [MolMonoSteps_filterMap_cons, MolMonoSteps_filterMap_cons, List.filterMap_nil,
      List.append_nil, MolMonoSteps_edgeD_solidC, MolMonoSteps_edgeD_solidC, h₁, h₂,
      hgood, hgood]
    have hk' : c.kind ≠ .dot := by rw [hk]; simp
    have hm : c.kind.mclass = some (MolMonoSteps_chClass ch) := by rw [hk]; cases ch <;> rfl
    unfold MolMono_edgeD
    by_cases he : C.molRep (C.flatAtom c.x) = C.molRep (C.flatAtom c.y)
    · simp only [he, or_true, ite_true, Option.map_none, Option.toList_none]
      exact .nil _
    · simp only [hk', he, or_self, ite_false, hm, Option.map_some, Option.toList_some,
        MolMonoSteps_hat]
      have := MolMonoSteps_R.path (I := I) (T.molRep (liftA 1 (C.molRep (C.flatAtom c.x))))
        (T.molRep (liftA 1 (C.molRep (C.flatAtom c.y)))) V (MolMonoSteps_chClass ch) hV
        (MolMonoSteps_R.nil (I := I) [])
      simpa using this
  have hW : c.kind.mclass = none → MolMonoSteps_R I
      (((MolMono_edgeD C c).map (MolMonoSteps_hat T (liftA 1))).toList)
      (ps.filterMap (MolMono_edgeD T)) := fun h => by
    rw [MolMonoSteps_edgeD_mclass C h]; exact .nil _
  unfold Comp.dPieces at hps
  simp only [Comp.map] at hps
  cases hk : c.kind with
  | G ch =>
    cases ch with
    | plus =>
      simp only [hk, Option.some.injEq, Kind.isWeight] at hps
      exact hG .plus hk p q hp hq (by rw [← hps]; rfl)
    | minus =>
      simp only [hk, Option.some.injEq, Kind.isWeight] at hps
      exact hG .minus hk q p hq hp (by rw [← hps]; rfl)
  | weight ch => exact hW (by rw [hk]; rfl)
  | light ch => exact hW (by rw [hk]; rfl)
  | _ => simp [hk] at hps

/-- The terms of `dTerms`: one random component replaced by its two factors. -/
private theorem MolMonoSteps_mem_dTerms {V : Type*} [DecidableEq V] {p q : V}
    {cs : List (Comp V)} {d : List (Comp V)} (h : d ∈ dTerms p q cs) :
    ∃ j, ∃ hj : j < cs.length, ∃ ps, cs[j].dPieces p q = some ps ∧ d = cs.eraseIdx j ++ ps := by
  unfold dTerms at h
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 h
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hi
  exact ⟨i, i.2, ps, hps, rfl⟩

/-- The two factors of a random component are solid edges or weights. -/
private theorem MolMonoSteps_dPieces_kind {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) :
    c.kind.joinsMol = false ∧ ∀ d ∈ ps, d.kind ≠ .dot := by
  have hs : ∀ (ch : Charge) (a b : V), (solidC ch a b).kind ≠ .dot := by
    intro ch a b; unfold solidC; split_ifs <;> simp [mkC]
  have hps : ∀ a b, ps = [a, b] → (∀ d ∈ ps, d.kind = .dot → d = a ∨ d = b) := by
    intro a b h d hd _; rw [h] at hd; simpa using hd
  have key : ∀ (ch : Charge) (a b e f : V), [solidC ch a b, solidC ch e f] = ps →
      ∀ d ∈ ps, d.kind ≠ .dot := by
    rintro ch a b e f rfl d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact hs _ _ _
  obtain ⟨κ, cx, cy, mi, la⟩ := c
  unfold Comp.dPieces at h
  cases κ with
  | G ch => cases ch <;> exact ⟨rfl, key _ _ _ _ _ (Option.some.inj h)⟩
  | weight ch => cases ch <;> exact ⟨rfl, key _ _ _ _ _ (Option.some.inj h)⟩
  | light ch => cases ch <;> exact ⟨rfl, key _ _ _ _ _ (Option.some.inj h)⟩
  | _ => cases h

/-! ### Selections of entries by their indices -/

/-- The entries of `l` whose index satisfies `q`. -/
private def MolMonoSteps_sel {α : Type} (q : ℕ → Bool) (l : List α) : List α :=
  (l.zipIdx.filter fun p => q p.2).map Prod.fst

private theorem MolMonoSteps_zipIdx_nodup {α : Type} (l : List α) : l.zipIdx.Nodup :=
  List.Nodup.of_map Prod.snd (by rw [List.zipIdx_map_snd]; exact List.nodup_range' ..)

private theorem MolMonoSteps_zipIdx_lt {α : Type} {l : List α} {p : α × ℕ} (h : p ∈ l.zipIdx) :
    p.2 < l.length ∧ l[p.2]? = some p.1 := by
  have h' := List.mem_zipIdx_iff_getElem?.1 h
  exact ⟨(List.getElem?_eq_some_iff.1 h').1, h'⟩

/-- Selections with disjoint conditions are joined by the disjunction. -/
private theorem MolMonoSteps_sel_append {α : Type} (q₁ q₂ q : ℕ → Bool) (l : List α)
    (h : ∀ i < l.length, q i = (q₁ i || q₂ i))
    (hd : ∀ i < l.length, ¬ (q₁ i = true ∧ q₂ i = true)) :
    (MolMonoSteps_sel q₁ l ++ MolMonoSteps_sel q₂ l).Perm (MolMonoSteps_sel q l) := by
  unfold MolMonoSteps_sel
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have hn := MolMonoSteps_zipIdx_nodup l
  refine (List.perm_ext_iff_of_nodup ?_ (hn.filter _)).2 fun p => ?_
  · refine List.nodup_append.2 ⟨hn.filter _, hn.filter _, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨ha, h1⟩ := List.mem_filter.1 ha
    exact hd a.2 (MolMonoSteps_zipIdx_lt ha).1 ⟨h1, (List.mem_filter.1 hb).2⟩
  · simp only [List.mem_append, List.mem_filter]
    constructor
    · rintro (⟨hp, h1⟩ | ⟨hp, h2⟩)
      · exact ⟨hp, by rw [h _ (MolMonoSteps_zipIdx_lt hp).1, h1]; rfl⟩
      · exact ⟨hp, by rw [h _ (MolMonoSteps_zipIdx_lt hp).1, h2, Bool.or_true]⟩
    · rintro ⟨hp, hq⟩
      rw [h _ (MolMonoSteps_zipIdx_lt hp).1, Bool.or_eq_true] at hq
      rcases hq with hq | hq
      · exact Or.inl ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hq⟩

/-- The selection of all entries. -/
private theorem MolMonoSteps_sel_all {α : Type} (q : ℕ → Bool) (l : List α)
    (h : ∀ i < l.length, q i = true) : MolMonoSteps_sel q l = l := by
  unfold MolMonoSteps_sel
  rw [List.filter_eq_self.2 fun p hp => h _ (MolMonoSteps_zipIdx_lt hp).1, List.zipIdx_map_fst]

/-- The selection of one index. -/
private theorem MolMonoSteps_sel_one {α : Type} (q : ℕ → Bool) (l : List α) {i : ℕ} {c : α}
    (hc : l[i]? = some c) (h : ∀ j < l.length, q j = true ↔ j = i) :
    (MolMonoSteps_sel q l).Perm [c] := by
  unfold MolMonoSteps_sel
  have hn := MolMonoSteps_zipIdx_nodup l
  have : (l.zipIdx.filter fun p => q p.2).Perm [(c, i)] := by
    refine (List.perm_ext_iff_of_nodup (hn.filter _) (List.nodup_singleton _)).2 fun p => ?_
    simp only [List.mem_filter, List.mem_singleton]
    constructor
    · rintro ⟨hp, hq⟩
      obtain ⟨hlt, hget⟩ := MolMonoSteps_zipIdx_lt hp
      have hpi := (h _ hlt).1 hq
      rw [hpi, hc] at hget
      cases hget
      rw [← hpi]
    · rintro rfl
      exact ⟨List.mem_zipIdx_iff_getElem?.2 hc,
        (h _ (List.getElem?_eq_some_iff.1 hc).1).2 rfl⟩
  simpa using this.map Prod.fst

/-- A list is the entries outside two distinct indices followed by the entries at the two
indices. -/
private theorem MolMonoSteps_perm_erase2 {α : Type} {l : List α} {i₁ i₂ : ℕ} {c₁ c₂ : α}
    (h₁ : l[i₁]? = some c₁) (h₂ : l[i₂]? = some c₂) (hne : i₁ ≠ i₂) :
    l.Perm (eraseIdxs [i₁, i₂] l ++ [c₁, c₂]) := by
  have e1 := MolMonoSteps_sel_one (fun j => j == i₁) l h₁ (fun j _ => by simp)
  have e2 := MolMonoSteps_sel_one (fun j => j == i₂) l h₂ (fun j _ => by simp)
  have e12 := MolMonoSteps_sel_append (fun j => j == i₁) (fun j => j == i₂)
    (fun j => [i₁, i₂].contains j) l (fun j _ => by
      simp only [List.contains_cons, List.contains_nil, Bool.or_false])
    (fun j _ h => by
      simp only [beq_iff_eq] at h
      exact hne (h.1.symm.trans h.2))
  have e := MolMonoSteps_sel_append (fun j => !([i₁, i₂].contains j)) (fun j => [i₁, i₂].contains j)
    (fun _ => true) l (fun j _ => by cases [i₁, i₂].contains j <;> rfl)
    (fun j _ h => by
      obtain ⟨h1, h2⟩ := h
      rw [h2] at h1
      cases h1)
  rw [MolMonoSteps_sel_all _ l fun _ _ => rfl] at e
  refine e.symm.trans (List.Perm.append_left _ ?_)
  exact e12.symm.trans (e1.append e2)

/-- The indices of the solid edges of a given charge leaving or entering `x`. -/
private theorem MolMonoSteps_mem_edgeIdx {Γ : Graph k n} {x : Atom k n} {ch : Charge}
    {out : Bool} {j : ℕ} (h : j ∈ Γ.edgeIdx x ch out) :
    ∃ c, Γ.comps[j]? = some c ∧ c.kind = .G ch ∧
      (out = true → c.x = x ∧ c.y ≠ x) ∧ (out = false → c.y = x ∧ c.x ≠ x) := by
  unfold Graph.edgeIdx at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨hp, hq⟩ := List.mem_filter.1 hp
  refine ⟨p.1, (MolMonoSteps_zipIdx_lt hp).2, ?_⟩
  cases out <;> simp_all

/-! ### Terms obtained from other terms -/

/-- A term whose components are those of a term `T` with the same kinds and ends (labels
changed), followed by components without waved or dotted edges. -/
private theorem MolMonoSteps_core_mapExtra {C : Graph k n} {T T' : Graph k m}
    {f : Atom k n → Atom k m} (h : MolMonoSteps_Core C T f)
    (g : Comp (Atom k m) → Comp (Atom k m))
    (hg : ∀ c, (g c).kind = c.kind ∧ (g c).x = c.x ∧ (g c).y = c.y)
    (E : List (Comp (Atom k m))) (hE : ∀ d ∈ E, d.kind.joinsMol = false)
    (hT : T'.comps = T.comps.map g ++ E) : MolMonoSteps_Core C T' f := by
  obtain ⟨hB, hM⟩ := MolMonoSteps_same_of_join (Γ₁ := T) (Γ₂ := T')
    (MolMonoSteps_joinSub_of fun c hc _ =>
      ⟨g c, by rw [hT]; exact List.mem_append_left _ (List.mem_map_of_mem hc), hg c⟩)
    (MolMonoSteps_joinSub_of fun d hd hj => by
      rw [hT] at hd
      rcases List.mem_append.1 hd with hd | hd
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
        obtain ⟨h1, h2, h3⟩ := hg c
        exact ⟨c, hc, h1.symm, h2.symm, h3.symm⟩
      · rw [hE d hd] at hj; cases hj)
  have r : T'.molRep = T.molRep := funext fun u => (MolMonoSteps_molRep_congr hM u).symm
  have fl : T'.flatAtom = T.flatAtom := funext fun u => (MolMonoSteps_flatAtom_congr hB u).symm
  have hh : MolMonoSteps_hat T' f = MolMonoSteps_hat T f := by
    funext p; simp only [MolMonoSteps_hat, r]
  have hi : T'.toMG'.int = T.toMG'.int := (MolMonoSteps_int_congr hM).symm
  refine ⟨h.isRight, h.inl, fun a b hab => ?_, fun v hv => ?_, fun u => ?_, fun a => ?_, ?_⟩
  · rw [r]; exact h.molRep_eq a b hab
  · rw [hi] at hv; rw [r]; exact h.onto v hv
  · rw [r, fl]; exact h.good u
  · rw [hh, ← MolMonoSteps_pinD_congr hB hM]; exact h.pin a
  · rw [hh, hi, ← MolMonoSteps_edgeD_congr hB hM, hT, List.filterMap_append, List.filterMap_map]
    have he : (MolMono_edgeD T ∘ g) = MolMono_edgeD T := funext fun c =>
      MolMonoSteps_edgeD_eq_of T (hg c).1 (hg c).2.1 (hg c).2.2
    rw [he]
    exact .perm (h.edges.weaken (E.filterMap (MolMono_edgeD T))) (List.Perm.refl _)
      List.perm_append_comm

/-- The identity map from a graph to itself with its labels changed. -/
private theorem MolMonoSteps_core_relabel (C : Graph k n) (T : Graph k n)
    (g : Comp (Atom k n) → Comp (Atom k n))
    (hg : ∀ c, (g c).kind = c.kind ∧ (g c).x = c.x ∧ (g c).y = c.y)
    (hT : T.comps = C.comps.map g) : MolMonoSteps_Core C T id :=
  MolMonoSteps_core_mapExtra (MolMonoSteps_core_same (C := C) (T := C) (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (List.Perm.refl _)) g hg [] (by simp) (by rw [hT, List.append_nil])

/-- `Comp.labelQ` keeps the kind and the ends. -/
private theorem MolMonoSteps_labelQ {V : Type*} (u : V) (c : Comp V) :
    (c.labelQ u).kind = c.kind ∧ (c.labelQ u).x = c.x ∧ (c.labelQ u).y = c.y := by
  unfold Comp.labelQ; split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-! ### Terms with a new atom: the comparison of the replaced components -/

/-- Replacements of the present edges, one component at a time. -/
private theorem MolMonoSteps_R_of_forall₂ {Γ₁ : Graph k n} {Γ₂ : Graph k m}
    {I : Finset (Atom k m)} (φ : Atom k n → Atom k m) {Rem : List (Comp (Atom k n))}
    {Xs : List (List (Comp (Atom k m)))}
    (h : List.Forall₂ (fun c xs => MolMonoSteps_R I
      ((MolMono_edgeD Γ₁ c).map (MolMonoSteps_hat Γ₂ φ)).toList
      (xs.filterMap (MolMono_edgeD Γ₂))) Rem Xs)
    (extra X : List (Comp (Atom k m))) (hX : X.Perm (Xs.flatten ++ extra)) :
    MolMonoSteps_R I ((Rem.filterMap (MolMono_edgeD Γ₁)).map (MolMonoSteps_hat Γ₂ φ))
      (X.filterMap (MolMono_edgeD Γ₂)) := by
  have key : MolMonoSteps_R I ((Rem.filterMap (MolMono_edgeD Γ₁)).map (MolMonoSteps_hat Γ₂ φ))
      (Xs.flatten.filterMap (MolMono_edgeD Γ₂)) := by
    clear hX
    induction h with
    | nil => exact .nil _
    | @cons c xs Rem' Xs' hc _ ih =>
      rw [MolMonoSteps_filterMap_cons, List.map_append, List.flatten_cons,
        List.filterMap_append]
      have e : ((MolMono_edgeD Γ₁ c).toList).map (MolMonoSteps_hat Γ₂ φ) =
          ((MolMono_edgeD Γ₁ c).map (MolMonoSteps_hat Γ₂ φ)).toList := by
        cases MolMono_edgeD Γ₁ c <;> rfl
      rw [e]
      exact hc.append ih
  refine .perm (key.weaken (extra.filterMap (MolMono_edgeD Γ₂))) (List.Perm.refl _) ?_
  rw [← List.filterMap_append]
  exact ((hX.trans List.perm_append_comm).filterMap _).symm

/-- A component without class has no present edge. -/
private theorem MolMonoSteps_noEdge {Γ₁ : Graph k n} {Γ₂ : Graph k m} {I : Finset (Atom k m)}
    (φ : Atom k n → Atom k m) {c : Comp (Atom k n)} (h : c.kind.mclass = none)
    (B : List (Atom k m × Atom k m × MClass)) :
    MolMonoSteps_R I ((MolMono_edgeD Γ₁ c).map (MolMonoSteps_hat Γ₂ φ)).toList B := by
  rw [MolMonoSteps_edgeD_mclass Γ₁ h]; exact .nil _

/-- A component replaced by a component of the same kind, each end kept (lifted) or moved from
`x` to the new atom. -/
private theorem MolMonoSteps_keepPair {C : Graph k n} {T : Graph k (n + 1)} {x : Atom k n}
    (hx : x.isRight = true) {I : Finset (Atom k (n + 1))}
    (hα : T.molRep (T.flatAtom (newA 0)) = T.molRep (liftA 1 x))
    (hgood : ∀ u, T.molRep (T.flatAtom (liftA 1 u)) = T.molRep (liftA 1 (C.molRep (C.flatAtom u))))
    (c : Comp (Atom k n)) (c' : Comp (Atom k (n + 1))) (hk : c'.kind = c.kind)
    (ex : c'.x = liftA 1 c.x ∨ (c'.x = newA 0 ∧ c.x = x))
    (ey : c'.y = liftA 1 c.y ∨ (c'.y = newA 0 ∧ c.y = x)) :
    MolMonoSteps_R I ((MolMono_edgeD C c).map (MolMonoSteps_hat T (liftA 1))).toList
      ([c'].filterMap (MolMono_edgeD T)) := by
  obtain ⟨i₀, rfl⟩ := (MolMonoSteps_isRight_iff x).1 hx
  have hend : ∀ (u' : Atom k (n + 1)) (u : Atom k n),
      (u' = liftA 1 u ∨ (u' = newA 0 ∧ u = .inr i₀)) →
      T.molRep (T.flatAtom u') = T.molRep (liftA 1 (C.molRep (C.flatAtom u))) := by
    rintro u' u (rfl | ⟨rfl, rfl⟩)
    · exact hgood u
    · rw [hα, ← hgood]; rfl
  rw [MolMonoSteps_filterMap_cons, List.filterMap_nil, List.append_nil]
  exact MolMonoSteps_edge_R _ _ c c' hk (hend _ _ ex) (hend _ _ ey)

/-- **A term with one new atom `α` joined to `x`**, in the form used for the identities
[II, (4.23)] and [II, (4.24)]: `C` is the kept components `K` and the replaced components `Rem`
(without waved or dotted edges), the term is the lifted `K` and the components `X` (without
dotted edges, with the waved edge `s_{xα}`), and the present edges of each replaced component are
replaced by those of a group of components of `X`. -/
private theorem MolMonoSteps_core_gen {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    (K Rem : List (Comp (Atom k n))) (hC : C.comps.Perm (K ++ Rem))
    (hRem : ∀ c ∈ Rem, c.kind.joinsMol = false)
    (X : List (Comp (Atom k (n + 1)))) (hXd : ∀ d ∈ X, d.kind ≠ .dot)
    (hsx : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ X) (d : Coeff)
    (Xs : List (List (Comp (Atom k (n + 1))))) (extra : List (Comp (Atom k (n + 1))))
    (hX : X.Perm (Xs.flatten ++ extra))
    (hpair : let T : Graph k (n + 1) := ⟨liftCs 1 K ++ X, d⟩
      T.molRep (T.flatAtom (newA 0)) = T.molRep (liftA 1 x) →
      (∀ u, T.molRep (T.flatAtom (liftA 1 u)) = T.molRep (liftA 1 (C.molRep (C.flatAtom u)))) →
      T.molRep (liftA 1 x) ∈ T.toMG'.int →
      List.Forall₂ (fun c xs => MolMonoSteps_R T.toMG'.int
        ((MolMono_edgeD C c).map (MolMonoSteps_hat T (liftA 1))).toList
        (xs.filterMap (MolMono_edgeD T))) Rem Xs) :
    MolMonoSteps_Core C ⟨liftCs 1 K ++ X, d⟩ (liftA 1) := by
  refine MolMonoSteps_core_lift hx K Rem X hC (List.Perm.refl _) hRem hXd hsx fun hα hgood => ?_
  obtain ⟨i₀, rfl⟩ := (MolMonoSteps_isRight_iff x).1 hx
  exact MolMonoSteps_R_of_forall₂ _ (hpair hα hgood (MolMono_molRep_mem_int _ _)) extra X hX

/-- A term in which the replaced components have no present edge. -/
private theorem MolMonoSteps_core_noEdge {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    (K Rem : List (Comp (Atom k n))) (hC : C.comps.Perm (K ++ Rem))
    (hRem : ∀ c ∈ Rem, c.kind.joinsMol = false ∧ c.kind.mclass = none)
    (X : List (Comp (Atom k (n + 1)))) (hXd : ∀ d ∈ X, d.kind ≠ .dot)
    (hsx : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ X) (d : Coeff) :
    MolMonoSteps_Core C ⟨liftCs 1 K ++ X, d⟩ (liftA 1) := by
  refine MolMonoSteps_core_lift hx K Rem X hC (List.Perm.refl _) (fun c hc => (hRem c hc).1) hXd
    hsx fun _ _ => ?_
  rw [List.filterMap_eq_nil_iff.2 fun c hc => MolMonoSteps_edgeD_mclass C (hRem c hc).2]
  exact .nil _

/-- A term in which two solid edges at the indices `i₁ ≠ i₂` are replaced by solid edges of the
same kinds, with ends kept or moved from `x` to the new atom. -/
private theorem MolMonoSteps_core_two {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    {i₁ i₂ : ℕ} {c₁ c₂ : Comp (Atom k n)} (h₁ : C.comps[i₁]? = some c₁)
    (h₂ : C.comps[i₂]? = some c₂) (hne : i₁ ≠ i₂) {ch₁ ch₂ : Charge} (hk₁ : c₁.kind = .G ch₁)
    (hk₂ : c₂.kind = .G ch₂) (d₁ d₂ : Comp (Atom k (n + 1))) (hd₁ : d₁.kind = c₁.kind)
    (hd₂ : d₂.kind = c₂.kind)
    (e₁x : d₁.x = liftA 1 c₁.x ∨ (d₁.x = newA 0 ∧ c₁.x = x))
    (e₁y : d₁.y = liftA 1 c₁.y ∨ (d₁.y = newA 0 ∧ c₁.y = x))
    (e₂x : d₂.x = liftA 1 c₂.x ∨ (d₂.x = newA 0 ∧ c₂.x = x))
    (e₂y : d₂.y = liftA 1 c₂.y ∨ (d₂.y = newA 0 ∧ c₂.y = x)) (d : Coeff) :
    MolMonoSteps_Core C ⟨liftCs 1 (eraseIdxs [i₁, i₂] C.comps) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), d₁, d₂], d⟩ (liftA 1) := by
  refine MolMonoSteps_core_gen hx _ [c₁, c₂] (MolMonoSteps_perm_erase2 h₁ h₂ hne)
    (fun c hc => ?_) _ (fun e he => ?_) (by simp) d [[d₁], [d₂]]
    [mkC (.waved .s) (liftA 1 x) (newA 0)]
    (by simpa using (List.perm_append_singleton _ [d₁, d₂]).symm) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [hk₁]; rfl
    · rw [hk₂]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · simp [mkC]
    · rw [hd₁, hk₁]; simp
    · rw [hd₂, hk₂]; simp
  · intro _ hα hgood _
    exact .cons (MolMonoSteps_keepPair hx hα hgood c₁ d₁ hd₁ e₁x e₁y)
      (.cons (MolMonoSteps_keepPair hx hα hgood c₂ d₂ hd₂ e₂x e₂y) .nil)

/-- A term in which the solid edge at the index `i₁` is replaced by a solid edge of the same
kind, with ends kept or moved from `x` to the new atom, among other components without dotted
edges. -/
private theorem MolMonoSteps_core_one {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    {i₁ : ℕ} {c₁ : Comp (Atom k n)} (h₁ : C.comps[i₁]? = some c₁) {ch₁ : Charge}
    (hk₁ : c₁.kind = .G ch₁) (d₁ : Comp (Atom k (n + 1))) (hd₁ : d₁.kind = c₁.kind)
    (e₁x : d₁.x = liftA 1 c₁.x ∨ (d₁.x = newA 0 ∧ c₁.x = x))
    (e₁y : d₁.y = liftA 1 c₁.y ∨ (d₁.y = newA 0 ∧ c₁.y = x))
    (Y Z : List (Comp (Atom k (n + 1)))) (hY : Y.Perm (d₁ :: Z)) (hZ : ∀ z ∈ Z, z.kind ≠ .dot)
    (d : Coeff) :
    MolMonoSteps_Core C ⟨liftCs 1 (C.comps.eraseIdx i₁) ++
      (mkC (.waved .s) (liftA 1 x) (newA 0) :: Y), d⟩ (liftA 1) := by
  refine MolMonoSteps_core_gen hx _ [c₁] (MolMonoSteps_perm_eraseIdx h₁)
    (fun c hc => ?_) _ (fun e he => ?_) List.mem_cons_self d [[d₁]]
    (mkC (.waved .s) (liftA 1 x) (newA 0) :: Z) ?_ ?_
  · rw [List.mem_singleton.1 hc, hk₁]; rfl
  · rcases List.mem_cons.1 he with rfl | he
    · simp [mkC]
    · rcases List.mem_cons.1 (hY.mem_iff.1 he) with rfl | he
      · rw [hd₁, hk₁]; simp
      · exact hZ e he
  · simpa using ((hY.cons _).trans (List.Perm.swap _ _ _))
  · intro _ hα hgood _
    exact .cons (MolMonoSteps_keepPair hx hα hgood c₁ d₁ hd₁ e₁x e₁y) .nil

/-- **The derivative terms** ([I, (3.8)]): a term whose components are the lifted `A`, a term of
`dTerms p q` of the lifted `L` with `p`, `q` among `x` and the new atom, the waved edge `s_{xα}`,
a component `d₁` replacing `c₁` (or `c₁` without class), and components without dotted edges. -/
private theorem MolMonoSteps_core_dTerms {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    (A L : List (Comp (Atom k n))) (c₁ : Comp (Atom k n)) (hC : C.comps.Perm (A ++ L ++ [c₁]))
    (hj₁ : c₁.kind.joinsMol = false) {p q : Atom k (n + 1)} (hp : p = newA 0 ∨ p = liftA 1 x)
    (hq : q = newA 0 ∨ q = liftA 1 x) {dl : List (Comp (Atom k (n + 1)))}
    (hdl : dl ∈ dTerms p q (liftCs 1 L)) (d₁ : Comp (Atom k (n + 1))) (hd₁k : d₁.kind ≠ .dot)
    (Z : List (Comp (Atom k (n + 1)))) (hZ : ∀ z ∈ Z, z.kind ≠ .dot)
    (hc₁ : c₁.kind.mclass = none ∨ (d₁.kind = c₁.kind ∧
      (d₁.x = liftA 1 c₁.x ∨ (d₁.x = newA 0 ∧ c₁.x = x)) ∧
      (d₁.y = liftA 1 c₁.y ∨ (d₁.y = newA 0 ∧ c₁.y = x))))
    (d : Coeff) :
    MolMonoSteps_Core C ⟨liftCs 1 A ++ dl ++
      (mkC (.waved .s) (liftA 1 x) (newA 0) :: d₁ :: Z), d⟩ (liftA 1) := by
  obtain ⟨j, hj, ps, hps, rfl⟩ := MolMonoSteps_mem_dTerms hdl
  have hjL : j < L.length := by simpa [liftCs] using hj
  have hget : (liftCs 1 L)[j] = L[j].map (liftA 1) := by simp [liftCs]
  have herase : (liftCs 1 L).eraseIdx j = liftCs 1 (L.eraseIdx j) := by
    simp only [liftCs, List.eraseIdx_map]
  rw [hget] at hps
  obtain ⟨hpk, hpsd⟩ := MolMonoSteps_dPieces_kind hps
  have hL := MolMonoSteps_perm_eraseIdx (List.getElem?_eq_getElem hjL)
  have hT : liftCs 1 A ++ ((liftCs 1 L).eraseIdx j ++ ps) ++
      (mkC (.waved .s) (liftA 1 x) (newA 0) :: d₁ :: Z) =
      liftCs 1 (A ++ L.eraseIdx j) ++
        (ps ++ (mkC (.waved .s) (liftA 1 x) (newA 0) :: d₁ :: Z)) := by
    rw [herase]; simp [liftCs, List.append_assoc]
  rw [hT]
  refine MolMonoSteps_core_gen hx (A ++ L.eraseIdx j) [L[j], c₁] ?_ (fun c hc => ?_) _
    (fun e he => ?_) (by simp) d [ps, [d₁]] (mkC (.waved .s) (liftA 1 x) (newA 0) :: Z) ?_ ?_
  · refine hC.trans ?_
    have := (hL.append_left A).append_right [c₁]
    simpa [List.append_assoc] using this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hpk
    · exact hj₁
  · rcases List.mem_append.1 he with he | he
    · exact hpsd e he
    · rcases List.mem_cons.1 he with rfl | he
      · simp [mkC]
      · rcases List.mem_cons.1 he with rfl | he
        · exact hd₁k
        · exact hZ e he
  · simpa using (List.Perm.swap _ _ _).append_left ps
  · intro _ hα hgood hV
    obtain ⟨i₀, rfl⟩ := (MolMonoSteps_isRight_iff x).1 hx
    have hpq : ∀ r, (r = newA 0 ∨ r = liftA 1 (.inr i₀)) →
        Graph.molRep ⟨liftCs 1 (A ++ L.eraseIdx j) ++
          (ps ++ (mkC (.waved .s) (liftA 1 (.inr i₀)) (newA 0) :: d₁ :: Z)), d⟩
          (Graph.flatAtom ⟨liftCs 1 (A ++ L.eraseIdx j) ++
          (ps ++ (mkC (.waved .s) (liftA 1 (.inr i₀)) (newA 0) :: d₁ :: Z)), d⟩ r) =
        Graph.molRep ⟨liftCs 1 (A ++ L.eraseIdx j) ++
          (ps ++ (mkC (.waved .s) (liftA 1 (.inr i₀)) (newA 0) :: d₁ :: Z)), d⟩
          (liftA 1 (.inr i₀)) := by
      rintro r (rfl | rfl)
      · exact hα
      · rfl
    refine .cons (MolMonoSteps_dPieces_R _ hV (hpq p hp) (hpq q hq) hgood L[j] ps hps)
      (.cons ?_ .nil)
    rcases hc₁ with hm | ⟨hk, ex, ey⟩
    · exact MolMonoSteps_noEdge _ hm _
    · exact MolMonoSteps_keepPair hx hα hgood c₁ d₁ hk ex ey

/-- Components without waved or dotted edges appended to a term. -/
private theorem MolMonoSteps_core_ext {C : Graph k n} {cs : List (Comp (Atom k m))} {d : Coeff}
    {f : Atom k n → Atom k m} (h : MolMonoSteps_Core C ⟨cs, d⟩ f) (E : List (Comp (Atom k m)))
    (hE : ∀ e ∈ E, e.kind.joinsMol = false) (d' : Coeff) :
    MolMonoSteps_Core C ⟨cs ++ E, d'⟩ f :=
  MolMonoSteps_core_mapExtra h id (fun _ => ⟨rfl, rfl, rfl⟩) E hE (by simp)

/-- The labels `Q_u` put on a term. -/
private theorem MolMonoSteps_core_lq {C : Graph k n} {cs : List (Comp (Atom k m))} {d : Coeff}
    {f : Atom k n → Atom k m} (h : MolMonoSteps_Core C ⟨cs, d⟩ f) (u : Atom k m) (d' : Coeff) :
    MolMonoSteps_Core C ⟨labelQs u cs, d'⟩ f :=
  MolMonoSteps_core_mapExtra h (Comp.labelQ u) (MolMonoSteps_labelQ u) [] (by simp)
    (by simp [labelQs])

/-- The terms of [II, (4.23)] at the first light weight of positive charge on the internal atom
`x`. -/
private theorem MolMonoSteps_core_P2Pos {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    {E : TExpansion k n} (hE : oWeightP2Pos x C = some E) :
    ∀ t ∈ E, MolMonoSteps_Core C t.g t.f := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i hi
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  have hc₀ : C.comps[i]? = some C.comps[i] := List.getElem?_eq_getElem hlt
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hk0, -⟩ := hp
  have hsx : ∀ (A : List (Comp (Atom k (n + 1)))),
      mkC (.waved .s) (liftA 1 x) (newA 0) ∈ mkC (.waved .s) (liftA 1 x) (newA 0) :: A :=
    fun _ => List.mem_cons_self
  have hX : ∀ e ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA (n := n) 0)
      (newA 0)], e.kind ≠ .dot := by simp [mkC]
  cases hE
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at ht
  rcases ht with (rfl | rfl) | ⟨dl, hdl, rfl⟩
  · exact MolMonoSteps_core_noEdge hx _ [C.comps[i]] (MolMonoSteps_perm_eraseIdx hc₀)
      (fun c hc => by rw [List.mem_singleton.1 hc, hk0]; exact ⟨rfl, rfl⟩) _ hX (hsx _) _
  · exact MolMonoSteps_core_noEdge hx C.comps [] (by simp) (by simp) _ hX (hsx _) _
  · have := MolMonoSteps_core_dTerms hx [] (C.comps.eraseIdx i) C.comps[i]
      (by simpa using MolMonoSteps_perm_eraseIdx hc₀) (by rw [hk0]; rfl) (Or.inl rfl)
      (Or.inr rfl) hdl (mkC (.G .plus) (newA 0) (liftA 1 x)) (by simp [mkC]) [] (by simp)
      (Or.inl (by rw [hk0]; rfl)) (cm * C.coeff)
    simpa [liftCs] using this

private theorem MolMonoSteps_getD_of {α : Type} {l : List α} {j : ℕ} {c e : α}
    (h : l[j]? = some c) : l.getD j e = c := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

/-- The terms of the multi-edge expansion [I, (3.13)] at the internal atom `x`. -/
private theorem MolMonoSteps_core_multiEOut {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    {E : TExpansion k n} (hE : multiEOut x C = some E) :
    ∀ t ∈ E, MolMonoSteps_Core C t.g t.f := by
  unfold multiEOut at hE
  split at hE
  · cases hE
  rename_i i₁ is₂ hidx
  split at hE
  · cases hE
  rename_i e₁ he₁
  simp only [Option.ite_none_left_eq_some, Option.some.injEq] at hE
  obtain ⟨-, hE⟩ := hE
  obtain ⟨c, hc, hk₁, hx₁, -⟩ := MolMonoSteps_mem_edgeIdx (out := true)
    (by rw [hidx]; exact List.mem_cons_self)
  rw [he₁] at hc
  cases hc
  obtain ⟨hx₁, hy₁⟩ := hx₁ rfl
  set sx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0) with hsxd
  have hsx : ∀ A, sx ∈ sx :: A := fun _ => List.mem_cons_self
  -- The main terms with an edge of charge `minus` leaving `x`.
  have hM : ∀ j ∈ C.edgeIdx x .minus true, ∀ d,
      MolMonoSteps_Core C ⟨liftCs 1 (eraseIdxs [i₁, j] C.comps) ++
        [sx, mkC (.G .plus) (newA 0) (liftA 1 e₁.y),
          mkC (.G .minus) (newA 0) (liftA 1 ((C.comps.getD j e₁).y))], d⟩ (liftA 1) := by
    intro j hjm d
    obtain ⟨cj, hcj, hkj, hxj, -⟩ := MolMonoSteps_mem_edgeIdx hjm
    obtain ⟨hxj, -⟩ := hxj rfl
    rw [MolMonoSteps_getD_of hcj]
    have hne : i₁ ≠ j := by
      rintro rfl; rw [he₁] at hcj; cases hcj; rw [hk₁] at hkj; cases hkj
    exact MolMonoSteps_core_two hx he₁ hcj hne hk₁ hkj _ _ hk₁.symm hkj.symm
      (Or.inr ⟨rfl, hx₁⟩) (Or.inl rfl) (Or.inr ⟨rfl, hxj⟩) (Or.inl rfl) d
  -- The main terms with an edge of charge `plus` entering `x`.
  have hP : ∀ j ∈ C.edgeIdx x .plus false, ∀ d,
      MolMonoSteps_Core C ⟨liftCs 1 (eraseIdxs [i₁, j] C.comps) ++
        [sx, mkC (.G .plus) (newA 0) (liftA 1 e₁.y),
          mkC (.G .plus) (liftA 1 ((C.comps.getD j e₁).x)) (newA 0)], d⟩ (liftA 1) := by
    intro j hjm d
    obtain ⟨cj, hcj, hkj, -, hxj⟩ := MolMonoSteps_mem_edgeIdx hjm
    obtain ⟨hyj, hxj⟩ := hxj rfl
    rw [MolMonoSteps_getD_of hcj]
    have hne : i₁ ≠ j := by
      rintro rfl; rw [he₁] at hcj; cases hcj; exact hxj hx₁
    exact MolMonoSteps_core_two hx he₁ hcj hne hk₁ hkj _ _ hk₁.symm hkj.symm
      (Or.inr ⟨rfl, hx₁⟩) (Or.inl rfl) (Or.inl rfl) (Or.inr ⟨rfl, hyj⟩) d
  -- The term `m ∑_α s_{xα} (G_{αα} - m) 𝒢`.
  have hL : ∀ d, MolMonoSteps_Core C ⟨liftCs 1 C.comps ++
      [sx, mkC (.light .plus) (newA 0) (newA 0)], d⟩ (liftA 1) := fun d =>
    MolMonoSteps_core_noEdge hx C.comps [] (by simp) (by simp) _ (by simp [hsxd, mkC]) (hsx _) d
  -- The `(k₁ - 1)` and `k₄` terms.
  have hE1 : ∀ d, MolMonoSteps_Core C ⟨liftCs 1 (C.comps.eraseIdx i₁) ++
      [sx, mkC (.G .plus) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e₁.y)], d⟩
      (liftA 1) := fun d =>
    MolMonoSteps_core_one hx he₁ hk₁ _ hk₁.symm (Or.inr ⟨rfl, hx₁⟩) (Or.inl rfl) _ _
      (List.Perm.swap _ _ _) (by simp [mkC]) d
  have hE2 : ∀ d, MolMonoSteps_Core C ⟨liftCs 1 (C.comps.eraseIdx i₁) ++
      [sx, mkC (.G .minus) (newA 0) (liftA 1 x), mkC (.G .plus) (newA 0) (liftA 1 e₁.y)], d⟩
      (liftA 1) := fun d =>
    MolMonoSteps_core_one hx he₁ hk₁ _ hk₁.symm (Or.inr ⟨rfl, hx₁⟩) (Or.inl rfl) _ _
      (List.Perm.swap _ _ _) (by simp [mkC]) d
  -- The derivative terms.
  have hD : ∀ dl ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (C.edgeIdx x .plus true ++
      C.edgeIdx x .minus true ++ C.edgeIdx x .plus false ++ C.edgeIdx x .minus false) C.comps)),
      ∀ d, MolMonoSteps_Core C ⟨liftCs 1 (pickIdxs ((C.edgeIdx x .plus true ++
        C.edgeIdx x .minus true ++ C.edgeIdx x .plus false ++ C.edgeIdx x .minus false).filter
        (· != i₁)) C.comps) ++ dl ++ [sx, mkC (.G .plus) (newA 0) (liftA 1 e₁.y)], d⟩
        (liftA 1) := by
    intro dl hdl d
    refine MolMonoSteps_core_dTerms hx _ _ e₁ ?_ (by rw [hk₁]; rfl) (Or.inl rfl) (Or.inr rfl)
      hdl _ (by simp [mkC]) [] (by simp) (Or.inr ⟨hk₁.symm, Or.inr ⟨rfl, hx₁⟩, Or.inl rfl⟩) d
    set xI := C.edgeIdx x .plus true ++ C.edgeIdx x .minus true ++ C.edgeIdx x .plus false ++
      C.edgeIdx x .minus false with hxI
    have hi₁ : i₁ ∈ xI := by rw [hxI, hidx]; simp
    have e1 := MolMonoSteps_sel_one (fun j => j == i₁) C.comps he₁ (fun j _ => by simp)
    have hfc : ∀ j, (xI.filter (· != i₁)).contains j = (xI.contains j && j != i₁) := by
      intro j
      rw [Bool.eq_iff_iff, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem,
        List.mem_filter]
    have eA := MolMonoSteps_sel_append (fun j => (xI.filter (· != i₁)).contains j)
      (fun j => !(xI.contains j)) (fun j => j != i₁) C.comps (fun j _ => by
        rw [hfc]
        by_cases h1 : j = i₁
        · subst h1; rw [List.contains_iff_mem.2 hi₁]; simp
        · have : (j != i₁) = true := by simpa using h1
          rw [this]; cases xI.contains j <;> rfl)
      (fun j _ h => by
        obtain ⟨h1, h2⟩ := h
        rw [hfc, Bool.and_eq_true] at h1
        rw [h1.1] at h2
        cases h2)
    have eB := MolMonoSteps_sel_append (fun j => j != i₁) (fun j => j == i₁) (fun _ => true)
      C.comps (fun j _ => by cases h : j == i₁ <;> simp [bne, h])
      (fun j _ h => by cases h' : j == i₁ <;> simp_all [bne])
    rw [MolMonoSteps_sel_all _ _ fun _ _ => rfl] at eB
    refine eB.symm.trans ?_
    exact (eA.symm.append e1)
  subst hE
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_ite_nil_left, or_assoc] at ht
  rcases ht with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨d, ⟨dl, hdl, rfl⟩, rfl⟩ | rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨d, ⟨dl, hdl, rfl⟩, rfl⟩
  · exact hM j hj _
  · exact hP j hj _
  · exact MolMonoSteps_core_ext (hM j hj 0) _ (by simp [mkC, Kind.joinsMol]) _
  · exact MolMonoSteps_core_ext (hP j hj 0) _ (by simp [mkC, Kind.joinsMol]) _
  · exact hL _
  · exact hE1 _
  · exact hE2 _
  · simpa [List.append_assoc] using hD dl hdl (cm * C.coeff)
  · exact MolMonoSteps_core_relabel C _ (Comp.labelQ x) (MolMonoSteps_labelQ x) rfl
  · exact MolMonoSteps_core_lq (MolMonoSteps_core_ext (hM j hj 0) _
      (by simp [mkC, Kind.joinsMol]) 0) _ _
  · exact MolMonoSteps_core_lq (MolMonoSteps_core_ext (hP j hj 0) _
      (by simp [mkC, Kind.joinsMol]) 0) _ _
  · exact MolMonoSteps_core_lq (hL 0) _ _
  · exact MolMonoSteps_core_lq (hE1 0) _ _
  · exact MolMonoSteps_core_lq (hE2 0) _ _
  · exact MolMonoSteps_core_lq (by simpa [List.append_assoc] using hD dl hdl 0) _ _

/-- The terms of the multi-edge expansion [I, (3.14)] at the internal atom `x`. -/
private theorem MolMonoSteps_core_multiEIn {C : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    {E : TExpansion k n} (hE : multiEIn x C = some E) :
    ∀ t ∈ E, MolMonoSteps_Core C t.g t.f := by
  unfold multiEIn at hE
  split at hE
  · cases hE
  rename_i i₁ is₂ hidx
  split at hE
  · cases hE
  rename_i e₁ he₁
  simp only [Option.ite_none_left_eq_some, Option.some.injEq] at hE
  obtain ⟨-, hE⟩ := hE
  obtain ⟨c, hc, hk₁, -, hx₁⟩ := MolMonoSteps_mem_edgeIdx (out := false)
    (by rw [hidx]; exact List.mem_cons_self)
  rw [he₁] at hc
  cases hc
  obtain ⟨hy₁, -⟩ := hx₁ rfl
  set sx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0) with hsxd
  have hsx : ∀ A, sx ∈ sx :: A := fun _ => List.mem_cons_self
  -- The main terms with an edge of charge `minus` entering `x`.
  have hM : ∀ j ∈ C.edgeIdx x .minus false, ∀ d,
      MolMonoSteps_Core C ⟨liftCs 1 (eraseIdxs [i₁, j] C.comps) ++
        [sx, mkC (.G .plus) (liftA 1 e₁.x) (newA 0),
          mkC (.G .minus) (liftA 1 ((C.comps.getD j e₁).x)) (newA 0)], d⟩ (liftA 1) := by
    intro j hjm d
    obtain ⟨cj, hcj, hkj, -, hxj⟩ := MolMonoSteps_mem_edgeIdx hjm
    obtain ⟨hyj, -⟩ := hxj rfl
    rw [MolMonoSteps_getD_of hcj]
    have hne : i₁ ≠ j := by
      rintro rfl; rw [he₁] at hcj; cases hcj; rw [hk₁] at hkj; cases hkj
    exact MolMonoSteps_core_two hx he₁ hcj hne hk₁ hkj _ _ hk₁.symm hkj.symm
      (Or.inl rfl) (Or.inr ⟨rfl, hy₁⟩) (Or.inl rfl) (Or.inr ⟨rfl, hyj⟩) d
  -- The term `m ∑_α s_{xα} (G_{αα} - m) 𝒢`.
  have hL : ∀ d, MolMonoSteps_Core C ⟨liftCs 1 C.comps ++
      [sx, mkC (.light .plus) (newA 0) (newA 0)], d⟩ (liftA 1) := fun d =>
    MolMonoSteps_core_noEdge hx C.comps [] (by simp) (by simp) _ (by simp [hsxd, mkC]) (hsx _) d
  -- The `(k₃ - 1)` term.
  have hE1 : ∀ d, MolMonoSteps_Core C ⟨liftCs 1 (C.comps.eraseIdx i₁) ++
      [sx, mkC (.G .plus) (liftA 1 e₁.x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)], d⟩
      (liftA 1) := fun d =>
    MolMonoSteps_core_one hx he₁ hk₁ _ hk₁.symm (Or.inl rfl) (Or.inr ⟨rfl, hy₁⟩) _ _
      (List.Perm.refl _) (by simp [mkC]) d
  -- The derivative terms.
  have hD : ∀ dl ∈ dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (C.edgeIdx x .plus false ++
      C.edgeIdx x .minus false) C.comps)),
      ∀ d, MolMonoSteps_Core C ⟨liftCs 1 (pickIdxs ((C.edgeIdx x .plus false ++
        C.edgeIdx x .minus false).filter (· != i₁)) C.comps) ++ dl ++
        [sx, mkC (.G .plus) (liftA 1 e₁.x) (newA 0)], d⟩ (liftA 1) := by
    intro dl hdl d
    refine MolMonoSteps_core_dTerms hx _ _ e₁ ?_ (by rw [hk₁]; rfl) (Or.inr rfl) (Or.inl rfl)
      hdl _ (by simp [mkC]) [] (by simp) (Or.inr ⟨hk₁.symm, Or.inl rfl, Or.inr ⟨rfl, hy₁⟩⟩) d
    set xI := C.edgeIdx x .plus false ++ C.edgeIdx x .minus false with hxI
    have hi₁ : i₁ ∈ xI := by rw [hxI, hidx]; simp
    have e1 := MolMonoSteps_sel_one (fun j => j == i₁) C.comps he₁ (fun j _ => by simp)
    have hfc : ∀ j, (xI.filter (· != i₁)).contains j = (xI.contains j && j != i₁) := by
      intro j
      rw [Bool.eq_iff_iff, Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem,
        List.mem_filter]
    have eA := MolMonoSteps_sel_append (fun j => (xI.filter (· != i₁)).contains j)
      (fun j => !(xI.contains j)) (fun j => j != i₁) C.comps (fun j _ => by
        rw [hfc]
        by_cases h1 : j = i₁
        · subst h1; rw [List.contains_iff_mem.2 hi₁]; simp
        · have : (j != i₁) = true := by simpa using h1
          rw [this]; cases xI.contains j <;> rfl)
      (fun j _ h => by
        obtain ⟨h1, h2⟩ := h
        rw [hfc, Bool.and_eq_true] at h1
        rw [h1.1] at h2
        cases h2)
    have eB := MolMonoSteps_sel_append (fun j => j != i₁) (fun j => j == i₁) (fun _ => true)
      C.comps (fun j _ => by cases h : j == i₁ <;> simp [bne, h])
      (fun j _ h => by cases h' : j == i₁ <;> simp_all [bne])
    rw [MolMonoSteps_sel_all _ _ fun _ _ => rfl] at eB
    refine eB.symm.trans ?_
    exact (eA.symm.append e1)
  subst hE
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_ite_nil_left, or_assoc] at ht
  rcases ht with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ | ⟨d, ⟨dl, hdl, rfl⟩, rfl⟩ | rfl |
    ⟨j, hj, rfl⟩ | rfl | ⟨-, rfl⟩ | ⟨d, ⟨dl, hdl, rfl⟩, rfl⟩
  · exact hM j hj _
  · exact MolMonoSteps_core_ext (hM j hj 0) _ (by simp [mkC, Kind.joinsMol]) _
  · exact hL _
  · exact hE1 _
  · simpa [List.append_assoc] using hD dl hdl (cm * C.coeff)
  · exact MolMonoSteps_core_relabel C _ (Comp.labelQ x) (MolMonoSteps_labelQ x) rfl
  · exact MolMonoSteps_core_lq (MolMonoSteps_core_ext (hM j hj 0) _
      (by simp [mkC, Kind.joinsMol]) 0) _ _
  · exact MolMonoSteps_core_lq (hL 0) _ _
  · exact MolMonoSteps_core_lq (hE1 0) _ _
  · exact MolMonoSteps_core_lq (by simpa [List.append_assoc] using hD dl hdl 0) _ _

/-- The terms of `Ô^{(x)}_multi-e` ([I, Def 3.11]) at the internal atom `x`: the four cases, the
second and the fourth by complex conjugation. -/
private theorem MolMonoSteps_core_multiEHat {C : Graph k n} {x : Atom k n}
    (hx : x.isRight = true) {E : TExpansion k n} (hE : multiEHat x C = some E) :
    ∀ t ∈ E, MolMonoSteps_Core C t.g t.f := by
  unfold multiEHat at hE
  split_ifs at hE
  · exact MolMonoSteps_core_multiEOut hx hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact MolMonoSteps_core_conj (MolMonoSteps_core_multiEOut hx hE' t' ht')
  · exact MolMonoSteps_core_multiEIn hx hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact MolMonoSteps_core_conj (MolMonoSteps_core_multiEIn hx hE' t' ht')

/-- **[II, (4.23)] inside `P_x`** ([II, §4.4, Step 2]): every term of `Õ^{(x),2}_weight` is
`Graph.MolMono` with its atom map, for an internal atom `x`. The new atom is joined to `x` by a
waved edge, and the derivative terms replace an edge by a path through the molecule of `x`. -/
theorem molMono_oWeightP2T (x : Atom k n) (Γ : Graph k n) (hx : x.isRight = true)
    (t : Tracked k n) (ht : t ∈ oWeightP2T x Γ) : Γ.MolMono t.g t.f := by
  unfold oWeightP2T at ht
  split at ht
  · rename_i E hE
    exact MolMonoSteps_pLift (MolMonoSteps_core_P2Pos hx hE) t ht
  · split at ht
    · rename_i E hE
      refine MolMonoSteps_pLift (fun s hs => ?_) t ht
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      exact MolMonoSteps_core_conj (MolMonoSteps_core_P2Pos hx hE s' hs')
    · rw [List.mem_singleton.1 ht]; exact Graph.MolMono.refl Γ

/-- **[II, (4.24)] = [I, (3.13), (3.14)] inside `P_x`** ([II, §4.4, Step 3]): every term of the
multi-edge expansion `Ô^{(x)}_multi-e` of the graph inside `P_x` is `Graph.MolMono` with its atom
map, for an internal atom `x`. -/
theorem molMono_pMultiE (x : Atom k n) (Γ : Graph k n) (hx : x.isRight = true)
    (E : TExpansion k n) (hE : multiEHat x Γ.pCore = some E) (t : Tracked k n)
    (ht : t ∈ pLiftT x Γ E) : Γ.MolMono t.g t.f :=
  MolMonoSteps_pLift (MolMonoSteps_core_multiEHat hx hE) t ht

end PLift

section Assembly

end Assembly

/-! ## Decidability instances for concrete graphs -/

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

private instance MolMonoSteps_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

private instance MolMonoSteps_decIsPFormAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.IsPFormAt u) := by
  unfold Graph.IsPFormAt; infer_instance

end Instances

end RBM8D.Graphs
