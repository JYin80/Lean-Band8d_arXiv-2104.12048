module

public import RBM8D.Graph.QExp.PSteps
public import RBM8D.Graph.QExp.Step3

@[expose] public section

/-!
# The `Q`-expansions

[II, Lemma 4.15], from [II, Lemmas 4.11, 4.13, 4.14].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Graphs with changed labels -/

section Relabel

variable {k n : ℕ}

/-- The map `h` of components keeps the kind, the ends and the minor. -/
def KeepsShape (h : Comp (Atom k n) → Comp (Atom k n)) : Prop :=
  ∀ c, (h c).kind = c.kind ∧ (h c).x = c.x ∧ (h c).y = c.y ∧ (h c).minor = c.minor

theorem relab_exists {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (L : List (Comp (Atom k n))) (P : Kind → Atom k n → Atom k n → Prop) :
    (∃ c ∈ L.map h, P c.kind c.x c.y) ↔ ∃ c ∈ L, P c.kind c.x c.y := by
  constructor
  · rintro ⟨c, hc, hP⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2, h3, -⟩ := hs d
    exact ⟨d, hd, by rwa [h1, h2, h3] at hP⟩
  · rintro ⟨d, hd, hP⟩
    obtain ⟨h1, h2, h3, -⟩ := hs d
    exact ⟨h d, List.mem_map_of_mem hd, by rwa [h1, h2, h3]⟩

theorem relab_fromRel {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (L : List (Comp (Atom k n))) (P : Kind → Prop) :
    SimpleGraph.fromRel (fun u v => ∃ c ∈ L.map h, P c.kind ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel (fun u v => ∃ c ∈ L, P c.kind ∧ c.x = u ∧ c.y = v) := by
  ext u v
  simp only [SimpleGraph.fromRel_adj]
  rw [relab_exists hs L (fun κ a b => P κ ∧ a = u ∧ b = v),
    relab_exists hs L (fun κ a b => P κ ∧ a = v ∧ b = u)]

theorem relab_edgeGraph {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) : (⟨g.comps.map h, co⟩ : Graph k n).edgeGraph = g.edgeGraph := by
  have := relab_fromRel hs g.comps (fun _ => True)
  simp only [true_and] at this
  exact this

theorem relab_wavedThetaGraph {h : Comp (Atom k n) → Comp (Atom k n)}
    (hs : KeepsShape h) (g : Graph k n) (co : Coeff) :
    (⟨g.comps.map h, co⟩ : Graph k n).wavedThetaGraph = g.wavedThetaGraph :=
  relab_fromRel hs g.comps (fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true)

theorem relab_dotGraph {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) : (⟨g.comps.map h, co⟩ : Graph k n).dotGraph = g.dotGraph :=
  relab_fromRel hs g.comps (fun κ => κ = .dot)

theorem relab_molGraph {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) : (⟨g.comps.map h, co⟩ : Graph k n).molGraph = g.molGraph :=
  relab_fromRel hs g.comps (fun κ => κ.joinsMol = true)

theorem relab_sameBlock {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) :
    (⟨g.comps.map h, co⟩ : Graph k n).SameBlock = g.SameBlock := by
  funext u v
  simp only [Graph.SameBlock, relab_dotGraph hs]

theorem relab_sameMol {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) :
    (⟨g.comps.map h, co⟩ : Graph k n).SameMol = g.SameMol := by
  funext u v
  simp only [Graph.SameMol, relab_molGraph hs]

theorem relab_ord {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) : (⟨g.comps.map h, co⟩ : Graph k n).ord = g.ord := by
  have hk : ∀ c, (h c).kind = c.kind := fun c => (hs c).1
  simp [Graph.ord, List.map_map, Function.comp_def, hk]

theorem relab_dotExcess {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (g : Graph k n) (co : Coeff) :
    (⟨g.comps.map h, co⟩ : Graph k n).dotExcess = g.dotExcess := by
  have hk : ∀ c, (h c).kind = c.kind := fun c => (hs c).1
  have hn : (⟨g.comps.map h, co⟩ : Graph k n).nDots = g.nDots := by
    simp [Graph.nDots, List.filter_map, Function.comp_def, hk]
  simp only [Graph.dotExcess, hn, relab_dotGraph hs]

theorem relab_xdotApart {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    {g : Graph k n} (co : Coeff) (hX : g.XdotApart) :
    (⟨g.comps.map h, co⟩ : Graph k n).XdotApart := by
  intro c hc hk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2, h3, -⟩ := hs d
  rw [relab_sameBlock hs, h2, h3]
  exact hX d hd (h1 ▸ hk)

theorem relab_normal {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    {C : ℕ} {g : Graph k n} (co : Coeff) (hN : g.Normal C) :
    (⟨g.comps.map h, co⟩ : Graph k n).Normal C := by
  obtain ⟨⟨hsz, hcon, hint, hdot⟩, hsol, hxs⟩ := hN
  refine ⟨⟨by simpa using hsz, by rw [relab_edgeGraph hs]; exact hcon,
    by rw [relab_wavedThetaGraph hs]; exact hint, ?_⟩, ?_, ?_⟩
  · intro c hc hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2, h3, -⟩ := hs d
    rw [h2, h3]
    exact hdot d hd (h1 ▸ hk)
  · intro c hc hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2, h3, -⟩ := hs d
    rw [h2, h3]
    exact hsol d hd (h1 ▸ hk)
  · intro u v huv
    have e1 := relab_exists hs g.comps (fun κ a b => κ = .xdot ∧ (a = u ∧ b = v ∨ a = v ∧ b = u))
    have e2 := relab_exists hs g.comps
      (fun κ a b => κ.isSolid = true ∧ (a = u ∧ b = v ∨ a = v ∧ b = u))
    exact e1.trans ((hxs u v huv).trans e2.symm)

theorem relab_plain {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (hl : ∀ c, (h c).label.isSome = true → c.label.isSome = true) {g : Graph k n} (co : Coeff)
    (hP : g.Plain) : (⟨g.comps.map h, co⟩ : Graph k n).Plain := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2, h3, h4⟩ := hs d
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP d hd
  refine ⟨h4 ▸ p1, h1 ▸ p2, h1 ▸ p3, ?_, ?_, ?_⟩
  · rw [h1, h2, h3]; exact p4
  · rw [h1, h2, h3]; exact p5
  · rw [h1]; exact fun hs' => p6 (hl d hs')

theorem relab_qJoined {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    (hl : ∀ c, c.label = none → (h c).label = none) {g : Graph k n} (co : Coeff)
    {u v : Atom k n} (hJ : g.QJoined u v) : (⟨g.comps.map h, co⟩ : Graph k n).QJoined u v := by
  rcases hJ with hb | ⟨c, hc, hsol, hlab, hends⟩
  · left
    rw [relab_sameBlock hs]
    exact hb
  · right
    obtain ⟨h1, h2, h3, -⟩ := hs c
    exact ⟨h c, List.mem_map_of_mem hc, h1 ▸ hsol, hl c hlab, by rw [h2, h3]; exact hends⟩

theorem relab_dc {h : Comp (Atom k n) → Comp (Atom k n)} (hs : KeepsShape h)
    {g : Graph k n} (co : Coeff) (hdc : g.DoublyConnected) :
    (⟨g.comps.map h, co⟩ : Graph k n).DoublyConnected := by
  obtain ⟨black, blue, hdisj, hb, hu, hsb, hsu⟩ := hdc
  set g' : Graph k n := ⟨g.comps.map h, co⟩ with hg'
  have hlen : g.comps.length = g'.comps.length := by simp [hg']
  let e : Fin g.comps.length ≃ Fin g'.comps.length := finCongr hlen
  have hget : ∀ i : Fin g.comps.length, g'.comps[e i] = h g.comps[i] := by
    intro i
    simp [hg', e]
  have hnet : ∀ B : Finset (Fin g.comps.length), g'.net (B.map e.toEmbedding) = g.net B := by
    intro B
    ext a b
    simp only [Graph.net, SimpleGraph.fromRel_adj, Finset.mem_map, Equiv.coe_toEmbedding]
    have hm : g'.SameMol = g.SameMol := relab_sameMol hs g co
    rw [hm]
    have key : ∀ a b : Fin n, (∃ i, (∃ j ∈ B, e j = i) ∧ g'.comps[i].x = Sum.inr a ∧
        g'.comps[i].y = Sum.inr b) ↔ ∃ i ∈ B, g.comps[i].x = Sum.inr a ∧
          g.comps[i].y = Sum.inr b := by
      intro a b
      constructor
      · rintro ⟨i, ⟨j, hj, rfl⟩, hx, hy⟩
        rw [hget] at hx hy
        exact ⟨j, hj, (hs _).2.1 ▸ hx, (hs _).2.2.1 ▸ hy⟩
      · rintro ⟨j, hj, hx, hy⟩
        refine ⟨e j, ⟨j, hj, rfl⟩, ?_, ?_⟩
        · rw [hget, (hs _).2.1]; exact hx
        · rw [hget, (hs _).2.2.1]; exact hy
    rw [key a b, key b a]
  refine ⟨black.map e.toEmbedding, blue.map e.toEmbedding, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_map _ |>.2 hdisj
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    simp only [Equiv.coe_toEmbedding, hget, (hs _).1]
    exact hb j hj
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    simp only [Equiv.coe_toEmbedding, hget, (hs _).1]
    exact hu j hj
  · unfold Graph.Spans
    rw [hnet]
    exact hsb
  · unfold Graph.Spans
    rw [hnet]
    exact hsu

/-- Removing the label keeps the kind, the ends and the minor of a component. -/
theorem keepsShape_drop : KeepsShape (k := k) (n := n) fun c => { c with label := none } :=
  fun _ => ⟨rfl, rfl, rfl, rfl⟩

/-- The map of components replacing the label `Q_u` by `P_u`. -/
def qp (u : Atom k n) (c : Comp (Atom k n)) : Comp (Atom k n) :=
  if c.label = some (.Q, u) then { c with label := some (.P, u) } else c

theorem keepsShape_qp (u : Atom k n) : KeepsShape (qp u) := by
  intro c
  unfold qp
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem qp_label_isSome (u : Atom k n) (c : Comp (Atom k n)) :
    (qp u c).label.isSome = c.label.isSome := by
  unfold qp
  split
  · next h => rw [h]; rfl
  · rfl

theorem qp_label_none (u : Atom k n) (c : Comp (Atom k n)) (h : c.label = none) :
    (qp u c).label = none := by
  simp [qp, h]

/-- The second term of `oQPT u Γ`: `-Γ` with the label `Q_u` replaced by `P_u`. -/
def Graph.qpGraph (u : Atom k n) (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map (qp u), -Γ.coeff⟩

theorem oQPT_eq (u : Atom k n) (Γ : Graph k n) :
    oQPT u Γ = [Tracked.self Γ.dropLabels, Tracked.self (Γ.qpGraph u)] := rfl

theorem qpGraph_pForm {u : Atom k n} {Γ : Graph k n} (hQ : Γ.IsQFormAt u) :
    (Γ.qpGraph u).IsPFormAt u := by
  obtain ⟨⟨c, hc, hcl⟩, hl⟩ := hQ
  refine ⟨⟨qp u c, List.mem_map_of_mem hc, by simp [qp, hcl]⟩, ?_⟩
  intro d hd
  obtain ⟨d, hd', rfl⟩ := List.mem_map.1 hd
  rcases hl d hd' with h | h
  · left; exact qp_label_none u d h
  · right; simp [qp, h]

end Relabel

/-! ## The value of `Q_u = 1 - P_u` -/

section QPValue

variable {k n : ℕ}

theorem dedup_eq_singleton' {α : Type*} [DecidableEq α] (l : List α) (a : α)
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

/-- A graph whose labels are all `ℓ`, with at least one, has the single label `ℓ`. -/
theorem labels_eq_single' (L : List (Comp (Atom k n))) (co : Coeff)
    (ℓ : PQ × Atom k n) (hl : ∀ c ∈ L, c.label = none ∨ c.label = some ℓ)
    (hex : ∃ c ∈ L, c.label = some ℓ) : (⟨L, co⟩ : Graph k n).labels = [ℓ] := by
  unfold Graph.labels
  apply dedup_eq_singleton'
  · intro a ha
    obtain ⟨c, hc, hca⟩ := List.mem_filterMap.1 ha
    rcases hl c hc with h | h
    · rw [h] at hca; cases hca
    · rw [h] at hca; exact (Option.some.inj hca).symm
  · obtain ⟨c, hc, hcl⟩ := hex
    exact List.mem_filterMap.2 ⟨c, hc, hcl⟩

/-- The identity `Q_u = 1 - P_u` on a graph `Γ Q_u(𝒢)`: the values of the two terms of `oQPT u Γ`
add up to the value of `Γ`, for every conditional expectation family and data record. -/
theorem qp_value (Γ : Graph k n) (u : Atom k n) (hQ : Γ.IsQFormAt u)
    {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) :
    Γ.dropLabels.valR PF D e + (Γ.qpGraph u).valR PF D e = Γ.valR PF D e := by
  obtain ⟨cs, co⟩ := Γ
  obtain ⟨hex, hl⟩ := hQ
  have hlab1 : (⟨cs, co⟩ : Graph k n).labels = [(.Q, u)] := labels_eq_single' cs co _ hl hex
  have hlab2 : (Graph.dropLabels ⟨cs, co⟩).labels = [] := by
    unfold Graph.labels
    rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
    intro c hc
    simp only [Graph.dropLabels, List.mem_map] at hc
    obtain ⟨c₀, -, rfl⟩ := hc
    rfl
  have hlab3 : (Graph.qpGraph u ⟨cs, co⟩).labels = [(.P, u)] := by
    refine labels_eq_single' _ _ _ ?_ ?_
    · intro d hd
      obtain ⟨d, hd', rfl⟩ := List.mem_map.1 hd
      rcases hl d hd' with h | h
      · left; exact qp_label_none u d h
      · right; simp [qp, h]
    · obtain ⟨c, hc, hcl⟩ := hex
      exact ⟨qp u c, List.mem_map_of_mem hc, by simp [qp, hcl]⟩
  have hvq : ∀ (d : Data ι) (σ : Atom k n → ι) (c : Comp (Atom k n)),
      Comp.val d σ (qp u c) = Comp.val d σ c := by
    intro d σ c
    unfold qp
    split <;> rfl
  have hf1 : (cs.map (qp u)).filter (fun c => c.label.isNone) =
      (cs.filter fun c => c.label.isNone).map (qp u) := by
    rw [List.filter_map]
    congr 1
    refine List.filter_congr fun c _ => ?_
    simp only [Function.comp_apply]
    rw [← Option.not_isSome, ← Option.not_isSome, qp_label_isSome]
  have hf2 : (cs.map (qp u)).filter (fun c => decide (c.label = some (.P, u))) =
      (cs.filter fun c => decide (c.label = some (.Q, u))).map (qp u) := by
    rw [List.filter_map]
    congr 1
    refine List.filter_congr fun c hc => ?_
    simp only [Function.comp_apply]
    rcases hl c hc with h | h
    · rw [qp_label_none u c h, h]; simp
    · simp [qp, h]
  funext ω
  simp only [Graph.valR, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  set σ := Sum.elim e s
  set F : Ω → ℂ := fun ω' => ((cs.filter fun c => decide (c.label = some (PQ.Q, u))).map
    (Comp.val (D ω') σ)).prod with hFdef
  have hF' : (fun ω' => (((cs.map (qp u)).filter fun c => decide (c.label = some (PQ.P, u))).map
      (Comp.val (D ω') σ)).prod) = F := by
    funext ω'
    rw [hf2, List.map_map]
    simp only [hFdef]
    congr 1
    exact List.map_congr_left fun c _ => hvq _ _ c
  have hU : (((cs.map (qp u)).filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod =
      ((cs.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod := by
    rw [hf1, List.map_map]
    congr 1
    exact List.map_congr_left fun c _ => hvq _ _ c
  have hall : ((cs.map fun c => { c with label := none }).filter fun c => c.label.isNone) =
      cs.map fun c => { c with label := none } :=
    List.filter_eq_self.2 fun c hc => by
      obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 hc
      rfl
  have hval : ((cs.map fun c => { c with label := none }).map (Comp.val (D ω) σ)) =
      cs.map (Comp.val (D ω) σ) := by
    rw [List.map_map]
    rfl
  have hsplit : (cs.map (Comp.val (D ω) σ)).prod =
      ((cs.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod * F ω := by
    have hp := List.filter_append_perm (fun c : Comp (Atom k n) => c.label.isNone) cs
    have hc : cs.filter (fun c => !c.label.isNone) =
        cs.filter fun c => decide (c.label = some (PQ.Q, u)) := by
      refine List.filter_congr fun c hc => ?_
      rcases hl c hc with h | h <;> simp [h]
    rw [hc] at hp
    rw [← (hp.map (Comp.val (D ω) σ)).prod_eq, List.map_append, List.prod_append]
  have hneg : Coeff.eval (D ω).m (-co) = -Coeff.eval (D ω).m co := by
    simp [Coeff.eval]
  simp only [Graph.termR, hlab1, hlab2, hlab3, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, PFamily.op]
  simp only [Graph.dropLabels, Graph.qpGraph, hall, hval, hsplit, hF', hU, hneg] at *
  simp only [Pi.sub_apply]
  ring

end QPValue

/-! ## Tracked graphs and their composition -/

section Rel

variable {k : ℕ}

/-- The composition of tracked graphs: `s` is an output of `t.g`. -/
def Tracked.main_comp {n : ℕ} (t : Tracked k n) (s : Tracked k t.nOut) : Tracked k n :=
  ⟨s.nOut, s.g, s.f ∘ t.f⟩

theorem normal_mono {n C C' : ℕ} {g : Graph k n} (h : g.Normal C) (hC : C ≤ C') :
    g.Normal C' :=
  ⟨⟨h.1.size.trans hC, h.1.connected, h.1.internal, h.1.noIntDot⟩, h.2.1, h.2.2⟩

theorem plain_clean {n : ℕ} {g : Graph k n} (h : g.Plain) : g.Clean := fun c hc =>
  ⟨(h c hc).1, (h c hc).2.1, (h c hc).2.2.2.1, (h c hc).2.2.2.2⟩

theorem reachable_fromRel_iff' {V : Type*} (r : V → V → Prop) (u v : V) :
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

theorem subperm_map'' {α β : Type*} {l l' : List α} (h : l.Subperm l') (f : α → β) :
    (l.map f).Subperm (l'.map f) := by
  obtain ⟨l'', hp, hs⟩ := h
  exact ⟨l''.map f, hp.map f, hs.map f⟩

theorem subperm_filter_of_forall' {α : Type*} {l l' : List α} (h : l.Subperm l')
    (p : α → Bool) (hp : ∀ a ∈ l, p a = true) : l.Subperm (l'.filter p) := by
  have := h.filter p
  rwa [List.filter_eq_self.2 hp] at this

theorem carries_mem {n : ℕ} {g : Graph k n} {s : Tracked k n} (h : s.Carries g)
    {c : Comp (Atom k n)} (hc : c ∈ g.comps) (hl : c.label = none) (hd : c.kind ≠ .dot)
    (hx : c.kind ≠ .xdot) : c.map s.f ∈ s.g.comps :=
  h.1.subset (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, by simp [hl, hd, hx]⟩, rfl⟩)

theorem carries_trans {n : ℕ} {g : Graph k n} {t : Tracked k n}
    {s : Tracked k t.nOut} (h1 : t.Carries g) (h2 : s.Carries t.g) : (t.main_comp s).Carries g := by
  refine ⟨?_, fun u v huv => h2.2 _ _ (h1.2 u v huv)⟩
  have hA := subperm_filter_of_forall' h1.1
    (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)) (by
      intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      have := (List.mem_filter.1 hd).2
      simp only [decide_eq_true_eq] at this ⊢
      simp only [Comp.map]
      refine ⟨by rw [this.1]; rfl, this.2.1, this.2.2⟩)
  have hB := (subperm_map'' hA (Comp.map s.f)).trans h2.1
  simp only [List.map_map] at hB
  change ((g.comps.filter _).map (Comp.map (s.f ∘ t.f))).Subperm s.g.comps
  convert hB using 2
  funext c
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map, Function.comp_def]

theorem carries_waved {n : ℕ} {g : Graph k n} {s : Tracked k n}
    (h : s.Carries g) (hp : g.Plain) {u v : Atom k n} (huv : g.wavedGraph.Reachable u v) :
    s.g.wavedGraph.Reachable (s.f u) (s.f v) := by
  have hw : ∀ c ∈ g.comps, (∃ w, c.kind = .waved w) → c.label = none := by
    rintro c hc ⟨w, hw⟩
    by_contra hne
    have := (hp c hc).2.2.2.2.2 (Option.isSome_iff_ne_none.2 hne)
    rw [hw] at this
    simp [Kind.isRandom] at this
  unfold Graph.wavedGraph at huv ⊢
  rw [reachable_fromRel_iff'] at huv ⊢
  induction huv with
  | rel a b hab =>
    obtain ⟨c, hc, ⟨w, hw'⟩, rfl, rfl⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨c.map s.f, carries_mem h hc (hw c hc ⟨w, hw'⟩)
      (by rw [hw']; simp) (by rw [hw']; simp), ⟨w, hw'⟩, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

theorem carries_qJoined {n : ℕ} {g : Graph k n} {s : Tracked k n} (h : s.Carries g)
    {u v : Atom k n} (hJ : g.QJoined u v) : s.g.QJoined (s.f u) (s.f v) := by
  rcases hJ with hb | ⟨c, hc, hsol, hlab, hends⟩
  · exact Or.inl (h.2 u v hb)
  · right
    have hd : c.kind ≠ .dot := fun h' => by rw [h'] at hsol; simp [Kind.isSolid] at hsol
    have hx : c.kind ≠ .xdot := fun h' => by rw [h'] at hsol; simp [Kind.isSolid] at hsol
    refine ⟨c.map s.f, carries_mem h hc hlab hd hx, hsol, by simp [Comp.map, hlab], ?_⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; simp [Comp.map, h1, h2]
    · right; simp [Comp.map, h1, h2]

theorem carries_self {n : ℕ} (g : Graph k n) : (Tracked.self g).Carries g := by
  refine ⟨?_, fun u v h => h⟩
  have : (g.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).map
      (Comp.map (Tracked.self g).f) = g.comps.filter fun c => decide (c.label = none ∧
        c.kind ≠ .dot ∧ c.kind ≠ .xdot) := by
    simp only [Tracked.self]
    conv_rhs => rw [← List.map_id (g.comps.filter _)]
    refine List.map_congr_left fun c _ => ?_
    cases c; simp [Comp.map]
  rw [this]
  exact List.filter_sublist.subperm

/-- The clauses kept from an input graph `g` at `x` to an output `t` of [II, §4.4, Steps 2, 3]:
`Tracked.QBase`, `Tracked.Carries`, and new atoms joined to the image of `x` by waved edges. -/
def Rel {n : ℕ} (C' : ℕ) (x : Atom k n) (g : Graph k n) (t : Tracked k n) : Prop :=
  t.QBase C' x g ∧ t.Carries g ∧ ∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f x) u

theorem Rel.mono {n C C' : ℕ} {x : Atom k n} {g : Graph k n} {t : Tracked k n}
    (h : Rel C x g t) (hC : C ≤ C') : Rel C' x g t :=
  ⟨⟨normal_mono h.1.1 hC, h.1.2⟩, h.2⟩

theorem Rel.trans {n C₁ C₂ : ℕ} {x : Atom k n} {g : Graph k n} {t : Tracked k n}
    {s : Tracked k t.nOut} (h1 : Rel C₁ x g t) (hp : t.g.Plain) (h2 : Rel C₂ (t.f x) t.g s) :
    Rel C₂ x g (t.main_comp s) := by
  obtain ⟨⟨-, ho1, -, he1, -, hd1, hc1⟩, hca1, hw1⟩ := h1
  obtain ⟨⟨hN2, ho2, hx2, he2, hr2, hd2, hc2⟩, hca2, hw2⟩ := h2
  refine ⟨⟨hN2, ho1.trans ho2, hx2, he2.trans he1, hr2, fun h => hd2 (hd1 h), hc1.trans hc2⟩,
    carries_trans hca1 hca2, ?_⟩
  intro u hu
  by_cases hs : s.IsNew u
  · exact hw2 u hs
  · unfold Tracked.IsNew at hs
    push Not at hs
    obtain ⟨w, rfl⟩ := hs
    have hw : t.IsNew w := fun v hv => hu v (by simp [Tracked.main_comp, hv])
    exact carries_waved hca2 hp (hw1 w hw)

theorem Rel.self {n C : ℕ} {x : Atom k n} {g : Graph k n} (hN : g.Normal C)
    (hx : x.isRight = true) (hX : g.XdotApart) : Rel C x g (Tracked.self g) :=
  ⟨⟨hN, le_rfl, hX, le_rfl, hx, id, Relation.ReflTransGen.refl⟩, carries_self g,
    fun u hu => absurd rfl (hu u)⟩

end Rel

/-! ## Sums of expansions -/

section Sums

variable {k : ℕ}

theorem valR_cons' {n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (t : Tracked k n) (E : TExpansion k n) :
    (TExpansion.forget (t :: E)).valR PF D e =
      t.g.valR PF D e + (TExpansion.forget E).valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR]

theorem valueEq_self {n : ℕ} (g : Graph k n) :
    TExpansion.ValueEq [Tracked.self g] g modelAdm := by
  intro Ω ι _ _ PF D _ e
  funext ω
  simp [TExpansion.forget, Expansion.valR, Tracked.self]

end Sums

/-! ## The iteration of [II, §4.4, Steps 2, 3] -/

section Iter

variable {k : ℕ}

theorem exists_inr_of_isRight {n : ℕ} {u : Atom k n} (h : u.isRight = true) :
    ∃ y, u = .inr y := by
  rcases u with u | u
  · simp at h
  · exact ⟨u, rfl⟩

end Iter

section Instances

end Instances

/-! ## The components at an external atom -/

section OAt

variable {k : ℕ}

/-- The component has an end at the external atom `o`. -/
def main_atO {n : ℕ} (o : Fin k) (c : Comp (Atom k n)) : Bool :=
  decide (c.x = .inl o ∨ c.y = .inl o)

/-- Every component of `Γ` at the external atom `o` is a diffusive edge. -/
def MainODiff {n : ℕ} (o : Fin k) (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl o ∨ c.y = .inl o) → c.kind.isDiffusive = true

/-- The components of `T` at the external atom `o` are, up to order, those of `Γ`. -/
def MainOKeep {n : ℕ} (o : Fin k) (Γ T : Graph k n) : Prop :=
  (T.comps.filter (main_atO o)).Perm (Γ.comps.filter (main_atO o))

/-- The components of the output graph `t` at the external atom `o` are, up to order, the images
of those of `Γ`. -/
def MainOOut {n : ℕ} (o : Fin k) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  (t.g.comps.filter (main_atO o)).Perm ((Γ.comps.filter (main_atO o)).map (Comp.map t.f))

/-- At every external atom at which all components of `Γ` are diffusive, the components of `T`
are, up to order, those of `Γ`. -/
def MainOK1 {n : ℕ} (Γ T : Graph k n) : Prop := ∀ o, MainODiff o Γ → MainOKeep o Γ T

/-- At every external atom at which all components of `Γ` are diffusive, the components of the
output graph `t` are, up to order, the images of those of `Γ`. -/
def MainOO1 {n : ℕ} (Γ : Graph k n) (t : Tracked k n) : Prop := ∀ o, MainODiff o Γ → MainOOut o Γ t

theorem atO_iff {n : ℕ} {o : Fin k} {c : Comp (Atom k n)} :
    main_atO o c = true ↔ (c.x = .inl o ∨ c.y = .inl o) := by
  simp [main_atO]

theorem MainODiff.of_keep {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : MainOKeep o Γ T)
    (hO : MainODiff o Γ) : MainODiff o T := by
  intro c hc ho
  have hc' := (List.mem_filter.1 (h.subset (List.mem_filter.2 ⟨hc, atO_iff.2 ho⟩))).1
  exact hO c hc' ho

theorem Comp.map_id'' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

theorem Comp.map_comp'' {U V W : Type*} (f : U → V) (g : V → W) (c : Comp U) :
    (c.map f).map g = c.map (g ∘ f) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map, Function.comp_def]

theorem MainOO1.self {n : ℕ} (Γ : Graph k n) : MainOO1 Γ (Tracked.self Γ) := by
  intro o _
  change (Γ.comps.filter (main_atO o)).Perm ((Γ.comps.filter (main_atO o)).map (Comp.map id))
  rw [show (Γ.comps.filter (main_atO o)).map (Comp.map id) = Γ.comps.filter (main_atO o) by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (main_atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c]

/-- The graph `T` itself as an output keeps the components at the external atoms. -/
theorem MainOO1.of_keep {n : ℕ} {Γ T : Graph k n} (h : MainOK1 Γ T) :
    MainOO1 Γ (Tracked.self T) := by
  intro o hO
  have hid : (Γ.comps.filter (main_atO o)).map (Comp.map (Tracked.self T).f) =
      Γ.comps.filter (main_atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (main_atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c
  change (T.comps.filter (main_atO o)).Perm _
  rw [hid]
  exact h o hO

theorem MainOO1.of_ok {n : ℕ} {Γ T : Graph k n} {t : Tracked k n} (h1 : MainOK1 Γ T)
    (h2 : MainOO1 T t) : MainOO1 Γ t := by
  intro o hO
  have h1o := h1 o hO
  exact (h2 o (MainODiff.of_keep h1o hO)).trans (List.Perm.map _ h1o)

theorem MainODiff.of_oout {n : ℕ} {o : Fin k} {Γ : Graph k n} {t : Tracked k n}
    (h : MainOOut o Γ t) (hO : MainODiff o Γ) : MainODiff o t.g := by
  intro c hc ho
  have hc' : c ∈ (Γ.comps.filter (main_atO o)).map (Comp.map t.f) :=
    h.subset (List.mem_filter.2 ⟨hc, atO_iff.2 ho⟩)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨hdΓ, hdo⟩ := List.mem_filter.1 hd
  exact hO d hdΓ (atO_iff.1 hdo)

theorem MainOO1.comp {n : ℕ} {Γ : Graph k n} {t : Tracked k n} {s : Tracked k t.nOut}
    (h1 : MainOO1 Γ t) (h2 : MainOO1 t.g s) : MainOO1 Γ (t.main_comp s) := by
  intro o hO
  have h1o := h1 o hO
  have h2o := h2 o (MainODiff.of_oout h1o hO)
  change (s.g.comps.filter (main_atO o)).Perm ((Γ.comps.filter (main_atO o)).map (Comp.map (s.f ∘ t.f)))
  refine h2o.trans ((List.Perm.map _ h1o).trans ?_)
  rw [List.map_map]
  exact List.Perm.of_eq (List.map_congr_left fun c _ => Comp.map_comp'' t.f s.f c)

/-- A map of components that keeps the ends and fixes the components without label keeps the
components at the external atoms of a plain graph. -/
theorem MainOK1.relab {n : ℕ} {g : Graph k n} (hp : g.Plain)
    (φ : Comp (Atom k n) → Comp (Atom k n)) (hφe : ∀ c, (φ c).x = c.x ∧ (φ c).y = c.y)
    (hφl : ∀ c, c.label = none → φ c = c) (co : Coeff) : MainOK1 g ⟨g.comps.map φ, co⟩ := by
  intro o hO
  change ((g.comps.map φ).filter (main_atO o)).Perm (g.comps.filter (main_atO o))
  rw [List.filter_map]
  have e1 : g.comps.filter (main_atO o ∘ φ) = g.comps.filter (main_atO o) :=
    List.filter_congr fun c _ => by simp only [Function.comp_apply, main_atO, (hφe c).1, (hφe c).2]
  have e2 : (g.comps.filter (main_atO o)).map φ = g.comps.filter (main_atO o) := by
    conv_rhs => rw [← List.map_id (g.comps.filter (main_atO o))]
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨hcg, ho⟩ := List.mem_filter.1 hc
    have hd := hO c hcg (atO_iff.1 ho)
    refine hφl c ?_
    by_contra hne
    have hr := (hp c hcg).2.2.2.2.2 (Option.isSome_iff_ne_none.2 hne)
    cases hk : c.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
  rw [e1, e2]

theorem MainOK1.dropLabels {n : ℕ} {g : Graph k n} (hp : g.Plain) : MainOK1 g g.dropLabels :=
  MainOK1.relab hp (fun c => { c with label := none }) (fun _ => ⟨rfl, rfl⟩)
    (fun c hc => by cases c; simp_all) g.coeff

theorem MainOK1.qpGraph {n : ℕ} {g : Graph k n} (hp : g.Plain) (u : Atom k n) :
    MainOK1 g (g.qpGraph u) :=
  MainOK1.relab hp (qp u) (fun c => ⟨(keepsShape_qp u c).2.1, (keepsShape_qp u c).2.2.1⟩)
    (fun c hc => by simp [qp, hc]) (-g.coeff)

end OAt

section IterO

variable {k : ℕ}

end IterO

section InstancesO

set_option maxRecDepth 100000

end InstancesO

end RBM8D.Graphs
