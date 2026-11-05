import RBM8D.Graph.MolCarry
import RBM8D.Graph.MolRead
import RBM8D.Graph.IsolatedNest

/-!
# Inserting a molecular graph at three molecules, and merging molecules

The molecular graph of picture (6.5) of [II, Lemma 6.5 (2)]: a molecular multigraph `L` inserted
into a molecular multigraph `K`, the external vertices `⊗`, `⊕`, `⊖` of `L` sent to the internal
vertices `u₀`, `u₁`, `u₂` of `K`, and the edges `b` (blue solid, or absent when `u₀ = u₁`) and
`r` (red solid or absent) of `K` removed. Under the hypotheses of [II, Lemma 6.5 (2)] on `K` and
`L`, the result is sequentially pre-deterministic ([II, Def 5.9]); its proper isolated subsets are
those of the chain (6.6) of [II, Lemma 6.5 (2)]: the proper isolated subsets of `K` together with
the internal vertices of `L`, the internal vertices of `L`, and the proper isolated subsets of
`L`; all of them except the internal vertices of `L` are weakly isolated ([II, Def 6.1]) when `K`
and `L` are globally standard ([II, Def 6.2]).

The molecular multigraph with its vertices identified by an idempotent map of the internal
vertices (a composition of operations (A) of [II, §5.4]) and its loops removed is sequentially
pre-deterministic, and globally standard when the proper isolated subsets saturated for the map
are weakly isolated; the edges present in the graph are assumed to join vertices.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

variable {V W E F : Type}

/-! ## The insertion and the removal of loops -/

/-- The molecular multigraph `L` inserted into `K` ([II, Lemma 6.5 (2)], picture (6.5)): the
internal vertices are those of `K` (left) and of `L` (right), the external vertices are those of
`K`. An edge of `K` keeps its ends and class, and is absent if it lies in `B`; an edge of `L`
keeps its class, and each of its ends is kept if it is an internal vertex of `L` and is replaced
by its image under `σ` (left) otherwise. -/
def MGraph.insert [DecidableEq V] [DecidableEq W] [DecidableEq E] (K : MGraph V E)
    (L : MGraph W F) (σ : W → V) (B : Finset E) : MGraph (V ⊕ W) (E ⊕ F) where
  int := K.int.disjSum L.int
  ext := K.ext.map Function.Embedding.inl
  ends
    | .inl e => (.inl (K.ends e).1, .inl (K.ends e).2)
    | .inr f =>
      (if (L.ends f).1 ∈ L.int then .inr (L.ends f).1 else .inl (σ (L.ends f).1),
        if (L.ends f).2 ∈ L.int then .inr (L.ends f).2 else .inl (σ (L.ends f).2))
  cls
    | .inl e => if e ∈ B then none else K.cls e
    | .inr f => L.cls f

/-- The molecular multigraph with all its loops removed: an edge whose two ends coincide becomes
absent. -/
def MGraph.unloop [DecidableEq V] (G : MGraph V E) : MGraph V E :=
  { G with cls := fun e => if (G.ends e).1 = (G.ends e).2 then none else G.cls e }

/-! ## Present edges between internal vertices, and graphs related by a map -/

section Rel

variable {V' E' : Type}

/-- Two molecular multigraphs are equal when their four components are. -/
private theorem MolInsert_ext {G H : MGraph V E} (h1 : G.int = H.int) (h2 : G.ext = H.ext)
    (h3 : G.ends = H.ends) (h4 : G.cls = H.cls) : G = H := by
  cases G; cases H; simp_all

/-- The edge `e` is present, not a red solid edge, and joins two internal vertices. -/
private def Live (G : MGraph V E) (e : E) : Prop :=
  G.cls e ≠ none ∧ G.cls e ≠ some .minus ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int

/-- The graph `G'` is the image of `G` under the map `f` of the vertices and the injective map `g`
of the edges, as far as the present edges other than red solid edges between internal vertices
are concerned; `G'` may have in addition diffusive loops. -/
private structure Rel (G : MGraph V E) (G' : MGraph V' E') (f : V → V') (g : E → E') : Prop where
  mem : ∀ v', v' ∈ G'.int ↔ ∃ v ∈ G.int, f v = v'
  inj : Function.Injective g
  cls : ∀ e, Live G e → G'.cls (g e) = G.cls e
  ends : ∀ e, Live G e → G'.ends (g e) = (f (G.ends e).1, f (G.ends e).2) ∨
    G'.ends (g e) = (f (G.ends e).2, f (G.ends e).1)
  surj : ∀ e', Live G' e' → (∃ e, Live G e ∧ g e = e') ∨
    ((G'.ends e').1 = (G'.ends e').2 ∧ G'.cls e' = some .diff)

variable {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'}

private theorem Rel.mem_of (h : Rel G G' f g) {v : V} (hv : v ∈ G.int) : f v ∈ G'.int :=
  (h.mem _).2 ⟨v, hv, rfl⟩

private theorem Rel.ends_int (h : Rel G G' f g) {e : E} (he : Live G e) :
    (G'.ends (g e)).1 ∈ G'.int ∧ (G'.ends (g e)).2 ∈ G'.int := by
  rcases h.ends e he with h' | h' <;> rw [h'] <;>
    exact ⟨h.mem_of (by first | exact he.2.2.1 | exact he.2.2.2),
      h.mem_of (by first | exact he.2.2.2 | exact he.2.2.1)⟩

/-- A spanning set of edges of `G` is carried to a spanning set of edges of `G'`. -/
private theorem Rel.spans (h : Rel G G' f g) {B : Finset E}
    (hB : ∀ e ∈ B, G.cls e ≠ some .minus) (hsp : G.Spans B) :
    open Classical in G'.Spans ((B.filter (Live G)).image g) := by
  classical
  intro S' hS' hne hn
  set S : Finset V := G.int.filter fun v => f v ∈ S' with hSdef
  have hmemS : ∀ v ∈ G.int, (v ∈ S ↔ f v ∈ S') := fun v hv => by simp [hSdef, hv]
  obtain ⟨s', hs'⟩ := hne
  obtain ⟨s, hs, rfl⟩ := (h.mem _).1 (hS' hs')
  obtain ⟨t', ht', ht'S⟩ := Finset.not_subset.1 hn
  obtain ⟨t, ht, rfl⟩ := (h.mem _).1 ht'
  obtain ⟨e, heB, hc, h1, h2, hcut⟩ := hsp S (Finset.filter_subset _ _) ⟨s, (hmemS s hs).2 hs'⟩
    (fun hsub => ht'S ((hmemS t ht).1 (hsub ht)))
  have hl : Live G e := ⟨hc, hB e heB, h1, h2⟩
  refine ⟨g e, Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨heB, hl⟩, rfl⟩, ?_,
    (h.ends_int hl).1, (h.ends_int hl).2, ?_⟩
  · rw [h.cls e hl]; exact hc
  · have e1 := hmemS _ h1
    have e2 := hmemS _ h2
    unfold MGraph.Cut at hcut ⊢
    rcases h.ends e hl with h' | h' <;> rw [h'] <;> simp only at * <;> tauto

/-- The doubly connected property is carried from `G` to `G'`. -/
private theorem Rel.dc (h : Rel G G' f g) (hG : G.DC) : G'.DC := by
  classical
  obtain ⟨bk, bl, hd, hbk, hbl, hsk, hsl⟩ := hG
  refine ⟨(bk.filter (Live G)).image g, (bl.filter (Live G)).image g, ?_, ?_, ?_,
    h.spans (fun e he => by rw [hbk e he]; simp) hsk,
    h.spans (fun e he => by rcases hbl e he with h' | h' | h' <;> rw [h'] <;> simp) hsl⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨c, hc, hca⟩ := Finset.mem_image.1 hx'
    rw [h.inj hca] at hc
    exact Finset.disjoint_left.1 hd (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hc).1
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_filter] at ha
    rw [h.cls a ha.2]
    exact hbk a ha.1
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_filter] at ha
    rw [h.cls a ha.2]
    exact hbl a ha.1

private theorem live_convert [DecidableEq E] {l : List E} {e : E} :
    Live (G.convert l) e ↔ Live G e := by
  unfold Live MGraph.convert
  simp only
  split_ifs with hc
  · rw [hc.2]; simp
  · exact Iff.rfl

private theorem live_erase [DecidableEq E] {e₀ e : E} :
    Live (G.erase e₀) e ↔ e ≠ e₀ ∧ Live G e := by
  unfold Live MGraph.erase
  by_cases he : e = e₀
  · subst he; simp
  · simp [he]

/-- The relation is kept when the blue solid edges of a list are changed into `Θ` edges. -/
private theorem Rel.convert [DecidableEq E] [DecidableEq E'] (h : Rel G G' f g) (l : List E) :
    Rel (G.convert l) (G'.convert (l.map g)) f g := by
  refine ⟨h.mem, h.inj, fun e he => ?_, fun e he => h.ends e (live_convert.1 he), fun e' he' => ?_⟩
  · have he0 := live_convert.1 he
    change (if g e ∈ l.map g ∧ G'.cls (g e) = some .plus then some MClass.diff else G'.cls (g e)) =
      (if e ∈ l ∧ G.cls e = some .plus then some MClass.diff else G.cls e)
    rw [h.cls e he0]
    simp only [List.mem_map_of_injective h.inj]
  · rcases h.surj e' (live_convert.1 he') with ⟨e, he, rfl⟩ | ⟨hl, hc⟩
    · exact Or.inl ⟨e, live_convert.2 he, rfl⟩
    · refine Or.inr ⟨hl, ?_⟩
      change (if e' ∈ l.map g ∧ G'.cls e' = some .plus then some MClass.diff else G'.cls e') = _
      rw [hc]; simp

/-- The relation is kept when an edge and its image are removed. -/
private theorem Rel.erase [DecidableEq E] [DecidableEq E'] (h : Rel G G' f g) (e₀ : E) :
    Rel (G.erase e₀) (G'.erase (g e₀)) f g := by
  refine ⟨h.mem, h.inj, fun e he => ?_, fun e he => h.ends e (live_erase.1 he).2,
    fun e' he' => ?_⟩
  · obtain ⟨hne, hl⟩ := live_erase.1 he
    change Function.update G'.cls (g e₀) none (g e) = Function.update G.cls e₀ none e
    rw [Function.update_of_ne hne, Function.update_of_ne (fun h' => hne (h.inj h')), h.cls e hl]
  · obtain ⟨hne, hl⟩ := live_erase.1 he'
    rcases h.surj e' hl with ⟨e, he, rfl⟩ | ⟨hl', hc⟩
    · exact Or.inl ⟨e, live_erase.2 ⟨fun h' => hne (h' ▸ rfl), he⟩, rfl⟩
    · refine Or.inr ⟨hl', ?_⟩
      change Function.update G'.cls (g e₀) none e' = _
      rw [Function.update_of_ne hne, hc]

/-- Internal blue solid edges of `G'` are the images of those of `G`. -/
private theorem Rel.intPlus (h : Rel G G' f g) (e' : E') :
    G'.IsIntPlus e' ↔ ∃ e, G.IsIntPlus e ∧ g e = e' := by
  constructor
  · intro hp
    have hl : Live G' e' := ⟨by rw [hp.1]; simp, by rw [hp.1]; simp, hp.2.1, hp.2.2⟩
    rcases h.surj e' hl with ⟨e, he, rfl⟩ | ⟨-, hc⟩
    · exact ⟨e, ⟨by rw [← h.cls e he, hp.1], he.2.2.1, he.2.2.2⟩, rfl⟩
    · rw [hp.1] at hc; exact absurd hc (by simp)
  · rintro ⟨e, hp, rfl⟩
    have hl : Live G e := ⟨by rw [hp.1]; simp, by rw [hp.1]; simp, hp.2.1, hp.2.2⟩
    exact ⟨by rw [h.cls e hl, hp.1], (h.ends_int hl).1, (h.ends_int hl).2⟩

/-- The pre-deterministic property is carried from `G` to `G'`. -/
private theorem Rel.preDet [DecidableEq E] [DecidableEq E'] (h : Rel G G' f g) (hG : G.PreDet) :
    G'.PreDet := by
  obtain ⟨hdc, l, hnd, hmem, hred⟩ := hG
  refine ⟨h.dc hdc, l.map g, hnd.map h.inj, fun e' => ?_, fun j hj => ?_⟩
  · rw [h.intPlus, List.mem_map]
    exact ⟨fun ⟨e, he, hge⟩ => ⟨e, (hmem e).1 he, hge⟩, fun ⟨e, he, hge⟩ => ⟨e, (hmem e).2 he, hge⟩⟩
  · have hj' : j < l.length := by simpa using hj
    obtain ⟨hp, hd1, hd2⟩ := hred j hj'
    have hr := h.convert (l.take j)
    rw [List.map_take] at hr
    simp only [List.getElem_map]
    have hip : (G.convert (l.take j)).IsIntPlus l[j] :=
      ⟨hp, ((hmem _).1 (List.getElem_mem hj')).2.1, ((hmem _).1 (List.getElem_mem hj')).2.2⟩
    have hl : Live (G.convert (l.take j)) l[j] :=
      ⟨by rw [hip.1]; simp, by rw [hip.1]; simp, hip.2.1, hip.2.2⟩
    exact ⟨by rw [hr.cls _ hl, hp], hr.dc hd1, (hr.erase l[j]).dc hd2⟩

end Rel

/-! ## Nets -/

private theorem convert_nil [DecidableEq E] (G : MGraph V E) : G.convert [] = G :=
  MolInsert_ext rfl rfl rfl (funext fun e => by simp [MGraph.convert])

/-- Spanning nets of `G` outside `Ω`, together with spanning nets of the subgraph induced on `Ω`
without `b`, span `G` without `b` ([II, Lemma 6.5 (2)], the nets inside the minimal isolated
subset). -/
private theorem spans_erase_induce [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    {Ω : Finset V} (hΩ : Ω ⊆ G.int) {b : E} (hb : (G.ends b).1 ∈ Ω ∧ (G.ends b).2 ∈ Ω)
    {N M : Finset E} (hN : G.Spans N) (hM : ((G.induce Ω).erase b).Spans M) :
    (G.erase b).Spans (N.filter (fun e => ¬ ((G.ends e).1 ∈ Ω ∧ (G.ends e).2 ∈ Ω)) ∪ M) := by
  intro S hS hne hn
  by_cases hc : (S ∩ Ω).Nonempty ∧ ¬ Ω ⊆ S
  · obtain ⟨e, he, hce, h1, h2, hcut⟩ := hM (S ∩ Ω) Finset.inter_subset_right hc.1
      (fun h' => hc.2 (h'.trans Finset.inter_subset_left))
    have heb : e ≠ b := by
      rintro rfl
      simp [MGraph.erase] at hce
    have h1' : (G.ends e).1 ∈ Ω := h1
    have h2' : (G.ends e).2 ∈ Ω := h2
    refine ⟨e, Finset.mem_union_right _ he, ?_, hΩ h1', hΩ h2', ?_⟩
    · simp only [MGraph.erase, MGraph.induce, Function.update_of_ne heb] at hce ⊢
      intro h'
      simp [h'] at hce
    · change ((G.ends e).1 ∈ S ∩ Ω ∧ (G.ends e).2 ∉ S ∩ Ω) ∨
        ((G.ends e).1 ∉ S ∩ Ω ∧ (G.ends e).2 ∈ S ∩ Ω) at hcut
      change ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∉ S) ∨ ((G.ends e).1 ∉ S ∧ (G.ends e).2 ∈ S)
      simp only [Finset.mem_inter, h1', h2', and_true] at hcut
      exact hcut
  · obtain ⟨e, he, hce, h1, h2, hcut⟩ := hN S hS hne hn
    have hin : ¬ ((G.ends e).1 ∈ Ω ∧ (G.ends e).2 ∈ Ω) := by
      rintro ⟨g1, g2⟩
      apply hc
      rcases hcut with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · exact ⟨⟨_, Finset.mem_inter.2 ⟨c1, g1⟩⟩, fun h' => c2 (h' g2)⟩
      · exact ⟨⟨_, Finset.mem_inter.2 ⟨c2, g2⟩⟩, fun h' => c1 (h' g1)⟩
    have heb : e ≠ b := fun h' => hin (h' ▸ hb)
    refine ⟨e, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hin⟩), ?_, h1, h2, hcut⟩
    simpa [MGraph.erase, Function.update_of_ne heb] using hce

/-- The doubly connected property of `G` without `b`, from that of `G` and of the subgraph induced
on `Ω` without `b`, when both ends of `b` lie in `Ω`. -/
private theorem dc_erase_induce [DecidableEq V] [DecidableEq E] {G : MGraph V E} (hG : G.DC)
    {Ω : Finset V} (hΩ : Ω ⊆ G.int) {b : E} (hb : (G.ends b).1 ∈ Ω ∧ (G.ends b).2 ∈ Ω)
    (hH : ((G.induce Ω).erase b).DC) : (G.erase b).DC := by
  obtain ⟨bk, bl, hd, hbk, hbl, hsk, hsl⟩ := hG
  obtain ⟨ck, cl, hd', hck, hcl, hsk', hsl'⟩ := hH
  have hHc : ∀ e, ((G.induce Ω).erase b).cls e ≠ none →
      e ≠ b ∧ (G.ends e).1 ∈ Ω ∧ (G.ends e).2 ∈ Ω ∧ ((G.induce Ω).erase b).cls e = G.cls e := by
    intro e he
    have heb : e ≠ b := by
      rintro rfl
      simp [MGraph.erase] at he
    simp only [MGraph.erase, MGraph.induce, Function.update_of_ne heb] at he ⊢
    split_ifs at he ⊢ with hi
    · exact ⟨heb, hi.1, hi.2, rfl⟩
    · exact absurd rfl he
  have hEc : ∀ e, e ≠ b → (G.erase b).cls e = G.cls e := fun e he => by
    simp [MGraph.erase, Function.update_of_ne he]
  have hbin : ∀ e, ¬ ((G.ends e).1 ∈ Ω ∧ (G.ends e).2 ∈ Ω) → e ≠ b := fun e he h' => he (h' ▸ hb)
  refine ⟨bk.filter (fun e => ¬ ((G.ends e).1 ∈ Ω ∧ (G.ends e).2 ∈ Ω)) ∪ ck,
    bl.filter (fun e => ¬ ((G.ends e).1 ∈ Ω ∧ (G.ends e).2 ∈ Ω)) ∪ cl, ?_, ?_, ?_,
    spans_erase_induce hΩ hb hsk hsk', spans_erase_induce hΩ hb hsl hsl'⟩
  · rw [Finset.disjoint_left]
    intro e he he'
    rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
    · exact Finset.disjoint_left.1 hd (Finset.mem_filter.1 he).1 (Finset.mem_filter.1 he').1
    · have := hHc e (by rcases hcl e he' with h' | h' | h' <;> rw [h'] <;> simp)
      exact (Finset.mem_filter.1 he).2 ⟨this.2.1, this.2.2.1⟩
    · have := hHc e (by rw [hck e he]; simp)
      exact (Finset.mem_filter.1 he').2 ⟨this.2.1, this.2.2.1⟩
    · exact Finset.disjoint_left.1 hd' he he'
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨he, hin⟩ := Finset.mem_filter.1 he
      rw [hEc e (hbin e hin)]
      exact hbk e he
    · have := hHc e (by rw [hck e he]; simp)
      rw [hEc e this.1, ← this.2.2.2]
      exact hck e he
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨he, hin⟩ := Finset.mem_filter.1 he
      rw [hEc e (hbin e hin)]
      exact hbl e he
    · have := hHc e (by rcases hcl e he with h' | h' | h' <;> rw [h'] <;> simp)
      rw [hEc e this.1, ← this.2.2.2]
      exact hcl e he

/-! ## Induced and replaced subgraphs -/

private theorem itp {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

private theorem itn {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

section Repl

variable [DecidableEq V] [DecidableEq E] {G : MGraph V E} {S P A : Finset V} {e e₁ e₂ : E}

private theorem rep_cls₁ : (G.replace S P e₁ e₂).cls e₁ = some .diff := by
  simp [MGraph.replace]

private theorem rep_ends₁ : (G.replace S P e₁ e₂).ends e₁ = (G.outer P e₁, G.outer P e₂) := by
  simp [MGraph.replace]

private theorem rep_cls₂ (h : e₂ ≠ e₁) : (G.replace S P e₁ e₂).cls e₂ = none := by
  simp [MGraph.replace, h]

private theorem rep_cls (h1 : e ≠ e₁) (h2 : e ≠ e₂) :
    (G.replace S P e₁ e₂).cls e = (G.induce (S \ P)).cls e := by
  simp [MGraph.replace, h1, h2]

private theorem rep_ends (h1 : e ≠ e₁) : (G.replace S P e₁ e₂).ends e = G.ends e := by
  simp [MGraph.replace, h1]

omit [DecidableEq E] in
private theorem ind_cls : (G.induce A).cls e =
    if (G.ends e).1 ∈ A ∧ (G.ends e).2 ∈ A then G.cls e else none := rfl

omit [DecidableEq E] in
/-- An edge of the induced subgraph is live iff it is live in the graph with both ends in the
set. -/
private theorem live_induce :
    Live (G.induce A) e ↔ (G.ends e).1 ∈ A ∧ (G.ends e).2 ∈ A ∧ G.cls e ≠ none ∧
      G.cls e ≠ some .minus := by
  unfold Live
  rw [ind_cls]
  change (_ ≠ none ∧ _ ≠ some MClass.minus ∧ (G.ends e).1 ∈ A ∧ (G.ends e).2 ∈ A) ↔ _
  split_ifs with hA
  · tauto
  · simp only [ne_eq, not_true_eq_false, false_and, false_iff]
    tauto

/-- An edge of the replaced subgraph other than the two edges `e₁`, `e₂` is live iff it is live
in the subgraph induced on `S \ P`. -/
private theorem live_rep (h1 : e ≠ e₁) (h2 : e ≠ e₂) :
    Live (G.replace S P e₁ e₂) e ↔ Live (G.induce (S \ P)) e := by
  unfold Live
  rw [rep_cls h1 h2, rep_ends h1]
  rfl

private theorem live_rep₁ :
    Live (G.replace S P e₁ e₂) e₁ ↔ G.outer P e₁ ∈ S \ P ∧ G.outer P e₂ ∈ S \ P := by
  unfold Live
  rw [rep_cls₁, rep_ends₁]
  exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨by simp, by simp, h.1, h.2⟩⟩

private theorem not_live_rep₂ (h : e₂ ≠ e₁) : ¬ Live (G.replace S P e₁ e₂) e₂ :=
  fun hl => hl.1 (rep_cls₂ h)

end Repl

/-- A pre-deterministic order headed by `b`: the graph with `b` changed into a `Θ` edge is
pre-deterministic, with the rest of the order. -/
private theorem preDet_convert_head [DecidableEq E] {G : MGraph V E} {l : List E} {b : E}
    (hl : G.IsPDOrder l) (hh : l.head? = some b) : (G.convert [b]).PreDet := by
  obtain ⟨t, rfl⟩ : ∃ t, l = b :: t := by
    cases l with
    | nil => simp at hh
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨t, by rw [hh]⟩
  obtain ⟨hnd, hmem, hred⟩ := hl
  have hbt : b ∉ t := (List.nodup_cons.1 hnd).1
  have hc : ∀ m, (G.convert [b]).convert m = G.convert (b :: m) := by
    intro m
    refine MolInsert_ext rfl rfl rfl (funext fun e => ?_)
    simp only [MGraph.convert]
    by_cases heb : e = b
    · subst heb
      by_cases hp : G.cls e = some .plus <;> simp [hp]
    · simp [heb]
  have hdc : G.DC := by
    have := hred 0 (by simp)
    simpa [convert_nil] using this.2.1
  refine ⟨MGraph.DC_convert _ _ G [b] hdc, t, (List.nodup_cons.1 hnd).2, fun e => ?_,
    fun j hj => ?_⟩
  · constructor
    · intro het
      have hne : e ≠ b := fun h' => hbt (h' ▸ het)
      obtain ⟨hp, h1, h2⟩ := (hmem e).1 (List.mem_cons_of_mem _ het)
      exact ⟨by simp [MGraph.convert, hne, hp], h1, h2⟩
    · rintro ⟨hp, h1, h2⟩
      have hne : e ≠ b := by
        rintro rfl
        by_cases hpb : G.cls e = some .plus <;> simp [MGraph.convert, hpb] at hp
      have hG : G.IsIntPlus e := ⟨by simpa [MGraph.convert, hne] using hp, h1, h2⟩
      rcases List.mem_cons.1 ((hmem e).2 hG) with h' | h'
      · exact absurd h' hne
      · exact h'
  · have := hred (j + 1) (by simpa using hj)
    rw [hc]
    simpa [List.take_succ_cons] using this

/-! ## Edges of the inserted graph -/

/-- An edge with ends `a`, `c` (in either order) crosses `S` iff exactly one of them lies in
`S`. -/
private theorem cut_of_ends {X : Type} {G : MGraph X E} {S : Finset X} {e : E} {a c : X}
    (h : G.ends e = (a, c) ∨ G.ends e = (c, a)) : G.Cut S e ↔ (a ∈ S ↔ c ∉ S) := by
  unfold MGraph.Cut
  rcases h with h | h <;> rw [h] <;> simp only <;> tauto


section Insert

variable [DecidableEq V] [DecidableEq W] [DecidableEq E] {K : MGraph V E} {L : MGraph W F}
  {σ : W → V} {B : Finset E}

/-- The vertex of the inserted graph at an end `w` of an edge of `L`. -/
private def tau (L : MGraph W F) (σ : W → V) (w : W) : V ⊕ W :=
  if w ∈ L.int then .inr w else .inl (σ w)

private theorem ins_ends_inl (e : E) :
    (K.insert L σ B).ends (.inl e) = (.inl (K.ends e).1, .inl (K.ends e).2) := rfl

private theorem ins_ends_inr (f : F) :
    (K.insert L σ B).ends (.inr f) = (tau L σ (L.ends f).1, tau L σ (L.ends f).2) := rfl

private theorem ins_cls_inl (e : E) :
    (K.insert L σ B).cls (.inl e) = if e ∈ B then none else K.cls e := rfl

private theorem ins_cls_inr (f : F) : (K.insert L σ B).cls (.inr f) = L.cls f := rfl

private theorem ins_int : (K.insert L σ B).int = K.int.disjSum L.int := rfl

private theorem vtx_inl (v : V) : (K.insert L σ B).IsVtx (.inl v) ↔ K.IsVtx v := by
  simp [MGraph.IsVtx, MGraph.insert]

private theorem vtx_inr (w : W) : (K.insert L σ B).IsVtx (.inr w) ↔ w ∈ L.int := by
  simp [MGraph.IsVtx, MGraph.insert]

omit [DecidableEq V] in
private theorem tau_int {w : W} (hw : w ∈ L.int) : tau L σ w = .inr w := by
  simp [tau, hw]

omit [DecidableEq V] in
private theorem tau_not {w : W} (hw : w ∉ L.int) : tau L σ w = .inl (σ w) := by
  simp [tau, hw]

omit [DecidableEq V] in
private theorem tau_mem (T : Finset V) (Y : Finset W) (w : W) :
    tau L σ w ∈ T.disjSum Y ↔ (w ∈ L.int ∧ w ∈ Y) ∨ (w ∉ L.int ∧ σ w ∈ T) := by
  by_cases hw : w ∈ L.int <;> simp [tau, hw]

/-- The ends of an edge of `L` from an external vertex `w` to an internal vertex `x`, in the
inserted graph: `σ w` and `x`. -/
private theorem ends_att (hd : Disjoint L.int L.ext) {f : F} {w x : W} {u : V} (hw : w ∈ L.ext)
    (hx : x ∈ L.int) (hσ : σ w = u) (ho : L.ends f = (w, x) ∨ L.ends f = (x, w)) :
    (K.insert L σ B).ends (.inr f) = (.inl u, .inr x) ∨
      (K.insert L σ B).ends (.inr f) = (.inr x, .inl u) := by
  have hw' : w ∉ L.int := fun h' => Finset.disjoint_left.1 hd h' hw
  rw [ins_ends_inr]
  rcases ho with ho | ho <;> rw [ho] <;> simp [tau_int hx, tau_not hw', hσ]

/-- An edge of `L` from an external vertex to an internal vertex `x`, neither absent nor red,
crosses `T ⊔ Y` in the inserted graph iff exactly one of `σ w`, `x` lies in it. -/
private theorem crosses_att {f : F} {u : V} {x : W} (hu : u ∈ K.int) (hx : x ∈ L.int)
    (hc : L.cls f ≠ none) (hc' : L.cls f ≠ some .minus)
    (he : (K.insert L σ B).ends (.inr f) = (.inl u, .inr x) ∨
      (K.insert L σ B).ends (.inr f) = (.inr x, .inl u)) (T : Finset V) (Y : Finset W) :
    (K.insert L σ B).Crosses (T.disjSum Y) (.inr f) ↔ (u ∈ T ↔ x ∉ Y) := by
  unfold MGraph.Crosses
  rw [cut_of_ends he, ins_cls_inr]
  have hv : (K.insert L σ B).IsVtx (.inl u) := (vtx_inl u).2 (Or.inl hu)
  have hv' : (K.insert L σ B).IsVtx (.inr x) := (vtx_inr x).2 hx
  rcases he with he | he <;> rw [he] <;> simp [hc, hc', hv, hv']

/-- The red solid edge of `L` from an external vertex to an internal vertex `x` is a red edge
between `T ⊔ Y` and its complement iff exactly one of `σ w`, `x` lies in it. -/
private theorem red_att {f : F} {u : V} {x : W} (hu : u ∈ K.int) (hx : x ∈ L.int)
    (hc : L.cls f = some .minus)
    (he : (K.insert L σ B).ends (.inr f) = (.inl u, .inr x) ∨
      (K.insert L σ B).ends (.inr f) = (.inr x, .inl u)) (T : Finset V) (Y : Finset W) :
    (K.insert L σ B).RedCrosses (T.disjSum Y) (.inr f) ↔ (u ∈ T ↔ x ∉ Y) := by
  unfold MGraph.RedCrosses
  rw [cut_of_ends he, ins_cls_inr]
  have hv : (K.insert L σ B).IsVtx (.inl u) := (vtx_inl u).2 (Or.inl hu)
  have hv' : (K.insert L σ B).IsVtx (.inr x) := (vtx_inr x).2 hx
  rcases he with he | he <;> rw [he] <;> simp [hc, hv, hv']

omit [DecidableEq W] in
/-- In `L`, an edge from an external vertex `w` to an internal vertex `x`, neither absent nor
red, crosses a set `Y` of internal vertices iff `x ∈ Y`. -/
private theorem lcross_att (hd : Disjoint L.int L.ext) {f : F} {w x : W} (hw : w ∈ L.ext)
    (hx : x ∈ L.int) (hc : L.cls f ≠ none) (hc' : L.cls f ≠ some .minus)
    (ho : L.ends f = (w, x) ∨ L.ends f = (x, w)) {Y : Finset W} (hY : Y ⊆ L.int) :
    L.Crosses Y f ↔ x ∈ Y := by
  have hwY : w ∉ Y := fun h' => Finset.disjoint_left.1 hd (hY h') hw
  unfold MGraph.Crosses
  rw [cut_of_ends ho]
  rcases ho with ho | ho <;> rw [ho] <;> simp [hc, hc', hwY, MGraph.IsVtx, hw, hx]

omit [DecidableEq W] in
/-- In `L`, a red solid edge from an external vertex `w` to an internal vertex `x` is a red edge
between a set `Y` of internal vertices and its complement iff `x ∈ Y`. -/
private theorem lred_att (hd : Disjoint L.int L.ext) {f : F} {w x : W} (hw : w ∈ L.ext)
    (hx : x ∈ L.int) (hc : L.cls f = some .minus)
    (ho : L.ends f = (w, x) ∨ L.ends f = (x, w)) {Y : Finset W} (hY : Y ⊆ L.int) :
    L.RedCrosses Y f ↔ x ∈ Y := by
  have hwY : w ∉ Y := fun h' => Finset.disjoint_left.1 hd (hY h') hw
  unfold MGraph.RedCrosses
  rw [cut_of_ends ho]
  rcases ho with ho | ho <;> rw [ho] <;> simp [hc, hwY, MGraph.IsVtx, hw, hx]

/-- An edge of `L` with both ends internal crosses `T ⊔ Y` in the inserted graph iff it crosses
`Y` in `L`. -/
private theorem crosses_int {f : F}
    (ho : L.cls f ≠ none → (L.ends f).1 ∈ L.int ∧ (L.ends f).2 ∈ L.int)
    (T : Finset V) (Y : Finset W) :
    (K.insert L σ B).Crosses (T.disjSum Y) (.inr f) ↔ L.Crosses Y f := by
  by_cases hc : L.cls f = none
  · simp [MGraph.Crosses, ins_cls_inr, hc]
  obtain ⟨h1, h2⟩ := ho hc
  unfold MGraph.Crosses MGraph.Cut
  rw [ins_ends_inr, ins_cls_inr, tau_int h1, tau_int h2, vtx_inr, vtx_inr]
  simp [MGraph.IsVtx, h1, h2]

/-- An edge of `L` with both ends internal is a red edge between `T ⊔ Y` and its complement in
the inserted graph iff it is one between `Y` and its complement in `L`. -/
private theorem red_int {f : F}
    (ho : L.cls f ≠ none → (L.ends f).1 ∈ L.int ∧ (L.ends f).2 ∈ L.int)
    (T : Finset V) (Y : Finset W) :
    (K.insert L σ B).RedCrosses (T.disjSum Y) (.inr f) ↔ L.RedCrosses Y f := by
  by_cases hc : L.cls f = none
  · simp [MGraph.RedCrosses, ins_cls_inr, hc]
  obtain ⟨h1, h2⟩ := ho hc
  unfold MGraph.RedCrosses MGraph.Cut
  rw [ins_ends_inr, ins_cls_inr, tau_int h1, tau_int h2, vtx_inr, vtx_inr]
  simp [MGraph.IsVtx, h1, h2]

/-- An edge of `K` crosses `T ⊔ Y` in the inserted graph iff it is not in `B` and crosses `T` in
`K`. -/
private theorem crosses_inl (e : E) (T : Finset V) (Y : Finset W) :
    (K.insert L σ B).Crosses (T.disjSum Y) (.inl e) ↔ e ∉ B ∧ K.Crosses T e := by
  unfold MGraph.Crosses MGraph.Cut
  rw [ins_ends_inl, ins_cls_inl, vtx_inl, vtx_inl]
  by_cases he : e ∈ B <;> simp [he]

/-- An edge of `K` is a red edge between `T ⊔ Y` and its complement in the inserted graph iff it
is not in `B` and is one between `T` and its complement in `K`. -/
private theorem red_inl (e : E) (T : Finset V) (Y : Finset W) :
    (K.insert L σ B).RedCrosses (T.disjSum Y) (.inl e) ↔ e ∉ B ∧ K.RedCrosses T e := by
  unfold MGraph.RedCrosses MGraph.Cut
  rw [ins_ends_inl, ins_cls_inl, vtx_inl, vtx_inl]
  by_cases he : e ∈ B <;> simp [he]

end Insert

/-- A set crossed by three distinct edges is not isolated. -/
private theorem not_iso_three {X : Type} {G : MGraph X E} {P : Finset X} {a c d : E} (h1 : a ≠ c)
    (h2 : a ≠ d) (h3 : c ≠ d) (ha : G.Crosses P a) (hc : G.Crosses P c) (hd : G.Crosses P d) :
    ¬ G.IsIsolated P := by
  rintro ⟨-, e₁, e₂, -, h⟩
  rcases (h a).1 ha with rfl | rfl <;> rcases (h c).1 hc with rfl | rfl <;>
    rcases (h d).1 hd with rfl | rfl <;> simp_all

/-- Every finite set of vertices of `V ⊕ W` is `T ⊔ Y`. -/
private theorem exists_disjSum {X Y : Type} (P : Finset (X ⊕ Y)) :
    ∃ (T : Finset X) (Y' : Finset Y), P = T.disjSum Y' :=
  ⟨_, _, Finset.toLeft_disjSum_toRight.symm⟩

private theorem disjSum_sub {X Y : Type} {T T' : Finset X} {Y₁ Y₂ : Finset Y} :
    T.disjSum Y₁ ⊆ T'.disjSum Y₂ ↔ T ⊆ T' ∧ Y₁ ⊆ Y₂ := by
  simp [Finset.disjSum_subset]

private theorem disjSum_ssub {X Y : Type} {T T' : Finset X} {Y₁ Y₂ : Finset Y} :
    T.disjSum Y₁ ⊂ T'.disjSum Y₂ ↔ (T ⊆ T' ∧ Y₁ ⊆ Y₂) ∧ ¬ (T' ⊆ T ∧ Y₂ ⊆ Y₁) := by
  rw [Finset.ssubset_def, disjSum_sub, disjSum_sub]

/-! ## The hypotheses of [II, Lemma 6.5 (2)] on `K` and `L` -/

section Glue

variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
  {K : MGraph V E} {L : MGraph W F} {σ : W → V} {u₀ u₁ u₂ : V} {b r : E}
  {f₀ f₁ f₂ : F} {w₀ w₁ w₂ x₀ x₁ x₂ : W}

/-- The hypotheses of `MGraph.spd_insert` on `K` and `L`, with the three edges `f₀`, `f₁`, `f₂`
of `L` from its external vertices `w₀`, `w₁`, `w₂` to its internal vertices `x₀`, `x₁`, `x₂`. -/
private structure Hyp (K : MGraph V E) (L : MGraph W F) (σ : W → V) (u₀ u₁ u₂ : V) (b r : E)
    (f₀ f₁ f₂ : F) (w₀ w₁ w₂ x₀ x₁ x₂ : W) : Prop where
  kspd : K.SPD
  kdis : Disjoint K.int K.ext
  hu₀ : u₀ ∈ K.int
  hu₁ : u₁ ∈ K.int
  mis₀ : u₀ ∈ K.MIS
  mis₁ : u₁ ∈ K.MIS
  k3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
    ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b)
  k4 : K.cls r = none ∨ K.cls r = some .minus
  k5 : ∃ e, K.cls e ≠ none ∧ K.cls e ≠ some .minus ∧
    (((K.ends e).1 ∈ K.int ∧ (K.ends e).2 ∈ K.ext) ∨
      ((K.ends e).1 ∈ K.ext ∧ (K.ends e).2 ∈ K.int))
  lspd : L.SPD
  ldis : Disjoint L.int L.ext
  f01 : f₀ ≠ f₁
  f02 : f₀ ≠ f₂
  f12 : f₁ ≠ f₂
  hw₀ : w₀ ∈ L.ext
  hw₁ : w₁ ∈ L.ext
  hw₂ : w₂ ∈ L.ext
  σ₀ : σ w₀ = u₀
  σ₁ : σ w₁ = u₁
  σ₂ : σ w₂ = u₂
  hx₀ : x₀ ∈ L.int
  hx₁ : x₁ ∈ L.int
  hx₂ : x₂ ∈ L.int
  o₀ : L.ends f₀ = (w₀, x₀) ∨ L.ends f₀ = (x₀, w₀)
  o₁ : L.ends f₁ = (w₁, x₁) ∨ L.ends f₁ = (x₁, w₁)
  o₂ : L.ends f₂ = (w₂, x₂) ∨ L.ends f₂ = (x₂, w₂)
  c₀ : L.cls f₀ = some .diff
  c₁ : L.cls f₁ = some .plus ∨ L.cls f₁ = some .diff
  c₂ : L.cls f₂ = some .minus
  oth : ∀ f, f ≠ f₀ → f ≠ f₁ → f ≠ f₂ → L.cls f ≠ none →
    (L.ends f).1 ∈ L.int ∧ (L.ends f).2 ∈ L.int

namespace Hyp

variable (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
include h

private theorem m₀ : ∀ P, K.IsProperIso K.int P → u₀ ∈ P := by
  have := h.mis₀
  simp only [MGraph.MIS, Finset.mem_filter] at this
  exact this.2

private theorem m₁ : ∀ P, K.IsProperIso K.int P → u₁ ∈ P := by
  have := h.mis₁
  simp only [MGraph.MIS, Finset.mem_filter] at this
  exact this.2

private theorem c₁n : L.cls f₁ ≠ none := by rcases h.c₁ with h' | h' <;> rw [h'] <;> simp

private theorem c₁m : L.cls f₁ ≠ some .minus := by rcases h.c₁ with h' | h' <;> rw [h'] <;> simp

private theorem e₀ : (K.insert L σ {b, r}).ends (.inr f₀) = (.inl u₀, .inr x₀) ∨
    (K.insert L σ {b, r}).ends (.inr f₀) = (.inr x₀, .inl u₀) :=
  ends_att h.ldis h.hw₀ h.hx₀ h.σ₀ h.o₀

private theorem e₁ : (K.insert L σ {b, r}).ends (.inr f₁) = (.inl u₁, .inr x₁) ∨
    (K.insert L σ {b, r}).ends (.inr f₁) = (.inr x₁, .inl u₁) :=
  ends_att h.ldis h.hw₁ h.hx₁ h.σ₁ h.o₁

private theorem e₂ : (K.insert L σ {b, r}).ends (.inr f₂) = (.inl u₂, .inr x₂) ∨
    (K.insert L σ {b, r}).ends (.inr f₂) = (.inr x₂, .inl u₂) :=
  ends_att h.ldis h.hw₂ h.hx₂ h.σ₂ h.o₂

private theorem cr₀ (T : Finset V) (Y : Finset W) :
    (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inr f₀) ↔ (u₀ ∈ T ↔ x₀ ∉ Y) :=
  crosses_att h.hu₀ h.hx₀ (by rw [h.c₀]; simp) (by rw [h.c₀]; simp) h.e₀ T Y

private theorem cr₁ (T : Finset V) (Y : Finset W) :
    (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inr f₁) ↔ (u₁ ∈ T ↔ x₁ ∉ Y) :=
  crosses_att h.hu₁ h.hx₁ h.c₁n h.c₁m h.e₁ T Y

omit h in
private theorem ncr₂ (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) (P : Finset (V ⊕ W)) :
    ¬ (K.insert L σ {b, r}).Crosses P (.inr f₂) := fun hc => hc.2.1 h.c₂

private theorem crl (e : E) (T : Finset V) (Y : Finset W) :
    (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inl e) ↔ e ≠ b ∧ K.Crosses T e := by
  rw [crosses_inl]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · exact fun ⟨⟨hb, _⟩, hc⟩ => ⟨hb, hc⟩
  · refine fun ⟨hb, hc⟩ => ⟨⟨hb, fun hr => ?_⟩, hc⟩
    subst hr
    rcases h.k4 with h' | h'
    · exact hc.1 h'
    · exact hc.2.1 h'

private theorem cro {f : F} (h0 : f ≠ f₀) (h1 : f ≠ f₁) (h2 : f ≠ f₂) (T : Finset V)
    (Y : Finset W) :
    (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inr f) ↔ L.Crosses Y f :=
  crosses_int (h.oth f h0 h1 h2) T Y

private theorem lcr₀ {Y : Finset W} (hY : Y ⊆ L.int) : L.Crosses Y f₀ ↔ x₀ ∈ Y :=
  lcross_att h.ldis h.hw₀ h.hx₀ (by rw [h.c₀]; simp) (by rw [h.c₀]; simp) h.o₀ hY

private theorem lcr₁ {Y : Finset W} (hY : Y ⊆ L.int) : L.Crosses Y f₁ ↔ x₁ ∈ Y :=
  lcross_att h.ldis h.hw₁ h.hx₁ h.c₁n h.c₁m h.o₁ hY

private theorem lncr₂ (Y : Finset W) : ¬ L.Crosses Y f₂ := fun hc => hc.2.1 h.c₂

/-- An edge of `L` with both ends internal is none of `f₀`, `f₁`, `f₂`. -/
private theorem int_ne {f : F} (h1 : (L.ends f).1 ∈ L.int) (h2 : (L.ends f).2 ∈ L.int) :
    f ≠ f₀ ∧ f ≠ f₁ ∧ f ≠ f₂ := by
  have hn : ∀ {g : F} {w x : W}, w ∈ L.ext → (L.ends g = (w, x) ∨ L.ends g = (x, w)) → f ≠ g := by
    intro g w x hw ho hfg
    subst hfg
    have hw' : w ∉ L.int := fun h' => Finset.disjoint_left.1 h.ldis h' hw
    rcases ho with ho | ho <;> rw [ho] at h1 h2 <;> simp_all
  exact ⟨hn h.hw₀ h.o₀, hn h.hw₁ h.o₁, hn h.hw₂ h.o₂⟩

/-- No edge of `L` other than `f₀`, `f₁` crosses the set of internal vertices of `L`. -/
private theorem lncr_int {f : F} (h0 : f ≠ f₀) (h1 : f ≠ f₁) : ¬ L.Crosses L.int f := by
  intro hc
  by_cases h2 : f = f₂
  · exact h.lncr₂ _ (h2 ▸ hc)
  obtain ⟨g1, g2⟩ := h.oth f h0 h1 h2 hc.1
  rcases hc.2.2.2.2 with ⟨-, h'⟩ | ⟨h', -⟩ <;> contradiction

/-- The internal vertices of `L` form an isolated set of `L`, crossed by `f₀` and `f₁`. -/
private theorem lint_iso : L.IsIsolated L.int := by
  refine ⟨subset_rfl, f₀, f₁, h.f01, fun f => ⟨fun hc => ?_, ?_⟩⟩
  · by_contra hn
    push Not at hn
    exact h.lncr_int hn.1 hn.2 hc
  · rintro (rfl | rfl)
    · exact (h.lcr₀ subset_rfl).2 h.hx₀
    · exact (h.lcr₁ subset_rfl).2 h.hx₁

/-- The edge `b` does not cross a set containing `u₀` and `u₁`. -/
private theorem b_nc {T : Finset V} (hu₀ : u₀ ∈ T) (hu₁ : u₁ ∈ T) : ¬ K.Crosses T b := by
  intro hc
  rcases h.k3 with ⟨hb, -⟩ | ⟨-, hb, -⟩
  · exact hc.1 hb
  · rcases hc.2.2.2.2 with ⟨-, h'⟩ | ⟨h', -⟩ <;> rw [hb] at h' <;> contradiction

/-- If `b` crosses `T`, exactly one of `u₀`, `u₁` lies in `T`. -/
private theorem b_cr {T : Finset V} (hc : K.Crosses T b) : (u₀ ∈ T ↔ u₁ ∉ T) := by
  rcases h.k3 with ⟨hb, -⟩ | ⟨-, hb, -⟩
  · exact absurd hb hc.1
  · have := hc.2.2.2.2
    unfold MGraph.Cut at this
    rw [hb] at this
    simp only at this
    tauto

/-- A nonempty set of internal vertices of `K` is crossed in `K` by an edge other than `b`. -/
private theorem kcr {T : Finset V} (hT : T ⊆ K.int) (hne : T.Nonempty) :
    ∃ e, K.Crosses T e ∧ e ≠ b := by
  by_cases hall : K.int ⊆ T
  · have hTe : T = K.int := Finset.Subset.antisymm hT hall
    obtain ⟨e, hc, hc', hends⟩ := h.k5
    have hc'' : K.Crosses T e := by
      refine ⟨hc, hc', ?_, ?_, ?_⟩
      · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [Or.inl h1, Or.inr h1]
      · rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩
        exacts [Or.inr h2, Or.inl h2]
      · rw [hTe]
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, fun h' => Finset.disjoint_left.1 h.kdis h' h2⟩
        · exact Or.inr ⟨fun h' => Finset.disjoint_left.1 h.kdis h' h1, h2⟩
    refine ⟨e, hc'', fun heb => ?_⟩
    subst heb
    exact h.b_nc (hTe ▸ h.hu₀) (hTe ▸ h.hu₁) hc''
  · obtain ⟨i, j, -, hi, -, hci, -⟩ := MGraph.claim51 _ _ K h.kspd.1 T hT hne hall
    refine ⟨i, hi, fun hib => ?_⟩
    subst hib
    rcases h.k3 with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] at hci <;> simp at hci

/-- The crossing edges of `∅ ⊔ Y` in the inserted graph are those of `Y` in `L`. -/
private theorem crossSecond {Y : Finset W} (hY : Y ⊆ L.int) (x : E ⊕ F) :
    (K.insert L σ {b, r}).Crosses ((∅ : Finset V).disjSum Y) x ↔
      ∃ f, x = .inr f ∧ L.Crosses Y f := by
  rcases x with e | f
  · rw [h.crl]
    simp [MGraph.Crosses, MGraph.Cut]
  · simp only [Sum.inr.injEq, exists_eq_left']
    by_cases h0 : f = f₀
    · subst h0; rw [h.cr₀, h.lcr₀ hY]; simp
    by_cases h1 : f = f₁
    · subst h1; rw [h.cr₁, h.lcr₁ hY]; simp
    by_cases h2 : f = f₂
    · subst h2; exact iff_of_false (h.ncr₂ _) (h.lncr₂ _)
    exact h.cro h0 h1 h2 _ _

/-- For `T` containing `u₀` and `u₁`, the crossing edges of `T ⊔ L.int` in the inserted graph are
those of `T` in `K`. -/
private theorem crossFirst {T : Finset V} (hu₀ : u₀ ∈ T) (hu₁ : u₁ ∈ T) (x : E ⊕ F) :
    (K.insert L σ {b, r}).Crosses (T.disjSum L.int) x ↔ ∃ e, x = .inl e ∧ K.Crosses T e := by
  rcases x with e | f
  · rw [h.crl]
    simp only [Sum.inl.injEq, exists_eq_left']
    exact ⟨fun h' => h'.2, fun h' => ⟨fun heb => h.b_nc hu₀ hu₁ (heb ▸ h'), h'⟩⟩
  · simp only [reduceCtorEq, false_and, exists_false, iff_false]
    by_cases h0 : f = f₀
    · subst h0; rw [h.cr₀]; simp [hu₀, h.hx₀]
    by_cases h1 : f = f₁
    · subst h1; rw [h.cr₁]; simp [hu₁, h.hx₁]
    by_cases h2 : f = f₂
    · subst h2; exact h.ncr₂ _
    rw [h.cro h0 h1 h2]
    exact h.lncr_int h0 h1

end Hyp

/-! ## The isolated sets of the inserted graph -/

/-- Three distinct edges of `K` crossing `T`, and an edge of `L` crossing `T ⊔ Y` if `b` crosses
`T`, give three edges crossing `T ⊔ Y` in the inserted graph. -/
private theorem Hyp.three_K (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {T : Finset V} {Y : Finset W} {i j k : E} (hi : K.Crosses T i) (hj : K.Crosses T j)
    (hk : K.Crosses T k) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hbf : K.Crosses T b → ∃ f, (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inr f)) :
    ¬ (K.insert L σ {b, r}).IsIsolated (T.disjSum Y) := by
  have lift : ∀ e, K.Crosses T e → e ≠ b →
      (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inl e) :=
    fun e he hb => (h.crl e T Y).2 ⟨hb, he⟩
  by_cases hib : i = b
  · subst hib
    obtain ⟨f, hf⟩ := hbf hi
    exact not_iso_three (by simpa using hkj.symm) (by simp) (by simp) (lift j hj (Ne.symm hij))
      (lift k hk hki) hf
  by_cases hjb : j = b
  · subst hjb
    obtain ⟨f, hf⟩ := hbf hj
    exact not_iso_three (by simpa using hki.symm) (by simp) (by simp) (lift i hi hib)
      (lift k hk hkj) hf
  by_cases hkb : k = b
  · subst hkb
    obtain ⟨f, hf⟩ := hbf hk
    exact not_iso_three (by simpa using hij) (by simp) (by simp) (lift i hi hib) (lift j hj hjb) hf
  exact not_iso_three (by simpa using hij) (by simpa using hki.symm) (by simpa using hkj.symm)
    (lift i hi hib) (lift j hj hjb) (lift k hk hkb)

/-- **The isolated sets of the inserted graph** ([II, Lemma 6.5 (2)], chain (6.6)): `T ⊔ Y` is
isolated iff either `Y` is the set of internal vertices of `L` and `T` is an isolated set of `K`
containing `u₀` and `u₁`, or `T` is empty and `Y` is an isolated set of `L`. -/
private theorem Hyp.iso_iff (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    (T : Finset V) (Y : Finset W) :
    (K.insert L σ {b, r}).IsIsolated (T.disjSum Y) ↔
      (Y = L.int ∧ u₀ ∈ T ∧ u₁ ∈ T ∧ K.IsIsolated T) ∨ (T = ∅ ∧ L.IsIsolated Y) := by
  constructor
  · intro hP
    obtain ⟨hsub, a, c, hac, hcr⟩ := hP
    rw [ins_int, disjSum_sub] at hsub
    obtain ⟨hT, hY⟩ := hsub
    by_cases hT0 : T = ∅
    · subst hT0
      refine Or.inr ⟨rfl, hY, ?_⟩
      obtain ⟨a', rfl, -⟩ := (h.crossSecond hY a).1 ((hcr a).2 (Or.inl rfl))
      obtain ⟨c', rfl, -⟩ := (h.crossSecond hY c).1 ((hcr c).2 (Or.inr rfl))
      refine ⟨a', c', fun h' => hac (h' ▸ rfl), fun f => ?_⟩
      have := hcr (.inr f)
      rw [h.crossSecond hY] at this
      simpa using this
    have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hT0
    by_cases hYm : Y.Nonempty ∧ ¬ L.int ⊆ Y
    · exfalso
      obtain ⟨bk, bl, hd, hbk, hbl, hsk, hsl⟩ := h.lspd.1
      obtain ⟨f, hfb, hfc, hf1, hf2, hfcut⟩ := hsk Y hY hYm.1 hYm.2
      obtain ⟨f', hfb', hfc', hf1', hf2', hfcut'⟩ := hsl Y hY hYm.1 hYm.2
      obtain ⟨n0, n1, n2⟩ := h.int_ne hf1 hf2
      obtain ⟨n0', n1', n2'⟩ := h.int_ne hf1' hf2'
      obtain ⟨e, he, heb⟩ := h.kcr hT hTne
      have hff : f ≠ f' := fun h' => Finset.disjoint_left.1 hd hfb (h' ▸ hfb')
      have c1 : (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inr f) :=
        (h.cro n0 n1 n2 T Y).2 ⟨hfc, by rw [hbk f hfb]; simp, Or.inl hf1, Or.inl hf2, hfcut⟩
      have c2 : (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inr f') :=
        (h.cro n0' n1' n2' T Y).2 ⟨hfc',
          by rcases hbl f' hfb' with h' | h' | h' <;> rw [h'] <;> simp,
          Or.inl hf1', Or.inl hf2', hfcut'⟩
      have c3 : (K.insert L σ {b, r}).Crosses (T.disjSum Y) (.inl e) := (h.crl e T Y).2 ⟨heb, he⟩
      exact not_iso_three (by simpa using hff) (by simp) (by simp) c1 c2 c3
        ⟨by rw [ins_int, disjSum_sub]; exact ⟨hT, hY⟩, a, c, hac, hcr⟩
    have hY' : Y = ∅ ∨ Y = L.int := by
      by_cases hYe : Y = ∅
      · exact Or.inl hYe
      · push Not at hYm
        exact Or.inr (Finset.Subset.antisymm hY (hYm (Finset.nonempty_iff_ne_empty.2 hYe)))
    have hPi : (K.insert L σ {b, r}).IsIsolated (T.disjSum Y) :=
      ⟨by rw [ins_int, disjSum_sub]; exact ⟨hT, hY⟩, a, c, hac, hcr⟩
    by_cases hu : u₀ ∈ T ∧ u₁ ∈ T
    · rcases hY' with rfl | rfl
      · exfalso
        obtain ⟨e, he, heb⟩ := h.kcr hT hTne
        exact not_iso_three (by simpa using h.f01) (by simp) (by simp)
          ((h.cr₀ T ∅).2 (by simp [hu.1])) ((h.cr₁ T ∅).2 (by simp [hu.2]))
          ((h.crl e T ∅).2 ⟨heb, he⟩) hPi
      · refine Or.inl ⟨rfl, hu.1, hu.2, hT, ?_⟩
        obtain ⟨a', rfl, -⟩ := (h.crossFirst hu.1 hu.2 a).1 ((hcr a).2 (Or.inl rfl))
        obtain ⟨c', rfl, -⟩ := (h.crossFirst hu.1 hu.2 c).1 ((hcr c).2 (Or.inr rfl))
        refine ⟨a', c', fun h' => hac (h' ▸ rfl), fun e => ?_⟩
        have := hcr (.inl e)
        rw [h.crossFirst hu.1 hu.2] at this
        simpa using this
    · exfalso
      have hTp : ¬ K.int ⊆ T := fun hs => hu ⟨hs h.hu₀, hs h.hu₁⟩
      have hTni : ¬ K.IsIsolated T := fun hi =>
        hu ⟨h.m₀ T ⟨hi, Finset.ssubset_def.2 ⟨hT, hTp⟩⟩,
          h.m₁ T ⟨hi, Finset.ssubset_def.2 ⟨hT, hTp⟩⟩⟩
      obtain ⟨i, j, hij, hi, hj, -⟩ := MGraph.claim51 _ _ K h.kspd.1 T hT hTne hTp
      obtain ⟨k, hk, hki, hkj⟩ : ∃ k, K.Crosses T k ∧ k ≠ i ∧ k ≠ j := by
        by_contra hn
        push Not at hn
        refine hTni ⟨hT, i, j, hij, fun e => ⟨fun he => ?_, fun h' => ?_⟩⟩
        · by_contra h'
          push Not at h'
          exact h'.2 (hn e he h'.1)
        · rcases h' with rfl | rfl
          exacts [hi, hj]
      refine h.three_K hi hj hk hij hki hkj (fun hb => ?_) hPi
      have hx := h.b_cr hb
      rcases hY' with rfl | rfl
      · by_cases h0 : u₀ ∈ T
        · exact ⟨f₀, (h.cr₀ T ∅).2 (iff_of_true h0 (Finset.notMem_empty _))⟩
        · exact ⟨f₁, (h.cr₁ T ∅).2
            (iff_of_true (by_contra fun h' => h0 (hx.2 h')) (Finset.notMem_empty _))⟩
      · by_cases h0 : u₀ ∈ T
        · exact ⟨f₁, (h.cr₁ _ _).2 (iff_of_false (hx.1 h0) (fun h' => h' h.hx₁))⟩
        · exact ⟨f₀, (h.cr₀ _ _).2 (iff_of_false h0 (fun h' => h' h.hx₀))⟩
  · rintro (⟨rfl, hu₀, hu₁, hTi⟩ | ⟨rfl, hYi⟩)
    · obtain ⟨hT, a, c, hac, hcr⟩ := hTi
      refine ⟨by rw [ins_int, disjSum_sub]; exact ⟨hT, subset_rfl⟩, .inl a, .inl c,
        by simpa using hac, fun x => ?_⟩
      rw [h.crossFirst hu₀ hu₁]
      constructor
      · rintro ⟨e, rfl, he⟩
        rcases (hcr e).1 he with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · exact ⟨a, rfl, (hcr a).2 (Or.inl rfl)⟩
        · exact ⟨c, rfl, (hcr c).2 (Or.inr rfl)⟩
    · obtain ⟨hY, a, c, hac, hcr⟩ := hYi
      refine ⟨by rw [ins_int, disjSum_sub]; exact ⟨Finset.empty_subset _, hY⟩, .inr a, .inr c,
        by simpa using hac, fun x => ?_⟩
      rw [h.crossSecond hY]
      constructor
      · rintro ⟨f, rfl, hf⟩
        rcases (hcr f).1 hf with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · exact ⟨a, rfl, (hcr a).2 (Or.inl rfl)⟩
        · exact ⟨c, rfl, (hcr c).2 (Or.inr rfl)⟩

/-- The internal vertices of `L` form an isolated set of the inserted graph. -/
private theorem Hyp.x_iso (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.insert L σ {b, r}).IsIsolated ((∅ : Finset V).disjSum L.int) :=
  (h.iso_iff ∅ L.int).2 (Or.inr ⟨rfl, h.lint_iso⟩)

omit [DecidableEq V] [DecidableEq W] [DecidableEq F] in
/-- A subset of the internal vertices of `L` is a proper subset of `T ⊔ L.int` when `T` is
nonempty. -/
private theorem x_ssub {T : Finset V} {Y : Finset W} {u : V} (hu : u ∈ T) (hY : Y ⊆ L.int) :
    (∅ : Finset V).disjSum Y ⊂ T.disjSum L.int := by
  rw [disjSum_ssub]
  exact ⟨⟨Finset.empty_subset _, hY⟩, fun h' => by simpa using h'.1 hu⟩

/-- **The proper isolated sets form a chain** ([II, Def 5.9 (ii)] for the inserted graph). -/
private theorem Hyp.chain (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.insert L σ {b, r}).IsoChain := by
  intro P Q hP hQ
  obtain ⟨T, Y, rfl⟩ := exists_disjSum P
  obtain ⟨T', Y', rfl⟩ := exists_disjSum Q
  have hPs := hP.2
  have hQs := hQ.2
  rw [ins_int, disjSum_ssub] at hPs hQs
  rcases (h.iso_iff T Y).1 hP.1 with ⟨rfl, -, -, hTi⟩ | ⟨rfl, hYi⟩ <;>
    rcases (h.iso_iff T' Y').1 hQ.1 with ⟨rfl, -, -, hTi'⟩ | ⟨rfl, hYi'⟩
  · have hTp : K.IsProperIso K.int T :=
      ⟨hTi, Finset.ssubset_def.2 ⟨hPs.1.1, fun h' => hPs.2 ⟨h', subset_rfl⟩⟩⟩
    have hTp' : K.IsProperIso K.int T' :=
      ⟨hTi', Finset.ssubset_def.2 ⟨hQs.1.1, fun h' => hQs.2 ⟨h', subset_rfl⟩⟩⟩
    rcases h.kspd.2.1 T T' hTp hTp' with h' | h'
    · exact Or.inl (disjSum_sub.2 ⟨h', subset_rfl⟩)
    · exact Or.inr (disjSum_sub.2 ⟨h', subset_rfl⟩)
  · exact Or.inr (disjSum_sub.2 ⟨Finset.empty_subset _, hYi'.1⟩)
  · exact Or.inl (disjSum_sub.2 ⟨Finset.empty_subset _, hYi.1⟩)
  · by_cases hY : Y = L.int
    · subst hY
      exact Or.inr (disjSum_sub.2 ⟨subset_rfl, hYi'.1⟩)
    by_cases hY' : Y' = L.int
    · subst hY'
      exact Or.inl (disjSum_sub.2 ⟨subset_rfl, hYi.1⟩)
    rcases h.lspd.2.1 Y Y' ⟨hYi, Finset.ssubset_iff_subset_ne.2 ⟨hYi.1, hY⟩⟩
      ⟨hYi', Finset.ssubset_iff_subset_ne.2 ⟨hYi'.1, hY'⟩⟩ with h' | h'
    · exact Or.inl (disjSum_sub.2 ⟨subset_rfl, h'⟩)
    · exact Or.inr (disjSum_sub.2 ⟨subset_rfl, h'⟩)

/-! ## The inserted graph is doubly connected -/

/-- The doubly connected property of `K` without `b` ([II, Lemma 6.5 (2)]): in Case B, from the
pre-deterministic order of the subgraph induced on the minimal isolated subset headed by `b`. -/
private theorem Hyp.kdc' (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.erase b).DC := by
  rcases h.k3 with ⟨hb, -⟩ | ⟨-, hbe, l, hl, hlh⟩
  · have : K.erase b = K :=
      MolInsert_ext rfl rfl rfl (by simp [MGraph.erase, Function.update_eq_self_iff, hb])
    rw [this]
    exact h.kspd.1
  · obtain ⟨t, rfl⟩ : ∃ t, l = b :: t := by
      cases l with
      | nil => simp at hlh
      | cons a t =>
        simp only [List.head?_cons, Option.some.injEq] at hlh
        exact ⟨t, by rw [hlh]⟩
    have hr := hl.2.2 0 (by simp)
    simp only [List.take_zero, List.getElem_cons_zero, convert_nil] at hr
    have hΩ : K.MIS ⊆ K.int := by
      intro v hv
      simp only [MGraph.MIS, Finset.mem_filter] at hv
      exact hv.1
    exact dc_erase_induce h.kspd.1 hΩ (by rw [hbe]; exact ⟨h.mis₁, h.mis₀⟩) hr.2.2

/-- Spanning nets of `K` without `b` and of `L`, and the edge `f` from `u` to `x`, span the
inserted graph. -/
private theorem Hyp.spans (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {N : Finset E} {M : Finset F} (hN : (K.erase b).Spans N)
    (hNm : ∀ e ∈ N, (K.erase b).cls e ≠ some .minus) (hM : L.Spans M) {f : F} {u : V} {x : W}
    (hu : u ∈ K.int) (hx : x ∈ L.int) (hc : L.cls f ≠ none)
    (he : (K.insert L σ {b, r}).ends (.inr f) = (.inl u, .inr x) ∨
      (K.insert L σ {b, r}).ends (.inr f) = (.inr x, .inl u)) :
    (K.insert L σ {b, r}).Spans (N.image .inl ∪ (M \ {f₀, f₁}).image .inr ∪ {.inr f}) := by
  intro S hS hne hn
  obtain ⟨T, Y, rfl⟩ := exists_disjSum S
  rw [ins_int, disjSum_sub] at hS hn
  obtain ⟨hT, hY⟩ := hS
  by_cases hYc : Y.Nonempty ∧ ¬ L.int ⊆ Y
  · obtain ⟨g, hg, hgc, g1, g2, gcut⟩ := hM Y hY hYc.1 hYc.2
    obtain ⟨n0, n1, -⟩ := h.int_ne g1 g2
    refine ⟨.inr g, by simp [hg, n0, n1], ?_, ?_, ?_, ?_⟩
    · rw [ins_cls_inr]; exact hgc
    · rw [ins_ends_inr, tau_int g1]; simpa [ins_int] using g1
    · rw [ins_ends_inr, tau_int g2]; simpa [ins_int] using g2
    · unfold MGraph.Cut at gcut ⊢
      rw [ins_ends_inr, tau_int g1, tau_int g2]
      simpa using gcut
  by_cases hTc : T.Nonempty ∧ ¬ K.int ⊆ T
  · obtain ⟨e, he', hec, e1, e2, ecut⟩ := hN T hT hTc.1 hTc.2
    have heb : e ≠ b := by
      rintro rfl
      simp [MGraph.erase] at hec
    have hKe : (K.erase b).cls e = K.cls e := by simp [MGraph.erase, Function.update_of_ne heb]
    have her : e ≠ r := by
      rintro rfl
      rcases h.k4 with h' | h'
      · exact hec (hKe.trans h')
      · exact hNm _ he' (hKe.trans h')
    refine ⟨.inl e, by simp [he'], ?_, ?_, ?_, ?_⟩
    · rw [ins_cls_inl]
      simpa [heb, her, hKe] using hec
    · simpa [ins_ends_inl, ins_int] using e1
    · simpa [ins_ends_inl, ins_int] using e2
    · unfold MGraph.Cut at ecut ⊢
      rw [ins_ends_inl]
      simpa using ecut
  refine ⟨.inr f, by simp, by rw [ins_cls_inr]; exact hc, ?_, ?_, ?_⟩
  · rcases he with he | he <;> rw [he] <;> simp [ins_int, hu, hx]
  · rcases he with he | he <;> rw [he] <;> simp [ins_int, hu, hx]
  · rw [cut_of_ends he]
    simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]
    push Not at hYc hTc
    rcases Finset.eq_empty_or_nonempty T with hT0 | hT0 <;>
      rcases Finset.eq_empty_or_nonempty Y with hY0 | hY0
    · subst hT0 hY0
      exact absurd hne (by simp)
    · subst hT0
      simp [hYc hY0 hx]
    · subst hY0
      simp [hTc hT0 hu]
    · exact absurd ⟨hTc hT0, hYc hY0⟩ hn

omit [DecidableEq V] [DecidableEq W] in
private theorem mem_net_inl {N : Finset E} {M : Finset F} {g : F} {e : E} :
    (Sum.inl e : E ⊕ F) ∈ N.image .inl ∪ (M \ {f₀, f₁}).image .inr ∪ {.inr g} ↔ e ∈ N := by
  simp

omit [DecidableEq V] [DecidableEq W] in
private theorem mem_net_inr {N : Finset E} {M : Finset F} {g f : F} :
    (Sum.inr f : E ⊕ F) ∈ N.image .inl ∪ (M \ {f₀, f₁}).image .inr ∪ {.inr g} ↔
      (f ∈ M ∧ f ≠ f₀ ∧ f ≠ f₁) ∨ f = g := by
  simp [or_comm]

/-- **The inserted graph is doubly connected** ([II, Lemma 6.5 (2)], [II, Def 5.9 (i)]): the black
net of `K` without `b`, that of `L` and `f₀`, and the blue net of `K` without `b`, that of `L` and
`f₁`. -/
private theorem Hyp.dc (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.insert L σ {b, r}).DC := by
  obtain ⟨bk, bl, hd, hbk, hbl, hsk, hsl⟩ := h.kdc'
  obtain ⟨ck, cl, hd', hck, hcl, hsk', hsl'⟩ := h.lspd.1
  have hKc : ∀ e, (K.erase b).cls e ≠ none → (K.erase b).cls e ≠ some .minus →
      (K.insert L σ {b, r}).cls (.inl e) = (K.erase b).cls e := by
    intro e hn hm
    have heb : e ≠ b := by
      rintro rfl
      simp [MGraph.erase] at hn
    have hKe : (K.erase b).cls e = K.cls e := by simp [MGraph.erase, Function.update_of_ne heb]
    have her : e ≠ r := by
      rintro rfl
      rcases h.k4 with h' | h'
      · exact hn (hKe.trans h')
      · exact hm (hKe.trans h')
    rw [ins_cls_inl, hKe]
    simp [heb, her]
  refine ⟨bk.image .inl ∪ (ck \ {f₀, f₁}).image .inr ∪ {.inr f₀},
    bl.image .inl ∪ (cl \ {f₀, f₁}).image .inr ∪ {.inr f₁}, ?_, ?_, ?_,
    h.spans hsk (fun e he => by rw [hbk e he]; simp) hsk' h.hu₀ h.hx₀ (by rw [h.c₀]; simp) h.e₀,
    h.spans hsl (fun e he => by rcases hbl e he with h' | h' | h' <;> rw [h'] <;> simp) hsl'
      h.hu₁ h.hx₁ h.c₁n h.e₁⟩
  · rw [Finset.disjoint_left]
    rintro (e | f) hx hx'
    · rw [mem_net_inl] at hx hx'
      exact Finset.disjoint_left.1 hd hx hx'
    · rw [mem_net_inr] at hx hx'
      rcases hx with ⟨hx, -, n1⟩ | rfl <;> rcases hx' with ⟨hx', n0', -⟩ | h'
      · exact Finset.disjoint_left.1 hd' hx hx'
      · exact n1 h'
      · exact n0' rfl
      · exact h.f01 h'
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Finset.mem_sdiff] at hx
    rcases hx with (⟨e, he, rfl⟩ | ⟨f, ⟨hf, -⟩, rfl⟩) | rfl
    · rw [hKc e (by rw [hbk e he]; simp) (by rw [hbk e he]; simp)]
      exact hbk e he
    · rw [ins_cls_inr]; exact hck f hf
    · rw [ins_cls_inr]; exact h.c₀
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Finset.mem_sdiff] at hx
    rcases hx with (⟨e, he, rfl⟩ | ⟨f, ⟨hf, -⟩, rfl⟩) | rfl
    · rw [hKc e (by rcases hbl e he with h' | h' | h' <;> rw [h'] <;> simp)
        (by rcases hbl e he with h' | h' | h' <;> rw [h'] <;> simp)]
      exact hbl e he
    · rw [ins_cls_inr]; exact hcl f hf
    · rw [ins_cls_inr]
      rcases h.c₁ with h' | h' <;> simp [h']

/-! ## The replaced subgraphs of the inserted graph -/

omit [DecidableEq F] in
/-- The subgraph of the inserted graph induced on `∅ ⊔ Y` is that of `L` induced on `Y`. -/
private theorem rel_induceL {Y : Finset W} (hY : Y ⊆ L.int) :
    Rel (L.induce Y) ((K.insert L σ {b, r}).induce ((∅ : Finset V).disjSum Y)) Sum.inr
      Sum.inr := by
  have htY : ∀ p, tau L σ p ∈ (∅ : Finset V).disjSum Y ↔ p ∈ Y := fun p => by
    rw [tau_mem]
    constructor
    · rintro (⟨-, h'⟩ | ⟨-, h'⟩)
      · exact h'
      · simp at h'
    · exact fun h' => Or.inl ⟨hY h', h'⟩
  refine ⟨fun v' => ?_, Sum.inr_injective, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · rcases v' with v | w <;> simp [MGraph.induce]
  · obtain ⟨g1, g2, -, -⟩ := live_induce.1 he
    rw [ind_cls, ind_cls, itp ⟨(htY _).2 g1, (htY _).2 g2⟩, itp ⟨g1, g2⟩, ins_cls_inr]
  · obtain ⟨g1, g2, -, -⟩ := live_induce.1 he
    left
    change (K.insert L σ {b, r}).ends (.inr e) = _
    rw [ins_ends_inr, tau_int (hY g1), tau_int (hY g2)]
    rfl
  · left
    rcases e' with e | f
    · exfalso
      obtain ⟨g1, -, -, -⟩ := live_induce.1 he'
      rw [ins_ends_inl] at g1
      simp at g1
    · obtain ⟨g1, g2, g3, g4⟩ := live_induce.1 he'
      rw [ins_ends_inr, htY] at g1 g2
      exact ⟨f, live_induce.2 ⟨g1, g2, g3, g4⟩, rfl⟩

/-- The replacement of a proper isolated set `Q` of `Y` in the inserted graph is that in `L`. -/
private theorem Hyp.rel_replaceL (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {Y Q : Finset W} (hY : L.IsoOrTop Y) (hYs : Y ⊆ L.int) (hQ : L.IsProperIso Y Q) {a c : F}
    (hac : a ≠ c) (ha : L.Crosses Q a) (hc : L.Crosses Q c) :
    Rel (L.replace Y Q a c) ((K.insert L σ {b, r}).replace ((∅ : Finset V).disjSum Y)
      ((∅ : Finset V).disjSum Q) (.inr a) (.inr c)) Sum.inr Sum.inr := by
  have hQs : Q ⊆ L.int := hQ.2.subset.trans hYs
  have hoa := MGraph.replace_ends _ _ L h.lspd.1 Y Q a hY hQ ha
  have hoc := MGraph.replace_ends _ _ L h.lspd.1 Y Q c hY hQ hc
  have htQ : ∀ p, tau L σ p ∈ (∅ : Finset V).disjSum Q ↔ p ∈ Q := fun p => by
    rw [tau_mem]
    constructor
    · rintro (⟨-, h'⟩ | ⟨-, h'⟩)
      · exact h'
      · simp at h'
    · exact fun h' => Or.inl ⟨hQs h', h'⟩
  have htYQ : ∀ p, tau L σ p ∈ (∅ : Finset V).disjSum Y \ (∅ : Finset V).disjSum Q ↔
      p ∈ Y \ Q := fun p => by
    rw [Finset.mem_sdiff, Finset.mem_sdiff, htQ, tau_mem]
    constructor
    · rintro ⟨⟨-, h'⟩ | ⟨-, h'⟩, h''⟩
      · exact ⟨h', h''⟩
      · simp at h'
    · exact fun h' => ⟨Or.inl ⟨hYs h'.1, h'.1⟩, h'.2⟩
  have hout : ∀ f, (K.insert L σ {b, r}).outer ((∅ : Finset V).disjSum Q) (.inr f) =
      tau L σ (L.outer Q f) := by
    intro f
    unfold MGraph.outer
    rw [ins_ends_inr]
    simp only [htQ]
    split_ifs <;> rfl
  have hac' : (Sum.inr c : E ⊕ F) ≠ .inr a := by simpa using hac.symm
  refine ⟨fun v' => ?_, Sum.inr_injective, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · rcases v' with v | w <;> simp [MGraph.replace]
  · by_cases hea : e = a
    · subst hea
      rw [rep_cls₁, rep_cls₁]
    have hec : e ≠ c := by
      rintro rfl
      exact not_live_rep₂ hac.symm he
    rw [rep_cls (by simpa using hea) (by simpa using hec), rep_cls hea hec]
    obtain ⟨g1, g2, -, -⟩ := live_induce.1 ((live_rep hea hec).1 he)
    rw [ind_cls, ind_cls, itp ⟨(htYQ _).2 g1, (htYQ _).2 g2⟩, itp ⟨g1, g2⟩, ins_cls_inr]
  · left
    by_cases hea : e = a
    · subst hea
      rw [rep_ends₁, rep_ends₁, hout, hout, tau_int (hYs (Finset.mem_sdiff.1 hoa).1),
        tau_int (hYs (Finset.mem_sdiff.1 hoc).1)]
    have hec : e ≠ c := by
      rintro rfl
      exact not_live_rep₂ hac.symm he
    obtain ⟨g1, g2, -, -⟩ := live_induce.1 ((live_rep hea hec).1 he)
    rw [rep_ends (by simpa using hea), rep_ends hea, ins_ends_inr,
      tau_int (hYs (Finset.mem_sdiff.1 g1).1), tau_int (hYs (Finset.mem_sdiff.1 g2).1)]
  · left
    rcases e' with e | f
    · exfalso
      have hn1 : (Sum.inl e : E ⊕ F) ≠ .inr a := by simp
      have hn2 : (Sum.inl e : E ⊕ F) ≠ .inr c := by simp
      obtain ⟨g1, -, -, -⟩ := live_induce.1 ((live_rep hn1 hn2).1 he')
      rw [ins_ends_inl] at g1
      simp at g1
    · by_cases hfa : f = a
      · subst hfa
        exact ⟨f, live_rep₁.2 ⟨hoa, hoc⟩, rfl⟩
      have hfc : f ≠ c := by
        rintro rfl
        exact not_live_rep₂ hac' he'
      obtain ⟨g1, g2, g3, g4⟩ := live_induce.1 ((live_rep (by simpa using hfa)
        (by simpa using hfc)).1 he')
      rw [ins_ends_inr, htYQ] at g1 g2
      exact ⟨f, (live_rep hfa hfc).2 (live_induce.2 ⟨g1, g2, g3, g4⟩), rfl⟩

/-- A present edge of `L` has an internal end. -/
private theorem Hyp.lend (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) {f : F}
    (hf : L.cls f ≠ none) : (L.ends f).1 ∈ L.int ∨ (L.ends f).2 ∈ L.int := by
  by_cases h0 : f = f₀
  · subst h0; rcases h.o₀ with h' | h' <;> rw [h'] <;> simp [h.hx₀]
  by_cases h1 : f = f₁
  · subst h1; rcases h.o₁ with h' | h' <;> rw [h'] <;> simp [h.hx₁]
  by_cases h2 : f = f₂
  · subst h2; rcases h.o₂ with h' | h' <;> rw [h'] <;> simp [h.hx₂]
  exact Or.inl (h.oth f h0 h1 h2 hf).1

/-- A live edge of the subgraph of the inserted graph induced on a set `Z` of vertices of `K` is
an edge of `K` other than `b` and `r`, live in the subgraph of `K` induced on `Z`. -/
private theorem Hyp.live_indK (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {Z : Finset (V ⊕ W)} (hZ : ∀ w, Sum.inr w ∉ Z) {x : E ⊕ F}
    (hx : Live ((K.insert L σ {b, r}).induce Z) x) :
    ∃ e, x = .inl e ∧ e ≠ b ∧ e ≠ r ∧ Live (K.induce Z.toLeft) e := by
  obtain ⟨g1, g2, g3, g4⟩ := live_induce.1 hx
  rcases x with e | f
  · rw [ins_cls_inl] at g3 g4
    rw [ins_ends_inl] at g1 g2
    have hbr : e ∉ ({b, r} : Finset E) := fun h' => g3 (by simp [h'])
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbr
    simp only [Finset.mem_insert, Finset.mem_singleton, hbr.1, hbr.2, or_self,
      ite_false] at g3 g4
    exact ⟨e, rfl, hbr.1, hbr.2, live_induce.2 ⟨by simpa using g1, by simpa using g2, g3, g4⟩⟩
  · exfalso
    rw [ins_cls_inr] at g3
    rw [ins_ends_inr] at g1 g2
    rcases h.lend g3 with h' | h'
    · rw [tau_int h'] at g1; exact hZ _ g1
    · rw [tau_int h'] at g2; exact hZ _ g2

omit [DecidableEq F] in
/-- An edge of `K` other than `b` and `r` has the same class in the subgraph of the inserted
graph induced on `Z` as in the subgraph of `K` induced on the vertices of `K` in `Z`. -/
private theorem cls_indK {Z : Finset (V ⊕ W)} {e : E} (hb : e ≠ b) (hr : e ≠ r) :
    ((K.insert L σ {b, r}).induce Z).cls (.inl e) = (K.induce Z.toLeft).cls e := by
  rw [ind_cls, ind_cls, ins_ends_inl, ins_cls_inl]
  simp [hb, hr]

/-- The edge `r` is never live in a subgraph of `K`. -/
private theorem Hyp.r_nl (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    (A : Finset V) : ¬ Live (K.induce A) r := by
  intro hl
  obtain ⟨-, -, g3, g4⟩ := live_induce.1 hl
  rcases h.k4 with h' | h'
  · exact g3 h'
  · exact g4 h'

/-- The edge `b` is not live in the subgraph of `K` induced on a set missing `u₀` or `u₁`. -/
private theorem Hyp.b_nl (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {A : Finset V} (hA : u₀ ∉ A ∨ u₁ ∉ A) : ¬ Live (K.induce A) b := by
  intro hl
  obtain ⟨g1, g2, g3, -⟩ := live_induce.1 hl
  rcases h.k3 with ⟨hb, -⟩ | ⟨-, hbe, -⟩
  · exact g3 hb
  · rw [hbe] at g1 g2
    rcases hA with hA | hA
    · exact hA g2
    · exact hA g1

/-- The replacement of a maximal isolated set `T' ⊔ L.int` of `T ⊔ L.int` in the inserted graph
is the replacement of `T'` in `K`. -/
private theorem Hyp.rel_replaceK (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {T T' : Finset V} (hT : K.IsoOrTop T) (hT' : K.IsProperIso T T') (hu₀ : u₀ ∈ T') {a c : E}
    (hac : a ≠ c) (ha : K.Crosses T' a) (hc : K.Crosses T' c) :
    Rel (K.replace T T' a c) ((K.insert L σ {b, r}).replace (T.disjSum L.int) (T'.disjSum L.int)
      (.inl a) (.inl c)) Sum.inl Sum.inl := by
  have hoa := MGraph.replace_ends _ _ K h.kspd.1 T T' a hT hT' ha
  have hoc := MGraph.replace_ends _ _ K h.kspd.1 T T' c hT hT' hc
  have hZ : ∀ w, (Sum.inr w : V ⊕ W) ∉ T.disjSum L.int \ T'.disjSum L.int := by simp
  have hZl : (T.disjSum L.int \ T'.disjSum L.int).toLeft = T \ T' := by
    rw [Finset.toLeft_sdiff, Finset.toLeft_disjSum, Finset.toLeft_disjSum]
  have hout : ∀ e, (K.insert L σ {b, r}).outer (T'.disjSum L.int) (.inl e) =
      .inl (K.outer T' e) := by
    intro e
    unfold MGraph.outer
    rw [ins_ends_inl]
    simp only [Finset.inl_mem_disjSum]
    split_ifs <;> rfl
  have hca : (Sum.inl c : E ⊕ F) ≠ .inl a := by simpa using hac.symm
  have hbT : u₀ ∉ T \ T' ∨ u₁ ∉ T \ T' := Or.inl (fun h' => (Finset.mem_sdiff.1 h').2 hu₀)
  refine ⟨fun v' => ?_, Sum.inl_injective, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · rcases v' with v | w <;> simp [MGraph.replace]
  · by_cases hea : e = a
    · subst hea
      rw [rep_cls₁, rep_cls₁]
    have hec : e ≠ c := by
      rintro rfl
      exact not_live_rep₂ hac.symm he
    have hl := (live_rep hea hec).1 he
    have heb : e ≠ b := fun h' => h.b_nl hbT (h' ▸ hl)
    have her : e ≠ r := fun h' => h.r_nl _ (h' ▸ hl)
    rw [rep_cls (by simpa using hea) (by simpa using hec), rep_cls hea hec, cls_indK heb her, hZl]
  · left
    by_cases hea : e = a
    · subst hea
      rw [rep_ends₁, rep_ends₁, hout, hout]
    have hec : e ≠ c := by
      rintro rfl
      exact not_live_rep₂ hac.symm he
    rw [rep_ends (by simpa using hea), rep_ends hea, ins_ends_inl]
  · left
    by_cases hea : e' = .inl a
    · subst hea
      exact ⟨a, live_rep₁.2 ⟨hoa, hoc⟩, rfl⟩
    have hec : e' ≠ .inl c := by
      rintro rfl
      exact not_live_rep₂ hca he'
    obtain ⟨e, rfl, -, -, hl⟩ := h.live_indK hZ ((live_rep hea hec).1 he')
    rw [hZl] at hl
    exact ⟨e, (live_rep (by simpa using hea) (by simpa using hec)).2 hl, rfl⟩

private theorem Hyp.outX₀ (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.insert L σ {b, r}).outer ((∅ : Finset V).disjSum L.int) (.inr f₀) = .inl u₀ := by
  unfold MGraph.outer
  rcases h.e₀ with e | e <;> rw [e] <;> simp [h.hx₀]

private theorem Hyp.outX₁ (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.insert L σ {b, r}).outer ((∅ : Finset V).disjSum L.int) (.inr f₁) = .inl u₁ := by
  unfold MGraph.outer
  rcases h.e₁ with e | e <;> rw [e] <;> simp [h.hx₁]

omit [DecidableEq E] [DecidableEq F] in
private theorem omega_sdiff (A : Finset V) :
    (A.disjSum L.int \ (∅ : Finset V).disjSum L.int).toLeft = A := by
  rw [Finset.toLeft_sdiff, Finset.toLeft_disjSum, Finset.toLeft_disjSum, Finset.sdiff_empty]

omit [DecidableEq E] [DecidableEq F] in
private theorem omega_inr (A : Finset V) (w : W) :
    (Sum.inr w : V ⊕ W) ∉ A.disjSum L.int \ (∅ : Finset V).disjSum L.int := by
  simp

/-- Case B of [II, Lemma 6.5 (2)]: the replacement of the internal vertices of `L` in the
minimal isolated subset of `K` together with them is the subgraph of `K` induced on its minimal
isolated subset, with `b` changed into a `Θ` edge. -/
private theorem Hyp.rel_omegaB (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    (hb : K.cls b = some .plus) (hbe : K.ends b = (u₁, u₀)) {a c : F}
    (hac : (a = f₀ ∧ c = f₁) ∨ (a = f₁ ∧ c = f₀)) :
    Rel ((K.induce K.MIS).convert [b]) ((K.insert L σ {b, r}).replace (K.MIS.disjSum L.int)
      ((∅ : Finset V).disjSum L.int) (.inr a) (.inr c)) Sum.inl
      (fun e => if e = b then .inr a else .inl e) := by
  have hac' : a ≠ c := by
    rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h.f01, h.f01.symm]
  have hbl : Live (K.induce K.MIS) b := live_induce.2 ⟨by rw [hbe]; exact h.mis₁,
    by rw [hbe]; exact h.mis₀, by rw [hb]; simp, by rw [hb]; simp⟩
  have hcvb : ((K.induce K.MIS).convert [b]).cls b = some .diff := by
    have : (K.induce K.MIS).cls b = some .plus := by
      rw [ind_cls, hbe]
      simp [h.mis₀, h.mis₁, hb]
    change (if b ∈ [b] ∧ (K.induce K.MIS).cls b = some .plus then some MClass.diff
      else (K.induce K.MIS).cls b) = _
    rw [this]
    simp
  have hcv : ∀ e, e ≠ b → ((K.induce K.MIS).convert [b]).cls e = (K.induce K.MIS).cls e := by
    intro e he
    simp [MGraph.convert, he]
  refine ⟨fun v' => ?_, fun e e' hee => ?_, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · rcases v' with v | w <;> simp [MGraph.replace, MGraph.convert, MGraph.induce]
  · by_cases h1 : e = b <;> by_cases h2 : e' = b <;> simp_all
  · by_cases heb : e = b
    · subst heb
      simp only [ite_true]
      rw [rep_cls₁, hcvb]
    · simp only [heb, ite_false]
      have hl := live_convert.1 he
      have her : e ≠ r := fun h' => h.r_nl _ (h' ▸ hl)
      rw [rep_cls (by simp) (by simp), cls_indK heb her, omega_sdiff, hcv e heb]
  · by_cases heb : e = b
    · subst heb
      simp only [ite_true]
      rw [rep_ends₁]
      change _ = (Sum.inl (K.ends e).1, Sum.inl (K.ends e).2) ∨
        _ = (Sum.inl (K.ends e).2, Sum.inl (K.ends e).1)
      rw [hbe]
      rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right
        rw [h.outX₀, h.outX₁]
      · left
        rw [h.outX₁, h.outX₀]
    · simp only [heb, ite_false]
      left
      rw [rep_ends (by simp), ins_ends_inl]
      rfl
  · left
    by_cases hea : e' = .inr a
    · subst hea
      exact ⟨b, live_convert.2 hbl, by simp⟩
    have hec : e' ≠ .inr c := by
      rintro rfl
      exact not_live_rep₂ (by simpa using hac'.symm) he'
    obtain ⟨e, rfl, heb, -, hl⟩ := h.live_indK (omega_inr _) ((live_rep hea hec).1 he')
    rw [omega_sdiff] at hl
    exact ⟨e, live_convert.2 hl, by simp [heb]⟩

/-- Case A of [II, Lemma 6.5 (2)]: the replacement of the internal vertices of `L` in the
minimal isolated subset of `K` together with them is the subgraph of `K` induced on its minimal
isolated subset, with a `Θ` loop at `u₀`. -/
private theorem Hyp.rel_omegaA (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    (hb : K.cls b = none) (hu : u₀ = u₁) {a c : F}
    (hac : (a = f₀ ∧ c = f₁) ∨ (a = f₁ ∧ c = f₀)) :
    Rel (K.induce K.MIS) ((K.insert L σ {b, r}).replace (K.MIS.disjSum L.int)
      ((∅ : Finset V).disjSum L.int) (.inr a) (.inr c)) Sum.inl Sum.inl := by
  have hac' : a ≠ c := by
    rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h.f01, h.f01.symm]
  refine ⟨fun v' => ?_, Sum.inl_injective, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · rcases v' with v | w <;> simp [MGraph.replace, MGraph.induce]
  · have heb : e ≠ b := fun h' => (live_induce.1 (h' ▸ he)).2.2.1 hb
    have her : e ≠ r := fun h' => h.r_nl _ (h' ▸ he)
    rw [rep_cls (by simp) (by simp), cls_indK heb her, omega_sdiff]
  · left
    rw [rep_ends (by simp), ins_ends_inl]
    rfl
  · by_cases hea : e' = .inr a
    · subst hea
      right
      refine ⟨?_, rep_cls₁⟩
      rw [rep_ends₁]
      rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h.outX₀, h.outX₁, hu]
      · rw [h.outX₁, h.outX₀, hu]
    left
    have hec : e' ≠ .inr c := by
      rintro rfl
      exact not_live_rep₂ (by simpa using hac'.symm) he'
    obtain ⟨e, rfl, -, -, hl⟩ := h.live_indK (omega_inr _) ((live_rep hea hec).1 he')
    rw [omega_sdiff] at hl
    exact ⟨e, hl, rfl⟩

/-! ## The inserted graph is sequentially pre-deterministic -/

/-- [II, Def 5.9 (iii)] for the minimal isolated subset of the inserted graph: it is a minimal
isolated subset of `L`. -/
private theorem Hyp.clauseA (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    ∀ S, (K.insert L σ {b, r}).IsoOrTop S → (∀ Q, ¬ (K.insert L σ {b, r}).IsProperIso S Q) →
      ((K.insert L σ {b, r}).induce S).PreDet := by
  intro S hS hmin
  obtain ⟨T, Y, rfl⟩ := exists_disjSum S
  rcases hS with hS | hS
  · exfalso
    apply hmin ((∅ : Finset V).disjSum L.int)
    refine ⟨h.x_iso, ?_⟩
    rw [hS, ins_int]
    exact x_ssub h.hu₀ subset_rfl
  rcases (h.iso_iff T Y).1 hS with ⟨rfl, hu₀, -, -⟩ | ⟨rfl, hYi⟩
  · exact absurd ⟨h.x_iso, x_ssub hu₀ subset_rfl⟩ (hmin _)
  · have hLmin : ∀ Q, ¬ L.IsProperIso Y Q := fun Q hQ =>
      hmin ((∅ : Finset V).disjSum Q) ⟨(h.iso_iff ∅ Q).2 (Or.inr ⟨rfl, hQ.1⟩),
        Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset subset_rfl hQ.2⟩
    exact (rel_induceL hYi.1).preDet (h.lspd.2.2.1 Y (Or.inr hYi) hLmin)

/-- [II, Def 5.9 (iii)] for a proper isolated subset of `L` inside an isolated subset of `L`. -/
private theorem Hyp.replace_second (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {Y : Finset W} (hYi : L.IsIsolated Y) {P : Finset (V ⊕ W)} {e₁ e₂ : E ⊕ F}
    (hPm : (K.insert L σ {b, r}).IsMaximalIso ((∅ : Finset V).disjSum Y) P) (hne : e₁ ≠ e₂)
    (he₁ : (K.insert L σ {b, r}).Crosses P e₁) (he₂ : (K.insert L σ {b, r}).Crosses P e₂) :
    ((K.insert L σ {b, r}).replace ((∅ : Finset V).disjSum Y) P e₁ e₂).PreDet := by
  obtain ⟨T', Y', rfl⟩ := exists_disjSum P
  obtain ⟨⟨hPi, hPs⟩, hPmax⟩ := hPm
  rw [disjSum_ssub] at hPs
  have hT' : T' = ∅ := Finset.subset_empty.1 hPs.1.1
  subst hT'
  have hY'Y : Y' ⊂ Y := Finset.ssubset_def.2 ⟨hPs.1.2, fun h' => hPs.2 ⟨subset_rfl, h'⟩⟩
  rcases (h.iso_iff ∅ Y').1 hPi with ⟨-, hu₀, -, -⟩ | ⟨-, hY'i⟩
  · simp at hu₀
  have hmax : L.IsMaximalIso Y Y' := ⟨⟨hY'i, hY'Y⟩, fun Q hQ hlt =>
    hPmax ((∅ : Finset V).disjSum Q) ⟨(h.iso_iff ∅ Q).2 (Or.inr ⟨rfl, hQ.1⟩),
      Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset subset_rfl hQ.2⟩
      (Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset subset_rfl hlt)⟩
  obtain ⟨a, rfl, ha⟩ := (h.crossSecond hY'i.1 e₁).1 he₁
  obtain ⟨c, rfl, hc⟩ := (h.crossSecond hY'i.1 e₂).1 he₂
  have hac : a ≠ c := fun h' => hne (h' ▸ rfl)
  exact (h.rel_replaceL (Or.inr hYi) hYi.1 ⟨hY'i, hY'Y⟩ hac ha hc).preDet
    (h.lspd.2.2.2 Y Y' a c (Or.inr hYi) hmax hac ha hc)

/-- [II, Def 5.9 (iii)] for `T ⊔ L.int`, with `T` the set of internal vertices of `K` or an
isolated subset of `K` containing `u₀` and `u₁`: the replacement of `T' ⊔ L.int` for the maximal
isolated subset `T'` of `T`, and, for `T` the minimal isolated subset of `K`, the replacement of
the internal vertices of `L` (Cases A and B of [II, Lemma 6.5 (2)]). -/
private theorem Hyp.replace_first (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    {T : Finset V} (hT : K.IsoOrTop T) (hTs : T ⊆ K.int) (hu₀ : u₀ ∈ T) {P : Finset (V ⊕ W)}
    {e₁ e₂ : E ⊕ F} (hPm : (K.insert L σ {b, r}).IsMaximalIso (T.disjSum L.int) P)
    (hne : e₁ ≠ e₂) (he₁ : (K.insert L σ {b, r}).Crosses P e₁)
    (he₂ : (K.insert L σ {b, r}).Crosses P e₂) :
    ((K.insert L σ {b, r}).replace (T.disjSum L.int) P e₁ e₂).PreDet := by
  obtain ⟨T', Y', rfl⟩ := exists_disjSum P
  obtain ⟨⟨hPi, hPs⟩, hPmax⟩ := hPm
  have hlift : ∀ Q, K.IsProperIso T Q →
      (K.insert L σ {b, r}).IsProperIso (T.disjSum L.int) (Q.disjSum L.int) ∧ u₀ ∈ Q := by
    intro Q hQ
    have hQK : K.IsProperIso K.int Q := ⟨hQ.1, Finset.ssubset_of_ssubset_of_subset hQ.2 hTs⟩
    exact ⟨⟨(h.iso_iff Q L.int).2 (Or.inl ⟨rfl, h.m₀ Q hQK, h.m₁ Q hQK, hQ.1⟩),
      Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset hQ.2 subset_rfl⟩, h.m₀ Q hQK⟩
  by_cases hex : ∃ Q, K.IsProperIso T Q
  · obtain ⟨Q, hQ⟩ := hex
    rcases (h.iso_iff T' Y').1 hPi with ⟨rfl, hu₀', hu₁', hT'i⟩ | ⟨rfl, hY'i⟩
    · rw [disjSum_ssub] at hPs
      have hT'T : T' ⊂ T := Finset.ssubset_def.2 ⟨hPs.1.1, fun h' => hPs.2 ⟨h', subset_rfl⟩⟩
      have hmax : K.IsMaximalIso T T' := ⟨⟨hT'i, hT'T⟩, fun Q' hQ' hlt => hPmax _ (hlift Q' hQ').1
        (Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset hlt subset_rfl)⟩
      obtain ⟨a, rfl, ha⟩ := (h.crossFirst hu₀' hu₁' e₁).1 he₁
      obtain ⟨c, rfl, hc⟩ := (h.crossFirst hu₀' hu₁' e₂).1 he₂
      have hac : a ≠ c := fun h' => hne (h' ▸ rfl)
      exact (h.rel_replaceK hT ⟨hT'i, hT'T⟩ hu₀' hac ha hc).preDet
        (h.kspd.2.2.2 T T' a c hT hmax hac ha hc)
    · exfalso
      obtain ⟨hQg, hq₀⟩ := hlift Q hQ
      exact hPmax _ hQg (x_ssub hq₀ hY'i.1)
  · push Not at hex
    have hTΩ : T = K.MIS := (MGraph.MIS_spec _ _ K h.kspd.2.1).2.2 T hT hex
    rcases (h.iso_iff T' Y').1 hPi with ⟨rfl, -, -, hT'i⟩ | ⟨rfl, hY'i⟩
    · exfalso
      rw [disjSum_ssub] at hPs
      exact hex T' ⟨hT'i, Finset.ssubset_def.2 ⟨hPs.1.1, fun h' => hPs.2 ⟨h', subset_rfl⟩⟩⟩
    have hY' : Y' = L.int := by
      by_contra hY'
      exact hPmax _ ⟨h.x_iso, x_ssub hu₀ subset_rfl⟩
        (Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset subset_rfl
          (Finset.ssubset_iff_subset_ne.2 ⟨hY'i.1, hY'⟩))
    subst hY'
    have hXc : ∀ x, (K.insert L σ {b, r}).Crosses ((∅ : Finset V).disjSum L.int) x →
        x = .inr f₀ ∨ x = .inr f₁ := by
      intro x hx
      obtain ⟨f, rfl, hf⟩ := (h.crossSecond subset_rfl x).1 hx
      by_contra hn
      push Not at hn
      exact h.lncr_int (by simpa using hn.1) (by simpa using hn.2) hf
    obtain ⟨a, c, rfl, rfl, hac⟩ : ∃ a c, e₁ = .inr a ∧ e₂ = .inr c ∧
        ((a = f₀ ∧ c = f₁) ∨ (a = f₁ ∧ c = f₀)) := by
      rcases hXc e₁ he₁ with rfl | rfl <;> rcases hXc e₂ he₂ with rfl | rfl
      · exact absurd rfl hne
      · exact ⟨f₀, f₁, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨f₁, f₀, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
      · exact absurd rfl hne
    subst hTΩ
    rcases h.k3 with ⟨hb, hu⟩ | ⟨hb, hbe, l, hl, hlh⟩
    · exact (h.rel_omegaA hb hu hac).preDet (h.kspd.2.2.1 K.MIS hT hex)
    · exact (h.rel_omegaB hb hbe hac).preDet (preDet_convert_head hl hlh)

/-- [II, Def 5.9 (iii)] for the replacements in the inserted graph. -/
private theorem Hyp.clauseB (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    ∀ S P e₁ e₂, (K.insert L σ {b, r}).IsoOrTop S → (K.insert L σ {b, r}).IsMaximalIso S P →
      e₁ ≠ e₂ → (K.insert L σ {b, r}).Crosses P e₁ → (K.insert L σ {b, r}).Crosses P e₂ →
        ((K.insert L σ {b, r}).replace S P e₁ e₂).PreDet := by
  intro S P e₁ e₂ hS hPm hne he₁ he₂
  obtain ⟨T, Y, rfl⟩ := exists_disjSum S
  have hS' : (Y = L.int ∧ K.IsoOrTop T ∧ u₀ ∈ T ∧ T ⊆ K.int) ∨ (T = ∅ ∧ L.IsIsolated Y) := by
    rcases hS with hS | hS
    · rw [ins_int, Finset.disjSum_inj] at hS
      obtain ⟨rfl, rfl⟩ := hS
      exact Or.inl ⟨rfl, Or.inl rfl, h.hu₀, subset_rfl⟩
    · rcases (h.iso_iff T Y).1 hS with ⟨rfl, hu₀, -, hTi⟩ | hr
      · exact Or.inl ⟨rfl, Or.inr hTi, hu₀, hTi.1⟩
      · exact Or.inr hr
  rcases hS' with ⟨rfl, hT, hu₀, hTs⟩ | ⟨rfl, hYi⟩
  · exact h.replace_first hT hTs hu₀ hPm hne he₁ he₂
  · exact h.replace_second hYi hPm hne he₁ he₂

/-- **[II, Lemma 6.5 (2)]**: the inserted graph is sequentially pre-deterministic. -/
private theorem Hyp.spd (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂) :
    (K.insert L σ {b, r}).SPD :=
  ⟨h.dc, h.chain, h.clauseA, h.clauseB⟩

/-- The proper isolated subsets of the inserted graph other than the internal vertices of `L`
are weakly isolated when `K` and `L` are globally standard and `r` joins `u₂` to `u₀`
([II, Lemma 6.5 (2)], [II, Def 6.1]). -/
private theorem Hyp.weak (h : Hyp K L σ u₀ u₁ u₂ b r f₀ f₁ f₂ w₀ w₁ w₂ x₀ x₁ x₂)
    (hu₂ : u₂ ∈ K.int) (hKg : K.GloballyStandard) (hLg : L.GloballyStandard)
    (hre : K.ends r = (u₂, u₀)) (P : Finset (V ⊕ W))
    (hP : (K.insert L σ {b, r}).IsProperIso (K.insert L σ {b, r}).int P)
    (hPX : P ≠ (∅ : Finset V).disjSum L.int) : (K.insert L σ {b, r}).IsWeaklyIso P := by
  obtain ⟨T, Y, rfl⟩ := exists_disjSum P
  have hPs := hP.2
  rw [ins_int, disjSum_ssub] at hPs
  refine ⟨hP.1, ?_⟩
  rcases (h.iso_iff T Y).1 hP.1 with ⟨rfl, hu₀', -, hTi⟩ | ⟨rfl, hYi⟩
  · have hTp : K.IsProperIso K.int T :=
      ⟨hTi, Finset.ssubset_def.2 ⟨hPs.1.1, fun h' => hPs.2 ⟨h', subset_rfl⟩⟩⟩
    obtain ⟨-, e, e', hee, he, he'⟩ := hKg.2 T hTp
    have lift : ∀ x, K.RedCrosses T x → x ≠ r →
        (K.insert L σ {b, r}).RedCrosses (T.disjSum L.int) (.inl x) := by
      intro x hx hxr
      have hxb : x ≠ b := by
        rintro rfl
        have hm := hx.1
        rcases h.k3 with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] at hm <;> simp at hm
      exact (red_inl x T L.int).2 ⟨by simp [hxb, hxr], hx⟩
    have hf₂ : K.RedCrosses T r → (K.insert L σ {b, r}).RedCrosses (T.disjSum L.int) (.inr f₂) := by
      intro hr
      have hcut := hr.2.2.2
      rw [cut_of_ends (Or.inl hre)] at hcut
      rw [red_att hu₂ h.hx₂ h.c₂ h.e₂]
      exact iff_of_false (fun h' => hcut.1 h' hu₀') (fun h' => h' h.hx₂)
    by_cases her : e = r
    · subst her
      exact ⟨.inr f₂, .inl e', by simp, hf₂ he, lift e' he' (Ne.symm hee)⟩
    by_cases her' : e' = r
    · subst her'
      exact ⟨.inl e, .inr f₂, by simp, lift e he her, hf₂ he'⟩
    exact ⟨.inl e, .inl e', by simpa using hee, lift e he her, lift e' he' her'⟩
  · have hY : Y ≠ L.int := fun h' => hPX (by rw [h'])
    obtain ⟨-, f, f', hff, hf, hf'⟩ := hLg.2 Y ⟨hYi, Finset.ssubset_iff_subset_ne.2 ⟨hYi.1, hY⟩⟩
    have lift : ∀ g, L.RedCrosses Y g →
        (K.insert L σ {b, r}).RedCrosses ((∅ : Finset V).disjSum Y) (.inr g) := by
      intro g hg
      by_cases h2 : g = f₂
      · subst h2
        rw [red_att hu₂ h.hx₂ h.c₂ h.e₂]
        rw [lred_att h.ldis h.hw₂ h.hx₂ h.c₂ h.o₂ hYi.1] at hg
        simp [hg]
      have h0 : g ≠ f₀ := by
        rintro rfl
        have hm := hg.1
        rw [h.c₀] at hm
        simp at hm
      have h1 : g ≠ f₁ := by
        rintro rfl
        have hm := hg.1
        rcases h.c₁ with h' | h' <;> rw [h'] at hm <;> simp at hm
      exact (red_int (h.oth g h0 h1 h2) ∅ Y).2 hg
    exact ⟨.inr f, .inr f', by simpa using hff, lift f hf, lift f' hf'⟩

end Glue

/-! ## [II, Lemma 6.5 (2)] -/

/-- **[II, Lemma 6.5 (2)]**, picture (6.5) (b) and chain (6.6): the graph `L` inserted into `K`
at `u₀`, `u₁`, `u₂` with the edges `b` and `r` of `K` removed is sequentially
pre-deterministic ([II, Def 5.9]). Hypotheses on `K`: (K1) `K` is sequentially pre-deterministic,
has no ghost edge, and its internal and external vertices are distinct; (K2) `u₀`, `u₁`, `u₂` are
internal and `u₀`, `u₁` lie in the minimal isolated subset; (K3) either `b` is absent and
`u₀ = u₁` (Case A), or `b` is a blue solid edge from `u₁` to `u₀` heading a pre-deterministic
order of the subgraph induced on the minimal isolated subset (Case B); (K4) `r` is absent or red
solid; (K5) some edge between an internal and an external vertex is neither absent nor red.
Hypotheses on `L`: (L1) `L` is sequentially pre-deterministic, has no ghost edge, and its
internal and external vertices are distinct; (L2) three distinct edges `f₀` (diffusive), `f₁`
(blue solid or diffusive) and `f₂` (red solid) join three distinct external vertices `w₀`, `w₁`,
`w₂` with `σ wᵢ = uᵢ` to internal vertices, and every other present edge joins two internal
vertices. -/
theorem MGraph.spd_insert :
  ∀ (V W E F : Type) [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
    (K : MGraph V E) (L : MGraph W F) (σ : W → V) (u₀ u₁ u₂ : V) (b r : E),
    K.SPD → (∀ e, K.cls e ≠ some .ghost) → Disjoint K.int K.ext →
    u₀ ∈ K.int → u₁ ∈ K.int → u₂ ∈ K.int → u₀ ∈ K.MIS → u₁ ∈ K.MIS →
    ((K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b)) →
    (K.cls r = none ∨ K.cls r = some .minus) →
    (∃ e, K.cls e ≠ none ∧ K.cls e ≠ some .minus ∧
      (((K.ends e).1 ∈ K.int ∧ (K.ends e).2 ∈ K.ext) ∨
        ((K.ends e).1 ∈ K.ext ∧ (K.ends e).2 ∈ K.int))) →
    L.SPD → (∀ f, L.cls f ≠ some .ghost) → Disjoint L.int L.ext →
    (∃ (f₀ f₁ f₂ : F) (w₀ w₁ w₂ : W), f₀ ≠ f₁ ∧ f₀ ≠ f₂ ∧ f₁ ≠ f₂ ∧
      w₀ ∈ L.ext ∧ w₁ ∈ L.ext ∧ w₂ ∈ L.ext ∧ w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧
      σ w₀ = u₀ ∧ σ w₁ = u₁ ∧ σ w₂ = u₂ ∧
      (∃ x ∈ L.int, L.ends f₀ = (w₀, x) ∨ L.ends f₀ = (x, w₀)) ∧
      (∃ x ∈ L.int, L.ends f₁ = (w₁, x) ∨ L.ends f₁ = (x, w₁)) ∧
      (∃ x ∈ L.int, L.ends f₂ = (w₂, x) ∨ L.ends f₂ = (x, w₂)) ∧
      L.cls f₀ = some .diff ∧ (L.cls f₁ = some .plus ∨ L.cls f₁ = some .diff) ∧
      L.cls f₂ = some .minus ∧
      ∀ f, f ≠ f₀ → f ≠ f₁ → f ≠ f₂ → L.cls f ≠ none →
        (L.ends f).1 ∈ L.int ∧ (L.ends f).2 ∈ L.int) →
    (K.insert L σ {b, r}).SPD := by
  intro V W E F _ _ _ _ K L σ u₀ u₁ u₂ b r hK _ hKd hu₀ hu₁ _ hm₀ hm₁ hK3 hK4 hK5 hL _ hLd hL2
  obtain ⟨f₀, f₁, f₂, w₀, w₁, w₂, h01, h02, h12, hw₀, hw₁, hw₂, -, -, -, hσ₀, hσ₁, hσ₂,
    ⟨x₀, hx₀, ho₀⟩, ⟨x₁, hx₁, ho₁⟩, ⟨x₂, hx₂, ho₂⟩, hc₀, hc₁, hc₂, hoth⟩ := hL2
  exact (Hyp.mk hK hKd hu₀ hu₁ hm₀ hm₁ hK3 hK4 hK5 hL hLd h01 h02 h12 hw₀ hw₁ hw₂ hσ₀ hσ₁ hσ₂
    hx₀ hx₁ hx₂ ho₀ ho₁ ho₂ hc₀ hc₁ hc₂ hoth).spd

/-- **[II, Lemma 6.5 (2)]**, weak isolation in the chain (6.6): under the hypotheses of
`MGraph.spd_insert`, when `K` and `L` are globally standard ([II, Def 6.2]) and `r` joins `u₂`
to `u₀` (red solid, or with `u₂ = u₀`), every proper isolated subset of the inserted graph other
than the set of internal vertices of `L` is weakly isolated ([II, Def 6.1]). -/
theorem MGraph.insert_weakIso :
  ∀ (V W E F : Type) [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
    (K : MGraph V E) (L : MGraph W F) (σ : W → V) (u₀ u₁ u₂ : V) (b r : E),
    K.SPD → (∀ e, K.cls e ≠ some .ghost) → Disjoint K.int K.ext →
    u₀ ∈ K.int → u₁ ∈ K.int → u₂ ∈ K.int → u₀ ∈ K.MIS → u₁ ∈ K.MIS →
    ((K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b)) →
    (K.cls r = none ∨ K.cls r = some .minus) →
    (∃ e, K.cls e ≠ none ∧ K.cls e ≠ some .minus ∧
      (((K.ends e).1 ∈ K.int ∧ (K.ends e).2 ∈ K.ext) ∨
        ((K.ends e).1 ∈ K.ext ∧ (K.ends e).2 ∈ K.int))) →
    L.SPD → (∀ f, L.cls f ≠ some .ghost) → Disjoint L.int L.ext →
    (∃ (f₀ f₁ f₂ : F) (w₀ w₁ w₂ : W), f₀ ≠ f₁ ∧ f₀ ≠ f₂ ∧ f₁ ≠ f₂ ∧
      w₀ ∈ L.ext ∧ w₁ ∈ L.ext ∧ w₂ ∈ L.ext ∧ w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧
      σ w₀ = u₀ ∧ σ w₁ = u₁ ∧ σ w₂ = u₂ ∧
      (∃ x ∈ L.int, L.ends f₀ = (w₀, x) ∨ L.ends f₀ = (x, w₀)) ∧
      (∃ x ∈ L.int, L.ends f₁ = (w₁, x) ∨ L.ends f₁ = (x, w₁)) ∧
      (∃ x ∈ L.int, L.ends f₂ = (w₂, x) ∨ L.ends f₂ = (x, w₂)) ∧
      L.cls f₀ = some .diff ∧ (L.cls f₁ = some .plus ∨ L.cls f₁ = some .diff) ∧
      L.cls f₂ = some .minus ∧
      ∀ f, f ≠ f₀ → f ≠ f₁ → f ≠ f₂ → L.cls f ≠ none →
        (L.ends f).1 ∈ L.int ∧ (L.ends f).2 ∈ L.int) →
    K.GloballyStandard → L.GloballyStandard →
    (K.ends r = (u₂, u₀) ∧ (K.cls r = some .minus ∨ u₂ = u₀)) →
    ∀ P, (K.insert L σ {b, r}).IsProperIso (K.insert L σ {b, r}).int P →
      P ≠ (∅ : Finset V).disjSum L.int → (K.insert L σ {b, r}).IsWeaklyIso P := by
  intro V W E F _ _ _ _ K L σ u₀ u₁ u₂ b r hK _ hKd hu₀ hu₁ hu₂ hm₀ hm₁ hK3 hK4 hK5 hL _ hLd hL2
    hKg hLg hr
  obtain ⟨f₀, f₁, f₂, w₀, w₁, w₂, h01, h02, h12, hw₀, hw₁, hw₂, -, -, -, hσ₀, hσ₁, hσ₂,
    ⟨x₀, hx₀, ho₀⟩, ⟨x₁, hx₁, ho₁⟩, ⟨x₂, hx₂, ho₂⟩, hc₀, hc₁, hc₂, hoth⟩ := hL2
  exact (Hyp.mk hK hKd hu₀ hu₁ hm₀ hm₁ hK3 hK4 hK5 hL hLd h01 h02 h12 hw₀ hw₁ hw₂ hσ₀ hσ₁ hσ₂
    hx₀ hx₁ hx₂ ho₀ ho₁ ho₂ hc₀ hc₁ hc₂ hoth).weak hu₂ hKg hLg hr.1

/-! ## Merging molecules by an idempotent map -/

section Merge

variable [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
private theorem mapV_mapV (G : MGraph V E) (f g : V → V) :
    (G.mapV f).mapV g = G.mapV (g ∘ f) :=
  MolInsert_ext (by simp [MGraph.mapV, Finset.image_image])
    (by simp [MGraph.mapV, Finset.image_image]) rfl rfl

/-- The vertices of `D` identified with their images under the idempotent map `π`, one at a time
by operation (A) of [II, §5.4]: the graph stays sequentially pre-deterministic. -/
private theorem spd_mapV_finset (G : MGraph V E) (π : V → V) (hidem : ∀ v, π (π v) = π v)
    (hint : ∀ v ∈ G.int, π v ∈ G.int) (hs : G.SPD) (hng : ∀ e, G.cls e ≠ some .ghost)
    (D : Finset V) (hD : ∀ v ∈ D, v ∈ G.int ∧ π v ≠ v) :
    (G.mapV fun v => if v ∈ D then π v else v).SPD := by
  induction D using Finset.induction_on with
  | empty =>
    have : (G.mapV fun v => if v ∈ (∅ : Finset V) then π v else v) = G :=
      MolInsert_ext (by simp [MGraph.mapV]) (by simp [MGraph.mapV]) rfl rfl
    rw [this]
    exact hs
  | insert d D hd ih =>
    have ih' := ih (fun v hv => hD v (Finset.mem_insert_of_mem hv))
    have hd' := hD d (Finset.mem_insert_self d D)
    have heq : (G.mapV fun v => if v ∈ insert d D then π v else v) =
        (G.mapV fun v => if v ∈ D then π v else v).merge (π d) d := by
      unfold MGraph.merge
      rw [mapV_mapV]
      congr 1
      funext v
      simp only [Function.comp, Finset.mem_insert]
      by_cases hv : v = d
      · subst hv
        simp [hd]
      · by_cases hvD : v ∈ D
        · have hpv : π v ≠ d := by
            intro h'
            apply hd'.2
            rw [← h', hidem]
          simp [hv, hvD, hpv]
        · simp [hv, hvD]
    rw [heq]
    refine MGraph.spd_merge _ _ _ _ _ (fun e => hng e) ih' ?_ ?_
    · refine Finset.mem_image.2 ⟨π d, hint d hd'.1, ?_⟩
      by_cases h' : π d ∈ D <;> simp [h', hidem]
    · exact Finset.mem_image.2 ⟨d, hd'.1, by simp [hd]⟩

/-- Removing all loops keeps the sequentially pre-deterministic property: the loops are removed
one at a time. -/
private theorem spd_unloop_all [Finite E] (G : MGraph V E) (hs : G.SPD) : G.unloop.SPD := by
  have := Fintype.ofFinite E
  have key : ∀ D : Finset E, ({ G with cls := fun e =>
      if e ∈ D ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } : MGraph V E).SPD := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      have : ({ G with cls := fun e =>
          if e ∈ (∅ : Finset E) ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } :
            MGraph V E) = G :=
        MolInsert_ext rfl rfl rfl (funext fun e => by simp)
      rw [this]
      exact hs
    | insert d D hd ih =>
      by_cases hl : (G.ends d).1 = (G.ends d).2
      · have : ({ G with cls := fun e =>
            if e ∈ insert d D ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } :
              MGraph V E) = MGraph.erase { G with cls := fun e =>
            if e ∈ D ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } d := by
          refine MolInsert_ext rfl rfl rfl (funext fun e => ?_)
          simp only [MGraph.erase, Finset.mem_insert]
          by_cases hed : e = d
          · subst hed
            simp [hl]
          · simp [hed]
        rw [this]
        exact (MGraph.spd_unloop _ _ { G with cls := fun e =>
            if e ∈ D ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } d hl).2 ih
      · have : ({ G with cls := fun e =>
            if e ∈ insert d D ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } :
              MGraph V E) = { G with cls := fun e =>
            if e ∈ D ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } := by
          refine MolInsert_ext rfl rfl rfl (funext fun e => ?_)
          simp only [Finset.mem_insert]
          by_cases hed : e = d
          · subst hed
            simp [hl]
          · simp [hed]
        rw [this]
        exact ih
  have h' := key Finset.univ
  have : G.unloop = { G with cls := fun e =>
      if e ∈ (Finset.univ : Finset E) ∧ (G.ends e).1 = (G.ends e).2 then none else G.cls e } :=
    MolInsert_ext rfl rfl rfl (funext fun e => by simp [MGraph.unloop])
  rw [this]
  exact h'

end Merge

/-- **Merging molecules** ([II, §5.4], operation (A) applied to several pairs of molecules, and the
removal of the loops it creates): for an idempotent map `π` of the vertices sending internal
vertices to internal vertices and fixing the external ones, a sequentially pre-deterministic graph
without ghost edges ([II, Def 5.9]), whose internal and external vertices are distinct and whose
present edges join vertices, stays sequentially pre-deterministic when its vertices are mapped by
`π` and its loops are removed. -/
theorem MGraph.spd_mapV_merge :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] [Finite E] (G : MGraph V E) (π : V → V),
    (∀ v, π (π v) = π v) → (∀ v ∈ G.int, π v ∈ G.int) → (∀ v ∈ G.ext, π v = v) →
    (∀ v ∈ G.int, π v ∉ G.ext) → G.SPD → (∀ e, G.cls e ≠ some .ghost) →
    Disjoint G.int G.ext →
    (∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) →
    ((G.mapV π).unloop).SPD := by
  intro V E _ _ _ G π hidem hint hext _ hs hng hd hR2
  set π' : V → V := fun v => if v ∈ G.int then π v else v with hπ'
  have hagree : ∀ v, G.IsVtx v → π' v = π v := by
    intro v hv
    rcases hv with hv | hv
    · simp [hπ', hv]
    · have hv' : v ∉ G.int := fun h' => Finset.disjoint_left.1 hd h' hv
      simp [hπ', hv', hext v hv]
  have hπD : π' = fun v => if v ∈ G.int.filter (fun v => π v ≠ v) then π v else v := by
    funext v
    by_cases hv : v ∈ G.int <;> by_cases hpv : π v = v <;> simp [hπ', hv, hpv]
  have h1 : (G.mapV π').SPD := by
    rw [hπD]
    exact spd_mapV_finset G π hidem hint hs hng _ (fun v hv => by simpa using hv)
  have h2 : ((G.mapV π').unloop).SPD := spd_unloop_all _ h1
  have hcls : ∀ e, G.cls e ≠ none →
      ((G.mapV π').unloop).cls e = ((G.mapV π).unloop).cls e := by
    intro e he
    obtain ⟨v1, v2⟩ := hR2 e he
    change (if π' (G.ends e).1 = π' (G.ends e).2 then none else G.cls e) =
      (if π (G.ends e).1 = π (G.ends e).2 then none else G.cls e)
    rw [hagree _ v1, hagree _ v2]
  have hGc : ∀ e, ((G.mapV π').unloop).cls e ≠ none → G.cls e ≠ none := by
    intro e he h'
    apply he
    change (if π' (G.ends e).1 = π' (G.ends e).2 then none else G.cls e) = none
    simp [h']
  have hGc' : ∀ e, ((G.mapV π).unloop).cls e ≠ none → G.cls e ≠ none := by
    intro e he h'
    apply he
    change (if π (G.ends e).1 = π (G.ends e).2 then none else G.cls e) = none
    simp [h']
  have himg : ∀ v, G.IsVtx v → ((G.mapV π').unloop).IsVtx (π' v) := by
    intro v hv
    rcases hv with hv | hv
    · exact Or.inl (Finset.mem_image_of_mem _ hv)
    · exact Or.inr (Finset.mem_image_of_mem _ hv)
  refine (MGraph.spd_transport _ _ _ _ ((G.mapV π').unloop) ((G.mapV π).unloop)
    ⟨id, id, fun _ _ _ _ h' => h', Set.injOn_id _, ?_, ?_, fun e he => ?_, fun e he => ?_,
      fun e he => ?_, fun e' he' => ?_⟩).2 h2
  · change G.int.image π = (G.int.image π').image id
    rw [Finset.image_id]
    exact Finset.image_congr (fun v hv => (hagree v (Or.inl hv)).symm)
  · change G.ext.image π = (G.ext.image π').image id
    rw [Finset.image_id]
    exact Finset.image_congr (fun v hv => (hagree v (Or.inr hv)).symm)
  · obtain ⟨v1, v2⟩ := hR2 e (hGc e he)
    exact ⟨himg _ v1, himg _ v2⟩
  · exact (hcls e (hGc e he)).symm
  · obtain ⟨v1, v2⟩ := hR2 e (hGc e he)
    left
    change (π (G.ends e).1, π (G.ends e).2) = (π' (G.ends e).1, π' (G.ends e).2)
    rw [hagree _ v1, hagree _ v2]
  · by_contra hn
    exact he' e' (by rw [hcls e' (hGc' e' hn)]; exact hn) rfl

/-- **Merging molecules, globally standard** ([II, §5.4], [II, Def 6.2]): under the hypotheses of
`MGraph.spd_mapV_merge`, if every proper isolated subset of `G` saturated for `π` (the set of
internal vertices whose image lies in its image) is weakly isolated ([II, Def 6.1]), then the
graph with its vertices mapped by `π` and its loops removed is globally standard: a proper
isolated subset of the image is the image of the saturated set of its preimages, with the same
edges and red solid edges to the complement. -/
theorem MGraph.gs_mapV_merge :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] [Finite E] (G : MGraph V E) (π : V → V),
    (∀ v, π (π v) = π v) → (∀ v ∈ G.int, π v ∈ G.int) → (∀ v ∈ G.ext, π v = v) →
    (∀ v ∈ G.int, π v ∉ G.ext) → G.SPD → (∀ e, G.cls e ≠ some .ghost) →
    Disjoint G.int G.ext →
    (∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) →
    (∀ P, G.IsProperIso G.int P → P = G.int.filter (fun v => π v ∈ P.image π) →
      G.IsWeaklyIso P) →
    ((G.mapV π).unloop).GloballyStandard := by
  intro V E _ _ _ G π hidem hint hext hnie hs hng hd hR2 hsat
  refine ⟨MGraph.spd_mapV_merge V E G π hidem hint hext hnie hs hng hd hR2, fun P' hP' => ?_⟩
  set H := (G.mapV π).unloop with hH
  have hHint : H.int = G.int.image π := rfl
  have hHcls : ∀ e, H.cls e = if π (G.ends e).1 = π (G.ends e).2 then none else G.cls e :=
    fun e => rfl
  have hHends : ∀ e, H.ends e = (π (G.ends e).1, π (G.ends e).2) := fun e => rfl
  have hP's : P' ⊆ G.int := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hP'.1.1 hy)
    exact hint v hv
  set P := G.int.filter (fun v => π v ∈ P') with hPdef
  have hmem : ∀ a, G.IsVtx a → (a ∈ P ↔ π a ∈ P') := by
    intro a ha
    rcases ha with ha | ha
    · simp [hPdef, ha]
    · have hna : a ∉ G.int := fun h' => Finset.disjoint_left.1 hd h' ha
      simp only [hPdef, Finset.mem_filter, hna, false_and, false_iff]
      rw [hext a ha]
      exact fun h' => hna (hP's h')
  have hvtx : ∀ a, G.IsVtx a → H.IsVtx (π a) := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (Finset.mem_image_of_mem _ ha)
    · exact Or.inr (Finset.mem_image_of_mem _ ha)
  have hcut : ∀ e, G.IsVtx (G.ends e).1 → G.IsVtx (G.ends e).2 → (H.Cut P' e ↔ G.Cut P e) := by
    intro e v1 v2
    unfold MGraph.Cut
    rw [hHends, hmem _ v1, hmem _ v2]
  have hcr : ∀ e, H.Crosses P' e ↔ G.Crosses P e := by
    intro e
    constructor
    · rintro ⟨hc, hm, -, -, hct⟩
      have hGc : G.cls e ≠ none := fun h' => hc (by rw [hHcls]; simp [h'])
      obtain ⟨v1, v2⟩ := hR2 e hGc
      have hne : π (G.ends e).1 ≠ π (G.ends e).2 := fun h' => hc (by rw [hHcls]; simp [h'])
      rw [hHcls, itn hne] at hm
      exact ⟨hGc, hm, v1, v2, (hcut e v1 v2).1 hct⟩
    · rintro ⟨hc, hm, v1, v2, hct⟩
      have hct' := (hcut e v1 v2).2 hct
      have hne : π (G.ends e).1 ≠ π (G.ends e).2 := by
        intro h'
        unfold MGraph.Cut at hct'
        rw [hHends, h'] at hct'
        tauto
      have hcl : H.cls e = G.cls e := by rw [hHcls, itn hne]
      refine ⟨hcl ▸ hc, hcl ▸ hm, ?_, ?_, hct'⟩
      · rw [hHends]; exact hvtx _ v1
      · rw [hHends]; exact hvtx _ v2
  have hred : ∀ e, G.RedCrosses P e → H.RedCrosses P' e := by
    rintro e ⟨hm, v1, v2, hct⟩
    have hct' := (hcut e v1 v2).2 hct
    have hne : π (G.ends e).1 ≠ π (G.ends e).2 := by
      intro h'
      unfold MGraph.Cut at hct'
      rw [hHends, h'] at hct'
      tauto
    have hcl : H.cls e = G.cls e := by rw [hHcls, itn hne]
    refine ⟨hcl ▸ hm, ?_, ?_, hct'⟩
    · rw [hHends]; exact hvtx _ v1
    · rw [hHends]; exact hvtx _ v2
  have hPi : G.IsProperIso G.int P := by
    refine ⟨⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
    · obtain ⟨-, e₁, e₂, hne, hc⟩ := hP'.1
      exact ⟨e₁, e₂, hne, fun e => (hcr e).symm.trans (hc e)⟩
    · obtain ⟨y, hy, hyP⟩ := Finset.exists_of_ssubset hP'.2
      rw [hHint] at hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨π v, hint v hv, ?_⟩
      simp [hidem, hyP]
  have hsatP : P = G.int.filter (fun v => π v ∈ P.image π) := by
    ext v
    simp only [hPdef, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hv, hvP⟩
      exact ⟨hv, v, ⟨hv, hvP⟩, rfl⟩
    · rintro ⟨hv, w, ⟨-, hwP⟩, hwv⟩
      exact ⟨hv, hwv ▸ hwP⟩
  obtain ⟨-, e, e', hee, he, he'⟩ := hsat P hPi hsatP
  exact ⟨hP'.1, e, e', hee, hred e he, hred e' he'⟩

/-! ## Present edges joining vertices -/

/-- In the molecular graph of the block reading (`Graph.toMG'`), every edge joins two vertices:
its ends are representatives of molecules or external atoms. In particular every present edge
joins two vertices, the hypothesis on the present edges of `MGraph.spd_mapV_merge`. -/
theorem MolInsert_toMG'_ends_vtx :
  ∀ (k n : ℕ) (Γ : Graph k n) (e : Fin Γ.comps.length ⊕ Fin k),
    Γ.toMG'.IsVtx (Γ.toMG'.ends e).1 ∧ Γ.toMG'.IsVtx (Γ.toMG'.ends e).2 := by
  intro k n Γ e
  have hrep : ∀ u, Γ.toMG'.IsVtx (Γ.molRep u) := by
    intro u
    rcases u with a | a
    · exact Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · exact Or.inl (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  have hext : ∀ a : Fin k, Γ.toMG'.IsVtx (.inl a : Atom k n) := fun a =>
    Or.inr (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  rcases e with i | a
  · exact ⟨hrep _, hrep _⟩
  · change Γ.toMG'.IsVtx (match Γ.anchor (.inl a) with
        | some b => (Γ.molRep (.inr b), (.inl a : Atom k n))
        | none => ((.inl a : Atom k n), (.inl a : Atom k n))).1 ∧
      Γ.toMG'.IsVtx (match Γ.anchor (.inl a) with
        | some b => (Γ.molRep (.inr b), (.inl a : Atom k n))
        | none => ((.inl a : Atom k n), (.inl a : Atom k n))).2
    split
    · exact ⟨hrep (.inr _), hext a⟩
    · exact ⟨hext a, hext a⟩

section Instances

variable {X Z : Type}

end Instances

end RBM8D.Graphs
