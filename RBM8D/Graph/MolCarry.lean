import RBM8D.Graph.MolMerge
import RBM8D.Graph.MolSplit

/-!
# Operations on molecular multigraphs and the sequentially pre-deterministic property

A change of the names of the vertices and of the present edges, and the operations on molecular
multigraphs used in the proof of [II, Lemmas 5.10–5.13] (operations (A) and (B),
[II, Lemma 5.12 (v)], loops, red edges and edges to external vertices), with their effect on the
sequentially pre-deterministic property of [II, Def 5.9].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Lemmas on the molecular multigraph -/

section MGraphLemmas

variable {V E V' E' : Type}

/-- `G'` is `G` up to the names of the vertices and of the present edges and the orientation of
the present edges: a map of the vertices injective on the vertices of `G` and onto those of `G'`,
and a map of the edges injective on the present edges of `G`, keeping their classes and their
pairs of ends (in either order); every present edge of `G'` is the image of a present edge of `G`,
and the present edges of `G` join vertices. Absent edges of `G` and of `G'` (class `none`) are not
matched, so their number may change. -/
def MGraph.Transported [DecidableEq V'] (G : MGraph V E) (G' : MGraph V' E') : Prop :=
  ∃ (f : V → V') (g : E → E'),
    (∀ e₁ e₂, G.cls e₁ ≠ none → G.cls e₂ ≠ none → g e₁ = g e₂ → e₁ = e₂) ∧
    Set.InjOn f (↑G.int ∪ ↑G.ext) ∧
    G'.int = G.int.image f ∧ G'.ext = G.ext.image f ∧
    (∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) ∧
    (∀ e, G.cls e ≠ none → G'.cls (g e) = G.cls e) ∧
    (∀ e, G.cls e ≠ none → G'.ends (g e) = (f (G.ends e).1, f (G.ends e).2) ∨
      G'.ends (g e) = (f (G.ends e).2, f (G.ends e).1)) ∧
    ∀ e', (∀ e, G.cls e ≠ none → g e ≠ e') → G'.cls e' = none

/-- The operations on molecular multigraphs used in the proof of [II, Lemmas 5.10–5.13]:
* `merge`: operation (A), two internal vertices identified;
* `split`: operation (B), a blue solid edge with an internal end replaced by a path of two blue
  solid edges through an internal vertex ([II, Lemma 5.12], with case (v) of an external end);
* `splitExt`: a diffusive edge from an internal to an external vertex replaced by a diffusive
  edge to an internal vertex `w` and an edge of class blue or dotted from `w` to the external
  vertex;
* `loop`: a blue solid loop added at an internal vertex;
* `unloop`: a present loop of any class removed (after operation (A), the edges between the two
  identified vertices are loops);
* `red`: an absent or red solid edge moved or set absent or red;
* `ext`: an edge from an internal to an external vertex recoloured among blue, diffusive and
  dotted;
* `conv`: an internal blue solid edge changed into a diffusive edge;
* `dropExt`: an edge from an internal vertex `v` to an external vertex, neither absent nor red,
  removed when another such edge from `v` to an external vertex is present. -/
inductive MGraph.CarStep [DecidableEq V] [DecidableEq E] : MGraph V E → MGraph V E → Prop
  | merge (G : MGraph V E) (M M' : V) (hM : M ∈ G.int) (hM' : M' ∈ G.int) :
      MGraph.CarStep G (G.merge M M')
  | split (G : MGraph V E) (e e' : E) (w : V) (he : G.cls e = some .plus)
      (h1 : G.IsVtx (G.ends e).1) (h2 : G.IsVtx (G.ends e).2)
      (hi : (G.ends e).1 ∈ G.int ∨ (G.ends e).2 ∈ G.int) (hne : e ≠ e') (he' : G.cls e' = none)
      (hw : w ∈ G.int) : MGraph.CarStep G (G.split e e' w)
  | splitExt (G : MGraph V E) (e e' : E) (w : V) (c : MClass) (he : G.cls e = some .diff)
      (h1 : (G.ends e).1 ∈ G.int) (h2 : (G.ends e).2 ∈ G.ext) (hne : e ≠ e')
      (he' : G.cls e' = none) (hw : w ∈ G.int) (hc : c = .plus ∨ c = .dot) :
      MGraph.CarStep G ((G.split e e' w).recolor e' (some c))
  | loop (G : MGraph V E) (e : E) (v : V) (he : G.cls e = none) (hv : v ∈ G.int) :
      MGraph.CarStep G (G.setEdge e v v (some .plus))
  | unloop (G : MGraph V E) (e : E) (he : G.cls e ≠ none) (hl : (G.ends e).1 = (G.ends e).2) :
      MGraph.CarStep G (G.erase e)
  | red (G : MGraph V E) (e : E) (u v : V) (c : Option MClass)
      (he : G.cls e = none ∨ G.cls e = some .minus) (hc : c = none ∨ c = some .minus) :
      MGraph.CarStep G (G.setEdge e u v c)
  | ext (G : MGraph V E) (e : E) (c : MClass)
      (he : G.cls e = some .plus ∨ G.cls e = some .diff ∨ G.cls e = some .dot)
      (hc : c = .plus ∨ c = .diff ∨ c = .dot) (h1 : (G.ends e).1 ∈ G.int)
      (h2 : (G.ends e).2 ∈ G.ext) : MGraph.CarStep G (G.recolor e (some c))
  | conv (G : MGraph V E) (e : E) (he : G.IsIntPlus e) :
      MGraph.CarStep G (G.recolor e (some .diff))
  | dropExt (G : MGraph V E) (e e' : E) (hne : e ≠ e')
      (he : G.cls e ≠ none ∧ G.cls e ≠ some .minus) (h1 : (G.ends e).1 ∈ G.int)
      (h2 : (G.ends e).2 ∈ G.ext)
      (he' : G.cls e' ≠ none ∧ G.cls e' ≠ some .minus) (h1' : (G.ends e').1 = (G.ends e).1)
      (h2' : (G.ends e').2 ∈ G.ext) : MGraph.CarStep G (G.erase e)

end MGraphLemmas

section Invariance

variable {V E V' E' : Type}

/-! ### The fields of the operations -/

/-- Two molecular multigraphs with the same fields are equal. -/
private theorem mg_ext {G H : MGraph V E} (h1 : G.int = H.int) (h2 : G.ext = H.ext)
    (h3 : G.ends = H.ends) (h4 : G.cls = H.cls) : G = H := by
  cases G
  cases H
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

@[simp] private theorem erase_int' [DecidableEq E] (G : MGraph V E) (e : E) :
    (G.erase e).int = G.int := rfl
@[simp] private theorem erase_ext' [DecidableEq E] (G : MGraph V E) (e : E) :
    (G.erase e).ext = G.ext := rfl
@[simp] private theorem erase_ends' [DecidableEq E] (G : MGraph V E) (e : E) :
    (G.erase e).ends = G.ends := rfl
@[simp] private theorem erase_cls' [DecidableEq E] (G : MGraph V E) (e : E) :
    (G.erase e).cls = Function.update G.cls e none := rfl
@[simp] private theorem convert_int' [DecidableEq E] (G : MGraph V E) (l : List E) :
    (G.convert l).int = G.int := rfl
@[simp] private theorem convert_ext' [DecidableEq E] (G : MGraph V E) (l : List E) :
    (G.convert l).ext = G.ext := rfl
@[simp] private theorem convert_ends' [DecidableEq E] (G : MGraph V E) (l : List E) :
    (G.convert l).ends = G.ends := rfl
@[simp] private theorem convert_cls' [DecidableEq E] (G : MGraph V E) (l : List E) (x : E) :
    (G.convert l).cls x = if x ∈ l ∧ G.cls x = some .plus then some .diff else G.cls x := rfl
@[simp] private theorem induce_int' [DecidableEq V] (G : MGraph V E) (S : Finset V) :
    (G.induce S).int = S := rfl
@[simp] private theorem induce_ext' [DecidableEq V] (G : MGraph V E) (S : Finset V) :
    (G.induce S).ext = ∅ := rfl
@[simp] private theorem induce_ends' [DecidableEq V] (G : MGraph V E) (S : Finset V) :
    (G.induce S).ends = G.ends := rfl
@[simp] private theorem induce_cls' [DecidableEq V] (G : MGraph V E) (S : Finset V) (x : E) :
    (G.induce S).cls x =
      if (G.ends x).1 ∈ S ∧ (G.ends x).2 ∈ S then G.cls x else none := rfl
@[simp] private theorem replace_int' [DecidableEq V] [DecidableEq E] (G : MGraph V E)
    (S P : Finset V) (e₁ e₂ : E) : (G.replace S P e₁ e₂).int = S \ P := rfl
@[simp] private theorem replace_ext' [DecidableEq V] [DecidableEq E] (G : MGraph V E)
    (S P : Finset V) (e₁ e₂ : E) : (G.replace S P e₁ e₂).ext = ∅ := rfl
@[simp] private theorem replace_ends' [DecidableEq V] [DecidableEq E] (G : MGraph V E)
    (S P : Finset V) (e₁ e₂ x : E) : (G.replace S P e₁ e₂).ends x =
      if x = e₁ then (G.outer P e₁, G.outer P e₂) else G.ends x := rfl
@[simp] private theorem replace_cls' [DecidableEq V] [DecidableEq E] (G : MGraph V E)
    (S P : Finset V) (e₁ e₂ x : E) : (G.replace S P e₁ e₂).cls x =
      if x = e₁ then some .diff else if x = e₂ then none else (G.induce (S \ P)).cls x := rfl
@[simp] private theorem recolor_int' [DecidableEq E] (G : MGraph V E) (e : E)
    (c : Option MClass) : (G.recolor e c).int = G.int := rfl
@[simp] private theorem recolor_ext' [DecidableEq E] (G : MGraph V E) (e : E)
    (c : Option MClass) : (G.recolor e c).ext = G.ext := rfl
@[simp] private theorem recolor_ends' [DecidableEq E] (G : MGraph V E) (e : E)
    (c : Option MClass) : (G.recolor e c).ends = G.ends := rfl
@[simp] private theorem recolor_cls' [DecidableEq E] (G : MGraph V E) (e : E)
    (c : Option MClass) : (G.recolor e c).cls = Function.update G.cls e c := rfl
@[simp] private theorem setEdge_int' [DecidableEq E] (G : MGraph V E) (e : E) (u v : V)
    (c : Option MClass) : (G.setEdge e u v c).int = G.int := rfl
@[simp] private theorem setEdge_ext' [DecidableEq E] (G : MGraph V E) (e : E) (u v : V)
    (c : Option MClass) : (G.setEdge e u v c).ext = G.ext := rfl
@[simp] private theorem setEdge_ends' [DecidableEq E] (G : MGraph V E) (e : E) (u v : V)
    (c : Option MClass) (x : E) :
    (G.setEdge e u v c).ends x = if x = e then (u, v) else G.ends x := rfl
@[simp] private theorem setEdge_cls' [DecidableEq E] (G : MGraph V E) (e : E) (u v : V)
    (c : Option MClass) : (G.setEdge e u v c).cls = Function.update G.cls e c := rfl
@[simp] private theorem split_int' [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V) :
    (G.split e e' w).int = G.int := rfl
@[simp] private theorem split_ext' [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V) :
    (G.split e e' w).ext = G.ext := rfl
@[simp] private theorem split_ends' [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V) (x : E) :
    (G.split e e' w).ends x =
      if x = e then ((G.ends e).1, w) else if x = e' then (w, (G.ends e).2) else G.ends x := rfl
@[simp] private theorem split_cls' [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V) (x : E) :
    (G.split e e' w).cls x = if x = e' then G.cls e else G.cls x := rfl

/-- The empty list changes no edge. -/
private theorem convert_nil' [DecidableEq E] (G : MGraph V E) : G.convert [] = G :=
  mg_ext rfl rfl rfl (funext fun x => by simp)

/-- Removing an absent edge changes nothing. -/
private theorem erase_of_none [DecidableEq E] (G : MGraph V E) {e : E} (h : G.cls e = none) :
    G.erase e = G :=
  mg_ext rfl rfl rfl (by rw [erase_cls', ← h, Function.update_eq_self])

/-- Inducing on a set of vertices commutes with removing an edge. -/
private theorem induce_erase' [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S : Finset V)
    (e : E) : (G.erase e).induce S = (G.induce S).erase e := by
  refine mg_ext rfl rfl rfl (funext fun x => ?_)
  by_cases hx : x = e
  · subst hx
    simp
  · simp [hx]

/-- The replacement of [II, Def 5.9 (iii)] commutes with removing an edge other than the two
external edges. -/
private theorem replace_erase' [DecidableEq V] [DecidableEq E] (G : MGraph V E) (S P : Finset V)
    {e e₁ e₂ : E} (h1 : e ≠ e₁) (h2 : e ≠ e₂) :
    (G.erase e).replace S P e₁ e₂ = (G.replace S P e₁ e₂).erase e := by
  refine mg_ext rfl rfl rfl (funext fun x => ?_)
  by_cases hx : x = e
  · subst hx
    simp [h1, h2]
  · simp [hx]

/-- An edge with exactly one end in a set is not a loop. -/
private theorem cut_ne {G : MGraph V E} {S : Finset V} {x : E} (h : G.Cut S x) :
    (G.ends x).1 ≠ (G.ends x).2 := by
  intro h'
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact b (h' ▸ a)
  · exact a (h' ▸ b)

/-! ### The doubly connected property and the isolated subsets -/

/-- The doubly connected property passes from `G` to `G'` when they have the same internal
vertices and every edge of `G` between two distinct internal vertices keeps its ends, a diffusive
edge stays diffusive, and a blue solid or ghost edge becomes diffusive, blue solid or ghost. -/
private theorem dc_mono {G G' : MGraph V E} (hint : G'.int = G.int)
    (h : ∀ x, (G.ends x).1 ∈ G.int → (G.ends x).2 ∈ G.int → (G.ends x).1 ≠ (G.ends x).2 →
      (G.cls x = some .diff → G'.cls x = some .diff ∧ G'.ends x = G.ends x) ∧
      (G.cls x = some .plus ∨ G.cls x = some .ghost →
        (G'.cls x = some .diff ∨ G'.cls x = some .plus ∨ G'.cls x = some .ghost) ∧
          G'.ends x = G.ends x))
    (hG : G.DC) : G'.DC := by
  classical
  obtain ⟨black, blue, hd, hbk, hbu, hsk, hsu⟩ := hG
  let U : E → Prop := fun x =>
    (G.ends x).1 ∈ G.int ∧ (G.ends x).2 ∈ G.int ∧ (G.ends x).1 ≠ (G.ends x).2
  have hblue : ∀ x, U x → (G.cls x = some .diff ∨ G.cls x = some .plus ∨
      G.cls x = some .ghost) →
      (G'.cls x = some .diff ∨ G'.cls x = some .plus ∨ G'.cls x = some .ghost) ∧
        G'.ends x = G.ends x := by
    rintro x ⟨h1, h2, h3⟩ hc
    rcases hc with hc | hc | hc
    · exact ⟨Or.inl ((h x h1 h2 h3).1 hc).1, ((h x h1 h2 h3).1 hc).2⟩
    · exact (h x h1 h2 h3).2 (Or.inl hc)
    · exact (h x h1 h2 h3).2 (Or.inr hc)
  refine ⟨black.filter U, blue.filter U,
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hx, h1, h2, h3⟩ := Finset.mem_filter.1 hx
    exact ((h x h1 h2 h3).1 (hbk x hx)).1
  · intro x hx
    obtain ⟨hx, hU⟩ := Finset.mem_filter.1 hx
    exact (hblue x hU (hbu x hx)).1
  · intro S hS hne hn
    rw [hint] at hS hn
    obtain ⟨x, hx, -, h1, h2, h3⟩ := hsk S hS hne hn
    have hU : U x := ⟨h1, h2, cut_ne h3⟩
    obtain ⟨hc', he'⟩ := (h x h1 h2 (cut_ne h3)).1 (hbk x hx)
    refine ⟨x, Finset.mem_filter.2 ⟨hx, hU⟩, by rw [hc']; simp, ?_, ?_, ?_⟩
    · rw [he', hint]; exact h1
    · rw [he', hint]; exact h2
    · simpa [MGraph.Cut, he'] using h3
  · intro S hS hne hn
    rw [hint] at hS hn
    obtain ⟨x, hx, -, h1, h2, h3⟩ := hsu S hS hne hn
    have hU : U x := ⟨h1, h2, cut_ne h3⟩
    obtain ⟨hc', he'⟩ := hblue x hU (hbu x hx)
    refine ⟨x, Finset.mem_filter.2 ⟨hx, hU⟩, ?_, ?_, ?_, ?_⟩
    · rcases hc' with hc' | hc' | hc' <;> rw [hc'] <;> simp
    · rw [he', hint]; exact h1
    · rw [he', hint]; exact h2
    · simpa [MGraph.Cut, he'] using h3

/-- Isolated subsets agree when the internal vertices and the crossing edges agree. -/
private theorem isIso_congr {A B : MGraph V E} (hint : B.int = A.int) {P : Finset V}
    (hc : ∀ x, B.Crosses P x ↔ A.Crosses P x) : B.IsIsolated P ↔ A.IsIsolated P := by
  unfold MGraph.IsIsolated
  rw [hint]
  simp only [hc]

/-- Three distinct edges crossing `P` show that `P` is not isolated. -/
private theorem not_iso_of_three {G : MGraph V E} {P : Finset V} {a b c : E} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : G.Crosses P a) (hb : G.Crosses P b)
    (hc : G.Crosses P c) : ¬ G.IsIsolated P := by
  rintro ⟨-, e₁, e₂, -, h⟩
  rcases (h a).1 ha with rfl | rfl <;> rcases (h b).1 hb with rfl | rfl <;>
    rcases (h c).1 hc with rfl | rfl <;> simp_all

/-- The sequentially pre-deterministic property passes from `A` to `B` when they have the same
internal vertices and the same proper isolated subsets, the external edges of an isolated subset
of `B` cross it in `A`, and the doubly connected property, the induced subgraphs on sets of
internal vertices and the replacements of [II, Def 5.9 (iii)] pass from `A` to `B`. -/
private theorem spd_congr [DecidableEq V] [DecidableEq E] {A B : MGraph V E}
    (hint : B.int = A.int)
    (hiso : ∀ P, P ⊆ A.int → P ≠ A.int → (B.IsIsolated P ↔ A.IsIsolated P))
    (hcr : ∀ P x, P ⊆ A.int → P ≠ A.int → A.IsIsolated P → B.Crosses P x → A.Crosses P x)
    (hdc : A.DC → B.DC)
    (hind : ∀ S, S ⊆ A.int → (A.induce S).PreDet → (B.induce S).PreDet)
    (hrep : ∀ S P e₁ e₂, S ⊆ A.int → P ⊂ S → A.IsIsolated P → e₁ ≠ e₂ → A.Crosses P e₁ →
      A.Crosses P e₂ → (A.replace S P e₁ e₂).PreDet → (B.replace S P e₁ e₂).PreDet)
    (h : A.SPD) : B.SPD := by
  obtain ⟨hdA, hch, h3, h4⟩ := h
  have hsub : ∀ S, B.IsoOrTop S → S ⊆ A.int := by
    rintro S (rfl | hS)
    · exact hint.le
    · exact hint ▸ hS.1
  have hne_of : ∀ S Q, S ⊆ A.int → Q ⊂ S → Q ≠ A.int := by
    rintro S Q hS hQ rfl
    exact (Finset.ssubset_iff_subset_ne.1 hQ).2 (Finset.Subset.antisymm hQ.subset hS)
  have htop : ∀ S, B.IsoOrTop S → A.IsoOrTop S := by
    intro S hS
    by_cases hSA : S = A.int
    · exact Or.inl hSA
    · rcases hS with h | h
      · exact absurd (h.trans hint) hSA
      · exact Or.inr ((hiso S (hint ▸ h.1) hSA).1 h)
  have hprop : ∀ S Q, S ⊆ A.int → (B.IsProperIso S Q ↔ A.IsProperIso S Q) := by
    intro S Q hS
    constructor
    · rintro ⟨hQ, hlt⟩
      exact ⟨(hiso Q (hlt.subset.trans hS) (hne_of S Q hS hlt)).1 hQ, hlt⟩
    · rintro ⟨hQ, hlt⟩
      exact ⟨(hiso Q (hlt.subset.trans hS) (hne_of S Q hS hlt)).2 hQ, hlt⟩
  refine ⟨hdc hdA, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    rw [hint] at hP hQ
    exact hch P Q ((hprop _ _ le_rfl).1 hP) ((hprop _ _ le_rfl).1 hQ)
  · intro S hS hno
    have hSA := hsub S hS
    exact hind S hSA (h3 S (htop S hS) fun Q hQ => hno Q ((hprop S Q hSA).2 hQ))
  · intro S P e₁ e₂ hS hmax hne c₁ c₂
    have hSA := hsub S hS
    have hmaxA : A.IsMaximalIso S P :=
      ⟨(hprop S P hSA).1 hmax.1, fun Q hQ => hmax.2 Q ((hprop S Q hSA).2 hQ)⟩
    have hPA : A.IsIsolated P := hmaxA.1.1
    have hPs : P ⊆ A.int := hmax.1.2.subset.trans hSA
    have hPn : P ≠ A.int := hne_of S P hSA hmax.1.2
    have c₁' := hcr P e₁ hPs hPn hPA c₁
    have c₂' := hcr P e₂ hPs hPn hPA c₂
    exact hrep S P e₁ e₂ hSA hmax.1.2 hPA hne c₁' c₂' (h4 S P e₁ e₂ (htop S hS) hmaxA hne c₁' c₂')

end Invariance

section Orders

variable {V E : Type}

/-! ### Pre-deterministic orders without one edge -/

/-- An element of `l.filter p` and the elements before it, matched with an element of `l` and the
elements before it, up to the elements outside `p`. -/
private theorem filter_take_aux {α : Type} (p : α → Bool) :
    ∀ (l : List α) (j : ℕ) (hj : j < (l.filter p).length), ∃ (j' : ℕ) (hj' : j' < l.length),
      (l.filter p)[j] = l[j'] ∧ ∀ x, p x = true → (x ∈ (l.filter p).take j ↔ x ∈ l.take j')
  | [], j, hj => by simp at hj
  | a :: t, j, hj => by
    by_cases ha : p a = true
    · have hf : (a :: t).filter p = a :: t.filter p := List.filter_cons_of_pos ha
      rcases j with _ | j
      · refine ⟨0, by simp, by simp [hf], fun x _ => by simp⟩
      · have hj' : j < (t.filter p).length := by
          simp only [hf, List.length_cons] at hj
          omega
        obtain ⟨j', hj'', heq, hm⟩ := filter_take_aux p t j hj'
        refine ⟨j' + 1, by simp; omega, by simp [hf, heq], fun x hx => ?_⟩
        simp only [hf, List.take_succ_cons, List.mem_cons, hm x hx]
    · have hf : (a :: t).filter p = t.filter p := List.filter_cons_of_neg ha
      have hj' : j < (t.filter p).length := by
        rw [hf] at hj
        exact hj
      obtain ⟨j', hj'', heq, hm⟩ := filter_take_aux p t j hj'
      refine ⟨j' + 1, by simp; omega, by simp [hf, heq], fun x hx => ?_⟩
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      simp only [hf, List.take_succ_cons, List.mem_cons, hm x hx, hxa, false_or]

/-- A pre-deterministic graph `H` gives a pre-deterministic graph `H'` whose internal blue solid
edges are those of `H` other than `e`, when the doubly connected property and redundancy pass
from `H` to `H'` after changing the same edges other than `e` into `Θ` edges. -/
private theorem preDet_drop [DecidableEq E] {H H' : MGraph V E} (e : E)
    (hp : ∀ x, H'.IsIntPlus x ↔ H.IsIntPlus x ∧ x ≠ e)
    (hred : ∀ L L' : List E, (∀ x, x ≠ e → (x ∈ L ↔ x ∈ L')) → ∀ y, y ≠ e →
      (H.convert L).IsRedundant y → (H'.convert L').IsRedundant y)
    (hdc : H.DC → H'.DC) (h : H.PreDet) : H'.PreDet := by
  obtain ⟨hd, l, hnd, hmem, hr⟩ := h
  refine ⟨hdc hd, l.filter (fun x => decide (x ≠ e)), hnd.filter _, fun x => ?_, fun j hj => ?_⟩
  · rw [List.mem_filter, hmem, hp, decide_eq_true_iff]
  · obtain ⟨j', hj', heq, hm⟩ := filter_take_aux _ l j hj
    have hy : (l.filter (fun x => decide (x ≠ e)))[j] ≠ e := by
      have := List.getElem_mem hj
      rw [List.mem_filter, decide_eq_true_iff] at this
      exact this.2
    rw [heq] at hy ⊢
    exact hred _ _ (fun x hx => (hm x (decide_eq_true hx)).symm) _ hy (hr j' hj')

/-! ### Loops -/

/-- `B` agrees with `A` except possibly for the class of the edge `e`. -/
private def AgreeOff (A B : MGraph V E) (e : E) : Prop :=
  B.int = A.int ∧ B.ext = A.ext ∧ B.ends = A.ends ∧ ∀ x, x ≠ e → B.cls x = A.cls x

private theorem AgreeOff.symm {A B : MGraph V E} {e : E} (h : AgreeOff A B e) :
    AgreeOff B A e :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun x hx => (h.2.2.2 x hx).symm⟩

/-- The doubly connected property does not see the class of a loop. -/
private theorem AgreeOff.dc {A B : MGraph V E} {e : E} (h : AgreeOff A B e)
    (hl : (A.ends e).1 = (A.ends e).2) (hA : A.DC) : B.DC := by
  refine dc_mono h.1 (fun x _ _ hx => ?_) hA
  have hxe : x ≠ e := by
    rintro rfl
    exact hx hl
  rw [h.2.2.2 x hxe, h.2.2.1]
  exact ⟨fun hc => ⟨hc, rfl⟩, fun hc => ⟨by rcases hc with hc | hc <;> simp [hc], rfl⟩⟩

/-- A loop crosses no set. -/
private theorem AgreeOff.crosses {A B : MGraph V E} {e : E} (h : AgreeOff A B e)
    (hl : (A.ends e).1 = (A.ends e).2) (P : Finset V) (x : E) :
    B.Crosses P x ↔ A.Crosses P x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  by_cases hx : x = e
  · subst hx
    have hl' : (B.ends x).1 = (B.ends x).2 := by rw [h3]; exact hl
    constructor
    · rintro ⟨-, -, -, -, hc⟩
      exact absurd hl' (cut_ne hc)
    · rintro ⟨-, -, -, -, hc⟩
      exact absurd hl (cut_ne hc)
  · simp only [MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, h1, h2, h3, h4 x hx]

private theorem AgreeOff.erase [DecidableEq E] {A B : MGraph V E} {e : E} (h : AgreeOff A B e)
    (y : E) : AgreeOff (A.erase y) (B.erase y) e := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x hx => ?_⟩
  by_cases hy : x = y
  · subst hy
    simp
  · simp [hy, h.2.2.2 x hx]

private theorem AgreeOff.convert [DecidableEq E] {A B : MGraph V E} {e : E} (h : AgreeOff A B e)
    {L L' : List E} (hL : ∀ x, x ≠ e → (x ∈ L ↔ x ∈ L')) :
    AgreeOff (A.convert L) (B.convert L') e := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x hx => ?_⟩
  simp [h.2.2.2 x hx, hL x hx]

/-- Redundancy of an edge other than a loop does not see the class of the loop. -/
private theorem AgreeOff.redundant [DecidableEq E] {A B : MGraph V E} {e y : E}
    (h : AgreeOff A B e) (hl : (A.ends e).1 = (A.ends e).2) (hy : y ≠ e)
    (hr : A.IsRedundant y) : B.IsRedundant y :=
  ⟨by rw [h.2.2.2 y hy]; exact hr.1, h.dc hl hr.2.1, (h.erase y).dc hl hr.2.2⟩

/-- Removing a loop keeps the pre-deterministic property. -/
private theorem preDet_erase_loop [DecidableEq E] {H : MGraph V E} {e : E}
    (hl : (H.ends e).1 = (H.ends e).2) (h : H.PreDet) : (H.erase e).PreDet := by
  have hag : AgreeOff H (H.erase e) e := ⟨rfl, rfl, rfl, fun x hx => by simp [hx]⟩
  refine preDet_drop e (fun x => ?_) (fun L L' hL y hy hr => ?_) (hag.dc hl) h
  · by_cases hx : x = e
    · subst hx
      simp [MGraph.IsIntPlus]
    · simp [MGraph.IsIntPlus, hx]
  · exact (hag.convert hL).redundant hl hy hr

/-- Adding back a loop keeps the pre-deterministic property: a blue solid loop at an internal
vertex is redundant and comes first in the order. -/
private theorem preDet_of_erase_loop [DecidableEq E] {H : MGraph V E} {e : E}
    (hl : (H.ends e).1 = (H.ends e).2) (h : (H.erase e).PreDet) : H.PreDet := by
  have hag : AgreeOff (H.erase e) H e := ⟨rfl, rfl, rfl, fun x hx => by simp [hx]⟩
  have hl' : ((H.erase e).ends e).1 = ((H.erase e).ends e).2 := hl
  obtain ⟨hd, l, hnd, hmem, hr⟩ := h
  have hdH : H.DC := hag.dc hl' hd
  have hne : ∀ x ∈ l, x ≠ e := by
    rintro x hx rfl
    have := ((hmem x).1 hx).1
    simp [MGraph.erase] at this
  have hpe : ∀ x, x ≠ e → ((H.erase e).IsIntPlus x ↔ H.IsIntPlus x) := by
    intro x hx
    simp [MGraph.IsIntPlus, hx]
  by_cases hp : H.IsIntPlus e
  · refine ⟨hdH, e :: l, List.nodup_cons.2 ⟨fun he => hne e he rfl, hnd⟩, fun x => ?_,
      fun j hj => ?_⟩
    · by_cases hx : x = e
      · subst hx
        simpa using hp
      · rw [List.mem_cons, hmem, hpe x hx]
        simp [hx]
    · rcases j with _ | j
      · simp only [List.take_zero, List.getElem_cons_zero, convert_nil']
        exact ⟨hp.1, hdH, hd⟩
      · simp only [List.take_succ_cons, List.getElem_cons_succ]
        have hj' : j < l.length := by simp at hj; omega
        have hag' : AgreeOff ((H.erase e).convert (l.take j)) (H.convert (e :: l.take j)) e :=
          hag.convert (fun x hx => by simp [hx])
        exact hag'.redundant hl' (hne _ (List.getElem_mem hj')) (hr j hj')
  · refine ⟨hdH, l, hnd, fun x => ?_, fun j hj => ?_⟩
    · by_cases hx : x = e
      · subst hx
        constructor
        · intro h
          exact absurd rfl (hne x h)
        · intro h
          exact absurd h hp
      · rw [hmem, hpe x hx]
    · exact (hag.convert (fun x _ => Iff.rfl)).redundant hl' (hne _ (List.getElem_mem hj))
        (hr j hj)

/-- Removing a loop does not change the sequentially pre-deterministic property. -/
private theorem spd_erase_loop [DecidableEq V] [DecidableEq E] {G : MGraph V E} {e : E}
    (hl : (G.ends e).1 = (G.ends e).2) : (G.erase e).SPD ↔ G.SPD := by
  have hag : AgreeOff G (G.erase e) e := ⟨rfl, rfl, rfl, fun x hx => by simp [hx]⟩
  have hl' : ((G.erase e).ends e).1 = ((G.erase e).ends e).2 := hl
  have hne : ∀ (H : MGraph V E) P x, H.ends = G.ends → H.Crosses P x → x ≠ e := by
    rintro H P x hH ⟨-, -, -, -, hc⟩ rfl
    exact cut_ne hc (by rw [hH]; exact hl)
  constructor
  · refine spd_congr rfl (fun P _ _ => isIso_congr (A := G.erase e) (B := G) rfl
      (hag.symm.crosses hl' P))
      (fun P x _ _ _ hc => (hag.symm.crosses hl' P x).1 hc) (hag.symm.dc hl')
      (fun S _ h => ?_) (fun S P e₁ e₂ _ _ _ _ c₁ c₂ h => ?_)
    · rw [induce_erase'] at h
      exact preDet_of_erase_loop hl h
    · rw [replace_erase' G S P (hne (G.erase e) P e₁ rfl c₁).symm
        (hne (G.erase e) P e₂ rfl c₂).symm] at h
      have hl'' : ((G.replace S P e₁ e₂).ends e).1 = ((G.replace S P e₁ e₂).ends e).2 := by
        simp [(hne (G.erase e) P e₁ rfl c₁).symm, hl]
      exact preDet_of_erase_loop hl'' h
  · refine spd_congr rfl (fun P _ _ => isIso_congr (A := G) (B := G.erase e) rfl
      (hag.crosses hl P))
      (fun P x _ _ _ hc => (hag.crosses hl P x).1 hc) (hag.dc hl)
      (fun S _ h => ?_) (fun S P e₁ e₂ _ _ _ _ c₁ c₂ h => ?_)
    · rw [induce_erase']
      exact preDet_erase_loop hl h
    · rw [replace_erase' G S P (hne _ P e₁ rfl c₁).symm (hne _ P e₂ rfl c₂).symm]
      have hl'' : ((G.replace S P e₁ e₂).ends e).1 = ((G.replace S P e₁ e₂).ends e).2 := by
        simp [(hne _ P e₁ rfl c₁).symm, hl]
      exact preDet_erase_loop hl'' h

end Orders

section Classes

variable {V E : Type}

/-! ### Red solid edges and edges with an end that is not internal -/

/-- `B` is `A` up to the edges that are absent or red solid in both and up to the classes of the
edges that have an end that is not internal and are present and not red solid in both. -/
private def SimE (A B : MGraph V E) (x : E) : Prop :=
  (B.cls x = A.cls x ∧ B.ends x = A.ends x) ∨
    ((A.cls x = none ∨ A.cls x = some .minus) ∧ (B.cls x = none ∨ B.cls x = some .minus)) ∨
    (B.ends x = A.ends x ∧ ((A.ends x).1 ∉ A.int ∨ (A.ends x).2 ∉ A.int) ∧
      (A.cls x ≠ none ∧ A.cls x ≠ some .minus) ∧ (B.cls x ≠ none ∧ B.cls x ≠ some .minus))

/-- `B` is `A` up to the edges of `SimE`, with the same internal and external vertices. -/
private def Sim (A B : MGraph V E) : Prop := B.int = A.int ∧ B.ext = A.ext ∧ ∀ x, SimE A B x

private theorem Sim.symm {A B : MGraph V E} (h : Sim A B) : Sim B A := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, h2.symm, fun x => ?_⟩
  rcases h3 x with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨a.symm, b.symm⟩
  · exact Or.inr (Or.inl ⟨b, a⟩)
  · exact Or.inr (Or.inr ⟨a.symm, by rw [a, h1]; exact b, d, c⟩)

/-- An edge between two internal vertices that is present and not red solid in `A` has the same
class and ends in `B`. -/
private theorem Sim.same {A B : MGraph V E} (h : Sim A B) {x : E}
    (h1 : (A.ends x).1 ∈ A.int) (h2 : (A.ends x).2 ∈ A.int)
    (hl : A.cls x ≠ none ∧ A.cls x ≠ some .minus) : B.cls x = A.cls x ∧ B.ends x = A.ends x := by
  rcases h.2.2 x with h' | ⟨a, -⟩ | ⟨-, b, -⟩
  · exact h'
  · rcases a with a | a
    · exact absurd a hl.1
    · exact absurd a hl.2
  · rcases b with b | b
    · exact absurd h1 b
    · exact absurd h2 b

private theorem Sim.crosses {A B : MGraph V E} (h : Sim A B) (P : Finset V) (x : E) :
    B.Crosses P x ↔ A.Crosses P x := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases h3 x with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, -, c, d⟩
  · simp only [MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, h1, h2, a, b]
  · constructor
    · rintro ⟨c1, c2, -⟩
      rcases b with b | b
      · exact absurd b c1
      · exact absurd b c2
    · rintro ⟨c1, c2, -⟩
      rcases a with a | a
      · exact absurd a c1
      · exact absurd a c2
  · simp only [MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, h1, h2, a, c, d, ne_eq, not_false_eq_true,
      true_and]

private theorem Sim.dc {A B : MGraph V E} (h : Sim A B) (hA : A.DC) : B.DC := by
  refine dc_mono h.1 (fun x h1 h2 _ => ?_) hA
  constructor
  · intro hc
    have := h.same h1 h2 (by rw [hc]; simp)
    exact ⟨this.1.trans hc, this.2⟩
  · intro hc
    have := h.same h1 h2 (by rcases hc with hc | hc <;> rw [hc] <;> simp)
    refine ⟨?_, this.2⟩
    rw [this.1]
    rcases hc with hc | hc <;> simp [hc]

private theorem Sim.convert [DecidableEq E] {A B : MGraph V E} (h : Sim A B) (l : List E) :
    Sim (A.convert l) (B.convert l) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun x => ?_⟩
  rcases h3 x with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨by simp [a], b⟩
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rcases a with a | a <;> simp [a]
    · rcases b with b | b <;> simp [b]
  · refine Or.inr (Or.inr ⟨a, b, ?_, ?_⟩)
    · simp only [convert_cls']
      split_ifs <;> simp_all
    · simp only [convert_cls']
      split_ifs <;> simp_all

private theorem Sim.erase [DecidableEq E] {A B : MGraph V E} (h : Sim A B) (y : E) :
    Sim (A.erase y) (B.erase y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun x => ?_⟩
  by_cases hx : x = y
  · subst hx
    exact Or.inr (Or.inl ⟨by simp, by simp⟩)
  · have := h3 x
    simpa [SimE, hx] using this

private theorem Sim.induce [DecidableEq V] {A B : MGraph V E} (h : Sim A B) {S : Finset V}
    (hS : S ⊆ A.int) : Sim (A.induce S) (B.induce S) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨rfl, rfl, fun x => ?_⟩
  rcases h3 x with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨by simp [a, b], by simp [b]⟩
  · refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [induce_cls']
      split_ifs <;> simp_all
    · simp only [induce_cls']
      split_ifs <;> simp_all
  · have hn : ¬ ((A.ends x).1 ∈ S ∧ (A.ends x).2 ∈ S) := by
      rintro ⟨e1, e2⟩
      rcases b with b | b
      · exact b (hS e1)
      · exact b (hS e2)
    have hn' : ¬ ((B.ends x).1 ∈ S ∧ (B.ends x).2 ∈ S) := by rw [a]; exact hn
    exact Or.inr (Or.inl ⟨Or.inl (by simp [hn]), Or.inl (by simp [hn'])⟩)

private theorem Sim.replace [DecidableEq V] [DecidableEq E] {A B : MGraph V E} (h : Sim A B)
    {S P : Finset V} {e₁ e₂ : E} (hS : S ⊆ A.int) (c₁ : A.Crosses P e₁)
    (c₂ : A.Crosses P e₂) : Sim (A.replace S P e₁ e₂) (B.replace S P e₁ e₂) := by
  have he : ∀ y, A.Crosses P y → B.ends y = A.ends y := by
    intro y hy
    rcases h.2.2 y with ⟨-, b⟩ | ⟨a, -⟩ | ⟨b, -⟩
    · exact b
    · rcases a with a | a
      · exact absurd a hy.1
      · exact absurd a hy.2.1
    · exact b
  have hi := (h.induce (S := S \ P) (fun v hv => hS (Finset.mem_sdiff.1 hv).1)).2.2
  refine ⟨rfl, rfl, fun x => ?_⟩
  by_cases hx1 : x = e₁
  · subst hx1
    refine Or.inl ⟨by simp, ?_⟩
    simp [MGraph.outer, he x c₁, he e₂ c₂]
  · by_cases hx2 : x = e₂
    · subst hx2
      exact Or.inl ⟨by simp [hx1], by simp [hx1, he x c₂]⟩
    · have := hi x
      simpa [SimE, hx1, hx2] using this

private theorem Sim.preDet [DecidableEq E] {A B : MGraph V E} (h : Sim A B) (hA : A.PreDet) :
    B.PreDet := by
  obtain ⟨hd, l, hnd, hmem, hr⟩ := hA
  have hp : ∀ x, B.IsIntPlus x ↔ A.IsIntPlus x := by
    have key : ∀ {A B : MGraph V E}, Sim A B → ∀ x, A.IsIntPlus x → B.IsIntPlus x := by
      intro A B h x ⟨hc, h1, h2⟩
      have := h.same h1 h2 (by rw [hc]; simp)
      refine ⟨this.1.trans hc, ?_, ?_⟩
      · rw [this.2, h.1]; exact h1
      · rw [this.2, h.1]; exact h2
    exact fun x => ⟨key h.symm x, key h x⟩
  refine ⟨h.dc hd, l, hnd, fun x => (hmem x).trans (hp x).symm, fun j hj => ?_⟩
  have hs := h.convert (l.take j)
  obtain ⟨hc, hd1, hd2⟩ := hr j hj
  have hint := (hmem _).1 (List.getElem_mem hj)
  have := hs.same (by simpa using hint.2.1) (by simpa using hint.2.2) (by rw [hc]; simp)
  exact ⟨this.1.trans hc, hs.dc hd1, (hs.erase _).dc hd2⟩

/-- The sequentially pre-deterministic property passes along `Sim`. -/
private theorem Sim.spd [DecidableEq V] [DecidableEq E] {A B : MGraph V E} (h : Sim A B)
    (hA : A.SPD) : B.SPD :=
  spd_congr h.1 (fun P _ _ => isIso_congr h.1 (h.crosses P))
    (fun P x _ _ _ hc => (h.crosses P x).1 hc) h.dc
    (fun _ hS hp => (h.induce hS).preDet hp)
    (fun _ _ _ _ hS _ _ _ c₁ c₂ hp => (h.replace hS c₁ c₂).preDet hp) hA

/-! ### Changing an internal blue solid edge into a diffusive edge -/

/-- The doubly connected property passes from `A` to `B` when `B` agrees with `A` off `e` and the
edge `e`, blue solid or diffusive in `A`, is diffusive in `B`. -/
private theorem dc_conv_off {A B : MGraph V E} {e : E} (hint : B.int = A.int)
    (hends : B.ends = A.ends) (hoff : ∀ x, x ≠ e → B.cls x = A.cls x)
    (he : B.cls e = some .diff) (hA : A.cls e = some .plus ∨ A.cls e = some .diff)
    (h : A.DC) : B.DC := by
  refine dc_mono hint (fun x _ _ _ => ?_) h
  rw [hends]
  by_cases hx : x = e
  · subst hx
    rw [he]
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨Or.inl rfl, rfl⟩⟩
  · rw [hoff x hx]
    exact ⟨fun hc => ⟨hc, rfl⟩, fun hc => ⟨by rcases hc with hc | hc <;> simp [hc], rfl⟩⟩

/-- Changing an internal blue solid edge of a pre-deterministic graph into a diffusive edge keeps
it pre-deterministic: the edge is dropped from the order. -/
private theorem preDet_conv [DecidableEq E] {H : MGraph V E} {e : E} (hp : H.IsIntPlus e)
    (h : H.PreDet) : (H.recolor e (some .diff)).PreDet := by
  refine preDet_drop e (fun x => ?_) (fun L L' hL y hy hr => ?_)
    (dc_conv_off (A := H) (B := H.recolor e (some .diff)) (e := e) rfl rfl
      (fun x hx => by simp [hx]) (by simp) (Or.inl hp.1)) h
  · by_cases hx : x = e
    · subst hx
      simp [MGraph.IsIntPlus]
    · simp [MGraph.IsIntPlus, hx]
  · have hoff : ∀ x, x ≠ e →
        ((H.recolor e (some .diff)).convert L').cls x = (H.convert L).cls x := by
      intro x hx
      simp [hx, hL x hx]
    have he : ((H.recolor e (some .diff)).convert L').cls e = some .diff := by simp
    have hA : (H.convert L).cls e = some .plus ∨ (H.convert L).cls e = some .diff := by
      simp only [convert_cls', hp.1]
      split_ifs <;> simp
    set A := H.convert L
    set B := (H.recolor e (some .diff)).convert L'
    refine ⟨by rw [hoff y hy]; exact hr.1,
      dc_conv_off (A := A) (B := B) (e := e) rfl rfl hoff he hA hr.2.1,
      dc_conv_off (A := A.erase y) (B := B.erase y) (e := e) rfl rfl (fun x hx => ?_)
        (by simp [Ne.symm hy, he]) (by simpa [Ne.symm hy] using hA) hr.2.2⟩
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy, hoff x hx]

end Classes

section Transport

variable {V E V' E' : Type}

/-! ### A change of the names of the vertices and of the present edges -/

/-- A change of names from `G` to `G'`: a map `f` of the vertices injective on a set `T` that
contains the vertices of `G` and the ends of its present edges, and a map `g` of the edges
injective on the present edges of `G` and onto the present edges of `G'`, keeping the classes and
the pairs of ends (in either order). -/
private structure TrH [DecidableEq V'] (G : MGraph V E) (G' : MGraph V' E') (f : V → V')
    (g : E → E') (T : Set V) : Prop where
  inj : Set.InjOn f T
  int_sub : ∀ v ∈ G.int, v ∈ T
  ext_sub : ∀ v ∈ G.ext, v ∈ T
  ends_mem : ∀ e, G.cls e ≠ none → (G.ends e).1 ∈ T ∧ (G.ends e).2 ∈ T
  int_eq : G'.int = G.int.image f
  ext_eq : G'.ext = G.ext.image f
  ginj : ∀ e₁ e₂, G.cls e₁ ≠ none → G.cls e₂ ≠ none → g e₁ = g e₂ → e₁ = e₂
  cls_eq : ∀ e, G.cls e ≠ none → G'.cls (g e) = G.cls e
  ends_eq : ∀ e, G.cls e ≠ none → G'.ends (g e) = (f (G.ends e).1, f (G.ends e).2) ∨
    G'.ends (g e) = (f (G.ends e).2, f (G.ends e).1)
  surj : ∀ e', G'.cls e' ≠ none → ∃ e, G.cls e ≠ none ∧ g e = e'

/-- A molecular multigraph without present edges is sequentially pre-deterministic iff it has at
most one internal vertex. -/
private theorem spd_iff_of_noEdge [DecidableEq V] [DecidableEq E] {G : MGraph V E}
    (hn : ∀ e, G.cls e = none) : G.SPD ↔ G.int.card ≤ 1 := by
  constructor
  · intro hs
    by_contra hc
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (not_le.1 hc)
    obtain ⟨black, -, -, -, -, hsk, -⟩ := hs.1
    obtain ⟨x, -, hx, -⟩ := hsk {a} (Finset.singleton_subset_iff.2 ha)
      (Finset.singleton_nonempty a) (fun hsub => hab (Finset.mem_singleton.1 (hsub hb)).symm)
    exact hx (hn x)
  · intro hc
    have hsp : ∀ B : Finset E, G.Spans B := by
      intro B S hS ⟨v, hv⟩ hn'
      refine absurd (fun w hw => ?_) hn'
      rw [Finset.card_le_one.1 hc w hw v (hS hv)]
      exact hv
    refine MGraph.SPD_of_preDet _ _ G ⟨⟨∅, ∅, disjoint_bot_left, by simp, by simp, hsp _, hsp _⟩,
      [], List.nodup_nil, fun e => ⟨by simp, fun h => ?_⟩, fun j hj => absurd hj (by simp)⟩ ?_
    · have := h.1
      rw [hn e] at this
      exact absurd this (by simp)
    · rintro Q ⟨⟨_, e₁, e₂, _, hcr⟩, _⟩
      exact ((hcr e₁).2 (Or.inl rfl)).1 (hn e₁)

section

variable [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'}
  {T : Set V}

private theorem TrH.mem_image (h : TrH G G' f g T) {S : Finset V} (hS : ∀ v ∈ S, v ∈ T) {a : V}
    (ha : a ∈ T) : f a ∈ S.image f ↔ a ∈ S := by
  constructor
  · intro hm
    obtain ⟨b, hb, hfb⟩ := Finset.mem_image.1 hm
    rw [← h.inj (hS b hb) ha hfb]
    exact hb
  · exact Finset.mem_image_of_mem f

private theorem TrH.image_subset_iff (h : TrH G G' f g T) {S P : Finset V}
    (hS : ∀ v ∈ S, v ∈ T) (hP : ∀ v ∈ P, v ∈ T) : S.image f ⊆ P.image f ↔ S ⊆ P :=
  ⟨fun hsub a ha => (h.mem_image hP (hS a ha)).1 (hsub (Finset.mem_image_of_mem f ha)),
    fun hsub => Finset.image_subset_image hsub⟩

private theorem TrH.image_inj (h : TrH G G' f g T) {S P : Finset V}
    (hS : ∀ v ∈ S, v ∈ T) (hP : ∀ v ∈ P, v ∈ T) : S.image f = P.image f ↔ S = P := by
  constructor
  · intro he
    exact Finset.Subset.antisymm ((h.image_subset_iff hS hP).1 he.le)
      ((h.image_subset_iff hP hS).1 he.ge)
  · rintro rfl
    rfl

private theorem TrH.image_ssubset_iff (h : TrH G G' f g T) {S P : Finset V}
    (hS : ∀ v ∈ S, v ∈ T) (hP : ∀ v ∈ P, v ∈ T) : S.image f ⊂ P.image f ↔ S ⊂ P := by
  rw [Finset.ssubset_def, Finset.ssubset_def, h.image_subset_iff hS hP, h.image_subset_iff hP hS]

private theorem TrH.isVtx (h : TrH G G' f g T) {a : V} (ha : a ∈ T) :
    G'.IsVtx (f a) ↔ G.IsVtx a := by
  simp only [MGraph.IsVtx, h.int_eq, h.ext_eq, h.mem_image h.int_sub ha, h.mem_image h.ext_sub ha]

private theorem TrH.ends_image_iff (h : TrH G G' f g T) {S : Finset V} (hS : ∀ v ∈ S, v ∈ T)
    {e : E} (he : G.cls e ≠ none) :
    ((G'.ends (g e)).1 ∈ S.image f ∧ (G'.ends (g e)).2 ∈ S.image f) ↔
      ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S) := by
  obtain ⟨ha, hb⟩ := h.ends_mem e he
  rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only <;>
    rw [h.mem_image hS ha, h.mem_image hS hb]
  exact and_comm

private theorem TrH.cut_iff (h : TrH G G' f g T) {P : Finset V} (hP : ∀ v ∈ P, v ∈ T) {e : E}
    (he : G.cls e ≠ none) : G'.Cut (P.image f) (g e) ↔ G.Cut P e := by
  obtain ⟨ha, hb⟩ := h.ends_mem e he
  unfold MGraph.Cut
  rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only <;>
    rw [h.mem_image hP ha, h.mem_image hP hb]
  tauto

private theorem TrH.vtx_iff (h : TrH G G' f g T) {e : E} (he : G.cls e ≠ none) :
    (G'.IsVtx (G'.ends (g e)).1 ∧ G'.IsVtx (G'.ends (g e)).2) ↔
      (G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) := by
  obtain ⟨ha, hb⟩ := h.ends_mem e he
  rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only <;>
    rw [h.isVtx ha, h.isVtx hb]
  exact and_comm

private theorem TrH.crosses_fwd (h : TrH G G' f g T) {P : Finset V} (hP : ∀ v ∈ P, v ∈ T)
    {e : E} (hc : G.Crosses P e) : G'.Crosses (P.image f) (g e) := by
  obtain ⟨c1, c2, v1, v2, cu⟩ := hc
  have hv := (h.vtx_iff c1).2 ⟨v1, v2⟩
  exact ⟨by rw [h.cls_eq e c1]; exact c1, by rw [h.cls_eq e c1]; exact c2, hv.1, hv.2,
    (h.cut_iff hP c1).2 cu⟩

private theorem TrH.crosses_bwd (h : TrH G G' f g T) {P : Finset V} (hP : ∀ v ∈ P, v ∈ T)
    {e' : E'} (hc : G'.Crosses (P.image f) e') : ∃ e, g e = e' ∧ G.Crosses P e := by
  obtain ⟨e, he, rfl⟩ := h.surj e' hc.1
  obtain ⟨c1, c2, v1, v2, cu⟩ := hc
  rw [h.cls_eq e he] at c1 c2
  have hv := (h.vtx_iff he).1 ⟨v1, v2⟩
  exact ⟨e, rfl, c1, c2, hv.1, hv.2, (h.cut_iff hP he).1 cu⟩

private theorem TrH.iso_iff (h : TrH G G' f g T) {P : Finset V} (hP : ∀ v ∈ P, v ∈ T) :
    G'.IsIsolated (P.image f) ↔ G.IsIsolated P := by
  constructor
  · rintro ⟨hsub, e₁', e₂', hne, hc⟩
    obtain ⟨e₁, rfl, c₁⟩ := h.crosses_bwd hP ((hc e₁').2 (Or.inl rfl))
    obtain ⟨e₂, rfl, c₂⟩ := h.crosses_bwd hP ((hc e₂').2 (Or.inr rfl))
    refine ⟨?_, e₁, e₂, fun h' => hne (h' ▸ rfl), fun e => ⟨fun hce => ?_, ?_⟩⟩
    · rw [h.int_eq] at hsub
      exact (h.image_subset_iff hP h.int_sub).1 hsub
    · rcases (hc (g e)).1 (h.crosses_fwd hP hce) with he | he
      · exact Or.inl (h.ginj _ _ hce.1 c₁.1 he)
      · exact Or.inr (h.ginj _ _ hce.1 c₂.1 he)
    · rintro (rfl | rfl)
      · exact c₁
      · exact c₂
  · rintro ⟨hsub, e₁, e₂, hne, hc⟩
    have c₁ := (hc e₁).2 (Or.inl rfl)
    have c₂ := (hc e₂).2 (Or.inr rfl)
    refine ⟨?_, g e₁, g e₂, fun h' => hne (h.ginj _ _ c₁.1 c₂.1 h'), fun e' => ⟨fun hce => ?_, ?_⟩⟩
    · rw [h.int_eq]
      exact Finset.image_subset_image hsub
    · obtain ⟨e, rfl, hce2⟩ := h.crosses_bwd hP hce
      rcases (hc e).1 hce2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact h.crosses_fwd hP c₁
      · exact h.crosses_fwd hP c₂

private theorem TrH.pull (h : TrH G G' f g T) {S' : Finset V'} (hS' : S' ⊆ G'.int) :
    ∃ S, S ⊆ G.int ∧ S.image f = S' := by
  refine ⟨G.int.filter (fun v => f v ∈ S'), Finset.filter_subset _ _, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    exact (Finset.mem_filter.1 ha).2
  · intro hy
    have := hS' hy
    rw [h.int_eq] at this
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
    exact Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨ha, hy⟩)

private theorem TrH.dc (h : TrH G G' f g T) (hG : G.DC) : G'.DC := by
  classical
  obtain ⟨black, blue, hd, hbk, hbu, hsk, hsu⟩ := hG
  have pb : ∀ x ∈ black, G.cls x ≠ none := fun x hx => by rw [hbk x hx]; simp
  have pu : ∀ x ∈ blue, G.cls x ≠ none := fun x hx => by
    rcases hbu x hx with hc | hc | hc <;> rw [hc] <;> simp
  have hsp : ∀ B : Finset E, G.Spans B → G'.Spans (B.image g) := by
    intro B hB S' hS' hne hn
    obtain ⟨S, hSi, rfl⟩ := h.pull hS'
    have hST : ∀ v ∈ S, v ∈ T := fun v hv => h.int_sub v (hSi hv)
    rw [h.int_eq] at hn
    obtain ⟨x, hx, cx, h1, h2, cu⟩ := hB S hSi (Finset.image_nonempty.1 hne)
      (fun hsub => hn (Finset.image_subset_image hsub))
    have he := (h.ends_image_iff h.int_sub cx).2 ⟨h1, h2⟩
    rw [← h.int_eq] at he
    exact ⟨g x, Finset.mem_image_of_mem g hx, by rw [h.cls_eq x cx]; exact cx, he.1, he.2,
      (h.cut_iff hST cx).2 cu⟩
  refine ⟨black.image g, blue.image g, ?_, ?_, ?_, hsp black hsk, hsp blue hsu⟩
  · rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hy'
    rw [h.ginj _ _ (pu b hb) (pb a ha) hab] at hb
    exact Finset.disjoint_left.1 hd ha hb
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    rw [h.cls_eq a (pb a ha)]
    exact hbk a ha
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    rw [h.cls_eq a (pu a ha)]
    exact hbu a ha

private theorem TrH.intPlus_fwd (h : TrH G G' f g T) {x : E} (hx : G.IsIntPlus x) :
    G'.IsIntPlus (g x) := by
  have cx : G.cls x ≠ none := by rw [hx.1]; simp
  have he := (h.ends_image_iff h.int_sub cx).2 ⟨hx.2.1, hx.2.2⟩
  rw [← h.int_eq] at he
  exact ⟨by rw [h.cls_eq x cx]; exact hx.1, he.1, he.2⟩

private theorem TrH.intPlus_bwd (h : TrH G G' f g T) {x' : E'} (hx : G'.IsIntPlus x') :
    ∃ x, G.IsIntPlus x ∧ g x = x' := by
  obtain ⟨x, cx, rfl⟩ := h.surj x' (by rw [hx.1]; simp)
  have he : ((G'.ends (g x)).1 ∈ G.int.image f ∧ (G'.ends (g x)).2 ∈ G.int.image f) := by
    rw [← h.int_eq]
    exact ⟨hx.2.1, hx.2.2⟩
  have he' := (h.ends_image_iff h.int_sub cx).1 he
  exact ⟨x, ⟨by rw [← h.cls_eq x cx]; exact hx.1, he'.1, he'.2⟩, rfl⟩

private theorem TrH.convert [DecidableEq E] [DecidableEq E'] (h : TrH G G' f g T) {l : List E}
    (hl : ∀ x ∈ l, G.cls x ≠ none) : TrH (G.convert l) (G'.convert (l.map g)) f g T := by
  have hp : ∀ {F : Type} [DecidableEq F] (H : MGraph V' F) (L : List F) (x : F),
      (H.convert L).cls x ≠ none ↔ H.cls x ≠ none := by
    intro F _ H L x
    simp only [convert_cls']
    split_ifs with hc
    · simp [hc.2]
    · exact Iff.rfl
  have hp' : ∀ x, (G.convert l).cls x ≠ none ↔ G.cls x ≠ none := by
    intro x
    simp only [convert_cls']
    split_ifs with hc
    · simp [hc.2]
    · exact Iff.rfl
  refine ⟨h.inj, h.int_sub, h.ext_sub, fun e he => h.ends_mem e ((hp' e).1 he), h.int_eq,
    h.ext_eq, fun e₁ e₂ h₁ h₂ => h.ginj e₁ e₂ ((hp' e₁).1 h₁) ((hp' e₂).1 h₂),
    fun e he => ?_, fun e he => h.ends_eq e ((hp' e).1 he), fun e' he' => ?_⟩
  · have he' := (hp' e).1 he
    have hmem : g e ∈ l.map g ↔ e ∈ l := by
      constructor
      · intro hm
        obtain ⟨a, ha, hga⟩ := List.mem_map.1 hm
        rw [← h.ginj _ _ (hl a ha) he' hga]
        exact ha
      · exact List.mem_map_of_mem
    simp only [convert_cls', hmem, h.cls_eq e he']
  · obtain ⟨e, he, rfl⟩ := h.surj e' ((hp G' _ e').1 he')
    exact ⟨e, (hp' e).2 he, rfl⟩

private theorem TrH.erase [DecidableEq E] [DecidableEq E'] (h : TrH G G' f g T) {x : E}
    (hx : G.cls x ≠ none) : TrH (G.erase x) (G'.erase (g x)) f g T := by
  have hp : ∀ e, (G.erase x).cls e ≠ none ↔ e ≠ x ∧ G.cls e ≠ none := by
    intro e
    by_cases he : e = x
    · subst he
      simp
    · simp [he]
  refine ⟨h.inj, h.int_sub, h.ext_sub, fun e he => h.ends_mem e ((hp e).1 he).2, h.int_eq,
    h.ext_eq, fun e₁ e₂ h₁ h₂ => h.ginj e₁ e₂ ((hp e₁).1 h₁).2 ((hp e₂).1 h₂).2,
    fun e he => ?_, fun e he => h.ends_eq e ((hp e).1 he).2, fun e' he' => ?_⟩
  · obtain ⟨hne, he'⟩ := (hp e).1 he
    have hg : g e ≠ g x := fun hg => hne (h.ginj _ _ he' hx hg)
    simp [hg, hne, h.cls_eq e he']
  · have hne : e' ≠ g x := by
      rintro rfl
      simp at he'
    have he'' : G'.cls e' ≠ none := by simpa [hne] using he'
    obtain ⟨e, he, rfl⟩ := h.surj e' he''
    exact ⟨e, (hp e).2 ⟨fun h' => hne (h' ▸ rfl), he⟩, rfl⟩

private theorem TrH.induce [DecidableEq V] (h : TrH G G' f g T) {S : Finset V}
    (hS : ∀ v ∈ S, v ∈ T) : TrH (G.induce S) (G'.induce (S.image f)) f g T := by
  have hp : ∀ e, (G.induce S).cls e ≠ none ↔
      ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S) ∧ G.cls e ≠ none := by
    intro e
    simp only [induce_cls']
    split_ifs with hc <;> simp [hc]
  refine ⟨h.inj, fun v hv => hS v hv, fun v hv => by simp at hv,
    fun e he => h.ends_mem e ((hp e).1 he).2, rfl, by simp,
    fun e₁ e₂ h₁ h₂ => h.ginj e₁ e₂ ((hp e₁).1 h₁).2 ((hp e₂).1 h₂).2, fun e he => ?_,
    fun e he => h.ends_eq e ((hp e).1 he).2, fun e' he' => ?_⟩
  · obtain ⟨hin, he'⟩ := (hp e).1 he
    have := (h.ends_image_iff hS he').2 hin
    simp only [induce_cls', this, hin, h.cls_eq e he']
  · simp only [induce_cls'] at he'
    split_ifs at he' with hin
    · obtain ⟨e, he, rfl⟩ := h.surj _ he'
      exact ⟨e, (hp e).2 ⟨(h.ends_image_iff hS he).1 hin, he⟩, rfl⟩
    · exact absurd rfl he'

private theorem TrH.outer_eq [DecidableEq V] (h : TrH G G' f g T) {P : Finset V}
    (hP : ∀ v ∈ P, v ∈ T) {e : E} (he : G.cls e ≠ none) (hc : G.Cut P e) :
    G'.outer (P.image f) (g e) = f (G.outer P e) := by
  obtain ⟨ha, hb⟩ := h.ends_mem e he
  unfold MGraph.outer
  rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only
  · have hm := h.mem_image hP ha
    simp only [hm]
    split_ifs <;> rfl
  · have hm := h.mem_image hP hb
    simp only [hm]
    rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> simp [c1, c2]

private theorem TrH.replace [DecidableEq V] [DecidableEq E] [DecidableEq E']
    (h : TrH G G' f g T) {S P : Finset V} (hS : ∀ v ∈ S, v ∈ T) (hP : ∀ v ∈ P, v ∈ T)
    {e₁ e₂ : E} (c₁ : G.cls e₁ ≠ none) (c₂ : G.cls e₂ ≠ none) (k₁ : G.Cut P e₁)
    (k₂ : G.Cut P e₂) :
    TrH (G.replace S P e₁ e₂) (G'.replace (S.image f) (P.image f) (g e₁) (g e₂)) f g T := by
  have hSP : ∀ v ∈ S \ P, v ∈ T := fun v hv => hS v (Finset.mem_sdiff.1 hv).1
  have hI := h.induce hSP
  have himg : S.image f \ P.image f = (S \ P).image f := by
    ext y
    constructor
    · intro hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.1 hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy1
      exact Finset.mem_image_of_mem f
        (Finset.mem_sdiff.2 ⟨ha, fun haP => hy2 (Finset.mem_image_of_mem f haP)⟩)
    · intro hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨ha1, ha2⟩ := Finset.mem_sdiff.1 ha
      exact Finset.mem_sdiff.2 ⟨Finset.mem_image_of_mem f ha1,
        fun hm => ha2 ((h.mem_image hP (hS a ha1)).1 hm)⟩
  have hp : ∀ x, (G.replace S P e₁ e₂).cls x ≠ none →
      x = e₁ ∨ (x ≠ e₁ ∧ x ≠ e₂ ∧ (G.induce (S \ P)).cls x ≠ none) := by
    intro x hx
    simp only [replace_cls'] at hx
    split_ifs at hx with h1 h2
    · exact Or.inl h1
    · exact absurd rfl hx
    · exact Or.inr ⟨h1, h2, hx⟩
  have hpG : ∀ x, (G.replace S P e₁ e₂).cls x ≠ none → G.cls x ≠ none := by
    intro x hx
    rcases hp x hx with rfl | ⟨-, -, hx⟩
    · exact c₁
    · simp only [induce_cls'] at hx
      split_ifs at hx
      · exact hx
      · exact absurd rfl hx
  have ho₁ : G.outer P e₁ = (G.ends e₁).1 ∨ G.outer P e₁ = (G.ends e₁).2 := by
    unfold MGraph.outer
    split_ifs <;> simp
  have ho₂ : G.outer P e₂ = (G.ends e₂).1 ∨ G.outer P e₂ = (G.ends e₂).2 := by
    unfold MGraph.outer
    split_ifs <;> simp
  refine ⟨h.inj, fun v hv => hSP v hv, fun v hv => by simp at hv, fun x hx => ?_,
    by simp [himg], by simp, fun x y hx hy => h.ginj x y (hpG x hx) (hpG y hy), fun x hx => ?_,
    fun x hx => ?_, fun e' he' => ?_⟩
  · by_cases hx1 : x = e₁
    · subst hx1
      simp only [replace_ends', ite_true]
      constructor
      · rcases ho₁ with h' | h' <;> rw [h']
        · exact (h.ends_mem _ c₁).1
        · exact (h.ends_mem _ c₁).2
      · rcases ho₂ with h' | h' <;> rw [h']
        · exact (h.ends_mem _ c₂).1
        · exact (h.ends_mem _ c₂).2
    · simp only [replace_ends', hx1, ite_false]
      exact h.ends_mem x (hpG x hx)
  · rcases hp x hx with rfl | ⟨hx1, hx2, hxi⟩
    · simp
    · have hg1 : g x ≠ g e₁ := fun hg => hx1 (h.ginj _ _ (hpG x hx) c₁ hg)
      have hg2 : g x ≠ g e₂ := fun hg => hx2 (h.ginj _ _ (hpG x hx) c₂ hg)
      simp only [replace_cls', hg1, hg2, hx1, hx2, ite_false, himg]
      exact hI.cls_eq x hxi
  · by_cases hx1 : x = e₁
    · subst hx1
      left
      simp only [replace_ends', ite_true, h.outer_eq hP c₁ k₁, h.outer_eq hP c₂ k₂]
    · have hg1 : g x ≠ g e₁ := fun hg => hx1 (h.ginj _ _ (hpG x hx) c₁ hg)
      simp only [replace_ends', hg1, hx1, ite_false]
      exact h.ends_eq x (hpG x hx)
  · by_cases h1 : e' = g e₁
    · subst h1
      exact ⟨e₁, by simp, rfl⟩
    · by_cases h2 : e' = g e₂
      · subst h2
        simp [h1] at he'
      · simp only [replace_cls', h1, h2, ite_false, himg] at he'
        obtain ⟨x, hx, rfl⟩ := hI.surj _ he'
        have hx1 : x ≠ e₁ := fun hx' => h1 (hx' ▸ rfl)
        have hx2 : x ≠ e₂ := fun hx' => h2 (hx' ▸ rfl)
        exact ⟨x, by simp only [replace_cls', hx1, hx2, ite_false]; exact hx, rfl⟩

private theorem TrH.preDet [DecidableEq E] [DecidableEq E'] (h : TrH G G' f g T)
    (hG : G.PreDet) : G'.PreDet := by
  obtain ⟨hd, l, hnd, hmem, hr⟩ := hG
  have pl : ∀ x ∈ l, G.cls x ≠ none := fun x hx => by rw [((hmem x).1 hx).1]; simp
  refine ⟨h.dc hd, l.map g, hnd.map_on fun x hx y hy hxy => h.ginj x y (pl x hx) (pl y hy) hxy,
    fun e' => ⟨fun he' => ?_, fun he' => ?_⟩, fun j hj => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
    exact h.intPlus_fwd ((hmem x).1 hx)
  · obtain ⟨x, hx, rfl⟩ := h.intPlus_bwd he'
    exact List.mem_map_of_mem ((hmem x).2 hx)
  · have hj' : j < l.length := by simpa using hj
    have hc := h.convert (l := l.take j) (fun x hx => pl x (List.mem_of_mem_take hx))
    obtain ⟨c, d1, d2⟩ := hr j hj'
    have cx : (G.convert (l.take j)).cls l[j] ≠ none := by rw [c]; simp
    rw [List.getElem_map, ← List.map_take]
    exact ⟨by rw [hc.cls_eq _ cx]; exact c, hc.dc d1, (hc.erase cx).dc d2⟩

private theorem TrH.spd [DecidableEq V] [DecidableEq E] [DecidableEq E'] (h : TrH G G' f g T)
    (hG : G.SPD) : G'.SPD := by
  obtain ⟨hdc, hch, h3, h4⟩ := hG
  have hT : ∀ S, S ⊆ G.int → ∀ v ∈ S, v ∈ T := fun S hS v hv => h.int_sub v (hS hv)
  have htop : ∀ S, S ⊆ G.int → (G'.IsoOrTop (S.image f) ↔ G.IsoOrTop S) := by
    intro S hS
    unfold MGraph.IsoOrTop
    rw [h.int_eq, h.image_inj (hT S hS) h.int_sub, h.iso_iff (hT S hS)]
  have hprop : ∀ S Q, S ⊆ G.int → Q ⊆ G.int →
      (G'.IsProperIso (S.image f) (Q.image f) ↔ G.IsProperIso S Q) := by
    intro S Q hS hQ
    unfold MGraph.IsProperIso
    rw [h.iso_iff (hT Q hQ), h.image_ssubset_iff (hT Q hQ) (hT S hS)]
  have hsub : ∀ S', G'.IsoOrTop S' → S' ⊆ G'.int := by
    rintro S' (rfl | hS')
    · exact le_rfl
    · exact hS'.1
  refine ⟨h.dc hdc, ?_, ?_, ?_⟩
  · intro P' Q' hP' hQ'
    obtain ⟨P, hP, rfl⟩ := h.pull hP'.1.1
    obtain ⟨Q, hQ, rfl⟩ := h.pull hQ'.1.1
    rw [h.int_eq] at hP' hQ'
    rcases hch P Q ((hprop _ _ le_rfl hP).1 hP') ((hprop _ _ le_rfl hQ).1 hQ') with hPQ | hPQ
    · exact Or.inl (Finset.image_subset_image hPQ)
    · exact Or.inr (Finset.image_subset_image hPQ)
  · intro S' hS' hno
    obtain ⟨S, hS, rfl⟩ := h.pull (hsub S' hS')
    refine (h.induce (hT S hS)).preDet (h3 S ((htop S hS).1 hS') fun Q hQ => ?_)
    exact hno (Q.image f) ((hprop S Q hS (hQ.2.subset.trans hS)).2 hQ)
  · intro S' P' e₁' e₂' hS' hmax hne c₁ c₂
    obtain ⟨S, hS, rfl⟩ := h.pull (hsub S' hS')
    obtain ⟨P, hP, rfl⟩ := h.pull (hmax.1.2.subset.trans (hsub _ hS'))
    obtain ⟨e₁, rfl, d₁⟩ := h.crosses_bwd (hT P hP) c₁
    obtain ⟨e₂, rfl, d₂⟩ := h.crosses_bwd (hT P hP) c₂
    have hmaxG : G.IsMaximalIso S P := by
      refine ⟨(hprop S P hS hP).1 hmax.1, fun Q hQ hPQ => ?_⟩
      have hQi : Q ⊆ G.int := hQ.2.subset.trans hS
      exact hmax.2 (Q.image f) ((hprop S Q hS hQi).2 hQ)
        ((h.image_ssubset_iff (hT P hP) (hT Q hQi)).2 hPQ)
    have hne' : e₁ ≠ e₂ := fun he => hne (he ▸ rfl)
    exact (h.replace (hT S hS) (hT P hP) d₁.1 d₂.1 d₁.2.2.2.2 d₂.2.2.2.2).preDet
      (h4 S P e₁ e₂ ((htop S hS).1 hS') hmaxG hne' d₁ d₂)

end

/-- The inverse change of names. -/
private theorem TrH.symm [DecidableEq V] [DecidableEq V'] [Nonempty V] [Nonempty E]
    {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'} {T : Set V}
    (h : TrH G G' f g T) :
    TrH G' G (Function.invFunOn f T) (Function.invFunOn g {e | G.cls e ≠ none}) (f '' T) := by
  have hl : ∀ a ∈ T, Function.invFunOn f T (f a) = a := fun a ha => h.inj.leftInvOn_invFunOn ha
  have hginj : Set.InjOn g {e | G.cls e ≠ none} := fun a ha b hb hab => h.ginj a b ha hb hab
  have hgl : ∀ e, G.cls e ≠ none → Function.invFunOn g {e | G.cls e ≠ none} (g e) = e :=
    fun e he => hginj.leftInvOn_invFunOn he
  have hgp : ∀ e', G'.cls e' ≠ none →
      ∃ e, G.cls e ≠ none ∧ g e = e' ∧ Function.invFunOn g {e | G.cls e ≠ none} e' = e := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := h.surj e' he'
    exact ⟨e, he, rfl, hgl e he⟩
  have himg : ∀ S : Finset V, (∀ v ∈ S, v ∈ T) →
      (S.image f).image (Function.invFunOn f T) = S := by
    intro S hS
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rw [hl a (hS a ha)]
      exact ha
    · intro hv
      exact ⟨f v, ⟨v, hv, rfl⟩, hl v (hS v hv)⟩
  refine ⟨Function.invFunOn_injOn_image f T, fun v hv => ?_, fun v hv => ?_, fun e' he' => ?_,
    ?_, ?_, fun e₁' e₂' h₁ h₂ hg => ?_, fun e' he' => ?_, fun e' he' => ?_, fun e he => ?_⟩
  · rw [h.int_eq] at hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨a, h.int_sub a ha, rfl⟩
  · rw [h.ext_eq] at hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨a, h.ext_sub a ha, rfl⟩
  · obtain ⟨e, he, rfl, -⟩ := hgp e' he'
    obtain ⟨ha, hb⟩ := h.ends_mem e he
    rcases h.ends_eq e he with hE | hE <;> rw [hE]
    · exact ⟨⟨_, ha, rfl⟩, ⟨_, hb, rfl⟩⟩
    · exact ⟨⟨_, hb, rfl⟩, ⟨_, ha, rfl⟩⟩
  · rw [h.int_eq, himg _ h.int_sub]
  · rw [h.ext_eq, himg _ h.ext_sub]
  · obtain ⟨a, -, rfl, ha⟩ := hgp e₁' h₁
    obtain ⟨b, -, rfl, hb⟩ := hgp e₂' h₂
    rw [ha, hb] at hg
    rw [hg]
  · obtain ⟨e, he, rfl, hge⟩ := hgp e' he'
    rw [hge, h.cls_eq e he]
  · obtain ⟨e, he, rfl, hge⟩ := hgp e' he'
    obtain ⟨ha, hb⟩ := h.ends_mem e he
    rw [hge]
    rcases h.ends_eq e he with hE | hE <;> rw [hE] <;> dsimp only <;> rw [hl _ ha, hl _ hb]
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact ⟨g e, by rw [h.cls_eq e he]; exact he, hgl e he⟩

/-- A change of names does not change the sequentially pre-deterministic property. -/
private theorem TrH.spd_iff [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
    {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'} {T : Set V}
    (h : TrH G G' f g T) : G'.SPD ↔ G.SPD := by
  refine ⟨fun h' => ?_, h.spd⟩
  by_cases hE : Nonempty E
  · obtain ⟨e₀⟩ := hE
    have : Nonempty E := ⟨e₀⟩
    have : Nonempty V := ⟨(G.ends e₀).1⟩
    exact h.symm.spd h'
  · have hn : ∀ e, G.cls e = none := fun e => absurd ⟨e⟩ hE
    have hn' : ∀ e', G'.cls e' = none := by
      intro e'
      by_contra hc
      obtain ⟨e, -, -⟩ := h.surj e' hc
      exact hE ⟨e⟩
    have hcard : G'.int.card = G.int.card := by
      rw [h.int_eq]
      exact Finset.card_image_of_injOn (h.inj.mono fun v hv => h.int_sub v hv)
    rw [spd_iff_of_noEdge hn', hcard] at h'
    exact (spd_iff_of_noEdge hn).2 h'

end Transport

section Operations

variable {V E : Type}

/-! ### The operations on one edge -/

/-- Moving an absent or red solid edge and making it absent or red solid does not change the
sequentially pre-deterministic property. -/
private theorem spd_setEdge_red [DecidableEq V] [DecidableEq E] {G : MGraph V E} {e : E}
    {u v : V} {c : Option MClass} (he : G.cls e = none ∨ G.cls e = some .minus)
    (hc : c = none ∨ c = some .minus) : (G.setEdge e u v c).SPD ↔ G.SPD := by
  have hs : Sim G (G.setEdge e u v c) := by
    refine ⟨rfl, rfl, fun x => ?_⟩
    by_cases hx : x = e
    · subst hx
      exact Or.inr (Or.inl ⟨he, by simpa using hc⟩)
    · exact Or.inl ⟨by simp [hx], by simp [hx]⟩
  exact ⟨hs.symm.spd, hs.spd⟩

/-- On a graph whose internal and external vertices are distinct, recolouring an edge from an
internal to an external vertex among blue solid, diffusive and dotted does not change the
sequentially pre-deterministic property. -/
private theorem spd_recolor_ext [DecidableEq V] [DecidableEq E] {G : MGraph V E} {e : E}
    {c : MClass} (hd : Disjoint G.int G.ext)
    (he : G.cls e = some .plus ∨ G.cls e = some .diff ∨ G.cls e = some .dot)
    (hc : c = .plus ∨ c = .diff ∨ c = .dot) (h2 : (G.ends e).2 ∈ G.ext) :
    (G.recolor e (some c)).SPD ↔ G.SPD := by
  have hx : (G.ends e).2 ∉ G.int := fun h => Finset.disjoint_left.1 hd h h2
  have hs : Sim G (G.recolor e (some c)) := by
    refine ⟨rfl, rfl, fun x => ?_⟩
    by_cases hxe : x = e
    · subst hxe
      refine Or.inr (Or.inr ⟨rfl, Or.inr hx, ?_, ?_⟩)
      · rcases he with h | h | h <;> rw [h] <;> simp
      · rcases hc with h | h | h <;> subst h <;> simp
    · exact Or.inl ⟨by simp [hxe], rfl⟩
  exact ⟨hs.symm.spd, hs.spd⟩

/-- Changing an internal blue solid edge into a diffusive edge keeps the sequentially
pre-deterministic property. -/
private theorem spd_recolor_conv [DecidableEq V] [DecidableEq E] {G : MGraph V E} {e : E}
    (hp : G.IsIntPlus e) (hs : G.SPD) : (G.recolor e (some .diff)).SPD := by
  set B := G.recolor e (some .diff) with hB
  have hcr : ∀ P x, B.Crosses P x ↔ G.Crosses P x := by
    intro P x
    by_cases hx : x = e
    · subst hx
      simp [B, MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, hp.1]
    · simp [B, MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, hx]
  have hoff : ∀ x, x ≠ e → B.cls x = G.cls x := fun x hx => by simp [B, hx]
  -- `H'` is `H`, or `H` with its internal blue solid edge `e` changed into a diffusive edge
  have hpre : ∀ H H' : MGraph V E, (H' = H ∨ (H.IsIntPlus e ∧ H' = H.recolor e (some .diff))) →
      H.PreDet → H'.PreDet := by
    rintro H H' (rfl | ⟨hi, rfl⟩) h
    · exact h
    · exact preDet_conv hi h
  refine spd_congr (A := G) (B := B) rfl (fun P _ _ => isIso_congr (A := G) (B := B) rfl (hcr P))
    (fun P x _ _ _ h => (hcr P x).1 h)
    (dc_conv_off (A := G) (B := B) (e := e) rfl rfl hoff (by simp [B]) (Or.inl hp.1))
    (fun S _ h => hpre _ _ ?_ h) (fun S P e₁ e₂ _ _ _ _ _ _ h => hpre _ _ ?_ h) hs
  · by_cases hin : (G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S
    · refine Or.inr ⟨⟨by simp [hin, hp.1], hin.1, hin.2⟩, mg_ext rfl rfl rfl (funext fun x => ?_)⟩
      by_cases hx : x = e
      · subst hx
        simp [B, hin]
      · simp [B, hx]
    · refine Or.inl (mg_ext rfl rfl rfl (funext fun x => ?_))
      by_cases hx : x = e
      · subst hx
        simp [B, hin]
      · simp [B, hx]
  · by_cases h12 : e = e₁ ∨ e = e₂
    · refine Or.inl (mg_ext rfl rfl rfl (funext fun x => ?_))
      by_cases hx1 : x = e₁
      · simp [hx1]
      · by_cases hx2 : x = e₂
        · simp [hx2]
        · have hxe : x ≠ e := by
            rintro rfl
            rcases h12 with h | h
            · exact hx1 h
            · exact hx2 h
          simp [B, hx1, hx2, hxe]
    · rw [not_or] at h12
      by_cases hin : (G.ends e).1 ∈ S \ P ∧ (G.ends e).2 ∈ S \ P
      · refine Or.inr ⟨⟨by simp [h12.1, h12.2, hin, hp.1], by simpa [h12.1] using hin.1,
          by simpa [h12.1] using hin.2⟩, mg_ext rfl rfl rfl (funext fun x => ?_)⟩
        by_cases hx : x = e
        · subst hx
          simp [B, hin, h12.1, h12.2]
        · simp [B, hx]
      · refine Or.inl (mg_ext rfl rfl rfl (funext fun x => ?_))
        by_cases hx : x = e
        · subst hx
          simp only [Finset.mem_sdiff] at hin
          simp [B, hin, h12.1, h12.2]
        · simp [B, hx]

/-- An edge crosses a set after another edge is removed iff it is not the removed edge and
crosses the set before. -/
private theorem crosses_erase_iff [DecidableEq E] {G : MGraph V E} {e x : E} {P : Finset V} :
    (G.erase e).Crosses P x ↔ x ≠ e ∧ G.Crosses P x := by
  by_cases hx : x = e
  · subst hx
    simp [MGraph.Crosses]
  · simp [MGraph.Crosses, MGraph.IsVtx, MGraph.Cut, hx]

/-- On a graph whose internal and external vertices are distinct, an edge from an internal vertex
`v` to an external vertex, neither absent nor red solid, can be removed when another such edge
from `v` to an external vertex is present. -/
private theorem spd_erase_ext [DecidableEq V] [DecidableEq E] {G : MGraph V E} {e e' : E}
    (hne : e ≠ e') (hd : Disjoint G.int G.ext) (he : G.cls e ≠ none ∧ G.cls e ≠ some .minus)
    (h1 : (G.ends e).1 ∈ G.int) (h2 : (G.ends e).2 ∈ G.ext)
    (he' : G.cls e' ≠ none ∧ G.cls e' ≠ some .minus) (h1' : (G.ends e').1 = (G.ends e).1)
    (h2' : (G.ends e').2 ∈ G.ext) (hs : G.SPD) : (G.erase e).SPD := by
  have hx : (G.ends e).2 ∉ G.int := fun h => Finset.disjoint_left.1 hd h h2
  have hx' : (G.ends e').2 ∉ G.int := fun h => Finset.disjoint_left.1 hd h h2'
  -- a proper subset of the internal vertices containing `v` is isolated in neither graph
  have key : ∀ P, P ⊆ G.int → P ≠ G.int → (G.ends e).1 ∈ P →
      ¬ G.IsIsolated P ∧ ¬ (G.erase e).IsIsolated P := by
    intro P hP hPn hv
    obtain ⟨black, blue, hdj, hbk, hbu, hsk, hsu⟩ := hs.1
    have hn : ¬ G.int ⊆ P := fun h => hPn (Finset.Subset.antisymm hP h)
    obtain ⟨b, hb, cb, b1, b2, kb⟩ := hsk P hP ⟨_, hv⟩ hn
    obtain ⟨u, hu, cu, u1, u2, ku⟩ := hsu P hP ⟨_, hv⟩ hn
    have hbu' : b ≠ u := fun h => Finset.disjoint_left.1 hdj hb (h ▸ hu)
    have hbe' : b ≠ e' := fun h => hx' (h ▸ b2)
    have hue' : u ≠ e' := fun h => hx' (h ▸ u2)
    have hbe : b ≠ e := fun h => hx (h ▸ b2)
    have hue : u ≠ e := fun h => hx (h ▸ u2)
    have Cb : G.Crosses P b := ⟨cb, by rw [hbk b hb]; simp, Or.inl b1, Or.inl b2, kb⟩
    have Cu : G.Crosses P u :=
      ⟨cu, by rcases hbu u hu with h | h | h <;> rw [h] <;> simp, Or.inl u1, Or.inl u2, ku⟩
    have Ce' : G.Crosses P e' := ⟨he'.1, he'.2, Or.inl (h1' ▸ h1), Or.inr h2',
      Or.inl ⟨h1' ▸ hv, fun h => hx' (hP h)⟩⟩
    exact ⟨not_iso_of_three hbu' hbe' hue' Cb Cu Ce',
      not_iso_of_three hbu' hbe' hue' (crosses_erase_iff.2 ⟨hbe, Cb⟩)
        (crosses_erase_iff.2 ⟨hue, Cu⟩) (crosses_erase_iff.2 ⟨hne.symm, Ce'⟩)⟩
  have hcr : ∀ P x, P ⊆ G.int → (G.ends e).1 ∉ P → ((G.erase e).Crosses P x ↔ G.Crosses P x) := by
    intro P x hP hv
    rw [crosses_erase_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h.2.2.2.2 with ⟨a, -⟩ | ⟨-, a⟩
      · exact hv a
      · exact hx (hP a)
  have hnone : ∀ S, S ⊆ G.int → (G.induce S).cls e = none := by
    intro S hS
    have : ¬ ((G.ends e).1 ∈ S ∧ (G.ends e).2 ∈ S) := fun h => hx (hS h.2)
    simp [this]
  refine spd_congr (A := G) (B := G.erase e) rfl (fun P hP hPn => ?_)
    (fun P x _ _ _ h => (crosses_erase_iff.1 h).2) (dc_mono rfl (fun x _ hx2 _ => ?_))
    (fun S hS h => ?_) (fun S P e₁ e₂ hS hPS hP _ c₁ c₂ h => ?_) hs
  · by_cases hv : (G.ends e).1 ∈ P
    · exact ⟨fun h => absurd h (key P hP hPn hv).2, fun h => absurd h (key P hP hPn hv).1⟩
    · exact isIso_congr (A := G) (B := G.erase e) rfl fun x => hcr P x hP hv
  · have hxe : x ≠ e := by
      rintro rfl
      exact hx hx2
    rw [erase_cls', erase_ends', Function.update_of_ne hxe]
    exact ⟨fun hc => ⟨hc, rfl⟩, fun hc => ⟨by rcases hc with hc | hc <;> simp [hc], rfl⟩⟩
  · rw [induce_erase', erase_of_none _ (hnone S hS)]
    exact h
  · have hSi : S ⊆ G.int := hS
    have hPi : P ⊆ G.int := hPS.subset.trans hSi
    have hPn : P ≠ G.int := by
      rintro rfl
      exact (Finset.ssubset_iff_subset_ne.1 hPS).2 (Finset.Subset.antisymm hPS.subset hSi)
    have hv : (G.ends e).1 ∉ P := fun hv => (key P hPi hPn hv).1 hP
    have hne1 : e ≠ e₁ := by
      rintro rfl
      exact (crosses_erase_iff.1 ((hcr P e hPi hv).2 c₁)).1 rfl
    have hne2 : e ≠ e₂ := by
      rintro rfl
      exact (crosses_erase_iff.1 ((hcr P e hPi hv).2 c₂)).1 rfl
    rw [replace_erase' G S P hne1 hne2, erase_of_none]
    · exact h
    · simp only [replace_cls', hne1, hne2, ite_false]
      exact hnone (S \ P) (fun v hv' => hSi (Finset.mem_sdiff.1 hv').1)

end Operations

/-- The sequentially pre-deterministic property is kept by a change of the names of the
vertices and of the present edges (`MGraph.Transported`). -/
theorem MGraph.spd_transport :
  ∀ (V E V' E' : Type) [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
    (G : MGraph V E) (G' : MGraph V' E'), G.Transported G' → (G'.SPD ↔ G.SPD) := by
  intro V E V' E' _ _ _ _ G G' ⟨f, g, hg, hf, hint, hext, hv, hc, he, hs⟩
  refine TrH.spd_iff (T := ↑G.int ∪ ↑G.ext) ⟨hf, fun v hv => Or.inl hv, fun v hv => Or.inr hv,
    fun e he' => ⟨(hv e he').1, (hv e he').2⟩, hint, hext, hg, hc, he, fun e' he' => ?_⟩
  by_contra hn
  push Not at hn
  exact he' (hs e' fun e h1 h2 => hn e h1 h2)

/-- A blue solid loop at an internal vertex, added to a graph where its edge is absent,
does not change the sequentially pre-deterministic property. -/
theorem MGraph.spd_loop :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E) (v : V),
    G.cls e = none → v ∈ G.int → ((G.setEdge e v v (some .plus)).SPD ↔ G.SPD) := by
  intro V E _ _ G e v he _
  have h1 : (G.setEdge e v v (some .plus)).erase e = G.setEdge e v v none :=
    mg_ext rfl rfl rfl (by simp)
  rw [← spd_erase_loop (G := G.setEdge e v v (some .plus)) (e := e) (by simp), h1]
  exact spd_setEdge_red (Or.inl he) (Or.inl rfl)

/-- Removing a loop does not change the sequentially pre-deterministic property: a loop crosses no
cut and joins no two distinct vertices, so the doubly connected property, the isolated subsets,
the induced and replaced subgraphs of [II, Def 5.9 (iii)] (up to the loop) and the
pre-deterministic orders (up to the loop, which is redundant whenever it is blue) are
unchanged. -/
theorem MGraph.spd_unloop :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E),
    (G.ends e).1 = (G.ends e).2 → ((G.erase e).SPD ↔ G.SPD) := by
  intro V E _ _ G e hl
  exact spd_erase_loop hl

/-- Moving an edge that is absent or red, and making it absent or red, does not change the
sequentially pre-deterministic property: red solid edges are in no cut, net or pre-deterministic
order. -/
theorem MGraph.spd_red :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E) (u v : V)
    (c : Option MClass), (G.cls e = none ∨ G.cls e = some .minus) → (c = none ∨ c = some .minus) →
    ((G.setEdge e u v c).SPD ↔ G.SPD) := by
  intro V E _ _ G e u v c he hc
  exact spd_setEdge_red he hc

/-- On a graph whose internal and external vertices are distinct, recolouring an edge from an
internal to an external vertex among blue, diffusive and dotted does not change the sequentially
pre-deterministic property. -/
theorem MGraph.spd_ext :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E) (c : MClass),
    Disjoint G.int G.ext →
    (G.cls e = some .plus ∨ G.cls e = some .diff ∨ G.cls e = some .dot) →
    (c = .plus ∨ c = .diff ∨ c = .dot) → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.ext →
    ((G.recolor e (some c)).SPD ↔ G.SPD) := by
  intro V E _ _ G e c hd he hc _ h2
  exact spd_recolor_ext hd he hc h2

/-- Changing an internal blue solid edge into a diffusive edge keeps the sequentially
pre-deterministic property. -/
theorem MGraph.spd_conv :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e : E),
    G.IsIntPlus e → G.SPD → (G.recolor e (some .diff)).SPD := by
  intro V E _ _ G e hp hs
  exact spd_recolor_conv hp hs

/-- [II, Lemma 5.12 (v)] for a diffusive edge: on a graph without ghost edges whose internal and
external vertices are distinct, a diffusive edge from an internal to an external vertex replaced
by a diffusive edge to an internal vertex `w` and a blue or dotted edge from `w` to the external
vertex keeps the sequentially pre-deterministic property. -/
theorem MGraph.spd_splitExt :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e e' : E) (w : V) (c : MClass),
    Disjoint G.int G.ext → (∀ e₀ : E, G.cls e₀ ≠ some .ghost) → G.SPD → G.cls e = some .diff →
    (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.ext → e ≠ e' → G.cls e' = none → w ∈ G.int →
    (c = .plus ∨ c = .dot) → ((G.split e e' w).recolor e' (some c)).SPD := by
  intro V E _ _ G e e' w c hd hng hs he h1 h2 hne he' hw hc
  have hne' : e' ≠ e := Ne.symm hne
  -- the diffusive edge `e` recoloured blue solid
  have s1 : (G.recolor e (some .plus)).SPD :=
    (spd_recolor_ext hd (Or.inr (Or.inl he)) (Or.inl rfl) h2).2 hs
  have hng1 : ∀ e₀ : E, (G.recolor e (some .plus)).cls e₀ ≠ some .ghost := by
    intro e₀
    by_cases h0 : e₀ = e
    · subst h0
      simp
    · simpa [h0] using hng e₀
  -- operation (B) on the blue solid edge `e` through `w`
  have s2 : ((G.recolor e (some .plus)).split e e' w).SPD :=
    MGraph.spd_split _ _ _ e e' w hng1 s1 (by simp) (Or.inl h1) (Or.inr h2) (Or.inl h1) hne
      (by simp [hne', he']) hw
  -- the new edge `e'` from `w` to the external vertex recoloured blue solid or dotted
  have s3 : (((G.recolor e (some .plus)).split e e' w).recolor e' (some c)).SPD :=
    (spd_recolor_ext (G := (G.recolor e (some .plus)).split e e' w) hd (Or.inl (by simp))
      (by rcases hc with rfl | rfl <;> simp) (by simpa [hne'] using h2)).2 s2
  -- the internal edge `e` from `v` to `w` changed into a diffusive edge
  have s4 : ((((G.recolor e (some .plus)).split e e' w).recolor e' (some c)).recolor e
      (some .diff)).SPD :=
    spd_recolor_conv ⟨by simp [hne], by simpa using h1, by simpa using hw⟩ s3
  have heq : (((G.recolor e (some .plus)).split e e' w).recolor e' (some c)).recolor e
      (some .diff) = (G.split e e' w).recolor e' (some c) := by
    refine mg_ext rfl rfl rfl (funext fun x => ?_)
    by_cases hx : x = e
    · subst hx
      simp [hne, he]
    · by_cases hx' : x = e'
      · subst hx'
        simp [hne']
      · simp [hx, hx']
  rw [← heq]
  exact s4

/-- On a graph whose internal and external vertices are distinct, an edge from an internal vertex
`v` to an external vertex, neither absent nor red, can be removed when another such edge from `v`
to an external vertex is present: every proper subset containing `v` keeps three or more edges to
its complement. -/
theorem MGraph.spd_dropExt :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G : MGraph V E) (e e' : E), e ≠ e' →
    Disjoint G.int G.ext →
    (G.cls e ≠ none ∧ G.cls e ≠ some .minus) → (G.ends e).1 ∈ G.int → (G.ends e).2 ∈ G.ext →
    (G.cls e' ≠ none ∧ G.cls e' ≠ some .minus) → (G.ends e').1 = (G.ends e).1 →
    (G.ends e').2 ∈ G.ext → G.SPD → (G.erase e).SPD := by
  intro V E _ _ G e e' hne hd he h1 h2 he' h1' h2' hs
  exact spd_erase_ext hne hd he h1 h2 he' h1' h2' hs

/-- The operations `MGraph.CarStep` keep the sequentially pre-deterministic property on graphs
without ghost edges whose internal and external vertices are distinct, create no ghost edge and
keep the internal and external vertices distinct. -/
theorem MGraph.carStep_spd :
  ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (G G' : MGraph V E), MGraph.CarStep G G' →
    Disjoint G.int G.ext → (∀ e₀ : E, G.cls e₀ ≠ some .ghost) → G.SPD →
    G'.SPD ∧ (∀ e₀ : E, G'.cls e₀ ≠ some .ghost) ∧ Disjoint G'.int G'.ext := by
  intro V E _ _ G G' h hd hng hs
  cases h with
  | merge M M' hM hM' =>
    refine ⟨MGraph.spd_merge _ _ G M M' hng hs hM hM', fun e₀ => hng e₀, ?_⟩
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [MGraph.merge, MGraph.mapV, Finset.mem_image] at hy hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, hab⟩ := hy'
    have hbM' : b ≠ M' := fun h => Finset.disjoint_left.1 hd hM' (h ▸ hb)
    simp only [hbM', ↓reduceIte] at hab
    subst hab
    by_cases haM : a = M'
    · simp only [haM, ↓reduceIte] at hb
      exact Finset.disjoint_left.1 hd hM hb
    · simp only [haM, ↓reduceIte] at hb
      exact Finset.disjoint_left.1 hd ha hb
  | split e e' w he h1 h2 hi hne he' hw =>
    refine ⟨MGraph.spd_split _ _ G e e' w hng hs he h1 h2 hi hne he' hw, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e'
    · simp [h0, he]
    · simpa [h0] using hng e₀
  | splitExt e e' w c he h1 h2 hne he' hw hc =>
    refine ⟨MGraph.spd_splitExt _ _ G e e' w c hd hng hs he h1 h2 hne he' hw hc,
      fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e'
    · subst h0
      rcases hc with rfl | rfl <;> simp
    · simpa [h0] using hng e₀
  | loop e v he hv =>
    refine ⟨(MGraph.spd_loop _ _ G e v he hv).2 hs, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e
    · subst h0
      simp
    · simpa [h0] using hng e₀
  | unloop e he hl =>
    refine ⟨(MGraph.spd_unloop _ _ G e hl).2 hs, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e
    · subst h0
      simp
    · simpa [h0] using hng e₀
  | red e u v c he hc =>
    refine ⟨(MGraph.spd_red _ _ G e u v c he hc).2 hs, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e
    · subst h0
      rcases hc with rfl | rfl <;> simp
    · simpa [h0] using hng e₀
  | ext e c he hc h1 h2 =>
    refine ⟨(MGraph.spd_ext _ _ G e c hd he hc h1 h2).2 hs, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e
    · subst h0
      rcases hc with rfl | rfl | rfl <;> simp
    · simpa [h0] using hng e₀
  | conv e he =>
    refine ⟨MGraph.spd_conv _ _ G e he hs, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e
    · subst h0
      simp
    · simpa [h0] using hng e₀
  | dropExt e e' hne he h1 h2 he' h1' h2' =>
    refine ⟨MGraph.spd_dropExt _ _ G e e' hne hd he h1 h2 he' h1' h2' hs, fun e₀ => ?_, hd⟩
    by_cases h0 : e₀ = e
    · subst h0
      simp
    · simpa [h0] using hng e₀

section Instances

end Instances

end RBM8D.Graphs
