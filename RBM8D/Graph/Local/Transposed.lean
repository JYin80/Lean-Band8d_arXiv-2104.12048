import RBM8D.Graph.Transpose
import RBM8D.Graph.QExp.Defs
import RBM8D.Graph.Local.EdgeOrder
import RBM8D.Graph.Local.Doubly

/-!
# The transposed `GG` expansion

The `GG` expansion of [II, (4.10)] = [I, (3.17)] with all `G` entries transposed, used at an atom
whose outgoing solid edge ends at an external atom: its value identity, the conditions under
which each form is used, and [I, Lemma 3.16] and [II, Lemma 4.10] for it.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- Every random component (solid edge or weight) has an internal first atom: the external atoms
are only column indices of `G` and `Ḡ` entries (for `k = 3` this is the first half of
`Graph.ColourInv'`). -/
def Graph.RandomFirstInt {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, c.kind.isRandom = true → c.x.isRight = true

/-- Every solid edge leaving `x`, of either charge, ends at an internal atom: the condition under
which the `GG` expansion at `x` is applied in the form of [II, (4.10)]. -/
def Graph.GGOutInt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) : Prop :=
  ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x = x → c.y.isRight = true

/-- Every solid edge entering `x`, of either charge, starts at an internal atom: the condition
under which the `GG` expansion at `x` is applied in the transposed form of [II, (4.10)]. -/
def Graph.GGInInt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) : Prop :=
  ∀ c ∈ Γ.comps, c.kind.isSolid = true → c.y = x → c.x.isRight = true

/-- The tracked formal sum with the two atoms of every solid edge exchanged; the atom maps are
kept. -/
def TExpansion.swapSolid {k n : ℕ} (E : TExpansion k n) : TExpansion k n :=
  E.map fun t => ⟨t.nOut, t.g.swapSolid, t.f⟩

/-- The transposed `GG` expansion at `x`: the expansion `Ô^{(x)}_GG` of [II, (4.10)] applied to the
graph with all `G` entries transposed, the result transposed back, then `O_dot`. For
`𝒢 = G_{xy} G_{y'x} f(G)` its main term is `m S⁺_{xy'} G_{y'y} f(G)`, for
`𝒢 = Ḡ_{xy} Ḡ_{y'x} f(G)` it is `m̄ S⁻_{xy'} Ḡ_{y'y} f(G)`; the waved edge of the main term joins
`x` to the first atom `y'` of the edge entering `x`. The identity if the solid edges attached to
`x` are not of these forms or a `×`-dotted edge `x ≠ y`, `x ≠ y'` is missing, and on graphs with a
`P`/`Q` label, a `G^{(T)}` entry or a `(G_{xx})⁻¹` or `W_D` weight. -/
def oGGTT {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if !(Γ.comps.all Comp.isPlainB) then [Tracked.self Γ] else
  match ggPos x Γ.swapSolid with
  | some E => E.swapSolid.bind fun _ g => oDotT g
  | none =>
    match ggPos x Γ.swapSolid.conj with
    | some E => E.conj.swapSolid.bind fun _ g => oDotT g
    | none => [Tracked.self Γ]

/-! ## The graph with every solid edge reversed -/

section Basic

private theorem comp_swapSolid_kind {V : Type*} (c : Comp V) : c.swapSolid.kind = c.kind := by
  unfold Comp.swapSolid
  split <;> rfl

private theorem comp_swapSolid_label {V : Type*} (c : Comp V) : c.swapSolid.label = c.label := by
  unfold Comp.swapSolid
  split <;> rfl

private theorem comp_swapSolid_of_not_solid {V : Type*} (c : Comp V) (h : c.kind.isSolid = false) :
    c.swapSolid = c := by
  simp [Comp.swapSolid, h]

private theorem comp_swapSolid_of_solid {V : Type*} (c : Comp V) (h : c.kind.isSolid = true) :
    c.swapSolid = { c with x := c.y, y := c.x } := by
  simp [Comp.swapSolid, h]

private theorem comp_swapSolid_swapSolid {V : Type*} (c : Comp V) : c.swapSolid.swapSolid = c := by
  rcases c with ⟨κ, x, y, m, l⟩
  by_cases h : κ.isSolid = true <;> simp [Comp.swapSolid, h]

/-- Reversing every solid edge twice gives the graph back. -/
private theorem graph_swapSolid_swapSolid {k n : ℕ} (Γ : Graph k n) :
    Γ.swapSolid.swapSolid = Γ := by
  rcases Γ with ⟨cs, c⟩
  simp [Graph.swapSolid, List.map_map, Function.comp_def, comp_swapSolid_swapSolid]

private theorem isPlainB_swapSolid {V : Type*} (c : Comp V) :
    c.swapSolid.isPlainB = c.isPlainB := by
  unfold Comp.swapSolid
  split <;> rfl

private theorem swapSolid_ord {k n : ℕ} (Γ : Graph k n) : Γ.swapSolid.ord = Γ.ord := by
  simp [Graph.ord, Graph.swapSolid, List.map_map, Function.comp_def, comp_swapSolid_kind]

private theorem swapSolid_labelFree {k n : ℕ} (Γ : Graph k n) :
    Γ.swapSolid.LabelFree ↔ Γ.LabelFree := by
  simp [Graph.LabelFree, Graph.swapSolid, comp_swapSolid_label]

private theorem swapSolid_plain {k n : ℕ} (Γ : Graph k n) : Γ.swapSolid.Plain ↔ Γ.Plain := by
  simp only [Graph.Plain, Graph.swapSolid, List.forall_mem_map]
  refine forall₂_congr fun c _ => ?_
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [Comp.swapSolid, Kind.isSolid, Comp.WF, Kind.isWeight, Kind.isRandom]

private theorem not_solid_of_joinsMol {V : Type*} (c : Comp V) (h : c.kind.joinsMol = true) :
    c.kind.isSolid = false := by
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp_all [Kind.joinsMol, Kind.isSolid]

private theorem swapSolid_molGraph {k n : ℕ} (Γ : Graph k n) :
    Γ.swapSolid.molGraph = Γ.molGraph := by
  ext u v
  simp only [Graph.molGraph, Graph.swapSolid, SimpleGraph.fromRel_adj, List.mem_map]
  have key : ∀ a b : Atom k n, (∃ c, (∃ c₀ ∈ Γ.comps, c₀.swapSolid = c) ∧
      c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b) ↔
      ∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b := by
    intro a b
    constructor
    · rintro ⟨c, ⟨c₀, hc₀, rfl⟩, hj, hx, hy⟩
      rw [comp_swapSolid_kind] at hj
      rw [comp_swapSolid_of_not_solid c₀ (not_solid_of_joinsMol c₀ hj)] at hx hy
      exact ⟨c₀, hc₀, hj, hx, hy⟩
    · rintro ⟨c, hc, hj, hx, hy⟩
      refine ⟨c, ⟨c, hc, comp_swapSolid_of_not_solid c (not_solid_of_joinsMol c hj)⟩, hj, hx, hy⟩
  rw [key u v, key v u]

private theorem swapSolid_sameMol {k n : ℕ} (Γ : Graph k n) (u v : Atom k n) :
    Γ.swapSolid.SameMol u v ↔ Γ.SameMol u v := by
  simp only [Graph.SameMol, swapSolid_molGraph]

private theorem swapSolid_ggOutInt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) :
    Γ.swapSolid.GGOutInt x ↔ Γ.GGInInt x := by
  simp only [Graph.GGOutInt, Graph.GGInInt, Graph.swapSolid, List.forall_mem_map]
  refine forall₂_congr fun c _ => ?_
  by_cases h : c.kind.isSolid = true
  · simp [comp_swapSolid_of_solid c h, h]
  · have h' : c.kind.isSolid = false := by simpa using h
    simp [comp_swapSolid_of_not_solid c h', h']

private theorem swapSolid_wt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Γ.swapSolid.wt u = Γ.wt u := by
  simp only [Graph.wt, Graph.swapSolid, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun c _ => ?_
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [Comp.swapSolid, Kind.isSolid]

private theorem swapSolid_deg {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Γ.swapSolid.deg u = Γ.deg u := by
  simp only [Graph.deg, Graph.swapSolid, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun c _ => ?_
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [Comp.swapSolid, Kind.isSolid, Bool.or_comm]

end Basic

/-- **Reversing every solid edge**: the graph with the two atoms of every solid edge exchanged
(every `G` entry transposed, [II, Strategy 6.6, Step 3]) gives the graph back when
applied twice, and has the same scaling order, degrees, numbers of weights and molecules; it has no
label, resp. is plain, exactly when the graph is; the condition of the `GG` expansion in the form of
[II, (4.10)] at `x` for it is the condition of the transposed form at `x` for the graph. -/
theorem swapSolid_basic :
  ∀ (k n : ℕ) (Γ : Graph k n), Γ.swapSolid.swapSolid = Γ ∧ Γ.swapSolid.ord = Γ.ord ∧
    (Γ.swapSolid.LabelFree ↔ Γ.LabelFree) ∧ (Γ.swapSolid.Plain ↔ Γ.Plain) ∧
    (∀ u v, Γ.swapSolid.SameMol u v ↔ Γ.SameMol u v) ∧
    (∀ u, Γ.swapSolid.deg u = Γ.deg u) ∧ (∀ u, Γ.swapSolid.wt u = Γ.wt u) ∧
    (∀ x, Γ.swapSolid.GGOutInt x ↔ Γ.GGInInt x) :=
  fun _ _ Γ => ⟨graph_swapSolid_swapSolid Γ, swapSolid_ord Γ, swapSolid_labelFree Γ,
    swapSolid_plain Γ, swapSolid_sameMol Γ, swapSolid_deg Γ, swapSolid_wt Γ,
    swapSolid_ggOutInt Γ⟩

/-! ## The value identity -/

section Value

private theorem forget_bind_oDotT {k n : ℕ} (E : TExpansion k n) :
    (E.bind fun _ g => oDotT g).forget = E.flatMap fun t => oDot t.g := by
  simp [TExpansion.bind, TExpansion.forget, List.map_flatMap, List.map_map, Function.comp_def,
    oDot]

private theorem valR_flatMap {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] {α : Type*}
    (L : List α) (F : α → Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι)
    (ω : Ω) :
    Expansion.valR (L.flatMap F) PF D e ω = (L.map fun a => (F a).valR PF D e ω).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
    simp [Expansion.valR, List.map_append, List.sum_append]

private theorem valR_self {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι}
    {D : Ω → Data ι} {e : Fin k → ι} (Γ : Graph k n) :
    (TExpansion.forget [Tracked.self Γ]).valR PF D e = Γ.valR PF D e := by
  funext ω
  simp [TExpansion.forget, Tracked.self, Expansion.valR]

end Value

/-- **The value identity of the transposed `GG` expansion** ([II, (4.10)] = [I, (3.17)] with all `G`
entries transposed, followed by `O_dot`): under the model relations the transposed `GG` expansion
at `x` has the value of the graph. It is the value identity of `O_GG` at the record with every
resolvent minor matrix transposed, whose model relations hold, together with the value of the
graph with every solid edge reversed and the value identity of `O_dot`. -/
theorem oGGT_value' :
  ∀ (k n : ℕ) (x : Atom k n), PreservesValue (fun Γ => (oGGTT x Γ).forget) modelAdm := by
  intro k n x Ω ι _ _ PF D hA Γ e
  have hbind : ∀ (F : TExpansion k n) (D' : Ω → Data ι),
      (F.bind fun _ g => oDotT g).forget.valR PF D' e = F.forget.valR PF D' e := by
    intro F D'
    funext ω
    rw [forget_bind_oDotT, valR_flatMap]
    simp only [Expansion.valR, TExpansion.forget, List.map_map, Function.comp_def]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    exact congrFun (oDot_value k t.nOut Ω ι PF D' trivial t.g e) ω
  have hsw' : ∀ F : TExpansion k n,
      F.swapSolid.forget.valR PF D e = F.forget.valR PF (fun ω => (D ω).transposeG) e := by
    intro F
    funext ω
    simp only [Expansion.valR, TExpansion.swapSolid, TExpansion.forget, List.map_map,
      Function.comp_def]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    exact congrFun (swapSolid_value k t.nOut t.g Ω ι PF D e) ω
  have hΓ : Γ.valR PF D e = Γ.swapSolid.valR PF (fun ω => (D ω).transposeG) e := by
    rw [← swapSolid_value k n Γ.swapSolid Ω ι PF D e, graph_swapSolid_swapSolid]
  have hO := oGG_value k n x Ω ι PF _ (modelAdm_transpose Ω ι PF D hA) Γ.swapSolid e
  have hpl : Γ.swapSolid.comps.all Comp.isPlainB = Γ.comps.all Comp.isPlainB := by
    simp [Graph.swapSolid, List.all_map, Function.comp_def, isPlainB_swapSolid]
  change (oGGTT x Γ).forget.valR PF D e = Γ.valR PF D e
  unfold oGG oGGT at hO
  unfold oGGTT
  rw [hpl] at hO
  by_cases hp : (!(Γ.comps.all Comp.isPlainB)) = true
  · simp only [hp, ite_true]
    exact valR_self Γ
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hO ⊢
    cases h1 : ggPos x Γ.swapSolid with
    | some E =>
      simp only [h1] at hO ⊢
      rw [hbind] at hO ⊢
      rw [hsw' E, hO, ← hΓ]
    | none =>
      simp only [h1] at hO ⊢
      cases h2 : ggPos x Γ.swapSolid.conj with
      | some E =>
        simp only [h2] at hO ⊢
        rw [hbind] at hO ⊢
        rw [hsw' E.conj, hO, ← hΓ]
      | none =>
        exact valR_self Γ

/-! ## `O_dot` on the graph with every solid edge reversed -/

section Corr

open List

/-- Two components of the same kind, minor and label whose ends are equal, or exchanged when they
are not weights. -/
private def URel {V : Type*} (c' c : Comp V) : Prop :=
  c'.kind = c.kind ∧ c'.minor = c.minor ∧ c'.label = c.label ∧
    ((c'.x = c.x ∧ c'.y = c.y) ∨ (c.kind.isWeight = false ∧ c'.x = c.y ∧ c'.y = c.x))

/-- Two components of the same kind, minor and label whose ends are equal or exchanged, or which
are weights. -/
private def ORel {V : Type*} (c' c : Comp V) : Prop :=
  c'.kind = c.kind ∧ c'.minor = c.minor ∧ c'.label = c.label ∧
    (c.kind.isWeight = true ∨ (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x))

private theorem URel.oRel {V : Type*} {c' c : Comp V} (h : URel c' c) : ORel c' c := by
  obtain ⟨h1, h2, h3, h4 | ⟨-, h4⟩⟩ := h
  · exact ⟨h1, h2, h3, Or.inr (Or.inl h4)⟩
  · exact ⟨h1, h2, h3, Or.inr (Or.inr h4)⟩

private theorem oRel_refl {V : Type*} (c : Comp V) : ORel c c :=
  ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

private theorem uRel_swapSolid {V : Type*} (c : Comp V) : URel c.swapSolid c := by
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [URel, Comp.swapSolid, Kind.isSolid, Kind.isWeight]

private theorem oRel_swapSolid_right {V : Type*} (c : Comp V) : ORel c c.swapSolid := by
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [ORel, Comp.swapSolid, Kind.isSolid, Kind.isWeight]

private theorem forall₂_swapSolid {V : Type*} (l : List (Comp V)) :
    Forall₂ URel (l.map Comp.swapSolid) l := by
  rw [forall₂_map_left_iff, forall₂_same]
  exact fun c _ => uRel_swapSolid c

/-- Two tracked graphs with the same number of atoms and the same atom map, the same coefficient
and corresponding components. -/
private def TRel {k n : ℕ} (t' t : Tracked k n) : Prop :=
  ∃ (m : ℕ) (g' g : Graph k m) (f : Atom k n → Atom k m), t' = ⟨m, g', f⟩ ∧ t = ⟨m, g, f⟩ ∧
    g'.coeff = g.coeff ∧ Forall₂ ORel g'.comps g.comps

/-! ### Lists of corresponding entries -/

private theorem forall₂_any {α β : Type*} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) {l' : List α} {l : List β} (h : Forall₂ R l' l) :
    l'.any p = l.any q := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => simp only [List.any_cons, hpq _ _ h₁, ih]

private theorem forall₂_map_eq {α β γ : Type*} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) {l' : List α} {l : List β} (h : Forall₂ R l' l) :
    l'.map f = l.map g := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => simp only [List.map_cons, hfg _ _ h₁, ih]

private theorem forall₂_filterMap_eq {α β γ : Type*} {R : α → β → Prop} {f : α → Option γ}
    {g : β → Option γ} (hfg : ∀ a b, R a b → f a = g b) {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : l'.filterMap f = l.filterMap g := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => simp only [List.filterMap_cons, hfg _ _ h₁, ih]

private theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : ∀ a ∈ l', ∃ b ∈ l, R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons h₁ _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., h₁⟩
    · obtain ⟨b, hb, hab⟩ := ih a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

private theorem forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : ∀ b ∈ l, ∃ a ∈ l', R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons h₁ _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., h₁⟩
    · obtain ⟨a, ha, hab⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

private theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) (H : ∀ a b, a ∈ l' → b ∈ l → R a b → S a b) : Forall₂ S l' l := by
  induction h with
  | nil => exact .nil
  | cons h₁ _ ih =>
    exact .cons (H _ _ (List.mem_cons_self ..) (List.mem_cons_self ..) h₁)
      (ih fun a b ha hb => H a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb))

private theorem forall₂_isEmpty {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : l'.isEmpty = l.isEmpty := by
  cases h <;> rfl

/-- A sublist of a list without repetitions corresponds to the sublist at the same positions of a
corresponding list without repetitions. -/
private theorem sublist_transfer {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) (hn' : l'.Nodup) (hn : l.Nodup) {A' : List α} (hA' : A' <+ l') :
    ∃ A, A <+ l ∧ Forall₂ R A' A ∧ Forall₂ (fun a' a => R a' a ∧ (a' ∈ A' ↔ a ∈ A)) l' l := by
  induction h generalizing A' with
  | nil =>
    rw [List.sublist_nil] at hA'
    subst hA'
    exact ⟨[], List.Sublist.slnil, .nil, .nil⟩
  | @cons a' a l' l h₁ h₂ ih =>
    rw [List.nodup_cons] at hn' hn
    cases hA' with
    | cons _ hA' =>
      obtain ⟨A, hA, hR, hM⟩ := ih hn'.2 hn.2 hA'
      refine ⟨A, hA.cons a, hR, .cons ⟨h₁, ?_⟩ hM⟩
      exact ⟨fun h => absurd (hA'.subset h) hn'.1, fun h => absurd (hA.subset h) hn.1⟩
    | cons_cons _ hA' =>
      obtain ⟨A, hA, hR, hM⟩ := ih hn'.2 hn.2 hA'
      refine ⟨a :: A, hA.cons_cons a, .cons h₁ hR, .cons ⟨h₁, by simp⟩ ?_⟩
      refine forall₂_imp_mem hM fun b' b hb' hb ⟨hr, hm⟩ => ⟨hr, ?_⟩
      have hb'a : b' ≠ a' := fun h => hn'.1 (h ▸ hb')
      have hba : b ≠ a := fun h => hn.1 (h ▸ hb)
      simp only [List.mem_cons, hb'a, hba, false_or, hm]

/-! ### The pairs of `O_dot` -/

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
  · exact (foldl_spStep_pairwise _ [] List.Pairwise.nil).imp fun {a b} h hab => h (Or.inl hab.symm)

/-- Two pairs of atoms that are equal as unordered pairs. -/
private def PRel (p' p : Atom k n × Atom k n) : Prop := p' = p ∨ p' = p.swap

/-- Two pairs of `O_dot` with the same flag that are equal as unordered pairs. -/
private def SPRel (p' p : Atom k n × Atom k n × Bool) : Prop :=
  p'.2.2 = p.2.2 ∧ PRel (p'.1, p'.2.1) (p.1, p.2.1)

private theorem bool_sym (a b c d : Bool) : (a && b || c && d) = (d && c || b && a) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem spJoined_comm (Γ : Graph k n) (p : Kind → Bool) (u v : Atom k n) :
    spJoined Γ p u v = spJoined Γ p v u := by
  unfold spJoined
  congr 1
  funext c
  rw [bool_sym (c.x == u), Bool.and_comm (c.x == v), Bool.and_comm (c.y == v)]

private theorem spJoined_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps)
    (p : Kind → Bool) (u v : Atom k n) : spJoined Γ' p u v = spJoined Γ p u v := by
  unfold spJoined
  refine forall₂_any (fun c' c h => ?_) hR
  obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
  · rw [hk, hx, hy]
  · rw [hk, hx, hy, bool_sym (c.y == u)]

private theorem pRel_iff (q' q p' p : Atom k n × Atom k n) (hq : PRel q' q) (hp : PRel p' p) :
    (q' == p' || q' == p'.swap) = (q == p || q == p.swap) := by
  rcases q with ⟨a, b⟩
  rcases p with ⟨c, d⟩
  apply Bool.eq_iff_iff.2
  rcases hq with rfl | rfl <;> rcases hp with rfl | rfl <;>
    simp only [Prod.swap_prod_mk, beq_iff_eq, Prod.mk.injEq, Bool.or_eq_true] <;>
    tauto

private theorem spUniq_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps) :
    Forall₂ PRel (spUniq Γ') (spUniq Γ) := by
  have hc : Forall₂ PRel (spCand Γ') (spCand Γ) := by
    refine List.rel_filterMap (fun c' c h => ?_) hR
    obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
    · rw [hk, hx, hy]
      split_ifs
      · exact .some (Or.inl rfl)
      · exact .none
    · rw [hk, hx, hy, bne_comm]
      split_ifs
      · exact .some (Or.inr rfl)
      · exact .none
  refine List.rel_foldl (fun acc' acc hacc p' p hp => ?_) Forall₂.nil hc
  unfold spStep
  rw [forall₂_any (fun q' q hq => pRel_iff q' q p' p hq hp) hacc]
  split_ifs
  · exact hacc
  · exact List.rel_append hacc (.cons hp .nil)

private theorem splitPairs_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps) :
    Forall₂ SPRel Γ'.splitPairs Γ.splitPairs := by
  rw [splitPairs_eq, splitPairs_eq]
  refine List.rel_filterMap (fun p' p hp => ?_) (spUniq_rel hR)
  have hj : ∀ pr : Kind → Bool, spJoined Γ' pr p'.1 p'.2 = spJoined Γ pr p.1 p.2 := by
    intro pr
    rw [spJoined_rel hR]
    rcases hp with rfl | rfl
    · rfl
    · exact spJoined_comm Γ pr _ _
  simp only [hj]
  split_ifs
  · exact .some ⟨rfl, hp⟩
  · exact .none

/-! ### The terms of `O_dot` -/

private theorem dotChoice_rel {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ URel Γ'.comps Γ.comps) {SP' SP A' A : List (Atom k n × Atom k n × Bool)}
    (hSP : Forall₂ (fun p' p => SPRel p' p ∧ (p' ∈ A' ↔ p ∈ A)) SP' SP)
    (hA : Forall₂ SPRel A' A) :
    (Γ'.dotChoice SP' A').coeff = (Γ.dotChoice SP A).coeff ∧
      Forall₂ URel (Γ'.dotChoice SP' A').comps (Γ.dotChoice SP A).comps := by
  have hxo : ∀ u v : Atom k n,
      (SP'.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))) =
        (SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))) := by
    intro u v
    refine forall₂_any (fun p' p h => ?_) hSP
    obtain ⟨⟨hb, hq⟩, -⟩ := h
    rcases p' with ⟨a', b', c'⟩
    rcases p with ⟨a, b, c⟩
    simp only at hb hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hb]
    · rw [hb, bool_sym (b == u)]
  have hxs : ∀ u v : Atom k n,
      (SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))) =
        (SP.any fun p => !p.2.2 && ((p.1 == v && p.2.1 == u) || (p.1 == u && p.2.1 == v))) := by
    intro u v
    congr 1
    funext p
    rw [Bool.or_comm]
  refine ⟨?_, ?_⟩
  · simp only [Graph.dotChoice, hc]
    congr 2
    refine Forall₂.length_eq (List.rel_filter (fun p' p h => ?_) hA)
    dsimp only
    rw [h.1]
  · simp only [Graph.dotChoice]
    refine List.rel_append (List.rel_filter (fun c' c h => ?_) hR)
      (List.rel_filterMap (fun p' p h => ?_) hSP)
    · dsimp only
      obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
      · rw [hk, hx, hy, hxo]
      · rw [hk, hx, hy, hxo, hxs]
    · obtain ⟨⟨hb, hq⟩, hm⟩ := h
      by_cases h1 : p ∈ A
      · have h1' : p' ∈ A' := hm.2 h1
        simp only [h1, h1', ↓reduceIte]
        refine .some ⟨rfl, rfl, rfl, ?_⟩
        rcases hq with h | h <;> simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h <;>
          simp [mkC, h, Kind.isWeight]
      · have h1' : p' ∉ A' := fun h => h1 (hm.1 h)
        simp only [h1, h1', ↓reduceIte, hb]
        split_ifs
        · refine .some ⟨rfl, rfl, rfl, ?_⟩
          rcases hq with h | h <;> simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h <;>
            simp [mkC, h, Kind.isWeight]
        · exact .none

/-- One component under `O_merge`. -/
private def mergeC {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- `O_merge` for the partition `P` into blocks. -/
private def mergeWith (P : List (List (Atom k n))) (cs : List (Comp (Atom k n))) (d : Coeff) :
    Option (Tracked k n) :=
  let rep := blockRep P
  if cs.any (fun c => c.kind == .xdot && rep c.x == rep c.y) then none else
  let roots := ((List.finRange n).map fun i => rep (Sum.inr i)).dedup
  let f : Atom k n → Atom k roots.length := fun u =>
    match u with
    | .inl a => .inl a
    | .inr i => .inr ⟨roots.idxOf (rep (.inr i)),
        List.idxOf_lt_length_of_mem
          (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩
  some ⟨roots.length, ⟨cs.filterMap (mergeC rep f), d⟩, f⟩

private theorem mergeT_eq_mergeWith (Γ : Graph k n) :
    Γ.mergeT = mergeWith (dotBlocks (allAtoms k n) Γ.comps) Γ.comps Γ.coeff := rfl

private theorem joinBlocks_comm (P : List (List (Atom k n))) (u v : Atom k n) :
    joinBlocks P u v = joinBlocks P v u := by
  unfold joinBlocks
  simp only [Bool.or_comm]

private theorem dotBlocks_rel {cs' cs : List (Comp (Atom k n))} (hR : Forall₂ URel cs' cs) :
    dotBlocks (allAtoms k n) cs' = dotBlocks (allAtoms k n) cs := by
  unfold dotBlocks
  refine List.rel_foldl (fun P Q hPQ c' c h => ?_) rfl hR
  subst hPQ
  obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
  · rw [hk, hx, hy]
  · rw [hk, hx, hy, joinBlocks_comm]

private theorem mergeC_rel {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    {c' c : Comp (Atom k n)} (h : URel c' c) :
    Option.Rel ORel (mergeC rep f c') (mergeC rep f c) := by
  obtain ⟨hk, hm, hl, ⟨hx, hy⟩ | ⟨hw, hx, hy⟩⟩ := h
  · have : c' = c := by
      rcases c' with ⟨_, _, _, _, _⟩
      rcases c with ⟨_, _, _, _, _⟩
      simp_all
    subst this
    cases mergeC rep f c' with
    | none => exact .none
    | some d => exact .some (oRel_refl d)
  · unfold mergeC
    rw [hk, hx, hy, Bool.beq_comm (a := f c.y), Bool.beq_comm (a := rep c.y)]
    split_ifs with h1 h2
    · exact .none
    · refine .some ⟨rfl, by simp [Comp.map, hm], by simp [Comp.map, hl], Or.inl ?_⟩
      simp only [Bool.and_eq_true] at h2
      rcases hc : c.kind with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
        simp_all [Kind.isSolid, Kind.toWeight, Kind.isWeight]
    · exact .some ⟨by simp [Comp.map, hk], by simp [Comp.map, hm], by simp [Comp.map, hl],
        Or.inr (Or.inr ⟨by simp [Comp.map, hx], by simp [Comp.map, hy]⟩)⟩

private theorem mergeWith_rel (P : List (List (Atom k n))) {cs' cs : List (Comp (Atom k n))}
    (d : Coeff) (hR : Forall₂ URel cs' cs) {t' : Tracked k n} (h : mergeWith P cs' d = some t') :
    ∃ t, mergeWith P cs d = some t ∧ TRel t' t := by
  unfold mergeWith at h ⊢
  have hany : (cs'.any fun c => c.kind == .xdot && blockRep P c.x == blockRep P c.y) =
      (cs.any fun c => c.kind == .xdot && blockRep P c.x == blockRep P c.y) := by
    refine forall₂_any (fun c' c h => ?_) hR
    obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
    · rw [hk, hx, hy]
    · rw [hk, hx, hy, Bool.beq_comm (a := blockRep P c.y)]
  simp only [hany] at h ⊢
  split_ifs at h ⊢
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, _, _, _, _, rfl, rfl, rfl,
    List.rel_filterMap (fun c' c h => mergeC_rel _ _ h) hR⟩

private theorem mergeT_rel {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ URel Γ'.comps Γ.comps) {t' : Tracked k n} (h : Γ'.mergeT = some t') :
    ∃ t, Γ.mergeT = some t ∧ TRel t' t := by
  rw [mergeT_eq_mergeWith, dotBlocks_rel hR, hc] at h
  rw [mergeT_eq_mergeWith]
  exact mergeWith_rel _ _ hR h

private theorem labels_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps) :
    Γ'.labels = Γ.labels := by
  unfold Graph.labels
  rw [forall₂_filterMap_eq (fun c' c h => h.2.2.1) hR]

private theorem tRel_self {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ ORel Γ'.comps Γ.comps) : TRel (Tracked.self Γ') (Tracked.self Γ) :=
  ⟨n, Γ', Γ, id, rfl, rfl, hc, hR⟩

/-- Every term of `O_dot` on a graph corresponds to a term of `O_dot` on a graph whose components
are those of the first graph with the ends of some non-weight components exchanged. -/
private theorem oDotT_rel {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ URel Γ'.comps Γ.comps) : ∀ t' ∈ oDotT Γ', ∃ t ∈ oDotT Γ, TRel t' t := by
  intro t' ht
  have hlab := labels_rel hR
  have hany1 : (Γ'.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) =
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) :=
    forall₂_any (fun c' c h => by rw [h.1, h.2.2.1]) hR
  have hany2 : (Γ'.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y)) =
      (Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y)) := by
    refine forall₂_any (fun c' c h => ?_) hR
    obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
    · rw [hk, hx, hy]
    · rw [hk, hx, hy, Bool.beq_comm (a := c.y), Bool.and_assoc, Bool.and_comm c.y.isRight,
        ← Bool.and_assoc]
  have hSP := splitPairs_rel hR
  have hemp : Γ'.splitPairs.isEmpty = Γ.splitPairs.isEmpty := forall₂_isEmpty hSP
  have hself : TRel (Tracked.self Γ') (Tracked.self Γ) := tRel_self hc (hR.imp fun _ _ h => h.oRel)
  unfold oDotT at ht ⊢
  simp only [hlab, hany1, hany2, hemp] at ht ⊢
  split_ifs at ht ⊢
  · exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht) ▸ hself⟩
  · exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht) ▸ hself⟩
  · obtain ⟨A', hA', hm⟩ := List.mem_filterMap.1 ht
    obtain ⟨A, hA, hAR, hM⟩ := sublist_transfer hSP (splitPairs_nodup Γ') (splitPairs_nodup Γ)
      (List.mem_sublists.1 hA')
    obtain ⟨hc', hR'⟩ := dotChoice_rel hc hR hM hAR
    obtain ⟨t, ht, hT⟩ := mergeT_rel hc' hR' hm
    exact ⟨t, List.mem_filterMap.2 ⟨A, List.mem_sublists.2 hA, ht⟩, hT⟩

/-- Every term of `O_dot` applied after the reversal of every solid edge corresponds to a term of
`O_dot` applied before it. -/
private theorem bind_swapSolid_rel (E : TExpansion k n) :
    ∀ t' ∈ E.swapSolid.bind (fun _ g => oDotT g),
      ∃ t ∈ E.bind (fun _ g => oDotT g), TRel t' t := by
  intro t' ht'
  simp only [TExpansion.bind, TExpansion.swapSolid, List.flatMap_map, List.mem_flatMap,
    List.mem_map] at ht'
  obtain ⟨e, he, s', hs', rfl⟩ := ht'
  obtain ⟨s, hs, m, g', g, f, rfl, rfl, hc, hR⟩ :=
    oDotT_rel (Γ' := e.g.swapSolid) (Γ := e.g) rfl (forall₂_swapSolid e.g.comps) s' hs'
  refine ⟨⟨m, g, f ∘ e.f⟩, ?_, m, g', g, f ∘ e.f, rfl, rfl, hc, hR⟩
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map]
  exact ⟨e, he, ⟨m, g, f⟩, hs, rfl⟩

/-- Every term of the transposed `GG` expansion at `x` corresponds to a term of the `GG`
expansion at `x` of the graph with every solid edge reversed. -/
private theorem oGGTT_rel (x : Atom k n) (Γ : Graph k n) :
    ∀ t' ∈ oGGTT x Γ, ∃ t ∈ oGGT x Γ.swapSolid, TRel t' t := by
  intro t' ht'
  have hpl : Γ.swapSolid.comps.all Comp.isPlainB = Γ.comps.all Comp.isPlainB := by
    simp [Graph.swapSolid, List.all_map, Function.comp_def, isPlainB_swapSolid]
  have hself : TRel (Tracked.self Γ) (Tracked.self Γ.swapSolid) := by
    refine tRel_self rfl ?_
    simp only [Graph.swapSolid]
    rw [forall₂_map_right_iff, forall₂_same]
    exact fun c _ => oRel_swapSolid_right c
  unfold oGGTT at ht'
  unfold oGGT
  rw [hpl]
  by_cases hp : (!(Γ.comps.all Comp.isPlainB)) = true
  · simp only [hp, ite_true] at ht' ⊢
    exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht') ▸ hself⟩
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at ht' ⊢
    cases h1 : ggPos x Γ.swapSolid with
    | some E =>
      simp only [h1] at ht' ⊢
      exact bind_swapSolid_rel E t' ht'
    | none =>
      simp only [h1] at ht' ⊢
      cases h2 : ggPos x Γ.swapSolid.conj with
      | some E =>
        simp only [h2] at ht' ⊢
        exact bind_swapSolid_rel E.conj t' ht'
      | none =>
        simp only [h2] at ht' ⊢
        exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht') ▸ hself⟩

end Corr

/-! ## Properties kept by the correspondence -/

section Transfer

open List

variable {k n : ℕ}

private theorem ord_rel {m : ℕ} {g' g : Graph k m} (hR : Forall₂ ORel g'.comps g.comps) :
    g'.ord = g.ord := by
  unfold Graph.ord
  rw [forall₂_map_eq (f := fun c => c.kind.ord) (g := fun c => c.kind.ord)
    (fun c' c h => by rw [h.1]) hR]

private theorem labelFree_rel {m : ℕ} {g' g : Graph k m} (hR : Forall₂ ORel g'.comps g.comps) :
    g'.LabelFree ↔ g.LabelFree := by
  constructor
  · intro h c hc
    obtain ⟨c', hc', hr⟩ := forall₂_mem_right hR c hc
    rw [← hr.2.2.1]
    exact h c' hc'
  · intro h c' hc'
    obtain ⟨c, hc, hr⟩ := forall₂_mem_left hR c' hc'
    rw [hr.2.2.1]
    exact h c hc

private theorem deg_rel {m : ℕ} {g' g : Graph k m} (hR : Forall₂ ORel g'.comps g.comps)
    (u : Atom k m) : g'.deg u = g.deg u := by
  unfold Graph.deg
  refine Forall₂.length_eq (List.rel_filter (fun c' c h => ?_) hR)
  dsimp only
  obtain ⟨hk, -, -, hw | ⟨hx, hy⟩ | ⟨hx, hy⟩⟩ := h
  · have hs : c.kind.isSolid = false := by
      cases hc : c.kind <;> simp_all [Kind.isWeight, Kind.isSolid]
    rw [hk, hs]
    simp
  · rw [hk, hx, hy]
  · rw [hk, hx, hy, Bool.or_comm]

private theorem exists_sym_rel {V : Type*} {R : Comp V → Comp V → Prop} {l' l : List (Comp V)}
    (hR : Forall₂ R l' l) (P : Comp V → Prop) (hP : ∀ c' c, R c' c → (P c' ↔ P c))
    (hends : ∀ c' c, R c' c → P c → (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x))
    (u v : V) :
    (∃ c ∈ l', P c ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
      ∃ c ∈ l, P c ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
  constructor
  · rintro ⟨c', hc', hp, he⟩
    obtain ⟨c, hc, hr⟩ := forall₂_mem_left hR c' hc'
    have hp' := (hP c' c hr).1 hp
    refine ⟨c, hc, hp', ?_⟩
    rcases hends c' c hr hp' with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] at he <;> tauto
  · rintro ⟨c, hc, hp, he⟩
    obtain ⟨c', hc', hr⟩ := forall₂_mem_right hR c hc
    refine ⟨c', hc', (hP c' c hr).2 hp, ?_⟩
    rcases hends c' c hr hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] <;> tauto

private theorem fromRel_rel {V : Type*} {R : Comp V → Comp V → Prop} {l' l : List (Comp V)}
    (hR : Forall₂ R l' l) (P : Comp V → Prop) (hP : ∀ c' c, R c' c → (P c' ↔ P c))
    (hends : ∀ c' c, R c' c → P c → (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)) :
    SimpleGraph.fromRel (fun u v => ∃ c ∈ l', P c ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel (fun u v => ∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v) := by
  ext u v
  simp only [SimpleGraph.fromRel_adj]
  have key : ∀ l : List (Comp V), ((∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v) ∨
      ∃ c ∈ l, P c ∧ c.x = v ∧ c.y = u) ↔
      ∃ c ∈ l, P c ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
    intro l
    constructor
    · rintro (⟨c, hc, hp, h⟩ | ⟨c, hc, hp, h⟩)
      exacts [⟨c, hc, hp, Or.inl h⟩, ⟨c, hc, hp, Or.inr h⟩]
    · rintro ⟨c, hc, hp, h | h⟩
      exacts [Or.inl ⟨c, hc, hp, h⟩, Or.inr ⟨c, hc, hp, h⟩]
  rw [key, key, exists_sym_rel hR P hP hends]

private theorem oRel_ends_of_not_weight {V : Type*} {c' c : Comp V} (h : ORel c' c)
    (hw : c.kind.isWeight = false) : (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x) := by
  obtain ⟨-, -, -, h | h | h⟩ := h
  · rw [hw] at h
    exact absurd h (by simp)
  · exact Or.inl h
  · exact Or.inr h

private theorem molGraph_rel {m : ℕ} {g' g : Graph k m} (hR : Forall₂ ORel g'.comps g.comps) :
    g'.molGraph = g.molGraph :=
  fromRel_rel hR (fun c => c.kind.joinsMol = true) (fun c' c h => by rw [h.1])
    fun c' c h hp => oRel_ends_of_not_weight h (by
      rcases c with ⟨κ, _, _, _, _⟩
      cases κ <;> simp_all [Kind.joinsMol, Kind.isWeight])

private theorem sameMol_rel {m : ℕ} {g' g : Graph k m} (hR : Forall₂ ORel g'.comps g.comps)
    (u v : Atom k m) : g'.SameMol u v ↔ g.SameMol u v := by
  simp only [Graph.SameMol, molGraph_rel hR]

private theorem not_weight_of_net {κ : Kind} (h : κ.isDiffusive = true ∨ κ.isBlue = true) :
    κ.isWeight = false := by
  cases κ <;> simp_all [Kind.isDiffusive, Kind.isBlue, Kind.isWeight]

/-- The doubly connected property passes to a graph with corresponding components. -/
private theorem doublyConnected_rel {m : ℕ} {g' g : Graph k m}
    (hR : Forall₂ ORel g'.comps g.comps) (h : g.DoublyConnected) : g'.DoublyConnected := by
  obtain ⟨black, blue, hdis, hb, hbl, hsb, hsbl⟩ := h
  have hlen : g'.comps.length = g.comps.length := hR.length_eq
  let e : Fin g.comps.length ↪ Fin g'.comps.length := ⟨Fin.cast hlen.symm, Fin.cast_injective _⟩
  have hget : ∀ i : Fin g.comps.length, ORel g'.comps[e i] g.comps[i] := by
    intro i
    have := hR.get (i := i.1) (by rw [hlen]; exact i.2) i.2
    simpa [e] using this
  have hspan : ∀ B : Finset (Fin g.comps.length), (∀ i ∈ B, g.comps[i].kind.isWeight = false) →
      g.Spans B → g'.Spans (B.map e) := by
    intro B hB hs a b
    refine (hs a b).mono ?_
    intro u v huv
    simp only [Graph.net, SimpleGraph.fromRel_adj] at huv ⊢
    obtain ⟨hne, h⟩ := huv
    refine ⟨hne, ?_⟩
    have key : ∀ u v : Fin m, (g.SameMol (.inr u) (.inr v) ∨
        ∃ i ∈ B, g.comps[i].x = .inr u ∧ g.comps[i].y = .inr v) →
        (g'.SameMol (.inr u) (.inr v) ∨
          ∃ i ∈ B.map e, g'.comps[i].x = .inr u ∧ g'.comps[i].y = .inr v) ∨
        (g'.SameMol (.inr v) (.inr u) ∨
          ∃ i ∈ B.map e, g'.comps[i].x = .inr v ∧ g'.comps[i].y = .inr u) := by
      rintro u v (hm | ⟨i, hi, hx, hy⟩)
      · exact Or.inl (Or.inl ((sameMol_rel hR _ _).2 hm))
      · rcases oRel_ends_of_not_weight (hget i) (hB i hi) with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
        · exact Or.inl (Or.inr ⟨e i, Finset.mem_map_of_mem e hi, hx'.trans hx, hy'.trans hy⟩)
        · exact Or.inr (Or.inr ⟨e i, Finset.mem_map_of_mem e hi, hx'.trans hy, hy'.trans hx⟩)
    rcases h with h | h
    · exact key u v h
    · exact (key v u h).symm
  refine ⟨black.map e, blue.map e, (Finset.disjoint_map e).2 hdis, ?_, ?_,
    hspan _ (fun i hi => not_weight_of_net (Or.inl (hb i hi))) hsb,
    hspan _ (fun i hi => not_weight_of_net (hbl i hi)) hsbl⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    rw [(hget j).1]
    exact hb j hj
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    rw [(hget j).1]
    exact hbl j hj

/-- Reversing every solid edge keeps normal regularity. -/
private theorem normal_swapSolid {C : ℕ} {Γ : Graph k n} (h : Γ.Normal C) :
    Γ.swapSolid.Normal C := by
  obtain ⟨⟨hsize, hconn, hint, hdot⟩, hloop, hx⟩ := h
  have hR : Forall₂ URel Γ.swapSolid.comps Γ.comps := forall₂_swapSolid Γ.comps
  have hends : ∀ (P : Comp (Atom k n) → Prop) (c' c : Comp (Atom k n)), URel c' c → P c →
      (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x) := by
    rintro P c' c ⟨-, -, -, h | ⟨-, h⟩⟩ -
    exacts [Or.inl h, Or.inr h]
  have hedge : Γ.swapSolid.edgeGraph = Γ.edgeGraph := by
    have := fromRel_rel hR (fun _ => True) (fun _ _ _ => Iff.rfl) (hends _)
    simp only [true_and] at this
    exact this
  have hwave : Γ.swapSolid.wavedThetaGraph = Γ.wavedThetaGraph :=
    fromRel_rel hR (fun c => c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true)
      (fun c' c h => by rw [h.1]) (hends _)
  refine ⟨⟨by simpa [Graph.swapSolid] using hsize, by rw [hedge]; exact hconn,
    fun a b => by rw [hwave]; exact hint a b, ?_⟩, ?_, ?_⟩
  · intro c hc hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [comp_swapSolid_kind] at hk
    rw [comp_swapSolid_of_not_solid d (by rw [hk]; rfl)]
    exact hdot d hd hk
  · intro c hc hs
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [comp_swapSolid_kind] at hs
    rw [comp_swapSolid_of_solid d hs]
    exact (hloop d hd hs).symm
  · intro u v huv
    rw [exists_sym_rel hR (fun c => c.kind = .xdot) (fun c' c h => by rw [h.1]) (hends _),
      exists_sym_rel hR (fun c => c.kind.isSolid = true) (fun c' c h => by rw [h.1]) (hends _)]
    exact hx u v huv

private theorem ggInput_swapSolid {Γ : Graph k n} {x y y' : Atom k n} (h : Γ.GGInputAt x y y') :
    Γ.swapSolid.GGInputAt x y' y := by
  obtain ⟨hd, ch, ⟨c, hc, hk, hx, hy⟩, ⟨c', hc', hk', hx', hy'⟩⟩ := h
  have hs : ∀ d : Comp (Atom k n), d.kind = .G ch → d.swapSolid = { d with x := d.y, y := d.x } :=
    fun d hd => comp_swapSolid_of_solid d (by rw [hd]; rfl)
  refine ⟨by rw [swapSolid_deg]; exact hd, ch, ⟨c'.swapSolid, List.mem_map_of_mem hc', ?_⟩,
    ⟨c.swapSolid, List.mem_map_of_mem hc, ?_⟩⟩
  · rw [hs c' hk']
    exact ⟨hk', hy', hx'⟩
  · rw [hs c hk]
    exact ⟨hk, hy, hx⟩

private theorem ggShape_of_swapSolid {Γ : Graph k n} {x z : Atom k n}
    (h : Γ.swapSolid.GGShapeAt x z) : Γ.GGShapeAt x z := by
  obtain ⟨hd, ch, ⟨c, hc, hk, hx, hy⟩, ⟨c', hc', hk', hx', hy'⟩⟩ := h
  obtain ⟨d, hd1, rfl⟩ := List.mem_map.1 hc
  obtain ⟨d', hd2, rfl⟩ := List.mem_map.1 hc'
  rw [comp_swapSolid_kind] at hk hk'
  rw [comp_swapSolid_of_solid d (by rw [hk]; rfl)] at hx hy
  rw [comp_swapSolid_of_solid d' (by rw [hk']; rfl)] at hx' hy'
  exact ⟨by rw [← swapSolid_deg]; exact hd, ch, ⟨d', hd2, hk', hy', hx'⟩, ⟨d, hd1, hk, hy, hx⟩⟩

private theorem pairRemoved_rel {m : ℕ} {g' g : Graph k m} (f : Atom k n → Atom k m)
    (hR : Forall₂ ORel g'.comps g.comps) {Γ : Graph k n} {x y : Atom k n}
    (h : (⟨m, g, f⟩ : Tracked k n).PairRemoved Γ.swapSolid x y) :
    (⟨m, g', f⟩ : Tracked k n).PairRemoved Γ x y := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5 ⊢
  rw [swapSolid_ord] at h1
  rw [swapSolid_deg] at h3
  simp only [swapSolid_deg] at h4
  refine ⟨by rw [ord_rel hR]; exact h1, by rw [deg_rel hR]; exact h2, by rw [deg_rel hR]; exact h3,
    fun v hv hv' => by rw [deg_rel hR]; exact h4 v hv hv',
    fun u hu => by rw [deg_rel hR]; exact h5 u hu⟩

end Transfer

/-- **[I, Lemma 3.16] for the transposed `GG` expansion** (case (a) and case (b), [I, Def 3.15] =
[II, Def 4.5] with all `G` entries transposed): for a plain normal regular graph without labels and
without weight on the internal atom `x`, whose solid edges at `x` are `G_{xy} G_{y'x}` or
`Ḡ_{xy} Ḡ_{y'x}`, every output graph of the transposed `GG` expansion at `x` without labels has a
strictly higher scaling order, or is the graph with the two solid edges between `x` and some `y`
of one charge removed. -/
theorem ggLemmaT :
  ∀ (k n C : ℕ) (x y y' : Atom k n) (Γ : Graph k n),
    x.isRight = true → Γ.Normal C → Γ.LabelFree → Γ.Plain →
    Γ.wt x = 0 → Γ.GGInputAt x y y' → ∀ t ∈ oGGTT x Γ, t.g.LabelFree →
      Γ.ord + 1 ≤ t.g.ord ∨ ∃ y, Γ.GGShapeAt x y ∧ t.PairRemoved Γ x y := by
  intro k n C x y y' Γ hx hN hlf hP hwt hin t' ht' hlf'
  obtain ⟨t, ht, m, g', g, f, rfl, rfl, -, hR⟩ := oGGTT_rel x Γ t' ht'
  have hlfg : g.LabelFree := (labelFree_rel hR).1 hlf'
  rcases ggLemma k n C x y' y Γ.swapSolid hx (normal_swapSolid hN)
      ((swapSolid_labelFree Γ).2 hlf) ((swapSolid_plain Γ).2 hP)
      (by rw [swapSolid_wt]; exact hwt) (ggInput_swapSolid hin) _ ht hlfg with h | ⟨z, hz, hpr⟩
  · left
    dsimp only at h ⊢
    rw [ord_rel hR]
    rwa [swapSolid_ord] at h
  · exact Or.inr ⟨z, ggShape_of_swapSolid hz, pairRemoved_rel f hR hpr⟩

/-- **[II, Lemma 4.10] for the transposed `GG` expansion**: for a doubly connected normal regular
graph in which every blue solid edge entering the internal atom `x` starts at an internal atom,
every output graph of the transposed `GG` expansion at `x` is doubly connected. -/
theorem localDoublyConnectedT :
  ∀ (k n C : ℕ) (x : Atom k n) (Γ : Graph k n), Γ.DoublyConnected →
    x.isRight = true → Γ.Normal C →
    (∀ c ∈ Γ.comps, c.kind = .G .plus → c.y = x → c.x.isRight = true) →
    ∀ t ∈ oGGTT x Γ, t.g.DoublyConnected := by
  intro k n C x Γ hdc hx hN hin t' ht'
  obtain ⟨t, ht, m, g', g, f, rfl, rfl, -, hR⟩ := oGGTT_rel x Γ t' ht'
  have hdcT : Γ.swapSolid.DoublyConnected :=
    doublyConnected_rel (g' := Γ.swapSolid) ((forall₂_swapSolid Γ.comps).imp fun _ _ h => h.oRel)
      hdc
  have hinT : ∀ c ∈ Γ.swapSolid.comps, c.kind = .G .plus → c.x = x → c.y.isRight = true := by
    intro c hc hk hcx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [comp_swapSolid_kind] at hk
    rw [comp_swapSolid_of_solid d (by rw [hk]; rfl)] at hcx ⊢
    exact hin d hd hk hcx
  exact doublyConnected_rel hR
    ((localDoublyConnected k n C x Γ.swapSolid hdcT).2.2.2.1 hx (normal_swapSolid hN) hinT _ ht)

section Instances

/-! ### Decidability on atomic graphs -/

/-- Adjacency in the graph of waved and dotted components is decidable. -/
private instance instDecAdjMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

/-- Being in one molecule is decidable. -/
private instance instDecSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjMol Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

section Mol

variable {V E : Type}

end Mol

end Instances

end RBM8D.Graphs
