import Batteries.Tactic.OpenPrivate
import RBM8D.Diffusion.ErrBound
import RBM8D.Bound.Doubly
import RBM8D.Bound.KeySum
import RBM8D.Graph.DotBlocks

/-!
# The forms of [I, (8.20)]: the bounds with one or two fixed atoms

A graph `g` with root edge `Θ_{⊗v}` gives the rooted graph `𝒢_{x, 𝔟𝔟}` read at `(x, 𝔟, 𝔟)`
([I, (8.14)–(8.15)], [II, Def 3.3 (4)]). By [I, (8.20)] its value is the sum over the labels of
the internal atoms of the core `𝒢₀` times the tips (`ErrBound.val_decomp`). This file bounds it in
every form of [I, (8.20)], from the bounds [I, Lemma 6.10, (6.20)–(6.21)] (`dcStrong`,
`dcSingle`) on graphs with two or one fixed atoms.

* **`𝔟` isolated in `𝒢₀`** (no waved or dotted edge joins `⊕` or `⊖` to an internal atom; the
  first form of [I, (8.20)] and its variants `y = y'`, `y = x`). The fixed atoms are the root
  atom `x` and the internal end `y` of a solid or diffusive tip; `𝔟` and the components at `⊕`,
  `⊖` are dropped (`ErrForms.gA2`, `ErrForms.gA1`). The dropped components are bounded by their
  supremum and the tip at `y` by `B^{1/2}_{y𝔟}`; the sum over `y` is the convolution
  `Σ_y B^{3/2}_{xy} B^{1/2}_{y𝔟} ≲ W^{-d/2} B^{1/2}_{x𝔟}`.
* **`𝔟` in a waved or dotted block of `𝒢₀`**. Every dotted edge `𝔟–y` is contracted (`y ↦ 𝔟`),
  the dotted loops are removed, and the fixed atoms are `x` and `𝔟` (`ErrForms.gB2`), or `𝔟`
  alone with the factor `1_{x = 𝔟}` when the root atom is forced to `𝔟` (`ErrForms.gB1`). A solid
  edge whose ends are both contracted to `𝔟` comes with its `×`-dotted edge, so the term
  `G_{𝔟𝔟} 1_{𝔟 ≠ 𝔟}` vanishes.

In both cases the graph with its fixed atoms made internal is normal regular and doubly connected,
inherited from `g`, and its scaling order is read off the scaling order of `g`, the number of its
dotted edges and the number of contracted atoms (`ErrForms.effOrd`). With dot excess `0` this is at
least the diagonal scaling order `n_𝔟` (`ErrForms.diagOrd_le_effOrd`). The pointwise bounds of the
components on the data record `gData` ([I, (1.8)], [I, Lemma 2.2], [I, Lemma 6.2]) and the three
convolutions of `B` on `ℤ_L^d` complete the bounds `|𝒢_{x, 𝔟𝔟}| ≺ W^{-(n_𝔟 - 1)d/2} B^{1/2}_{x𝔟}`
(or `W^{-(n_𝔟 - 2)d/2} 1_{x = 𝔟}`) and `Σ_x B_{𝔞x} |𝒢_{x, 𝔟𝔟}| ≺ W^{-n_𝔟 d/2}` of the proof of
[I, (8.17)].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

open private rest_term from RBM8D.Diffusion.ErrBound
open private brk_pos₁ le_brk₁ bB_pos₁ bB_le_rpow rpow_mul_sqrt_bB_le sqrt_bB_eq comp_le compBnd lamW
  gData_inputs sqrtB_norms weakNorm_le_mul strongNorm_le_mul im_pos_of_specDom
  from RBM8D.Bound.Doubly

namespace ErrForms

variable {n k : ℕ}

/-! ## Pinning internal atoms -/

/-- A component with an end at `⊗`. -/
def atT (c : Comp (Atom 3 n)) : Bool := c.x == .inl 0 || c.y == .inl 0

/-- The internal atoms that a pinning `P` leaves internal. -/
abbrev Free (P : Fin n → Option (Fin k)) : Type := {i : Fin n // P i = none}

/-- The number of internal atoms that a pinning `P` leaves internal. -/
def nFree (P : Fin n → Option (Fin k)) : ℕ := Fintype.card (Free P)

/-- An enumeration of the internal atoms that a pinning leaves internal. -/
def freeEquiv (P : Fin n → Option (Fin k)) : Free P ≃ Fin (nFree P) := Fintype.equivFin _

/-- The atom map of a pinning `P : Fin n → Option (Fin k)` of the internal atoms of a graph with
external atoms `⊗`, `⊕`, `⊖`: the external atoms go to the external atom `β`, an internal atom `i`
with `P i = some a` goes to the external atom `a`, and the other internal atoms stay internal. -/
def pinAtom (β : Fin k) (P : Fin n → Option (Fin k)) : Atom 3 n → Atom k (nFree P)
  | .inl _ => .inl β
  | .inr i => match h : P i with
    | some a => .inl a
    | none => .inr (freeEquiv P ⟨i, h⟩)

/-- A pinned internal atom goes to its external atom. -/
theorem pinAtom_some {β : Fin k} {P : Fin n → Option (Fin k)} {i : Fin n} {a : Fin k}
    (h : P i = some a) : pinAtom β P (.inr i) = .inl a := by
  simp only [pinAtom]
  split <;> simp_all

/-- A free internal atom stays internal. -/
theorem pinAtom_none {β : Fin k} {P : Fin n → Option (Fin k)} {i : Fin n} (h : P i = none) :
    pinAtom β P (.inr i) = .inr (freeEquiv P ⟨i, h⟩) := by
  simp only [pinAtom]
  split
  · simp_all
  · rfl

/-- The graph obtained from `g` by keeping the components with `p` that are not at `⊗` and moving
their ends by `pinAtom β P` ([I, (8.20)]: the fixed atoms of the bound of `𝒢_{x, 𝔟𝔟}`). -/
def pin (g : Graph 3 n) (p : Comp (Atom 3 n) → Bool) (β : Fin k)
    (P : Fin n → Option (Fin k)) : Graph k (nFree P) :=
  ⟨(g.comps.filter fun c => p c && !atT c).map (Comp.map (pinAtom β P)), g.coeff⟩

/-- **The sum over the labels of a pinned graph**: summing over the labels `t` of the free
internal atoms is summing over the labels `s` of all internal atoms with the pinned atoms labelled
by their external atoms. -/
theorem sum_pin {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (β : Fin k)
    (P : Fin n → Option (Fin k)) (e : Fin k → ι) (F : (Atom 3 n → ι) → M) :
    ∑ t : Fin (nFree P) → ι, F (Sum.elim e t ∘ pinAtom β P) =
      ∑ s : Fin n → ι, if (∀ i a, P i = some a → s i = e a) then
        F (Sum.elim (fun _ => e β) s) else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun t i => Sum.elim e t (pinAtom β P (.inr i)))
    (fun s u => s ((freeEquiv P).symm u).1) ?_ ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i a h
    rw [pinAtom_some h]
    rfl
  · intro s _
    exact Finset.mem_univ _
  · intro t _
    funext u
    have h := ((freeEquiv P).symm u).2
    simp only
    rw [pinAtom_none h]
    simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    funext i
    rcases hP : P i with _ | a
    · rw [pinAtom_none hP]
      simp
    · rw [pinAtom_some hP]
      exact (hs i a hP).symm
  · intro t _
    congr 1
    funext u
    rcases u with a | i
    · rfl
    · rfl

/-- The same identity for the absolute-value graph. -/
theorem absVal_pin {ι : Type*} [Fintype ι] [DecidableEq ι] (g : Graph 3 n)
    (p : Comp (Atom 3 n) → Bool) (β : Fin k) (P : Fin n → Option (Fin k)) (D : Data ι)
    (e : Fin k → ι) :
    (pin g p β P).absVal D e = ∑ s : Fin n → ι, if (∀ i a, P i = some a → s i = e a) then
      ‖g.coeff.eval D.m‖ * ((g.comps.filter fun c => p c && !atT c).map
        fun c => ‖Comp.val D (Sum.elim (fun _ => e β) s) c‖).prod else 0 := by
  rw [← sum_pin β P e (fun σ => ‖g.coeff.eval D.m‖ *
    ((g.comps.filter fun c => p c && !atT c).map fun c => ‖Comp.val D σ c‖).prod)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [pin, List.map_map]
  congr 2
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, Comp.val, Comp.map, List.map_map]
  rfl

/-! ## The root data and the value of the rooted graph -/

/-- The root data of [II, Def 3.3 (4)]: the component `j` is the plain edge `Θ_{⊗v}` with
`v ≠ ⊗`, and no other component reads `⊗` (neither in its ends nor in its minor). -/
structure Rooted (g : Graph 3 n) (j : Fin g.comps.length) (v : Atom 3 n) : Prop where
  ne : v ≠ .inl 0
  kind : g.comps[j].kind = .theta []
  ends : g.comps[j].x = .inl 0 ∧ g.comps[j].y = v
  rest : ∀ c ∈ (g.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor

/-- The components of `g` not at `⊗` are, up to order, the components other than the root edge. -/
theorem filter_atT_perm {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) : (g.comps.filter fun c => !atT c).Perm (g.comps.eraseIdx j) := by
  have hp : g.comps.Perm (g.comps[j] :: g.comps.eraseIdx j) :=
    (List.getElem_cons_eraseIdx_perm j.2).symm
  refine (hp.filter _).trans ?_
  have h1 : (!atT g.comps[j]) = false := by
    have := hR.ends.1
    simp only [Fin.getElem_fin] at this
    simp [atT, this]
  rw [List.filter_cons_of_neg (by simpa [Fin.getElem_fin] using h1)]
  rw [List.filter_eq_self.2 fun c hc => ?_]
  obtain ⟨h1, h2, -⟩ := hR.rest c hc
  simp [atT, h1, h2]

/-- A component other than a plain `Θ` edge is not at `⊗`. -/
theorem atT_eq_false {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    {c : Comp (Atom 3 n)} (hc : c ∈ g.comps) (hk : c.kind ≠ .theta []) : atT c = false := by
  have hmem : c ∈ g.comps.eraseIdx j := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    refine List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, fun h => hk ?_, rfl⟩
    have := hR.kind
    simp only [Fin.getElem_fin] at this
    subst h
    exact this
  obtain ⟨h1, h2, -⟩ := hR.rest c hmem
  simp [atT, h1, h2]

/-! ## The contraction forms: `𝔟` in a waved or dotted block of the core -/

/-- The internal atom `i` is an end of a dotted edge. By the normal regular property of `g`
([I, Def 2.11 (iii)]) the other end is `⊕` or `⊖`, so in the core `𝒢₀` this is a dotted edge
`𝔟–i`. -/
def dotB (g : Graph 3 n) (i : Fin n) : Bool :=
  g.comps.any fun c => decide (c.kind = .dot) && (c.x == .inr i || c.y == .inr i)

/-- The components kept in the contraction forms: all but the dotted edges. -/
def nd (c : Comp (Atom 3 n)) : Bool := decide (c.kind ≠ .dot)

/-- The pinning of the contraction forms: every internal atom dotted to `⊕` or `⊖` goes to the
external atom `β` (the atom `𝔟`), the root atom `v` (if internal and not dotted) to the external
atom `r` (the atom `x`); the other internal atoms stay internal. -/
def pB (g : Graph 3 n) (v : Atom 3 n) (β r : Fin k) : Fin n → Option (Fin k) :=
  fun i => if dotB g i then some β else if Sum.inr i = v then some r else none

/-- **The graph with fixed atoms `x` and `𝔟`** of the contraction forms of [I, (8.20)]: the root
edge and the dotted edges are removed, every atom dotted to `⊕` or `⊖` is identified with `𝔟`, the
root atom is the external atom `x = 0`, and `⊕ = ⊖ = 𝔟` is the external atom `1`. -/
def gB2 (g : Graph 3 n) (v : Atom 3 n) : Graph 2 (nFree (pB g v (1 : Fin 2) 0)) :=
  pin g nd 1 (pB g v 1 0)

/-- **The graph with the fixed atom `𝔟`** of the contraction forms in which the root atom is forced
to `𝔟` (the root atom is `⊕` or `⊖`, or is dotted to one of them): the root edge and the dotted
edges are removed and every atom dotted to `⊕` or `⊖`, the root atom included, is identified with
the external atom `𝔟 = 0`. -/
def gB1 (g : Graph 3 n) (v : Atom 3 n) : Graph 1 (nFree (pB g v (0 : Fin 1) 0)) :=
  pin g nd 0 (pB g v 0 0)

/-- The product of dotted edges at a labelling is `1` if every one joins equal labels, else `0`. -/
theorem prod_dots {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (σ : V → ι)
    (l : List (Comp V)) (hl : ∀ c ∈ l, c.kind = .dot) :
    (l.map (Comp.val D σ)).prod = if ∀ c ∈ l, σ c.x = σ c.y then 1 else 0 := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have hc : Comp.val D σ c = if σ c.x = σ c.y then 1 else 0 := by
      obtain ⟨κ, x, y, mi, lab⟩ := c
      have : κ = .dot := hl _ (List.mem_cons_self ..)
      subst this
      rfl
    rw [List.map_cons, List.prod_cons, hc, ih fun c hc => hl c (List.mem_cons_of_mem _ hc)]
    by_cases h1 : σ c.x = σ c.y <;> by_cases h2 : ∀ c ∈ l, σ c.x = σ c.y <;> simp [h1, h2]

/-- The dotted edges of `g` (none of which is at `⊗`) join equal labels under `(⊕, ⊖ ↦ 𝔟; s)`
exactly when every dotted internal atom has the label `𝔟`: every dotted edge has an external end
([I, Def 2.11 (iii)]). -/
theorem dots_iff {ι : Type*} {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v)
    (hdot : ∀ c ∈ g.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    (b : ι) (s : Fin n → ι) :
    (∀ c ∈ g.comps.filter (fun c => !nd c && !atT c),
      Sum.elim (fun _ => b) s c.x = Sum.elim (fun _ => b) s c.y) ↔
      ∀ i, dotB g i = true → s i = b := by
  constructor
  · intro h i hi
    simp only [dotB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq] at hi
    obtain ⟨c, hc, hk, hxy⟩ := hi
    have hT := atT_eq_false hR hc (by rw [hk]; simp)
    have h1 := h c (List.mem_filter.2 ⟨hc, by simp [nd, hk, hT]⟩)
    rcases hxy with hx | hy
    · rcases hdot c hc hk with hl | hl
      · rw [hx] at hl; simp at hl
      · rcases hcy : c.y with a | a
        · rw [hx, hcy] at h1; exact h1
        · rw [hcy] at hl; simp at hl
    · rcases hdot c hc hk with hl | hl
      · rcases hcx : c.x with a | a
        · rw [hy, hcx] at h1; exact h1.symm
        · rw [hcx] at hl; simp at hl
      · rw [hy] at hl; simp at hl
  · intro h c hc
    obtain ⟨hc, hk⟩ := List.mem_filter.1 hc
    have hk' : c.kind = .dot := (by simpa [nd] using hk : c.kind = .dot ∧ _).1
    have hend : ∀ u, (u = c.x ∨ u = c.y) → Sum.elim (fun _ => b) s u = b := by
      intro u hu
      rcases u with a | i
      · rfl
      · refine h i ?_
        simp only [dotB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
          beq_iff_eq]
        exact ⟨c, hc, hk', by rcases hu with hu | hu <;> simp [hu]⟩
    rw [hend _ (Or.inl rfl), hend _ (Or.inr rfl)]

/-! ## The forms with `𝔟` isolated in the core -/

/-- A component between two internal atoms. -/
def bi (c : Comp (Atom 3 n)) : Bool := c.x.isRight && c.y.isRight

/-- The components at `⊕` or `⊖`: the tips and the loops at `𝔟` of the core. -/
def extC (c : Comp (Atom 3 n)) : Bool := !bi c && !atT c

/-- The pinning of the root atom `v` to the external atom `0` (the atom `x`) and of the internal
end `y` of a tip to the external atom `1`. -/
def pA2 (v y : Fin n) : Fin n → Option (Fin 2) :=
  fun i => if i = v then some 0 else if i = y then some 1 else none

/-- The pinning of the root atom `v` to the external atom `0` (the atom `x`). -/
def pA1 (v : Fin n) : Fin n → Option (Fin 1) := fun i => if i = v then some 0 else none

/-- **The graph with fixed atoms `x`, `y`** of the forms with `𝔟` isolated in the core
(the first form of [I, (8.20)] and its variant `y = y'`): the components between internal atoms of
`g`, with the root atom `v` the external atom `x = 0` and the end `y ≠ v` of a tip the external
atom `1`. It is the core `𝒢₀` with `𝔟` and its loops dropped. -/
def gA2 (g : Graph 3 n) (v y : Fin n) : Graph 2 (nFree (pA2 v y)) := pin g bi 0 (pA2 v y)

/-- **The graph with the fixed atom `x`** of the forms with `𝔟` isolated in the core and the tip
at the root atom (`y = x` in [I, (8.20)]): the components between internal atoms of `g`, with the
root atom `v` the external atom `x = 0`. -/
def gA1 (g : Graph 3 n) (v : Fin n) : Graph 1 (nFree (pA1 v)) := pin g bi 0 (pA1 v)

/-- A component between internal atoms without minor reads the labelling only on the internal
atoms. -/
theorem val_elim_congr {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (f f' : V → ι) (s : Fin n → ι) (c : Comp (V ⊕ Fin n)) (hx : c.x.isRight = true)
    (hy : c.y.isRight = true) (hm : c.minor = []) :
    Comp.val D (Sum.elim f s) c = Comp.val D (Sum.elim f' s) c := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp only at hx hy hm
  subst hm
  rcases x with a | a
  · simp at hx
  rcases y with b | b
  · simp at hy
  rfl

/-! ## The internal form of a pinned graph: doubly connected and normal regular -/

/-- A reachability maps to a reachability under `ψ` if every edge does. -/
theorem reach_map {X Y : Type*} {G₁ : SimpleGraph X} {G₂ : SimpleGraph Y} (ψ : X → Y)
    (h : ∀ x y, G₁.Adj x y → G₂.Reachable (ψ x) (ψ y)) {x y : X} (hr : G₁.Reachable x y) :
    G₂.Reachable (ψ x) (ψ y) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- An edge of a graph `fromRel r` with ends `u`, `v` gives a reachability. -/
theorem reach_of_rel {X : Type*} (r : X → X → Prop) {u v : X} (h : r u v) :
    (SimpleGraph.fromRel r).Reachable u v := by
  by_cases e : u = v
  · rw [e]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨e, Or.inl h⟩)

/-- The image of a component under two atom maps is its image under their composition. -/
theorem comp_map_map {U V X : Type*} (f : V → X) (f' : U → V) (c : Comp U) :
    (c.map f').map f = c.map (f ∘ f') := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp only [Comp.map, List.map_map]
  congr 1
  cases lab <;> rfl

/-- The internal label of an atom of `g` in the internal form of a pinned graph. -/
def θ (β : Fin k) (P : Fin n → Option (Fin k)) (u : Atom 3 n) : Fin (k + nFree P) :=
  finSumFinEquiv (pinAtom β P u)

/-- The components of the internal form of a pinned graph. -/
theorem internalize_pin_comps (g : Graph 3 n) (p : Comp (Atom 3 n) → Bool) (β : Fin k)
    (P : Fin n → Option (Fin k)) :
    (pin g p β P).internalize.comps = (g.comps.filter fun c => p c && !atT c).map
      (Comp.map fun u => (Sum.inr (θ β P u) : Atom 0 (k + nFree P))) := by
  simp only [Graph.internalize, Graph.mapAtoms, pin, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, comp_map_map]
  congr 1
  funext u
  simp only [Function.comp_apply, θ]
  rcases pinAtom β P u with a | a <;> simp

/-- A path of waved and dotted edges of `g` maps to one of the internal form of a pinned graph,
when every waved or dotted edge that is not kept joins atoms with one image. -/
theorem molReach_pin {g : Graph 3 n} {p : Comp (Atom 3 n) → Bool} {β : Fin k}
    {P : Fin n → Option (Fin k)}
    (h2 : ∀ c ∈ g.comps, c.kind.joinsMol = true → (p c && !atT c) = false →
      pinAtom β P c.x = pinAtom β P c.y)
    {u u' : Atom 3 n} (h : g.molGraph.Reachable u u') :
    (pin g p β P).internalize.molGraph.Reachable (.inr (θ β P u)) (.inr (θ β P u')) := by
  refine reach_map (fun u => (.inr (θ β P u) : Atom 0 _)) (fun a b hab => ?_) h
  rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
  have one : ∀ a b, (∃ c ∈ g.comps, c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b) →
      (pin g p β P).internalize.molGraph.Reachable (.inr (θ β P a)) (.inr (θ β P b)) := by
    rintro a b ⟨c, hc, hj, rfl, rfl⟩
    by_cases hq : (p c && !atT c) = true
    · refine reach_of_rel _ ⟨c.map fun u => (Sum.inr (θ β P u) : Atom 0 _), ?_, hj, rfl, rfl⟩
      rw [internalize_pin_comps]
      exact List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hq⟩, rfl⟩
    · have := h2 c hc hj (by simpa using hq)
      simp only [θ, this]
      rfl
  rcases hab.2 with h | h
  · exact one a b h
  · exact (one b a h).symm

/-- **The doubly connected property of the internal form of a pinned graph** ([I, Def 6.5]): the
nets of `g` restricted to its components between internal atoms span the internal form, when the
components between internal atoms are kept, every waved or dotted edge that is not kept joins two
atoms with one image, and every atom of the pinned graph is joined to the image of an internal
atom of `g` by a path of waved and dotted edges of `g` (or is the only atom). -/
theorem dc_pin (g : Graph 3 n) (p : Comp (Atom 3 n) → Bool) (β : Fin k)
    (P : Fin n → Option (Fin k)) (hDC : g.DoublyConnected)
    (h1 : ∀ c ∈ g.comps, bi c = true → p c = true)
    (h2 : ∀ c ∈ g.comps, c.kind.joinsMol = true → (p c && !atT c) = false →
      pinAtom β P c.x = pinAtom β P c.y)
    (h3 : ∀ w : Atom k (nFree P), (∃ (u : Atom 3 n) (i : Fin n), pinAtom β P u = w ∧
      g.molGraph.Reachable u (.inr i)) ∨ ∀ w' : Atom k (nFree P), w' = w) :
    (pin g p β P).internalize.DoublyConnected := by
  apply Graph.dc_of_dcl
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hDC
  set I := (pin g p β P).internalize with hI
  set f : Atom 3 n → Atom 0 (k + nFree P) := fun u => .inr (θ β P u) with hf
  have hbiq : ∀ c, bi c = true → c ∈ g.comps → (p c && !atT c) = true := by
    intro c hc hcm
    simp only [bi, Bool.and_eq_true] at hc
    have hx : c.x ≠ .inl 0 := by intro e; rw [e] at hc; simp at hc
    have hy : c.y ≠ .inl 0 := by intro e; rw [e] at hc; simp at hc
    simp [h1 c hcm (by simp [bi, hc.1, hc.2]), atT, hx, hy]
  have hnet : ∀ (L : List (Comp (Atom 3 n))) (a b : Fin n), nrel g L a b →
      Relation.EqvGen (nrel I ((L.filter bi).map (Comp.map f))) (θ β P (.inr a))
        (θ β P (.inr b)) := by
    intro L a b hab
    rcases hab with hm | ⟨c, hc, hca, hcb⟩
    · rcases hm with he | ⟨-, -, hr⟩
      · rw [he]; exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ (Or.inl (Or.inr ⟨rfl, rfl, molReach_pin h2 hr⟩))
    · refine Relation.EqvGen.rel _ _ (Or.inr ⟨c.map f, List.mem_map.2 ⟨c, List.mem_filter.2
        ⟨hc, by simp [bi, hca, hcb]⟩, rfl⟩, ?_, ?_⟩)
      · simp [Comp.map, hca, hf]
      · simp [Comp.map, hcb, hf]
  have hspan : ∀ L : List (Comp (Atom 3 n)), (SimpleGraph.fromRel (nrel g L)).Preconnected →
      (SimpleGraph.fromRel (nrel I ((L.filter bi).map (Comp.map f)))).Preconnected := by
    intro L hL α γ
    rw [reachable_fromRel_iff]
    have hcov : ∀ α : Fin (k + nFree P), (∃ i : Fin n, Relation.EqvGen
        (nrel I ((L.filter bi).map (Comp.map f))) α (θ β P (.inr i))) ∨ ∀ γ, γ = α := by
      intro α
      rcases h3 (finSumFinEquiv.symm α) with ⟨u, i, hu, hr⟩ | hall
      · refine Or.inl ⟨i, Relation.EqvGen.rel _ _ (Or.inl (Or.inr ⟨rfl, rfl, ?_⟩))⟩
        have := molReach_pin h2 (p := p) hr
        simp only [θ, hu, Equiv.apply_symm_apply] at this
        exact this
      · refine Or.inr fun γ => ?_
        have := hall (finSumFinEquiv.symm γ)
        simpa using congrArg finSumFinEquiv this
    have hlink : ∀ i i' : Fin n, Relation.EqvGen (nrel I ((L.filter bi).map (Comp.map f)))
        (θ β P (.inr i)) (θ β P (.inr i')) := by
      intro i i'
      have h := hL i i'
      rw [reachable_fromRel_iff] at h
      induction h with
      | rel a b hab => exact hnet L a b hab
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
    rcases hcov α with ⟨i, hi⟩ | hall
    · rcases hcov γ with ⟨i', hi'⟩ | hall'
      · exact (hi.trans _ _ _ (hlink i i')).trans _ _ _ hi'.symm
      · rw [hall' α]; exact Relation.EqvGen.refl _
    · rw [hall γ]; exact Relation.EqvGen.refl _
  refine ⟨(Lb.filter bi).map (Comp.map f), (Lu.filter bi).map (Comp.map f), ?_, ?_, ?_,
    hspan Lb hsb, hspan Lu hsu⟩
  · rw [← List.map_append, ← List.filter_append, hI, internalize_pin_comps]
    have hs1 : ((Lb ++ Lu).filter bi).Subperm (g.comps.filter bi) := hsub.filter bi
    have hs2 : (g.comps.filter bi).Sublist (g.comps.filter fun c => p c && !atT c) := by
      have : g.comps.filter bi = (g.comps.filter fun c => p c && !atT c).filter bi := by
        rw [List.filter_filter]
        refine List.filter_congr fun c hc => ?_
        by_cases hb : bi c = true
        · simp [hb, hbiq c hb hc]
        · simp [hb]
      rw [this]
      exact List.filter_sublist
    exact subperm_map' (hs1.trans hs2.subperm) _
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact hb c₀ (List.mem_filter.1 hc₀).1
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact hu c₀ (List.mem_filter.1 hc₀).1

/-- A doubly connected graph without external atoms and without dotted edges has any two atoms
joined by a path of waved and diffusive edges: its black net spans, and its molecules are joined by
waved edges. -/
theorem wavedTheta_of_dc {N : ℕ} (Γ : Graph 0 N) (hnd : ∀ c ∈ Γ.comps, c.kind ≠ .dot)
    (h : Γ.DoublyConnected) (a b : Fin N) :
    Γ.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
  obtain ⟨black, -, -, hbk, -, hsb, -⟩ := h
  have hmol : ∀ u v, Γ.molGraph.Adj u v → Γ.wavedThetaGraph.Reachable u v := by
    have one : ∀ u v, (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) →
        Γ.wavedThetaGraph.Reachable u v := by
      rintro u v ⟨c, hc, hj, rfl, rfl⟩
      exact reach_of_rel _ ⟨c, hc, Or.inl ⟨hj, hnd c hc⟩, rfl, rfl⟩
    intro u v huv
    rw [Graph.molGraph, SimpleGraph.fromRel_adj] at huv
    rcases huv.2 with h | h
    · exact one u v h
    · exact (one v u h).symm
  refine reach_map (fun a => (.inr a : Atom 0 N)) (fun a b hab => ?_) (hsb a b)
  rw [Graph.net, SimpleGraph.fromRel_adj] at hab
  have one : ∀ a b, (Γ.SameMol (.inr a) (.inr b) ∨ ∃ i ∈ black,
      Γ.comps[i].x = .inr a ∧ Γ.comps[i].y = .inr b) →
      Γ.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    rintro a b (h | ⟨i, hi, hx, hy⟩)
    · rcases h with h | ⟨-, -, h⟩
      · rw [h]
      · exact reach_map id hmol h
    · rw [← hx, ← hy]
      exact reach_of_rel _ ⟨Γ.comps[i], List.getElem_mem _, Or.inr (hbk i hi), rfl, rfl⟩
  rcases hab.2 with h | h
  · exact one a b h
  · exact (one b a h).symm

/-- **The normal regular property of the internal form of a pinned graph** ([I, Def 2.11]): from
its doubly connected property, when no dotted edge is kept, no kept solid edge has its two ends
pinned to one atom, and the `×`-dotted and solid edges of `g` between atoms with distinct images
come in pairs among the kept components. -/
theorem normal_pin (g : Graph 3 n) (p : Comp (Atom 3 n) → Bool) (β : Fin k)
    (P : Fin n → Option (Fin k)) (hDCI : (pin g p β P).internalize.DoublyConnected)
    (hnd : ∀ c ∈ g.comps, (p c && !atT c) = true → c.kind ≠ .dot)
    (hsol : ∀ c ∈ g.comps, (p c && !atT c) = true → c.kind.isSolid = true →
      pinAtom β P c.x ≠ pinAtom β P c.y)
    (hxs : ∀ c ∈ g.comps, (p c && !atT c) = true → pinAtom β P c.x ≠ pinAtom β P c.y →
      (c.kind = .xdot → ∃ c' ∈ g.comps, (p c' && !atT c') = true ∧ c'.kind.isSolid = true ∧
        (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x)) ∧
      (c.kind.isSolid = true → ∃ c' ∈ g.comps, (p c' && !atT c') = true ∧ c'.kind = .xdot ∧
        (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x))) :
    ∃ C, (pin g p β P).internalize.Normal C := by
  set I := (pin g p β P).internalize with hI
  have hmemI : ∀ c ∈ I.comps, ∃ c₀ ∈ g.comps, (p c₀ && !atT c₀) = true ∧
      c = c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _) := by
    intro c hc
    rw [hI, internalize_pin_comps] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact ⟨c₀, (List.mem_filter.1 hc₀).1, (List.mem_filter.1 hc₀).2, rfl⟩
  have himg : ∀ c₀ ∈ g.comps, (p c₀ && !atT c₀) = true →
      (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)) ∈ I.comps := by
    intro c₀ hc₀ hq
    rw [hI, internalize_pin_comps]
    exact List.mem_map.2 ⟨c₀, List.mem_filter.2 ⟨hc₀, hq⟩, rfl⟩
  have hθ : ∀ u u' : Atom 3 n, θ β P u = θ β P u' ↔ pinAtom β P u = pinAtom β P u' := by
    intro u u'; simp [θ]
  have hnd' : ∀ c ∈ I.comps, c.kind ≠ .dot := by
    intro c hc
    obtain ⟨c₀, hc₀, hq, rfl⟩ := hmemI c hc
    exact hnd c₀ hc₀ hq
  have hwt := wavedTheta_of_dc I hnd' hDCI
  refine ⟨0 + (k + nFree P) + I.comps.length, ⟨le_rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    rcases u with a | a
    · exact a.elim0
    rcases v with b | b
    · exact b.elim0
    refine (hwt a b).mono ?_
    intro x y hxy
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hxy
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
    refine ⟨hxy.1, ?_⟩
    rcases hxy.2 with ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩
    · exact Or.inl ⟨c, hc, h1, h2⟩
    · exact Or.inr ⟨c, hc, h1, h2⟩
  · exact hwt
  · intro c hc hd
    exact absurd hd (hnd' c hc)
  · intro c hc hs
    obtain ⟨c₀, hc₀, hq, rfl⟩ := hmemI c hc
    simp only [Comp.map, ne_eq, Sum.inr.injEq, hθ]
    exact hsol c₀ hc₀ hq hs
  · intro u v huv
    rcases u with a | a
    · exact a.elim0
    rcases v with b | b
    · exact b.elim0
    have hends : ∀ c₀ : Comp (Atom 3 n),
        ((c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).x = .inr a ∧
          (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).y = .inr b ∨
        (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).x = .inr b ∧
          (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).y = .inr a) →
        pinAtom β P c₀.x ≠ pinAtom β P c₀.y := by
      intro c₀ h e
      have e' : θ β P c₀.x = θ β P c₀.y := (hθ _ _).2 e
      simp only [Comp.map, Sum.inr.injEq] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact huv (by rw [← h1, ← h2, e'])
      · exact huv (by rw [← h1, ← h2, e'])
    have transfer : ∀ c₀ c' : Comp (Atom 3 n),
        (c'.x = c₀.x ∧ c'.y = c₀.y ∨ c'.x = c₀.y ∧ c'.y = c₀.x) →
        ((c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).x = .inr a ∧
          (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).y = .inr b ∨
        (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).x = .inr b ∧
          (c₀.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).y = .inr a) →
        ((c'.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).x = .inr a ∧
          (c'.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).y = .inr b ∨
        (c'.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).x = .inr b ∧
          (c'.map fun u => (Sum.inr (θ β P u) : Atom 0 _)).y = .inr a) := by
      intro c₀ c' hc' h
      simp only [Comp.map] at h ⊢
      rcases hc' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> tauto
    constructor
    · rintro ⟨c, hc, hk, hab⟩
      obtain ⟨c₀, hc₀, hq, rfl⟩ := hmemI c hc
      obtain ⟨c', hc', hq', hs', hxy'⟩ := (hxs c₀ hc₀ hq (hends c₀ hab)).1 hk
      exact ⟨_, himg c' hc' hq', hs', transfer c₀ c' hxy' hab⟩
    · rintro ⟨c, hc, hk, hab⟩
      obtain ⟨c₀, hc₀, hq, rfl⟩ := hmemI c hc
      obtain ⟨c', hc', hq', hs', hxy'⟩ := (hxs c₀ hc₀ hq (hends c₀ hab)).2 hk
      exact ⟨_, himg c' hc' hq', hs', transfer c₀ c' hxy' hab⟩

/-! ## Kinds and scaling orders of the pinned graphs -/

/-- The kinds of [II, Def 3.2] pass to a pinned graph. -/
theorem tKinds_pin {N : ℕ} {g : Graph 3 n} (h : g.TKinds N) (p : Comp (Atom 3 n) → Bool)
    (β : Fin k) (P : Fin n → Option (Fin k)) : (pin g p β P).TKinds N := by
  unfold Graph.TKinds at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  have := h c₀ (List.mem_filter.1 hc₀).1
  obtain ⟨κ, x, y, mi, lab⟩ := c₀
  cases mi <;> simp_all [Comp.isTKind, Comp.map]

/-- The scaling order of a pinned graph: the orders of the kept components minus twice the number
of free internal atoms. -/
theorem ord_pin (g : Graph 3 n) (p : Comp (Atom 3 n) → Bool) (β : Fin k)
    (P : Fin n → Option (Fin k)) :
    (pin g p β P).ord = ((g.comps.filter fun c => p c && !atT c).map fun c => c.kind.ord).sum -
      2 * (nFree P : ℤ) := by
  simp only [Graph.ord, pin, List.map_map]
  rfl

/-- The number of free internal atoms of a pinning. -/
theorem nFree_add (P : Fin n → Option (Fin k)) :
    nFree P + (Finset.univ.filter fun i => P i ≠ none).card = n := by
  rw [nFree, Fintype.card_subtype, Finset.card_filter_add_card_filter_not]
  simp

/-- The scaling order of `g` is that of the root edge plus that of the other components, minus
twice the number of internal atoms. -/
theorem sum_ord_eq {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v) :
    (g.comps.map fun c => c.kind.ord).sum =
      2 + ((g.comps.filter fun c => !atT c).map fun c => c.kind.ord).sum := by
  have hp : g.comps.Perm (g.comps[j] :: g.comps.eraseIdx j) :=
    (List.getElem_cons_eraseIdx_perm j.2).symm
  rw [(hp.map _).sum_eq, ((filter_atT_perm hR).map _).sum_eq, List.map_cons, List.sum_cons,
    hR.kind]
  rfl

/-- The order of the components not at `⊗` splits along a predicate. -/
theorem sum_ord_split (l : List (Comp (Atom 3 n))) (q : Comp (Atom 3 n) → Bool) :
    ((l.filter fun c => !atT c).map fun c => c.kind.ord).sum =
      ((l.filter fun c => q c && !atT c).map fun c => c.kind.ord).sum +
        ((l.filter fun c => !q c && !atT c).map fun c => c.kind.ord).sum := by
  have hp := List.filter_append_perm q (l.filter fun c => !atT c)
  rw [List.filter_filter, List.filter_filter] at hp
  rw [← (hp.map _).sum_eq, List.map_append, List.sum_append]

/-- The number `|Y|` of internal atoms dotted to `⊕` or `⊖`. -/
def nDotted (g : Graph 3 n) : ℕ := (Finset.univ.filter fun i => dotB g i = true).card

/-- **The effective diagonal order** `ord g + 2|Y| − 2 #dots`: the scaling order of `g` after the
dotted edges at `⊕`, `⊖` are contracted (each contracted atom removes `2` from the count of
internal atoms, each removed dotted edge removes its order `2`). -/
def effOrd (g : Graph 3 n) : ℤ := g.ord + 2 * (nDotted g : ℤ) - 2 * (g.nDots : ℤ)

/-- The scaling order of the components at `⊕`, `⊖` (the tips and the loops at `𝔟`). -/
def extOrd (g : Graph 3 n) : ℤ := ((g.comps.filter extC).map fun c => c.kind.ord).sum

/-- The dotted edges are the dotted edges not at `⊗`, and contribute `2` each. -/
theorem sum_ord_dots {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) :
    ((g.comps.filter fun c => !nd c && !atT c).map fun c => c.kind.ord).sum =
      2 * (g.nDots : ℤ) := by
  have e : (g.comps.filter fun c => !nd c && !atT c) =
      g.comps.filter fun c => decide (c.kind = .dot) := by
    refine List.filter_congr fun c hc => ?_
    by_cases hk : c.kind = .dot
    · have := atT_eq_false hR hc (by rw [hk]; simp)
      simp [nd, hk, this]
    · simp [nd, hk]
  rw [e, Graph.nDots]
  have : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c.kind = .dot) →
      (l.map fun c => c.kind.ord).sum = 2 * (l.length : ℤ) := by
    intro l hl
    induction l with
    | nil => simp
    | cons c l ih =>
      rw [List.map_cons, List.sum_cons, ih fun c hc => hl c (List.mem_cons_of_mem _ hc),
        hl c (List.mem_cons_self ..)]
      simp [Kind.ord]; ring
  exact this _ fun c hc => by simpa using (List.mem_filter.1 hc).2

/-- **Order of `gB2`**: `ord gB2 = effOrd g`. -/
theorem ord_gB2 {g : Graph 3 n} {j : Fin g.comps.length} {v : Fin n} (hR : Rooted g j (.inr v))
    (hv : dotB g v = false) : (gB2 g (.inr v)).ord = effOrd g := by
  have hc : (Finset.univ.filter fun i => pB g (.inr v) (1 : Fin 2) 0 i ≠ none).card =
      nDotted g + 1 := by
    have : (Finset.univ.filter fun i => pB g (.inr v) (1 : Fin 2) 0 i ≠ none) =
        insert v (Finset.univ.filter fun i => dotB g i = true) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      unfold pB
      by_cases h1 : dotB g i = true
      · simp [h1]
      · by_cases h2 : i = v
        · subst h2; split_ifs <;> simp_all
        · simp [h1, h2]
    rw [this, Finset.card_insert_of_notMem (by simp [hv]), nDotted]
  have hn := nFree_add (pB g (.inr v) (1 : Fin 2) 0)
  rw [hc] at hn
  have h1 := sum_ord_eq hR
  have h2 := sum_ord_split g.comps nd
  have h3 := sum_ord_dots hR
  rw [gB2, ord_pin, effOrd, Graph.ord]
  have hn' : (nFree (pB g (.inr v) (1 : Fin 2) 0) : ℤ) = n - nDotted g - 1 := by omega
  rw [hn']
  linarith

/-- **Order of `gB1`**: `ord gB1 = effOrd g − 2` (the root atom is forced to `𝔟`). -/
theorem ord_gB1 {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    (hv : ∀ i, v = .inr i → dotB g i = true) : (gB1 g v).ord = effOrd g - 2 := by
  have hc : (Finset.univ.filter fun i => pB g v (0 : Fin 1) 0 i ≠ none).card = nDotted g := by
    have : (Finset.univ.filter fun i => pB g v (0 : Fin 1) 0 i ≠ none) =
        Finset.univ.filter fun i => dotB g i = true := by
      ext i
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      unfold pB
      by_cases h1 : dotB g i = true
      · simp [h1]
      · have : Sum.inr i ≠ v := fun e => h1 (hv i e.symm)
        simp [h1, this]
    rw [this, nDotted]
  have hn := nFree_add (pB g v (0 : Fin 1) 0)
  rw [hc] at hn
  have h1 := sum_ord_eq hR
  have h2 := sum_ord_split g.comps nd
  have h3 := sum_ord_dots hR
  rw [gB1, ord_pin, effOrd, Graph.ord]
  have hn' : (nFree (pB g v (0 : Fin 1) 0) : ℤ) = n - nDotted g := by omega
  rw [hn']
  linarith

/-- **Order of `gA2`**: `ord gA2 = ord g + 2 − Σ_{components at ⊕, ⊖} ord`. -/
theorem ord_gA2 {g : Graph 3 n} {j : Fin g.comps.length} {v' : Atom 3 n} (hR : Rooted g j v')
    {v y : Fin n} (hvy : v ≠ y) : (gA2 g v y).ord = g.ord + 2 - extOrd g := by
  have hc : (Finset.univ.filter fun i => pA2 v y i ≠ none).card = 2 := by
    have : (Finset.univ.filter fun i => pA2 v y i ≠ none) = {v, y} := by
      ext i
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      simp only [Finset.mem_univ, true_and]
      unfold pA2
      by_cases h1 : i = v
      · simp [h1]
      · by_cases h2 : i = y
        · subst h2; split_ifs <;> simp_all
        · simp [h1, h2]
    rw [this, Finset.card_pair hvy]
  have hn := nFree_add (pA2 v y)
  rw [hc] at hn
  have h1 := sum_ord_eq hR
  have h2 := sum_ord_split g.comps bi
  rw [gA2, ord_pin, extOrd, Graph.ord]
  have hn' : (nFree (pA2 v y) : ℤ) = n - 2 := by omega
  have e : (g.comps.filter extC) = g.comps.filter fun c => !bi c && !atT c := rfl
  rw [hn', e]
  linarith

/-- **Order of `gA1`**: `ord gA1 = ord g − Σ_{components at ⊕, ⊖} ord`. -/
theorem ord_gA1 {g : Graph 3 n} {j : Fin g.comps.length} {v' : Atom 3 n} (hR : Rooted g j v')
    (v : Fin n) : (gA1 g v).ord = g.ord - extOrd g := by
  have hc : (Finset.univ.filter fun i => pA1 v i ≠ none).card = 1 := by
    have : (Finset.univ.filter fun i => pA1 v i ≠ none) = {v} := by
      ext i
      rw [Finset.mem_filter, Finset.mem_singleton]
      simp only [Finset.mem_univ, true_and]
      unfold pA1
      by_cases h1 : i = v <;> simp [h1]
    rw [this, Finset.card_singleton]
  have hn := nFree_add (pA1 v)
  rw [hc] at hn
  have h1 := sum_ord_eq hR
  have h2 := sum_ord_split g.comps bi
  rw [gA1, ord_pin, extOrd, Graph.ord]
  have hn' : (nFree (pA1 v) : ℤ) = n - 1 := by omega
  have e : (g.comps.filter extC) = g.comps.filter fun c => !bi c && !atT c := rfl
  rw [hn', e]
  linarith

/-! ## The two cases: `𝔟` in a waved or dotted block of the core, or `𝔟` isolated -/

/-- **`𝔟` lies in a waved or dotted block of the core**: some waved or dotted edge joins `⊕` or `⊖`
to an internal atom. Its negation is the case of the first form of [I, (8.20)] (`𝔟` isolated in
`𝒢₀`, up to loops at `𝔟`). -/
def CaseB (g : Graph 3 n) : Prop :=
  ∃ c ∈ g.comps, c.kind.joinsMol = true ∧
    ((c.x = .inl 1 ∨ c.x = .inl 2) ∧ c.y.isRight = true ∨
      (c.y = .inl 1 ∨ c.y = .inl 2) ∧ c.x.isRight = true)

/-- `pinAtom` is injective on the internal atoms when no two internal atoms are pinned to one
external atom. -/
theorem pinAtom_inr_inj {β : Fin k} {P : Fin n → Option (Fin k)}
    (hP : ∀ i i' a, P i = some a → P i' = some a → i = i') {i i' : Fin n}
    (h : pinAtom β P (.inr i) = pinAtom β P (.inr i')) : i = i' := by
  rcases h1 : P i with _ | a <;> rcases h2 : P i' with _ | a'
  · rw [pinAtom_none h1, pinAtom_none h2] at h
    have := (freeEquiv P).injective (Sum.inr_injective h)
    exact congrArg Subtype.val this
  · rw [pinAtom_none h1, pinAtom_some h2] at h; cases h
  · rw [pinAtom_some h1, pinAtom_none h2] at h; cases h
  · rw [pinAtom_some h1, pinAtom_some h2] at h
    cases h
    exact hP i i' a h1 h2

/-- The paired `×`-dotted and solid edges of a normal regular graph are kept by a pinning whose
choice of kept components depends only on the ends of a solid or `×`-dotted edge. -/
theorem xs_of_normal {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    {C : ℕ} (hN : g.Normal C) (p : Comp (Atom 3 n) → Bool)
    (hp : ∀ c ∈ g.comps, ∀ c' ∈ g.comps, (c.kind = .xdot ∨ c.kind.isSolid = true) →
      (c'.kind = .xdot ∨ c'.kind.isSolid = true) →
      (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x) → p c = true → p c' = true)
    (β : Fin k) (P : Fin n → Option (Fin k)) :
    ∀ c ∈ g.comps, (p c && !atT c) = true → pinAtom β P c.x ≠ pinAtom β P c.y →
      (c.kind = .xdot → ∃ c' ∈ g.comps, (p c' && !atT c') = true ∧ c'.kind.isSolid = true ∧
        (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x)) ∧
      (c.kind.isSolid = true → ∃ c' ∈ g.comps, (p c' && !atT c') = true ∧ c'.kind = .xdot ∧
        (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x)) := by
  intro c hc hq hne
  have hne' : c.x ≠ c.y := fun e => hne (by rw [e])
  have hpc : p c = true := by simp only [Bool.and_eq_true] at hq; exact hq.1
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨c', hc', hs', hxy⟩ := (hN.2.2 c.x c.y hne').1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    have hT := atT_eq_false hR hc' (by intro e; rw [e] at hs'; simp [Kind.isSolid] at hs')
    exact ⟨c', hc', by simp [hp c hc c' hc' (Or.inl hk) (Or.inr hs') hxy hpc, hT], hs', hxy⟩
  · obtain ⟨c', hc', hk', hxy⟩ := (hN.2.2 c.x c.y hne').2 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    have hT := atT_eq_false hR hc' (by rw [hk']; simp)
    exact ⟨c', hc', by simp [hp c hc c' hc' (Or.inr hk) (Or.inl hk') hxy hpc, hT], hk', hxy⟩

/-- Under a contraction pinning, both ends of a dotted edge go to `𝔟`. -/
theorem pinAtom_dot_end {g : Graph 3 n} {v : Atom 3 n} {β r : Fin k} {c : Comp (Atom 3 n)}
    (hc : c ∈ g.comps) (hk : c.kind = .dot) {u : Atom 3 n} (hu : u = c.x ∨ u = c.y) :
    pinAtom β (pB g v β r) u = .inl β := by
  rcases u with a | i
  · rfl
  · have hd : dotB g i = true := by
      simp only [dotB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
        beq_iff_eq]
      exact ⟨c, hc, hk, by rcases hu with hu | hu <;> simp [← hu]⟩
    exact pinAtom_some (by simp [pB, hd])

/-- The waved and dotted edges dropped by a contraction pinning are the dotted edges, whose ends
both go to `𝔟`. -/
theorem h2_B {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    (β r : Fin k) : ∀ c ∈ g.comps, c.kind.joinsMol = true → (nd c && !atT c) = false →
      pinAtom β (pB g v β r) c.x = pinAtom β (pB g v β r) c.y := by
  intro c hc hj hq
  have hT := atT_eq_false hR hc (by intro e; rw [e] at hj; simp [Kind.joinsMol] at hj)
  have hk : c.kind = .dot := by simpa [nd, hT] using hq
  rw [pinAtom_dot_end hc hk (Or.inl rfl), pinAtom_dot_end hc hk (Or.inr rfl)]

/-- The pinned atom `𝔟` of a contraction pinning is joined to an internal atom by a waved or
dotted edge of `g` in the case `CaseB`. -/
theorem h3_B {g : Graph 3 n} {v : Atom 3 n} {β r : Fin k} (hB : CaseB g) :
    ∃ (u : Atom 3 n) (i : Fin n), pinAtom β (pB g v β r) u = .inl β ∧
      g.molGraph.Reachable u (.inr i) := by
  obtain ⟨c, hc, hj, h⟩ := hB
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases hcy : c.y with a | i
    · rw [hcy] at hy; simp at hy
    refine ⟨c.x, i, by rcases hx with e | e <;> rw [e] <;> rfl, ?_⟩
    rw [← hcy]
    exact reach_of_rel _ ⟨c, hc, hj, rfl, rfl⟩
  · rcases hcx : c.x with a | i
    · rw [hcx] at hx; simp at hx
    refine ⟨c.y, i, by rcases hy with e | e <;> rw [e] <;> rfl, ?_⟩
    rw [← hcx]
    exact (reach_of_rel _ ⟨c, hc, hj, rfl, rfl⟩).symm

/-- A free atom of a pinned graph is the image of an internal atom. -/
theorem h3_free {β : Fin k} {P : Fin n → Option (Fin k)} (t : Fin (nFree P)) :
    pinAtom β P (.inr ((freeEquiv P).symm t).1) = .inr t := by
  rw [pinAtom_none ((freeEquiv P).symm t).2]
  simp

/-- A dotted edge of a normal regular graph is not between internal atoms. -/
theorem nd_of_bi {g : Graph 3 n} {C : ℕ} (hN : g.Normal C) {c : Comp (Atom 3 n)}
    (hc : c ∈ g.comps) (hb : bi c = true) : nd c = true := by
  simp only [bi, Bool.and_eq_true] at hb
  by_contra h
  have hk : c.kind = .dot := by simpa [nd] using h
  rcases hN.1.noIntDot c hc hk with e | e
  · rcases hcx : c.x with a | a <;> rw [hcx] at e hb <;> simp_all
  · rcases hcy : c.y with a | a <;> rw [hcy] at e hb <;> simp_all

/-- **`gB2` is doubly connected** (internal form), in the case `CaseB`, for a root atom internal and
not dotted. -/
theorem dc_gB2 {g : Graph 3 n} {j : Fin g.comps.length} {v : Fin n} (hR : Rooted g j (.inr v))
    {C : ℕ} (hN : g.Normal C) (hDC : g.DoublyConnected) (hv : dotB g v = false)
    (hB : CaseB g) : (gB2 g (.inr v)).internalize.DoublyConnected := by
  refine dc_pin g nd 1 _ hDC (fun c hc hb => nd_of_bi hN hc hb) (h2_B hR 1 0) fun w => Or.inl ?_
  rcases w with a | t
  · fin_cases a
    · exact ⟨.inr v, v, pinAtom_some (by simp [pB, hv]), SimpleGraph.Reachable.refl _⟩
    · exact h3_B hB
  · exact ⟨_, _, h3_free t, SimpleGraph.Reachable.refl _⟩

/-- **`gB1` is doubly connected** (internal form), in the case `CaseB` or without internal atoms. -/
theorem dc_gB1 {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    {C : ℕ} (hN : g.Normal C) (hDC : g.DoublyConnected) (hB : CaseB g ∨ n = 0) :
    (gB1 g v).internalize.DoublyConnected := by
  refine dc_pin g nd 0 _ hDC (fun c hc hb => nd_of_bi hN hc hb) (h2_B hR 0 0) fun w => ?_
  rcases hB with hB | rfl
  · refine Or.inl ?_
    rcases w with a | t
    · rw [Subsingleton.elim a 0]; exact h3_B hB
    · exact ⟨_, _, h3_free t, SimpleGraph.Reachable.refl _⟩
  · refine Or.inr fun w' => ?_
    rcases w with a | t
    · rcases w' with a' | t'
      · rw [Subsingleton.elim a a']
      · exact ((freeEquiv _).symm t').1.elim0
    · exact ((freeEquiv _).symm t).1.elim0

/-- Under the contraction pinning, the kept solid edges have distinct images when no kept
`×`-dotted edge has both ends pinned to one atom. -/
theorem hsol_B {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    {C : ℕ} (hN : g.Normal C) (β r : Fin k)
    (hZ : ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind = .xdot →
      pinAtom β (pB g v β r) c.x ≠ pinAtom β (pB g v β r) c.y) :
    ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind.isSolid = true →
      pinAtom β (pB g v β r) c.x ≠ pinAtom β (pB g v β r) c.y := by
  intro c hc hq hs e
  have hne := hN.2.1 c hc hs
  obtain ⟨c', hc', hk', hxy⟩ := (hN.2.2 c.x c.y hne).2 ⟨c, hc, hs, Or.inl ⟨rfl, rfl⟩⟩
  have hT := atT_eq_false hR hc' (by rw [hk']; simp)
  refine hZ c' hc' (by simp [nd, hk', hT]) hk' ?_
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> [exact e; exact e.symm]

/-- The choice of kept components of the contraction forms keeps the paired solid and `×`-dotted
edges. -/
theorem hp_nd (g : Graph 3 n) : ∀ c ∈ g.comps, ∀ c' ∈ g.comps,
    (c.kind = .xdot ∨ c.kind.isSolid = true) → (c'.kind = .xdot ∨ c'.kind.isSolid = true) →
    (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x) → nd c = true → nd c' = true := by
  intro c _ c' _ _ h' _ _
  rcases h' with h' | h'
  · simp [nd, h']
  · simp only [nd, decide_eq_true_eq]
    intro e; rw [e] at h'; simp [Kind.isSolid] at h'

/-- **`gB2` is normal regular** (internal form), when no kept `×`-dotted edge has both ends pinned
to one atom. -/
theorem normal_gB2 {g : Graph 3 n} {j : Fin g.comps.length} {v : Fin n}
    (hR : Rooted g j (.inr v)) {C : ℕ} (hN : g.Normal C) (hDC : g.DoublyConnected)
    (hv : dotB g v = false) (hB : CaseB g)
    (hZ : ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind = .xdot →
      pinAtom 1 (pB g (.inr v) (1 : Fin 2) 0) c.x ≠ pinAtom 1 (pB g (.inr v) (1 : Fin 2) 0) c.y) :
    ∃ C', (gB2 g (.inr v)).internalize.Normal C' :=
  normal_pin g nd 1 _ (dc_gB2 hR hN hDC hv hB)
    (fun c _ hq => (by simpa [nd] using hq : ¬ c.kind = .dot ∧ _).1)
    (hsol_B hR hN 1 0 hZ) (xs_of_normal hR hN nd (hp_nd g) 1 _)

/-- **`gB1` is normal regular** (internal form), when no kept `×`-dotted edge has both ends pinned
to `𝔟`. -/
theorem normal_gB1 {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    {C : ℕ} (hN : g.Normal C) (hDC : g.DoublyConnected) (hB : CaseB g ∨ n = 0)
    (hZ : ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind = .xdot →
      pinAtom 0 (pB g v (0 : Fin 1) 0) c.x ≠ pinAtom 0 (pB g v (0 : Fin 1) 0) c.y) :
    ∃ C', (gB1 g v).internalize.Normal C' :=
  normal_pin g nd 0 _ (dc_gB1 hR hN hDC hB)
    (fun c _ hq => (by simpa [nd] using hq : ¬ c.kind = .dot ∧ _).1)
    (hsol_B hR hN 0 0 hZ) (xs_of_normal hR hN nd (hp_nd g) 0 _)

/-- In the case `¬ CaseB`, every waved or dotted edge with an end at `⊕` or `⊖` has both ends in
`{⊕, ⊖}`, so that its ends have one image under a pinning. -/
theorem h2_A {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} (hR : Rooted g j v)
    (hA : ¬ CaseB g) (β : Fin k) (P : Fin n → Option (Fin k)) :
    ∀ c ∈ g.comps, c.kind.joinsMol = true → (bi c && !atT c) = false →
      pinAtom β P c.x = pinAtom β P c.y := by
  intro c hc hj hq
  have hT := atT_eq_false hR hc (by intro e; rw [e] at hj; simp [Kind.joinsMol] at hj)
  obtain ⟨hx, hy, -⟩ : c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ True := by
    simp only [atT, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hT
    exact ⟨hT.1, hT.2, trivial⟩
  have hb : bi c = false := by simpa [hT] using hq
  have hext : ∀ u : Atom 3 n, u ≠ .inl 0 → u.isLeft = true → u = .inl 1 ∨ u = .inl 2 := by
    intro u hu hl
    rcases u with a | a
    · fin_cases a
      · exact absurd rfl hu
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simp at hl
  rcases hcx : c.x with a | i <;> rcases hcy : c.y with a' | i'
  · rfl
  · exact absurd ⟨c, hc, hj, Or.inl ⟨hext _ hx (by simp [hcx]), by simp [hcy]⟩⟩ hA
  · exact absurd ⟨c, hc, hj, Or.inr ⟨hext _ hy (by simp [hcy]), by simp [hcx]⟩⟩ hA
  · simp [bi, hcx, hcy] at hb

/-- The choice of kept components of the forms with `𝔟` isolated keeps the paired solid and
`×`-dotted edges. -/
theorem hp_bi (g : Graph 3 n) : ∀ c ∈ g.comps, ∀ c' ∈ g.comps,
    (c.kind = .xdot ∨ c.kind.isSolid = true) → (c'.kind = .xdot ∨ c'.kind.isSolid = true) →
    (c'.x = c.x ∧ c'.y = c.y ∨ c'.x = c.y ∧ c'.y = c.x) → bi c = true → bi c' = true := by
  intro c _ c' _ _ _ hxy hb
  simp only [bi, Bool.and_eq_true] at hb ⊢
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto

/-- No two internal atoms are pinned to one external atom by `pA2`. -/
theorem pA2_inj {v y : Fin n} (hvy : v ≠ y) :
    ∀ i i' a, pA2 v y i = some a → pA2 v y i' = some a → i = i' := by
  intro i i' a h h'
  simp only [pA2] at h h'
  split_ifs at h h' <;> subst_vars <;> simp_all <;> cases h' <;> simp_all

/-- **`gA2` is doubly connected** (internal form), in the case `¬ CaseB`. -/
theorem dc_gA2 {g : Graph 3 n} {j : Fin g.comps.length} {v' : Atom 3 n} (hR : Rooted g j v')
    (hDC : g.DoublyConnected) (hA : ¬ CaseB g) {v y : Fin n} (hvy : v ≠ y) :
    (gA2 g v y).internalize.DoublyConnected := by
  refine dc_pin g bi 0 _ hDC (fun c _ hb => hb) (h2_A hR hA 0 _) fun w => Or.inl ?_
  rcases w with a | t
  · fin_cases a
    · exact ⟨.inr v, v, pinAtom_some (by simp [pA2]), SimpleGraph.Reachable.refl _⟩
    · exact ⟨.inr y, y, pinAtom_some (by simp [pA2, hvy.symm]), SimpleGraph.Reachable.refl _⟩
  · exact ⟨_, _, h3_free t, SimpleGraph.Reachable.refl _⟩

/-- **`gA2` is normal regular** (internal form), in the case `¬ CaseB`. -/
theorem normal_gA2 {g : Graph 3 n} {j : Fin g.comps.length} {v' : Atom 3 n} (hR : Rooted g j v')
    {C : ℕ} (hN : g.Normal C) (hDC : g.DoublyConnected) (hA : ¬ CaseB g) {v y : Fin n}
    (hvy : v ≠ y) : ∃ C', (gA2 g v y).internalize.Normal C' := by
  refine normal_pin g bi 0 _ (dc_gA2 hR hDC hA hvy)
    (fun c hc hq => ?_) (fun c hc hq hs e => ?_) (xs_of_normal hR hN bi (hp_bi g) 0 _)
  · have := nd_of_bi hN hc (by simp only [Bool.and_eq_true] at hq; exact hq.1)
    simpa [nd] using this
  · simp only [Bool.and_eq_true, bi] at hq
    obtain ⟨⟨hx, hy⟩, -⟩ := hq
    have hne := hN.2.1 c hc hs
    rcases hcx : c.x with a | i
    · rw [hcx] at hx; simp at hx
    rcases hcy : c.y with a | i'
    · rw [hcy] at hy; simp at hy
    rw [hcx, hcy] at e hne
    exact hne (congrArg _ (pinAtom_inr_inj (pA2_inj hvy) e))

/-- **`gA1` is doubly connected** (internal form), in the case `¬ CaseB`. -/
theorem dc_gA1 {g : Graph 3 n} {j : Fin g.comps.length} {v' : Atom 3 n} (hR : Rooted g j v')
    (hDC : g.DoublyConnected) (hA : ¬ CaseB g) (v : Fin n) :
    (gA1 g v).internalize.DoublyConnected := by
  refine dc_pin g bi 0 _ hDC (fun c _ hb => hb) (h2_A hR hA 0 _) fun w => Or.inl ?_
  rcases w with a | t
  · rw [Subsingleton.elim a 0]
    exact ⟨.inr v, v, pinAtom_some (by simp [pA1]), SimpleGraph.Reachable.refl _⟩
  · exact ⟨_, _, h3_free t, SimpleGraph.Reachable.refl _⟩

/-- **`gA1` is normal regular** (internal form), in the case `¬ CaseB`. -/
theorem normal_gA1 {g : Graph 3 n} {j : Fin g.comps.length} {v' : Atom 3 n} (hR : Rooted g j v')
    {C : ℕ} (hN : g.Normal C) (hDC : g.DoublyConnected) (hA : ¬ CaseB g) (v : Fin n) :
    ∃ C', (gA1 g v).internalize.Normal C' := by
  refine normal_pin g bi 0 _ (dc_gA1 hR hDC hA v)
    (fun c hc hq => ?_) (fun c hc hq hs e => ?_) (xs_of_normal hR hN bi (hp_bi g) 0 _)
  · have := nd_of_bi hN hc (by simp only [Bool.and_eq_true] at hq; exact hq.1)
    simpa [nd] using this
  · simp only [Bool.and_eq_true, bi] at hq
    obtain ⟨⟨hx, hy⟩, -⟩ := hq
    have hne := hN.2.1 c hc hs
    rcases hcx : c.x with a | i
    · rw [hcx] at hx; simp at hx
    rcases hcy : c.y with a | i'
    · rw [hcy] at hy; simp at hy
    rw [hcx, hcy] at e hne
    have hinj : ∀ i i' a, pA1 v i = some a → pA1 v i' = some a → i = i' := by
      intro i i' a h h'
      simp only [pA1] at h h'
      split_ifs at h h'
      simp_all
    exact hne (congrArg _ (pinAtom_inr_inj hinj e))

/-! ## The bound `B`, the entry hypothesis, and the convolutions on `ℤ_L^d` -/

section Analytic

variable {d L W : ℕ} [NeZero L]

/-- `B_{xy} = B_{yx}`. -/
theorem bB_comm (x y : Zd d L) : bB d L W x y = bB d L W y x := by
  unfold bB
  rw [← zdistInf_neg d L (x - y), neg_sub]

omit [NeZero L] in
/-- `B_{xy}^{1/2} ≤ W^{-d/2}` for `d ≥ 2`, `W ≥ 1`. -/
theorem sqrt_bB_le (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    Real.sqrt (bB d L W x y) ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := rpow_mul_sqrt_bB_le hd hW x y
  have hp : 0 < (W : ℝ) ^ ((d : ℝ) / 2) := by positivity
  rw [Real.rpow_neg hW0.le, ← one_div, le_div_iff₀ hp, mul_comm]
  exact h

omit [NeZero L] in
/-- `B_{xy}^{3/2} = B_{xy} B_{xy}^{1/2}`. -/
theorem bB_three_halves (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ^ ((3 : ℝ) / 2) = bB d L W x y * Real.sqrt (bB d L W x y) := by
  have hB := bB_pos₁ (d := d) (L := L) hW x y
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hB.le (by norm_num)]
  norm_num

omit [NeZero L] in
/-- `B_{xy}^{3/2} ≤ W^{-d} B_{xy}^{1/2}` for `d ≥ 2`, `W ≥ 1`. -/
theorem bB_three_halves_le (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) :
    bB d L W x y ^ ((3 : ℝ) / 2) ≤ (W : ℝ) ^ (-(d : ℝ)) * Real.sqrt (bB d L W x y) := by
  rw [bB_three_halves hW]
  exact mul_le_mul_of_nonneg_right (bB_le_rpow hd hW x y) (Real.sqrt_nonneg _)

/-- The entry hypothesis `|G_{xy} − δ_{xy} m| ≤ Λ B_{xy}^{1/2}` gives `‖G − m‖_{s;(1,1)} ≤ Λ`
([I, (6.13)], `‖B^{1/2}‖_{s;(1,1)} = 1`). -/
theorem strong_of_entry (hW : 1 ≤ W) (G : Matrix (Zd d L) (Zd d L) ℂ) (z : ℂ) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (h : ∀ p q, errAbs G z p q ≤ Λ * Real.sqrt (bB d L W p q)) :
    strongNorm d L W 1 1 (errAbs G z) ≤ Λ := by
  have h1 := strongNorm_le_mul hW 1 1 Λ hΛ (errAbs G z) (fun x y => Real.sqrt (bB d L W x y))
    (fun x y => by
      rw [abs_of_nonneg (show 0 ≤ errAbs G z x y from norm_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact h x y)
  rw [(bB_strongNorm d L W hW).2, mul_one] at h1
  exact h1

/-- The weak-`(1,2)` norm of `B^{1/2}` is bounded: `‖B^{1/2}‖_{w;(1,2)} ≤ C₀` for `d ≥ 8`. -/
theorem weak_sqrtB (hd : 8 ≤ d) : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W →
    ∀ Λ : ℝ, 0 ≤ Λ → ∀ A : Matrix (Zd d L) (Zd d L) ℝ,
      (∀ p q, |A p q| ≤ Λ * Real.sqrt (bB d L W p q)) → weakNorm d L W 1 2 A ≤ C₀ * Λ := by
  obtain ⟨C₀, hC₀, hn⟩ := sqrtB_norms d hd
  refine ⟨C₀, hC₀, fun L W _ hW Λ hΛ A hA => ?_⟩
  have hC0 : 0 < C₀ := by linarith
  have h1 := weakNorm_le_mul (d := d) (L := L) (W := W) 1 2 (Λ * C₀) (by positivity) A
    (fun x y => Real.sqrt (bB d L W x y) / C₀) (fun x y => by
      rw [abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (bB d L W x y) / C₀)]
      calc |A x y| ≤ Λ * Real.sqrt (bB d L W x y) := hA x y
        _ = Λ * C₀ * (Real.sqrt (bB d L W x y) / C₀) := by field_simp)
  calc weakNorm d L W 1 2 A ≤ Λ * C₀ * weakNorm d L W 1 2
        (fun x y => Real.sqrt (bB d L W x y) / C₀) := h1
    _ ≤ Λ * C₀ * 1 := mul_le_mul_of_nonneg_left (hn L W hW).1 (by positivity)
    _ = C₀ * Λ := by ring

omit [NeZero L] in
/-- `Γ(y) = 1` for one point. -/
theorem gammaB_one (y : Fin 1 → Zd d L) : gammaB d L W y = 1 := by
  simp [gammaB, Finset.univ_unique]

/-- **Convolution (C1)** on `ℤ_L^d` ([I, (6.33)]): for `d ≥ 8`, `W ≥ 1`, `L ≥ 2W`,
`Σ_y B^{3/2}_{xy} B^{1/2}_{y𝔟} ≤ C (log₂(L/W) + 2)³ W^{-d/2} B^{1/2}_{x𝔟}`, with `C` depending
on `d` only. -/
theorem conv1 (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
    ∀ x b : Zd d L, ∑ y, bB d L W x y ^ ((3 : ℝ) / 2) * Real.sqrt (bB d L W y b) ≤
      C * logF L W ^ 3 * (W : ℝ) ^ (-((d : ℝ) / 2)) * Real.sqrt (bB d L W x b) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, h⟩ := keyobs2Strong d 1 1 (by omega) one_pos one_pos (by linarith) 1 le_rfl
  refine ⟨max C 0, le_max_right _ _, fun L W _ hW hWL x b => ?_⟩
  have h1 := h L W hW hWL (fun p q => Real.sqrt (bB d L W p q))
    (fun p q => Real.sqrt (bB d L W p q)) x b ![x]
  rw [(bB_strongNorm d L W hW).2, gammaB_one] at h1
  have hs : (W : ℝ) ^ (-(1 : ℝ)) * brk d L W x b ^ (-(1 * (d : ℝ) / 2 - 1)) =
      Real.sqrt (bB d L W x b) := by
    rw [sqrt_bB_eq hW]; congr 2; ring
  rw [hs] at h1
  have hlhs : ∑ y, bB d L W x y ^ ((3 : ℝ) / 2) * Real.sqrt (bB d L W y b) =
      ∑ y, |Real.sqrt (bB d L W y x)| * |Real.sqrt (bB d L W y b)| *
        ∏ i : Fin 1, bB d L W y (![x] i) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      Fin.prod_univ_one, bB_three_halves hW, bB_comm x y]
    simp only [Matrix.cons_val_zero]
    ring
  rw [hlhs]
  refine h1.trans ?_
  have hl : 0 ≤ logF L W ^ (1 + 2) * (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) *
      Real.sqrt (bB d L W x b) := by
    have : 0 ≤ logF L W := by
      unfold logF
      have : (1 : ℝ) ≤ (L : ℝ) / W := by
        rw [le_div_iff₀ (by exact_mod_cast hW)]
        have : (2 * W : ℝ) ≤ L := by exact_mod_cast hWL
        linarith
      have := Real.logb_nonneg (b := 2) (by norm_num) this
      linarith
    positivity
  have e : -(1 * (d : ℝ) / 2) = -((d : ℝ) / 2) := by ring
  calc C * logF L W ^ (1 + 2) * (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) * 1 *
        Real.sqrt (bB d L W x b) * 1 * 1
      = C * (logF L W ^ (1 + 2) * (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) *
          Real.sqrt (bB d L W x b)) := by ring
    _ ≤ max C 0 * (logF L W ^ (1 + 2) * (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) *
          Real.sqrt (bB d L W x b)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hl
    _ = _ := by rw [e]; ring

omit [NeZero L] in
/-- `log₂(L/W) + 2 ≥ 0` for `L ≥ W ≥ 1`. -/
theorem logF_nonneg (hW : 1 ≤ W) (hWL : W ≤ L) : 0 ≤ logF L W := by
  unfold logF
  have : (1 : ℝ) ≤ (L : ℝ) / W := by
    rw [le_div_iff₀ (by exact_mod_cast hW)]
    have : (W : ℝ) ≤ L := by exact_mod_cast hWL
    linarith
  have := Real.logb_nonneg (b := 2) (by norm_num) this
  linarith

/-- `‖B^{1/2}‖_{w;(1,2)} ≥ 0`. -/
theorem weak_sqrtB_nonneg (hW : 1 ≤ W) (a : Zd d L) :
    0 ≤ weakNorm d L W 1 2 (fun p q => Real.sqrt (bB d L W p q)) := by
  have := (normBasic d L W hW 1 2 (fun p q => Real.sqrt (bB d L W p q))).1 a a
  have h0 : 0 < (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hpos' : 0 < |Real.sqrt (bB d L W a a)| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_pos.2 (bB_pos₁ hW a a)
  by_contra hneg
  push Not at hneg
  have : (W : ℝ) ^ (-(1 * (d : ℝ) / 2)) *
      weakNorm d L W 1 2 (fun p q => Real.sqrt (bB d L W p q)) < 0 :=
    mul_neg_of_pos_of_neg h0 hneg
  linarith

/-- **Convolution (C2)** on `ℤ_L^d` ([I, (6.32)]): for `d ≥ 8`, `W ≥ 1`, `L ≥ 2W`,
`Σ_x B_{𝔞x} B^{1/2}_{x𝔟} ≤ C (log₂(L/W) + 2) W^{-d/2}`. -/
theorem conv2 (hd : 8 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
    ∀ a b : Zd d L, ∑ x, bB d L W a x * Real.sqrt (bB d L W x b) ≤
      C * logF L W * (W : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, h⟩ := keyobs3 d 1 2 (by omega) one_pos two_pos (by linarith) 1 le_rfl
  obtain ⟨C₀, hC₀, hw⟩ := weak_sqrtB hd
  refine ⟨max C 0 * C₀, by positivity, fun L W _ hW hWL a b => ?_⟩
  have h1 := h L W hW hWL (fun p q => Real.sqrt (bB d L W p q)) b ![a]
  have hwn := hw L W hW 1 zero_le_one (fun p q => Real.sqrt (bB d L W p q))
    (fun p q => by rw [abs_of_nonneg (Real.sqrt_nonneg _), one_mul])
  rw [gammaB_one] at h1
  have hlhs : ∑ x, bB d L W a x * Real.sqrt (bB d L W x b) =
      ∑ x, |Real.sqrt (bB d L W x b)| * ∏ i : Fin 1, bB d L W x (![a] i) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Fin.prod_univ_one, bB_comm a x]
    simp only [Matrix.cons_val_zero]
    ring
  rw [hlhs]
  refine h1.trans ?_
  have hl := logF_nonneg hW (by omega : W ≤ L)
  have hw0 := weak_sqrtB_nonneg (d := d) hW a
  have e : -(1 * (d : ℝ) / 2) = -((d : ℝ) / 2) := by ring
  rw [e]
  calc C * logF L W ^ 1 * (W : ℝ) ^ (-((d : ℝ) / 2)) * 1 *
        weakNorm d L W 1 2 (fun p q => Real.sqrt (bB d L W p q))
      ≤ max C 0 * logF L W * (W : ℝ) ^ (-((d : ℝ) / 2)) * (C₀ * 1) := by
        rw [pow_one, mul_one]
        gcongr
        exact le_max_left _ _
    _ = _ := by ring

end Analytic

/-! ## Sizes along `adm(c₀, c₁)` -/

/-- Along `adm(c₀, c₁)`, `L ≤ W^{1/c₁}`. -/
theorem L_le_of_adm {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) {W L : ℕ} (h : (W, L) ∈ adm c₀ c₁) :
    (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
  have h1 : (L : ℝ) ^ c₁ ≤ W := h.1
  calc (L : ℝ) = ((L : ℝ) ^ c₁) ^ (1 / c₁) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hc₁.ne', Real.rpow_one]
    _ ≤ (W : ℝ) ^ (1 / c₁) := Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- A constant is at most `W^δ` for `W ≥ (max 1 M)^{1/δ}`. -/
theorem const_le_rpow' {M δ Wr : ℝ} (hδ : 0 < δ) (hW : (max 1 M) ^ (1 / δ) ≤ Wr) :
    M ≤ Wr ^ δ := by
  have h1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  calc M ≤ max 1 M := le_max_right _ _
    _ = ((max 1 M) ^ (1 / δ)) ^ δ := by
        rw [← Real.rpow_mul (by linarith), one_div_mul_cancel hδ.ne', Real.rpow_one]
    _ ≤ Wr ^ δ := Real.rpow_le_rpow (by positivity) hW hδ.le

/-- **`log₂(L/W) + 2 ≤ W^δ`** along `adm(c₀, c₁)` for `W ≥ W₀(δ)`. -/
theorem logF_le_rpow {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ W L : ℕ, (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 1 ≤ L →
      logF L W ≤ (W : ℝ) ^ δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := 1 / c₁ / Real.log 2 * (2 / δ) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(max 1 (A + 2)) ^ (2 / δ), Real.one_le_rpow (le_max_left _ _) (by positivity),
    fun W L hadm hW hL => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := (Real.one_le_rpow (le_max_left _ _) (by positivity)).trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hM : A + 2 ≤ (W : ℝ) ^ (δ / 2) :=
    const_le_rpow' (by positivity) (by rw [show 1 / (δ / 2) = 2 / δ by ring]; exact hW)
  have hlog1 : Real.log ((L : ℝ) / W) ≤ Real.log L :=
    Real.log_le_log (by positivity) (div_le_self hL0.le hW1)
  have hlog2 : Real.log L ≤ 1 / c₁ * Real.log W := by
    rw [← Real.log_rpow hW0]
    exact Real.log_le_log hL0 (L_le_of_adm hc₁ hadm)
  have hlog3 : Real.log W ≤ (W : ℝ) ^ (δ / 2) / (δ / 2) :=
    Real.log_le_rpow_div hW0.le (by positivity)
  have hWd : (1 : ℝ) ≤ (W : ℝ) ^ (δ / 2) := Real.one_le_rpow hW1 (by positivity)
  have hlogb : Real.logb 2 ((L : ℝ) / W) ≤ A * (W : ℝ) ^ (δ / 2) := by
    rw [Real.logb, div_le_iff₀ hl2]
    calc Real.log ((L : ℝ) / W) ≤ 1 / c₁ * ((W : ℝ) ^ (δ / 2) / (δ / 2)) :=
          hlog1.trans (hlog2.trans (mul_le_mul_of_nonneg_left hlog3 (by positivity)))
      _ = A * (W : ℝ) ^ (δ / 2) * Real.log 2 := by
          rw [hA]; field_simp
  unfold logF
  calc Real.logb 2 ((L : ℝ) / W) + 2 ≤ A * (W : ℝ) ^ (δ / 2) + 2 * (W : ℝ) ^ (δ / 2) := by
        linarith
    _ = (A + 2) * (W : ℝ) ^ (δ / 2) := by ring
    _ ≤ (W : ℝ) ^ (δ / 2) * (W : ℝ) ^ (δ / 2) :=
        mul_le_mul_of_nonneg_right hM (by positivity)
    _ = (W : ℝ) ^ δ := by rw [← Real.rpow_add hW0]; ring_nf

/-- **`L ≥ 2W`** along `adm(c₀, c₁)` for `0 < c₀ < 1` and `W ≥ W₀`. -/
theorem two_mul_le_of_adm {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ < 1) :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ W L : ℕ, (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 2 * W ≤ L := by
  set e : ℝ := c₀ / (1 - c₀) with he
  have he0 : 0 < e := div_pos hc₀ (by linarith)
  refine ⟨(max 1 2) ^ (1 / e), Real.one_le_rpow (le_max_left _ _) (by positivity),
    fun W L hadm hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := (Real.one_le_rpow (le_max_left _ _) (by positivity)).trans hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h2 : (2 : ℝ) ≤ (W : ℝ) ^ e := const_le_rpow' he0 hW
  have h1 : (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := hadm.2
  have hL : (W : ℝ) ^ (1 / (1 - c₀)) ≤ L := by
    calc (W : ℝ) ^ (1 / (1 - c₀)) ≤ ((L : ℝ) ^ (1 - c₀)) ^ (1 / (1 - c₀)) :=
          Real.rpow_le_rpow hW0.le h1 (by have : 0 < 1 - c₀ := by linarith
                                          positivity)
      _ = L := by
          rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel (by linarith),
            Real.rpow_one]
  have hsplit : (W : ℝ) ^ (1 / (1 - c₀)) = W * (W : ℝ) ^ e := by
    rw [he, show 1 / (1 - c₀) = 1 + c₀ / (1 - c₀) by field_simp; ring, Real.rpow_add hW0,
      Real.rpow_one]
  have : (2 * W : ℝ) ≤ L := by
    rw [hsplit] at hL
    nlinarith
  exact_mod_cast this

/-! ## The bounds of the components on `gData` -/

section Tips

variable {d L W : ℕ} [NeZero L]

/-- The order of a component with the dotted edges counted `0` (a dotted edge `1_{u = v}` is at
most `1`). -/
def ordNd {V : Type*} (c : Comp V) : ℤ := if c.kind = .dot then 0 else c.kind.ord

/-- A product of nonnegative factors is monotone in the factors. -/
theorem list_prod_le {α : Type*} (l : List α) (f g : α → ℝ) (hf : ∀ a ∈ l, 0 ≤ f a)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h3 : 0 ≤ (l.map f).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx; exact hf b (List.mem_cons_of_mem _ hb)
    exact mul_le_mul h1 h2 h3 ((hf a (List.mem_cons_self ..)).trans h1)

/-- `Π_{c ∈ l} K W^{-a_c d/2} = K^{|l|} W^{-(Σ a_c) d/2}`. -/
theorem list_prod_rpow {α : Type*} (hW : 1 ≤ W) (l : List α) (K : ℝ) (a : α → ℤ) :
    (l.map fun c => K * (W : ℝ) ^ (-((a c : ℝ) * d / 2))).prod =
      K ^ l.length * (W : ℝ) ^ (-((((l.map a).sum : ℤ) : ℝ) * d / 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, ih, pow_succ,
      Int.cast_add]
    rw [show -(((a c : ℝ) + ((l.map a).sum : ℝ)) * d / 2) =
      -((a c : ℝ) * d / 2) + -(((l.map a).sum : ℝ) * d / 2) by ring, Real.rpow_add hW0]
    ring

/-- **The tip bounds on `gData`** ([I, (8.20)]: the components at `⊕`, `⊖`). For a list of
components with the kinds of [II, Def 3.2] that contains the `×`-dotted edge of each of its solid
edges, and a solid or diffusive tip `t₀` from an internal atom `y` to an external atom, under
`|G_{pq} − δ_{pq} m| ≤ Λ B^{1/2}_{pq}`, `1 ≤ Λ ≤ W^{d/2}`, and the pointwise bounds `K₁` of the
waved edges and of the labelled `Θ` edges: at the labelling `(⊗, ⊕, ⊖ ↦ 𝔟; s)`,
`Π_c |c| ≤ (2 K₁ Λ)^{|l|} W^{-(Σ_c ord'(c) - 1) d/2} B^{1/2}_{s_y 𝔟}`, with `ord'` the order with
dotted edges counted `0`. Each factor is bounded by its supremum: `Λ W^{-d/2}` for solid edges and
light weights, `2` for weights, `1` for `×`-dotted and dotted edges, `K₁ W^{-d}` for waved edges and
`K₁ W^{-ord d/2}` for (labelled) `Θ` edges; the tip by `Λ B^{1/2}_{y𝔟}` (solid, with its `×`-dotted
edge) or `K₁ W^{-(ord-1) d/2} B^{1/2}_{y𝔟}` (`Θ`). -/
theorem tip_prod {n : ℕ} (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L)) (N : ℕ)
    (E : Matrix (Zd d L) (Zd d L) ℝ) (K₁ Λ : ℝ) (hK₁ : 1 ≤ K₁) (hΛ : 1 ≤ Λ)
    (hΛW : Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2)) (hm : ‖D.m‖ ≤ 1)
    (hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = E p q)
    (hEB : ∀ p q, E p q ≤ Λ * Real.sqrt (bB d L W p q))
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
      K₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (l : List (Comp (Atom 3 n)))
    (hth : ∀ c ∈ l, ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (hT : ∀ c ∈ l, c.isTKind N = true)
    (hpair : ∀ c ∈ l, c.kind.isSolid = true → ∃ c' ∈ l, c'.kind = .xdot ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)))
    {t₀ : Comp (Atom 3 n)} (ht₀ : t₀ ∈ l) (hk₀ : t₀.kind.isSolid = true ∨ ∃ o, t₀.kind = .theta o)
    {y : Fin n} (he₀ : t₀.x = .inr y ∧ t₀.y.isLeft = true ∨ t₀.y = .inr y ∧ t₀.x.isLeft = true)
    (b : Zd d L) (s : Fin n → Zd d L) :
    (l.map fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod ≤
      (2 * K₁ * Λ) ^ l.length * (W : ℝ) ^ (-(((((l.map ordNd).sum : ℤ) : ℝ) - 1) * d / 2)) *
        Real.sqrt (bB d L W (s y) b) := by
  classical
  set σ : Atom 3 n → Zd d L := Sum.elim (fun _ => b) s with hσ
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hKΛ : 1 ≤ 2 * K₁ * Λ := by nlinarith
  have hRHS : 0 ≤ (2 * K₁ * Λ) ^ l.length *
      (W : ℝ) ^ (-(((((l.map ordNd).sum : ℤ) : ℝ) - 1) * d / 2)) *
        Real.sqrt (bB d L W (s y) b) := by
    have : 0 ≤ 2 * K₁ * Λ := by linarith
    positivity
  by_cases hgood : ∀ c ∈ l, c.kind.isSolid = true → σ c.x ≠ σ c.y
  swap
  · push Not at hgood
    obtain ⟨c, hc, hsol, heq⟩ := hgood
    obtain ⟨c', hc', hk', hxy⟩ := hpair c hc hsol
    have h0 : ‖Comp.val D σ c'‖ = 0 := by
      have heq' : σ c'.x = σ c'.y := by
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact heq
        · rw [h1, h2]; exact heq.symm
      obtain ⟨κ, x, y, mi, lab⟩ := c'
      simp only at hk' heq'
      subst hk'
      simp [Comp.val, heq']
    rw [List.prod_eq_zero (List.mem_map.2 ⟨c', hc', h0⟩)]
    exact hRHS
  have hE : ∀ p q, E p q ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ := by
    intro p q
    calc E p q ≤ Λ * Real.sqrt (bB d L W p q) := hEB p q
      _ ≤ Λ * (W : ℝ) ^ (-((d : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (sqrt_bB_le hd hW p q) (by linarith)
      _ = _ := by ring_nf
  have hΛW' : (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ ≤ 1 := by
    calc (W : ℝ) ^ (-(1 : ℝ) * d / 2) * Λ
        ≤ (W : ℝ) ^ (-(1 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hΛW (by positivity)
      _ = 1 := by rw [← Real.rpow_add hW0]; ring_nf; exact Real.rpow_zero _
  -- the supremum bound of one component
  have hsup : ∀ c ∈ l, ‖Comp.val D σ c‖ ≤ 2 * K₁ * Λ * (W : ℝ) ^ (-((ordNd c : ℝ) * d / 2)) := by
    intro c hc
    by_cases hdot : c.kind = .dot
    · have h1 : ‖Comp.val D σ c‖ ≤ 1 := by
        obtain ⟨κ, x, y, mi, lab⟩ := c
        simp only at hdot
        subst hdot
        simp only [Comp.val]
        split_ifs <;> simp
      simp only [ordNd, hdot, ↓reduceIte, Int.cast_zero, zero_mul, zero_div, neg_zero,
        Real.rpow_zero, mul_one]
      linarith
    · have h1 := comp_le hd hW D N E K₁ 1 Λ hK₁ le_rfl hΛ hm hEeq hE hΛW' hwav σ c
        (hth c hc) (hT c hc) hdot (hgood c hc) False False (fun h => h.elim) (fun h => h.elim)
        (fun h => h.elim)
      refine h1.trans ?_
      unfold compBnd
      simp only [mul_one, ordNd, hdot, ↓reduceIte]
      have hlam : Λ ^ lamW c ≤ Λ := by
        unfold lamW
        split
        · simp
        · simp
        · simp; linarith
      have e : (W : ℝ) ^ (-(c.kind.ord : ℝ) * d / 2) = (W : ℝ) ^ (-((c.kind.ord : ℝ) * d / 2)) := by
        ring_nf
      rw [e]
      have h0 : 0 ≤ (W : ℝ) ^ (-((c.kind.ord : ℝ) * d / 2)) := by positivity
      have hK0 : 0 ≤ K₁ := by linarith
      calc _ = 2 * K₁ * (Λ ^ lamW c * (W : ℝ) ^ (-((c.kind.ord : ℝ) * d / 2))) := by ring
        _ ≤ 2 * K₁ * (Λ * (W : ℝ) ^ (-((c.kind.ord : ℝ) * d / 2))) := by gcongr
        _ = _ := by ring
  -- the bound of the tip
  have hdot₀ : t₀.kind ≠ .dot := by
    rcases hk₀ with h | ⟨o, h⟩
    · intro e; rw [e] at h; simp [Kind.isSolid] at h
    · rw [h]; simp
  have hσ₀ : (σ t₀.x = s y ∧ σ t₀.y = b) ∨ (σ t₀.y = s y ∧ σ t₀.x = b) := by
    rcases he₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [h1]
      refine ⟨rfl, ?_⟩
      rcases ht : t₀.y with a | a
      · rfl
      · rw [ht] at h2; simp at h2
    · right
      rw [h1]
      refine ⟨rfl, ?_⟩
      rcases ht : t₀.x with a | a
      · rfl
      · rw [ht] at h2; simp at h2
  have hB : bB d L W (σ t₀.x) (σ t₀.y) = bB d L W (s y) b := by
    rcases hσ₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, bB_comm]
  have htip : ‖Comp.val D σ t₀‖ ≤
      K₁ * Λ * (W : ℝ) ^ (-((((t₀.kind.ord : ℤ) : ℝ) - 1) * d / 2)) *
        Real.sqrt (bB d L W (s y) b) := by
    have hmin : t₀.minor = [] := by
      have := hT t₀ ht₀
      simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at this
      exact this.1
    rcases hk₀ with hs | ⟨o, ho⟩
    · obtain ⟨κ, x, y', mi, lab⟩ := t₀
      simp only at hs hmin hB ⊢
      subst hmin
      cases κ with
      | G ch =>
        have hne := hgood _ ht₀ hs
        simp only at hne
        have hval : ‖Comp.val D σ (⟨.G ch, x, y', [], lab⟩ : Comp _)‖ = E (σ x) (σ y') := by
          rw [← hEeq]
          simp only [Comp.val, List.map_nil, List.toFinset_nil, hne, ite_false, sub_zero]
          cases ch <;> simp [Charge.apply]
        rw [hval, ← hB]
        have hord : (((Kind.G ch).ord : ℤ) : ℝ) - 1 = 0 := by simp [Kind.ord]
        rw [hord]
        simp only [zero_mul, zero_div, neg_zero, Real.rpow_zero, mul_one]
        calc E (σ x) (σ y') ≤ Λ * Real.sqrt (bB d L W (σ x) (σ y')) := hEB _ _
          _ = 1 * (Λ * Real.sqrt (bB d L W (σ x) (σ y'))) := by ring
          _ ≤ K₁ * (Λ * Real.sqrt (bB d L W (σ x) (σ y'))) := by
              have : 0 ≤ Λ := by linarith
              exact mul_le_mul_of_nonneg_right hK₁ (by positivity)
          _ = _ := by ring
      | _ => simp [Kind.isSolid] at hs
    · have h1 := hth t₀ ht₀ o ho (σ t₀.x) (σ t₀.y)
      have hval : ‖Comp.val D σ t₀‖ = ‖D.chain o (σ t₀.x) (σ t₀.y)‖ := by
        obtain ⟨κ, x, y', mi, lab⟩ := t₀
        simp only at ho
        subst ho
        rfl
      rw [hval]
      refine h1.trans ?_
      rw [ho, hB]
      set a := (W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W (s y) b) with ha
      have ha0 : 0 ≤ a := by positivity
      have ha1 : a ≤ 1 := rpow_mul_sqrt_bB_le hd hW (s y) b
      have haa : a * a ≤ a := by nlinarith
      have hsplit : (W : ℝ) ^ (-(((Kind.theta o).ord : ℝ)) * d / 2) * a =
          (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 1) * d / 2) *
            Real.sqrt (bB d L W (s y) b) := by
        rw [ha, ← mul_assoc, ← Real.rpow_add hW0]
        congr 2
        ring
      calc K₁ * (W : ℝ) ^ (-(((Kind.theta o).ord : ℝ)) * d / 2) * (a * a)
          ≤ K₁ * (W : ℝ) ^ (-(((Kind.theta o).ord : ℝ)) * d / 2) * a := by
            have : 0 ≤ K₁ * (W : ℝ) ^ (-(((Kind.theta o).ord : ℝ)) * d / 2) := by
              have : 0 ≤ K₁ := by linarith
              positivity
            exact mul_le_mul_of_nonneg_left haa this
        _ = K₁ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 1) * d / 2) *
              Real.sqrt (bB d L W (s y) b)) := by rw [mul_assoc, hsplit]
        _ ≤ K₁ * Λ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 1) * d / 2) *
              Real.sqrt (bB d L W (s y) b)) := by
            have : 0 ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 1) * d / 2) *
                Real.sqrt (bB d L W (s y) b) := by positivity
            have : 0 ≤ K₁ := by linarith
            calc _ = K₁ * 1 * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 1) * d / 2) *
                  Real.sqrt (bB d L W (s y) b)) := by ring
              _ ≤ _ := by gcongr
        _ = _ := by ring_nf
  -- the product
  have hperm := List.perm_cons_erase ht₀
  rw [(hperm.map _).prod_eq, List.map_cons, List.prod_cons]
  have hrest := list_prod_le (l.erase t₀) (fun c => ‖Comp.val D σ c‖)
    (fun c => 2 * K₁ * Λ * (W : ℝ) ^ (-((ordNd c : ℝ) * d / 2))) (fun _ _ => norm_nonneg _)
    (fun c hc => hsup c (List.mem_of_mem_erase hc))
  rw [list_prod_rpow hW] at hrest
  have hsum : ((l.map ordNd).sum : ℤ) = ordNd t₀ + ((l.erase t₀).map ordNd).sum := by
    rw [((hperm.map _).sum_eq), List.map_cons, List.sum_cons]
  have hord₀ : ordNd t₀ = t₀.kind.ord := by simp [ordNd, hdot₀]
  have hlen : l.length = (l.erase t₀).length + 1 := by
    rw [hperm.length_eq, List.length_cons]
  have hR0 : 0 ≤ (2 * K₁ * Λ) ^ (l.erase t₀).length *
      (W : ℝ) ^ (-(((((l.erase t₀).map ordNd).sum : ℤ) : ℝ) * d / 2)) := by
    have : 0 ≤ 2 * K₁ * Λ := by linarith
    positivity
  calc ‖Comp.val D σ t₀‖ * ((l.erase t₀).map fun c => ‖Comp.val D σ c‖).prod
      ≤ (K₁ * Λ * (W : ℝ) ^ (-((((t₀.kind.ord : ℤ) : ℝ) - 1) * d / 2)) *
          Real.sqrt (bB d L W (s y) b)) * ((2 * K₁ * Λ) ^ (l.erase t₀).length *
            (W : ℝ) ^ (-(((((l.erase t₀).map ordNd).sum : ℤ) : ℝ) * d / 2))) :=
        mul_le_mul htip hrest (List.prod_nonneg fun x hx => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _) (by
          have : 0 ≤ K₁ * Λ := by nlinarith
          positivity)
    _ ≤ (2 * K₁ * Λ * (W : ℝ) ^ (-((((t₀.kind.ord : ℤ) : ℝ) - 1) * d / 2)) *
          Real.sqrt (bB d L W (s y) b)) * ((2 * K₁ * Λ) ^ (l.erase t₀).length *
            (W : ℝ) ^ (-(((((l.erase t₀).map ordNd).sum : ℤ) : ℝ) * d / 2))) := by
        refine mul_le_mul_of_nonneg_right ?_ hR0
        have : 0 ≤ (W : ℝ) ^ (-((((t₀.kind.ord : ℤ) : ℝ) - 1) * d / 2)) *
            Real.sqrt (bB d L W (s y) b) := by positivity
        have : 0 ≤ K₁ * Λ := by nlinarith
        nlinarith
    _ = _ := by
        rw [hlen, pow_succ, hsum, hord₀, Int.cast_add]
        rw [show -(((t₀.kind.ord : ℝ) + ((((l.erase t₀).map ordNd).sum : ℤ) : ℝ) - 1) * d / 2) =
          -(((t₀.kind.ord : ℝ) - 1) * d / 2) +
            -(((((l.erase t₀).map ordNd).sum : ℤ) : ℝ) * d / 2) by ring, Real.rpow_add hW0]
        ring

end Tips

/-! ## The bounds of the forms -/

/-- `(W^{τ'})^r ≤ W^{τ/2}` when `τ' r ≤ τ/2`, `W ≥ 1`. -/
theorem rpow_rpow_le {Wr τ' r e : ℝ} (hW : 1 ≤ Wr) (h : τ' * r ≤ e) :
    (Wr ^ τ') ^ r ≤ Wr ^ e := by
  rw [← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hW h

/-- `τ' (o − 2) ≤ τ/2` for `τ' = min 1 (τ / (2 (|o − 2| + 1)))`. -/
theorem tau_mul_le {τ o : ℝ} (hτ : 0 < τ) :
    min 1 (τ / (2 * (|o| + 1))) * o ≤ τ / 2 := by
  have hA : 0 < |o| + 1 := by positivity
  have h1 : min 1 (τ / (2 * (|o| + 1))) ≤ τ / (2 * (|o| + 1)) := min_le_right _ _
  have h0 : 0 ≤ min 1 (τ / (2 * (|o| + 1))) := le_min zero_le_one (by positivity)
  calc min 1 (τ / (2 * (|o| + 1))) * o ≤ min 1 (τ / (2 * (|o| + 1))) * (|o| + 1) :=
        mul_le_mul_of_nonneg_left ((le_abs_self o).trans (by linarith)) h0
    _ ≤ τ / (2 * (|o| + 1)) * (|o| + 1) := mul_le_mul_of_nonneg_right h1 hA.le
    _ = τ / 2 := by field_simp

/-! ## The forms with `𝔟` isolated in the core -/

/-- `Σ ord'(c) = Σ ord(c) − 2 #dots` over a list of components. -/
theorem sum_ordNd {V : Type*} (l : List (Comp V)) :
    ((l.map ordNd).sum : ℤ) = (l.map fun c => c.kind.ord).sum -
      2 * ((l.filter fun c => decide (c.kind = .dot)).length : ℤ) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.filter_cons]
    by_cases hc : c.kind = .dot
    · simp only [ordNd, hc, ↓reduceIte, decide_true, List.length_cons]
      simp only [Kind.ord]
      push_cast
      ring
    · simp only [ordNd, hc, ↓reduceIte, decide_false, Bool.false_eq_true]
      ring

/-- The components at `⊕`, `⊖` contain all dotted edges of a normal regular graph. -/
theorem extOrdNd_eq {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) {C : ℕ} (hN : g.Normal C) :
    (((g.comps.filter extC).map ordNd).sum : ℤ) = extOrd g - 2 * (g.nDots : ℤ) := by
  rw [sum_ordNd, extOrd, Graph.nDots, List.filter_filter]
  congr 3
  congr 1
  refine List.filter_congr fun c hc => ?_
  by_cases hk : c.kind = .dot
  · have hT := atT_eq_false hR hc (by rw [hk]; simp)
    have hb : bi c = false := by
      by_contra h
      have := nd_of_bi hN hc (by simpa using h)
      simp [nd, hk] at this
    simp [extC, hk, hT, hb]
  · simp [hk]

/-- In the case `¬ CaseB` no internal atom is dotted, so `effOrd g = ord g − 2 #dots`. -/
theorem effOrd_of_not_caseB {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) {C : ℕ} (hN : g.Normal C) (hA : ¬ CaseB g) :
    effOrd g = g.ord - 2 * (g.nDots : ℤ) := by
  have h0 : nDotted g = 0 := by
    rw [nDotted, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    simp only [dotB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq] at hi
    obtain ⟨c, hc, hk, hxy⟩ := hi
    have hT := atT_eq_false hR hc (by rw [hk]; simp)
    simp only [atT, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hT
    have hext : ∀ u : Atom 3 n, u ≠ .inl 0 → u.isLeft = true → u = .inl 1 ∨ u = .inl 2 := by
      intro u hu hl
      rcases u with a | a
      · fin_cases a
        · exact absurd rfl hu
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp at hl
    have hj : c.kind.joinsMol = true := by rw [hk]; rfl
    rcases hxy with hx | hy
    · rcases hN.1.noIntDot c hc hk with h | h
      · rw [hx] at h; simp at h
      · exact hA ⟨c, hc, hj, Or.inr ⟨hext _ hT.2 h, by simp [hx]⟩⟩
    · rcases hN.1.noIntDot c hc hk with h | h
      · exact hA ⟨c, hc, hj, Or.inl ⟨hext _ hT.1 h, by simp [hy]⟩⟩
      · rw [hy] at h; simp at h
  rw [effOrd, h0]
  simp

/-- A solid or diffusive edge from `⊕` or `⊖` to the internal atom `y`: the tip of the first form
of [I, (8.20)]. -/
def TipAt (g : Graph 3 n) (y : Fin n) : Prop :=
  ∃ t₀ ∈ g.comps, (t₀.kind.isSolid = true ∨ ∃ o, t₀.kind = .theta o) ∧
    ((t₀.x = .inl 1 ∨ t₀.x = .inl 2) ∧ t₀.y = .inr y ∨ (t₀.y = .inl 1 ∨ t₀.y = .inl 2) ∧
      t₀.x = .inr y)

/-- The tip bounds of `tip_prod` for the components of `g` at `⊕`, `⊖`. -/
theorem tip_prod_ext {d L W : ℕ} [NeZero L] {g : Graph 3 n} {j : Fin g.comps.length}
    {v : Atom 3 n} (hR : Rooted g j v) {C N : ℕ} (hN : g.Normal C) (hT : g.TKinds N) {y : Fin n}
    (hTip : TipAt g y) (hd : 2 ≤ d) (hW : 1 ≤ W) (D : Data (Zd d L))
    (E : Matrix (Zd d L) (Zd d L) ℝ) (K₁ Λ : ℝ) (hK₁ : 1 ≤ K₁) (hΛ : 1 ≤ Λ)
    (hΛW : Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2)) (hm : ‖D.m‖ ≤ 1)
    (hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = E p q)
    (hEB : ∀ p q, E p q ≤ Λ * Real.sqrt (bB d L W p q))
    (hwav : ∀ (w : Wave) (p q : Zd d L), ‖Comp.val D id (⟨.waved w, p, q, [], none⟩ : Comp _)‖ ≤
      K₁ * (W : ℝ) ^ (-(2 : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (hth : ∀ c ∈ g.comps, ∀ o, c.kind = .theta o → ∀ p q, ‖D.chain o p q‖ ≤
      K₁ * (W : ℝ) ^ (-((Kind.theta o).ord : ℝ) * d / 2) *
        (((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q)) *
          ((W : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (bB d L W p q))))
    (b : Zd d L) (s : Fin n → Zd d L) :
    ((g.comps.filter fun c => extC c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod ≤
      (2 * K₁ * Λ) ^ (g.comps.filter extC).length *
        (W : ℝ) ^ (-((((extOrd g - 2 * (g.nDots : ℤ) : ℤ) : ℝ) - 1) * d / 2)) *
        Real.sqrt (bB d L W (s y) b) := by
  obtain ⟨t₀, ht₀, hk₀, he⟩ := hTip
  have hext : ∀ c ∈ g.comps, extC c = true ↔
      ((c.x = .inl 1 ∨ c.x = .inl 2 ∨ c.y = .inl 1 ∨ c.y = .inl 2) ∧
        c.x ≠ .inl 0 ∧ c.y ≠ .inl 0) := by
    intro c _
    simp only [extC, bi, atT, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      rcases h1 with h | h
      · rcases hc : c.x with a | a
        · fin_cases a
          · exact absurd hc h2
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · rw [hc] at h; simp at h
      · rcases hc : c.y with a | a
        · fin_cases a
          · exact absurd hc h3
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        · rw [hc] at h; simp at h
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      rcases h1 with h | h | h | h <;> simp [h]
  have hl := extOrdNd_eq hR hN
  have h := tip_prod hd hW D N E K₁ Λ hK₁ hΛ hΛW hm hEeq hEB hwav (g.comps.filter extC)
    (fun c hc => hth c (List.mem_filter.1 hc).1)
    (fun c hc => List.all_eq_true.1 hT c (List.mem_filter.1 hc).1)
    (fun c hc hs => by
      obtain ⟨hcm, hce⟩ := List.mem_filter.1 hc
      obtain ⟨c', hc', hk', hxy⟩ := (hN.2.2 c.x c.y (hN.2.1 c hcm hs)).2
        ⟨c, hcm, hs, Or.inl ⟨rfl, rfl⟩⟩
      refine ⟨c', List.mem_filter.2 ⟨hc', ?_⟩, hk', hxy⟩
      rw [hext c' hc']
      rw [hext c hcm] at hce
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto)
    (List.mem_filter.2 ⟨ht₀, by
      rw [hext t₀ ht₀]
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨by tauto, ?_, ?_⟩
        · rcases h1 with e | e <;> rw [e] <;> simp
        · rw [h2]; simp
      · refine ⟨by tauto, ?_, ?_⟩
        · rw [h2]; simp
        · rcases h1 with e | e <;> rw [e] <;> simp⟩)
    hk₀ (y := y) (by
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; refine ⟨h2, ?_⟩; rcases h1 with e | e <;> rw [e] <;> rfl
      · left; refine ⟨h2, ?_⟩; rcases h1 with e | e <;> rw [e] <;> rfl) b s
  rw [hl] at h
  exact h

/-- Four factors at most `W^{τ/8}` and the factor `W^{τ/4}` give at most `W^τ`. -/
theorem absorb4 {Wr τ a b c e : ℝ} (hW : 1 ≤ Wr) (hτ : 0 < τ) (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hc0 : 0 ≤ c) (he0 : 0 ≤ e) (ha : a ≤ Wr ^ (τ / 8)) (hb : b ≤ Wr ^ (τ / 8))
    (hc : c ≤ Wr ^ (τ / 8)) (he : e ≤ Wr ^ (τ / 8)) :
    a * b * c * e * Wr ^ (τ / 4) ≤ Wr ^ τ := by
  have hW0 : 0 < Wr := by linarith
  calc a * b * c * e * Wr ^ (τ / 4)
      ≤ Wr ^ (τ / 8) * Wr ^ (τ / 8) * Wr ^ (τ / 8) * Wr ^ (τ / 8) * Wr ^ (τ / 4) := by
        gcongr
    _ = Wr ^ (3 * τ / 4) := by
        simp only [← Real.rpow_add hW0]; ring_nf
    _ ≤ Wr ^ τ := Real.rpow_le_rpow_of_exponent_le hW (by linarith)

/-- `(W^{τ₁})^ℓ ≤ W^{τ/8}` for `τ₁ = τ / (8 (ℓ + 1))`. -/
theorem pow_tau₁_le {Wr τ : ℝ} (hW : 1 ≤ Wr) (hτ : 0 < τ) (ℓ : ℕ) :
    (Wr ^ (τ / (8 * ((ℓ : ℝ) + 1)))) ^ ℓ ≤ Wr ^ (τ / 8) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hW ?_
  have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `logF³ ≤ W^{τ/8}` from `logF ≤ W^{τ/24}`. -/
theorem logF_cube_le {Wr τ l : ℝ} (hW : 1 ≤ Wr) (hl0 : 0 ≤ l) (hl : l ≤ Wr ^ (τ / 24)) :
    l ^ 3 ≤ Wr ^ (τ / 8) := by
  calc l ^ 3 ≤ (Wr ^ (τ / 24)) ^ 3 := pow_le_pow_left₀ hl0 hl 3
    _ = Wr ^ (τ / 8) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; ring_nf

/-! ## The effective order and the diagonal order -/

/-- An atom without dotted edges is a dotted block of its own. -/
theorem reach_dot_isolated {k : ℕ} {Γ : Graph k n} {u w : Atom k n}
    (hu : ∀ c ∈ Γ.comps, c.kind = .dot → c.x ≠ u ∧ c.y ≠ u) (h : Γ.dotGraph.Reachable u w) :
    w = u := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with ⟨c, hc, hk, hx, -⟩ | ⟨c, hc, hk, -, hy⟩
    · exact absurd hx (hu c hc hk).1
    · exact absurd hy (hu c hc hk).2

/-- **The diagonal order is at most the effective order** for dot excess `0` ([II, §4.4]: the
dotted edges form a forest). The blocks of the dotted edges are `{⊗}`, the singletons of the
undotted internal atoms, and the blocks of `⊕` and `⊖` (one block when `⊕`, `⊖` lie in one dotted
block); the dotted edges number the atoms minus the blocks, at most `|Y| + 1_{PMBlock}`. So the
contraction of the dotted edges at `𝔟` loses at most the `−2` of `n_𝔟 = diagOrd g`. -/
theorem diagOrd_le_effOrd {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) (hx : g.dotExcess = 0) :
    g.diagOrd ≤ effOrd g := by
  classical
  have hT0 : ∀ c ∈ g.comps, c.kind = .dot → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc hk
    have := atT_eq_false hR hc (by rw [hk]; simp)
    simp only [atT, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at this
    exact this
  have hiso : ∀ i, dotB g i = false → ∀ c ∈ g.comps, c.kind = .dot →
      c.x ≠ .inr i ∧ c.y ≠ .inr i := by
    intro i hi c hc hk
    simp only [dotB, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq, not_and, not_or] at hi
    exact hi c hc hk
  set U := {i : Fin n // dotB g i = false}
  have hU : Fintype.card U + nDotted g = n := by
    have e : (Finset.univ.filter fun i => dotB g i = false) =
        Finset.univ.filter fun i => ¬ (dotB g i = true) := by ext; simp
    rw [Fintype.card_subtype, nDotted, e, add_comm, Finset.card_filter_add_card_filter_not]
    simp
  have hPMiff := Graph.pmBlock_iff_sameBlock g
  have key : ∀ (k₀ : ℕ) (f : Fin k₀ → Fin 3), Function.Injective f → (∀ a, f a ≠ 0 →
      ∀ a', f a' ≠ 0 → f a ≠ f a' → ¬ g.dotGraph.Reachable (.inl (f a)) (.inl (f a'))) →
      k₀ + Fintype.card U ≤ Nat.card g.dotGraph.ConnectedComponent := by
    intro k₀ f hf hpm
    let F : Fin k₀ ⊕ U → g.dotGraph.ConnectedComponent := fun z =>
      g.dotGraph.connectedComponentMk (Sum.elim (fun a => (.inl (f a) : Atom 3 n))
        (fun i => .inr i.1) z)
    have hF : Function.Injective F := by
      intro z z' h
      have hr := SimpleGraph.ConnectedComponent.exact h
      rcases z with a | ⟨i, hi⟩ <;> rcases z' with a' | ⟨i', hi'⟩
      · simp only [Sum.elim_inl] at hr
        by_cases e : f a = f a'
        · rw [hf e]
        · by_cases h0 : f a = 0
          · have := reach_dot_isolated (fun c hc hk => by rw [h0]; exact hT0 c hc hk) hr
            simp only [Sum.inl.injEq] at this
            exact absurd this.symm e
          · by_cases h0' : f a' = 0
            · have := reach_dot_isolated (fun c hc hk => by rw [h0']; exact hT0 c hc hk) hr.symm
              simp only [Sum.inl.injEq] at this
              exact absurd this e
            · exact absurd hr (hpm a h0 a' h0' e)
      · have := reach_dot_isolated (hiso i' hi') hr.symm
        simp at this
      · have := reach_dot_isolated (hiso i hi) hr
        simp at this
      · have := reach_dot_isolated (hiso i hi) hr
        simp only [Sum.elim_inr, Sum.inr.injEq] at this
        subst this
        rfl
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card]
      at this
  have hcard : (if g.pmBlockB then 2 else 3) + Fintype.card U ≤
      Nat.card g.dotGraph.ConnectedComponent := by
    split_ifs with hpm
    · refine key 2 ![0, 1] (by decide) fun a ha a' ha' e => ?_
      fin_cases a <;> fin_cases a' <;> simp_all
    · refine key 3 id Function.injective_id fun a ha a' ha' e hr => ?_
      have hpm' : ¬ g.SameBlock (.inl 1) (.inl 2) := fun h => hpm (hPMiff.2 h)
      fin_cases a <;> fin_cases a' <;> simp only [id, Fin.zero_eta, Fin.mk_one, ne_eq,
        not_true_eq_false] at ha ha' e ⊢
      · exact hpm' hr
      · exact hpm' hr.symm
  have hx' := hx
  unfold Graph.dotExcess at hx'
  rw [Graph.diagOrd, effOrd]
  split_ifs at hcard ⊢ with hpm <;> omega

section Instances

end Instances

end ErrForms

end RBM8D
