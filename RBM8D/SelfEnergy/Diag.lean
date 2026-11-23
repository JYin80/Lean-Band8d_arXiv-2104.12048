module

public import RBM8D.SelfEnergy.Contract
public import RBM8D.SelfEnergy.Step
public import RBM8D.Bound.DoublyDet
public import RBM8D.Bound.GraphSum
public import RBM8D.Graph.QExp.PSteps
public import RBM8D.Graph.QExp.SelRun

@[expose] public section

/-!
# The diagonal bound for self-energy graphs

A graph of `Σ_l` may be diagonal ([I, Def 2.13 (i)]): a dotted edge joins its external atoms
`x = 0` and `y = 1`. For a diagonal graph `Γ` with the shape of an `l`-th order self-energy,
`G13.diagBound` gives `|Γ|^{abs}_{xy} ≤ W^τ W^{-(l-2)d/2} 1_{x=y}` (`G13.diagBoundStmt`), the
diagonal term of [I, (1.26)].

* `Diag.dot_unique`: the dotted edges of the shape form a forest, so a diagonal graph has exactly
  one dotted edge.
* `Diag.atomMap`, `Diag.graph`: `x` and `y` are identified ([I, Def 3.1]), the dotted edge is
  removed, and the internal atom `0` becomes the external atom `y`.
* `Diag.absVal_eq`, `Diag.absVal_ne`: at `x = y` the absolute value of `Γ` is the sum over the
  label `b` of that atom of the absolute value of `Diag.graph` at `(x, b)`; at `x ≠ y` it is `0`.
* `Diag.ord_eq`, `Diag.all_isDetKind`, `Diag.internal`: the identified graph has scaling order
  `l` and deterministic kinds, and its internal form is normal regular and doubly connected, so
  that [I, Cor 6.12] (`detBound`) applies with one atom summed; `Σ_b B_{xb}² ≲ W^{-d}` closes the
  bound.
* A graph without internal atom: its other components are loops at `x = y`; two copies of them,
  each joining `x` and `y`, form a graph to which `detBound` applies at `x = y`, and the square
  root of that bound is the claim. A `×`-dotted edge is a loop and gives `0`; a graph whose only
  component is its dotted edge is bounded through its coefficient.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## One dotted edge -/

/-- The graph on the atoms of a graph with external atoms `x = 0`, `y = 1` whose one edge joins
`x` and `y`. -/
private def Diag_xyGraph (n : ℕ) : SimpleGraph (Atom 2 n) :=
  SimpleGraph.fromRel fun u v => u = .inl 0 ∧ v = .inl 1

/-- If a graph has a dotted edge and every dotted edge joins `x` and `y`, its graph of dotted
edges is the one edge `x – y`. -/
private theorem Diag_dotGraph_eq {n : ℕ} (Γ : Graph 2 n) (h1 : ∃ c ∈ Γ.comps, c.kind = .dot)
    (h2 : ∀ c ∈ Γ.comps, c.kind = .dot →
      (c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0)) :
    Γ.dotGraph = Diag_xyGraph n := by
  obtain ⟨c, hc, hk⟩ := h1
  ext u v
  simp only [Graph.dotGraph, Diag_xyGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, ⟨e, he, hek, rfl, rfl⟩ | ⟨e, he, hek, rfl, rfl⟩⟩ <;> refine ⟨huv, ?_⟩ <;>
      rcases h2 e he hek with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h', h⟩
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨h', h⟩
  · rintro ⟨huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> refine ⟨huv, ?_⟩ <;>
      rcases h2 c hc hk with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨c, hc, hk, h, h'⟩
    · exact Or.inr ⟨c, hc, hk, h, h'⟩
    · exact Or.inr ⟨c, hc, hk, h, h'⟩
    · exact Or.inl ⟨c, hc, hk, h, h'⟩

/-- A diagonal graph whose dotted edges form a forest (`Graph.DotsAcyclic`) has exactly one
dotted edge: with two dotted edges between `x` and `y` the dotted edges contain a cycle. -/
theorem Diag.dot_unique {n : ℕ} (Γ : Graph 2 n) (hD : G13.IsDiag Γ) (hA : Γ.DotsAcyclic) :
    ∃ i : ℕ, ∃ hi : i < Γ.comps.length, Γ.comps[i].kind = .dot ∧
      ∀ c ∈ Γ.comps.eraseIdx i, c.kind ≠ .dot := by
  obtain ⟨⟨c, hc, hk⟩, h2⟩ := hD
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  refine ⟨i, hi, hk, fun e he hek => ?_⟩
  have hperm := List.getElem_cons_eraseIdx_perm hi
  set Γ' : Graph 2 n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ'
  have hg : Γ.dotGraph = Diag_xyGraph n := Diag_dotGraph_eq Γ ⟨_, hc, hk⟩ h2
  have hg' : Γ'.dotGraph = Diag_xyGraph n :=
    Diag_dotGraph_eq Γ' ⟨e, he, hek⟩ fun c' hc' => h2 c' (List.mem_of_mem_eraseIdx hc')
  have hn : Γ.nDots = Γ'.nDots + 1 := by
    unfold Graph.nDots
    rw [← (hperm.filter _).length_eq, List.filter_cons_of_pos (by simpa using hk),
      List.length_cons]
  have h0 := (Graph.dotsAcyclic_iff_dotExcess_eq_zero Γ).1 hA
  have h1 := SelRun_dotExcess_nonneg Γ'
  unfold Graph.dotExcess at h0 h1
  rw [hg, hn] at h0
  rw [hg'] at h1
  push_cast at h0 h1
  omega

/-! ## The identification `x = y` -/

/-- The atom map of the identification of the external atoms `x = 0` and `y = 1`
([I, Def 3.1]), followed by making the internal atom `0` external: `x, y ↦ x`, the internal atom
`0 ↦ y`, the internal atom `i + 1 ↦ i`. -/
def Diag.atomMap (m : ℕ) : Atom 2 (m + 1) → Atom 2 m :=
  Sum.elim (fun _ => .inl 0) (Fin.cons (α := fun _ => Atom 2 m) (.inl 1) Sum.inr)

/-- The atom map `Diag.atomMap` is onto. -/
theorem Diag.atomMap_surjective (m : ℕ) : Function.Surjective (Diag.atomMap m) := by
  rintro (a | a)
  · fin_cases a
    · exact ⟨.inl 0, rfl⟩
    · exact ⟨.inr 0, rfl⟩
  · exact ⟨.inr a.succ, by simp [Diag.atomMap]⟩

/-- The graph `Γ` with its external atoms `x`, `y` identified into `x` and its internal atom `0`
made the external atom `y`: the `i`-th component is removed and the other components are mapped
by `Diag.atomMap`; the coefficient is kept. -/
def Diag.graph {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) : Graph 2 m :=
  ⟨(Γ.comps.eraseIdx i).map (Comp.map (Diag.atomMap m)), Γ.coeff⟩

private theorem Diag_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

/-- The factor of a dotted edge between `x` and `y` is `1(x = y)`. -/
private theorem Diag_val_dot {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (D : Data ι)
    (s : Fin n → ι) (x y : ι) (c : Comp (Atom 2 n)) (hk : c.kind = .dot)
    (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0) :
    ‖Comp.val D (Sum.elim ![x, y] s) c‖ = if x = y then 1 else 0 := by
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · by_cases h : x = y <;> simp [Comp.val, h]
  · by_cases h : x = y
    · simp [Comp.val, h]
    · simp [Comp.val, Ne.symm h, h]

/-- A graph with a dotted edge between `x` and `y` has absolute value `0` at `x ≠ y`. -/
theorem Diag.absVal_ne {n : ℕ} (Γ : Graph 2 n) (c : Comp (Atom 2 n)) (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) {x y : ι} (hne : x ≠ y) :
    Γ.absVal D ![x, y] = 0 := by
  unfold Graph.absVal
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [List.prod_eq_zero, mul_zero]
  exact List.mem_map.2 ⟨c, hc, by rw [Diag_val_dot D s x y c hk hxy]; simp [hne]⟩

private theorem Diag_elim_cons {ι : Type*} {m : ℕ} (x b : ι) (s : Fin m → ι) :
    Sum.elim ![x, x] (Fin.cons (α := fun _ => ι) b s) = Sum.elim ![x, b] s ∘ Diag.atomMap m := by
  funext u
  rcases u with a | u
  · fin_cases a <;> rfl
  · refine Fin.cases ?_ (fun i => ?_) u
    · simp [Diag.atomMap]
    · simp [Diag.atomMap]

/-- **Value.** If the `i`-th component of `Γ` is a dotted edge between `x` and `y`, then at
`x = y` the absolute value of `Γ` is the sum over the label `b` of the former internal atom `0`
of the absolute value of `Diag.graph Γ i` at `(x, b)`. -/
theorem Diag.absVal_eq {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inl 0 ∧ Γ.comps[i].y = .inl 1 ∨
      Γ.comps[i].x = .inl 1 ∧ Γ.comps[i].y = .inl 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) (x : ι) :
    Γ.absVal D ![x, x] = ∑ b, (Diag.graph Γ i).absVal D ![x, b] := by
  have hperm := List.getElem_cons_eraseIdx_perm hi
  have hterm : ∀ s : Fin (m + 1) → ι,
      (Γ.comps.map fun c => ‖Comp.val D (Sum.elim ![x, x] s) c‖).prod =
        ((Γ.comps.eraseIdx i).map fun c => ‖Comp.val D (Sum.elim ![x, x] s) c‖).prod := by
    intro s
    rw [← (hperm.map _).prod_eq, List.map_cons, List.prod_cons, Diag_val_dot D s x x _ hk hxy]
    simp
  unfold Graph.absVal
  simp_rw [hterm]
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [Fin.consEquiv_apply]
  rw [Diag_elim_cons]
  simp only [Diag.graph, List.map_map]
  congr 2
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, Diag_val_map]

/-- **Order.** If the `i`-th component of `Γ` is a dotted edge, `Diag.graph Γ i` has the
scaling order of `Γ`: the dotted edge of order `2` is removed and one internal atom fewer is
summed ([I, (2.12)]). -/
theorem Diag.ord_eq {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot) : (Diag.graph Γ i).ord = Γ.ord := by
  have hperm := (List.getElem_cons_eraseIdx_perm hi).map fun c => c.kind.ord
  unfold Graph.ord
  rw [← hperm.sum_eq, List.map_cons, List.sum_cons, hk]
  simp only [Diag.graph, List.map_map, Function.comp_def, Comp.map, Kind.ord]
  push_cast
  ring

/-- **Kinds.** The components of `Diag.graph Γ i` are of the deterministic kinds of
[II, Def 2.7 (i)] with labels in `[4, N]` when those of `Γ` are. -/
theorem Diag.all_isDetKind {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (N : ℕ)
    (h : Γ.comps.all (Comp.isDetKind N) = true) :
    (Diag.graph Γ i).comps.all (Comp.isDetKind N) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
  rw [Contract.isDetKind_map]
  exact h c (List.mem_of_mem_eraseIdx hc)

/-! ## The internal form after the identification -/

private theorem Diag_reach_fromRel {α : Type*} {r : α → α → Prop} {a b : α} (h : r a b) :
    (SimpleGraph.fromRel r).Reachable a b := by
  by_cases hab : a = b
  · subst hab
    rfl
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩).reachable

private theorem Diag_subperm_of_cons {α : Type*} {d : α} {l r : List α}
    (h : l.Subperm (d :: r)) (hd : d ∉ l) : l.Subperm r := by
  classical
  have := h.erase d
  rwa [List.erase_cons_head, List.erase_of_not_mem hd] at this

private theorem Diag_subperm_map {α β : Type*} (f : α → β) {l r : List α} (h : l.Subperm r) :
    (l.map f).Subperm (r.map f) := by
  obtain ⟨l', hp, hs⟩ := h
  exact ⟨l'.map f, hp.map f, hs.map f⟩

section Transport

variable {N N' : ℕ} {H : Graph 0 N} {H' : Graph 0 N'} {h : Fin N → Fin N'}
  {d : Comp (Atom 0 N)} {rest : List (Comp (Atom 0 N))}

private theorem Diag_mem_rest (hperm : (d :: rest).Perm H.comps) (hd : d.kind = .dot)
    {c : Comp (Atom 0 N)} (hc : c ∈ H.comps) (hk : c.kind ≠ .dot) : c ∈ rest := by
  rcases List.mem_cons.1 (hperm.mem_iff.2 hc) with rfl | h
  · exact absurd hd hk
  · exact h

/-- A path of waved and dotted edges of `H` maps to a path of `H'` in any graph whose relation
holds on the image of each waved edge, when every dotted edge of `H` is collapsed. -/
private theorem Diag_mol_lift (hperm : (d :: rest).Perm H.comps) (hd : d.kind = .dot)
    (hdots : ∀ c ∈ H.comps, c.kind = .dot → Sum.map id h c.x = Sum.map id h c.y)
    {r₂ : Atom 0 N' → Atom 0 N' → Prop}
    (hr : ∀ c ∈ rest, c.kind.joinsMol = true → c.kind ≠ .dot →
      r₂ (Sum.map id h c.x) (Sum.map id h c.y)) {u v : Atom 0 N}
    (huv : H.molGraph.Reachable u v) :
    (SimpleGraph.fromRel r₂).Reachable (Sum.map id h u) (Sum.map id h v) := by
  refine reach_lift _ (fun u v hadj => ?_) huv
  rw [Graph.molGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨-, ⟨c, hc, hj, rfl, rfl⟩ | ⟨c, hc, hj, rfl, rfl⟩⟩ := hadj
  · by_cases hk : c.kind = .dot
    · rw [hdots c hc hk]
    · exact Diag_reach_fromRel (hr c (Diag_mem_rest hperm hd hc hk) hj hk)
  · by_cases hk : c.kind = .dot
    · rw [hdots c hc hk]
    · exact (Diag_reach_fromRel (hr c (Diag_mem_rest hperm hd hc hk) hj hk)).symm

private theorem Diag_sameMol_lift (hperm : (d :: rest).Perm H.comps) (hd : d.kind = .dot)
    (hH' : H'.comps = rest.map (Comp.map (Sum.map id h)))
    (hdots : ∀ c ∈ H.comps, c.kind = .dot → Sum.map id h c.x = Sum.map id h c.y)
    {a b : Fin N} (hm : H.SameMol (.inr a) (.inr b)) :
    H'.SameMol (.inr (h a)) (.inr (h b)) := by
  rcases hm with he | ⟨-, -, hr⟩
  · left
    rw [Sum.inr_injective he]
  · right
    refine ⟨rfl, rfl, ?_⟩
    have := Diag_mol_lift (r₂ := fun u v => ∃ c ∈ H'.comps, c.kind.joinsMol = true ∧
      c.x = u ∧ c.y = v) hperm hd hdots (fun c hc hj _ => ⟨c.map (Sum.map id h),
        hH' ▸ List.mem_map_of_mem hc, hj, rfl, rfl⟩) hr
    exact this

/-- **Doubly connected.** If `H'` is `H` with a dotted edge `d` removed and the atoms mapped
onto by `h`, and every dotted edge of `H` is collapsed by `h`, then `H'` is doubly connected
when `H` is: the two nets are mapped component by component. -/
private theorem Diag_dc (hs : Function.Surjective h) (hperm : (d :: rest).Perm H.comps)
    (hd : d.kind = .dot) (hH' : H'.comps = rest.map (Comp.map (Sum.map id h)))
    (hdots : ∀ c ∈ H.comps, c.kind = .dot → Sum.map id h c.x = Sum.map id h c.y)
    (hDC : H.DoublyConnected) : H'.DoublyConnected := by
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hDC
  have hnd : d ∉ Lb ++ Lu := fun hm => by
    rcases List.mem_append.1 hm with hm | hm
    · have := hb d hm
      rw [hd] at this
      exact absurd this (by decide)
    · rcases hu d hm with h1 | h1 <;> rw [hd] at h1 <;> exact absurd h1 (by decide)
  have hsub' : (Lb ++ Lu).Subperm rest := Diag_subperm_of_cons (hperm.subperm_left.2 hsub) hnd
  have hlift : ∀ L : List (Comp (Atom 0 N)), (SimpleGraph.fromRel (nrel H L)).Preconnected →
      (SimpleGraph.fromRel (nrel H' (L.map (Comp.map (Sum.map id h))))).Preconnected := by
    intro L hL a' b'
    obtain ⟨a, rfl⟩ := hs a'
    obtain ⟨b, rfl⟩ := hs b'
    have key : ∀ a b, nrel H L a b →
        (SimpleGraph.fromRel (nrel H' (L.map (Comp.map (Sum.map id h))))).Reachable
          (h a) (h b) := by
      intro a b hr
      rcases hr with hm | ⟨c, hc, hx, hy⟩
      · exact Diag_reach_fromRel (Or.inl (Diag_sameMol_lift hperm hd hH' hdots hm))
      · refine Diag_reach_fromRel (Or.inr ⟨c.map (Sum.map id h), List.mem_map_of_mem hc, ?_, ?_⟩)
        · simp [Comp.map, hx]
        · simp [Comp.map, hy]
    refine reach_lift h (fun a b hab => ?_) (hL a b)
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with hr | hr
    · exact key a b hr
    · exact (key b a hr).symm
  refine Graph.dc_of_dcl ⟨Lb.map (Comp.map (Sum.map id h)), Lu.map (Comp.map (Sum.map id h)),
    ?_, ?_, ?_, hlift Lb hsb, hlift Lu hsu⟩
  · rw [hH', ← List.map_append]
    exact Diag_subperm_map _ hsub'
  · intro c hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    exact hb c hc'
  · intro c hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    exact hu c hc'

/-- **Waved and `Θ` paths.** Under the hypotheses of `Diag_dc`, any two atoms of `H'` are joined
by a path of waved and diffusive edges: the black net of `H` and its molecules are mapped. -/
private theorem Diag_waved (hs : Function.Surjective h) (hperm : (d :: rest).Perm H.comps)
    (hd : d.kind = .dot) (hH' : H'.comps = rest.map (Comp.map (Sum.map id h)))
    (hdots : ∀ c ∈ H.comps, c.kind = .dot → Sum.map id h c.x = Sum.map id h c.y)
    (hDC : H.DoublyConnected) (a' b' : Fin N') :
    H'.wavedThetaGraph.Reachable (.inr a') (.inr b') := by
  obtain ⟨Lb, Lu, hsub, hb, -, hsb, -⟩ := Graph.dcl_of_dc hDC
  obtain ⟨a, rfl⟩ := hs a'
  obtain ⟨b, rfl⟩ := hs b'
  have himg : ∀ c ∈ rest, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) →
      ∃ c' ∈ H'.comps, (c'.kind.joinsMol = true ∧ c'.kind ≠ .dot ∨ c'.kind.isDiffusive = true) ∧
        c'.x = Sum.map id h c.x ∧ c'.y = Sum.map id h c.y :=
    fun c hc hk => ⟨c.map (Sum.map id h), hH' ▸ List.mem_map_of_mem hc, hk, rfl, rfl⟩
  have key : ∀ a b, nrel H Lb a b →
      H'.wavedThetaGraph.Reachable (.inr (h a)) (.inr (h b)) := by
    intro a b hr
    rcases hr with hm | ⟨c, hc, hx, hy⟩
    · rcases hm with he | ⟨-, -, hr⟩
      · rw [Sum.inr_injective he]
      · exact Diag_mol_lift hperm hd hdots (fun c hc hj hk => himg c hc (Or.inl ⟨hj, hk⟩)) hr
    · have hcH : c ∈ H.comps := hsub.subset (List.mem_append_left _ hc)
      have hdf := hb c hc
      have hk : c.kind ≠ .dot := fun h' => by rw [h'] at hdf; exact absurd hdf (by decide)
      have := himg c (Diag_mem_rest hperm hd hcH hk) (Or.inr hdf)
      rw [hx, hy] at this
      exact Diag_reach_fromRel this
  refine reach_lift (fun a => (Sum.inr (h a) : Atom 0 N')) (fun a b hab => ?_) (hsb a b)
  rw [SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with hr | hr
  · exact key a b hr
  · exact (key b a hr).symm

end Transport

/-- A graph without external atoms whose components are neither dotted, `×`-dotted nor solid,
and in which any two atoms are joined by waved and diffusive edges, is normal regular. -/
private theorem Diag_normal {N' : ℕ} (H' : Graph 0 N')
    (hk : ∀ c ∈ H'.comps, c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false)
    (hw : ∀ a b : Fin N', H'.wavedThetaGraph.Reachable (.inr a) (.inr b)) :
    H'.Normal (N' + H'.comps.length) := by
  have hle : H'.wavedThetaGraph ≤ H'.edgeGraph := by
    intro u v huv
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
    obtain ⟨hne, ⟨c, hc, -, hx, hy⟩ | ⟨c, hc, -, hx, hy⟩⟩ := huv
    · exact ⟨hne, Or.inl ⟨c, hc, hx, hy⟩⟩
    · exact ⟨hne, Or.inr ⟨c, hc, hx, hy⟩⟩
  refine ⟨⟨by simp, ?_, hw, fun c hc hd => absurd hd (hk c hc).1⟩, fun c hc hs => ?_,
    fun u v _ => ?_⟩
  · rintro (u | a) (v | b)
    · exact u.elim0
    · exact u.elim0
    · exact v.elim0
    · exact (hw a b).mono hle
  · rw [(hk c hc).2.2] at hs
    exact absurd hs (by decide)
  · constructor
    · rintro ⟨c, hc, hx, -⟩
      exact absurd hx (hk c hc).2.1
    · rintro ⟨c, hc, hs, -⟩
      rw [(hk c hc).2.2] at hs
      exact absurd hs (by decide)

/-- The atom map of `Graph.internalize`, through `finSumFinEquiv`. -/
private def Diag_int {k n : ℕ} (u : Atom k n) : Atom 0 (k + n) := .inr (finSumFinEquiv u)

private theorem Diag_internalize_comps {k n : ℕ} (Γ : Graph k n) :
    Γ.internalize.comps = Γ.comps.map (Comp.map Diag_int) := by
  have : (Sum.elim (fun a => Sum.inr (Fin.castAdd n a)) (fun b => Sum.inr (Fin.natAdd k b)) :
      Atom k n → Atom 0 (k + n)) = Diag_int := by
    funext u
    rcases u with a | b <;> simp [Diag_int]
  simp only [Graph.internalize, Graph.mapAtoms, this]

private theorem Diag_map_map {U V W : Type*} (f : U → V) (g : V → W) (c : Comp U) :
    (c.map f).map g = c.map (g ∘ f) := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  rcases lab with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map]

/-- `Diag.atomMap` read on the internal forms. -/
private def Diag_hmap (m : ℕ) (p : Fin (2 + (m + 1))) : Fin (2 + m) :=
  finSumFinEquiv (Diag.atomMap m (finSumFinEquiv.symm p))

private theorem Diag_hmap_int (m : ℕ) (u : Atom 2 (m + 1)) :
    Sum.map id (Diag_hmap m) (Diag_int u) = Diag_int (Diag.atomMap m u) := by
  simp [Diag_int, Diag_hmap]

private theorem Diag_hmap_surjective (m : ℕ) : Function.Surjective (Diag_hmap m) := by
  intro q
  obtain ⟨u, hu⟩ := Diag.atomMap_surjective m (finSumFinEquiv.symm q)
  exact ⟨finSumFinEquiv u, by simp [Diag_hmap, hu]⟩

/-- **Internal form.** Let the `i`-th component of the diagonal graph `Γ` be its only dotted
edge, let the other components be neither dotted, `×`-dotted nor solid, and let the internal form
of `Γ` (with `x`, `y` internal) be doubly connected. Then the internal form of `Diag.graph Γ i`
(with the identified atom `x` and the new atom `y` internal) is normal regular and doubly connected:
the hypotheses of [I, Cor 6.12] in the form `detBound`. -/
theorem Diag.internal {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot) (hD : G13.IsDiag Γ)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false)
    (hDC : Γ.internalize.DoublyConnected) :
    (Diag.graph Γ i).internalize.Normal (2 + m + (Diag.graph Γ i).internalize.comps.length) ∧
      (Diag.graph Γ i).internalize.DoublyConnected := by
  have hperm : ((Γ.comps[i]).map Diag_int :: (Γ.comps.eraseIdx i).map (Comp.map Diag_int)).Perm
      Γ.internalize.comps := by
    rw [Diag_internalize_comps]
    exact (List.getElem_cons_eraseIdx_perm hi).map _
  have hcomm : Sum.map id (Diag_hmap m) ∘ Diag_int = Diag_int ∘ Diag.atomMap m := by
    funext u
    exact Diag_hmap_int m u
  have hH' : (Diag.graph Γ i).internalize.comps =
      ((Γ.comps.eraseIdx i).map (Comp.map Diag_int)).map (Comp.map (Sum.map id (Diag_hmap m))) := by
    rw [Diag_internalize_comps]
    simp only [Diag.graph, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, Diag_map_map, hcomm]
  have hdots : ∀ c ∈ Γ.internalize.comps, c.kind = .dot →
      Sum.map id (Diag_hmap m) c.x = Sum.map id (Diag_hmap m) c.y := by
    intro c hc hck
    rw [Diag_internalize_comps] at hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    change Sum.map id (Diag_hmap m) (Diag_int e.x) = Sum.map id (Diag_hmap m) (Diag_int e.y)
    rw [Diag_hmap_int, Diag_hmap_int]
    rcases hD.2 e he hck with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] <;> rfl
  have hdk : ((Γ.comps[i]).map Diag_int).kind = .dot := hk
  refine ⟨Diag_normal _ (fun c hc => ?_)
    (Diag_waved (Diag_hmap_surjective m) hperm hdk hH' hdots hDC),
    Diag_dc (Diag_hmap_surjective m) hperm hdk hH' hdots hDC⟩
  rw [Diag_internalize_comps] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc'
  exact hrest e he

/-! ## A graph without internal atoms -/

/-- The component `c` with its ends replaced by `x` and `y`. -/
private def Diag_redir (c : Comp (Atom 2 0)) : Comp (Atom 2 0) :=
  ⟨c.kind, .inl 0, .inl 1, c.minor, c.label⟩

/-- For a graph `Γ` without internal atoms: two copies of every component other than the `i`-th,
each with its ends replaced by `x` and `y`, and the coefficient squared. -/
private def Diag_double (Γ : Graph 2 0) (i : ℕ) : Graph 2 0 :=
  ⟨(Γ.comps.eraseIdx i).map Diag_redir ++ (Γ.comps.eraseIdx i).map Diag_redir,
    Γ.coeff * Γ.coeff⟩

private theorem Diag_absVal_zero {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph 2 0)
    (D : Data ι) (e : Fin 2 → ι) (s : Fin 0 → ι) :
    Γ.absVal D e =
      ‖Γ.coeff.eval D.m‖ * (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod := by
  unfold Graph.absVal
  rw [Fintype.sum_unique, Subsingleton.elim (default : Fin 0 → ι) s]

private theorem Diag_val_redir {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) (x : ι)
    (s : Fin 0 → ι) (c : Comp (Atom 2 0)) :
    Comp.val D (Sum.elim ![x, x] s) (Diag_redir c) = Comp.val D (Sum.elim ![x, x] s) c := by
  have hσ : ∀ u : Atom 2 0, Sum.elim ![x, x] s u = x := by
    rintro (a | a)
    · fin_cases a <;> rfl
    · exact a.elim0
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only [Comp.val, Diag_redir, hσ]

/-- At `x = y` the doubled graph has the square of the absolute value of `Γ`. -/
private theorem Diag_absVal_double (Γ : Graph 2 0) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inl 0 ∧ Γ.comps[i].y = .inl 1 ∨
      Γ.comps[i].x = .inl 1 ∧ Γ.comps[i].y = .inl 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) (x : ι) :
    (Diag_double Γ i).absVal D ![x, x] = Γ.absVal D ![x, x] ^ 2 := by
  rw [Diag_absVal_zero _ D _ Fin.elim0, Diag_absVal_zero Γ D _ Fin.elim0,
    ← ((List.getElem_cons_eraseIdx_perm hi).map _).prod_eq, List.map_cons, List.prod_cons,
    Diag_val_dot D _ x x _ hk hxy]
  simp only [Diag_double, List.map_append, List.prod_append, List.map_map, Function.comp_def,
    Diag_val_redir, Coeff.eval, map_mul, norm_mul]
  simp
  ring

/-- The doubled graph has twice the scaling order of `Γ` without its dotted edge. -/
private theorem Diag_ord_double (Γ : Graph 2 0) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot) : (Diag_double Γ i).ord = 2 * Γ.ord - 4 := by
  have hperm := (List.getElem_cons_eraseIdx_perm hi).map fun c => c.kind.ord
  unfold Graph.ord
  rw [← hperm.sum_eq, List.map_cons, List.sum_cons, hk]
  simp only [Diag_double, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    Diag_redir, Kind.ord]
  ring

private theorem Diag_double_isDetKind (Γ : Graph 2 0) (i N : ℕ)
    (h : Γ.comps.all (Comp.isDetKind N) = true) :
    (Diag_double Γ i).comps.all (Comp.isDetKind N) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  simp only [Diag_double, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;> exact h e (List.mem_of_mem_eraseIdx he)

private theorem Diag_two {V : Type*} {G : SimpleGraph V} (f : Fin (2 + 0) → V)
    (h : G.Reachable (f (finSumFinEquiv (Sum.inl 0))) (f (finSumFinEquiv (Sum.inl 1))))
    (a b : Fin (2 + 0)) : G.Reachable (f a) (f b) := by
  have h' : ∀ a, G.Reachable (f (finSumFinEquiv (Sum.inl 0))) (f a) := by
    intro a
    obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective a
    rcases u with u | u
    · fin_cases u
      · rfl
      · exact h
    · exact u.elim0
  exact (h' a).symm.trans (h' b)

/-- **Internal form of the doubled graph.** If the components of `Γ` other than the `i`-th are
waved or `Θ` edges and there is at least one, the internal form of the doubled graph is normal
regular and doubly connected: its two atoms lie in one molecule when a waved edge is present,
and are joined by the two copies of every `Θ` edge otherwise. -/
private theorem Diag_double_internal (Γ : Graph 2 0) (i : ℕ)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i, (∃ w, c.kind = .waved w) ∨ (∃ o, c.kind = .theta o))
    (hne : Γ.comps.eraseIdx i ≠ []) :
    (Diag_double Γ i).internalize.Normal (2 + 0 + (Diag_double Γ i).internalize.comps.length) ∧
      (Diag_double Γ i).internalize.DoublyConnected := by
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hne
  set A := ((Γ.comps.eraseIdx i).map Diag_redir).map (Comp.map (Diag_int (k := 2) (n := 0)))
    with hA
  have hcomps : (Diag_double Γ i).internalize.comps = A ++ A := by
    rw [Diag_internalize_comps]
    simp only [Diag_double, List.map_append, hA]
  have hc₀ : (Diag_redir e₀).map Diag_int ∈ A := List.mem_map_of_mem (List.mem_map_of_mem he₀)
  have hkA : ∀ c ∈ A, (∃ w, c.kind = .waved w) ∨ (∃ o, c.kind = .theta o) := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc'
    exact hrest e he
  have hmem : (Diag_redir e₀).map Diag_int ∈ (Diag_double Γ i).internalize.comps := by
    rw [hcomps]
    exact List.mem_append_left _ hc₀
  refine ⟨Diag_normal _ (fun c hc => ?_) (fun a b => ?_), ?_⟩
  · rw [hcomps, List.mem_append, or_self] at hc
    rcases hkA c hc with ⟨w, hw⟩ | ⟨o, ho⟩
    · simp [hw, Kind.isSolid]
    · simp [ho, Kind.isSolid]
  · refine Diag_two (fun a => (Sum.inr a : Atom 0 (2 + 0))) (Diag_reach_fromRel
      ⟨(Diag_redir e₀).map Diag_int, hmem, ?_, rfl, rfl⟩) a b
    rcases hkA _ hc₀ with ⟨w, hw⟩ | ⟨o, ho⟩
    · rw [hw]
      exact Or.inl ⟨rfl, by simp⟩
    · rw [ho]
      exact Or.inr rfl
  · set F := A.filter fun c => c.kind.isDiffusive
    have hrel : nrel (Diag_double Γ i).internalize F (finSumFinEquiv (Sum.inl 0))
        (finSumFinEquiv (Sum.inl 1)) := by
      rcases hkA _ hc₀ with ⟨w, hw⟩ | ⟨o, ho⟩
      · left
        refine Or.inr ⟨rfl, rfl, Diag_reach_fromRel ⟨(Diag_redir e₀).map Diag_int, hmem, ?_,
          rfl, rfl⟩⟩
        rw [hw]
        rfl
      · right
        refine ⟨(Diag_redir e₀).map Diag_int, List.mem_filter.2 ⟨hc₀, ?_⟩, rfl, rfl⟩
        rw [ho]
        rfl
    have hpc : (SimpleGraph.fromRel (nrel (Diag_double Γ i).internalize F)).Preconnected :=
      fun a b => Diag_two id (Diag_reach_fromRel hrel) a b
    refine Graph.dc_of_dcl ⟨F, F, ?_, fun c hc => by simpa using (List.mem_filter.1 hc).2,
      fun c hc => Or.inl (by simpa using (List.mem_filter.1 hc).2), hpc, hpc⟩
    rw [hcomps]
    exact (List.filter_sublist.append List.filter_sublist).subperm

/-! ## The bound -/

private theorem Diag_kind {V : Type*} {N : ℕ} (c : Comp V) (h : c.isDetKind N = true) :
    c.kind.isSolid = false ∧ (c.kind ≠ .dot → c.kind ≠ .xdot →
      (∃ w, c.kind = .waved w) ∨ (∃ o, c.kind = .theta o)) := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ <;> simp_all [Comp.isDetKind, Kind.isSolid]

private theorem Diag_absVal_nonneg {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (D : Data ι) (e : Fin k → ι) : 0 ≤ Γ.absVal D e := by
  unfold Graph.absVal
  refine Finset.sum_nonneg fun s _ => mul_nonneg (norm_nonneg _) (List.prod_nonneg ?_)
  intro a ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha
  exact norm_nonneg _

/-- A normal regular graph without solid edges and with a `×`-dotted edge has absolute value `0`:
the `×`-dotted edge is a loop. -/
private theorem Diag_absVal_xdot {n C : ℕ} (Γ : Graph 2 n) (hN : Γ.Normal C)
    (hs : ∀ c ∈ Γ.comps, c.kind.isSolid = false) {c : Comp (Atom 2 n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .xdot) {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin 2 → ι) :
    Γ.absVal D e = 0 := by
  have hxy : c.x = c.y := by
    by_contra hne
    obtain ⟨c', hc', hs', -⟩ := (hN.2.2 c.x c.y hne).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    rw [hs c' hc'] at hs'
    exact absurd hs' (by decide)
  unfold Graph.absVal
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [List.prod_eq_zero, mul_zero]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk hxy
  simp [Comp.val]

/-- [I, Cor 6.12] in the form `detBound` for a graph `G` of scaling order `l`, with the second
external atom summed: `Σ_b |G|^{abs}_{xb} ≤ W^{τ/2} W^{-(l-4)d/2} Σ_b B_{xb}² ≤ W^τ W^{-(l-2)d/2}`,
by `Σ_b B_{xb}² ≲ W^{-d}`. -/
private theorem Diag_bound_sum (d : ℕ) (hd : 6 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ)
    (Sig : ℕ → Expansion 2) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (l - 1)) {m C : ℕ}
    (G : Graph 2 m) (hN : G.internalize.Normal C) (hDC : G.internalize.DoublyConnected)
    (hK : G.comps.all (Comp.isDetKind (l - 1)) = true) (hO : G.ord = l) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ∑ b, G.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, b] ≤
          (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
  obtain ⟨W₁, hW₁⟩ := detBound d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (l - 1) Sig hSig m C G hN hDC hK
    (τ / 2) (by positivity)
  obtain ⟨CB, hCB⟩ := bSum.2 d (by omega)
  set C' := max CB 0 with hC'def
  refine ⟨max W₁ (max 1 (C' ^ (2 / τ))), fun W L _ hadm hW z hz x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hOr : ((G.ord : ℤ) : ℝ) = (l : ℝ) := by rw [hO]; push_cast; ring
  have hxx : brk d L W x x = W := by
    unfold brk
    rw [sub_self, (zdistInf_eq_zero_iff d L).2 rfl, Nat.cast_zero, zero_add]
  have hsum : ∑ b, bB d L W x b ^ 2 ≤
      C' * ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4))) := by
    have h := hCB L W hWn x x
    rw [hxx] at h
    calc ∑ b, bB d L W x b ^ 2 = ∑ b, bB d L W x b * bB d L W b x :=
          Finset.sum_congr rfl fun b _ => by rw [sq, bB_comm' b x]
      _ ≤ CB * (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4)) := h
      _ ≤ C' * ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hC' : C' ≤ (W : ℝ) ^ (τ / 2) := by
    have h0 : 0 ≤ C' := le_max_right _ _
    calc C' = (C' ^ (2 / τ)) ^ (τ / 2) := by
          rw [← Real.rpow_mul h0, show 2 / τ * (τ / 2) = 1 by field_simp, Real.rpow_one]
      _ ≤ (W : ℝ) ^ (τ / 2) :=
          Real.rpow_le_rpow (by positivity)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)) (by positivity)
  have hb : ∀ b, G.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, b] ≤
      (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W x b ^ 2 := by
    intro b
    have := hW₁ W L hadm (le_trans (le_max_left _ _) hW) z hz x b
    rwa [hOr] at this
  calc ∑ b, G.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, b]
      ≤ ∑ b, (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W x b ^ 2 :=
        Finset.sum_le_sum fun b _ => hb b
    _ = (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * ∑ b, bB d L W x b ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) *
          (C' * ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) *
          ((W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-((d : ℝ) - 4)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC' (by positivity))
          (by positivity)
    _ = (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
        simp only [← Real.rpow_add hW0]
        congr 1
        ring

/-- [I, Cor 6.12] in the form `detBound` for a graph `G` without internal atoms of scaling order
`2l - 4` at `x = y`: `|G|^{abs}_{xx} ≤ W^{2τ} W^{-(2l-8)d/2} B_{xx}² = (W^τ W^{-(l-2)d/2})²`. -/
private theorem Diag_bound_double (d : ℕ) (hd : 6 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ)
    (Sig : ℕ → Expansion 2) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (l - 1)) {C : ℕ}
    (G : Graph 2 0) (hN : G.internalize.Normal C) (hDC : G.internalize.DoublyConnected)
    (hK : G.comps.all (Comp.isDetKind (l - 1)) = true) (hO : G.ord = 2 * l - 4) (τ : ℝ)
    (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        G.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, x] ≤
          ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) ^ 2 := by
  obtain ⟨W₁, hW₁⟩ := detBound d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (l - 1) Sig hSig 0 C G hN hDC hK
    (2 * τ) (by positivity)
  refine ⟨max W₁ 1, fun W L _ hadm hW z hz x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hOr : ((G.ord : ℤ) : ℝ) = 2 * (l : ℝ) - 4 := by rw [hO]; push_cast; ring
  have h := hW₁ W L hadm (le_trans (le_max_left _ _) hW) z hz x x
  rw [hOr, bB_self hWn] at h
  refine h.trans (le_of_eq ?_)
  rw [sq, sq]
  simp only [← Real.rpow_add hW0]
  congr 1
  ring

/-- The diagonal bound at `x = y` for a graph without internal atoms. -/
private theorem Diag_case_zero (d : ℕ) (hd : 6 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ)
    (Sig : ℕ → Expansion 2) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (l - 1))
    (Γ : Graph 2 0) (hK : Γ.comps.all (Comp.isDetKind (l - 1)) = true) (hO : Γ.ord = l)
    (hD : G13.IsDiag Γ) (hA : Γ.DotsAcyclic) (hX : ∀ c ∈ Γ.comps, c.kind ≠ .xdot) (τ : ℝ)
    (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        Γ.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, x] ≤
          (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
  obtain ⟨i, hi, hk, hrest⟩ := Diag.dot_unique Γ hD hA
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hKc : ∀ c ∈ Γ.comps, c.isDetKind (l - 1) = true := List.all_eq_true.1 hK
  by_cases hR : Γ.comps.eraseIdx i = []
  · have hperm := List.getElem_cons_eraseIdx_perm hi
    rw [hR] at hperm
    have hl : (l : ℝ) = 2 := by
      have h2 : Γ.ord = 2 := by
        unfold Graph.ord
        rw [← (hperm.map fun c => c.kind.ord).sum_eq]
        simp [hk, Kind.ord]
      have : (l : ℤ) = 2 := by rw [← hO, h2]
      exact_mod_cast this
    obtain ⟨Cc, hCc0, hCc⟩ := coeff_bound κ hκ Γ.coeff
    refine ⟨max 1 (Cc ^ (1 / τ)), fun W L _ hadm hW z hz x => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
    have hval : Γ.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, x] =
        ‖Γ.coeff.eval (msc z)‖ := by
      rw [Diag_absVal_zero Γ _ _ Fin.elim0, ← (hperm.map _).prod_eq]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Diag_val_dot _ _ x x _ hk hxy]
      simp
      rfl
    rw [hval, hl, sub_self, zero_mul, zero_div, neg_zero, Real.rpow_zero, mul_one]
    calc ‖Γ.coeff.eval (msc z)‖ ≤ Cc :=
          hCc z (im_pos_of_specDom (by exact_mod_cast hW1) hz) hz.1 hz.2.2
      _ = (Cc ^ (1 / τ)) ^ τ := by
          rw [← Real.rpow_mul hCc0, one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hW) hτ.le
  · have hrestK : ∀ c ∈ Γ.comps.eraseIdx i,
        (∃ w, c.kind = .waved w) ∨ (∃ o, c.kind = .theta o) := fun c hc =>
      (Diag_kind c (hKc c (List.mem_of_mem_eraseIdx hc))).2 (hrest c hc)
        (hX c (List.mem_of_mem_eraseIdx hc))
    obtain ⟨hN₂, hDC₂⟩ := Diag_double_internal Γ i hrestK hR
    obtain ⟨W₀, hW₀⟩ := Diag_bound_double d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l Sig hSig
      (Diag_double Γ i) hN₂ hDC₂ (Diag_double_isDetKind Γ i _ hK)
      (by rw [Diag_ord_double Γ i hi hk, hO]) τ hτ
    refine ⟨max W₀ 1, fun W L _ hadm hW z hz x => ?_⟩
    have h := hW₀ W L hadm (le_trans (le_max_left _ _) hW) z hz x
    rw [Diag_absVal_double Γ i hi hk hxy] at h
    have hW0 : (0 : ℝ) < W := by linarith [le_max_right W₀ 1]
    exact (pow_le_pow_iff_left₀ (Diag_absVal_nonneg _ _ _) (by positivity) two_ne_zero).1 h

/-- The diagonal bound at `x = y` for a graph with at least one internal atom. -/
private theorem Diag_case_succ (d : ℕ) (hd : 6 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ)
    (Sig : ℕ → Expansion 2) (hSig : SelfEnergiesUpTo d (smatVar P) Sig (l - 1)) {m : ℕ}
    (Γ : Graph 2 (m + 1)) (hK : Γ.comps.all (Comp.isDetKind (l - 1)) = true) (hO : Γ.ord = l)
    (hD : G13.IsDiag Γ) (hA : Γ.DotsAcyclic) (hX : ∀ c ∈ Γ.comps, c.kind ≠ .xdot)
    (hDC : Γ.internalize.DoublyConnected) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        Γ.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, x] ≤
          (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
  obtain ⟨i, hi, hk, hrest⟩ := Diag.dot_unique Γ hD hA
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hKc : ∀ c ∈ Γ.comps, c.isDetKind (l - 1) = true := List.all_eq_true.1 hK
  have hrest' : ∀ c ∈ Γ.comps.eraseIdx i,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := fun c hc =>
    ⟨hrest c hc, hX c (List.mem_of_mem_eraseIdx hc),
      (Diag_kind c (hKc c (List.mem_of_mem_eraseIdx hc))).1⟩
  obtain ⟨hN', hDC'⟩ := Diag.internal Γ i hi hk hD hrest' hDC
  obtain ⟨W₀, hW₀⟩ := Diag_bound_sum d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l Sig hSig
    (Diag.graph Γ i) hN' hDC' (Diag.all_isDetKind Γ i _ hK) (by rw [Diag.ord_eq Γ i hi hk, hO])
    τ hτ
  refine ⟨W₀, fun W L _ hadm hW z hz x => ?_⟩
  rw [Diag.absVal_eq Γ i hi hk hxy]
  exact hW₀ W L hadm hW z hz x

/-- **The diagonal bound**: for `d ≥ 6`, lower orders that are self-energies and a diagonal graph
`Γ` with the shape of an `l`-th order self-energy, for every `τ > 0` there is `W₀` with
`|Γ|^{abs}_{xy} ≤ W^τ W^{-(l-2)d/2} 1_{x=y}` along `adm(c₀, c₁)` for `W ≥ W₀` and
`z ∈ 𝐃(κ, ε)`. The atoms `x = y` are identified ([I, Def 3.1]); with that atom fixed at `x` and one
further atom summed, [I, Cor 6.12] and `Σ_β B_{xβ}² ≲ W^{-d}` give the bound; a graph with no
internal atom is a product of loops at `x`. -/
def G13.diagBoundStmt : Prop :=
  ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (l : ℕ) (Sig : ℕ → Expansion 2),
      SelfEnergiesUpTo d (smatVar P) Sig (l - 1) →
    ∀ (n : ℕ) (Γ : Graph 2 n), SelfEnergyShape l [⟨n, Γ⟩] → G13.IsDiag Γ →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ,
        ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
          ∀ x y : Zd d L,
            Γ.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, y] ≤
              if x = y then (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0

/-- **The diagonal bound** ([I, Cor 6.12] for a graph of [I, Def 2.13 (i)] with its dotted edge
between `x` and `y`). A `×`-dotted edge is a loop and gives `0`. Otherwise the dotted edge is the
only one; with an internal atom, `x = y` is identified and the internal atom `0` fixed
(`Diag.absVal_eq`, `Diag.internal`); without one, the graph at `x = y` is bounded through two
copies of its other components joining `x` and `y`. -/
theorem G13.diagBound : G13.diagBoundStmt := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l Sig hSig n Γ hsh hD τ hτ
  obtain ⟨⟨C, hN, hA⟩, hK, hO, hDC⟩ := hsh _ (List.mem_singleton_self _)
  have hK : Γ.comps.all (Comp.isDetKind (l - 1)) = true := hK
  have hO : Γ.ord = l := hO
  have hDC : Γ.internalize.DoublyConnected := hDC
  have hN : Γ.Normal C := hN
  have hA : Γ.DotsAcyclic := hA
  have hsol : ∀ c ∈ Γ.comps, c.kind.isSolid = false := fun c hc =>
    (Diag_kind c (List.all_eq_true.1 hK c hc)).1
  obtain ⟨i, hi, hk, -⟩ := Diag.dot_unique Γ hD hA
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  by_cases hX : ∃ c ∈ Γ.comps, c.kind = .xdot
  · obtain ⟨c, hc, hck⟩ := hX
    refine ⟨0, fun W L _ _ _ z _ x y => ?_⟩
    rw [Diag_absVal_xdot Γ hN hsol hc hck]
    split_ifs
    · positivity
    · exact le_rfl
  replace hX : ∀ c ∈ Γ.comps, c.kind ≠ .xdot := fun c hc hck => hX ⟨c, hc, hck⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        Γ.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![x, x] ≤
          (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
    cases n with
    | zero =>
      exact Diag_case_zero d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l Sig hSig Γ hK hO hD hA hX τ hτ
    | succ m =>
      exact Diag_case_succ d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε l Sig hSig Γ hK hO hD hA hX hDC τ
        hτ
  refine ⟨W₀, fun W L _ hadm hW z hz x y => ?_⟩
  by_cases hxy' : x = y
  · subst hxy'
    simpa using hW₀ W L hadm hW z hz x
  · simp only [hxy', ↓reduceIte]
    rw [Diag.absVal_ne Γ _ (List.getElem_mem hi) hk hxy _ hxy']

section Instances

end Instances

end RBM8D.Graphs
