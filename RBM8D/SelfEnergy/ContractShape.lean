import RBM8D.SelfEnergy.Contract
import RBM8D.Bound.GraphSum
import RBM8D.Graph.QExp.PSteps
import RBM8D.Graph.QExp.SelRun

/-!
# Contraction of the dotted edges of a self-energy graph

A dotted edge between an internal atom `α` and an external atom `a` of a graph of `Σ_l` reads
"`α = a`" ([I, Def 2.12]); summing out `α` identifies it with `a`, as the merge operation
`O_merge` of [I, Def 3.1] does (`Contract.graph`, with the value, the scaling order and the
deterministic kinds kept by `Contract.val_eq`, `Contract.ord_eq`, `Contract.all_isDetKind`).

* `ContractShape.step`: one contraction keeps the shape of an `l`-th order self-energy
  (`SelfEnergyShape`): normal regularity with the same bound, the forest of dotted edges
  (`Graph.DotsAcyclic`), and the doubly connected property with `x`, `y` read as internal atoms.
* `ContractShape.final`: a graph with the shape of an `l`-th order self-energy whose dotted edges
  all join external atoms is normal regular with `x`, `y` read as internal atoms (no dotted edge),
  or diagonal ([I, Def 2.13 (i)]: its dotted edges join `x` and `y`).
* `G13.dotContract : G13.dotContractStmt`: contracting all dotted edges between an internal and
  an external atom, a graph with the shape of an `l`-th order self-energy has a graph with the
  same value on every data record and the same shape that is normal regular with `x`, `y` read as
  internal atoms, the premise of [I, Cor 6.12], or diagonal.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section Instances

end Instances

/-! ## Reachability under a map of the atoms -/

private theorem ContractShape_reach_fromRel {α : Type*} {r : α → α → Prop} {a b : α}
    (h : r a b) : (SimpleGraph.fromRel r).Reachable a b := by
  by_cases hab : a = b
  · subst hab
    rfl
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩).reachable

/-- A path of the graph of a relation `r` maps to a path of `G` under `ψ` if every pair related
by `r` does. -/
private theorem ContractShape_lift {X Y : Type*} {r : X → X → Prop} {G : SimpleGraph Y}
    (ψ : X → Y) (h : ∀ x y, r x y → G.Reachable (ψ x) (ψ y)) {x y : X}
    (hr : (SimpleGraph.fromRel r).Reachable x y) : G.Reachable (ψ x) (ψ y) := by
  refine reach_lift ψ (fun a b hab => ?_) hr
  rw [SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with h' | h'
  · exact h a b h'
  · exact (h b a h').symm

/-- A surjective map of the vertices that sends edges to paths does not increase the number of
connected components. -/
private theorem ContractShape_card_le {X Y : Type*} [Finite X] {G₁ : SimpleGraph X}
    {G₂ : SimpleGraph Y} (ψ : X → Y) (hs : Function.Surjective ψ)
    (h : ∀ x y, G₁.Adj x y → G₂.Reachable (ψ x) (ψ y)) :
    Nat.card G₂.ConnectedComponent ≤ Nat.card G₁.ConnectedComponent := by
  let F : G₁.ConnectedComponent → G₂.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift (fun v => G₂.connectedComponentMk (ψ v))
      (fun _ _ p _ => SimpleGraph.ConnectedComponent.sound (reach_lift ψ h p.reachable))
  refine Nat.card_le_card_of_surjective F fun C => ?_
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h y =>
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨G₁.connectedComponentMk x, rfl⟩

/-! ## One contraction -/

section Step

variable {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length) (j : Fin (n + 1)) (a₀ : Fin k)

private theorem ContractShape_surj :
    Function.Surjective (Contract.atomMap j a₀ : Atom k (n + 1) → Atom k n) := by
  rintro (b | b)
  · exact ⟨.inl b, rfl⟩
  · exact ⟨.inr (j.succAbove b), Contract.atomMap_succAbove j a₀ b⟩

/-- A component of `Γ` is the contracted one, or its image is a component of the contraction. -/
private theorem ContractShape_mem {c : Comp (Atom k (n + 1))} (hc : c ∈ Γ.comps) :
    c = Γ.comps[i] ∨ c.map (Contract.atomMap j a₀) ∈ (Contract.graph Γ i j a₀).comps := by
  rcases List.mem_cons.1 ((Contract.comps_perm Γ i).mem_iff.2 hc) with h | h
  · exact Or.inl h
  · exact Or.inr ((Contract.mem_graph_comps Γ i j a₀ _).2 ⟨c, h, rfl⟩)

/-- The ends of a dotted edge between `inr j` and `inl a₀` have one image. -/
private theorem ContractShape_collapse
    (hxy : Γ.comps[i].x = .inr j ∧ Γ.comps[i].y = .inl a₀ ∨
      Γ.comps[i].x = .inl a₀ ∧ Γ.comps[i].y = .inr j) :
    Contract.atomMap j a₀ Γ.comps[i].x = Contract.atomMap j a₀ Γ.comps[i].y := by
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] <;> simp

/-- A path of components of `Γ` with a property `P` maps to a path of components of the
contraction with a property `Q` kept by the map. -/
private theorem ContractShape_compLift
    (hcol : Contract.atomMap j a₀ Γ.comps[i].x = Contract.atomMap j a₀ Γ.comps[i].y)
    (P : Comp (Atom k (n + 1)) → Prop) (Q : Comp (Atom k n) → Prop)
    (hPQ : ∀ c, P c → Q (c.map (Contract.atomMap j a₀))) {u v : Atom k (n + 1)}
    (h : (SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, P c ∧ c.x = u ∧ c.y = v).Reachable u v) :
    (SimpleGraph.fromRel fun u v => ∃ c ∈ (Contract.graph Γ i j a₀).comps, Q c ∧ c.x = u ∧
      c.y = v).Reachable (Contract.atomMap j a₀ u) (Contract.atomMap j a₀ v) := by
  refine ContractShape_lift _ (fun x y ⟨c, hc, hP, hx, hy⟩ => ?_) h
  subst hx hy
  rcases ContractShape_mem Γ i j a₀ hc with rfl | hm
  · rw [hcol]
  · exact ContractShape_reach_fromRel ⟨_, hm, hPQ c hP, rfl, rfl⟩

/-- **Normal regularity.** If the ends of the `i`-th component of `Γ` have one image and `Γ` has
no solid edge, the contraction is normal regular with the bound of `Γ`. -/
private theorem ContractShape_normal {C : ℕ}
    (hcol : Contract.atomMap j a₀ Γ.comps[i].x = Contract.atomMap j a₀ Γ.comps[i].y)
    (hN : Γ.Normal C) (hS : ∀ c ∈ Γ.comps, c.kind.isSolid = false) :
    (Contract.graph Γ i j a₀).Normal C := by
  set f := Contract.atomMap j a₀ with hf
  have hlen : (Γ.comps.eraseIdx i).length + 1 = Γ.comps.length := by
    have := (Contract.comps_perm Γ i).length_eq
    rw [List.length_cons] at this
    exact this
  have hS' : ∀ c ∈ (Contract.graph Γ i j a₀).comps, c.kind.isSolid = false := by
    intro c hc
    obtain ⟨c, hc', rfl⟩ := (Contract.mem_graph_comps Γ i j a₀ _).1 hc
    exact hS c (List.mem_of_mem_eraseIdx hc')
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun c hc hs => absurd hs (by rw [hS' c hc]; decide),
    fun u v huv => ⟨?_, fun ⟨c, hc, hs, _⟩ => absurd hs (by rw [hS' c hc]; decide)⟩⟩
  · have h1 := hN.1.size
    simp only [Contract.graph_comps, List.length_map]
    omega
  · intro u' v'
    obtain ⟨u, rfl⟩ := ContractShape_surj j a₀ u'
    obtain ⟨v, rfl⟩ := ContractShape_surj j a₀ v'
    refine ContractShape_lift f (fun x y ⟨c, hc, hx, hy⟩ => ?_) (hN.1.connected u v)
    subst hx hy
    rcases ContractShape_mem Γ i j a₀ hc with rfl | hm
    · rw [hcol]
    · exact ContractShape_reach_fromRel ⟨_, hm, rfl, rfl⟩
  · intro a b
    have := ContractShape_compLift Γ i j a₀ hcol
      (fun c => (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true))
      (fun c => (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true))
      (fun c h => h) (hN.1.internal (j.succAbove a) (j.succAbove b))
    rwa [Contract.atomMap_succAbove, Contract.atomMap_succAbove] at this
  · intro c hc hd
    obtain ⟨c, hc', rfl⟩ := (Contract.mem_graph_comps Γ i j a₀ _).1 hc
    have hl : ∀ w : Atom k (n + 1), w.isLeft = true → (f w).isLeft = true := by
      rintro (w | w) hw
      · rfl
      · simp at hw
    rcases hN.1.noIntDot c (List.mem_of_mem_eraseIdx hc') hd with h | h
    · exact Or.inl (hl _ h)
    · exact Or.inr (hl _ h)
  · rintro ⟨c', hc', hx, hends⟩
    obtain ⟨c, hc, rfl⟩ := (Contract.mem_graph_comps Γ i j a₀ _).1 hc'
    have hcΓ := List.mem_of_mem_eraseIdx hc
    have hloop : c.x = c.y := by
      by_contra hne
      obtain ⟨e, he, hs, -⟩ := (hN.2.2 c.x c.y hne).1 ⟨c, hcΓ, hx, Or.inl ⟨rfl, rfl⟩⟩
      exact absurd hs (by rw [hS e he]; decide)
    exfalso
    apply huv
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact congrArg f hloop
    · rw [← h1, ← h2]
      exact (congrArg f hloop).symm

/-- **The forest of dotted edges.** The contraction of a dotted edge keeps `Graph.DotsAcyclic`:
it removes one dotted edge and one atom, and the blocks of the contraction are images of the
blocks of `Γ`. -/
private theorem ContractShape_dotsAcyclic (hk : Γ.comps[i].kind = .dot)
    (hcol : Contract.atomMap j a₀ Γ.comps[i].x = Contract.atomMap j a₀ Γ.comps[i].y)
    (hA : Γ.DotsAcyclic) : (Contract.graph Γ i j a₀).DotsAcyclic := by
  rw [Graph.dotsAcyclic_iff_dotExcess_eq_zero] at hA ⊢
  have hn : Γ.nDots = (Contract.graph Γ i j a₀).nDots + 1 := by
    unfold Graph.nDots
    rw [← ((Contract.comps_perm Γ i).filter _).length_eq,
      List.filter_cons_of_pos (by simpa using hk), List.length_cons, Contract.graph_comps,
      List.filter_map, List.length_map]
    rfl
  have hc : Nat.card (Contract.graph Γ i j a₀).dotGraph.ConnectedComponent ≤
      Nat.card Γ.dotGraph.ConnectedComponent :=
    ContractShape_card_le _ (ContractShape_surj j a₀) fun x y hadj =>
      ContractShape_compLift Γ i j a₀ hcol (fun c => c.kind = .dot) (fun c => c.kind = .dot)
        (fun _ h => h) hadj.reachable
  have h1 := SelRun_dotExcess_nonneg (Contract.graph Γ i j a₀)
  unfold Graph.dotExcess at hA h1 ⊢
  push_cast at hA h1 ⊢
  omega

end Step

/-! ## The doubly connected property along a map of the atoms -/

section Transport

variable {N N' : ℕ} {H : Graph 0 N} {H' : Graph 0 N'} {h : Fin N → Fin N'}
  {d : Comp (Atom 0 N)} {rest : List (Comp (Atom 0 N))}

private theorem ContractShape_sameMol_lift (hperm : (d :: rest).Perm H.comps)
    (hH' : H'.comps = rest.map (Comp.map (Sum.map id h)))
    (hcol : Sum.map id h d.x = Sum.map id h d.y)
    {a b : Fin N} (hm : H.SameMol (.inr a) (.inr b)) :
    H'.SameMol (.inr (h a)) (.inr (h b)) := by
  rcases hm with he | ⟨-, -, hr⟩
  · left
    rw [Sum.inr_injective he]
  · right
    refine ⟨rfl, rfl, ?_⟩
    have := ContractShape_lift (Sum.map id h) (r := fun u v => ∃ c ∈ H.comps,
      c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) (G := H'.molGraph)
      (fun x y ⟨c, hc, hj, hx, hy⟩ => by
        subst hx hy
        rcases List.mem_cons.1 (hperm.mem_iff.2 hc) with rfl | hc'
        · rw [hcol]
        · exact ContractShape_reach_fromRel
            ⟨c.map (Sum.map id h), hH' ▸ List.mem_map_of_mem hc', hj, rfl, rfl⟩) hr
    exact this

/-- **Doubly connected.** If `H'` is `H` with a dotted edge `d` removed and the atoms mapped onto
by `h`, and the ends of `d` have one image, then `H'` is doubly connected when `H` is: the two
nets are mapped component by component. -/
private theorem ContractShape_dcMap (hs : Function.Surjective h)
    (hperm : (d :: rest).Perm H.comps) (hd : d.kind = .dot)
    (hH' : H'.comps = rest.map (Comp.map (Sum.map id h)))
    (hcol : Sum.map id h d.x = Sum.map id h d.y)
    (hDC : H.DoublyConnected) : H'.DoublyConnected := by
  classical
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hDC
  have hnd : d ∉ Lb ++ Lu := fun hm => by
    rcases List.mem_append.1 hm with hm | hm
    · have := hb d hm
      rw [hd] at this
      exact absurd this (by decide)
    · rcases hu d hm with h1 | h1 <;> rw [hd] at h1 <;> exact absurd h1 (by decide)
  have hsub' : (Lb ++ Lu).Subperm rest := by
    have h2 := (hperm.subperm_left.2 hsub).erase d
    rwa [List.erase_cons_head, List.erase_of_not_mem hnd] at h2
  have hlift : ∀ L : List (Comp (Atom 0 N)), (SimpleGraph.fromRel (nrel H L)).Preconnected →
      (SimpleGraph.fromRel (nrel H' (L.map (Comp.map (Sum.map id h))))).Preconnected := by
    intro L hL a' b'
    obtain ⟨a, rfl⟩ := hs a'
    obtain ⟨b, rfl⟩ := hs b'
    refine ContractShape_lift h (fun a b hr => ?_) (hL a b)
    rcases hr with hm | ⟨c, hc, hx, hy⟩
    · exact ContractShape_reach_fromRel
        (Or.inl (ContractShape_sameMol_lift hperm hH' hcol hm))
    · refine ContractShape_reach_fromRel
        (Or.inr ⟨c.map (Sum.map id h), List.mem_map_of_mem hc, ?_, ?_⟩)
      · simp [Comp.map, hx]
      · simp [Comp.map, hy]
  refine Graph.dc_of_dcl ⟨Lb.map (Comp.map (Sum.map id h)), Lu.map (Comp.map (Sum.map id h)),
    ?_, ?_, ?_, hlift Lb hsb, hlift Lu hsu⟩
  · rw [hH', ← List.map_append]
    obtain ⟨l', hp, hs'⟩ := hsub'
    exact ⟨l'.map _, hp.map _, hs'.map _⟩
  · intro c hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    exact hb c hc'
  · intro c hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    exact hu c hc'

end Transport

/-- The atom map of `Graph.internalize`, through `finSumFinEquiv`. -/
private def ContractShape_int {k n : ℕ} (u : Atom k n) : Atom 0 (k + n) := .inr (finSumFinEquiv u)

private theorem ContractShape_internalize_comps {k n : ℕ} (Γ : Graph k n) :
    Γ.internalize.comps = Γ.comps.map (Comp.map ContractShape_int) := by
  have : (Sum.elim (fun a => Sum.inr (Fin.castAdd n a)) (fun b => Sum.inr (Fin.natAdd k b)) :
      Atom k n → Atom 0 (k + n)) = ContractShape_int := by
    funext u
    rcases u with a | b <;> simp [ContractShape_int]
  simp only [Graph.internalize, Graph.mapAtoms, this]

private theorem ContractShape_map_map {U V W : Type*} (f : U → V) (g : V → W) (c : Comp U) :
    (c.map f).map g = c.map (g ∘ f) := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  rcases lab with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map]

/-- `Contract.atomMap` read on the internal forms. -/
private def ContractShape_hmap {k n : ℕ} (j : Fin (n + 1)) (a₀ : Fin k)
    (p : Fin (k + (n + 1))) : Fin (k + n) :=
  finSumFinEquiv (Contract.atomMap j a₀ (finSumFinEquiv.symm p))

private theorem ContractShape_hmap_int {k n : ℕ} (j : Fin (n + 1)) (a₀ : Fin k)
    (u : Atom k (n + 1)) :
    Sum.map id (ContractShape_hmap j a₀) (ContractShape_int u) =
      ContractShape_int (Contract.atomMap j a₀ u) := by
  simp [ContractShape_int, ContractShape_hmap]

/-- **Internal form.** The contraction of a dotted edge between `inr j` and `inl a₀` keeps the
doubly connected property of the internal form (`x`, `y` read as internal atoms). -/
private theorem ContractShape_dc {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) (hk : Γ.comps[i].kind = .dot)
    (hcol : Contract.atomMap j a₀ Γ.comps[i].x = Contract.atomMap j a₀ Γ.comps[i].y)
    (hDC : Γ.internalize.DoublyConnected) :
    (Contract.graph Γ i j a₀).internalize.DoublyConnected := by
  have hperm : ((Γ.comps[i]).map ContractShape_int ::
      (Γ.comps.eraseIdx i).map (Comp.map ContractShape_int)).Perm Γ.internalize.comps := by
    rw [ContractShape_internalize_comps]
    exact (Contract.comps_perm Γ i).map _
  have hcomm : Sum.map id (ContractShape_hmap j a₀) ∘ ContractShape_int =
      ContractShape_int ∘ Contract.atomMap j a₀ := by
    funext u
    exact ContractShape_hmap_int j a₀ u
  have hH' : (Contract.graph Γ i j a₀).internalize.comps =
      ((Γ.comps.eraseIdx i).map (Comp.map ContractShape_int)).map
        (Comp.map (Sum.map id (ContractShape_hmap j a₀))) := by
    rw [ContractShape_internalize_comps]
    simp only [Contract.graph_comps, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, ContractShape_map_map, hcomm]
  have hs : Function.Surjective (ContractShape_hmap (k := k) j a₀) := by
    intro q
    obtain ⟨u, hu⟩ := ContractShape_surj j a₀ (finSumFinEquiv.symm q)
    exact ⟨finSumFinEquiv u, by simp [ContractShape_hmap, hu]⟩
  have hcol' : Sum.map id (ContractShape_hmap j a₀) ((Γ.comps[i]).map ContractShape_int).x =
      Sum.map id (ContractShape_hmap j a₀) ((Γ.comps[i]).map ContractShape_int).y := by
    change Sum.map id (ContractShape_hmap j a₀) (ContractShape_int Γ.comps[i].x) =
      Sum.map id (ContractShape_hmap j a₀) (ContractShape_int Γ.comps[i].y)
    rw [ContractShape_hmap_int, ContractShape_hmap_int, hcol]
  exact ContractShape_dcMap hs hperm hk hH' hcol' hDC

/-! ## The shape of a self-energy -/

/-- The shape of an `l`-th order self-energy for a single graph, conjunct by conjunct. -/
private theorem ContractShape_shape {l n : ℕ} (Γ : Graph 2 n) :
    SelfEnergyShape l [⟨n, Γ⟩] ↔ (∃ C, Γ.Normal C ∧ Γ.DotsAcyclic) ∧
      Γ.comps.all (Comp.isDetKind (l - 1)) = true ∧ Γ.ord = l ∧
      Γ.internalize.DoublyConnected := by
  unfold SelfEnergyShape
  rw [List.forall_mem_singleton]
  exact Iff.rfl

private theorem ContractShape_noSolid {V : Type*} {N : ℕ} (c : Comp V)
    (h : c.isDetKind N = true) : c.kind.isSolid = false := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ <;> first | rfl | simp [Comp.isDetKind] at h

/-- **One contraction.** If `Γ` has the shape of an `l`-th order self-energy and its `i`-th
component is a dotted edge between the internal atom `j` and the external atom `a₀` (either
orientation), the contraction `Contract.graph Γ i j a₀` ([I, Def 3.1] with `j` identified with
`a₀`) has the shape of an `l`-th order self-energy: normal regular with the bound of `Γ`, the
dotted edges a forest, deterministic kinds, scaling order `l`, and doubly connected with `x`, `y`
read as internal atoms. -/
theorem ContractShape.step {l n : ℕ} (Γ : Graph 2 (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin 2) (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inr j ∧ Γ.comps[i].y = .inl a₀ ∨
      Γ.comps[i].x = .inl a₀ ∧ Γ.comps[i].y = .inr j)
    (hΓ : SelfEnergyShape l [⟨n + 1, Γ⟩]) :
    SelfEnergyShape l [⟨n, Contract.graph Γ i j a₀⟩] := by
  obtain ⟨⟨C, hN, hA⟩, hdet, hord, hDC⟩ := (ContractShape_shape Γ).1 hΓ
  have hcol := ContractShape_collapse Γ i j a₀ hxy
  have hS : ∀ c ∈ Γ.comps, c.kind.isSolid = false := fun c hc =>
    ContractShape_noSolid c (List.all_eq_true.1 hdet c hc)
  exact (ContractShape_shape _).2 ⟨⟨C, ContractShape_normal Γ i j a₀ hcol hN hS,
    ContractShape_dotsAcyclic Γ i j a₀ hk hcol hA⟩, Contract.all_isDetKind Γ i j a₀ _ hdet,
    (Contract.ord_eq Γ i j a₀ hk).trans hord, ContractShape_dc Γ i j a₀ hk hcol hDC⟩

/-! ## No dotted edge at an internal atom -/

/-- A graph whose dotted edges form a forest has no dotted loop. -/
private theorem ContractShape_noLoop {k n : ℕ} (Γ : Graph k n) (hA : Γ.DotsAcyclic)
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hk : c.kind = .dot) : c.x ≠ c.y := by
  intro hxy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hperm := List.getElem_cons_eraseIdx_perm hi
  set Γ₀ : Graph k n := ⟨Γ.comps.eraseIdx i, Γ.coeff⟩ with hΓ₀
  have hg : Γ₀.dotGraph = Γ.dotGraph := by
    ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
    refine ⟨fun ⟨hne, h⟩ => ⟨hne, ?_⟩, fun ⟨hne, h⟩ => ⟨hne, ?_⟩⟩
    · rcases h with ⟨e, he, h⟩ | ⟨e, he, h⟩
      · exact Or.inl ⟨e, List.mem_of_mem_eraseIdx he, h⟩
      · exact Or.inr ⟨e, List.mem_of_mem_eraseIdx he, h⟩
    · have key : ∀ {a b : Atom k n}, a ≠ b → ∀ e ∈ Γ.comps, e.kind = .dot → e.x = a → e.y = b →
          e ∈ Γ₀.comps := by
        intro a b hab e he hek hea heb
        rcases List.mem_cons.1 (hperm.mem_iff.2 he) with rfl | h'
        · exact absurd (hea.symm.trans (hxy.trans heb)) hab
        · exact h'
      rcases h with ⟨e, he, hek, hx, hy⟩ | ⟨e, he, hek, hx, hy⟩
      · exact Or.inl ⟨e, key hne e he hek hx hy, hek, hx, hy⟩
      · exact Or.inr ⟨e, key (Ne.symm hne) e he hek hx hy, hek, hx, hy⟩
  have hn : Γ.nDots = Γ₀.nDots + 1 := by
    unfold Graph.nDots
    rw [← (hperm.filter _).length_eq, List.filter_cons_of_pos (by simpa using hk),
      List.length_cons]
  have h0 := (Graph.dotsAcyclic_iff_dotExcess_eq_zero Γ).1 hA
  have h1 := SelRun_dotExcess_nonneg Γ₀
  unfold Graph.dotExcess at h0 h1
  rw [← hg, hn] at h0
  push_cast at h0 h1
  omega

/-- A graph without external atoms whose components are neither dotted nor solid, whose
`×`-dotted edges are loops, and in which any two atoms are joined by waved and diffusive edges,
is normal regular. -/
private theorem ContractShape_normal_int {N : ℕ} (H : Graph 0 N)
    (hk : ∀ c ∈ H.comps, c.kind ≠ .dot ∧ c.kind.isSolid = false ∧ (c.kind = .xdot → c.x = c.y))
    (hw : ∀ a b : Fin N, H.wavedThetaGraph.Reachable (.inr a) (.inr b)) :
    H.Normal (N + H.comps.length) := by
  have hle : H.wavedThetaGraph ≤ H.edgeGraph := by
    intro u v huv
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
    obtain ⟨hne, ⟨c, hc, -, hx, hy⟩ | ⟨c, hc, -, hx, hy⟩⟩ := huv
    · exact ⟨hne, Or.inl ⟨c, hc, hx, hy⟩⟩
    · exact ⟨hne, Or.inr ⟨c, hc, hx, hy⟩⟩
  refine ⟨⟨by simp, ?_, hw, fun c hc hd => absurd hd (hk c hc).1⟩, fun c hc hs => ?_,
    fun u v huv => ?_⟩
  · rintro (u | a) (v | b)
    · exact u.elim0
    · exact u.elim0
    · exact v.elim0
    · exact (hw a b).mono hle
  · rw [(hk c hc).2.1] at hs
    exact absurd hs (by decide)
  · constructor
    · rintro ⟨c, hc, hx, hends⟩
      have hl := (hk c hc).2.2 hx
      exfalso
      apply huv
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hl]
      · rw [← h1, ← h2, hl]
    · rintro ⟨c, hc, hs, -⟩
      rw [(hk c hc).2.1] at hs
      exact absurd hs (by decide)

/-- In a doubly connected graph without external atoms and without dotted edges, any two atoms are
joined by a path of waved and diffusive edges: the black net and the molecules. -/
private theorem ContractShape_waved {N : ℕ} (H : Graph 0 N) (hd : ∀ c ∈ H.comps, c.kind ≠ .dot)
    (hDC : H.DoublyConnected) (a b : Fin N) :
    H.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
  obtain ⟨Lb, Lu, hsub, hb, -, hsb, -⟩ := Graph.dcl_of_dc hDC
  refine ContractShape_lift (fun a => (Sum.inr a : Atom 0 N)) (fun a b hr => ?_) (hsb a b)
  rcases hr with hm | ⟨c, hc, hx, hy⟩
  · rcases hm with he | ⟨-, -, hr⟩
    · rw [he]
    · exact ContractShape_lift id (G := H.wavedThetaGraph) (fun x y ⟨c, hc, hj, hx, hy⟩ =>
        ContractShape_reach_fromRel ⟨c, hc, Or.inl ⟨hj, hd c hc⟩, hx, hy⟩) hr
  · have hcH : c ∈ H.comps := hsub.subset (List.mem_append_left _ hc)
    exact ContractShape_reach_fromRel ⟨c, hcH, Or.inr (hb c hc), hx, hy⟩

/-- **The end of the contraction.** A graph `Γ` with the shape of an `l`-th order self-energy
whose dotted edges all join two external atoms is normal regular with `x`, `y` read as internal
atoms (when it has no dotted edge), or diagonal ([I, Def 2.13 (i)]: its dotted edges join `x`
and `y`). -/
theorem ContractShape.final {l n : ℕ} (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩])
    (hext : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∧ c.y.isLeft = true) :
    (∃ C, Γ.internalize.Normal C) ∨ G13.IsDiag Γ := by
  obtain ⟨⟨C, hN, hA⟩, hdet, -, hDC⟩ := (ContractShape_shape Γ).1 hΓ
  have hS : ∀ c ∈ Γ.comps, c.kind.isSolid = false := fun c hc =>
    ContractShape_noSolid c (List.all_eq_true.1 hdet c hc)
  by_cases hdot : ∃ c ∈ Γ.comps, c.kind = .dot
  · refine Or.inr ⟨hdot, fun c hc hk => ?_⟩
    have hne := ContractShape_noLoop Γ hA hc hk
    obtain ⟨hx, hy⟩ := hext c hc hk
    rcases hcx : c.x with a | a <;> rcases hcy : c.y with b | b <;>
      rw [hcx] at hx hne <;> rw [hcy] at hy hne <;> simp at hx hy
    fin_cases a <;> fin_cases b <;> simp at hne ⊢
  · simp only [not_exists, not_and] at hdot
    have hxdot : ∀ c ∈ Γ.comps, c.kind = .xdot → c.x = c.y := by
      intro c hc hx
      by_contra hne
      obtain ⟨e, he, hs, -⟩ := (hN.2.2 c.x c.y hne).1 ⟨c, hc, hx, Or.inl ⟨rfl, rfl⟩⟩
      exact absurd hs (by rw [hS e he]; decide)
    have hk : ∀ c ∈ Γ.internalize.comps,
        c.kind ≠ .dot ∧ c.kind.isSolid = false ∧ (c.kind = .xdot → c.x = c.y) := by
      intro c hc
      rw [ContractShape_internalize_comps] at hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact ⟨hdot c' hc', hS c' hc', fun hx => congrArg ContractShape_int (hxdot c' hc' hx)⟩
    exact Or.inl ⟨_, ContractShape_normal_int _ hk
      (ContractShape_waved _ (fun c hc => (hk c hc).1) hDC)⟩

/-- Without a dotted edge between an internal and an external atom, every dotted edge of a graph
with the shape of a self-energy joins two external atoms (`Graph.Regular.noIntDot`). -/
private theorem ContractShape_ends {l n : ℕ} (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩])
    (hex : ¬ ∃ c ∈ Γ.comps, c.kind = .dot ∧ ∃ (j : Fin n) (a₀ : Fin 2),
      (c.x = .inr j ∧ c.y = .inl a₀ ∨ c.x = .inl a₀ ∧ c.y = .inr j)) :
    ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∧ c.y.isLeft = true := by
  obtain ⟨⟨C, hN, -⟩, -⟩ := (ContractShape_shape Γ).1 hΓ
  intro c hc hk
  have h := hN.1.noIntDot c hc hk
  rcases hcx : c.x with a | a <;> rcases hcy : c.y with b | b
  · exact ⟨rfl, rfl⟩
  · exact absurd ⟨c, hc, hk, b, a, Or.inr ⟨hcx, hcy⟩⟩ hex
  · exact absurd ⟨c, hc, hk, a, b, Or.inl ⟨hcx, hcy⟩⟩ hex
  · rw [hcx, hcy] at h
    simp at h

/-! ## The contraction -/

/-- Contraction of the dotted edges between an internal and an external atom ([I, Def 3.1]): a
graph with the shape of an `l`-th order self-energy has a graph with the same value on every
data record and with the shape of an `l`-th order self-energy (scaling order, deterministic
kinds, the forest of dotted edges and the doubly connected property with `x`, `y` internal) that
is normal regular with `x`, `y` read as internal atoms, or diagonal. -/
def G13.dotContractStmt : Prop :=
  ∀ (l n : ℕ) (Γ : Graph 2 n), SelfEnergyShape l [⟨n, Γ⟩] →
    ∃ (n' : ℕ) (Γ' : Graph 2 n'), SelfEnergyShape l [⟨n', Γ'⟩] ∧
      (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin 2 → ι),
        Γ'.val D e = Γ.val D e) ∧
      ((∃ C, Γ'.internalize.Normal C) ∨ G13.IsDiag Γ')

/-- **The contraction** ([I, Def 3.1], [I, Def 2.12]): every dotted edge between an internal and
an external atom of a graph with the shape of an `l`-th order self-energy is contracted, one at
a time (`ContractShape.step`, `Contract.val_eq`); at the end every dotted edge joins `x` and `y`,
and the graph is normal regular with `x`, `y` internal or diagonal (`ContractShape.final`). -/
theorem G13.dotContract : G13.dotContractStmt := by
  intro l n
  induction n with
  | zero =>
    intro Γ hΓ
    exact ⟨0, Γ, hΓ, fun _ _ _ _ _ => rfl,
      ContractShape.final Γ hΓ (ContractShape_ends Γ hΓ fun ⟨_, _, _, j, _⟩ => j.elim0)⟩
  | succ m ih =>
    intro Γ hΓ
    by_cases hex : ∃ c ∈ Γ.comps, c.kind = .dot ∧ ∃ (j : Fin (m + 1)) (a₀ : Fin 2),
        (c.x = .inr j ∧ c.y = .inl a₀ ∨ c.x = .inl a₀ ∧ c.y = .inr j)
    · obtain ⟨c, hc, hk, j, a₀, hxy⟩ := hex
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      obtain ⟨n', Γ', h1, h2, h3⟩ :=
        ih (Contract.graph Γ ⟨i, hi⟩ j a₀) (ContractShape.step Γ ⟨i, hi⟩ j a₀ hk hxy hΓ)
      exact ⟨n', Γ', h1, fun ι _ _ D e =>
        (h2 ι D e).trans (Contract.val_eq Γ ⟨i, hi⟩ j a₀ hk hxy D e), h3⟩
    · exact ⟨m + 1, Γ, hΓ, fun _ _ _ _ _ => rfl,
        ContractShape.final Γ hΓ (ContractShape_ends Γ hΓ hex)⟩

end RBM8D.Graphs
