module

public import RBM8D.Diffusion.Defs
public import RBM8D.Graph.QExp.PSteps
public import RBM8D.Graph.ValueLemmas

@[expose] public section

/-!
# The error of the `T`-equation: the decomposition [I, (8.20)]

The graphs of the error `errMat` of the `n`-th order `T`-equation (the graphs of `A` in which `⊕`
and `⊖` do not lie in one dotted block, and the graphs of `Err`), read at `𝔟₁ = 𝔟₂ = 𝔟` after the
root edge `Θ_{⊗v}` is removed ([I, (8.14)–(8.15)], [II, Def 3.3 (4)]), in the form of [I, (8.20)]:

* the *tips* of a graph are its components with an end at `⊕` or `⊖` other than waved and dotted
  edges: the factors `G_{y𝔟}`, `Ḡ_{y'𝔟}` of the first form of [I, (8.20)], the `×`-dotted edges
  `y ≠ 𝔟`, the weights at `𝔟` and the diffusive edges `Θ_{y𝔟}`;
* the *core* `𝒢₀` is the graph of the other components, with `⊗`, `⊕`, `⊖` identified with one
  external atom `𝔟`; its internal atoms are those of the graph, the root atom included.

The rooted graph at `(x, 𝔟, 𝔟)` is the sum over the labels `s` of the internal atoms of the core
at `𝔟` times the tips at `⊕ = ⊖ = 𝔟`, with the root atom labelled `x` (`ErrBound.val_decomp`). The
first form `Σ_{y,y'} (𝒢₀)_{x,yy'} G_{y𝔟} Ḡ_{y'𝔟}` is the case of two solid tips `G_{y⊕}`, `Ḡ_{y'⊖}`
at distinct internal atoms; the forms with indices set equal are `y = y'`, `y` the root atom, and
`y = 𝔟` through a dotted edge of the core. The core is doubly connected whenever the graph is
(`ErrBound.core_doublyConnected`), and its scaling order is that of the graph minus the root edge
and the tips. `ErrBound.decomp` collects these facts for the graphs of `errMat`, with the diagonal
scaling order `n_𝔟 ≥ n + 1` and the graph properties of [II, Def 3.2] and [II, Def 6.3] that the
bounds of [I, (8.17)] read.

The last part gives the three graphs `r`, `r_m`, `r_ll` of order `5` with `r = r_m + r_ll`
(`G_{xx} = m + (G_{xx} − m)`), the transfer of the properties of an `n`-th order `T`-equation to the
equation with `−r`, `r_m` added to `R` and `r_ll` added to `A`, and the invariance of `corrMat` and
`errMat` under it.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

namespace ErrBound

/-! ## Tips and core -/

/-- A component with an end at `⊕` or `⊖`. -/
def atB {n : ℕ} (c : Comp (Atom 3 n)) : Bool :=
  c.x == .inl 1 || c.x == .inl 2 || c.y == .inl 1 || c.y == .inl 2

/-- A tip: a component with an end at `⊕` or `⊖` that is not a waved or dotted edge. -/
def isTip {n : ℕ} (c : Comp (Atom 3 n)) : Bool := atB c && !c.kind.joinsMol

/-- The atom map identifying `⊗`, `⊕`, `⊖` with the external atom `𝔟`; the internal atoms are
kept. -/
def pinB {n : ℕ} : Atom 3 n → Atom 1 n := Sum.elim (fun _ => .inl 0) .inr

/-- The core `𝒢₀` of [I, (8.20)] of a graph `Γ` with root component `j`: the components other
than the root component and the tips, with `⊗`, `⊕`, `⊖` identified with the external atom `𝔟`. -/
def core {n : ℕ} (Γ : Graph 3 n) (j : ℕ) : Graph 1 n :=
  ⟨((Γ.comps.eraseIdx j).filter fun c => !isTip c).map (Comp.map pinB), Γ.coeff⟩

/-- The tips of a graph `Γ` with root component `j`. -/
def tips {n : ℕ} (Γ : Graph 3 n) (j : ℕ) : List (Comp (Atom 3 n)) :=
  (Γ.comps.eraseIdx j).filter isTip

/-- The factor of the root atom `v` at `(x, 𝔟)`: `1_{s_v = x}` for an internal `v`, `1_{x = 𝔟}` for
`v = ⊕` or `v = ⊖`. -/
def rootInd {n : ℕ} {ι : Type*} [DecidableEq ι] (v : Atom 3 n) (x b : ι) (s : Fin n → ι) : ℂ :=
  match v with
  | .inr i => if s i = x then 1 else 0
  | .inl _ => if x = b then 1 else 0

/-- The graphs of `errMat`: those of `A` in which `⊕`, `⊖` do not lie in one dotted block, and those
of `Err`. -/
def errList (𝒬 : TEqRec) : Expansion 3 := 𝒬.A.filter (fun g => !g.2.pmBlockB) ++ 𝒬.Err

/-! ## The value: [I, (8.20)] -/

/-- The factor of a component after a map `f` of the atoms is the factor read at `σ ∘ f`. -/
private theorem comp_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

/-- The factor of a component reads the labelling only at its ends and its minor atoms. -/
private theorem comp_val_congr {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ₁ σ₂ : V → ι) (c : Comp V) (hx : σ₁ c.x = σ₂ c.x) (hy : σ₁ c.y = σ₂ c.y)
    (hm : ∀ u ∈ c.minor, σ₁ u = σ₂ u) : Comp.val D σ₁ c = Comp.val D σ₂ c := by
  have : c.minor.map σ₁ = c.minor.map σ₂ := List.map_congr_left hm
  simp only [Comp.val, hx, hy, this]

/-- The term of the image of a graph under a map of the atoms is the term read at `σ ∘ f`. -/
private theorem term_mapAtoms {k n k' n' : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (f : Atom k n → Atom k' n') (D : Data ι) (σ : Atom k' n' → ι) :
    (Γ.mapAtoms f).term D σ = Γ.term D (σ ∘ f) := by
  simp only [Graph.term, Graph.mapAtoms, List.map_map, Function.comp_def, comp_val_map]

/-- The root component is the first plain `Θ` edge from `⊗` when no other component starts at
`⊗`: `rootRest` removes it and roots the rest at its second end. -/
private theorem rootRest_eq {n : ℕ} (Γ : Graph 3 n) (j : Fin Γ.comps.length) (v : Atom 3 n)
    (hk : Γ.comps[j].kind = .theta []) (hxy : Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v)
    (hrest : ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0) :
    rootRest Γ = (Γ.dropComp j).rootGraph v := by
  simp only [Fin.getElem_fin] at hk hxy
  have hroot : rootTest Γ.comps[(j : ℕ)] = true := by simp [rootTest, hk, hxy.1]
  have hfalse : ∀ i (hi : i < Γ.comps.length), i ≠ j → rootTest Γ.comps[i] = false := by
    intro i hi hij
    have hmem : Γ.comps[i] ∈ (Γ.dropComp j).comps :=
      List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, hij, rfl⟩
    have := hrest _ hmem
    simp [rootTest, this]
  have hfind : Γ.comps.find? rootTest = some Γ.comps[(j : ℕ)] := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨hroot, j, j.2, rfl, fun i hi => ?_⟩
    have := hfalse i (hi.trans j.2) (Nat.ne_of_lt hi)
    simp [this]
  have hidx : Γ.comps.findIdx rootTest = j := by
    rw [List.findIdx_eq j.2]
    exact ⟨hroot, fun i hi => hfalse i (hi.trans j.2) (Nat.ne_of_lt hi)⟩
  unfold rootRest
  rw [hfind]
  simp only
  rw [hidx, hxy.2]

/-- The term of the graph without the root edge, at a labelling with `⊕ = ⊖ = 𝔟` and the labels
`s` of the internal atoms: the core at `𝔟` times the tips. -/
private theorem rest_term {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph 3 n) (j : ℕ)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx j, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor)
    (D : Data ι) (b : ι) (s : Fin n → ι) (σ : Atom 3 n → ι) (h1 : σ (.inl 1) = b)
    (h2 : σ (.inl 2) = b) (hs : ∀ i, σ (.inr i) = s i) :
    (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n).term D σ =
      (core Γ j).term D (Sum.elim ![b] s) *
        ((tips Γ j).map (Comp.val D (Sum.elim ![b, b, b] s))).prod := by
  have hag : ∀ τ : Atom 3 n → ι, τ (.inl 1) = b → τ (.inl 2) = b → (∀ i, τ (.inr i) = s i) →
      ∀ u : Atom 3 n, u ≠ .inl 0 → σ u = τ u := by
    intro τ t1 t2 ts u hu
    rcases u with a | i
    · fin_cases a
      · exact absurd rfl hu
      · exact h1.trans t1.symm
      · exact h2.trans t2.symm
    · exact (hs i).trans (ts i).symm
  have hval : ∀ τ : Atom 3 n → ι, τ (.inl 1) = b → τ (.inl 2) = b → (∀ i, τ (.inr i) = s i) →
      ∀ c ∈ Γ.comps.eraseIdx j, Comp.val D σ c = Comp.val D τ c := by
    intro τ t1 t2 ts c hc
    obtain ⟨hx, hy, hm⟩ := hrest c hc
    exact comp_val_congr D σ τ c (hag τ t1 t2 ts _ hx) (hag τ t1 t2 ts _ hy)
      fun u hu => hag τ t1 t2 ts u fun e => hm (e ▸ hu)
  have hp := (List.filter_append_perm (fun c => !isTip c) (Γ.comps.eraseIdx j))
  have hnt : ((Γ.comps.eraseIdx j).filter fun c => !!isTip c) = tips Γ j := by
    simp only [Bool.not_not, tips]
  rw [hnt] at hp
  have e1 : ((Γ.comps.eraseIdx j).map (Comp.val D σ)).prod =
      (((Γ.comps.eraseIdx j).filter fun c => !isTip c).map (Comp.val D σ)).prod *
        ((tips Γ j).map (Comp.val D σ)).prod := by
    rw [← (hp.map _).prod_eq, List.map_append, List.prod_append]
  have e2 : (((Γ.comps.eraseIdx j).filter fun c => !isTip c).map (Comp.val D σ)) =
      (((Γ.comps.eraseIdx j).filter fun c => !isTip c).map
        (Comp.val D (Sum.elim ![b] s ∘ pinB))) := by
    refine List.map_congr_left fun c hc => hval _ ?_ ?_ ?_ c (List.mem_filter.1 hc).1
    · rfl
    · rfl
    · intro i; rfl
  have e3 : (tips Γ j).map (Comp.val D σ) = (tips Γ j).map (Comp.val D (Sum.elim ![b, b, b] s)) :=
    List.map_congr_left fun c hc => hval _ rfl rfl (fun i => rfl) c (List.mem_filter.1 hc).1
  simp only [Graph.term, core, List.map_map, Function.comp_def, comp_val_map]
  rw [e1, e2, e3]
  simp only [Function.comp_def]
  ring

/-- `finDrop` is the inverse of `Fin.succAbove`. -/
private theorem succAbove_finDrop {m : ℕ} (i j : Fin (m + 1)) (h : j ≠ i) :
    i.succAbove (finDrop i j h) = j := by
  have hv : j.val ≠ i.val := Fin.val_ne_of_ne h
  ext
  simp only [Fin.succAbove, finDrop, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

/-- **[I, (8.20)]**: the rooted graph `𝒢_{x, 𝔟𝔟}` of a graph `Σ_x Θ_{⊗x} 𝒢_{x, 𝔟₁𝔟₂}` with root
component `j` ending at `v` is, at `(x, 𝔟, 𝔟)`, the sum over the labels `s` of the internal atoms of
`1_{s_v = x}` (`1_{x = 𝔟}` if `v` is `⊕` or `⊖`) times the core at `𝔟` times the tips at
`⊕ = ⊖ = 𝔟`. -/
theorem val_decomp {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph 3 n)
    (j : Fin Γ.comps.length) (v : Atom 3 n) (hv : v ≠ .inl 0)
    (hk : Γ.comps[j].kind = .theta []) (hxy : Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v)
    (hrest : ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor)
    (D : Data ι) (x b : ι) :
    (rootRest Γ).2.val D ![x, b, b] = ∑ s : Fin n → ι, rootInd v x b s *
      ((core Γ j).term D (Sum.elim ![b] s) *
        ((tips Γ j).map (Comp.val D (Sum.elim ![b, b, b] s))).prod) := by
  rw [rootRest_eq Γ j v hk hxy fun c hc => (hrest c hc).1]
  have hr : ∀ c ∈ Γ.comps.eraseIdx j, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor :=
    fun c hc => hrest c hc
  rcases v with a | i
  · have ha : ∀ y : ι, ![y, b, b] a = b := by
      intro y
      fin_cases a
      · exact absurd rfl hv
      · rfl
      · rfl
    simp only [Graph.rootGraph, Graph.val, rootInd]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hdot : Comp.val D (Sum.elim ![x, b, b] s) (mkC .dot (.inl 0) (.inl a)) =
        if x = b then 1 else 0 := by
      simp [Comp.val, mkC, ha]
    have hT : (⟨(Γ.dropComp j).comps ++ [mkC .dot (.inl 0) (.inl a)], Γ.coeff⟩ : Graph 3 n).term
        D (Sum.elim ![x, b, b] s) = (if x = b then 1 else 0) *
          (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 n).term D (Sum.elim ![x, b, b] s) := by
      simp only [Graph.term, Graph.dropComp, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, hdot]
      ring
    refine hT.trans ?_
    rw [rest_term Γ j hr D b s _ rfl rfl fun i => rfl]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    have hL : (Graph.rootGraph (Γ.dropComp j) (.inr i)).2.val D ![x, b, b] =
        ∑ s' : Fin m → ι, (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 (m + 1)).term D
          (Sum.elim ![x, b, b] (Fin.insertNth i x s')) := by
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [Graph.rootGraph, Graph.rootAt]
      rw [term_mapAtoms]
      change (Γ.dropComp j).term D _ = (Γ.dropComp j).term D _
      congr 1
      funext u
      rcases u with a | k
      · rfl
      · by_cases hk : k = i
        · subst hk
          simp only [Function.comp_apply, dite_true]
          exact (Fin.insertNth_apply_same (α := fun _ => ι) k x s').symm
        · simp only [Function.comp_apply, hk, dite_false, Sum.elim_inr]
          conv_rhs => rw [← succAbove_finDrop i k hk]
          exact (Fin.insertNth_apply_succAbove (α := fun _ => ι) i x s' _).symm
    rw [hL]
    set F : (Fin (m + 1) → ι) → ℂ := fun s => (core Γ j).term D (Sum.elim ![b] s) *
      ((tips Γ j).map (Comp.val D (Sum.elim ![b, b, b] s))).prod with hF
    have hterm : ∀ s' : Fin m → ι, (⟨Γ.comps.eraseIdx j, Γ.coeff⟩ : Graph 3 (m + 1)).term D
        (Sum.elim ![x, b, b] (Fin.insertNth i x s')) = F (Fin.insertNth i x s') :=
      fun s' => rest_term Γ j hr D b _ _ rfl rfl fun i => rfl
    simp only [hterm]
    symm
    calc ∑ s : Fin (m + 1) → ι, rootInd (.inr i) x b s * F s
        = ∑ p : ι × (Fin m → ι), rootInd (.inr i) x b (Fin.insertNth i p.1 p.2) *
            F (Fin.insertNth i p.1 p.2) :=
          ((Fin.insertNthEquiv (fun _ => ι) i).sum_comp fun s =>
            rootInd (.inr i) x b s * F s).symm
      _ = ∑ s' : Fin m → ι, F (Fin.insertNth i x s') := by
          rw [Fintype.sum_prod_type]
          simp [rootInd]

/-! ## Orders, molecules and kinds of the core -/

/-- The components of a graph are, up to order, the root component and the others. -/
private theorem comps_perm {k n : ℕ} (Γ : Graph k n) (j : Fin Γ.comps.length) :
    Γ.comps.Perm (Γ.comps[j] :: Γ.comps.eraseIdx j) :=
  (List.getElem_cons_eraseIdx_perm j.2).symm

/-- A component of the graph that differs from the root component in its kind or its first end is
a component of the graph without the root component. -/
private theorem mem_eraseIdx_of {k n : ℕ} (Γ : Graph k n) (j : Fin Γ.comps.length)
    (c : Comp (Atom k n)) (hc : c ∈ Γ.comps) (hne : c.kind ≠ Γ.comps[j].kind ∨ c.x ≠ Γ.comps[j].x) :
    c ∈ Γ.comps.eraseIdx j := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  refine List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, fun h => ?_, rfl⟩
  subst h
  rcases hne with h | h <;> exact h rfl

/-- The scaling order of the core plus the scaling orders of the tips plus `2` (the root edge) is
the scaling order of the graph ([I, Def 2.12]). -/
theorem ord_decomp {n : ℕ} (Γ : Graph 3 n) (j : Fin Γ.comps.length)
    (hk : Γ.comps[j].kind = .theta []) :
    (core Γ j).ord + ((tips Γ j).map fun c => c.kind.ord).sum + 2 = Γ.ord := by
  have hp := List.filter_append_perm (fun c => !isTip c) (Γ.comps.eraseIdx j)
  have hnt : ((Γ.comps.eraseIdx j).filter fun c => !!isTip c) = tips Γ j := by
    simp only [Bool.not_not, tips]
  rw [hnt] at hp
  have h2 : (Γ.comps[j]).kind.ord = 2 := by
    simp only [Fin.getElem_fin] at hk ⊢
    rw [hk]
    rfl
  have h1 : (Γ.comps.map fun c => c.kind.ord).sum = 2 +
      ((((Γ.comps.eraseIdx j).filter fun c => !isTip c).map fun c => c.kind.ord).sum +
        ((tips Γ j).map fun c => c.kind.ord).sum) := by
    rw [((comps_perm Γ j).map _).sum_eq, List.map_cons, List.sum_cons, h2,
      ← (hp.map _).sum_eq, List.map_append, List.sum_append]
  simp only [Graph.ord, core, List.map_map, Function.comp_def, Comp.map, h1]
  ring

/-- Two atoms in one molecule of the graph are in one molecule of the core, after `⊗`, `⊕`, `⊖`
are identified with `𝔟`: the root edge is not a waved or dotted edge, and the waved and dotted
edges are not tips. -/
private theorem sameMol_core {n : ℕ} (Γ : Graph 3 n) (j : Fin Γ.comps.length)
    (hk : Γ.comps[j].kind = .theta []) (u v : Atom 3 n) (h : Γ.SameMol u v) :
    (core Γ j).SameMol (pinB u) (pinB v) := by
  rcases h with rfl | ⟨hu, hv, h⟩
  · exact Or.inl rfl
  refine Or.inr ⟨?_, ?_, ?_⟩
  · rcases u with a | a
    · simp at hu
    · rfl
  · rcases v with a | a
    · simp at hv
    · rfl
  clear hu hv
  unfold Graph.molGraph at h ⊢
  rw [reachable_fromRel_iff] at h ⊢
  induction h with
  | rel a b hab =>
    obtain ⟨c, hc, hj, rfl, rfl⟩ := hab
    have hne : c.kind ≠ Γ.comps[j].kind := by
      rw [hk]
      intro e
      rw [e] at hj
      simp [Kind.joinsMol] at hj
    have hmem := mem_eraseIdx_of Γ j c hc (Or.inl hne)
    refine Relation.EqvGen.rel _ _ ⟨c.map pinB, ?_, hj, rfl, rfl⟩
    refine List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hmem, ?_⟩, rfl⟩
    simp [isTip, hj]
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- **The transfer of the doubly connected property** to the core: a black net of diffusive edges
and a blue net of diffusive and blue edges spanning the internal molecules of the graph give such
nets for the core. The edges of the nets between internal atoms are kept, and the molecules of the
graph lie in molecules of the core. -/
theorem core_doublyConnected {n : ℕ} (Γ : Graph 3 n) (j : Fin Γ.comps.length)
    (hk : Γ.comps[j].kind = .theta []) (hx : Γ.comps[j].x = .inl 0)
    (h : Γ.DoublyConnected) : (core Γ j).DoublyConnected := by
  apply Graph.dc_of_dcl
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc h
  set bi : Comp (Atom 3 n) → Bool := fun c => c.x.isRight && c.y.isRight with hbi
  have hbiT : ∀ c, bi c = true → (!isTip c) = true := by
    intro c hc
    simp only [hbi, Bool.and_eq_true] at hc
    obtain ⟨h1, h2⟩ := hc
    rcases hx' : c.x with a | a <;> rcases hy' : c.y with a' | a' <;> rw [hx'] at h1 <;>
      rw [hy'] at h2 <;> simp_all [isTip, atB]
  have hbiR : (Γ.comps.filter bi).Perm ((Γ.comps.eraseIdx j).filter bi) := by
    refine ((comps_perm Γ j).filter bi).trans ?_
    have : bi Γ.comps[j] = false := by
      simp only [Fin.getElem_fin] at hx ⊢
      simp [hbi, hx]
    rw [List.filter_cons_of_neg (by rw [Bool.not_eq_true]; exact this)]
  have hsub' : ((Γ.comps.eraseIdx j).filter bi).Sublist
      ((Γ.comps.eraseIdx j).filter fun c => !isTip c) := by
    have : (Γ.comps.eraseIdx j).filter bi =
        ((Γ.comps.eraseIdx j).filter fun c => !isTip c).filter bi := by
      rw [List.filter_filter]
      refine List.filter_congr fun c _ => ?_
      by_cases hc : bi c = true
      · simp [hc, hbiT c hc]
      · simp [hc]
    rw [this]
    exact List.filter_sublist
  have hmapI : ∀ (L : List (Comp (Atom 3 n))) (c : Comp (Atom 1 n)),
      c ∈ (L.filter bi).map (Comp.map pinB) → ∃ c₀ ∈ L, bi c₀ = true ∧ c = c₀.map pinB := by
    intro L c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact ⟨c₀, (List.mem_filter.1 hc₀).1, (List.mem_filter.1 hc₀).2, rfl⟩
  have hnet : ∀ (L : List (Comp (Atom 3 n))) (a b : Fin n), nrel Γ L a b →
      nrel (core Γ j) ((L.filter bi).map (Comp.map pinB)) a b := by
    intro L a b hab
    rcases hab with hm | ⟨c, hc, hca, hcb⟩
    · exact Or.inl (sameMol_core Γ j hk _ _ hm)
    · refine Or.inr ⟨c.map pinB, List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, ?_⟩, rfl⟩, ?_, ?_⟩
      · simp [hbi, hca, hcb]
      · simp [Comp.map, hca, pinB]
      · simp [Comp.map, hcb, pinB]
  have hspan : ∀ L : List (Comp (Atom 3 n)), (SimpleGraph.fromRel (nrel Γ L)).Preconnected →
      (SimpleGraph.fromRel (nrel (core Γ j) ((L.filter bi).map (Comp.map pinB)))).Preconnected := by
    intro L hL a b
    have h1 := hL a b
    rw [reachable_fromRel_iff] at h1 ⊢
    exact Relation.EqvGen.mono (hnet L) _ _ h1
  refine ⟨(Lb.filter bi).map (Comp.map pinB), (Lu.filter bi).map (Comp.map pinB), ?_, ?_, ?_,
    hspan Lb hsb, hspan Lu hsu⟩
  · rw [← List.map_append, ← List.filter_append]
    have h1 : ((Lb ++ Lu).filter bi).Subperm ((Γ.comps.eraseIdx j).filter fun c => !isTip c) :=
      ((hsub.filter bi).trans hbiR.subperm).trans hsub'.subperm
    exact subperm_map' h1 _
  · intro c hc
    obtain ⟨c₀, hc₀, -, rfl⟩ := hmapI Lb c hc
    exact hb c₀ hc₀
  · intro c hc
    obtain ⟨c₀, hc₀, -, rfl⟩ := hmapI Lu c hc
    exact hu c₀ hc₀

/-- A component of the core with an end at `𝔟` is a waved or dotted edge: the other components at
`⊕`, `⊖` are tips, and no component of the graph without the root edge is at `⊗`. -/
private theorem core_atB {n : ℕ} (Γ : Graph 3 n) (j : ℕ)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx j, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0) :
    ∀ c ∈ (core Γ j).comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.joinsMol = true := by
  intro c hc hcb
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  obtain ⟨hm, ht⟩ := List.mem_filter.1 hc₀
  obtain ⟨hx, hy⟩ := hrest c₀ hm
  have hb : atB c₀ = true := by
    rcases hcb with h | h
    · rcases hx' : c₀.x with a | a
      · rw [hx'] at hx
        fin_cases a <;> simp_all [atB]
      · simp [Comp.map, hx', pinB] at h
    · rcases hy' : c₀.y with a | a
      · rw [hy'] at hy
        fin_cases a <;> simp_all [atB]
      · simp [Comp.map, hy', pinB] at h
  simp only [isTip, hb, Bool.true_and, Bool.not_not] at ht
  exact ht

/-- The kinds of [II, Def 3.2] of a component do not depend on its atoms. -/
private theorem isTKind_map {V W : Type*} (N : ℕ) (f : V → W) (c : Comp V) :
    (c.map f).isTKind N = c.isTKind N := by
  simp only [Comp.isTKind, Comp.map, List.isEmpty_map]

/-- The core has the kinds of `Err` if the graph has them. -/
private theorem core_tKindsErr {n : ℕ} (Γ : Graph 3 n) (j : ℕ) (N : ℕ) (h : Γ.TKindsErr N) :
    (core Γ j).TKindsErr N := by
  unfold Graph.TKindsErr at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  have := h c₀ (List.mem_of_mem_eraseIdx (List.mem_filter.1 hc₀).1)
  simp only [isTKind_map]
  simpa only [Comp.map, List.isEmpty_map] using this

/-- The core has the kinds of [II, Def 3.2] if the graph has them. -/
private theorem core_tKinds {n : ℕ} (Γ : Graph 3 n) (j : ℕ) (N : ℕ) (h : Γ.TKinds N) :
    (core Γ j).TKinds N := by
  unfold Graph.TKinds at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  rw [isTKind_map]
  exact h c₀ (List.mem_of_mem_eraseIdx (List.mem_filter.1 hc₀).1)

/-- The tips are components of the graph. -/
private theorem tips_sublist {n : ℕ} (Γ : Graph 3 n) (j : ℕ) : (tips Γ j).Sublist Γ.comps :=
  List.filter_sublist.trans (List.eraseIdx_sublist _ _)

/-- The rooted graph of a graph without `P`/`Q` labels has no `P`/`Q` label. -/
private theorem rootGraph_labelFree {n : ℕ} (Γ : Graph 3 n) (v : Atom 3 n) (h : Γ.LabelFree) :
    (Γ.rootGraph v).2.LabelFree := by
  rcases v with a | i
  · intro c hc
    change c ∈ Γ.comps ++ [mkC .dot (.inl 0) (.inl a)] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h c hc
    · rcases hc with _ | ⟨_, hc⟩
      · rfl
      · cases hc
  · intro c hc
    change c ∈ Γ.comps.map (Comp.map _) at hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    change Option.map _ c₀.label = none
    rw [h c₀ hc₀]
    rfl


/-! ## The interface: the graphs of `errMat` in the form [I, (8.20)] -/

/-- **[I, (8.20)] for the graphs of the error `errMat`** ([I, (8.15)–(8.17)]), at `𝔟₁ = 𝔟₂ = 𝔟`.
For `4 ≤ n`, `n + 2 ≤ D` and formal sums `R`, `A`, `Q`, `Err` with the graph properties of
[II, Def 3.2] at order `n` and error order `D` (labels of entries in `[4, n − 1]`), every graph of
the form [II, Def 3.3 (4)] and the clauses of [II, Def 6.3] (the conjuncts of an `n`-th order
`T`-equation that are read here): every graph `g` of `errList` (the graphs of `A` in which `⊕`, `⊖`
do not lie in one dotted block, and those of `Err`) has a root component `j`, a plain `Θ_{⊗v}`
with `v ≠ ⊗`, such that
* the decomposition [I, (8.20)]: on every data record, the rooted graph `𝒢_{x,𝔟𝔟}` of `g` is
  `Σ_s 1_{s_v = x} 𝒢₀(s) Π_t t(s)` (with `1_{x = 𝔟}` if `v` is `⊕` or `⊖`), `𝒢₀` the core at `𝔟` and
  `t` the tips at `⊕ = ⊖ = 𝔟`: the factors `G_{y𝔟}`, `Ḡ_{y'𝔟}` bounded by the local law [I, (1.19)];
  the first form and the forms with indices set equal are read off the far ends of the tips;
* the core is doubly connected ([I, Def 6.5]; the property of `𝒢₀` that [I, Def 6.7] gives below
  [I, (8.20)]), read by the sums with two fixed atoms of [I, Lemma 6.10, (6.20)] and by the
  `B`-convolution `Σ_{x,y} B_{𝔞x} B_{xy}^{3/2} B_{y𝔟}^{1/2}` below [I, (8.20)] with [I, (1.24)];
* the scaling orders ([I, Def 2.12]): core plus tips plus the root edge is the scaling order of
  `g`, and the diagonal scaling order is `n_𝔟 ≥ n + 1` (`Graph.diagOrd`), the exponent of
  [I, (8.17)];
* the tips are components of `g`; the components of the core at `𝔟` are waved or dotted edges;
  the core has the kinds of `Err`;
* `g` is normal regular ([I, Def 2.11]), satisfies [II, Def 3.2 (9)], is doubly connected, has
  only diffusive edges at `⊗` and dot excess `0`;
* a graph of `A` has scaling order `> n`, `⊕`, `⊖` in distinct dotted blocks (so `n_𝔟` is its
  scaling order), no `P`/`Q` label (so neither has its rooted graph, whose labelled value is the
  value above: the expectation in [I, (8.15)–(8.17)] is that of this value), a core with the kinds
  of [II, Def 3.2], and the clause on the external atoms with the charge pattern, or no internal
  atom and the edge `Θ_{⊗⊕}`;
* a graph of `Err` has scaling order `> D`, the kinds of `Err` with the weights `W_d` of
  [II, (4.21)] (read by the majorant of `W_d`), at most one label group and no labelled dotted edge
  (read by the label removal of [II, Claims 8.6–8.7]), `Graph.RgCheck`, and is rooted at the
  external atoms when it has an internal atom and is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`. -/
def decompStmt : Prop :=
  ∀ (n D : ℕ) (𝒬 : TEqRec), 4 ≤ n → n + 2 ≤ D → 𝒬.toTRec.Shape (n - 1) n D →
    (∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, g.2.ThetaRooted) → 𝒬.toTRec.Def63 →
    ∀ g ∈ errList 𝒬, ∃ (j : ℕ) (v : Atom 3 g.1), v ≠ .inl 0 ∧
      (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Dt : Data ι) (x b : ι),
        (rootRest g.2).2.val Dt ![x, b, b] = ∑ s : Fin g.1 → ι, rootInd v x b s *
          ((core g.2 j).term Dt (Sum.elim ![b] s) *
            ((tips g.2 j).map (Comp.val Dt (Sum.elim ![b, b, b] s))).prod)) ∧
      (core g.2 j).DoublyConnected ∧
      (core g.2 j).ord + ((tips g.2 j).map fun c => c.kind.ord).sum + 2 = g.2.ord ∧
      (n : ℤ) + 1 ≤ g.2.diagOrd ∧
      (tips g.2 j).Sublist g.2.comps ∧
      (∀ c ∈ (core g.2 j).comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.joinsMol = true) ∧
      (core g.2 j).TKindsErr (n - 1) ∧
      ((∃ C, g.2.Normal C) ∧ g.2.AtExternals ∧ g.2.DoublyConnected ∧ g.2.TensorDiffusive ∧
        g.2.dotExcess = 0) ∧
      (g ∈ 𝒬.A.filter (fun h => !h.2.pmBlockB) →
        (n : ℤ) < g.2.ord ∧ g.2.pmBlockB = false ∧ g.2.diagOrd = g.2.ord ∧ g.2.LabelFree ∧
          (rootRest g.2).2.LabelFree ∧ (core g.2 j).TKinds (n - 1) ∧
          ((g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB)) ∧
      (g ∈ 𝒬.Err → (D : ℤ) < g.2.ord ∧ g.2.TKindsErr (n - 1) ∧ g.2.labels.length ≤ 1 ∧
        g.2.NoLabDot ∧ g.2.RgCheck ∧ (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt))

/-- **[I, (8.20)] for the graphs of `errMat`**, with the transfer of the doubly connected
property to the core, the scaling orders and the diagonal scaling order `n_𝔟 ≥ n + 1`
(`decompStmt`). -/
theorem decomp : decompStmt := by
  intro n D 𝒬 hn hD hS hR hDef g hg
  obtain ⟨⟨hS1, hS2⟩, -, hSA, -, hSE⟩ := hS
  obtain ⟨⟨-, hDA, -⟩, hDall, -, -, -, hDQE, hDroot, -, -⟩ := hDef
  have hgm : g ∈ 𝒬.A.filter (fun h => !h.2.pmBlockB) ∨ g ∈ 𝒬.Err := List.mem_append.1 hg
  have hall : g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err := by
    rcases hgm with h | h
    · simp [(List.mem_filter.1 h).1]
    · simp [h]
  obtain ⟨j, v, hv, hk, -, -, hxy, hrest, -⟩ := hR g hall
  have hr : ∀ c ∈ (g.2.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor :=
    fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1, (hrest c hc).2.2.1⟩
  have hr' : ∀ c ∈ g.2.comps.eraseIdx j, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 :=
    fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1⟩
  have hG : (∃ C, g.2.Normal C) ∧ g.2.TKindsErr (n - 1) ∧ g.2.AtExternals ∧
      g.2.DoublyConnected := by
    rcases hgm with h | h
    · obtain ⟨h1, h2, h3, h4⟩ := hS1 g (by simp [TEqRec.toTRec, (List.mem_filter.1 h).1])
      exact ⟨h1, Graph.tKindsErr_of_tKinds _ _ h2, h3, h4⟩
    · exact hS2 g h
  obtain ⟨hNo, hKE, hAE, hDC⟩ := hG
  obtain ⟨hTD, hdx, hNL, hlab⟩ := hDall g hall
  have hdiag : (n : ℤ) + 1 ≤ g.2.diagOrd := by
    rcases hgm with h | h
    · have hpm : g.2.pmBlockB = false := by simpa using (List.mem_filter.1 h).2
      have := (hSA g (List.mem_filter.1 h).1).2
      simp only [Graph.diagOrd, hpm]
      simp only [Bool.false_eq_true, ite_false, sub_zero]
      omega
    · have := hSE g h
      have hD' : ((n + 2 : ℕ) : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
      push_cast at hD'
      simp only [Graph.diagOrd]
      split_ifs <;> omega
  refine ⟨j, v, hv, fun ι _ _ Dt x b => val_decomp g.2 j v hv hk hxy hr Dt x b,
    core_doublyConnected g.2 j hk hxy.1 hDC, ord_decomp g.2 j hk, hdiag, tips_sublist g.2 j,
    core_atB g.2 j hr', core_tKindsErr g.2 j _ hKE, ⟨hNo, hAE, hDC, hTD, hdx⟩, fun h => ?_,
    fun h => ?_⟩
  · have hA := (List.mem_filter.1 h).1
    have hpm : g.2.pmBlockB = false := by simpa using (List.mem_filter.1 h).2
    obtain ⟨hLF, hord⟩ := hSA g hA
    have hT : g.2.TKinds (n - 1) := (hS1 g (by simp [TEqRec.toTRec, hA])).2.1
    refine ⟨hord, hpm, by simp [Graph.diagOrd, hpm], hLF, ?_, core_tKinds g.2 j _ hT,
      (hDA g hA).2⟩
    rw [rootRest_eq g.2 j v hk hxy fun c hc => (hrest c hc).1]
    exact rootGraph_labelFree _ v fun c hc => hLF c (List.mem_of_mem_eraseIdx hc)
  · refine ⟨hSE g h, hKE, hlab, hNL, hDQE g (by simp [TEqRec.toTRec, h]), fun h0 h1 =>
      hDroot g (by simp [TEqRec.toTRec, h]) h0 h1⟩

section Decide

end Decide

end ErrBound

end RBM8D
