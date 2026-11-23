module

public import RBM8D.Diffusion.Defs

@[expose] public section

/-!
# The rooted `T`-equation

The identity [I, (8.14)] before the expectation (`rootedTEqStmt`): for a `T`-equation `𝒬` whose
graphs have the form `Σ_x Θ_{a x} 𝒢_{x, b₁ b₂}` of [II, Def 3.3 (4)], and every record with the
model relations, `T_{a, b b} = Σ_x Θ_{a x} (Y'_{x b} + (Σ̃^{(n)} T)_{x, b b})` at every sample.

The proof reads the `T`-equation only through its identity [II, (3.5)] and the form (4) of its
graphs. For one graph `Γ` of that form, the plain `Θ` edge from `⊗` is split off: the value of `Γ`
at `a` is `Σ_x Θ_{a x}` times the value of the rooted graph `𝒢_x` (`rootRest`), whether the second
end of the root edge is an external atom (the rooted graph carries the dotted edge `x = b`) or an
internal atom (it becomes the external atom `x`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

namespace Rooting

/-! ## Maps of atoms that are injective only on the atoms read -/

/-- `dedup` commutes with a map that is injective on the entries of the list. -/
private theorem dedup_map_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (l : List α) (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).dedup = l.dedup.map f := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    by_cases ha : a ∈ l
    · rw [List.map_cons, List.dedup_cons_of_mem (List.mem_map_of_mem ha),
        List.dedup_cons_of_mem ha, ih']
    · have hna : f a ∉ l.map f := by
        intro h
        obtain ⟨y, hy, hy'⟩ := List.mem_map.1 h
        have hay := hf a List.mem_cons_self y (List.mem_cons_of_mem _ hy) hy'.symm
        subst hay
        exact ha hy
      rw [List.map_cons, List.dedup_cons_of_notMem hna, List.dedup_cons_of_notMem ha,
        List.map_cons, ih']

/-- The factor of a component after a map `f` of the atoms is the factor of the original
component read at `σ ∘ f`. -/
private theorem comp_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

/-- The labelled term of the image of a graph under a map `f` of the atoms is the labelled term
of the graph read at `σ ∘ f`, when `f` is injective on a set `S` that contains the atoms of all
labels of the graph. -/
private theorem termR_mapAtoms_injOn {k n k' n' : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (f : Atom k n → Atom k' n') (S : Set (Atom k n)) (hf : Set.InjOn f S)
    (hS : ∀ c ∈ Γ.comps, ∀ ℓ, c.label = some ℓ → ℓ.2 ∈ S)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k' n' → ι) (ω : Ω) :
    (Γ.mapAtoms f).termR PF D σ ω = Γ.termR PF D (σ ∘ f) ω := by
  have hLS : ∀ ℓ ∈ Γ.comps.filterMap Comp.label, ℓ.2 ∈ S := by
    intro ℓ hℓ
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 hℓ
    exact hS c hc ℓ hcl
  have hinj : ∀ ℓ ∈ Γ.comps.filterMap Comp.label, ∀ ℓ' ∈ Γ.comps.filterMap Comp.label,
      Prod.map id f ℓ = Prod.map id f ℓ' → ℓ = ℓ' := by
    intro ℓ hℓ ℓ' hℓ' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.map_fst, Prod.map_snd, id] at h1 h2
    exact Prod.ext h1 (hf (hLS ℓ hℓ) (hLS ℓ' hℓ') h2)
  have hlab : (Γ.mapAtoms f).labels = Γ.labels.map (Prod.map id f) := by
    unfold Graph.labels Graph.mapAtoms
    simp only
    rw [← dedup_map_of_injOn _ hinj, List.map_filterMap, List.filterMap_map]
    rfl
  have hunl : ∀ c : Comp (Atom k n), (Comp.map f c).label.isNone = c.label.isNone := by
    intro c
    simp [Comp.map]
  have hgrp : ∀ ℓ ∈ Γ.labels, ∀ c ∈ Γ.comps,
      decide ((Comp.map f c).label = some (Prod.map id f ℓ)) = decide (c.label = some ℓ) := by
    intro ℓ hℓ c hc
    have hℓS : ℓ.2 ∈ S := hLS ℓ (List.mem_dedup.1 hℓ)
    cases hcl : c.label with
    | none => simp [Comp.map, hcl]
    | some ℓ' =>
      have hℓ'S : ℓ'.2 ∈ S := hS c hc ℓ' hcl
      have : (Comp.map f c).label = some (Prod.map id f ℓ') := by simp [Comp.map, hcl]
      rw [this]
      have key : Prod.map id f ℓ' = Prod.map id f ℓ ↔ ℓ' = ℓ := by
        constructor
        · intro h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only [Prod.map_fst, Prod.map_snd, id] at h1 h2
          exact Prod.ext h1 (hf hℓ'S hℓS h2)
        · rintro rfl
          rfl
      simp [key]
  unfold Graph.termR
  rw [hlab]
  have e1 : (((Γ.mapAtoms f).comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)) =
      ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) (σ ∘ f))) := by
    simp only [Graph.mapAtoms, List.filter_map, List.map_map, Function.comp_def, comp_val_map,
      hunl]
  have e2 : ((Γ.labels.map (Prod.map id f)).map fun ℓ => PF.op ℓ.1 (σ ℓ.2) (fun ω' =>
        (((Γ.mapAtoms f).comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (D ω') σ)).prod) ω) =
      Γ.labels.map fun ℓ => PF.op ℓ.1 ((σ ∘ f) ℓ.2) (fun ω' =>
        ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (D ω') (σ ∘ f))).prod) ω := by
    rw [List.map_map]
    refine List.map_congr_left fun ℓ hℓ => ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id, Function.comp_def]
    congr 2
    funext ω'
    simp only [Graph.mapAtoms, List.filter_map, List.map_map, Function.comp_def, comp_val_map]
    congr 2
    exact List.filter_congr fun c hc => hgrp ℓ hℓ c hc
  rw [e1, e2]
  rfl

/-- A labelled term reads the labelling only on the atoms of the ends, the minors and the labels
of the components. -/
private theorem termR_congr {k n : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Graph k n) (PF : PFamily Ω ι) (D : Ω → Data ι) (σ₁ σ₂ : Atom k n → ι) (ω : Ω)
    (h : ∀ c ∈ Γ.comps, σ₁ c.x = σ₂ c.x ∧ σ₁ c.y = σ₂ c.y ∧ (∀ u ∈ c.minor, σ₁ u = σ₂ u) ∧
      ∀ ℓ, c.label = some ℓ → σ₁ ℓ.2 = σ₂ ℓ.2) :
    Γ.termR PF D σ₁ ω = Γ.termR PF D σ₂ ω := by
  have hv : ∀ (D' : Data ι), ∀ c ∈ Γ.comps, Comp.val D' σ₁ c = Comp.val D' σ₂ c := by
    intro D' c hc
    obtain ⟨hx, hy, hm, -⟩ := h c hc
    have : c.minor.map σ₁ = c.minor.map σ₂ := List.map_congr_left hm
    simp only [Comp.val, hx, hy, this]
  unfold Graph.termR
  congr 2
  · congr 1
    exact List.map_congr_left fun c hc => hv _ c (List.mem_filter.1 hc).1
  · refine List.map_congr_left fun ℓ hℓ => ?_
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 (List.mem_dedup.1 hℓ)
    have h2 : σ₁ ℓ.2 = σ₂ ℓ.2 := (h c hc).2.2.2 ℓ hcl
    rw [h2]
    congr 2
    funext ω'
    congr 1
    exact List.map_congr_left fun c hc => hv _ c (List.mem_filter.1 hc).1

/-! ## Splitting off the root edge -/

/-- The components of a graph are, up to order, one component `c` and the components of the graph
without `c`. -/
private theorem dropComp_perm {k n : ℕ} (Γ : Graph k n) (j : Fin Γ.comps.length) :
    Γ.comps.Perm (Γ.comps[j] :: (Γ.dropComp j).comps) :=
  (List.getElem_cons_eraseIdx_perm j.2).symm

/-- The labelled term of a graph with an unlabelled plain `Θ` edge `c` from `⊗` to `v` is the
entry `Θ_{σ ⊗, σ v}` times the labelled term of the graph without `c`. -/
private theorem termR_root {n : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph 3 n)
    (j : Fin Γ.comps.length) (v : Atom 3 n) (hk : Γ.comps[j].kind = .theta [])
    (hl : Γ.comps[j].label = none) (hxy : Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom 3 n → ι) (ω : Ω) :
    Γ.termR PF D σ ω = (D ω).Theta (σ (.inl 0)) (σ v) * (Γ.dropComp j).termR PF D σ ω := by
  have hperm := dropComp_perm Γ j
  have hcval : ∀ D' : Data ι, Comp.val D' σ Γ.comps[j] = D'.Theta (σ (.inl 0)) (σ v) := by
    intro D'
    simp only [Comp.val, hk, hxy.1, hxy.2]
    rfl
  simp only [Fin.getElem_fin] at hk hl hxy hperm hcval
  have e1 : ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod =
      (D ω).Theta (σ (.inl 0)) (σ v) *
        (((Γ.dropComp j).comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod := by
    rw [((hperm.filter _).map _).prod_eq]
    simp [hl, hcval]
  have e2 : ∀ (ℓ : PQ × Atom 3 n) (g : Comp (Atom 3 n) → ℂ),
      ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map g).prod =
        (((Γ.dropComp j).comps.filter fun c => decide (c.label = some ℓ)).map g).prod := by
    intro ℓ g
    rw [((hperm.filter _).map _).prod_eq]
    simp [hl]
  have hlab : Γ.labels.Perm (Γ.dropComp j).labels := by
    unfold Graph.labels
    refine List.Perm.dedup ?_
    refine (hperm.filterMap _).trans ?_
    simp [hl]
  unfold Graph.termR
  rw [e1]
  simp only [e2]
  rw [(hlab.map _).prod_eq]
  change _ = _ * (Coeff.eval (D ω).m Γ.coeff * _ * _)
  ring

/-- The component of the root edge is the first component with a plain `Θ` edge from `⊗`, when
the other components do not start at `⊗`: `rootRest` removes it and roots the rest at its second
end. -/
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

/-! ## The graph without the root edge does not read `⊗` -/

/-- Two labellings that agree away from `⊗` give the same labelled term to a graph that does not
read `⊗` in the ends, the minors and the labels of its components. -/
private theorem termR_congr_root {n : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Graph 3 n)
    (hrest : ∀ c ∈ Γ.comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0))
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ₁ σ₂ : Atom 3 n → ι) (ω : Ω)
    (h : ∀ u, u ≠ .inl 0 → σ₁ u = σ₂ u) :
    Γ.termR PF D σ₁ ω = Γ.termR PF D σ₂ ω := by
  refine termR_congr Γ PF D σ₁ σ₂ ω fun c hc => ?_
  obtain ⟨hx, hy, hm, hl⟩ := hrest c hc
  refine ⟨h _ hx, h _ hy, fun u hu => h u fun e => hm (e ▸ hu), fun ℓ hℓ => h _ ?_⟩
  intro e
  apply hl
  rw [hℓ]
  exact congrArg some e

/-- The external labellings `(x, b, b)` and `(y, b, b)` agree away from `⊗`. -/
private theorem vec_agree {ι : Type*} (x y b : ι) (j : Fin 3) (hj : j ≠ 0) :
    ![x, b, b] j = ![y, b, b] j := by
  fin_cases j
  · exact absurd rfl hj
  · rfl
  · rfl

/-- Labellings `(x, b, b | s)` and `(y, b, b | s)` of the atoms agree away from `⊗`. -/
private theorem elim_agree {n : ℕ} {ι : Type*} (x y b : ι) (s : Fin n → ι) (u : Atom 3 n)
    (hu : u ≠ .inl 0) : Sum.elim ![x, b, b] s u = Sum.elim ![y, b, b] s u := by
  rcases u with i | i
  · exact vec_agree x y b i fun h => hu (h ▸ rfl)
  · rfl

/-! ## The root edge ends at an external atom -/

/-- An unlabelled component appended to a graph multiplies its labelled term by its factor. -/
private theorem termR_snoc {k n : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (c : Comp (Atom k n)) (hc : c.label = none) (PF : PFamily Ω ι) (D : Ω → Data ι)
    (σ : Atom k n → ι) (ω : Ω) :
    (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph k n).termR PF D σ ω =
      Comp.val (D ω) σ c * Γ.termR PF D σ ω := by
  have hlab : (⟨Γ.comps ++ [c], Γ.coeff⟩ : Graph k n).labels = Γ.labels := by
    simp [Graph.labels, List.filterMap_append, hc]
  unfold Graph.termR
  rw [hlab]
  simp [List.filter_append, hc]
  ring

/-- The root edge `Θ_{a v}` with `v = b'` external: `Σ_s Θ_{a b} 𝒢(a, s)` is `Σ_x Θ_{a x}`
times the value of the rooted graph, which carries the dotted edge `x = b`. -/
private theorem root_external {n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph 3 n) (b' : Fin 3) (hb' : b' ≠ 0)
    (hrest : ∀ c ∈ Γ.comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0))
    (PF : PFamily Ω ι) (D : Ω → Data ι) (a b : ι) (ω : Ω) :
    ∑ s : Fin n → ι, (D ω).Theta a (Sum.elim ![a, b, b] s (.inl b')) *
        Γ.termR PF D (Sum.elim ![a, b, b] s) ω =
      ∑ x, (D ω).Theta a x * (Γ.rootGraph (.inl b')).2.valR PF D ![x, b, b] ω := by
  have hb : ∀ x : ι, ![x, b, b] b' = b := by
    intro x
    fin_cases b'
    · exact absurd rfl hb'
    · rfl
    · rfl
  have key : ∀ x : ι, (Γ.rootGraph (.inl b')).2.valR PF D ![x, b, b] ω =
      if x = b then ∑ s : Fin n → ι, Γ.termR PF D (Sum.elim ![a, b, b] s) ω else 0 := by
    intro x
    have hrg : Γ.rootGraph (.inl b') =
        ⟨n, ⟨Γ.comps ++ [mkC .dot (.inl 0) (.inl b')], Γ.coeff⟩⟩ := rfl
    have hdot : ∀ s : Fin n → ι,
        (⟨Γ.comps ++ [mkC .dot (.inl 0) (.inl b')], Γ.coeff⟩ : Graph 3 n).termR PF D
          (Sum.elim ![x, b, b] s) ω = (if x = b then 1 else 0) *
            Γ.termR PF D (Sum.elim ![x, b, b] s) ω := by
      intro s
      rw [termR_snoc Γ _ rfl]
      simp [Comp.val, mkC, hb]
    rw [hrg]
    simp only [Graph.valR, hdot, ← Finset.mul_sum]
    by_cases hx : x = b
    · subst hx
      simp only [ite_true, one_mul]
      exact Finset.sum_congr rfl fun s _ =>
        termR_congr_root Γ hrest PF D _ _ ω fun u hu => elim_agree x a x s u hu
    · simp [hx]
  simp only [key, Sum.elim_inl, hb, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.mul_sum]

/-! ## The root edge ends at an internal atom -/

/-- The map of the atoms of `Graph.rootAt`: the internal atom `i` becomes the external atom `x`,
the other internal atoms are renumbered. -/
private def rootMap {n : ℕ} (i : Fin n) : Atom 3 n → Atom 3 (n - 1)
  | .inl j => .inl j
  | .inr j => if h : j = i then .inl 0 else .inr (finDrop i j h)

/-- `Graph.rootAt` is the image under `rootMap`. -/
private theorem rootAt_eq {n : ℕ} (Γ : Graph 3 n) (i : Fin n) :
    Γ.rootAt i = Γ.mapAtoms (rootMap i) := by
  rfl

/-- `finDrop` is the inverse of `Fin.succAbove`. -/
private theorem succAbove_finDrop {m : ℕ} (i j : Fin (m + 1)) (h : j ≠ i) :
    i.succAbove (finDrop i j h) = j := by
  have hv : j.val ≠ i.val := Fin.val_ne_of_ne h
  ext
  simp only [Fin.succAbove, finDrop, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all <;> omega

/-- `rootMap` is injective away from `⊗`. -/
private theorem rootMap_injOn {m : ℕ} (i : Fin (m + 1)) :
    Set.InjOn (rootMap i) {u | u ≠ .inl 0} := by
  intro u hu u' hu' h
  rcases u with j | j <;> rcases u' with j' | j'
  · simpa [rootMap] using h
  · by_cases h' : j' = i
    · simp only [rootMap, h', ↓reduceDIte, Sum.inl.injEq] at h
      exact absurd (congrArg Sum.inl h) hu
    · simp [rootMap, h'] at h
  · by_cases h' : j = i
    · simp only [rootMap, h', ↓reduceDIte, Sum.inl.injEq] at h
      exact absurd (congrArg Sum.inl h.symm) hu'
    · simp [rootMap, h'] at h
  · by_cases h1 : j = i <;> by_cases h2 : j' = i
    · rw [h1, h2]
    · simp [rootMap, h1, h2] at h
    · simp [rootMap, h1, h2] at h
    · simp only [rootMap, h1, h2, dite_false, Sum.inr.injEq] at h
      have := congrArg i.succAbove h
      rw [succAbove_finDrop, succAbove_finDrop] at this
      rw [this]

/-- The root edge `Θ_{a v}` with `v = i` internal: summing over the label `s_i` of `v` and the
other labels is summing over `x` and the labels of the other atoms of `𝒢_x`. -/
private theorem root_internal {m : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph 3 (m + 1)) (i : Fin (m + 1))
    (hrest : ∀ c ∈ Γ.comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0))
    (PF : PFamily Ω ι) (D : Ω → Data ι) (a b : ι) (ω : Ω) :
    ∑ s : Fin (m + 1) → ι, (D ω).Theta a (Sum.elim ![a, b, b] s (.inr i)) *
        Γ.termR PF D (Sum.elim ![a, b, b] s) ω =
      ∑ x, (D ω).Theta a x * (Γ.rootAt i).valR PF D ![x, b, b] ω := by
  have hS : ∀ c ∈ Γ.comps, ∀ ℓ, c.label = some ℓ → ℓ.2 ∈ {u : Atom 3 (m + 1) | u ≠ .inl 0} := by
    intro c hc ℓ hℓ e
    apply (hrest c hc).2.2.2
    rw [hℓ]
    exact congrArg some e
  have hval : ∀ (x : ι) (s' : Fin m → ι), (Γ.rootAt i).termR PF D (Sum.elim ![x, b, b] s') ω =
      Γ.termR PF D (Sum.elim ![a, b, b] (Fin.insertNth i x s')) ω := by
    intro x s'
    rw [rootAt_eq, termR_mapAtoms_injOn _ _ _ (rootMap_injOn i) hS]
    refine termR_congr_root Γ hrest PF D _ _ ω fun u hu => ?_
    rcases u with j | j
    · exact vec_agree x a b j fun h => hu (h ▸ rfl)
    · by_cases hj : j = i
      · subst hj
        simp [rootMap]
      · simp only [Function.comp_apply, rootMap, hj, dite_false, Sum.elim_inr]
        conv_rhs => rw [← succAbove_finDrop i j hj]
        simp
  have hR : ∀ x : ι, (Γ.rootAt i).valR PF D ![x, b, b] ω =
      ∑ s' : Fin m → ι, Γ.termR PF D (Sum.elim ![a, b, b] (Fin.insertNth i x s')) ω :=
    fun x => Finset.sum_congr rfl fun s' _ => hval x s'
  simp only [hR, Finset.mul_sum]
  calc ∑ s : Fin (m + 1) → ι, (D ω).Theta a (Sum.elim ![a, b, b] s (.inr i)) *
        Γ.termR PF D (Sum.elim ![a, b, b] s) ω
      = ∑ p : ι × (Fin m → ι), (D ω).Theta a (Sum.elim ![a, b, b] (Fin.insertNth i p.1 p.2)
          (.inr i)) * Γ.termR PF D (Sum.elim ![a, b, b] (Fin.insertNth i p.1 p.2)) ω :=
        ((Fin.insertNthEquiv (fun _ => ι) i).sum_comp fun s => (D ω).Theta a
          (Sum.elim ![a, b, b] s (.inr i)) * Γ.termR PF D (Sum.elim ![a, b, b] s) ω).symm
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s' _ => ?_
        simp

/-! ## One rooted graph, and the formal sums -/

/-- A graph of the form [II, Def 3.3 (4)] is `Σ_x Θ_{a x} 𝒢_{x, b₁ b₂}`: at `b₁ = b₂ = b` its
value is `Σ_x Θ_{a x}` times the value of the rooted graph `rootRest Γ` at `(x, b, b)`. -/
private theorem valR_rooted {n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph 3 n)
    (hΓ : Γ.ThetaRooted) (PF : PFamily Ω ι) (D : Ω → Data ι) (a b : ι) (ω : Ω) :
    Γ.valR PF D ![a, b, b] ω =
      ∑ x, (D ω).Theta a x * (rootRest Γ).2.valR PF D ![x, b, b] ω := by
  obtain ⟨j, v, hv, hk, hm, hl, hxy, hrest, -⟩ := hΓ
  rw [rootRest_eq Γ j v hk hxy fun c hc => (hrest c hc).1]
  have hL : Γ.valR PF D ![a, b, b] ω = ∑ s : Fin n → ι,
      (D ω).Theta a (Sum.elim ![a, b, b] s v) *
        (Γ.dropComp j).termR PF D (Sum.elim ![a, b, b] s) ω := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [termR_root Γ j v hk hl hxy]
    rfl
  rw [hL]
  rcases v with b' | i
  · exact root_external _ b' (fun h => hv (h ▸ rfl)) hrest PF D a b ω
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    exact root_internal _ i hrest PF D a b ω

/-- Every graph of a formal sum of graphs of the form [II, Def 3.3 (4)] is rooted: the value of the
sum at `(a, b, b)` is `Σ_x Θ_{a x}` times its rooted sum `gammaVal` at `(x, b, b)`. -/
private theorem valR_expansion_rooted {Ω ι : Type} [Fintype ι] [DecidableEq ι] (E : Expansion 3)
    (hE : ∀ g ∈ E, g.2.ThetaRooted) (PF : PFamily Ω ι) (D : Ω → Data ι) (a b : ι) (ω : Ω) :
    E.valR PF D ![a, b, b] ω = ∑ x, (D ω).Theta a x * gammaVal E PF D x b ω := by
  induction E with
  | nil => simp [Expansion.valR, gammaVal]
  | cons g E ih =>
    have ih' := ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    simp only [Expansion.valR, gammaVal, List.map_cons, List.sum_cons] at ih' ⊢
    rw [valR_rooted g.2 (hE g List.mem_cons_self) PF D a b ω, ih', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- The value of the leading graph `m Θ_{a b₁} Ḡ_{b₁ b₂}` at `(a, b, b)`. -/
private theorem valR_leadExp {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) (a b : ι) (ω : Ω) :
    leadExp.valR PF D ![a, b, b] ω =
      (D ω).Theta a b * ((D ω).m * star ((D ω).Gm ∅ b b)) := by
  simp [Expansion.valR, leadExp, thetaLabelGraph, Graph.valR, Graph.termR, Graph.labels, Comp.val,
    mkC, Coeff.eval, cm, CVar.eval, Data.chain, Charge.apply]
  ring

end Rooting

/-! ## The rooted `T`-equation -/

/-- The rooted `T`-equation ([I, (8.14)] before the expectation, [II, Def 3.3 (4)]): for a
`T`-equation `𝒬` and every record with the model relations, `T_{a, b b} = Σ_x Θ_{a x} (Y'_{x b} +
(Σ̃^{(n)} T)_{x, b b})`, at every sample. The identity [II, (3.5)] and the form (4) of the graphs
of `R`, `A`, `Q`, `Err` are the only properties of `𝒬` used. -/
theorem rootedTEq : rootedTEqStmt := by
  intro Sig n D 𝒬 hQ _hno Ω ι _ _ PF Dt hA hSC a b ω
  have hid := hQ.2.1 Ω ι PF Dt hA hSC ![a, b, b] ω
  have hroot := hQ.2.2.2.2.2.1
  have e0 : (![a, b, b] : Fin 3 → ι) 0 = a := rfl
  have e1 : (![a, b, b] : Fin 3 → ι) 1 = b := rfl
  have e2 : (![a, b, b] : Fin 3 → ι) 2 = b := rfl
  rw [e0, e1, e2] at hid
  have hassoc : leadExp ++ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err =
      leadExp ++ (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err) := by simp [List.append_assoc]
  have hsplit : (leadExp ++ (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err)).valR PF Dt ![a, b, b] ω =
      leadExp.valR PF Dt ![a, b, b] ω + (𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err).valR PF Dt ![a, b, b] ω := by
    simp [Expansion.valR, List.map_append, List.sum_append]
  rw [hassoc, hsplit, Rooting.valR_leadExp, Rooting.valR_expansion_rooted _ hroot PF Dt a b ω]
    at hid
  rw [hid]
  have h1 : ∑ x, (Dt ω).Theta a x * (if x = b then (Dt ω).m * star ((Dt ω).Gm ∅ b b) else 0) =
      (Dt ω).Theta a b * ((Dt ω).m * star ((Dt ω).Gm ∅ b b)) := by
    simp [mul_ite]
  have h2 : ∑ x, ((Dt ω).Theta * sigTilde n 𝒬.SigN (Dt ω)) a x * tGraph.valR PF Dt ![x, b, b] ω =
      ∑ x, (Dt ω).Theta a x *
        ∑ y, sigTilde n 𝒬.SigN (Dt ω) x y * tGraph.valR PF Dt ![y, b, b] ω := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  simp only [yRoot, mul_add, Finset.sum_add_distrib, h1, h2]

end RBM8D
