import RBM8D.TExp.Defs
import RBM8D.Bound.GraphAbs

/-!
# Contraction of a dotted edge between an internal and an external atom

A dotted edge `δ_{α a}` between an internal atom `α` and an external atom `a` reads "the internal
atom `α` is equal to the external atom `a`" ([I, Def 2.12]). Summing out `α` against this factor
identifies `α` with `a`, as the merge operation `O_merge` of [I, Def 3.1] does for two atoms:

* `Contract.atomMap j a₀`: external atoms are kept, the internal atom `j` goes to the external
  atom `a₀`, the internal atom `j.succAbove i` goes to `i`;
* `Contract.graph Γ i j a₀`: `Γ` without its `i`-th component, every other component mapped by
  `Contract.atomMap j a₀`, the coefficient kept;
* when the `i`-th component is a dotted edge between `inr j` and `inl a₀` (either orientation):
  the value on every data record is kept (`Contract.val_eq`), the scaling order is kept
  (`Contract.ord_eq`; the `+2` of the dotted edge against one summed atom, [I, (2.12)]), and the
  deterministic kinds of [II, Def 2.7 (i)] are kept (`Contract.all_isDetKind`);
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section Instances

end Instances

/-! ## The contraction -/

/-- The atom map of the contraction of the internal atom `j` into the external atom `a₀`
([I, Def 3.1] with an internal and an external atom identified): external atoms are kept,
`inr j ↦ inl a₀`, and `inr (j.succAbove i) ↦ inr i`. -/
def Contract.atomMap {k n : ℕ} (j : Fin (n + 1)) (a₀ : Fin k) : Atom k (n + 1) → Atom k n :=
  Sum.elim Sum.inl (Fin.insertNth (α := fun _ => Atom k n) j (Sum.inl a₀) Sum.inr)

@[simp]
theorem Contract.atomMap_inl {k n : ℕ} (j : Fin (n + 1)) (a₀ b : Fin k) :
    Contract.atomMap j a₀ (.inl b) = .inl b := rfl

@[simp]
theorem Contract.atomMap_self {k n : ℕ} (j : Fin (n + 1)) (a₀ : Fin k) :
    Contract.atomMap j a₀ (.inr j) = .inl a₀ := by
  simp [Contract.atomMap]

@[simp]
theorem Contract.atomMap_succAbove {k n : ℕ} (j : Fin (n + 1)) (a₀ : Fin k) (i : Fin n) :
    Contract.atomMap j a₀ (.inr (j.succAbove i)) = .inr i := by
  simp [Contract.atomMap]

/-- The contraction of the `i`-th component of `Γ` into the external atom `a₀` at the internal
atom `j`: the `i`-th component is removed, every other component is mapped by
`Contract.atomMap j a₀`, and the coefficient is kept. -/
def Contract.graph {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length) (j : Fin (n + 1))
    (a₀ : Fin k) : Graph k n :=
  ⟨(Γ.comps.eraseIdx i).map (Comp.map (Contract.atomMap j a₀)), Γ.coeff⟩

theorem Contract.graph_comps {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) :
    (Contract.graph Γ i j a₀).comps = (Γ.comps.eraseIdx i).map (Comp.map (Contract.atomMap j a₀)) :=
  rfl

/-- A component of the contraction is the image of a component of `Γ` other than the `i`-th. -/
theorem Contract.mem_graph_comps {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) (c' : Comp (Atom k n)) :
    c' ∈ (Contract.graph Γ i j a₀).comps ↔
      ∃ c ∈ Γ.comps.eraseIdx i, c.map (Contract.atomMap j a₀) = c' :=
  List.mem_map

/-- The components of `Γ` are the `i`-th one and the others, up to order. -/
theorem Contract.comps_perm {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length) :
    (Γ.comps[i] :: Γ.comps.eraseIdx i).Perm Γ.comps :=
  List.getElem_cons_eraseIdx_perm i.2

/-! ## Value, order and kinds -/

private theorem Contract_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

/-- The factor of a dotted edge between `inr j` and `inl a₀` is `1(σ(inr j) = σ(inl a₀))`. -/
private theorem Contract_val_dot {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (D : Data ι)
    (σ : Atom k (n + 1) → ι) (c : Comp (Atom k (n + 1))) (j : Fin (n + 1)) (a₀ : Fin k)
    (hk : c.kind = .dot)
    (hxy : c.x = .inr j ∧ c.y = .inl a₀ ∨ c.x = .inl a₀ ∧ c.y = .inr j) :
    Comp.val D σ c = if σ (.inr j) = σ (.inl a₀) then 1 else 0 := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp only at hk hxy
  subst hk
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Comp.val]
  · simp [Comp.val, eq_comm]

/-- At the label `a₀` of the internal atom `j`, the labelling of the atoms of `Γ` factors through
`Contract.atomMap j a₀`. -/
private theorem Contract_elim_insertNth {ι : Type*} {k n : ℕ} (j : Fin (n + 1)) (a₀ : Fin k)
    (e : Fin k → ι) (s : Fin n → ι) :
    Sum.elim e (Fin.insertNth (α := fun _ => ι) j (e a₀) s) =
      Sum.elim e s ∘ Contract.atomMap j a₀ := by
  funext u
  rcases u with b | u
  · rfl
  · by_cases h : u = j
    · subst h
      simp
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq h
      simp

/-- **Value.** If the `i`-th component of `Γ` is a dotted edge between the internal atom `j` and
the external atom `a₀` (either orientation), the contraction has the value of `Γ` on every data
record and at every labelling of the external atoms ([I, Def 3.1], [I, Def 2.12]). -/
theorem Contract.val_eq {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inr j ∧ Γ.comps[i].y = .inl a₀ ∨
      Γ.comps[i].x = .inl a₀ ∧ Γ.comps[i].y = .inr j)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin k → ι) :
    (Contract.graph Γ i j a₀).val D e = Γ.val D e := by
  have hperm := Contract.comps_perm Γ i
  have hterm : ∀ s : Fin (n + 1) → ι, Γ.term D (Sum.elim e s) =
      if s j = e a₀ then Γ.coeff.eval D.m *
        ((Γ.comps.eraseIdx i).map (Comp.val D (Sum.elim e s))).prod else 0 := by
    intro s
    unfold Graph.term
    rw [← (hperm.map (Comp.val D (Sum.elim e s))).prod_eq, List.map_cons, List.prod_cons,
      Contract_val_dot D _ _ j a₀ hk hxy]
    simp only [Sum.elim_inr, Sum.elim_inl]
    split_ifs with h <;> simp [h]
  unfold Graph.val
  simp_rw [hterm]
  rw [← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  rw [Finset.sum_ite_eq' Finset.univ (e a₀)]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [Contract_elim_insertNth j a₀ e s]
  unfold Graph.term
  simp only [Contract.graph, List.map_map]
  congr 2
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply]
  rw [Contract_val_map]

/-- **Order.** If the `i`-th component of `Γ` is a dotted edge, the contraction at an internal
atom has the scaling order of `Γ`: the dotted edge of order `2` is removed and one internal atom
is summed ([I, (2.12)]). -/
theorem Contract.ord_eq {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) (hk : Γ.comps[i].kind = .dot) :
    (Contract.graph Γ i j a₀).ord = Γ.ord := by
  have hperm := (Contract.comps_perm Γ i).map fun c => c.kind.ord
  unfold Graph.ord
  rw [← hperm.sum_eq, List.map_cons, List.sum_cons, hk]
  simp only [Contract.graph, List.map_map, Function.comp_def, Comp.map, Kind.ord]
  push_cast
  ring

/-- A component and its image under a map of the atoms are of a deterministic kind together. -/
theorem Contract.isDetKind_map {V W : Type*} (N : ℕ) (f : V → W) (c : Comp V) :
    (c.map f).isDetKind N = c.isDetKind N := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp only [Comp.isDetKind, Comp.map, List.isEmpty_map, Option.isNone_map]

/-- **Kinds.** The contraction of a graph whose components are of the deterministic kinds of
[II, Def 2.7 (i)] with labels in `[4, N]` has the same property. -/
theorem Contract.all_isDetKind {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) (N : ℕ) (h : Γ.comps.all (Comp.isDetKind N) = true) :
    (Contract.graph Γ i j a₀).comps.all (Comp.isDetKind N) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := (Contract.mem_graph_comps Γ i j a₀ c').1 hc'
  rw [Contract.isDetKind_map]
  exact h c (List.mem_of_mem_eraseIdx hc)

/-! ## The graph `s_{xy} s_{xy}` and diagonal graphs -/

/-- The graph `s_{xy} s_{xy}` (external atoms `x = 0`, `y = 1`, no internal atom). -/
def G13.ssGraph : Graph 2 0 :=
  ⟨[mkC (.waved .s) (.inl 0) (.inl 1), mkC (.waved .s) (.inl 0) (.inl 1)], 1⟩

/-- A diagonal graph ([I, Def 2.13 (i)]): it has a dotted edge, and every dotted edge joins the
external atoms `x = 0` and `y = 1`. -/
def G13.IsDiag {n : ℕ} (Γ : Graph 2 n) : Prop :=
  (∃ c ∈ Γ.comps, c.kind = .dot) ∧
    ∀ c ∈ Γ.comps, c.kind = .dot →
      (c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0)

instance G13.instDecidableIsDiag {n : ℕ} (Γ : Graph 2 n) : Decidable (G13.IsDiag Γ) := by
  unfold G13.IsDiag; infer_instance

end RBM8D.Graphs
