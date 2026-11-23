module

public import RBM8D.TExp.Defs

@[expose] public section

/-!
# `t`-variables and their substitution

The `t`-variables of [II, (4.14)], the substitution of a graph for a `t`-variable at the atoms
`x, y₁, y₂` (`Graph.glue`, [II, §4.3]), the right side of [II, (4.15)] (`TRec.tSubst`) and the
substitution of a formal sum (`Graph.globalSubst`); the scaling order and the value of a
substituted graph, and [II, (4.15)] as a value identity.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The graph with the two ends of every component exchanged (every matrix index pair
transposed). -/
def Graph.swapEnds {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map fun c => { c with x := c.y, y := c.x }, Γ.coeff⟩

/-- The `t`-variable `t_{x,y₁y₂} = |m|² ∑_α s_{xα} G_{αy₁} Ḡ_{αy₂} 1_{α ≠ y₁} 1_{α ≠ y₂}` of
[II, (4.14)]: external atoms `x = 0`, `y₁ = 1`, `y₂ = 2`, internal atom `α`. -/
def tVarGraph : Graph 3 1 :=
  ⟨[mkC (.waved .s) (.inl 0) (.inr 0), mkC (.G .plus) (.inr 0) (.inl 1),
    mkC (.G .minus) (.inr 0) (.inl 2), mkC .xdot (.inr 0) (.inl 1), mkC .xdot (.inr 0) (.inl 2)],
    cm * cmb⟩

/-- The `t`-variable `t_{x,y₁y₂}` (`tr = false`) or `t_{y₁y₂,x}` (`tr = true`) of [II, (4.14)]. -/
def tVar (tr : Bool) : Graph 3 1 := if tr then tVarGraph.swapEnds else tVarGraph

/-- The image of an atom of a graph `𝒢` with external atoms `⊗, ⊕, ⊖` substituted into a graph
with the atoms `x, y₁, y₂`: the external atoms go to `x, y₁, y₂`, the internal atoms to new
internal atoms. -/
def glueAtom {k n n' : ℕ} (x y₁ y₂ : Atom k n) : Atom 3 n' → Atom k (n + n')
  | .inl i => liftA n' (![x, y₁, y₂] i)
  | .inr j => newA j

/-- The graph `H` times the graph `𝒢_{x,y₁y₂}` ([II, §4.3]): the components of `H` and those of
`𝒢` with `⊗, ⊕, ⊖` replaced by `x, y₁, y₂`; the internal atoms of `𝒢` are new atoms. For
`𝒢 = tVar tr` it is a graph with the `t`-variable at the last atom `α`; for a graph `𝒢` of the
expansion of the `t`-variable it is the result of the substitution. -/
def Graph.glue {k n n' : ℕ} (H : Graph k n) (x y₁ y₂ : Atom k n) (𝒢 : Graph 3 n') :
    Graph k (n + n') :=
  ⟨liftCs n' H.comps ++ 𝒢.comps.map (Comp.map (glueAtom x y₁ y₂)), H.coeff * 𝒢.coeff⟩

/-- The formal sum `E` substituted into `H` at `x, y₁, y₂`. -/
def Graph.globalSubst {k n : ℕ} (H : Graph k n) (x y₁ y₂ : Atom k n) (E : Expansion 3) :
    Expansion k :=
  E.map fun g => ⟨n + g.1, H.glue x y₁ y₂ g.2⟩

/-- The three recollision terms of [II, (4.15)]: `-|m|² ∑_α s_{xα} G_{αy₁} Ḡ_{αy₂}` times
`1_{α = y₁} 1_{α ≠ y₂}`, `1_{α ≠ y₁} 1_{α = y₂}`, `1_{α = y₁} 1_{α = y₂}` (the `O_dot` terms of
`T_{x,y₁y₂}` other than the first one, with the opposite sign). -/
def tVarCorr : Expansion 3 := Expansion.smul (-1) ((oDot tGraph).drop 1)

/-- The right side of [II, (4.15)] for the `T`-expansion `𝒯` of order `n`: the right side of
[II, (3.1)] and the three recollision terms. -/
def TRec.tSubst (n : ℕ) (𝒯 : TRec) : Expansion 3 := 𝒯.rhs n ++ tVarCorr

/-! ## Helper lemmas -/

section Helpers

private theorem valR_append {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (E F : Expansion k)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    (E ++ F).valR PF D e ω = E.valR PF D e ω + F.valR PF D e ω := by
  simp [Expansion.valR, List.map_append, List.sum_append]

private theorem valR_cons {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Σ n : ℕ, Graph k n) (E : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) :
    Expansion.valR (g :: E) PF D e ω = g.2.valR PF D e ω + Expansion.valR E PF D e ω := by
  simp [Expansion.valR]

/-- Multiplying every coefficient of a formal sum by `c` multiplies its value by the value of `c`. -/
private theorem valR_smul {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (c : Coeff)
    (E : Expansion k) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    (E.smul c).valR PF D e ω = c.eval (D ω).m * E.valR PF D e ω := by
  induction E with
  | nil => simp [Expansion.smul, Expansion.valR]
  | cons g E ih =>
    simp only [Expansion.smul, Expansion.valR, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    simp only [Graph.smul, Graph.valR, Graph.termR, Coeff.eval, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Graph.labels]
    ring

/-- The value of a component after a change of atoms is its value at the composite labelling. -/
private theorem comp_val_map {k n k' n' : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (f : Atom k n → Atom k' n') (σ : Atom k' n' → ι) (c : Comp (Atom k n)) :
    Comp.val D σ (Comp.map f c) = Comp.val D (σ ∘ f) c := by
  have h : (c.minor.map f).map σ = c.minor.map (σ ∘ f) := List.map_map ..
  simp only [Comp.val, Comp.map, h]
  rfl

private theorem map_val_map {k n k' n' : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (f : Atom k n → Atom k' n') (σ : Atom k' n' → ι) (cs : List (Comp (Atom k n))) :
    (cs.map (Comp.map f)).map (Comp.val D σ) = cs.map (Comp.val D (σ ∘ f)) := by
  rw [List.map_map]
  exact List.map_congr_left fun c _ => comp_val_map _ _ _ _

/-- A list with at most one distinct entry: its image under a map has the image of the entry as
its only distinct entry. -/
private theorem map_dedup_of_length_le_one {α β : Type} [DecidableEq α] [DecidableEq β]
    (φ : α → β) (L : List α) (h : L.dedup.length ≤ 1) : (L.map φ).dedup = L.dedup.map φ := by
  rcases hL : L.dedup with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rw [List.dedup_eq_nil] at hL
    subst hL
    rfl
  · have hmem : ∀ x ∈ L, x = a := fun x hx => by
      have : x ∈ L.dedup := List.mem_dedup.2 hx
      rw [hL] at this
      simpa using this
    have hne : L ≠ [] := fun h0 => by
      subst h0
      simp at hL
    have hrep : L = List.replicate L.length a := List.eq_replicate_iff.2 ⟨rfl, hmem⟩
    have hlen : L.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.1 h0)
    rw [hrep, List.map_replicate, List.replicate_dedup hlen]
    rfl
  · rw [hL] at h
    simp at h

private theorem eq_of_mem_of_dedup_length_le_one {α : Type} [DecidableEq α] {L : List α}
    (h : L.dedup.length ≤ 1) {a b : α} (ha : a ∈ L) (hb : b ∈ L) : a = b := by
  have ha' := List.mem_dedup.2 ha
  have hb' := List.mem_dedup.2 hb
  rcases hL : L.dedup with _ | ⟨c, _ | ⟨d, l⟩⟩
  · rw [hL] at ha'
    simp at ha'
  · rw [hL] at ha' hb'
    exact (List.mem_singleton.1 ha').trans (List.mem_singleton.1 hb').symm
  · rw [hL] at h
    simp at h

private theorem elim_append_comp_liftA {k n n' : ℕ} {ι : Type} (e : Fin k → ι)
    (s : Fin n → ι) (t : Fin n' → ι) :
    Sum.elim e (Fin.append s t) ∘ liftA n' = Sum.elim e s := by
  funext a
  rcases a with a | a <;> simp [liftA]

/-- The labelling of the atoms of `H.glue x y₁ y₂ 𝒢` by `(e, s, t)` is, on the atoms of `𝒢`, the
labelling by the values at `x, y₁, y₂` and by `t`. -/
private theorem elim_append_comp_glueAtom {k n n' : ℕ} {ι : Type} (x y₁ y₂ : Atom k n)
    (e : Fin k → ι) (s : Fin n → ι) (t : Fin n' → ι) :
    Sum.elim e (Fin.append s t) ∘ glueAtom x y₁ y₂ =
      Sum.elim ![Sum.elim e s x, Sum.elim e s y₁, Sum.elim e s y₂] t := by
  funext a
  rcases a with a | a
  · have h := congrFun (elim_append_comp_liftA (n' := n') e s t)
    fin_cases a
    · exact h x
    · exact h y₁
    · exact h y₂
  · simp [glueAtom, newA]

/-- The term of the substituted graph at the labelling `(e, s, t)` of its atoms is the term of `H`
at `(e, s)` times the term of `𝒢` at the labelling by the values at `x, y₁, y₂` and `t`; `H` has no
labels and `𝒢` at most one. -/
private theorem termR_glue {k n n' : ℕ} (H : Graph k n) (x y₁ y₂ : Atom k n) (𝒢 : Graph 3 n')
    {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) (hH : H.LabelFree) (h𝒢 : 𝒢.labels.length ≤ 1)
    (s : Fin n → ι) (t : Fin n' → ι) :
    (H.glue x y₁ y₂ 𝒢).termR PF D (Sum.elim e (Fin.append s t)) ω =
      H.term (D ω) (Sum.elim e s) *
        𝒢.termR PF D (Sum.elim ![Sum.elim e s x, Sum.elim e s y₁, Sum.elim e s y₂] t) ω := by
  set σ' := Sum.elim e (Fin.append s t) with hσ'
  set σ'' := Sum.elim ![Sum.elim e s x, Sum.elim e s y₁, Sum.elim e s y₂] t with hσ''
  have h1 : σ' ∘ liftA n' = Sum.elim e s := elim_append_comp_liftA e s t
  have h2 : σ' ∘ glueAtom x y₁ y₂ = σ'' := elim_append_comp_glueAtom x y₁ y₂ e s t
  have hHn : ∀ c ∈ H.comps, c.label = none := hH
  have hHl : ∀ c ∈ liftCs n' H.comps, c.label = none := by
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, hHn c0 hc0]
  -- the labels of the substituted graph
  have hL : (H.glue x y₁ y₂ 𝒢).comps.filterMap Comp.label =
      (𝒢.comps.filterMap Comp.label).map (Prod.map id (glueAtom x y₁ y₂)) := by
    simp only [Graph.glue, List.filterMap_append, List.filterMap_map]
    have : (liftCs n' H.comps).filterMap Comp.label = [] :=
      List.filterMap_eq_nil_iff.2 fun c hc => by simp [hHl c hc]
    rw [this, List.nil_append, List.map_filterMap]
    rfl
  have hlab : (H.glue x y₁ y₂ 𝒢).labels = 𝒢.labels.map (Prod.map id (glueAtom x y₁ y₂)) := by
    simp only [Graph.labels]
    rw [hL, map_dedup_of_length_le_one _ _ h𝒢]
  -- the unlabelled factors
  have hU : ((H.glue x y₁ y₂ 𝒢).comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ') =
      H.comps.map (Comp.val (D ω) (Sum.elim e s)) ++
        (𝒢.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ'') := by
    simp only [Graph.glue, List.filter_append, List.map_append]
    have hf1 : (liftCs n' H.comps).filter (fun c => c.label.isNone) = liftCs n' H.comps :=
      List.filter_eq_self.2 fun c hc => by simp [hHl c hc]
    have hf2 : (𝒢.comps.map (Comp.map (glueAtom x y₁ y₂))).filter (fun c => c.label.isNone) =
        (𝒢.comps.filter fun c => c.label.isNone).map (Comp.map (glueAtom x y₁ y₂)) := by
      rw [List.filter_map]
      congr 1
      simp [Function.comp_def, Comp.map]
    rw [hf1, hf2, liftCs, map_val_map, map_val_map, h1, h2]
  -- the labelled factors
  have hP : ((H.glue x y₁ y₂ 𝒢).labels.map fun ℓ => PF.op ℓ.1 (σ' ℓ.2)
      (fun ω' => (((H.glue x y₁ y₂ 𝒢).comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ')).prod) ω) =
      𝒢.labels.map fun ℓ => PF.op ℓ.1 (σ'' ℓ.2)
        (fun ω' => ((𝒢.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (D ω') σ'')).prod) ω := by
    rw [hlab, List.map_map]
    refine List.map_congr_left fun ℓ hℓ => ?_
    have hℓ' : ℓ ∈ 𝒢.comps.filterMap Comp.label := List.mem_dedup.1 hℓ
    simp only [Function.comp_apply, Prod.map_snd]
    have hfilt : ((H.glue x y₁ y₂ 𝒢).comps.filter fun c =>
        decide (c.label = some (Prod.map id (glueAtom x y₁ y₂) ℓ))) =
        (𝒢.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.map (glueAtom x y₁ y₂)) := by
      simp only [Graph.glue, List.filter_append]
      have hf1 : (liftCs n' H.comps).filter (fun c =>
          decide (c.label = some (Prod.map id (glueAtom x y₁ y₂) ℓ))) = [] :=
        List.filter_eq_nil_iff.2 fun c hc => by simp [hHl c hc]
      rw [hf1, List.nil_append, List.filter_map]
      congr 1
      refine List.filter_congr fun c hc => ?_
      simp only [Function.comp_apply, Comp.map]
      by_cases hcl : c.label = some ℓ
      · simp [hcl]
      · have hne : ¬ Option.map (Prod.map id (glueAtom x y₁ y₂)) c.label =
            some (Prod.map id (glueAtom x y₁ y₂) ℓ) := by
          intro hcontra
          obtain ⟨a, ha, hφ⟩ := Option.map_eq_some_iff.1 hcontra
          have hmem : a ∈ 𝒢.comps.filterMap Comp.label := List.mem_filterMap.2 ⟨c, hc, ha⟩
          have := eq_of_mem_of_dedup_length_le_one h𝒢 hmem hℓ'
          subst this
          exact hcl ha
        simp [hcl, hne]
    rw [hfilt]
    simp only [map_val_map, h2]
    have h3 := congrFun h2 ℓ.2
    simp only [Function.comp_apply] at h3
    rw [h3]
    rfl
  unfold Graph.termR Graph.term
  rw [hU, hP, List.prod_append]
  have hc : (H.glue x y₁ y₂ 𝒢).coeff.eval (D ω).m =
      H.coeff.eval (D ω).m * 𝒢.coeff.eval (D ω).m := by
    simp [Graph.glue, Coeff.eval]
  rw [hc]
  ring

end Helpers

/-- **The scaling order of a substituted graph** ([II, (2.5)]): the scaling order of `H` with the
graph `𝒢` substituted at `x, y₁, y₂` is the sum of the scaling orders of `H` and `𝒢`. -/
theorem glue_ord :
  ∀ (k n n' : ℕ) (H : Graph k n) (x y₁ y₂ : Atom k n) (𝒢 : Graph 3 n'),
    (H.glue x y₁ y₂ 𝒢).ord = H.ord + 𝒢.ord := by
  intro k n n' H x y₁ y₂ 𝒢
  simp only [Graph.ord, Graph.glue, liftCs, List.map_append, List.map_map, List.sum_append,
    Comp.map, Function.comp_def, Nat.cast_add]
  ring

/-- **The value of a substituted graph** ([II, §4.3]): for `H` without labels and `𝒢` with at most
one label, the value of `H` with `𝒢` substituted at `x, y₁, y₂` is the sum over the internal
atoms of `H` of the term of `H` times the value of `𝒢` at the images of `x, y₁, y₂`. -/
theorem glue_value :
  ∀ (k n n' : ℕ) (H : Graph k n) (x y₁ y₂ : Atom k n) (𝒢 : Graph 3 n') (Ω ι : Type) [Fintype ι]
    [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω),
    H.LabelFree → 𝒢.labels.length ≤ 1 →
    (H.glue x y₁ y₂ 𝒢).valR PF D e ω =
      ∑ s : Fin n → ι, H.term (D ω) (Sum.elim e s) *
        𝒢.valR PF D ![Sum.elim e s x, Sum.elim e s y₁, Sum.elim e s y₂] ω := by
  intro k n n' H x y₁ y₂ 𝒢 Ω ι _ _ PF D e ω hH h𝒢
  simp only [Graph.valR]
  rw [← (Fin.appendEquiv n n').sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact termR_glue H x y₁ y₂ 𝒢 PF D e ω hH h𝒢 s t

/-- **[II, (4.15)]** as a value identity: for an `n`-th order `T`-expansion `𝒯` over `Sig`, the
value of the `t`-variable is the value of the right side of [II, (3.1)] plus the three recollision
terms. -/
theorem tSubst_value :
  ∀ (Sig : ℕ → Expansion 2) (n : ℕ) (𝒯 : TRec), 𝒯.Identity Sig n →
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
      modelAdm Ω ι PF D → (∀ ω, SigConsistent Sig (n + 1) (D ω)) → ∀ e : Fin 3 → ι,
        (𝒯.tSubst n).valR PF D e = tVarGraph.valR PF D e := by
  intro Sig n 𝒯 hid Ω ι _ _ PF D hA hS e
  funext ω
  have h1 := hid Ω ι PF D hA hS e ω
  have h2 := congrFun (oDot_value 3 1 Ω ι PF D trivial tGraph e) ω
  -- the first term of `O_dot` of `T_{x,y₁y₂}` is the `t`-variable
  have hhead : (oDot tGraph).take 1 =
      [⟨1, ⟨tVarGraph.comps, (-1 : Coeff) ^ 0 * (cm * cmb)⟩⟩] := by
    rfl
  have hsplit : oDot tGraph = [⟨1, ⟨tVarGraph.comps, (-1 : Coeff) ^ 0 * (cm * cmb)⟩⟩] ++
      (oDot tGraph).drop 1 := by
    rw [← hhead, List.take_append_drop]
  rw [hsplit, valR_append] at h2
  have h3 : Expansion.valR [⟨1, ⟨tVarGraph.comps, (-1 : Coeff) ^ 0 * (cm * cmb)⟩⟩] PF D e ω =
      tVarGraph.valR PF D e ω := by
    simp [Expansion.valR, Graph.valR, Graph.termR, Graph.labels, tVarGraph]
  have h4 : tVarCorr.valR PF D e ω = -Expansion.valR ((oDot tGraph).drop 1) PF D e ω := by
    rw [tVarCorr, valR_smul]
    simp [Coeff.eval]
  change (𝒯.rhs n ++ tVarCorr).valR PF D e ω = _
  rw [valR_append, h1, h4]
  rw [h3] at h2
  linear_combination (-1 : ℂ) * h2

/-- The value of the substitution of a formal sum with at most one label per graph into a graph
without labels is the sum over the internal atoms of the term of the host times the value of the
formal sum at the images of `x, y₁, y₂`. -/
private theorem globalSubst_valR {k n : ℕ} (H : Graph k n) (x y₁ y₂ : Atom k n)
    {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) (hH : H.LabelFree) :
    ∀ E : Expansion 3, (∀ g ∈ E, g.2.labels.length ≤ 1) →
      (H.globalSubst x y₁ y₂ E).valR PF D e ω =
        ∑ s : Fin n → ι, H.term (D ω) (Sum.elim e s) *
          E.valR PF D ![Sum.elim e s x, Sum.elim e s y₁, Sum.elim e s y₂] ω := by
  intro E
  induction E with
  | nil =>
    intro _
    simp [Graph.globalSubst, Expansion.valR]
  | cons g E ih =>
    intro hE
    have hg := hE g (List.mem_cons_self ..)
    have ih' := ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    have h1 : (H.globalSubst x y₁ y₂ (g :: E)).valR PF D e ω =
        (H.glue x y₁ y₂ g.2).valR PF D e ω + (H.globalSubst x y₁ y₂ E).valR PF D e ω := by
      simp [Graph.globalSubst, Expansion.valR]
    rw [h1, ih', glue_value k n g.1 H x y₁ y₂ g.2 Ω ι PF D e ω hH hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [valR_cons, mul_add]

/-- **The value of a substituted formal sum**: if `E` (graphs with at most one label) has the
value of `𝒢` at every labelling of its external atoms, then `E` substituted into `H` (without
labels) at `x, y₁, y₂` has the value of `𝒢` substituted into `H`. -/
theorem globalSubst_value :
  ∀ (k n n' : ℕ) (H : Graph k n) (x y₁ y₂ : Atom k n) (𝒢 : Graph 3 n') (E : Expansion 3)
    (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
    H.LabelFree → 𝒢.labels.length ≤ 1 → (∀ g ∈ E, g.2.labels.length ≤ 1) →
    (∀ e' : Fin 3 → ι, E.valR PF D e' = 𝒢.valR PF D e') →
    ∀ e : Fin k → ι, (H.globalSubst x y₁ y₂ E).valR PF D e = (H.glue x y₁ y₂ 𝒢).valR PF D e := by
  intro k n n' H x y₁ y₂ 𝒢 E Ω ι _ _ PF D hH h𝒢 hE hEv e
  funext ω
  rw [globalSubst_valR H x y₁ y₂ PF D e ω hH E hE,
    glue_value k n n' H x y₁ y₂ 𝒢 Ω ι PF D e ω hH h𝒢]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hEv]

section Instances

end Instances

end RBM8D.Graphs
