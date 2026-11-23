module

public import RBM8D.Graph.Local.Dot
public import RBM8D.Graph.Local.Weight

@[expose] public section

/-!
# The first step of the `Q`-expansions

The resolvent identities [II, (4.17), (4.20)] and the Taylor expansion [II, (4.21)] of the weight
`(G_{xx})⁻¹` as operators on graphs, and their value preservation under the model relations.
Components of a label group that the model relations do not make admissible under `P_u`, `Q_u`
are left untouched ([II, §4.4]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- A component that the model relations make admissible under `P_u` and `Q_u`: a solid edge, a
weight or a light weight (any minor), or `(G_{xx})⁻¹`, `W_D` without minor. -/
def Comp.isGoodKind {V : Type*} (c : Comp V) : Bool :=
  match c.kind with
  | .G _ | .weight _ | .light _ => true
  | .inv _ | .wD _ _ => c.minor.isEmpty
  | _ => false

/-- Every component of `Γ` with the label `ℓ` is of a kind of `Comp.isGoodKind`. -/
def Graph.GoodGroup {k n : ℕ} (Γ : Graph k n) (ℓ : PQ × Atom k n) : Bool :=
  Γ.comps.all fun c => !decide (c.label = some ℓ) || c.isGoodKind

/-- The resolvent identity [II, (4.17)] at the solid edge with index `i`:
`G_{ab} = G^{(x)}_{ab} + G_{ax} G_{xb} (G_{xx})⁻¹` (its complex conjugate for `Ḡ_{ab}`), the label
of the edge kept on the new factors; the identity if that component is not a solid edge without
minor, or if its label is also carried by a component not of a kind of `Comp.isGoodKind`. -/
def oSchurT {k n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) : TExpansion k n :=
  match Γ.comps[i]? with
  | some c =>
    match c.kind with
    | .G ch =>
      if c.minor.isEmpty && c.label.all Γ.GoodGroup then
        let rest := Γ.comps.eraseIdx i
        [⟨n, ⟨rest ++ [{ c with minor := [x] }], Γ.coeff⟩, id⟩,
          ⟨n, ⟨rest ++ [{ solidC ch c.x x with label := c.label },
            { solidC ch x c.y with label := c.label },
            { mkC (.inv ch) x x with label := c.label }], Γ.coeff⟩, id⟩]
      else [Tracked.self Γ]
    | _ => [Tracked.self Γ]
  | none => [Tracked.self Γ]

/-- [II, (4.17)] as an operator. -/
def oSchur {k n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) : Expansion k :=
  (oSchurT x i Γ).forget

/-- The resolvent identity [II, (4.20)] at the component with index `i`:
`G^{(x)}_{ab} = G_{ab} - G_{ax} G_{xb} (G_{xx})⁻¹`; the identity if that component is not a solid
edge with minor `{x}`, or if its label is also carried by a component not of a kind of
`Comp.isGoodKind`. -/
def oSchurRevT {k n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) : TExpansion k n :=
  match Γ.comps[i]? with
  | some c =>
    match c.kind with
    | .G ch =>
      if c.minor = [x] && c.label.all Γ.GoodGroup then
        let rest := Γ.comps.eraseIdx i
        [⟨n, ⟨rest ++ [{ c with minor := [] }], Γ.coeff⟩, id⟩,
          ⟨n, ⟨rest ++ [{ solidC ch c.x x with label := c.label },
            { solidC ch x c.y with label := c.label },
            { mkC (.inv ch) x x with label := c.label }], -Γ.coeff⟩, id⟩]
      else [Tracked.self Γ]
    | _ => [Tracked.self Γ]
  | none => [Tracked.self Γ]

/-- [II, (4.20)] as an operator. -/
def oSchurRev {k n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) : Expansion k :=
  (oSchurRevT x i Γ).forget

/-- The expansion [II, (4.21)] of the weight `(G_{xx})⁻¹` with index `i`:
`(G_{xx})⁻¹ = ∑_{j ≤ D} (-1)^j m^{-(j+1)} (G_{xx} - m)^j + W^{(x)}_D` with
`W^{(x)}_D = (G_{xx})⁻¹ - m⁻¹ ∑_{j ≤ D} (-(G_{xx} - m)/m)^j` (and its complex conjugate); the
identity if that component is not a weight `(G_{xx})⁻¹`, or if it carries a label that no other
component carries or that a component not of a kind of `Comp.isGoodKind` carries. -/
def oTaylorT {k n : ℕ} (D : ℕ) (i : ℕ) (Γ : Graph k n) : TExpansion k n :=
  match Γ.comps[i]? with
  | some c =>
    match c.kind with
    | .inv ch =>
      let rest := Γ.comps.eraseIdx i
      if c.label.all (fun ℓ => Γ.GoodGroup ℓ &&
          rest.any fun c' => decide (c'.label = some ℓ)) then
        (List.range (D + 1)).map (fun j =>
          ⟨n, ⟨rest ++ List.replicate j { c with kind := .light ch, y := c.x },
            (-1 : Coeff) ^ j * mInvOf ch ^ (j + 1) * Γ.coeff⟩, id⟩) ++
          [⟨n, ⟨rest ++ [{ c with kind := .wD ch D, y := c.x }], Γ.coeff⟩, id⟩]
      else [Tracked.self Γ]
    | _ => [Tracked.self Γ]
  | none => [Tracked.self Γ]

/-- [II, (4.21)] as an operator. -/
def oTaylor {k n : ℕ} (D : ℕ) (i : ℕ) (Γ : Graph k n) : Expansion k := (oTaylorT D i Γ).forget

/-! ## Values of components -/

section Values

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι]

/-- The charge as a ring homomorphism: the identity or complex conjugation. -/
private def Charge.hom : Charge → ℂ →+* ℂ
  | .plus => RingHom.id ℂ
  | .minus => starRingEnd ℂ

private theorem Charge.apply_eq (ch : Charge) (z : ℂ) : ch.apply z = ch.hom z := by
  cases ch <;> rfl

private theorem Charge.hom_mInv (ch : Charge) (m : ℂ) :
    Coeff.eval m (mInvOf ch) = ch.hom (m⁻¹) := by
  cases ch <;> simp [mInvOf, Coeff.eval, CVar.eval, Charge.hom]

private theorem Comp.val_label {V : Type*} (d : Data ι) (σ : V → ι) (c : Comp V)
    (l : Option (PQ × V)) : Comp.val d σ { c with label := l } = Comp.val d σ c := rfl

end Values

/-! ## Good factors -/

section Good

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem good_pow' (A : ModelAdm Ω ι PF D) {f : Ω → ℂ} (hf : A.Good f) (n : ℕ) :
    A.Good fun ω => f ω ^ n := by
  induction n with
  | zero => simpa using A.laws.good_const 1
  | succ n ih =>
    have h := A.laws.good_mul _ _ ih hf
    convert h using 1
    funext ω
    simp [pow_succ]

private theorem good_sum_range (A : ModelAdm Ω ι PF D) (f : ℕ → Ω → ℂ)
    (hf : ∀ j, A.Good (f j)) (n : ℕ) : A.Good fun ω => ∑ j ∈ Finset.range n, f j ω := by
  induction n with
  | zero => simpa using A.laws.good_const 0
  | succ n ih =>
    have h := A.laws.good_add _ _ ih (hf n)
    convert h using 1
    funext ω
    simp [Finset.sum_range_succ]

private theorem good_charge (A : ModelAdm Ω ι PF D) (ch : Charge) {f : Ω → ℂ} (hf : A.Good f) :
    A.Good fun ω => ch.apply (f ω) := by
  cases ch
  · exact hf
  · exact A.good_star f hf

private theorem good_val (A : ModelAdm Ω ι PF D) {V : Type*} (σ : V → ι) (c : Comp V)
    (hc : c.isGoodKind = true) : A.Good fun ω => Comp.val (D ω) σ c := by
  obtain ⟨κ, x, y, T, l⟩ := c
  cases κ with
  | G ch => exact good_charge A ch (A.good_entry _ _ _)
  | weight ch => exact good_charge A ch (A.good_entry _ _ _)
  | light ch =>
    have h := A.laws.good_add _ _ (A.good_entry ((T.map σ).toFinset) (σ x) (σ x))
      (A.laws.good_const (-(msc A.z)))
    have key : (fun ω => Comp.val (D ω) σ ⟨.light ch, x, y, T, l⟩) =
        fun ω => ch.apply ((((fun ω => (D ω).Gm ((T.map σ).toFinset) (σ x) (σ x)) +
          fun _ => -(msc A.z)) : Ω → ℂ) ω) := by
      funext ω
      simp [Comp.val, A.data_m ω, sub_eq_add_neg]
    rw [key]
    exact good_charge A ch h
  | inv ch =>
    simp only [Comp.isGoodKind, List.isEmpty_iff] at hc
    subst hc
    have h := good_charge A ch (A.good_inv (σ x))
    convert h using 2 with ω
    simp [Comp.val]
  | wD ch d =>
    simp only [Comp.isGoodKind, List.isEmpty_iff] at hc
    subst hc
    have hu : A.Good fun ω => (D ω).Gm ∅ (σ x) (σ x) := A.good_entry _ _ _
    have hS : A.Good fun ω => ∑ j ∈ Finset.range (d + 1),
        ((-(msc A.z)⁻¹) * (D ω).Gm ∅ (σ x) (σ x) + (msc A.z * (msc A.z)⁻¹)) ^ j := by
      refine good_sum_range A (fun j ω => ((-(msc A.z)⁻¹) * (D ω).Gm ∅ (σ x) (σ x) +
        (msc A.z * (msc A.z)⁻¹)) ^ j) (fun j => good_pow' A ?_ j) _
      have := A.laws.good_add _ _ (A.laws.good_mul _ _ (A.laws.good_const (-(msc A.z)⁻¹)) hu)
        (A.laws.good_const (msc A.z * (msc A.z)⁻¹))
      exact this
    have h2 := A.laws.good_add _ _ (A.good_inv (σ x))
      (A.laws.good_mul _ _ (A.laws.good_const (-(msc A.z)⁻¹)) hS)
    have key : (fun ω => Comp.val (D ω) σ ⟨.wD ch d, x, y, [], l⟩) =
        fun ω => ch.apply ((((fun ω => ((D ω).Gm ∅ (σ x) (σ x))⁻¹) +
          ((fun _ => -(msc A.z)⁻¹) * fun ω => ∑ j ∈ Finset.range (d + 1),
            ((-(msc A.z)⁻¹) * (D ω).Gm ∅ (σ x) (σ x) +
              (msc A.z * (msc A.z)⁻¹)) ^ j)) : Ω → ℂ) ω) := by
      funext ω
      simp only [Comp.val, A.data_m ω, List.map_nil, List.toFinset_nil, Pi.add_apply, Pi.mul_apply]
      congr 1
      rw [neg_mul, ← sub_eq_add_neg]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [div_eq_mul_inv]
      ring
    rw [key]
    exact good_charge A ch h2
  | waved w => simp [Comp.isGoodKind] at hc
  | theta o => simp [Comp.isGoodKind] at hc
  | thetaErr n d => simp [Comp.isGoodKind] at hc
  | ghost => simp [Comp.isGoodKind] at hc
  | aux j r b => simp [Comp.isGoodKind] at hc
  | dot => simp [Comp.isGoodKind] at hc
  | xdot => simp [Comp.isGoodKind] at hc

end Good

/-! ## Linearity of the label operators -/

section Linear

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem P_zero (A : ModelAdm Ω ι PF D) (u : ι) : PF.P u (fun _ => 0) = fun _ => 0 := by
  have h := A.laws.smul u 0 (fun _ => (0 : ℂ)) (A.laws.good_const 0)
  have e : ((0 : ℂ) • (fun _ : Ω => (0 : ℂ))) = fun _ => 0 := by funext ω; simp
  rw [e] at h
  rw [h]
  funext ω
  simp

private theorem op_add (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) {f g : Ω → ℂ} (hf : A.Good f)
    (hg : A.Good g) : PF.op pq u (f + g) = PF.op pq u f + PF.op pq u g := by
  cases pq
  · exact A.laws.add u f g hf hg
  · simp only [PFamily.op]
    rw [A.laws.add u f g hf hg]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

private theorem op_smul (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) (a : ℂ) {f : Ω → ℂ}
    (hf : A.Good f) : PF.op pq u (a • f) = a • PF.op pq u f := by
  cases pq
  · exact A.laws.smul u a f hf
  · simp only [PFamily.op]
    rw [A.laws.smul u a f hf]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

private theorem op_zero (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) :
    PF.op pq u (fun _ => 0) = fun _ => 0 := by
  cases pq
  · exact P_zero A u
  · simp only [PFamily.op]
    rw [P_zero A u]
    funext ω
    simp

private theorem good_lincomb (A : ModelAdm Ω ι PF D) :
    ∀ l : List (ℂ × (Ω → ℂ)), (∀ p ∈ l, A.Good p.2) →
      A.Good fun ω => (l.map fun p => p.1 * p.2 ω).sum := by
  intro l
  induction l with
  | nil => intro _; simpa using A.laws.good_const 0
  | cons p l ih =>
    intro h
    have h1 := A.laws.good_add _ _
      (A.laws.good_mul _ _ (A.laws.good_const p.1) (h p (List.mem_cons_self ..)))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
    convert h1 using 1
    funext ω
    simp

/-- The label operators are linear on good functions. -/
private theorem op_lincomb (A : ModelAdm Ω ι PF D) (pq : PQ) (u : ι) :
    ∀ l : List (ℂ × (Ω → ℂ)), (∀ p ∈ l, A.Good p.2) →
      PF.op pq u (fun ω => (l.map fun p => p.1 * p.2 ω).sum) =
        fun ω => (l.map fun p => p.1 * PF.op pq u p.2 ω).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    simpa using op_zero A pq u
  | cons p l ih =>
    intro h
    have hp := h p (List.mem_cons_self ..)
    have hl := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have e : (fun ω => ((p :: l).map fun p => p.1 * p.2 ω).sum) =
        (p.1 • p.2) + fun ω => (l.map fun p => p.1 * p.2 ω).sum := by
      funext ω
      simp
    have hs : A.Good (p.1 • p.2) := by
      have := A.laws.good_mul _ _ (A.laws.good_const p.1) hp
      convert this using 1
    rw [e, op_add A pq u hs (good_lincomb A l hl), op_smul A pq u p.1 hp, ih hl]
    funext ω
    simp

end Linear

/-! ## Replacing one component by a list -/

section Replace

variable {k n : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem termR_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') (co : Coeff)
    (σ : Atom k n → ι) (ω : Ω) :
    Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω = Graph.termR (⟨L', co⟩ : Graph k n) PF D σ ω := by
  have h1 : ((L.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod =
      ((L'.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod :=
    ((h.filter _).map _).prod_eq
  have h2 : (L.filterMap Comp.label).dedup.Perm (L'.filterMap Comp.label).dedup :=
    (h.filterMap _).dedup
  have h3 : ∀ ℓ : PQ × Atom k n,
      (fun ω' => ((L.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) =
      (fun ω' => ((L'.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) :=
    fun ℓ => funext fun ω' => ((h.filter _).map _).prod_eq
  simp only [Graph.termR, Graph.labels, h3, h1]
  congr 1
  exact (h2.map _).prod_eq

private theorem filter_unl_of {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.label = none) :
    L.filter (fun c => c.label.isNone) = L :=
  List.filter_eq_self.2 fun c hc => by simp [h c hc]

private theorem filter_grp_of_none {L : List (Comp (Atom k n))} (h : ∀ c ∈ L, c.label = none)
    (ℓ : PQ × Atom k n) : L.filter (fun c => decide (c.label = some ℓ)) = [] :=
  List.filter_eq_nil_iff.2 fun c hc => by simp [h c hc]

private theorem filterMap_label_of_none {L : List (Comp (Atom k n))}
    (h : ∀ c ∈ L, c.label = none) : L.filterMap Comp.label = [] :=
  List.filterMap_eq_nil_iff.2 fun c hc => h c hc

private theorem termR_replace_none (σ : Atom k n → ι) (ω : Ω)
    (rest : List (Comp (Atom k n))) (c : Comp (Atom k n)) (hc : c.label = none) (coeff : Coeff)
    (outs : List (Coeff × List (Comp (Atom k n))))
    (hlab : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.label = none)
    (hval : Comp.val (D ω) σ c = (outs.map fun o => Coeff.eval (D ω).m o.1 *
      (o.2.map (Comp.val (D ω) σ)).prod).sum) :
    (outs.map fun o => Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω).sum =
      Graph.termR (⟨c :: rest, coeff⟩ : Graph k n) PF D σ ω := by
  set Fr := ((rest.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod with hFr
  set Lab := (((rest.filterMap Comp.label).dedup).map fun ℓ => PF.op ℓ.1 (σ ℓ.2)
    (fun ω' => ((rest.filter fun c => decide (c.label = some ℓ)).map
      (Comp.val (D ω') σ)).prod) ω).prod with hLab
  have hterm : ∀ o ∈ outs, Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω =
      (Coeff.eval (D ω).m coeff * Fr * Lab) *
        (Coeff.eval (D ω).m o.1 * (o.2.map (Comp.val (D ω) σ)).prod) := by
    intro o ho
    have h0 := hlab o ho
    simp only [Graph.termR, Graph.labels, List.filter_append, filter_unl_of h0,
      List.filterMap_append, filterMap_label_of_none h0, List.append_nil, filter_grp_of_none h0,
      List.map_append, List.prod_append, map_mul, Coeff.eval]
    rw [hFr, hLab]
    ring
  rw [List.map_congr_left hterm, List.sum_map_mul_left, ← hval]
  have hc1 : (c :: rest).filter (fun c => c.label.isNone) =
      c :: rest.filter (fun c => c.label.isNone) := List.filter_cons_of_pos (by simp [hc])
  have hc2 : ∀ ℓ : PQ × Atom k n, (c :: rest).filter (fun c => decide (c.label = some ℓ)) =
      rest.filter (fun c => decide (c.label = some ℓ)) :=
    fun ℓ => List.filter_cons_of_neg (by simp [hc])
  have hc3 : (c :: rest).filterMap Comp.label = rest.filterMap Comp.label := by
    simp [hc]
  simp only [Graph.termR, Graph.labels, hc1, hc2, hc3, List.map_cons, List.prod_cons]
  rw [← hFr, ← hLab]
  ring

/-- The product of the component values, as a function of the sample point. -/
private def Fn (D : Ω → Data ι) (σ : Atom k n → ι) (cs : List (Comp (Atom k n))) : Ω → ℂ :=
  fun ω => (cs.map (Comp.val (D ω) σ)).prod

private theorem Fn_append (σ : Atom k n → ι) (cs ds : List (Comp (Atom k n))) :
    Fn D σ (cs ++ ds) = Fn D σ cs * Fn D σ ds := by
  funext ω
  simp [Fn]

private theorem good_Fn (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) :
    ∀ cs : List (Comp (Atom k n)), (∀ c ∈ cs, c.isGoodKind = true) → A.Good (Fn D σ cs) := by
  intro cs
  induction cs with
  | nil =>
    intro _
    have := A.laws.good_const 1
    convert this using 1
    funext ω
    simp [Fn]
  | cons c cs ih =>
    intro h
    have := A.laws.good_mul _ _ (good_val A σ c (h c (List.mem_cons_self ..)))
      (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    convert this using 1
    funext ω
    simp [Fn]

private theorem mem_labs {L : List (Comp (Atom k n))} {a : PQ × Atom k n} :
    a ∈ (L.filterMap Comp.label).dedup ↔ ∃ c ∈ L, c.label = some a := by
  simp [List.mem_dedup, List.mem_filterMap]

private theorem labs_perm {L L' : List (Comp (Atom k n))}
    (h : ∀ a, (∃ c ∈ L, c.label = some a) ↔ ∃ c ∈ L', c.label = some a) :
    ((L.filterMap Comp.label).dedup).Perm ((L'.filterMap Comp.label).dedup) :=
  (List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)).2
    fun a => by rw [mem_labs, mem_labs]; exact h a

/-- The list without the label `ℓ`. -/
private def eraseL (l : List (PQ × Atom k n)) (ℓ : PQ × Atom k n) : List (PQ × Atom k n) :=
  l.filter fun ℓ' => decide (ℓ' ≠ ℓ)

private theorem prod_map_eraseL {l : List (PQ × Atom k n)} (hl : l.Nodup) {ℓ : PQ × Atom k n}
    (hℓ : ℓ ∈ l) (f : PQ × Atom k n → ℂ) :
    (l.map f).prod = f ℓ * ((eraseL l ℓ).map f).prod := by
  induction l with
  | nil => simp at hℓ
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    by_cases hal : a = ℓ
    · subst hal
      have : eraseL (a :: t) a = t := by
        simp only [eraseL, List.filter_cons]
        simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
        exact List.filter_eq_self.2 fun b hb => by
          simp only [decide_eq_true_eq]
          rintro rfl
          exact hl.1 hb
      rw [this]
      simp
    · have hℓt : ℓ ∈ t := by
        rcases List.mem_cons.1 hℓ with h | h
        · exact absurd h.symm hal
        · exact h
      have : eraseL (a :: t) ℓ = a :: eraseL t ℓ := by
        simp [eraseL, hal]
      rw [this, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih hl.2 hℓt]
      ring

private theorem termR_split (L : List (Comp (Atom k n))) (co : Coeff) (σ : Atom k n → ι)
    (ω : Ω) (ℓ : PQ × Atom k n) (hℓ : ∃ c ∈ L, c.label = some ℓ) :
    Graph.termR (⟨L, co⟩ : Graph k n) PF D σ ω =
      Coeff.eval (D ω).m co * ((L.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod *
        (PF.op ℓ.1 (σ ℓ.2) (Fn D σ (L.filter fun c => decide (c.label = some ℓ))) ω *
          ((eraseL ((L.filterMap Comp.label).dedup) ℓ).map fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
            (Fn D σ (L.filter fun c => decide (c.label = some ℓ'))) ω).prod) := by
  have hmem := mem_labs.2 hℓ
  simp only [Graph.termR, Graph.labels]
  rw [prod_map_eraseL (List.nodup_dedup _) hmem]
  rfl

private theorem others_eq {L L' : List (Comp (Atom k n))} (σ : Atom k n → ι) (ω : Ω)
    (ℓ : PQ × Atom k n)
    (hperm : ((L.filterMap Comp.label).dedup).Perm ((L'.filterMap Comp.label).dedup))
    (hgrp : ∀ ℓ', ℓ' ≠ ℓ → L.filter (fun c => decide (c.label = some ℓ')) =
      L'.filter (fun c => decide (c.label = some ℓ'))) :
    ((eraseL ((L.filterMap Comp.label).dedup) ℓ).map fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
        (Fn D σ (L.filter fun c => decide (c.label = some ℓ'))) ω).prod =
      ((eraseL ((L'.filterMap Comp.label).dedup) ℓ).map fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
        (Fn D σ (L'.filter fun c => decide (c.label = some ℓ'))) ω).prod := by
  have hp : (eraseL ((L.filterMap Comp.label).dedup) ℓ).Perm
      (eraseL ((L'.filterMap Comp.label).dedup) ℓ) := hperm.filter _
  rw [(hp.map (fun ℓ' => PF.op ℓ'.1 (σ ℓ'.2)
    (Fn D σ (L.filter fun c => decide (c.label = some ℓ'))) ω)).prod_eq]
  congr 1
  refine List.map_congr_left fun ℓ' hℓ' => ?_
  have hℓ'' : ℓ' ≠ ℓ := by
    simpa [eraseL] using (List.mem_filter.1 hℓ').2
  rw [hgrp ℓ' hℓ'']

private theorem filter_unl_of_some {M : List (Comp (Atom k n))} {ℓ : PQ × Atom k n}
    (h : ∀ c ∈ M, c.label = some ℓ) : M.filter (fun c => c.label.isNone) = [] :=
  List.filter_eq_nil_iff.2 fun c hc => by simp [h c hc]

private theorem filter_grp_of_some {M : List (Comp (Atom k n))} {ℓ : PQ × Atom k n}
    (h : ∀ c ∈ M, c.label = some ℓ) : M.filter (fun c => decide (c.label = some ℓ)) = M :=
  List.filter_eq_self.2 fun c hc => by simp [h c hc]

private theorem filter_grp_ne_of_some {M : List (Comp (Atom k n))} {ℓ ℓ' : PQ × Atom k n}
    (h : ∀ c ∈ M, c.label = some ℓ) (hne : ℓ' ≠ ℓ) :
    M.filter (fun c => decide (c.label = some ℓ')) = [] :=
  List.filter_eq_nil_iff.2 fun c hc => by simp [h c hc, Ne.symm hne]

private theorem termR_replace_some (A : ModelAdm Ω ι PF D) (σ : Atom k n → ι) (ω : Ω)
    (rest : List (Comp (Atom k n))) (c : Comp (Atom k n)) (ℓ : PQ × Atom k n)
    (hc : c.label = some ℓ) (coeff : Coeff) (outs : List (Coeff × List (Comp (Atom k n))))
    (hlab : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.label = some ℓ)
    (hgood : ∀ c' ∈ c :: rest, c'.label = some ℓ → c'.isGoodKind = true)
    (hgood' : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.isGoodKind = true)
    (hkeep : ∀ o ∈ outs, o.2 ≠ [] ∨ ∃ c' ∈ rest, c'.label = some ℓ)
    (hval : ∀ ω, Comp.val (D ω) σ c = (outs.map fun o => Coeff.eval (D ω).m o.1 *
      (o.2.map (Comp.val (D ω) σ)).prod).sum) :
    (outs.map fun o => Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω).sum =
      Graph.termR (⟨c :: rest, coeff⟩ : Graph k n) PF D σ ω := by
  set R : Ω → ℂ := Fn D σ (rest.filter fun c => decide (c.label = some ℓ)) with hR
  set U := ((rest.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod with hU
  set Oth := ((eraseL (((c :: rest).filterMap Comp.label).dedup) ℓ).map fun ℓ' =>
    PF.op ℓ'.1 (σ ℓ'.2) (Fn D σ ((c :: rest).filter fun c => decide (c.label = some ℓ'))) ω).prod
    with hOth
  have hRgood : A.Good R := by
    refine good_Fn A σ _ fun c' hc' => ?_
    obtain ⟨hc'1, hc'2⟩ := List.mem_filter.1 hc'
    exact hgood c' (List.mem_cons_of_mem _ hc'1) (by simpa using hc'2)
  -- the constants
  have hm : ∀ ω', (D ω').m = msc A.z := A.data_m
  set a : Coeff × List (Comp (Atom k n)) → ℂ := fun o => Coeff.eval (msc A.z) o.1 with ha
  have hval' : ∀ ω', Comp.val (D ω') σ c =
      (outs.map fun o => a o * (o.2.map (Comp.val (D ω') σ)).prod).sum := by
    intro ω'
    rw [hval ω', hm ω']
  -- the left side, term by term
  have hterm : ∀ o ∈ outs, Graph.termR (⟨rest ++ o.2, o.1 * coeff⟩ : Graph k n) PF D σ ω =
      (a o * Coeff.eval (D ω).m coeff * U) *
        (PF.op ℓ.1 (σ ℓ.2) (fun ω' => R ω' * Fn D σ o.2 ω') ω * Oth) := by
    intro o ho
    have h0 := hlab o ho
    have hℓo : ∃ c' ∈ rest ++ o.2, c'.label = some ℓ := by
      rcases hkeep o ho with h | ⟨c', hc', hc'l⟩
      · obtain ⟨c', hc'⟩ := List.exists_mem_of_ne_nil _ h
        exact ⟨c', List.mem_append_right _ hc', h0 c' hc'⟩
      · exact ⟨c', List.mem_append_left _ hc', hc'l⟩
    rw [termR_split _ _ σ ω ℓ hℓo]
    have e1 : (rest ++ o.2).filter (fun c => c.label.isNone) =
        rest.filter (fun c => c.label.isNone) := by
      rw [List.filter_append, filter_unl_of_some h0, List.append_nil]
    have e2 : (rest ++ o.2).filter (fun c => decide (c.label = some ℓ)) =
        rest.filter (fun c => decide (c.label = some ℓ)) ++ o.2 := by
      rw [List.filter_append, filter_grp_of_some h0]
    have hperm : (((c :: rest).filterMap Comp.label).dedup).Perm
        (((rest ++ o.2).filterMap Comp.label).dedup) := by
      refine labs_perm fun b => ?_
      constructor
      · rintro ⟨c', hc', hc'l⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · rw [hc] at hc'l
          obtain rfl : ℓ = b := Option.some.inj hc'l
          exact hℓo
        · exact ⟨c', List.mem_append_left _ hc', hc'l⟩
      · rintro ⟨c', hc', hc'l⟩
        rcases List.mem_append.1 hc' with hc' | hc'
        · exact ⟨c', List.mem_cons_of_mem _ hc', hc'l⟩
        · rw [h0 c' hc'] at hc'l
          obtain rfl : ℓ = b := Option.some.inj hc'l
          exact ⟨c, List.mem_cons_self .., hc⟩
    have hoth := others_eq (PF := PF) (D := D) σ ω ℓ hperm (fun ℓ' hℓ' => by
      rw [List.filter_append, filter_grp_ne_of_some h0 hℓ', List.append_nil,
        List.filter_cons_of_neg (by simp [hc, Ne.symm hℓ'])])
    rw [← hoth, e1, e2, Fn_append]
    simp only [map_mul, Coeff.eval, ha, hm ω]
    rfl
  rw [List.map_congr_left hterm]
  rw [termR_split (c :: rest) coeff σ ω ℓ ⟨c, List.mem_cons_self .., hc⟩]
  have e1 : (c :: rest).filter (fun c => c.label.isNone) =
      rest.filter (fun c => c.label.isNone) := List.filter_cons_of_neg (by simp [hc])
  have e2 : (c :: rest).filter (fun c => decide (c.label = some ℓ)) =
      c :: rest.filter (fun c => decide (c.label = some ℓ)) :=
    List.filter_cons_of_pos (by simp [hc])
  rw [e1, e2]
  have hgl : ∀ p ∈ outs.map (fun o => (a o, fun ω' => R ω' * Fn D σ o.2 ω')), A.Good p.2 := by
    intro p hp
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
    have := A.laws.good_mul _ _ hRgood (good_Fn A σ o.2 (hgood' o ho))
    exact this
  have hf : Fn D σ (c :: rest.filter fun c => decide (c.label = some ℓ)) =
      fun ω' => ((outs.map fun o => (a o, fun ω'' => R ω'' * Fn D σ o.2 ω'')).map
        fun p => p.1 * p.2 ω').sum := by
    funext ω'
    simp only [Fn, List.map_cons, List.prod_cons, List.map_map, Function.comp_def]
    rw [hval' ω', ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
    simp only [hR, Fn]
    ring
  rw [hf, op_lincomb A ℓ.1 (σ ℓ.2) _ hgl]
  simp only [List.map_map, Function.comp_def]
  calc _ = (outs.map fun o => (Coeff.eval (D ω).m coeff * U * Oth) *
        (a o * PF.op ℓ.1 (σ ℓ.2) (fun ω' => R ω' * Fn D σ o.2 ω') ω)).sum :=
        congrArg List.sum (List.map_congr_left fun o _ => by ring)
    _ = _ := by
        rw [List.sum_map_mul_left]
        ring

private theorem list_sum_map_sum {α β : Type*} [Fintype β] (l : List α) (f : α → β → ℂ) :
    (l.map fun a => ∑ b, f a b).sum = ∑ b, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

/-- The formal sum obtained by replacing the component with index `i` by the component lists of
`outs`, with their coefficients. -/
private def replT (Γ : Graph k n) (i : ℕ) (outs : List (Coeff × List (Comp (Atom k n)))) :
    TExpansion k n :=
  outs.map fun o => ⟨n, ⟨Γ.comps.eraseIdx i ++ o.2, o.1 * Γ.coeff⟩, id⟩

/-- Replacing the component `c` at index `i` by the lists of `outs`, with the coefficients of
`outs`, preserves the value, when the value of `c` is the corresponding combination, the new
components carry the label of `c`, and the group of that label consists of components of good
kinds. -/
private theorem valR_replace (A : ModelAdm Ω ι PF D) (Γ : Graph k n) (e : Fin k → ι)
    {i : ℕ} {c : Comp (Atom k n)} (hc : Γ.comps[i]? = some c)
    (outs : List (Coeff × List (Comp (Atom k n))))
    (hlab : ∀ o ∈ outs, ∀ c' ∈ o.2, c'.label = c.label)
    (hgood : c.label.all Γ.GoodGroup = true)
    (hgood' : c.label.isSome = true → ∀ o ∈ outs, ∀ c' ∈ o.2, c'.isGoodKind = true)
    (hkeep : ∀ ℓ, c.label = some ℓ → ∀ o ∈ outs,
      o.2 ≠ [] ∨ ∃ c' ∈ Γ.comps.eraseIdx i, c'.label = some ℓ)
    (hval : ∀ (σ : Atom k n → ι) (ω : Ω), Comp.val (D ω) σ c = (outs.map fun o =>
      Coeff.eval (D ω).m o.1 * (o.2.map (Comp.val (D ω) σ)).prod).sum) :
    (replT Γ i outs).forget.valR PF D e = Γ.valR PF D e := by
  obtain ⟨comps, coeff⟩ := Γ
  funext ω
  simp only [replT, TExpansion.forget, Expansion.valR, List.map_map, Function.comp_def,
    Graph.valR]
  rw [list_sum_map_sum outs (fun (o : Coeff × List (Comp (Atom k n))) (s : Fin n → ι) =>
    Graph.termR (⟨comps.eraseIdx i ++ o.2, o.1 * coeff⟩ : Graph k n) PF D (Sum.elim e s) ω)]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
  have hperm := List.getElem_cons_eraseIdx_perm hi
  rw [hci] at hperm
  have hmemΓ : ∀ c' ∈ c :: comps.eraseIdx i, c' ∈ comps := fun c' hc' => hperm.mem_iff.1 hc'
  rw [← termR_perm hperm coeff (Sum.elim e s) ω]
  cases hl : c.label with
  | none =>
    exact termR_replace_none _ ω _ c hl coeff outs (fun o ho c' hc' => by rw [hlab o ho c' hc', hl])
      (hval _ ω)
  | some ℓ =>
    rw [hl] at hlab hgood
    refine termR_replace_some A _ ω _ c ℓ hl coeff outs (fun o ho c' hc' => hlab o ho c' hc') ?_
      (fun o ho c' hc' => hgood' (by rw [hl]; rfl) o ho c' hc') (hkeep ℓ hl) (hval _)
    intro c' hc' hc'l
    have h1 := hgood
    simp only [Option.all_some, Graph.GoodGroup, List.all_eq_true] at h1
    have := h1 c' (hmemΓ c' hc')
    simpa [hc'l] using this

end Replace

/-! ## The value identities (4.17), (4.20) -/

section SchurVals

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

private theorem val_G_comp {V : Type*} (d : Data ι) (σ : V → ι) (c : Comp V) (ch : Charge)
    (hk : c.kind = .G ch) :
    Comp.val d σ c = ch.hom (d.Gm (c.minor.map σ).toFinset (σ c.x) (σ c.y)) := by
  simp [Comp.val, hk, Charge.apply_eq]

private theorem val_solidC {V : Type*} [DecidableEq V] (d : Data ι) (σ : V → ι) (ch : Charge)
    (u v : V) : Comp.val d σ (solidC ch u v) = ch.hom (d.Gm ∅ (σ u) (σ v)) := by
  unfold solidC
  split_ifs with h
  · subst h
    simp [Comp.val, mkC, Charge.apply_eq]
  · simp [Comp.val, mkC, Charge.apply_eq]

private theorem val_mkInv {V : Type*} (d : Data ι) (σ : V → ι) (ch : Charge) (u : V) :
    Comp.val d σ (mkC (.inv ch) u u) = ch.hom ((d.Gm ∅ (σ u) (σ u))⁻¹) := by
  simp [Comp.val, mkC, Charge.apply_eq]

/-- [II, (4.17)] on the entries of the data record. -/
private theorem schur_id (A : ModelAdm Ω ι PF D) (ω : Ω) (ch : Charge) (a b i : ι) :
    ch.hom ((D ω).Gm ∅ a b) = ch.hom ((D ω).Gm {i} a b) +
      ch.hom ((D ω).Gm ∅ a i) * (ch.hom ((D ω).Gm ∅ i b) * ch.hom (((D ω).Gm ∅ i i)⁻¹)) := by
  rw [A.data_G ω, A.data_minor ω i]
  have h := RBM8D.green_eq_greenMinor_add (green (A.H ω) A.z) i a b
  conv_lhs => rw [h]
  simp [Matrix.of_apply, map_add, map_mul, map_inv₀, div_eq_mul_inv, mul_assoc]

end SchurVals

private theorem good_label {V : Type*} (c : Comp V) (l : Option (PQ × V)) :
    ({ c with label := l } : Comp V).isGoodKind = c.isGoodKind := rfl

private theorem solidC_good {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    (solidC ch u v).isGoodKind = true := by
  unfold solidC
  split_ifs <;> simp [mkC, Comp.isGoodKind]

/-- A formal sum with one term `Γ` is value-preserving. -/
private theorem forget_self_valR {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) {k n : ℕ} (Γ : Graph k n) (e : Fin k → ι) :
    (TExpansion.forget [Tracked.self Γ]).valR PF D e = Γ.valR PF D e := by
  funext ω
  simp [TExpansion.forget, Expansion.valR, Tracked.self]

/-- [II, (4.17)]: `oSchur` preserves the value of every graph under the model relations. -/
theorem oSchur_value (k n : ℕ) (x : Atom k n) (i : ℕ) :
    PreservesValue (oSchur x i) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  unfold oSchur
  rcases hci : Γ.comps[i]? with _ | c
  · have : oSchurT x i Γ = [Tracked.self Γ] := by simp [oSchurT, hci]
    rw [this]
    exact forget_self_valR PF D Γ e
  · by_cases hkG : ∃ ch, c.kind = .G ch
    · obtain ⟨ch, hk⟩ := hkG
      by_cases hg : (c.minor.isEmpty && c.label.all Γ.GoodGroup) = true
      · have hE : oSchurT x i Γ = replT Γ i [(1, [{ c with minor := [x] }]),
            (1, [{ solidC ch c.x x with label := c.label },
              { solidC ch x c.y with label := c.label },
              { mkC (.inv ch) x x with label := c.label }])] := by
          simp [oSchurT, hci, hk, hg, replT]
        rw [hE]
        have hmin : c.minor = [] := by simpa using (Bool.and_eq_true_iff.1 hg).1
        refine valR_replace A Γ e hci _ ?_ (Bool.and_eq_true_iff.1 hg).2 ?_ ?_ ?_
        · intro o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc' <;>
            rcases hc' with rfl | rfl | rfl <;> rfl
        · intro _ o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          · rcases hc' with rfl; simp [Comp.isGoodKind, hk]
          · rcases hc' with rfl | rfl | rfl
            · rw [good_label]; exact solidC_good ch c.x x
            · rw [good_label]; exact solidC_good ch x c.y
            · simp [mkC, Comp.isGoodKind]
        · intro ℓ _ o ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp
        · intro σ ω
          have h1 := val_G_comp (D ω) σ c ch hk
          have h2 : Comp.val (D ω) σ { c with minor := [x] } =
              ch.hom ((D ω).Gm {σ x} (σ c.x) (σ c.y)) := by
            have := val_G_comp (D ω) σ { c with minor := [x] } ch hk
            simpa using this
          rw [h1, hmin]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
            List.prod_nil, Comp.val_label, val_solidC, val_mkInv, h2, mul_one,
            add_zero, List.toFinset_nil]
          have := schur_id A ω ch (σ c.x) (σ c.y) (σ x)
          simpa [Coeff.eval] using this
      · have : oSchurT x i Γ = [Tracked.self Γ] := by simp [oSchurT, hci, hk, hg]
        rw [this]
        exact forget_self_valR PF D Γ e
    · have : oSchurT x i Γ = [Tracked.self Γ] := by
        simp only [oSchurT, hci]
        cases hk : c.kind <;> simp_all
      rw [this]
      exact forget_self_valR PF D Γ e

/-- [II, (4.20)]: `oSchurRev` preserves the value of every graph under the model relations. -/
theorem oSchurRev_value (k n : ℕ) (x : Atom k n) (i : ℕ) :
    PreservesValue (oSchurRev x i) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  unfold oSchurRev
  rcases hci : Γ.comps[i]? with _ | c
  · have : oSchurRevT x i Γ = [Tracked.self Γ] := by simp [oSchurRevT, hci]
    rw [this]
    exact forget_self_valR PF D Γ e
  · by_cases hkG : ∃ ch, c.kind = .G ch
    · obtain ⟨ch, hk⟩ := hkG
      by_cases hg : (decide (c.minor = [x]) && c.label.all Γ.GoodGroup) = true
      · have hE : oSchurRevT x i Γ = replT Γ i [(1, [{ c with minor := [] }]),
            (-1, [{ solidC ch c.x x with label := c.label },
              { solidC ch x c.y with label := c.label },
              { mkC (.inv ch) x x with label := c.label }])] := by
          simp [oSchurRevT, hci, hk, hg, replT]
        rw [hE]
        have hmin : c.minor = [x] := by simpa using (Bool.and_eq_true_iff.1 hg).1
        refine valR_replace A Γ e hci _ ?_ (Bool.and_eq_true_iff.1 hg).2 ?_ ?_ ?_
        · intro o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc' <;>
            rcases hc' with rfl | rfl | rfl <;> rfl
        · intro _ o ho c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          · rcases hc' with rfl; simp [Comp.isGoodKind, hk]
          · rcases hc' with rfl | rfl | rfl
            · rw [good_label]; exact solidC_good ch c.x x
            · rw [good_label]; exact solidC_good ch x c.y
            · simp [mkC, Comp.isGoodKind]
        · intro ℓ _ o ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> simp
        · intro σ ω
          have h1 := val_G_comp (D ω) σ c ch hk
          have h2 : Comp.val (D ω) σ { c with minor := [] } =
              ch.hom ((D ω).Gm ∅ (σ c.x) (σ c.y)) := by
            have := val_G_comp (D ω) σ { c with minor := [] } ch hk
            simpa using this
          rw [h1, hmin]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
            List.prod_nil, Comp.val_label, val_solidC, val_mkInv, h2, mul_one,
            add_zero]
          have hs : ([σ x] : List ι).toFinset = {σ x} := by simp
          rw [hs]
          have := schur_id A ω ch (σ c.x) (σ c.y) (σ x)
          simp only [Coeff.eval, map_neg, map_one]
          linear_combination (-1 : ℂ) * this
      · have : oSchurRevT x i Γ = [Tracked.self Γ] := by simp [oSchurRevT, hci, hk, hg]
        rw [this]
        exact forget_self_valR PF D Γ e
    · have : oSchurRevT x i Γ = [Tracked.self Γ] := by
        simp only [oSchurRevT, hci]
        cases hk : c.kind <;> simp_all
      rw [this]
      exact forget_self_valR PF D Γ e

/-! ## The value identity (4.21) -/

section TaylorVals

private theorem taylor_id (g m : ℂ) (d : ℕ) :
    g⁻¹ = ∑ j ∈ Finset.range (d + 1), ((-1) ^ j * (m⁻¹) ^ (j + 1)) * (g - m) ^ j +
      (g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (d + 1), (-(g - m) / m) ^ j) := by
  have h : ∑ j ∈ Finset.range (d + 1), ((-1) ^ j * (m⁻¹) ^ (j + 1)) * (g - m) ^ j =
      m⁻¹ * ∑ j ∈ Finset.range (d + 1), (-(g - m) / m) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : -(g - m) / m = (-1) * ((g - m) * m⁻¹) := by ring
    rw [e, mul_pow, mul_pow]
    ring
  rw [h]
  ring

private theorem list_sum_range (f : ℕ → ℂ) (d : ℕ) :
    ((List.range d).map f).sum = ∑ j ∈ Finset.range d, f j := by
  induction d with
  | zero => simp
  | succ d ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

end TaylorVals

/-- [II, (4.21)]: `oTaylor` preserves the value of every graph under the model relations. -/
theorem oTaylor_value (k n D i : ℕ) :
    PreservesValue (oTaylor (k := k) (n := n) D i) modelAdm := by
  intro Ω ι _ _ PF D' hA Γ e
  obtain ⟨A⟩ := hA
  unfold oTaylor
  rcases hci : Γ.comps[i]? with _ | c
  · have : oTaylorT D i Γ = [Tracked.self Γ] := by simp [oTaylorT, hci]
    rw [this]
    exact forget_self_valR PF D' Γ e
  · by_cases hkI : ∃ ch, c.kind = .inv ch
    · obtain ⟨ch, hk⟩ := hkI
      by_cases hg : (c.label.all (fun ℓ => Γ.GoodGroup ℓ &&
          (Γ.comps.eraseIdx i).any fun c' => decide (c'.label = some ℓ))) = true
      · have hE : oTaylorT D i Γ = replT Γ i
            (((List.range (D + 1)).map fun j => (((-1 : Coeff) ^ j * mInvOf ch ^ (j + 1)),
              List.replicate j { c with kind := .light ch, y := c.x })) ++
              [(1, [{ c with kind := .wD ch D, y := c.x }])]) := by
          simp [oTaylorT, hci, hk, hg, replT, List.map_map, Function.comp_def]
        rw [hE]
        have hcmem : c ∈ Γ.comps := List.mem_of_getElem? hci
        have hmin : c.minor.isEmpty = true ∨ c.label = none := by
          cases hl : c.label with
          | none => exact Or.inr rfl
          | some ℓ =>
            left
            rw [hl] at hg
            simp only [Option.all_some, Bool.and_eq_true] at hg
            have h1 := hg.1
            simp only [Graph.GoodGroup, List.all_eq_true] at h1
            have := h1 c hcmem
            simpa [hl, Comp.isGoodKind, hk] using this
        refine valR_replace A Γ e hci _ ?_ ?_ ?_ ?_ ?_
        · intro o ho c' hc'
          simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ho
          rcases ho with ⟨j, hj, rfl⟩ | rfl
          · rw [List.mem_replicate] at hc'
            rw [hc'.2]
          · simp only [List.mem_singleton] at hc'
            rw [hc']
        · cases hl : c.label with
          | none => simp
          | some ℓ =>
            rw [hl] at hg
            simp only [Option.all_some, Bool.and_eq_true] at hg ⊢
            exact hg.1
        · intro hs o ho c' hc'
          have hm : c.minor.isEmpty = true := by
            rcases hmin with h | h
            · exact h
            · rw [h] at hs; simp at hs
          simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ho
          rcases ho with ⟨j, hj, rfl⟩ | rfl
          · rw [List.mem_replicate] at hc'
            rw [hc'.2]
            simp [Comp.isGoodKind]
          · simp only [List.mem_singleton] at hc'
            rw [hc']
            simpa [Comp.isGoodKind] using hm
        · intro ℓ hl o ho
          right
          rw [hl] at hg
          simp only [Option.all_some, Bool.and_eq_true] at hg
          have := hg.2
          simp only [List.any_eq_true, decide_eq_true_eq] at this
          exact this
        · intro σ ω
          have h1 : Comp.val (D' ω) σ c =
              ch.hom (((D' ω).Gm (c.minor.map σ).toFinset (σ c.x) (σ c.x))⁻¹) := by
            simp [Comp.val, hk, Charge.apply_eq]
          set g := (D' ω).Gm (c.minor.map σ).toFinset (σ c.x) (σ c.x) with hg0
          set m := (D' ω).m with hm0
          have hlight : Comp.val (D' ω) σ { c with kind := .light ch, y := c.x } =
              ch.hom (g - m) := by
            simp [Comp.val, Charge.apply_eq, g, m]
          have hwD : Comp.val (D' ω) σ { c with kind := .wD ch D, y := c.x } =
              ch.hom (g⁻¹ - m⁻¹ * ∑ j ∈ Finset.range (D + 1), (-(g - m) / m) ^ j) := by
            simp [Comp.val, Charge.apply_eq, g, m]
          have hco : ∀ j : ℕ, Coeff.eval m ((-1 : Coeff) ^ j * mInvOf ch ^ (j + 1)) =
              (-1) ^ j * (ch.hom m⁻¹) ^ (j + 1) := by
            intro j
            have := Charge.hom_mInv ch m
            simp only [Coeff.eval] at this ⊢
            simp only [map_mul, map_pow, map_neg, map_one, this]
          simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlight, hwD,
            List.map_replicate, List.prod_replicate, List.prod_cons, List.prod_nil, mul_one,
            add_zero, hco]
          rw [h1, list_sum_range]
          have := congrArg ch.hom (taylor_id g m D)
          simp only [map_add, map_sum, map_mul, map_pow, map_neg, map_one, map_sub, map_inv₀,
            map_div₀] at this ⊢
          have h1' : Coeff.eval m 1 = 1 := by simp [Coeff.eval]
          rw [h1', one_mul]
          exact this
      · have : oTaylorT D i Γ = [Tracked.self Γ] := by simp [oTaylorT, hci, hk, hg]
        rw [this]
        exact forget_self_valR PF D' Γ e
    · have : oTaylorT D i Γ = [Tracked.self Γ] := by
        simp only [oTaylorT, hci]
        cases hk : c.kind <;> simp_all
      rw [this]
      exact forget_self_valR PF D' Γ e

section Instances

end Instances

end RBM8D.Graphs
