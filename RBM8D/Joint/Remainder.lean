import RBM8D.Joint.Relabel

/-!
# The remainder of the iterated `T`-equation

[II, §6.1, (6.1)–(6.3)], [II, Cor 3.8]: the remainder `(Θ Σ̃^{(n)})^{K+1} T` of the `K`-fold
iteration of [II, (3.5)], `T_{x,⊕⊖} = |m|² Σ_α s_{xα} G_{α⊕} Ḡ_{α⊖}` ([I, (2.4)]).

By `Θ (1 − |m|² S) = |m|² S` ([II, (1.13)]),
`Σ_x ((Θ Σ̃)^{K+1})_{⊗x} T_{x,⊕⊖} = Σ_α ((Θ Σ̃)^{K+1} Θ)_{⊗α} G_{α⊕} Ḡ_{α⊖}
  − Σ_β ((Θ Σ̃)^{K+1} Θ)_{⊗β} T_{β,⊕⊖}`,
and `(Θ Σ̃)^{K+1} Θ` is the sum of the labelled `Θ` edges `Θ^{[o]}` over the words `o` of length
`K + 1` in the even orders `4, …, n` ([II, (2.10)]). The remainder `Remainder.rem n K` is the
formal sum, over these words, of the `O_dot` forms ([II, Def 4.2]) of
`Θ^{[o]}_{⊗α} G_{α⊕} Ḡ_{α⊖}` and `−|m|² Θ^{[o]}_{⊗β} s_{βα} G_{α⊕} Ḡ_{α⊖}`: each solid edge
`G_{α b}` at `b ∈ {⊕, ⊖}` becomes `G_{α b} ×_{α b}` or the weight `G_{αα}` with the dotted edge
`α = b`. These graphs are the relabellings by `o` of graphs with the plain `Θ` edge at `⊗`, of
scaling order `≥ 2 + 2(K + 1)` (`G14.remainder_stmt`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

namespace Remainder

/-! ## The graphs -/

/-- The two `O_dot` forms of the solid edge `G^c_{u b}` at the external atom `b`: the solid edge
with the `×`-dotted edge `u ≠ b` (`false`), and the weight `G^c_{uu}` with the dotted edge
`u = b` (`true`). -/
def piece {m : ℕ} (c : Charge) (u : Atom 3 m) (b : Fin 3) : Bool → List (Comp (Atom 3 m))
  | false => [mkC (.G c) u (.inl b), mkC .xdot u (.inl b)]
  | true => [mkC (.weight c) u u, mkC .dot u (.inl b)]

/-- An `O_dot` form of `Θ^{[o]}_{⊗α} G_{α⊕} Ḡ_{α⊖}`: internal atom `α`. -/
def lead (o : List ℕ) (d₁ d₂ : Bool) : Graph 3 1 :=
  ⟨mkC (.theta o) (.inl 0) (.inr 0) :: (piece .plus (.inr 0) 1 d₁ ++ piece .minus (.inr 0) 2 d₂),
    1⟩

/-- An `O_dot` form of `−|m|² Θ^{[o]}_{⊗β} s_{βα} G_{α⊕} Ḡ_{α⊖}`: internal atoms `β = 0`,
`α = 1`. -/
def tail (o : List ℕ) (d₁ d₂ : Bool) : Graph 3 2 :=
  ⟨mkC (.theta o) (.inl 0) (.inr 0) :: mkC (.waved .s) (.inr 0) (.inr 1) ::
    (piece .plus (.inr 1) 1 d₁ ++ piece .minus (.inr 1) 2 d₂), -(cm * cmb)⟩

/-- The `O_dot` forms of `Θ^{[o]}_{⊗α} G_{α⊕} Ḡ_{α⊖}` and of
`−|m|² Θ^{[o]}_{⊗β} s_{βα} G_{α⊕} Ḡ_{α⊖}`. -/
def forms (o : List ℕ) : Expansion 3 :=
  [false, true].flatMap fun d₁ => [false, true].flatMap fun d₂ =>
    [⟨1, lead o d₁ d₂⟩, ⟨2, tail o d₁ d₂⟩]

/-- The remainder `(Θ Σ̃^{(n)})^{K+1} T` as a formal sum: the forms `forms o` over the words `o`
of length `K + 1` in the even orders `4, …, n`. -/
def rem (n K : ℕ) : Expansion 3 := (G14.words n (K + 1)).flatMap forms

/-- `lead o d₁ d₂` is the relabelling by `o` of `lead [] d₁ d₂`. -/
theorem lead_relabel (o : List ℕ) (d₁ d₂ : Bool) :
    (lead [] d₁ d₂).relabelRoot o = lead o d₁ d₂ := by
  cases d₁ <;> cases d₂ <;> simp [Graph.relabelRoot, lead, piece, mkC]

/-- `tail o d₁ d₂` is the relabelling by `o` of `tail [] d₁ d₂`. -/
theorem tail_relabel (o : List ℕ) (d₁ d₂ : Bool) :
    (tail [] d₁ d₂).relabelRoot o = tail o d₁ d₂ := by
  cases d₁ <;> cases d₂ <;> simp [Graph.relabelRoot, tail, piece, mkC]

/-- The graphs of `rem n K` are the forms with the plain `Θ` edge relabelled by a word of length
`K + 1`. -/
theorem mem_rem {n K : ℕ} {g : Σ m : ℕ, Graph 3 m} (hg : g ∈ rem n K) :
    ∃ o ∈ G14.words n (K + 1), ∃ d₁ d₂ : Bool,
      g = ⟨1, (lead [] d₁ d₂).relabelRoot o⟩ ∨ g = ⟨2, (tail [] d₁ d₂).relabelRoot o⟩ := by
  obtain ⟨o, ho, hg⟩ := List.mem_flatMap.1 hg
  refine ⟨o, ho, ?_⟩
  simp only [forms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  simp only [lead_relabel, tail_relabel]
  rcases hg with ((h | h) | (h | h)) | ((h | h) | (h | h))
  · exact ⟨false, false, Or.inl h⟩
  · exact ⟨false, false, Or.inr h⟩
  · exact ⟨false, true, Or.inl h⟩
  · exact ⟨false, true, Or.inr h⟩
  · exact ⟨true, false, Or.inl h⟩
  · exact ⟨true, false, Or.inr h⟩
  · exact ⟨true, true, Or.inl h⟩
  · exact ⟨true, true, Or.inr h⟩

/-! ## The graph properties -/

section Base

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

local macro "kdec" : tactic => `(tactic| decide +kernel)

private instance Remainder_decTKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) :
    Decidable (Γ.TKinds N) :=
  inferInstanceAs (Decidable (_ = true))

private instance Remainder_decAtExternals {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.AtExternals :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private instance Remainder_decNoLabDot {k n : ℕ} (Γ : Graph k n) : Decidable Γ.NoLabDot := by
  unfold Graph.NoLabDot; infer_instance

/-- The properties of a graph with the plain `Θ` edge at `⊗` that `G14.relabel` carries to its
relabellings. -/
private def Base {m : ℕ} (F : Graph 3 m) : Prop :=
  G14.RootedTheta F ∧ F.Normal 12 ∧ F.TKinds 0 ∧ F.AtExternals ∧ F.Spans ∅ ∧
    F.TensorDiffusive ∧ F.DotsAcyclic ∧ F.NoLabDot ∧ F.labels.length ≤ 1 ∧ F.RgCheck ∧
    (F.DiagRecoll ∨ F.RootedAtExt) ∧ 2 ≤ F.ord

private theorem base_lead (d₁ d₂ : Bool) : Base (lead [] d₁ d₂) := by
  cases d₁ <;> cases d₂ <;>
    exact ⟨⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, by unfold lead piece; kdec⟩,
      by unfold lead piece; kdec, by unfold lead piece; kdec, by unfold lead piece; kdec,
      by unfold lead piece; kdec, by unfold lead piece; kdec, by unfold lead piece; kdec,
      by unfold lead piece; kdec, by unfold lead piece; kdec, by unfold lead piece; kdec,
      by unfold lead piece; kdec, by unfold lead piece; kdec⟩

private theorem base_tail (d₁ d₂ : Bool) : Base (tail [] d₁ d₂) := by
  cases d₁ <;> cases d₂ <;>
    exact ⟨⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, by unfold tail piece; kdec⟩,
      by unfold tail piece; kdec, by unfold tail piece; kdec, by unfold tail piece; kdec,
      by unfold tail piece; kdec, by unfold tail piece; kdec, by unfold tail piece; kdec,
      by unfold tail piece; kdec, by unfold tail piece; kdec, by unfold tail piece; kdec,
      by unfold tail piece; kdec, by unfold tail piece; kdec⟩

end Base

/-- The properties of the graphs of `Err` read by `TRec.Shape` and `TRec.Def63` for the
relabelling by a word of length `K + 1` of a graph with the properties of `Base`, for
`D ≤ 2K`. -/
private theorem lift {m n K D : ℕ} {F : Graph 3 m} (hF : Base F) {o : List ℕ}
    (ho : o ∈ G14.words n (K + 1)) (hD : D ≤ 2 * K) :
    ((∃ C, (F.relabelRoot o).Normal C) ∧ (F.relabelRoot o).TKindsErr n ∧
      (F.relabelRoot o).AtExternals ∧ (F.relabelRoot o).DoublyConnected) ∧
    (D : ℤ) < (F.relabelRoot o).ord ∧
    ((F.relabelRoot o).TensorDiffusive ∧ (F.relabelRoot o).dotExcess = 0 ∧
      (F.relabelRoot o).NoLabDot ∧ (F.relabelRoot o).labels.length ≤ 1) ∧
    (F.relabelRoot o).RgCheck ∧
    (¬ (F.relabelRoot o).DiagRecoll → (F.relabelRoot o).RootedAtExt) := by
  obtain ⟨hR, hN, hK, hE, hS, hT, hDA, hX, hl, hRg, hDR, hord⟩ := hF
  have hw : o ∈ G14.wordsUpTo n (K + 1) :=
    Words.mem_wordsUpTo.2 ⟨((Words.mem_words _ _).1 ho).1.le, ((Words.mem_words _ _).1 ho).2⟩
  have hlab : labelOK n o = true := Words.labelOK_of_mem_wordsUpTo hw le_rfl
  have hinc : 2 * (K + 1) ≤ Words.labelInc o := by
    have := Words.two_mul_length_le_labelInc_of_mem hw
    rwa [((Words.mem_words _ _).1 ho).1] at this
  have hent : ∀ e ∈ o, 2 ≤ e := fun e he => by
    have := List.all_eq_true.1 hlab e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    omega
  obtain ⟨h1, h2, -, h4, h5, h6, -, -, -, -, -, -, -, -, -, h16, h17, h18, h19, -, h21, h22,
    h23, -, -, -⟩ := G14.relabel F o hR
  have hord' : (F.relabelRoot o).ord = F.ord + Words.labelInc o := by
    rw [h1, Words.labelInc_cast o hent]
  refine ⟨⟨⟨12, h4 12 hN⟩, Graph.tKindsErr_of_tKinds n _ (h2 0 n (Nat.zero_le _) hlab hK), h5 hE,
    h6 ⟨∅, ∅, Finset.disjoint_empty_left _, by simp, by simp, hS, hS⟩⟩, ?_,
    ⟨h16 hT, by rw [h17]; exact (F.dotsAcyclic_iff_dotExcess_eq_zero).1 hDA, h18 hX,
      by rw [h19]; exact hl⟩, h21 hRg, fun hd => ?_⟩
  · rw [hord']
    omega
  · rcases hDR with h | h
    · exact absurd (h22.2 h) hd
    · exact h23 h

/-- Every graph of `rem n K` has the properties of a graph of `Err` read by `TRec.Shape` and
`TRec.Def63`, of scaling order `> D` for `D ≤ 2K`. -/
theorem props_rem {n K D : ℕ} (hD : D ≤ 2 * K) {g : Σ m : ℕ, Graph 3 m} (hg : g ∈ rem n K) :
    ((∃ C, g.2.Normal C) ∧ g.2.TKindsErr n ∧ g.2.AtExternals ∧ g.2.DoublyConnected) ∧
    (D : ℤ) < g.2.ord ∧
    (g.2.TensorDiffusive ∧ g.2.dotExcess = 0 ∧ g.2.NoLabDot ∧ g.2.labels.length ≤ 1) ∧
    g.2.RgCheck ∧ (¬ g.2.DiagRecoll → g.2.RootedAtExt) := by
  obtain ⟨o, ho, d₁, d₂, rfl | rfl⟩ := mem_rem hg
  · exact lift (base_lead d₁ d₂) ho hD
  · exact lift (base_tail d₁ d₂) ho hD

/-- The record with the remainder as `Err` has the properties of [II, Def 3.2] at order `n` with
error order `D ≤ 2K`. -/
theorem shape_rem {n K D : ℕ} (hD : D ≤ 2 * K) : (⟨[], [], [], rem n K⟩ : TRec).Shape n n D :=
  ⟨⟨fun g hg => by simp at hg, fun g hg => (props_rem hD hg).1⟩, fun g hg => by simp at hg,
    fun g hg => by simp at hg, fun g hg => by simp at hg, fun g hg => (props_rem hD hg).2.1⟩

/-- The record with the remainder as `Err` has the clauses of [II, Def 6.3] (`TRec.Def63`). -/
theorem def63_rem {n K : ℕ} : (⟨[], [], [], rem n K⟩ : TRec).Def63 := by
  refine ⟨⟨fun g hg => by simp at hg, fun g hg => by simp at hg, fun g hg => by simp at hg⟩,
    fun g hg => ?_, fun g hg => by simp at hg, fun g hg => by simp at hg,
    fun g hg => by simp at hg, fun g hg => ?_, fun g hg => ?_, fun g hg => by simp at hg,
    fun g hg => by simp at hg, fun g hg => by simp at hg⟩
  · simp only [List.nil_append] at hg
    exact (props_rem (le_refl (2 * K)) hg).2.2.1
  · simp only [List.nil_append] at hg
    exact (props_rem (le_refl (2 * K)) hg).2.2.2.1
  · simp only [List.nil_append] at hg
    exact fun _ => (props_rem (le_refl (2 * K)) hg).2.2.2.2

/-! ## The value -/

section Value

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι]

/-- The value of a graph without `P`/`Q` label is the product of its factors. -/
private theorem termR_of_labelFree {k n : ℕ} (Γ : Graph k n) (h : ∀ c ∈ Γ.comps, c.label = none)
    (PF : PFamily Ω ι) (Dt : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) :
    Γ.termR PF Dt σ ω = Γ.coeff.eval (Dt ω).m * (Γ.comps.map (Comp.val (Dt ω) σ)).prod := by
  have h1 : (Γ.comps.filter fun c => c.label.isNone) = Γ.comps :=
    List.filter_eq_self.2 fun c hc => by simp [h c hc]
  have h2 : Γ.labels = [] := by
    unfold Graph.labels
    rw [List.filterMap_eq_nil_iff.2 fun c hc => h c hc]
    rfl
  simp [Graph.termR, h1, h2]

/-- The two `O_dot` forms of a solid edge sum to the solid edge:
`G_{ab} 1_{a ≠ b} + G_{aa} 1_{a = b} = G_{ab}`. -/
private theorem piece_sum {m : ℕ} (D : Data ι) (σ : Atom 3 m → ι) (c : Charge) (u : Atom 3 m)
    (b : Fin 3) :
    ((piece c u b false).map (Comp.val D σ)).prod + ((piece c u b true).map (Comp.val D σ)).prod =
      c.apply (D.Gm ∅ (σ u) (σ (.inl b))) := by
  by_cases h : σ u = σ (.inl b)
  · simp [piece, mkC, Comp.val, h]
  · simp [piece, mkC, Comp.val, h]

omit [DecidableEq ι] in
/-- A sum over the labellings of one atom. -/
private theorem sum_fin_one (F : (Fin 1 → ι) → ℂ) : ∑ s, F s = ∑ a, F fun _ => a :=
  (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun s => by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl)

omit [DecidableEq ι] in
/-- A sum over the labellings of two atoms is a double sum. -/
private theorem sum_fin_two (F : (Fin 2 → ι) → ℂ) : ∑ s, F s = ∑ a, ∑ b, F ![a, b] := by
  rw [← (piFinTwoEquiv fun _ => ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- The factor of the `Θ` edge `Θ^{[o]}_{uv}`. -/
private theorem val_theta {V : Type*} (D : Data ι) (σ : V → ι) (o : List ℕ) (u v : V) :
    Comp.val D σ (mkC (.theta o) u v) = D.chain o (σ u) (σ v) := rfl

/-- The factor of the waved edge `s_{uv}`. -/
private theorem val_s {V : Type*} (D : Data ι) (σ : V → ι) (u v : V) :
    Comp.val D σ (mkC (.waved .s) u v) = D.S (σ u) (σ v) := rfl

/-- The four `O_dot` forms of `Θ^{[o]}_{⊗α} G_{α⊕} Ḡ_{α⊖}` sum to
`Σ_α Θ^{[o]}_{⊗α} G_{α⊕} Ḡ_{α⊖}`. -/
private theorem lead_sum (PF : PFamily Ω ι) (Dt : Ω → Data ι) (o : List ℕ) (e : Fin 3 → ι)
    (ω : Ω) :
    (lead o false false).valR PF Dt e ω + (lead o false true).valR PF Dt e ω +
        (lead o true false).valR PF Dt e ω + (lead o true true).valR PF Dt e ω =
      ∑ a, (Dt ω).chain o (e 0) a * ((Dt ω).Gm ∅ a (e 1) * star ((Dt ω).Gm ∅ a (e 2))) := by
  have hL : ∀ d₁ d₂ (s : Fin 1 → ι), (lead o d₁ d₂).termR PF Dt (Sum.elim e s) ω =
      (Dt ω).chain o (e 0) (s 0) *
        (((piece .plus (.inr 0) 1 d₁).map (Comp.val (Dt ω) (Sum.elim e s))).prod *
          ((piece .minus (.inr 0) 2 d₂).map (Comp.val (Dt ω) (Sum.elim e s))).prod) := by
    intro d₁ d₂ s
    rw [termR_of_labelFree _ (by cases d₁ <;> cases d₂ <;> simp [lead, piece, mkC])]
    simp only [lead, List.map_cons, List.map_append, List.prod_cons, List.prod_append, val_theta,
      Coeff.eval, map_one, one_mul]
    rfl
  simp only [Graph.valR, ← Finset.sum_add_distrib, hL]
  rw [sum_fin_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 := piece_sum (m := 1) (Dt ω) (Sum.elim e fun _ => a) .plus (.inr 0) 1
  have h2 := piece_sum (m := 1) (Dt ω) (Sum.elim e fun _ => a) .minus (.inr 0) 2
  simp only [Sum.elim_inr, Sum.elim_inl, Charge.apply] at h1 h2
  rw [← h1, ← h2]
  ring

/-- The four `O_dot` forms of `−|m|² Θ^{[o]}_{⊗β} s_{βα} G_{α⊕} Ḡ_{α⊖}` sum to
`−|m|² Σ_{β,α} Θ^{[o]}_{⊗β} s_{βα} G_{α⊕} Ḡ_{α⊖}`. -/
private theorem tail_sum (PF : PFamily Ω ι) (Dt : Ω → Data ι) (o : List ℕ) (e : Fin 3 → ι)
    (ω : Ω) :
    (tail o false false).valR PF Dt e ω + (tail o false true).valR PF Dt e ω +
        (tail o true false).valR PF Dt e ω + (tail o true true).valR PF Dt e ω =
      -((Dt ω).m * star (Dt ω).m) * ∑ b, ∑ a, (Dt ω).chain o (e 0) b * (Dt ω).S b a *
        ((Dt ω).Gm ∅ a (e 1) * star ((Dt ω).Gm ∅ a (e 2))) := by
  have hT : ∀ d₁ d₂ (s : Fin 2 → ι), (tail o d₁ d₂).termR PF Dt (Sum.elim e s) ω =
      -((Dt ω).m * star (Dt ω).m) * ((Dt ω).chain o (e 0) (s 0) * ((Dt ω).S (s 0) (s 1) *
        (((piece .plus (.inr 1) 1 d₁).map (Comp.val (Dt ω) (Sum.elim e s))).prod *
          ((piece .minus (.inr 1) 2 d₂).map (Comp.val (Dt ω) (Sum.elim e s))).prod))) := by
    intro d₁ d₂ s
    rw [termR_of_labelFree _ (by cases d₁ <;> cases d₂ <;> simp [tail, piece, mkC])]
    simp only [tail, List.map_cons, List.map_append, List.prod_cons, List.prod_append, val_theta,
      val_s]
    simp [Coeff.eval, CVar.eval]
  simp only [Graph.valR, ← Finset.sum_add_distrib, hT]
  rw [sum_fin_two, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 := piece_sum (Dt ω) (Sum.elim e ![b, a]) .plus (.inr 1) 1
  have h2 := piece_sum (Dt ω) (Sum.elim e ![b, a]) .minus (.inr 1) 2
  simp only [Sum.elim_inr, Sum.elim_inl, Charge.apply, Matrix.cons_val_one,
    Matrix.cons_val_zero] at h1 h2 ⊢
  rw [← h1, ← h2]
  ring

/-- The value of `forms o`. -/
private theorem forms_valR (PF : PFamily Ω ι) (Dt : Ω → Data ι) (o : List ℕ) (e : Fin 3 → ι)
    (ω : Ω) :
    (forms o).valR PF Dt e ω =
      ∑ a, (Dt ω).chain o (e 0) a * ((Dt ω).Gm ∅ a (e 1) * star ((Dt ω).Gm ∅ a (e 2))) -
        (Dt ω).m * star (Dt ω).m * ∑ b, ∑ a, (Dt ω).chain o (e 0) b * (Dt ω).S b a *
          ((Dt ω).Gm ∅ a (e 1) * star ((Dt ω).Gm ∅ a (e 2))) := by
  have h1 := lead_sum PF Dt o e ω
  have h2 := tail_sum PF Dt o e ω
  simp only [forms, Expansion.valR, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  linear_combination h1 + h2

/-- The value of a formal sum over a list of words is the sum of the values. -/
private theorem valR_flatMap (PF : PFamily Ω ι) (Dt : Ω → Data ι) (W : List (List ℕ))
    (f : List ℕ → Expansion 3) (e : Fin 3 → ι) (ω : Ω) :
    Expansion.valR (W.flatMap f) PF Dt e ω = (W.map fun o => (f o).valR PF Dt e ω).sum := by
  induction W with
  | nil => rfl
  | cons o W ih =>
    simp only [Expansion.valR] at ih ⊢
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-! ## The chain of the labelled `Θ` edges -/

/-- `(Θ Σ̃)^k Θ` is the sum of the labelled `Θ` edges over the words of length `k`
([II, (2.10)]), with `Σ̃` the sum of the matrices `Σ_l`, `l ∈ G14.sigOrders n`. -/
theorem chain_words (D : Data ι) (n : ℕ) : ∀ k : ℕ,
    ((G14.words n k).map D.chain).sum =
      (D.Theta * ((G14.sigOrders n).map D.Sig).sum) ^ k * D.Theta
  | 0 => by simp [G14.words, Data.chain]
  | k + 1 => by
    have hc : ∀ (o : List ℕ) (l : ℕ), D.chain (o ++ [l]) = D.chain o * D.Sig l * D.Theta :=
      fun o l => by simp [Data.chain, List.foldl_append]
    have hW : ∀ W : List (List ℕ),
        ((W.flatMap fun o => (G14.sigOrders n).map fun l => o ++ [l]).map D.chain).sum =
          (W.map D.chain).sum * ((G14.sigOrders n).map D.Sig).sum * D.Theta := by
      intro W
      induction W with
      | nil => simp
      | cons o W ih =>
        rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_map]
        simp only [Function.comp_def, hc, List.sum_map_mul_right, List.sum_map_mul_left,
          List.map_cons, List.sum_cons]
        noncomm_ring
    rw [G14.words, hW, chain_words D n k, pow_succ]
    simp only [mul_assoc]

/-- The scaling order of a deterministic component ([II, Def 2.7 (i)]) is even. -/
private theorem even_kind_ord {V : Type*} {N : ℕ} (c : Comp V) (h : c.isDetKind N = true) :
    Even c.kind.ord := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ with
  | waved w => exact ⟨1, rfl⟩
  | dot => exact ⟨1, rfl⟩
  | xdot => exact ⟨0, rfl⟩
  | theta o =>
    simp only [Comp.isDetKind, labelOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    have hs : ∀ l : List ℕ, (∀ j ∈ l, j % 2 = 0) → Even l.sum := by
      intro l hl
      induction l with
      | nil => exact ⟨0, rfl⟩
      | cons j l ih =>
        rw [List.sum_cons]
        exact (Nat.even_iff.2 (hl j (List.mem_cons_self ..))).add
          (ih fun i hi => hl i (List.mem_cons_of_mem _ hi))
    obtain ⟨r, hr⟩ := hs o fun j hj => (h.2 j hj).2
    refine ⟨(r : ℤ) + 1 - o.length, ?_⟩
    simp only [Kind.ord, hr]
    push_cast
    ring
  | _ => simp [Comp.isDetKind] at h

/-- A self-energy shape of odd order is the empty sum: deterministic graphs have even order. -/
private theorem nil_of_odd {n : ℕ} {E : Expansion 2} (hE : SelfEnergyShape n E) (hn : ¬ Even n) :
    E = [] := by
  rcases E with _ | ⟨g, E⟩
  · rfl
  · exfalso
    obtain ⟨-, hdet, hord, -⟩ := hE g (List.mem_cons_self ..)
    have hs : ∀ l : List (Comp (Atom 2 g.1)), l.all (Comp.isDetKind (n - 1)) = true →
        Even (l.map fun c => c.kind.ord).sum := by
      intro l hl
      induction l with
      | nil => exact ⟨0, rfl⟩
      | cons c l ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hl
        rw [List.map_cons, List.sum_cons]
        exact (even_kind_ord c hl.1).add (ih hl.2)
    have hev : Even g.2.ord := (hs _ hdet).sub (even_two_mul _)
    rw [hord] at hev
    exact hn ((Int.even_coe_nat n).1 hev)

/-- `Σ̃^{(n)}` is the sum of the matrices `Σ_l`, `l ∈ G14.sigOrders n`, on a record whose matrix of
order `n` is the value of `E` (for odd `n`, `E` is empty). -/
theorem sigTilde_eq {n : ℕ} (hn : 3 ≤ n) {Sig : ℕ → Expansion 2} {E : Expansion 2}
    (hE : SelfEnergyShape n E) {D : Data ι}
    (hc : SigConsistent (Function.update Sig n E) (n + 1) D) :
    sigTilde n E D = ((G14.sigOrders n).map D.Sig).sum := by
  rw [← List.sum_toFinset _ (Words.nodup_sigOrders n)]
  by_cases hev : Even n
  · have h2 : n % 2 = 0 := Nat.even_iff.1 hev
    have hset : (G14.sigOrders n).toFinset = insert n ((Finset.Ico 4 n).filter Even) := by
      ext l
      simp only [List.mem_toFinset, Words.mem_sigOrders, Finset.mem_insert, Finset.mem_filter,
        Finset.mem_Ico, Nat.even_iff]
      omega
    rw [hset, Finset.sum_insert (by simp), hc n (by omega) (by omega) hev, Function.update_self]
    rfl
  · have hset : (G14.sigOrders n).toFinset = (Finset.Ico 4 n).filter Even := by
      ext l
      simp only [List.mem_toFinset, Words.mem_sigOrders, Finset.mem_filter, Finset.mem_Ico,
        Nat.even_iff]
      rw [Nat.even_iff] at hev
      omega
    rw [hset, nil_of_odd hE hev]
    ext x y
    simp [sigTilde, Expansion.val]

/-- The value of `T_{x,⊕⊖}` ([I, (2.4)]): `|m|² Σ_α s_{xα} G_{α⊕} Ḡ_{α⊖}`. -/
private theorem tGraph_valR (PF : PFamily Ω ι) (Dt : Ω → Data ι) (x b₁ b₂ : ι) (ω : Ω) :
    tGraph.valR PF Dt ![x, b₁, b₂] ω =
      ∑ a, (Dt ω).m * star (Dt ω).m *
        ((Dt ω).S x a * ((Dt ω).Gm ∅ a b₁ * star ((Dt ω).Gm ∅ a b₂))) := by
  unfold Graph.valR
  rw [sum_fin_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [termR_of_labelFree _ (by simp [tGraph, mkC])]
  simp [tGraph, mkC, Comp.val, Coeff.eval, CVar.eval, Charge.apply]

/-- The value of the remainder ([II, (6.1)–(6.3)]): on every record with the model relations whose
self-energy matrices of even order `≤ n` are the values of `Sig` with `Σ_n = E`, the value of
`rem n K` is `Σ_x ((Θ Σ̃^{(n)})^{K+1})_{⊗x} T_{x,⊕⊖}`. -/
theorem valR_rem {n K : ℕ} (hn : 3 ≤ n) {Sig : ℕ → Expansion 2} {E : Expansion 2}
    (hE : SelfEnergyShape n E) (PF : PFamily Ω ι) (Dt : Ω → Data ι) (hadm : modelAdm Ω ι PF Dt)
    (hc : ∀ ω, SigConsistent (Function.update Sig n E) (n + 1) (Dt ω)) (e : Fin 3 → ι) (ω : Ω) :
    (rem n K).valR PF Dt e ω = ∑ x, (((Dt ω).Theta * sigTilde n E (Dt ω)) ^ (K + 1)) (e 0) x *
      tGraph.valR PF Dt ![x, e 1, e 2] ω := by
  obtain ⟨A⟩ := hadm
  set S := (Dt ω).S with hS
  set Θ := (Dt ω).Theta with hΘdef
  set c := (Dt ω).m * star (Dt ω).m with hcdef
  set Φ : ι → ℂ := fun a => (Dt ω).Gm ∅ a (e 1) * star ((Dt ω).Gm ∅ a (e 2)) with hΦ
  set M := (Θ * sigTilde n E (Dt ω)) ^ (K + 1) with hMdef
  set P := ∑ o ∈ (G14.words n (K + 1)).toFinset, (Dt ω).chain o with hPdef
  have hP : P = M * Θ := by
    rw [hPdef, List.sum_toFinset _ (Words.nodup_words n (K + 1)), chain_words, hMdef,
      sigTilde_eq hn hE (hc ω)]
  have hcc : c = ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcdef, A.data_m ω, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hΘ := A.data_Theta ω
  rw [← hcc] at hΘ
  have hcS : c • S = Θ - c • (Θ * S) := by
    rw [← hΘ, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  have hM : M * (c • S) = P - c • (P * S) := by
    rw [hcS, Matrix.mul_sub, Matrix.mul_smul, hP, Matrix.mul_assoc]
  have hkey : ∀ a, ∑ x, M (e 0) x * (c * S x a) = P (e 0) a - c * ∑ b, P (e 0) b * S b a := by
    intro a
    have := congrFun (congrFun hM (e 0)) a
    simpa [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using this
  have hL : (rem n K).valR PF Dt e ω =
      ∑ a, P (e 0) a * Φ a - c * ∑ b, ∑ a, P (e 0) b * S b a * Φ a := by
    rw [rem, valR_flatMap]
    simp only [forms_valR]
    rw [← List.sum_toFinset _ (Words.nodup_words n (K + 1)), Finset.sum_sub_distrib]
    simp only [hPdef, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_comm
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
  calc (rem n K).valR PF Dt e ω
      = ∑ a, P (e 0) a * Φ a - c * ∑ b, ∑ a, P (e 0) b * S b a * Φ a := hL
    _ = ∑ a, (P (e 0) a - c * ∑ b, P (e 0) b * S b a) * Φ a := by
      rw [Finset.sum_comm (f := fun b a => P (e 0) b * S b a * Φ a)]
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    _ = ∑ a, (∑ x, M (e 0) x * (c * S x a)) * Φ a := by simp only [hkey]
    _ = _ := by
      simp only [tGraph_valR, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => ?_
      ring

end Value

end Remainder

/-- The remainder `(Θ Σ̃^{(n)})^{K+1} T` of the `K`-fold iteration of [II, (3.5)] as a formal sum
of the graphs `Θ^{[o]}_{⊗y} (Σ_l)_{yx} T_{x,⊕⊖}` (`|o| = K`) in `O_dot` form: for `n < D ≤ 2K`
it has the value `Σ_x ((Θ Σ̃^{(n)})^{K+1})_{⊗x} T_{x,⊕⊖}` on every record with the model
relations whose self-energy matrices of even order `≤ n` are the values of `Sig` with
`Σ_n = E`, and as `Err` of a record it has the properties of [II, Def 3.2] (order `> D`) and of
[II, Def 6.3]. -/
def G14.remainderStmt : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (E : Expansion 2) (D K : ℕ), n < D → D ≤ 2 * K →
    SelfEnergyShapesUpTo Sig (n - 1) → SelfEnergyShape n E →
    ∃ Rem : Expansion 3,
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
        modelAdm Ω ι PF Dt → (∀ ω, SigConsistent (Function.update Sig n E) (n + 1) (Dt ω)) →
        ∀ (e : Fin 3 → ι) (ω : Ω),
          Rem.valR PF Dt e ω = ∑ x, (((Dt ω).Theta * sigTilde n E (Dt ω)) ^ (K + 1)) (e 0) x *
            tGraph.valR PF Dt ![x, e 1, e 2] ω) ∧
      (⟨[], [], [], Rem⟩ : TRec).Shape n n D ∧ (⟨[], [], [], Rem⟩ : TRec).Def63

/-- **The remainder of the iterated `T`-equation** (`G14.remainderStmt`, [II, (6.1)–(6.3)]): the
formal sum `Remainder.rem n K` of the `O_dot` forms of `Θ^{[o]}_{⊗α} G_{α⊕} Ḡ_{α⊖}` and
`−|m|² Θ^{[o]}_{⊗β} s_{βα} G_{α⊕} Ḡ_{α⊖}` over the words `o` of length `K + 1`, of scaling order
`≥ 2K + 4`. -/
theorem G14.remainder_stmt : G14.remainderStmt := by
  intro n hn Sig E D K _ hDK _ hE
  exact ⟨Remainder.rem n K, fun Ω ι _ _ PF Dt hadm hc e ω =>
    Remainder.valR_rem hn hE PF Dt hadm hc e ω, Remainder.shape_rem hDK, Remainder.def63_rem⟩

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end Instances

end RBM8D
