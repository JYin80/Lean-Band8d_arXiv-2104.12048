module

public import RBM8D.TExp.Defs

@[expose] public section

/-!
# The second order `T`-expansion

`H(2)` ([I, Lemma 2.5] = [II, (3.8)–(3.10)]) with [II, Def 6.3] in the block reading.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section Helpers

instance instDecTKinds {k n : ℕ} (N : ℕ) (Γ : Graph k n) : Decidable (Γ.TKinds N) :=
  inferInstanceAs (Decidable (_ = true))

instance instDecAtExternals {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.AtExternals :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance instDecLabelFree {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelFree :=
  inferInstanceAs (Decidable (∀ c ∈ Γ.comps, c.label = none))

instance instDecIsQGraph {k n : ℕ} (Γ : Graph k n) : Decidable Γ.IsQGraph :=
  inferInstanceAs (Decidable (∃ u : Atom k n, (∃ c ∈ Γ.comps, c.label = some (.Q, u)) ∧
    ∀ c ∈ Γ.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) → c.label = some (.Q, u)))

/-- A graph whose internal atoms lie in one molecule is doubly connected, with empty nets. -/
private theorem doublyConnected_of_spans_empty {k n : ℕ} (Γ : Graph k n) (h : Γ.Spans ∅) :
    Γ.DoublyConnected :=
  ⟨∅, ∅, Finset.disjoint_empty_left _, by simp, by simp, h, h⟩

/-- A molecular multigraph with at most one internal vertex has no proper isolated subset: the
only proper subset is `∅`, which is not isolated. -/
private theorem noProperIso_of_card_le_one {V E : Type} {G : MGraph V E} (hc : G.int.card ≤ 1) :
    ∀ Q, ¬ G.IsProperIso G.int Q := by
  rintro Q ⟨⟨hQ, e₁, e₂, -, hcross⟩, hlt⟩
  have hQe : Q = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    obtain ⟨w, hw, hwQ⟩ := Finset.exists_of_ssubset hlt
    exact hwQ (Finset.card_le_one.1 hc w hw v (hQ hv) ▸ hv)
  subst hQe
  obtain ⟨-, -, -, -, hc'⟩ := (hcross e₁).2 (Or.inl rfl)
  simp [MGraph.Cut] at hc'

/-- A decidable sufficient condition for the `Q`-label condition: every `Q`-label is at an
internal atom and all internal atoms lie in one molecule, or at `⊕`/`⊖` in a graph without
internal atoms. -/
private def QLabelCrit {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∀ c ∈ Γ.comps, ∀ u, c.label = some (.Q, u) →
    (u.isRight = true ∧ ∀ b c : Fin n, Γ.SameMol (.inr b) (.inr c)) ∨
      ((u = .inl 1 ∨ u = .inl 2) ∧ n = 0)

/-- The graph properties of [II, Def 3.2] hold for the second order `T`-expansion at order `2`,
with labels in `[4, N]` for `N = 1, 2`, for every error order `D`. -/
private theorem h2Rec_shape (N : ℕ) (hN : N = 1 ∨ N = 2) (D : ℕ) : h2Rec.Shape N 2 D := by
  have h1 : ∀ g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err,
      g.2.Normal 12 ∧ g.2.TKinds 1 ∧ g.2.TKinds 2 ∧ g.2.AtExternals ∧ g.2.Spans ∅ := by
    decide
  have hA : ∀ g ∈ h2Rec.A, g.2.LabelFree ∧ ((2 : ℕ) : ℤ) < g.2.ord := by decide
  have hQ : ∀ g ∈ h2Rec.Q, g.2.IsQGraph ∧ 2 ≤ g.2.ord := by decide
  refine ⟨⟨fun g hg => ?_, fun g hg => by simp [h2Rec] at hg⟩, fun g hg => by simp [h2Rec] at hg,
    hA, hQ, fun g hg => by simp [h2Rec] at hg⟩
  obtain ⟨hn, hk1, hk2, he, hs⟩ := h1 g (List.mem_append_left _ hg)
  exact ⟨⟨12, hn⟩, by rcases hN with rfl | rfl <;> assumption, he,
    doublyConnected_of_spans_empty _ hs⟩

/-- [II, Def 3.3 (4)] with the bound `C` on the size of `𝒢`. -/
def ThetaRootedC {n : ℕ} (C : ℕ) (Γ : Graph 3 n) : Prop :=
  ∃ (j : Fin Γ.comps.length) (v : Atom 3 n), v ≠ .inl 0 ∧
    Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧ Γ.comps[j].label = none ∧
    (Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y = v) ∧
    (∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0)) ∧
    ((Γ.dropComp j).rootGraph v).2.Normal C

set_option synthInstance.maxSize 512 in
instance instDecThetaRootedC {n : ℕ} (C : ℕ) (Γ : Graph 3 n) :
    Decidable (ThetaRootedC C Γ) := by
  unfold ThetaRootedC
  infer_instance

private theorem h2Rec_root : ∀ g ∈ h2Rec.A ++ h2Rec.Q, g.2.ThetaRooted := by
  have h : ∀ g ∈ h2Rec.A ++ h2Rec.Q, ThetaRootedC 12 g.2 := by decide
  intro g hg
  obtain ⟨j, v, h1, h2, h3, h4, h5, h6, h7⟩ := h g hg
  exact ⟨j, v, h1, h2, h3, h4, h5, h6, 12, h7⟩

private theorem valR_append {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (E F : Expansion k)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    (E ++ F).valR PF D e ω = E.valR PF D e ω + F.valR PF D e ω := by
  simp [Expansion.valR, List.map_append, List.sum_append]

private theorem valR_nil {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) (ω : Ω) :
    Expansion.valR ([] : Expansion k) PF D e ω = 0 := rfl

private theorem valR_flatMap_oDot {Ω ι : Type} [Fintype ι]
    [DecidableEq ι] (E : Expansion 3) (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin 3 → ι)
    (ω : Ω) :
    Expansion.valR (E.flatMap fun g => oDot g.2) PF D e ω = E.valR PF D e ω := by
  induction E with
  | nil => rfl
  | cons g E ih =>
    rw [List.flatMap_cons, valR_append, ih]
    have h1 := congrFun (oDot_value 3 g.1 Ω ι PF D trivial g.2 e) ω
    rw [h1]
    simp [Expansion.valR]

/-- The identity [II, (3.1)] at order `2` for the second order `T`-expansion follows from
[I, Lemma 2.5] and the value identity of `O_dot`. -/
private theorem h2Rec_identity (Sig : ℕ → Expansion 2) : h2Rec.Identity Sig 2 := by
  intro Ω ι _ _ PF D hA _ e ω
  have hsplit : secondOrderExp =
      leadExp ++ (secondOrderExp.drop 1).take 2 ++ secondOrderExp.drop 3 := rfl
  have hS : sigmaTExp 2 = [] := by decide
  rw [← congrFun (secondOrderT Ω ι PF D hA e) ω, hsplit]
  simp only [TRec.rhs, hS, h2Rec, valR_append, valR_nil, valR_flatMap_oDot]
  ring

/-- The plain label leaves a graph unchanged. -/
private theorem relabelRoot_nil {n : ℕ} (Γ : Graph 3 n) : Γ.relabelRoot [] = Γ := by
  rcases Γ with ⟨comps, coeff⟩
  simp only [Graph.relabelRoot, Graph.mk.injEq, and_true]
  conv_rhs => rw [← List.map_id comps]
  refine List.map_congr_left fun c _ => ?_
  split_ifs with h
  · rcases c with ⟨kind, x, y, minor, label⟩
    obtain rfl : kind = .theta [] := h.1
    rfl
  · rfl

/-- The identity [II, (3.11)] at order `2` for the second order `T`-equation: `Σ̃^{(2)} = 0`, and
the identity is [II, (3.1)] at order `2`. -/
private theorem h2TEq_identity (Sig : ℕ → Expansion 2) : h2TEq.Identity Sig 2 := by
  intro Ω ι _ _ PF D hA _ e ω
  have hsig : ∀ D' : Data ι, sigTilde 2 [] D' = 0 := by
    intro D'
    rw [sigTilde, Finset.Ico_eq_empty_of_le (by norm_num : 2 ≤ 4)]
    ext x y
    simp [Expansion.val]
  have hS : sigmaTExp 2 = [] := by decide
  have h := h2Rec_identity Sig Ω ι PF D hA
    (fun _ k hk hk3 _ => absurd (hk.trans_lt hk3) (by norm_num)) e ω
  simp only [TRec.rhs, hS, List.append_nil] at h
  simp only [h2TEq, hsig, Matrix.mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]
  exact h.symm

/-- The graphs of order `≤ 2` of the solved second order `T`-equation are those of `h2Rec`. -/
private theorem h2TEq_solveLow : TRec.Coherent 2 (h2TEq.solveLow 2) h2Rec := by
  have hc : chainLabels 2 = [] := by decide
  have hR : (h2TEq.solveLow 2).R = h2Rec.R := rfl
  have hQ : (h2TEq.solveLow 2).Q = h2Rec.Q := by
    simp only [TEqRec.solveLow, h2TEq, hc, relabelRoot_nil, List.map_cons, List.map_nil,
      Sigma.eta]
    exact List.flatMap_singleton' _
  exact fun j _ => ⟨by rw [hR], by rw [hQ]⟩

/-- The solved record of the second order `T`-equation, with `A` kept, is the second order
`T`-expansion: there is no label of order `≤ 2`. -/
private theorem h2TEq_solvePM : h2TEq.solvePM 2 = h2Rec := by
  have hc : chainLabels 2 = [] := by decide
  have hQ : h2TEq.Q.flatMap (fun g => ([] :: chainLabels 2).map
      fun o => (⟨g.1, g.2.relabelRoot o⟩ : Σ n, Graph 3 n)) = h2Rec.Q := by
    simp only [h2TEq, hc, relabelRoot_nil, List.map_cons, List.map_nil, Sigma.eta]
    exact List.flatMap_singleton' _
  simp only [TEqRec.solvePM, TEqRec.solveLow, hQ]
  rfl

instance Second_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

instance Second_decColourInv' {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.ColourInv' := by
  unfold Graph.ColourInv'; infer_instance

instance Second_decColourInvB {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.ColourInvB := by
  unfold Graph.ColourInvB; infer_instance

set_option synthInstance.maxSize 4000 in
instance Second_decExtClause {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.ExtClause := by
  unfold Graph.ExtClause Graph.HasDiffToPinned Graph.DiffToPinned; infer_instance

/-- A molecular multigraph without proper isolated subset of its internal vertices has all its
internal vertices in the minimal isolated subset. -/
private theorem Second_mis_eq {V E : Type} (G : MGraph V E) (h : ∀ Q, ¬ G.IsProperIso G.int Q) :
    G.MIS = G.int := by
  classical
  unfold MGraph.MIS
  exact Finset.filter_true_of_mem fun v _ P hP => absurd hP (h P)

instance Second_decNoLabDot {k n : ℕ} (Γ : Graph k n) : Decidable Γ.NoLabDot := by
  unfold Graph.NoLabDot; infer_instance

instance Second_decRgCheck {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.RgCheck := by
  unfold Graph.RgCheck; infer_instance

instance Second_decAdjDot {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

/-- The number of blocks of dotted edges, for the adjacency `Second_decAdjDot`. -/
private def Second_ccN {k n : ℕ} (Γ : Graph k n) : ℕ :=
  haveI := Second_decAdjDot Γ
  Fintype.card Γ.dotGraph.ConnectedComponent

/-- The dot excess with the number of blocks `Second_ccN`. -/
private theorem Second_dotExcess_eq {k n : ℕ} (Γ : Graph k n) :
    Γ.dotExcess = (Γ.nDots : ℤ) - ((k + n : ℕ) : ℤ) + (Second_ccN Γ : ℤ) := by
  unfold Graph.dotExcess Second_ccN
  rw [Fintype.card_eq_nat_card]

/-- Dot excess `0`, as a boolean. -/
private def Second_dexB {k n : ℕ} (Γ : Graph k n) : Bool :=
  decide ((Γ.nDots : ℤ) - ((k + n : ℕ) : ℤ) + (Second_ccN Γ : ℤ) = 0)

private theorem Second_dotExcess_of {k n : ℕ} {Γ : Graph k n} (h : Second_dexB Γ = true) :
    Γ.dotExcess = 0 := by
  rw [Second_dotExcess_eq]
  simpa [Second_dexB] using h

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
/-- [II, Def 6.3] in the block reading, with the clauses on the dotted edges, the labels, the
orders and the rooting, for the second order `T`-expansion: `R` and `Err` are empty; the internal
atoms of each graph of `A` and `Q` lie in one molecule, so these graphs are sequentially
pre-deterministic, and the `⊕/⊖`-recollision graphs of `A` globally standard, in the block reading;
every graph of `A`, and every graph of `Q` with an internal atom, satisfies the clause on the
external atoms and the charge pattern of the block normal form, and the two graphs of `Q` without
internal atoms have the `Θ` edge `Θ_{⊗⊕}` (`Graph.RootAtPlus`); the `Q`-label of each graph of `Q`
is at an internal atom, whose molecule is the only internal vertex of the molecular graph, or at
`⊕` or `⊖` in a graph without internal atoms, and in the two graphs of `Q` without internal atoms
it is at `⊕` (`Graph.QLabelAtPlus`); every graph has only the `Θ` edge at `⊗`, dot excess
`0`, no labelled dotted or `×`-dotted edge and at most one label; the two graphs of `A` in which
`⊕`, `⊖` lie in one dotted block have scaling order `5`, the four such graphs of `Q` scaling
orders `4, 4, 5, 4`; every graph of `Q` satisfies `Graph.RgCheck`; every graph of `A` and `Q` with
an internal atom that is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` is rooted at the external
atoms; every graph of `R`, `A`, `Q` is plain (`Graph.Plain`); the graphs of `A` and `Q` without an
internal atom have the profile at `⊖` (`Graph.MinusProfile`). -/
theorem h2Rec_def63 : h2Rec.Def63 := by
  have hA : ∀ g ∈ h2Rec.A, (∀ b c : Fin g.1, g.2.SameMol (.inr b) (.inr c)) ∧
      g.2.ExtClause ∧ g.2.ColourInvB := by
    decide +kernel
  have hQ : ∀ g ∈ h2Rec.Q, (∀ b c : Fin g.1, g.2.SameMol (.inr b) (.inr c)) ∧
      g.2.toMG'.int.card ≤ 1 ∧ ∀ c ∈ g.2.comps, ∀ u, c.label = some (.Q, u) →
        g.2.molRep u ∈ g.2.toMG'.int ∨ ((u = .inl 1 ∨ u = .inl 2) ∧ g.1 = 0) := by
    decide +kernel
  have hC : ∀ g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err, g.2.TensorDiffusive ∧
      Second_dexB g.2 = true ∧ g.2.NoLabDot ∧ g.2.labels.length ≤ 1 := by
    decide +kernel
  have hPM : (∀ g ∈ h2Rec.R ++ h2Rec.A, g.2.PMBlock → 5 ≤ g.2.ord) ∧
      (∀ g ∈ h2Rec.Q, g.2.PMBlock → 4 ≤ g.2.ord) ∧
      (∀ g ∈ h2Rec.Q ++ h2Rec.Err, g.2.RgCheck) := by
    decide +kernel
  have hRt : ∀ g ∈ h2Rec.A ++ h2Rec.Q ++ h2Rec.Err, g.1 ≠ 0 → ¬ g.2.DiagRecoll →
      g.2.RootedAtExt := by
    decide +kernel
  have hQx : ∀ g ∈ h2Rec.Q, (g.1 = 0 ∧ g.2.RootAtPlus) ∨ g.2.ExtClause ∧ g.2.ColourInvB := by
    decide +kernel
  have hPl : ∀ g ∈ h2Rec.R ++ h2Rec.A ++ h2Rec.Q, g.2.Plain := by
    decide +kernel
  have hL : ∀ g ∈ h2Rec.Q, g.1 = 0 → g.2.QLabelAtPlus := by
    decide +kernel
  have hMP : ∀ g ∈ h2Rec.A ++ h2Rec.Q, g.1 = 0 → g.2.MinusProfile := by
    decide +kernel
  refine ⟨⟨fun g hg => by simp [h2Rec] at hg, fun g hg => ⟨spdPM'_of_oneMol _ _ _ (hA g hg).1,
    Or.inr (hA g hg).2⟩, fun g hg => ⟨spdPM'_of_oneMol _ _ _ (hQ g hg).1, fun c hc u hu => ?_,
      hQx g hg⟩⟩, fun g hg => ?_, fun g hg _ => gsPM'_of_oneMol _ _ _ (hA g hg).1, hPM.1,
    hPM.2.1, hPM.2.2, hRt, hPl, hL, hMP⟩
  · rw [Second_mis_eq _ (noProperIso_of_card_le_one (hQ g hg).2.1)]
    rcases (hQ g hg).2.2 c hc u hu with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hC g hg
    exact ⟨h1, Second_dotExcess_of h2, h3, h4⟩

/-- The second order `T`-expansion is a `T`-expansion of order `2` with every error order
`D > 2`, given [I, Lemma 2.5] and the value identity of `O_dot`. -/
private theorem h2Rec_struct (Sig : ℕ → Expansion 2) (D : ℕ) (hD : 2 < D) :
    h2Rec.IsTExpStruct Sig 2 D :=
  ⟨hD, h2Rec_identity Sig, fun j hj hj' => absurd (hj.trans hj') (by norm_num),
    h2Rec_shape 2 (Or.inr rfl) D, h2Rec_def63⟩

/-- The second order `T`-equation is a `T`-equation of order `2` with every error order `D > 2`,
given [I, Lemma 2.5] and the value identity of `O_dot`. -/
private theorem h2TEq_struct (Sig : ℕ → Expansion 2) (D : ℕ) (hD : 2 < D) :
    h2TEq.IsTEqStruct Sig 2 D := by
  refine ⟨hD, h2TEq_identity Sig, fun j hj hj' => absurd (hj.trans hj') (by norm_num),
    fun g hg => by simp [h2TEq] at hg, h2Rec_shape 1 (Or.inl rfl) D, ?_, h2Rec_def63⟩
  intro g hg
  have hR : h2Rec.R = [] := rfl
  have hE : h2Rec.Err = [] := rfl
  simp only [h2TEq, hR, hE, List.nil_append, List.append_nil] at hg
  exact h2Rec_root g hg

/-- The families of `H(2)`: the second order `T`-equation and `T`-expansion for every error
order, for every construction `Strat` (the provenance clause starts at order `3`). -/
private theorem h2Fam (Strat : ℕ → ℕ → TRec → TEqRec) (Sig : ℕ → Expansion 2) :
    HFam Strat Sig 2 (fun _ _ => h2TEq) (fun _ _ => h2Rec) := by
  refine ⟨fun k D hk hk' hkD => ?_, fun k D hk hk' _ => by omega,
    fun k k' D _ _ _ _ => ⟨fun j _ => ⟨List.Perm.refl _, List.Perm.refl _⟩,
      fun j _ => ⟨List.Perm.refl _, List.Perm.refl _⟩, fun j _ => List.Perm.refl _⟩,
    fun k D D' _ _ _ _ => ⟨fun j _ => ⟨List.Perm.refl _, List.Perm.refl _, List.Perm.refl _,
      List.Perm.refl _⟩, fun j _ => ⟨List.Perm.refl _, List.Perm.refl _, List.Perm.refl _,
      List.Perm.refl _⟩⟩, fun D _ _ => rfl, fun k D hk hk' _ => by omega⟩
  obtain rfl : k = 2 := by omega
  refine ⟨h2TEq_struct Sig D hkD, h2Rec_struct Sig D hkD, h2TEq_solveLow, fun j _ => ?_⟩
  rw [h2TEq_solvePM]


end Helpers

/-- **[I, Lemma 2.5] = [II, (3.8)–(3.10)]**: `H(2)` holds for every dimension `d`, every family of
variance matrices `Svar`, every construction `Strat` and every family of self-energies `Sig`. The
second order `T`-equation is `h2TEq` and the second order `T`-expansion is `h2Rec` for every error
order `D > 2`: the identity [II, (3.1)] is [I, Lemma 2.5] followed by the value identity of `O_dot`
([I, Lemma 3.3]); [II, Def 6.3] holds in the block reading; the self-energy and provenance
clauses of `HFam` are empty at order `2`. -/
theorem h2 :
  ∀ (d : ℕ) (Svar : VarFamily d) (Strat : ℕ → ℕ → TRec → TEqRec) (Sig : ℕ → Expansion 2),
    HWith d Svar Strat Sig 2 := by
  intro d Svar Strat Sig
  exact ⟨fun _ hk hk' => absurd (hk.trans hk') (by norm_num), _, _, h2Fam Strat Sig⟩

section Examples

section QNoExt

end QNoExt

section RootAtPlusRecord

end RootAtPlusRecord

section PlainRecord

end PlainRecord

section LabelAtPlusRecord

end LabelAtPlusRecord

end Examples

end RBM8D.Graphs
