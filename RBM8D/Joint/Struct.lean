import RBM8D.Joint.Overflow
import RBM8D.TExp.Second

/-!
# The solved `T`-equation: graph properties, coherence and the error order

For an `n`-th order `T`-equation `𝒬` ([II, Def 3.3]) with error order `D ≤ 2K`, the record
`G14.solveRec n K 𝒬 Rem` of the `K`-fold iteration of [II, (3.5)] ([II, (6.1)–(6.3)]) is built from
the graphs of `𝒬` with their `Θ` edge at `⊗` relabelled by words in the even orders `4, …, n`
(`Σ_x Θ_{⊗x} 𝒢_x`, `G14.RootedTheta`), the `O_dot` forms of the leading graphs beyond `Σ_T^{(n)}`
(`G14.overflow`) and the remainder `Rem`. This file proves the three statements

* `G14.solveRec_struct`: the properties of [II, Def 3.2] at order `n` with labels in `[4, n]` and of
  [II, Def 6.3] (`TRec.Shape`, `TRec.Def63`);
* `G14.solveRec_coherent`: [II, Def 3.2 (7)] and its dotted-block form (`TRec.Coherent`,
  `TRec.CoherentPM`);
* `G14.solveRec_agree`: the graphs of order `≤ D` do not depend on the error order
  (`TRec.AgreeTo`, [II, Def 3.2 (8)]).

The proofs read of `TEqRec.IsTEqStruct` only `n < D`, the properties of [II, Def 3.2] with labels in
`[4, n - 1]`, the form `Σ_x Θ_{⊗x} 𝒢_x` of every graph and `TRec.Def63` (`Struct.Parts`). The
properties of one graph of each formal sum are `Struct.GoodR`, `Struct.GoodA`, `Struct.GoodQ`,
`Struct.GoodErr`: relabelling keeps them (`G14.relabel`), the graphs of `R` of order `> n` are
globally standard `⊕/⊖`-recollision graphs and so fit the clauses on `A`, and the `O_dot` forms
come from `G14.overflow_stmt`. A word of `G14.extra n K` raises the order by at least `n - 1`, and
a word of length `> K` by at least `2K + 2`, which gives the coherence and the independence of the
iteration number.
-/

noncomputable section

namespace RBM8D

open Graphs

namespace Struct

/-! ## What the solution reads of a `T`-equation -/

/-- What the solution of an `n`-th order `T`-equation `𝒬` with error order `D` reads of
`TEqRec.IsTEqStruct`: `n < D`, the properties of [II, Def 3.2] with labels in `[4, n - 1]`, the
form `Σ_x Θ_{⊗x} 𝒢_x` of every graph, and [II, Def 6.3]. -/
structure Parts (n D : ℕ) (𝒬 : TEqRec) : Prop where
  lt : n < D
  shape : 𝒬.toTRec.Shape (n - 1) n D
  root : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, G14.RootedTheta g.2
  def63 : 𝒬.toTRec.Def63

/-- `TEqRec.IsTEqStruct` gives the parts that the solution reads. -/
theorem Parts.of_struct {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec}
    (h : 𝒬.IsTEqStruct Sig n D) : Parts n D 𝒬 :=
  ⟨h.1, h.2.2.2.2.1, fun g hg => G14.rootedTheta_of_thetaRooted (h.2.2.2.2.2.1 g hg),
    h.2.2.2.2.2.2⟩

/-- Every graph of `R` of the `T`-equation is of the form `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem Parts.rootR {n D : ℕ} {𝒬 : TEqRec} (hp : Parts n D 𝒬) : ∀ g ∈ 𝒬.R, G14.RootedTheta g.2 :=
  fun g hg => hp.root g (by simp [hg])

/-- Every graph of `A` of the `T`-equation is of the form `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem Parts.rootA {n D : ℕ} {𝒬 : TEqRec} (hp : Parts n D 𝒬) : ∀ g ∈ 𝒬.A, G14.RootedTheta g.2 :=
  fun g hg => hp.root g (by simp [hg])

/-- Every graph of `Q` of the `T`-equation is of the form `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem Parts.rootQ {n D : ℕ} {𝒬 : TEqRec} (hp : Parts n D 𝒬) : ∀ g ∈ 𝒬.Q, G14.RootedTheta g.2 :=
  fun g hg => hp.root g (by simp [hg])

/-- Every graph of `Err` of the `T`-equation is of the form `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem Parts.rootErr {n D : ℕ} {𝒬 : TEqRec} (hp : Parts n D 𝒬) :
    ∀ g ∈ 𝒬.Err, G14.RootedTheta g.2 :=
  fun g hg => hp.root g (by simp [hg])

/-! ## The properties of one graph of each formal sum -/

/-- The clauses of [II, Def 3.2] and [II, Def 6.3] on a graph of `R`. -/
def GoodR (N n m : ℕ) (Γ : Graph 3 m) : Prop :=
  ((∃ C, Γ.Normal C) ∧ Γ.TKinds N ∧ Γ.AtExternals ∧ Γ.DoublyConnected) ∧
  (Γ.LabelFree ∧ Γ.IsRecollision {1, 2} ∧ 3 ≤ Γ.ord ∧ Γ.ord ≤ (n : ℤ)) ∧
  (gsPM' Γ ∧ Γ.ExtClause ∧ Γ.ColourInvB) ∧
  (Γ.TensorDiffusive ∧ Γ.dotExcess = 0 ∧ Γ.NoLabDot ∧ Γ.labels.length ≤ 1) ∧
  (Γ.PMBlock → 5 ≤ Γ.ord) ∧ Γ.Plain

/-- The clauses of [II, Def 3.2] and [II, Def 6.3] on a graph of `A` (`m` internal atoms). -/
def GoodA (N n m : ℕ) (Γ : Graph 3 m) : Prop :=
  ((∃ C, Γ.Normal C) ∧ Γ.TKinds N ∧ Γ.AtExternals ∧ Γ.DoublyConnected) ∧
  (Γ.LabelFree ∧ (n : ℤ) < Γ.ord) ∧
  (spdPM' Γ ∧ ((m = 0 ∧ Γ.RootAtPlus) ∨ Γ.ExtClause ∧ Γ.ColourInvB)) ∧
  (Γ.TensorDiffusive ∧ Γ.dotExcess = 0 ∧ Γ.NoLabDot ∧ Γ.labels.length ≤ 1) ∧
  (Γ.IsRecollision {1, 2} → gsPM' Γ) ∧ (Γ.PMBlock → 5 ≤ Γ.ord) ∧
  (m ≠ 0 → ¬ Γ.DiagRecoll → Γ.RootedAtExt) ∧ Γ.Plain ∧ (m = 0 → Γ.MinusProfile)

/-- The clauses of [II, Def 3.2] and [II, Def 6.3] on a graph of `Q` (`m` internal atoms). -/
def GoodQ (N m : ℕ) (Γ : Graph 3 m) : Prop :=
  ((∃ C, Γ.Normal C) ∧ Γ.TKinds N ∧ Γ.AtExternals ∧ Γ.DoublyConnected) ∧
  (Γ.IsQGraph ∧ 2 ≤ Γ.ord) ∧
  (spdPM' Γ ∧ Γ.QLabelInMISB ∧ ((m = 0 ∧ Γ.RootAtPlus) ∨ Γ.ExtClause ∧ Γ.ColourInvB)) ∧
  (Γ.TensorDiffusive ∧ Γ.dotExcess = 0 ∧ Γ.NoLabDot ∧ Γ.labels.length ≤ 1) ∧
  (Γ.PMBlock → 4 ≤ Γ.ord) ∧ Γ.RgCheck ∧ (m ≠ 0 → ¬ Γ.DiagRecoll → Γ.RootedAtExt) ∧
  Γ.Plain ∧ (m = 0 → Γ.QLabelAtPlus) ∧ (m = 0 → Γ.MinusProfile)

/-- The clauses of [II, Def 3.2] and [II, Def 6.3] on a graph of `Err` (`m` internal atoms). -/
def GoodErr (N D m : ℕ) (Γ : Graph 3 m) : Prop :=
  ((∃ C, Γ.Normal C) ∧ Γ.TKindsErr N ∧ Γ.AtExternals ∧ Γ.DoublyConnected) ∧
  (D : ℤ) < Γ.ord ∧
  (Γ.TensorDiffusive ∧ Γ.dotExcess = 0 ∧ Γ.NoLabDot ∧ Γ.labels.length ≤ 1) ∧
  Γ.RgCheck ∧ (m ≠ 0 → ¬ Γ.DiagRecoll → Γ.RootedAtExt)

/-- `TRec.Shape` and `TRec.Def63` of a record are the clauses on each of its graphs. -/
theorem good_iff (N n D : ℕ) (𝒯 : TRec) :
    (𝒯.Shape N n D ∧ 𝒯.Def63) ↔
      ((∀ g ∈ 𝒯.R, GoodR N n g.1 g.2) ∧ (∀ g ∈ 𝒯.A, GoodA N n g.1 g.2) ∧
        (∀ g ∈ 𝒯.Q, GoodQ N g.1 g.2) ∧ (∀ g ∈ 𝒯.Err, GoodErr N D g.1 g.2)) := by
  simp only [TRec.Shape, TRec.Def63, GoodR, GoodA, GoodQ, GoodErr, List.mem_append, or_imp,
    forall_and]
  tauto

/-! ## Relabelling the `Θ` edge at `⊗` -/

/-- The entries of a label with `labelOK N` are even in `[4, N]`, so `≥ 2`. -/
theorem entries_of_labelOK {N : ℕ} {o : List ℕ} (h : labelOK N o = true) : ∀ e ∈ o, 2 ≤ e := by
  intro e he
  have := List.all_eq_true.1 h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- The labels of `Σ_T^{(n)}` have entries even in `[4, n]`. -/
theorem labelOK_of_mem_chainLabels {n : ℕ} {o : List ℕ} (ho : o ∈ chainLabels n) :
    labelOK n o = true := by
  obtain ⟨-, h2, h3⟩ := Words.mem_chainLabels.1 ho
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro e he
  have := Words.le_labelInc_of_mem he
  have := (h2 e he).1
  exact ⟨⟨(h2 e he).1, by omega⟩, (h2 e he).2⟩

/-- The plain label and the labels of `Σ_T^{(n)}` have entries even in `[4, n]`. -/
theorem labelOK_of_mem_nil_cons {n : ℕ} {o : List ℕ} (ho : o ∈ [] :: chainLabels n) :
    labelOK n o = true := by
  rcases List.mem_cons.1 ho with rfl | ho
  · rfl
  · exact labelOK_of_mem_chainLabels ho

/-- The plain label leaves a graph unchanged. -/
theorem relabelRoot_nil {n : ℕ} (Γ : Graph 3 n) : Γ.relabelRoot [] = Γ := by
  rcases Γ with ⟨comps, coeff⟩
  simp only [Graph.relabelRoot, Graph.mk.injEq, and_true]
  conv_rhs => rw [← List.map_id comps]
  refine List.map_congr_left fun c _ => ?_
  split_ifs with h
  · rcases c with ⟨kind, x, y, minor, label⟩
    obtain rfl : kind = .theta [] := h.1
    rfl
  · rfl

/-- Relabelling by a label with `labelOK N` raises the scaling order by `Words.labelInc o`. -/
theorem ord_relabel {m N : ℕ} {Γ : Graph 3 m} (hΓ : G14.RootedTheta Γ) {o : List ℕ}
    (ho : labelOK N o = true) : (Γ.relabelRoot o).ord = Γ.ord + (Words.labelInc o : ℤ) :=
  Words.ord_relabelRoot_of_entries hΓ (entries_of_labelOK ho)

/-- Relabelling by a label with `labelOK N` does not lower the scaling order. -/
theorem le_ord_relabel {m N : ℕ} {Γ : Graph 3 m} (hΓ : G14.RootedTheta Γ) {o : List ℕ}
    (ho : labelOK N o = true) : Γ.ord ≤ (Γ.relabelRoot o).ord := by
  rw [ord_relabel hΓ ho]
  omega

/-- A graph of `R` with its `Θ` edge relabelled by a label with `labelOK n`, still of order
`≤ n`, has the clauses on a graph of `R`. -/
theorem goodR_relabel {n m : ℕ} {Γ : Graph 3 m} (hr : G14.RootedTheta Γ)
    (hg : GoodR (n - 1) n m Γ) {o : List ℕ} (ho : labelOK n o = true)
    (hle : (Γ.relabelRoot o).ord ≤ (n : ℤ)) : GoodR n n m (Γ.relabelRoot o) := by
  obtain ⟨⟨⟨C, hN⟩, hK, hAE, hDC⟩, ⟨hLF, hRec, h3, -⟩, ⟨hgs, hExt, hCol⟩,
    ⟨hTD, hDE, hNL, hlab⟩, hPM, hPl⟩ := hg
  obtain ⟨-, h2, -, h4, h5, h6, h7, -, h9, h10, -, h12, h13, -, -, h16, h17, h18, h19, h20, -, -,
    -, h24, -, -⟩ := G14.relabel Γ o hr
  have hle' := le_ord_relabel hr ho
  refine ⟨⟨⟨C, h4 C hN⟩, h2 (n - 1) n (by omega) ho hK, h5 hAE, h6 hDC⟩,
    ⟨h7 hLF, h9.2 hRec, by omega, hle⟩, ⟨h10 hgs, h12 hExt, h13 hCol⟩,
    ⟨h16 hTD, by rw [h17, hDE], h18 hNL, by rw [h19]; exact hlab⟩,
    fun h => by have := hPM (h20.1 h); omega, h24 hPl⟩

/-- A `⊕/⊖`-recollision graph ([II, Def 3.1 (i)]) is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`. -/
theorem diagRecoll_of_isRecollision {n : ℕ} {Γ : Graph 3 n} (h : Γ.IsRecollision {1, 2}) :
    Γ.DiagRecoll := by
  obtain ⟨c, hc, hk, hb⟩ := h
  have key : ∀ (b : Fin 3) (i : Fin n), (b = 1 ∨ b = 2) → Γ.SameBlock (.inl b) (.inr i) →
      Γ.DiagRecoll := by
    intro b i hb' hs
    obtain ⟨B, hB, hu, hv⟩ := (Γ.sameBlock_iff_mem_dotBlocks _ _).1 hs
    rw [Graph.DiagRecoll, List.any_eq_true]
    refine ⟨B, hB, ?_⟩
    rcases hb' with rfl | rfl <;>
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true] <;>
      exact ⟨by simp [hu], .inr i, hv, rfl⟩
  have hsb : Γ.SameBlock c.x c.y := by
    by_cases hxy : c.x = c.y
    · rw [hxy]; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
      exact ⟨hxy, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
  rcases hb with ⟨⟨b, hbB, hx⟩, hy⟩ | ⟨⟨b, hbB, hy⟩, hx⟩
  · rcases hcy : c.y with a | i
    · rw [hcy] at hy; simp at hy
    · rw [hx, hcy] at hsb
      exact key b i (by simpa using hbB) hsb
  · rcases hcx : c.x with a | i
    · rw [hcx] at hx; simp at hx
    · rw [hy, hcx] at hsb
      exact key b i (by simpa using hbB) hsb.symm

/-- A graph of `R` with its `Θ` edge relabelled by a label with `labelOK n`, of order `> n`, has
the clauses on a graph of `A`: it is globally standard, hence sequentially pre-deterministic, it
has the clauses on the external atoms, and it is a `⊕/⊖`-recollision graph, so that it is a
`⊕`-recollision graph at `𝔟₁ = 𝔟₂`. -/
theorem goodA_of_goodR {n m : ℕ} {Γ : Graph 3 m} (hr : G14.RootedTheta Γ)
    (hg : GoodR (n - 1) n m Γ) {o : List ℕ} (ho : labelOK n o = true)
    (hlt : (n : ℤ) < (Γ.relabelRoot o).ord) : GoodA n n m (Γ.relabelRoot o) := by
  obtain ⟨⟨⟨C, hN⟩, hK, hAE, hDC⟩, ⟨hLF, hRec, h3, -⟩, ⟨hgs, hExt, hCol⟩,
    ⟨hTD, hDE, hNL, hlab⟩, hPM, hPl⟩ := hg
  obtain ⟨-, h2, -, h4, h5, h6, h7, -, h9, h10, h11, h12, h13, -, -, h16, h17, h18, h19, h20, -,
    h22, -, h24, -, -⟩ := G14.relabel Γ o hr
  have hle' := le_ord_relabel hr ho
  refine ⟨⟨⟨C, h4 C hN⟩, h2 (n - 1) n (by omega) ho hK, h5 hAE, h6 hDC⟩, ⟨h7 hLF, hlt⟩,
    ⟨h11 hgs.1, Or.inr ⟨h12 hExt, h13 hCol⟩⟩,
    ⟨h16 hTD, by rw [h17, hDE], h18 hNL, by rw [h19]; exact hlab⟩, fun _ => h10 hgs,
    fun h => by have := hPM (h20.1 h); omega,
    fun _ hnd => absurd (h22.2 (diagRecoll_of_isRecollision hRec)) hnd, h24 hPl,
    fun h0 => absurd h0 (Strategy_extClause_ne_zero hExt)⟩

/-- A graph of `A` with its `Θ` edge relabelled by a label with `labelOK n` has the clauses on a
graph of `A`. -/
theorem goodA_relabel {n m : ℕ} {Γ : Graph 3 m} (hr : G14.RootedTheta Γ)
    (hg : GoodA (n - 1) n m Γ) {o : List ℕ} (ho : labelOK n o = true) :
    GoodA n n m (Γ.relabelRoot o) := by
  obtain ⟨⟨⟨C, hN⟩, hK, hAE, hDC⟩, ⟨hLF, hlt⟩, ⟨hspd, hdis⟩, ⟨hTD, hDE, hNL, hlab⟩, hrec, hPM,
    hroot, hPl, hMP⟩ := hg
  obtain ⟨-, h2, -, h4, h5, h6, h7, -, h9, h10, h11, h12, h13, -, h15, h16, h17, h18, h19, h20,
    -, h22, h23, h24, -, h26⟩ := G14.relabel Γ o hr
  have hle' := le_ord_relabel hr ho
  refine ⟨⟨⟨C, h4 C hN⟩, h2 (n - 1) n (by omega) ho hK, h5 hAE, h6 hDC⟩, ⟨h7 hLF, by omega⟩,
    ⟨h11 hspd, hdis.imp (fun h => ⟨h.1, h15 h.2⟩) (fun h => ⟨h12 h.1, h13 h.2⟩)⟩,
    ⟨h16 hTD, by rw [h17, hDE], h18 hNL, by rw [h19]; exact hlab⟩,
    fun h => h10 (hrec (h9.1 h)), fun h => by have := hPM (h20.1 h); omega,
    fun h0 hnd => h23 (hroot h0 fun hd => hnd (h22.2 hd)), h24 hPl, fun h0 => h26 (hMP h0)⟩

/-- A graph of `Q` with its `Θ` edge relabelled by a label with `labelOK n` has the clauses on a
graph of `Q`. -/
theorem goodQ_relabel {n m : ℕ} {Γ : Graph 3 m} (hr : G14.RootedTheta Γ)
    (hg : GoodQ (n - 1) m Γ) {o : List ℕ} (ho : labelOK n o = true) :
    GoodQ n m (Γ.relabelRoot o) := by
  obtain ⟨⟨⟨C, hN⟩, hK, hAE, hDC⟩, ⟨hQG, h2'⟩, ⟨hspd, hQM, hdis⟩, ⟨hTD, hDE, hNL, hlab⟩, hPM,
    hRg, hroot, hPl, hQAP, hMP⟩ := hg
  obtain ⟨-, h2, -, h4, h5, h6, -, h8, -, -, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := G14.relabel Γ o hr
  have hle' := le_ord_relabel hr ho
  refine ⟨⟨⟨C, h4 C hN⟩, h2 (n - 1) n (by omega) ho hK, h5 hAE, h6 hDC⟩, ⟨h8 hQG, by omega⟩,
    ⟨h11 hspd, h14 hQM, hdis.imp (fun h => ⟨h.1, h15 h.2⟩) (fun h => ⟨h12 h.1, h13 h.2⟩)⟩,
    ⟨h16 hTD, by rw [h17, hDE], h18 hNL, by rw [h19]; exact hlab⟩,
    fun h => by have := hPM (h20.1 h); omega, h21 hRg,
    fun h0 hnd => h23 (hroot h0 fun hd => hnd (h22.2 hd)), h24 hPl, fun h0 => h25 (hQAP h0),
    fun h0 => h26 (hMP h0)⟩

/-- A graph of `Err` with its `Θ` edge relabelled by a label with `labelOK n` has the clauses on a
graph of `Err`. -/
theorem goodErr_relabel {n D m : ℕ} {Γ : Graph 3 m} (hr : G14.RootedTheta Γ)
    (hg : GoodErr (n - 1) D m Γ) {o : List ℕ} (ho : labelOK n o = true) :
    GoodErr n D m (Γ.relabelRoot o) := by
  obtain ⟨⟨⟨C, hN⟩, hK, hAE, hDC⟩, hD, ⟨hTD, hDE, hNL, hlab⟩, hRg, hroot⟩ := hg
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -, -, -, -, -, -, -, h16, h17, h18, h19, -, h21, h22, h23,
    -, -, -⟩ := G14.relabel Γ o hr
  have hle' := le_ord_relabel hr ho
  refine ⟨⟨⟨C, h4 C hN⟩, h3 (n - 1) n (by omega) ho hK, h5 hAE, h6 hDC⟩, by omega,
    ⟨h16 hTD, by rw [h17, hDE], h18 hNL, by rw [h19]; exact hlab⟩, h21 hRg,
    fun h0 hnd => h23 (hroot h0 fun hd => hnd (h22.2 hd))⟩

/-- The `O_dot` forms of `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` for a word `o` of `G14.extra n K` have the
clauses on a graph of `A`. -/
theorem goodA_overflow {n K : ℕ} (hn : 3 ≤ n) {o : List ℕ} (ho : o ∈ G14.extra n K)
    {g : Σ m : ℕ, Graph 3 m} (hg : g ∈ oDot (thetaLabelGraph o)) : GoodA n n g.1 g.2 := by
  obtain ⟨h1, h2, h3⟩ := Words.mem_extra.1 ho
  obtain ⟨h0, ⟨C, hN⟩, hK, hAE, hDC, hLF, hord, hrec, hspd, hRP, hTD, hDE, hNL, hlab, hPM, hPl,
    hMP⟩ := G14.overflow_stmt n o hn h2 (Words.labelOK_of_mem_wordsUpTo h1 le_rfl) h3 g hg
  refine ⟨⟨⟨C, hN⟩, hK, hAE, hDC⟩, ⟨hLF, by omega⟩, ⟨hspd, Or.inl ⟨h0, hRP⟩⟩,
    ⟨hTD, hDE, hNL, hlab⟩, fun h => absurd h hrec, fun h => by have := hPM h; omega,
    fun h => absurd h0 h, hPl, fun _ => hMP⟩

/-! ## [II, Def 3.2] and [II, Def 6.3] for the solved record -/

/-- The graphs of the solved record `G14.solveRec n K 𝒬 Rem` have the clauses of [II, Def 3.2] at
order `n` with labels in `[4, n]` and of [II, Def 6.3]. -/
theorem shape_def63 {n D K : ℕ} {𝒬 : TEqRec} {Rem : Expansion 3} (hn : 3 ≤ n)
    (hp : Parts n D 𝒬) (hRs : (⟨[], [], [], Rem⟩ : TRec).Shape n n D)
    (hRd : (⟨[], [], [], Rem⟩ : TRec).Def63) :
    (G14.solveRec n K 𝒬 Rem).Shape n n D ∧ (G14.solveRec n K 𝒬 Rem).Def63 := by
  obtain ⟨gR, gA, gQ, gE⟩ := (good_iff (n - 1) n D 𝒬.toTRec).1 ⟨hp.shape, hp.def63⟩
  obtain ⟨-, -, -, gRem⟩ := (good_iff n n D ⟨[], [], [], Rem⟩).1 ⟨hRs, hRd⟩
  refine (good_iff n n D _).2 ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ (G14.relabels ([] :: chainLabels n) 𝒬.R).filter
        (fun g => decide (g.2.ord ≤ (n : ℤ))) := hg
    obtain ⟨hmem, hle⟩ := List.mem_filter.1 hg'
    obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 hmem
    exact goodR_relabel (hp.root h (by simp [hh])) (gR h hh) (labelOK_of_mem_nil_cons ho)
      (of_decide_eq_true hle)
  · intro g hg
    have hg' : g ∈ (G14.relabels ([] :: chainLabels n) 𝒬.R).filter
        (fun g => decide ((n : ℤ) < g.2.ord)) ++ G14.relabels (G14.extra n K) 𝒬.R ++
        G14.relabels (G14.wordsUpTo n K) 𝒬.A ++ G14.overflow n K := hg
    simp only [List.mem_append] at hg'
    rcases hg' with ((h1 | h2) | h3) | h4
    · obtain ⟨hmem, hlt⟩ := List.mem_filter.1 h1
      obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 hmem
      exact goodA_of_goodR (hp.root h (by simp [hh])) (gR h hh) (labelOK_of_mem_nil_cons ho)
        (of_decide_eq_true hlt)
    · obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 h2
      have hr := hp.root h (by simp [hh])
      have h3 := (gR h hh).2.1.2.2.1
      have h4 := Words.ord_relabelRoot_of_mem_extra (n := n) (K := K) hr ho
      exact goodA_of_goodR hr (gR h hh)
        (Words.labelOK_of_mem_wordsUpTo (Words.mem_extra.1 ho).1 le_rfl) (by omega)
    · obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 h3
      exact goodA_relabel (hp.root h (by simp [hh])) (gA h hh)
        (Words.labelOK_of_mem_wordsUpTo ho le_rfl)
    · obtain ⟨o, ho, hg⟩ := List.mem_flatMap.1 h4
      exact goodA_overflow hn ho hg
  · intro g hg
    have hg' : g ∈ G14.relabels ([] :: chainLabels n) 𝒬.Q ++ G14.relabels (G14.extra n K) 𝒬.Q := hg
    rcases List.mem_append.1 hg' with h1 | h2
    · obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 h1
      exact goodQ_relabel (hp.root h (by simp [hh])) (gQ h hh) (labelOK_of_mem_nil_cons ho)
    · obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 h2
      exact goodQ_relabel (hp.root h (by simp [hh])) (gQ h hh)
        (Words.labelOK_of_mem_wordsUpTo (Words.mem_extra.1 ho).1 le_rfl)
  · intro g hg
    have hg' : g ∈ G14.relabels (G14.wordsUpTo n K) 𝒬.Err ++ Rem := hg
    rcases List.mem_append.1 hg' with h1 | h2
    · obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 h1
      exact goodErr_relabel (hp.root h (by simp [hh])) (gE h hh)
        (Words.labelOK_of_mem_wordsUpTo ho le_rfl)
    · exact gRem g h2

/-! ## Coherence: the graphs of order `≤ n` and the dotted-block graphs of order `≤ n + 1` -/

/-- Relabelling by the words of `W` and summing over the graphs of `S` is, up to order, summing over
the words of `W` of the relabelled graphs of `S`. -/
theorem relabels_swap (W : List (List ℕ)) (S : Expansion 3) :
    (G14.relabels W S).Perm
      (W.flatMap fun o => S.map fun g => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m)) := by
  induction W with
  | nil => simp [G14.relabels]
  | cons o W ih =>
    simp only [G14.relabels, List.map_cons]
    refine (List.map_append_flatMap_perm S _ _).symm.trans ?_
    rw [List.flatMap_cons]
    exact ih.append_left _

/-- The graphs of `G14.relabels W S` have the order of a graph of `S` plus the excess of a word of
`W`. -/
theorem ord_of_mem_relabels {S : Expansion 3} (hS : ∀ g ∈ S, G14.RootedTheta g.2)
    {W : List (List ℕ)} (hW : ∀ o ∈ W, ∀ e ∈ o, 2 ≤ e) {g : Σ m : ℕ, Graph 3 m}
    (hg : g ∈ G14.relabels W S) :
    ∃ h ∈ S, ∃ o ∈ W, g.2.ord = h.2.ord + (Words.labelInc o : ℤ) := by
  obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 hg
  exact ⟨h, hh, o, ho, Words.ord_relabelRoot_of_entries (hS h hh) (hW o ho)⟩

/-- The words of `G14.wordsUpTo n K` have entries `≥ 2`. -/
theorem entries_of_mem_wordsUpTo {n K : ℕ} : ∀ o ∈ G14.wordsUpTo n K, ∀ e ∈ o, 2 ≤ e :=
  fun _ ho => entries_of_labelOK (Words.labelOK_of_mem_wordsUpTo ho le_rfl)

/-- The words of `G14.extra n K` have entries `≥ 2`. -/
theorem entries_of_mem_extra {n K : ℕ} : ∀ o ∈ G14.extra n K, ∀ e ∈ o, 2 ≤ e :=
  fun _ ho => entries_of_mem_wordsUpTo _ (Words.mem_extra.1 ho).1

/-- The plain label and the labels of `Σ_T^{(n)}` have entries `≥ 2`. -/
theorem entries_of_mem_nil_cons {n : ℕ} : ∀ o ∈ [] :: chainLabels n, ∀ e ∈ o, 2 ≤ e :=
  fun _ ho => entries_of_labelOK (labelOK_of_mem_nil_cons ho)

/-- No graph of order `≥ c` has order `k < c`. -/
theorem filter_ord_eq_nil {L : Expansion 3} {c k : ℤ} (hL : ∀ g ∈ L, c ≤ g.2.ord) (hk : k < c)
    (b : (Σ m : ℕ, Graph 3 m) → Bool) :
    L.filter (fun g => b g && decide (g.2.ord = k)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro g hg
  have := hL g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro _
  omega

/-- The graphs of `L` of order `k` when `k` is below the order `c` of every graph: none. -/
theorem filter_ord_eq_nil' {L : Expansion 3} {c k : ℤ} (hL : ∀ g ∈ L, c ≤ g.2.ord) (hk : k < c) :
    L.filter (fun g => decide (g.2.ord = k)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro g hg
  have := hL g hg
  simp only [decide_eq_true_eq]
  omega

/-- The graphs of order `≤ n` of `L` and those of order `> n` are the graphs of `L`, up to order,
after the filter by any predicate. -/
theorem filter_split_perm (L : Expansion 3) (n : ℕ) (F : (Σ m : ℕ, Graph 3 m) → Bool) :
    (((L.filter fun g => decide (g.2.ord ≤ (n : ℤ))).filter F) ++
      ((L.filter fun g => decide ((n : ℤ) < g.2.ord)).filter F)).Perm (L.filter F) := by
  have h : (L.filter fun g => decide ((n : ℤ) < g.2.ord)) =
      L.filter fun g => !decide (g.2.ord ≤ (n : ℤ)) :=
    List.filter_congr fun g _ => by
      rw [← decide_not]
      exact decide_eq_decide.2 (by omega)
  rw [h, ← List.filter_append]
  exact (List.filter_append_perm _ L).filter F

/-- `G14.relabels W S` filtered by the dotted-block predicate of order `k`: with the plain label
only, the graphs of `S` filtered, and the other words contribute nothing when their graphs have
order `> k`. -/
theorem filter_relabels_wordsUpTo_perm {n K : ℕ} {S : Expansion 3}
    (hS : ∀ g ∈ S, G14.RootedTheta g.2) (hn : ∀ g ∈ S, (n : ℤ) < g.2.ord) {k : ℤ}
    (hk : k ≤ n + 1) :
    ((G14.relabels (G14.wordsUpTo n K) S).filter
      fun g => g.2.pmBlockB && decide (g.2.ord = k)).Perm
      (S.filter fun g => g.2.pmBlockB && decide (g.2.ord = k)) := by
  have hmem : ([] : List ℕ) ∈ G14.wordsUpTo n K := Words.mem_wordsUpTo.2 ⟨by simp, by simp⟩
  have hperm := List.perm_cons_erase hmem
  refine ((relabels_swap _ S).filter _).trans ?_
  rw [List.filter_flatMap]
  refine (List.Perm.flatMap_right _ hperm).trans ?_
  rw [List.flatMap_cons]
  have h0 : (S.map fun g => (⟨g.1, g.2.relabelRoot []⟩ : Σ m : ℕ, Graph 3 m)) = S := by
    conv_rhs => rw [← List.map_id S]
    refine List.map_congr_left fun g _ => ?_
    simp [relabelRoot_nil]
  rw [h0]
  have h1 : ((G14.wordsUpTo n K).erase []).flatMap (fun o =>
      (S.map fun g => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m)).filter
        fun g => g.2.pmBlockB && decide (g.2.ord = k)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro o ho
    obtain ⟨hne, hoK⟩ := (((Words.nodup_wordsUpTo n K).mem_erase_iff).1 ho)
    have h2 := Words.two_mul_length_le_labelInc_of_mem hoK
    have h3 : 0 < o.length := List.length_pos_iff.2 hne
    rw [List.filter_map, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro g hg
    have := Words.ord_relabelRoot_of_mem_wordsUpTo (n := n) (K := K) (hS g hg) hoK
    have := hn g hg
    simp only [Function.comp, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro _
    omega
  rw [h1, List.append_nil]

/-- Relabelling the `Θ` edge at `⊗` keeps the dotted blocks. -/
theorem pmBlock_relabel {m : ℕ} {Γ : Graph 3 m} (hr : G14.RootedTheta Γ) (o : List ℕ) :
    (Γ.relabelRoot o).PMBlock ↔ Γ.PMBlock := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h20, -, -, -, -, -, -⟩ :=
    G14.relabel Γ o hr
  exact h20

/-- Every graph of `Q` of the `T`-equation is of the form `Σ_x Θ_{⊗x} 𝒢_x` and of order `≥ 2`. -/
theorem q_facts {n D : ℕ} {𝒬 : TEqRec} (hp : Parts n D 𝒬) :
    (∀ g ∈ 𝒬.Q, G14.RootedTheta g.2) ∧ ∀ g ∈ 𝒬.Q, (2 : ℤ) ≤ g.2.ord :=
  ⟨hp.rootQ, fun g hg => (hp.shape.2.2.2.1 g hg).2⟩

/-- **[II, Def 3.2 (7)]** for the solved record: the graphs of order `≤ n` of `R` and `Q` are those
of `TEqRec.solveLow`. -/
theorem coherent_solveLow {n D K : ℕ} {𝒬 : TEqRec} {Rem : Expansion 3} (hp : Parts n D 𝒬) :
    TRec.Coherent n (𝒬.solveLow n) (G14.solveRec n K 𝒬 Rem) := by
  obtain ⟨hQr, hQ2⟩ := q_facts hp
  intro k hk
  refine ⟨?_, ?_⟩
  · change ((𝒬.solveLow n).R.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      (((𝒬.solveLow n).R.filter fun g => decide (g.2.ord ≤ (n : ℤ))).filter
        fun g => decide (g.2.ord = (k : ℤ)))
    rw [List.filter_filter]
    refine List.Perm.of_eq (List.filter_congr fun g _ => ?_)
    by_cases h : g.2.ord = (k : ℤ)
    · simp [h, show (k : ℤ) ≤ n by exact_mod_cast hk]
    · simp [h]
  · change ((𝒬.solveLow n).Q.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      (((𝒬.solveLow n).Q ++ G14.relabels (G14.extra n K) 𝒬.Q).filter
        fun g => decide (g.2.ord = (k : ℤ)))
    rw [List.filter_append]
    have : (G14.relabels (G14.extra n K) 𝒬.Q).filter (fun g => decide (g.2.ord = (k : ℤ))) = [] :=
      filter_ord_eq_nil' (c := (n : ℤ) + 1) (fun g hg => by
        obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 hg
        have := Words.ord_relabelRoot_of_mem_extra (hQr h hh) ho
        have := hQ2 h hh
        dsimp only
        omega) (by omega)
    rw [this, List.append_nil]

/-- **[II, Def 3.2 (7)], dotted-block form** for the solved record: the graphs of order `≤ n + 1`
in which `⊕`, `⊖` lie in one dotted block are those of `TEqRec.solvePM`. -/
theorem coherentPM_solvePM {n D K : ℕ} {𝒬 : TEqRec} {Rem : Expansion 3} (hn : 3 ≤ n)
    (hp : Parts n D 𝒬) : TRec.CoherentPM (n + 1) (G14.solveRec n K 𝒬 Rem) (𝒬.solvePM n) := by
  obtain ⟨hQr, hQ2⟩ := q_facts hp
  obtain ⟨gR, gA, gQ, -⟩ := (good_iff (n - 1) n D 𝒬.toTRec).1 ⟨hp.shape, hp.def63⟩
  intro k hk
  have hkk : (k : ℤ) ≤ n + 1 := by exact_mod_cast hk
  have hXR : (G14.relabels (G14.extra n K) 𝒬.R).filter
      (fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))) = [] :=
    filter_ord_eq_nil (c := (n : ℤ) + 2) (fun g hg => by
      obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 hg
      have := Words.ord_relabelRoot_of_mem_extra (hp.root h (by simp [hh])) ho
      have := (gR h hh).2.1.2.2.1
      dsimp only
      omega) (by omega) _
  have hXQ : (G14.relabels (G14.extra n K) 𝒬.Q).filter
      (fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg
    obtain ⟨h, hh, o, ho, rfl⟩ := Words.mem_relabels.1 hg
    have h1 := Words.ord_relabelRoot_of_mem_extra (hQr h hh) ho
    have h2 := (gQ h hh).2.2.2.2.1
    have h3 := pmBlock_relabel (hQr h hh) o
    simp only [Graph.PMBlock] at h3
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro hpm
    have := h2 (h3.1 hpm)
    omega
  have hOV : (G14.overflow n K).filter
      (fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg
    obtain ⟨o, ho, hg⟩ := List.mem_flatMap.1 hg
    obtain ⟨h1, h2, h3⟩ := Words.mem_extra.1 ho
    have := (G14.overflow_stmt n o hn h2 (Words.labelOK_of_mem_wordsUpTo h1 le_rfl) h3 g
      hg).2.2.2.2.2.2.1
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro _
    omega
  have hA3 := filter_relabels_wordsUpTo_perm (n := n) (K := K) (k := (k : ℤ))
    hp.rootA (fun g hg => (gA g hg).2.1.2) hkk
  have hsplit := filter_split_perm (𝒬.solveLow n).R n
    (fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ)))
  change (((((𝒬.solveLow n).R.filter fun g => decide (g.2.ord ≤ (n : ℤ))) ++
      ((𝒬.solveLow n).R.filter (fun g => decide ((n : ℤ) < g.2.ord)) ++
        G14.relabels (G14.extra n K) 𝒬.R ++ G14.relabels (G14.wordsUpTo n K) 𝒬.A ++
        G14.overflow n K)) ++ ((𝒬.solveLow n).Q ++ G14.relabels (G14.extra n K) 𝒬.Q)).filter
      fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ))).Perm
    (((𝒬.solveLow n).R ++ 𝒬.A ++ (𝒬.solveLow n).Q).filter
      fun g => g.2.pmBlockB && decide (g.2.ord = (k : ℤ)))
  classical
  simp only [List.filter_append, hXR, hXQ, hOV, List.append_nil]
  refine List.perm_iff_count.2 fun x => ?_
  have h1 := hsplit.count_eq x
  have h2 := hA3.count_eq x
  simp only [List.count_append] at h1 h2 ⊢
  omega

/-! ## Independence of the error order -/

/-- For index lists `W ⊆ W'` without repetitions, the filtered sums `W'.flatMap Φ` and
`W.flatMap Φ` agree up to order if the indices of `W'` outside `W` contribute nothing after the
filter. -/
theorem flatMap_filter_perm_of_subset {α β : Type*} {W W' : List α} (hsub : W ⊆ W')
    (hW : W.Nodup) (hW' : W'.Nodup) (Φ : α → List β) (p : β → Bool)
    (h : ∀ o ∈ W', o ∉ W → (Φ o).filter p = []) :
    ((W'.flatMap Φ).filter p).Perm ((W.flatMap Φ).filter p) := by
  classical
  have hperm : W'.Perm (W ++ W'.filter fun o => decide (o ∉ W)) := by
    refine (List.perm_ext_iff_of_nodup hW' ?_).2 fun o => ?_
    · refine List.nodup_append.2 ⟨hW, hW'.filter _, fun a ha b hb hab => ?_⟩
      exact (by simpa using (List.mem_filter.1 hb).2 : b ∉ W) (hab ▸ ha)
    · simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
      constructor
      · intro ho
        by_cases h : o ∈ W
        · exact Or.inl h
        · exact Or.inr ⟨ho, h⟩
      · rintro (h | h)
        · exact hsub h
        · exact h.1
  rw [List.filter_flatMap, List.filter_flatMap]
  refine (hperm.flatMap_right _).trans ?_
  rw [List.flatMap_append]
  have : ((W'.filter fun o => decide (o ∉ W)).flatMap fun o => (Φ o).filter p) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro o ho
    obtain ⟨ho1, ho2⟩ := List.mem_filter.1 ho
    exact h o ho1 (by simpa using ho2)
  rw [this, List.append_nil]

/-- The graphs of order `k` among the relabelled graphs `T.map r_o`: those of order `k - labelInc o`
of `T`, relabelled. -/
theorem filter_map_relabel {T : Expansion 3} (hT : ∀ g ∈ T, G14.RootedTheta g.2) {o : List ℕ}
    (ho : ∀ e ∈ o, 2 ≤ e) (k : ℤ) :
    (T.map fun g => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m)).filter
        (fun g => decide (g.2.ord = k)) =
      (T.filter fun g => decide (g.2.ord = k - (Words.labelInc o : ℤ))).map
        fun g => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m) := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun g hg => ?_
  simp only [Function.comp, Words.ord_relabelRoot_of_entries (hT g hg) ho]
  exact decide_eq_decide.2 (by omega)

/-- **The key step.** If the graphs of `S` and `S'` of order `j ≤ D` agree up to order, and all
orders are `≥ 0`, then after relabelling by the words of `W` (entries `≥ 2`) the graphs of order
`k ≤ D` agree up to order. -/
theorem filter_relabels_perm_of_agree {D : ℕ} {S S' : Expansion 3}
    (hS : ∀ g ∈ S, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord)
    (hS' : ∀ g ∈ S', G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord)
    (hag : ∀ j : ℕ, j ≤ D → (S.filter fun g => decide (g.2.ord = (j : ℤ))).Perm
      (S'.filter fun g => decide (g.2.ord = (j : ℤ))))
    {W : List (List ℕ)} (hW : ∀ o ∈ W, ∀ e ∈ o, 2 ≤ e) {k : ℕ} (hk : k ≤ D) :
    ((G14.relabels W S).filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((G14.relabels W S').filter fun g => decide (g.2.ord = (k : ℤ))) := by
  refine ((relabels_swap W S).filter _).trans (List.Perm.trans ?_
    ((relabels_swap W S').filter _).symm)
  rw [List.filter_flatMap, List.filter_flatMap]
  refine List.Perm.flatMap_left _ fun o ho => ?_
  rw [filter_map_relabel (fun g hg => (hS g hg).1) (hW o ho),
    filter_map_relabel (fun g hg => (hS' g hg).1) (hW o ho)]
  by_cases hj : (Words.labelInc o : ℤ) ≤ k
  · obtain ⟨j, hj'⟩ : ∃ j : ℕ, (j : ℤ) = (k : ℤ) - (Words.labelInc o : ℤ) :=
      ⟨k - Words.labelInc o, by omega⟩
    rw [← hj']
    exact (hag j (by omega)).map _
  · have e1 : (S.filter fun g => decide (g.2.ord = (k : ℤ) - (Words.labelInc o : ℤ))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro g hg
      have := (hS g hg).2
      simp only [decide_eq_true_eq]
      omega
    have e2 : (S'.filter fun g => decide (g.2.ord = (k : ℤ) - (Words.labelInc o : ℤ))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro g hg
      have := (hS' g hg).2
      simp only [decide_eq_true_eq]
      omega
    rw [e1, e2]

/-- Enlarging the list of words `W` to `W'` (both without repetitions) changes the graphs of order
`k` of the relabelled graphs of `S` (orders `≥ 0`) only by words of excess `> k`: nothing. -/
theorem filter_relabels_perm_of_subset {S : Expansion 3}
    (hS : ∀ g ∈ S, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord)
    {W W' : List (List ℕ)} (hsub : W ⊆ W') (hW : W.Nodup) (hW' : W'.Nodup)
    (hent : ∀ o ∈ W', ∀ e ∈ o, 2 ≤ e) {k : ℕ}
    (hbig : ∀ o ∈ W', o ∉ W → k < Words.labelInc o) :
    ((G14.relabels W' S).filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((G14.relabels W S).filter fun g => decide (g.2.ord = (k : ℤ))) := by
  refine ((relabels_swap W' S).filter _).trans (List.Perm.trans ?_
    ((relabels_swap W S).filter _).symm)
  refine flatMap_filter_perm_of_subset hsub hW hW' _ _ fun o ho hno => ?_
  rw [filter_map_relabel (fun g hg => (hS g hg).1) (hent o ho)]
  have hb := hbig o ho hno
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro g hg
  have := (hS g hg).2
  simp only [decide_eq_true_eq]
  omega

/-- A word of `G14.extra n K'` that is not one of `G14.extra n K` has excess `≥ 2K + 2`. -/
theorem labelInc_of_extra_not_mem {n K K' : ℕ} {o : List ℕ} (ho : o ∈ G14.extra n K')
    (ho' : o ∉ G14.extra n K) : 2 * K + 2 ≤ Words.labelInc o := by
  obtain ⟨h1, h2, h3⟩ := Words.mem_extra.1 ho
  exact Words.two_mul_add_two_le_labelInc h1 fun h => ho' (Words.mem_extra.2 ⟨h, h2, h3⟩)

/-- The graphs of order `≤ n` of `L` and `L'` of order `k` agree if those of `L` and `L'` do, for
`k ≤ n`, and are none for `k > n`. -/
theorem filter_le_filter_perm {L L' : Expansion 3} (n k : ℕ)
    (h : k ≤ n → (L.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      (L'.filter fun g => decide (g.2.ord = (k : ℤ)))) :
    ((L.filter fun g => decide (g.2.ord ≤ (n : ℤ))).filter
        fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((L'.filter fun g => decide (g.2.ord ≤ (n : ℤ))).filter
        fun g => decide (g.2.ord = (k : ℤ))) := by
  rw [List.filter_filter, List.filter_filter]
  by_cases hk : k ≤ n
  · have e : ∀ g : Σ m : ℕ, Graph 3 m,
        (decide (g.2.ord = (k : ℤ)) && decide (g.2.ord ≤ (n : ℤ))) =
          decide (g.2.ord = (k : ℤ)) := fun g => by
      by_cases h : g.2.ord = (k : ℤ)
      · simp [h, show (k : ℤ) ≤ n by exact_mod_cast hk]
      · simp [h]
    rw [List.filter_congr (fun g _ => e g), List.filter_congr (fun g _ => e g)]
    exact h hk
  · have e : ∀ g : Σ m : ℕ, Graph 3 m,
        (decide (g.2.ord = (k : ℤ)) && decide (g.2.ord ≤ (n : ℤ))) = false := fun g => by
      by_cases h : g.2.ord = (k : ℤ)
      · simp [h, show ¬ (k : ℤ) ≤ n by exact_mod_cast hk]
      · simp [h]
    rw [List.filter_congr (fun g _ => e g), List.filter_congr (fun g _ => e g)]
    simp

/-- The graphs of order `> n` of `L` and `L'` of order `k` agree if those of `L` and `L'` do, for
`k > n`, and are none for `k ≤ n`. -/
theorem filter_gt_filter_perm {L L' : Expansion 3} (n k : ℕ)
    (h : n < k → (L.filter fun g => decide (g.2.ord = (k : ℤ))).Perm
      (L'.filter fun g => decide (g.2.ord = (k : ℤ)))) :
    ((L.filter fun g => decide ((n : ℤ) < g.2.ord)).filter
        fun g => decide (g.2.ord = (k : ℤ))).Perm
      ((L'.filter fun g => decide ((n : ℤ) < g.2.ord)).filter
        fun g => decide (g.2.ord = (k : ℤ))) := by
  rw [List.filter_filter, List.filter_filter]
  by_cases hk : n < k
  · have e : ∀ g : Σ m : ℕ, Graph 3 m,
        (decide (g.2.ord = (k : ℤ)) && decide ((n : ℤ) < g.2.ord)) =
          decide (g.2.ord = (k : ℤ)) := fun g => by
      by_cases h : g.2.ord = (k : ℤ)
      · simp [h, show (n : ℤ) < k by exact_mod_cast hk]
      · simp [h]
    rw [List.filter_congr (fun g _ => e g), List.filter_congr (fun g _ => e g)]
    exact h hk
  · have e : ∀ g : Σ m : ℕ, Graph 3 m,
        (decide (g.2.ord = (k : ℤ)) && decide ((n : ℤ) < g.2.ord)) = false := fun g => by
      by_cases h : g.2.ord = (k : ℤ)
      · simp [h, show ¬ (n : ℤ) < k by exact_mod_cast hk]
      · simp [h]
    rw [List.filter_congr (fun g _ => e g), List.filter_congr (fun g _ => e g)]
    simp

section Forms

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

/-- The `O_dot` form `Θ_{⊗⊕} Ḡ_{⊕⊖} ×_{⊕⊖}` of the leading graph is `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem rootedTheta_formA : G14.RootedTheta (Overflow.formA []) :=
  ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, by decide +kernel⟩

/-- The `O_dot` form `Θ_{⊗⊕} Ḡ_{⊕⊕} •_{⊕⊖}` of the leading graph is `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem rootedTheta_formB : G14.RootedTheta (Overflow.formB []) :=
  ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, by decide +kernel⟩

/-- The scaling order of `Θ_{⊗⊕} Ḡ_{⊕⊖} ×_{⊕⊖}` is `3`. -/
theorem ord_formA_nil : (Overflow.formA []).ord = 3 := by
  unfold Overflow.formA
  decide +kernel

/-- The scaling order of `Θ_{⊗⊕} Ḡ_{⊕⊕} •_{⊕⊖}` is `4`. -/
theorem ord_formB_nil : (Overflow.formB []).ord = 4 := by
  unfold Overflow.formB
  decide +kernel

end Forms

/-- The scaling orders of the `O_dot` forms of `m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` are `3 + labelInc o` and
`4 + labelInc o` ([II, (2.5)]). -/
theorem ord_oDot_thetaLabelGraph {o : List ℕ} (ho : ∀ e ∈ o, 2 ≤ e) {g : Σ m : ℕ, Graph 3 m}
    (hg : g ∈ oDot (thetaLabelGraph o)) : 3 + (Words.labelInc o : ℤ) ≤ g.2.ord := by
  rw [Overflow.oDot_thetaLabelGraph] at hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · rw [← Overflow.formA_relabel, Words.ord_relabelRoot_of_entries rootedTheta_formA ho,
      ord_formA_nil]
  · rw [← Overflow.formB_relabel]
    change 3 + (Words.labelInc o : ℤ) ≤ ((Overflow.formB []).relabelRoot o).ord
    rw [Words.ord_relabelRoot_of_entries rootedTheta_formB ho, ord_formB_nil]
    omega

/-- The graphs of `Err` of the solved record have order `> Dp` and those of the remainder order
`> Dr`, so none has order `k ≤ Dp`, `k ≤ Dr`. -/
theorem filter_err_nil {n K Dp Dr : ℕ} {𝒬 : TEqRec} {Rem : Expansion 3} (hp : Parts n Dp 𝒬)
    (hRem : ∀ g ∈ Rem, (Dr : ℤ) < g.2.ord) {k : ℕ} (hk : k ≤ Dp) (hk' : k ≤ Dr) :
    (G14.relabels (G14.wordsUpTo n K) 𝒬.Err ++ Rem).filter
      (fun g => decide (g.2.ord = (k : ℤ))) = [] := by
  rw [List.filter_append]
  have h1 : (G14.relabels (G14.wordsUpTo n K) 𝒬.Err).filter
      (fun g => decide (g.2.ord = (k : ℤ))) = [] :=
    filter_ord_eq_nil' (c := (Dp : ℤ) + 1) (fun g hg => by
      obtain ⟨h, hh, o, ho, hord⟩ := ord_of_mem_relabels hp.rootErr entries_of_mem_wordsUpTo hg
      have := hp.shape.2.2.2.2 h hh
      omega) (by omega)
  have h2 : Rem.filter (fun g => decide (g.2.ord = (k : ℤ))) = [] :=
    filter_ord_eq_nil' (c := (Dr : ℤ) + 1) (fun g hg => by have := hRem g hg; omega) (by omega)
  rw [h1, h2]
  rfl

/-- **The graphs of order `≤ D` of the solved record do not depend on the error order**
([II, Def 3.2 (8)]): for `T`-equations with error orders `D ≤ D'` whose graphs of order `≤ D`
agree, iteration numbers `D ≤ 2K`, `K ≤ K'` and remainders of order `> D`. -/
theorem agree_solveRec {n D D' K K' : ℕ} {𝒬 𝒬' : TEqRec} {Rem Rem' : Expansion 3}
    (hDD : D ≤ D') (hDK : D ≤ 2 * K) (hKK : K ≤ K') (hp : Parts n D 𝒬) (hp' : Parts n D' 𝒬')
    (hag : 𝒬.toTRec.AgreeTo D 𝒬'.toTRec) (hRem : ∀ g ∈ Rem, (D : ℤ) < g.2.ord)
    (hRem' : ∀ g ∈ Rem', (D : ℤ) < g.2.ord) :
    (G14.solveRec n K 𝒬 Rem).AgreeTo D (G14.solveRec n K' 𝒬' Rem') := by
  obtain ⟨gR, gA, gQ, gE⟩ := (good_iff (n - 1) n D 𝒬.toTRec).1 ⟨hp.shape, hp.def63⟩
  obtain ⟨gR', gA', gQ', gE'⟩ := (good_iff (n - 1) n D' 𝒬'.toTRec).1 ⟨hp'.shape, hp'.def63⟩
  have oR : ∀ g ∈ 𝒬.R, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord := fun g hg =>
    ⟨hp.rootR g hg, by have := (gR g hg).2.1.2.2.1; omega⟩
  have oR' : ∀ g ∈ 𝒬'.R, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord := fun g hg =>
    ⟨hp'.rootR g hg, by have := (gR' g hg).2.1.2.2.1; omega⟩
  have oA : ∀ g ∈ 𝒬.A, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord := fun g hg =>
    ⟨hp.rootA g hg, by have := (gA g hg).2.1.2; omega⟩
  have oA' : ∀ g ∈ 𝒬'.A, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord := fun g hg =>
    ⟨hp'.rootA g hg, by have := (gA' g hg).2.1.2; omega⟩
  have oQ : ∀ g ∈ 𝒬.Q, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord := fun g hg =>
    ⟨hp.rootQ g hg, by have := (gQ g hg).2.1.2; omega⟩
  have oQ' : ∀ g ∈ 𝒬'.Q, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord := fun g hg =>
    ⟨hp'.rootQ g hg, by have := (gQ' g hg).2.1.2; omega⟩
  have sE : G14.extra n K ⊆ G14.extra n K' := Words.extra_subset hKK
  have sW : G14.wordsUpTo n K ⊆ G14.wordsUpTo n K' := Words.wordsUpTo_subset hKK
  intro k hk
  have hbigE : ∀ o ∈ G14.extra n K', o ∉ G14.extra n K → k < Words.labelInc o :=
    fun o ho ho' => by have := labelInc_of_extra_not_mem ho ho'; omega
  have hbigW : ∀ o ∈ G14.wordsUpTo n K', o ∉ G14.wordsUpTo n K → k < Words.labelInc o :=
    fun o ho ho' => by have := Words.two_mul_add_two_le_labelInc ho ho'; omega
  have agR := fun j hj => (hag j hj).1
  have agA := fun j hj => (hag j hj).2.1
  have agQ := fun j hj => (hag j hj).2.2.1
  have e0 : ∀ o ∈ [] :: chainLabels n, ∀ e ∈ o, 2 ≤ e := entries_of_mem_nil_cons
  have k0 : ∀ {S S' : Expansion 3}, (∀ g ∈ S, G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord) →
      (∀ g ∈ S', G14.RootedTheta g.2 ∧ 0 ≤ g.2.ord) →
      (∀ j : ℕ, j ≤ D → (S.filter fun g => decide (g.2.ord = (j : ℤ))).Perm
        (S'.filter fun g => decide (g.2.ord = (j : ℤ)))) →
      ((G14.relabels (G14.extra n K) S).filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        ((G14.relabels (G14.extra n K') S').filter fun g => decide (g.2.ord = (k : ℤ))) :=
    fun hS hS' hag' => (filter_relabels_perm_of_agree hS hS' hag' entries_of_mem_extra hk).trans
      (filter_relabels_perm_of_subset hS' sE (Words.nodup_extra n K) (Words.nodup_extra n K')
        entries_of_mem_extra hbigE).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact filter_le_filter_perm n k fun _ => filter_relabels_perm_of_agree oR oR' agR e0 hk
  · simp only [G14.solveRec, List.filter_append]
    have h1 := filter_gt_filter_perm (L := (𝒬.solveLow n).R) (L' := (𝒬'.solveLow n).R) n k
      fun _ => filter_relabels_perm_of_agree oR oR' agR e0 hk
    have h2 := k0 oR oR' agR
    have h3 : ((G14.relabels (G14.wordsUpTo n K) 𝒬.A).filter
        fun g => decide (g.2.ord = (k : ℤ))).Perm
        ((G14.relabels (G14.wordsUpTo n K') 𝒬'.A).filter
        fun g => decide (g.2.ord = (k : ℤ))) :=
      (filter_relabels_perm_of_agree oA oA' agA entries_of_mem_wordsUpTo hk).trans
        (filter_relabels_perm_of_subset oA' sW (Words.nodup_wordsUpTo n K)
          (Words.nodup_wordsUpTo n K') entries_of_mem_wordsUpTo hbigW).symm
    have h4 : ((G14.overflow n K).filter fun g => decide (g.2.ord = (k : ℤ))).Perm
        ((G14.overflow n K').filter fun g => decide (g.2.ord = (k : ℤ))) :=
      (flatMap_filter_perm_of_subset sE (Words.nodup_extra n K) (Words.nodup_extra n K')
        (fun o => oDot (thetaLabelGraph o)) _ fun o ho hno => by
          rw [List.filter_eq_nil_iff]
          intro g hg
          have := ord_oDot_thetaLabelGraph (entries_of_mem_extra o ho) hg
          have := hbigE o ho hno
          simp only [decide_eq_true_eq]
          omega).symm
    exact ((h1.append h2).append h3).append h4
  · simp only [G14.solveRec, List.filter_append]
    have h1 := filter_relabels_perm_of_agree oQ oQ' agQ e0 hk
    exact h1.append (k0 oQ oQ' agQ)
  · rw [show (G14.solveRec n K 𝒬 Rem).Err = G14.relabels (G14.wordsUpTo n K) 𝒬.Err ++ Rem from rfl,
      show (G14.solveRec n K' 𝒬' Rem').Err = G14.relabels (G14.wordsUpTo n K') 𝒬'.Err ++ Rem'
        from rfl,
      filter_err_nil hp hRem hk hk, filter_err_nil hp' hRem' (by omega) hk]

end Struct

/-! ## The pins -/

/-- The graph properties of [II, Def 3.2] at order `n` with labels in `[4, n]` and of
[II, Def 6.3] for `G14.solveRec`, from those of the `T`-equation `𝒬` and of the remainder. -/
def G14.solveRec_structStmt : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (D K : ℕ) (𝒬 : TEqRec) (Rem : Expansion 3),
    n < D → D ≤ 2 * K → 𝒬.IsTEqStruct Sig n D →
    (⟨[], [], [], Rem⟩ : TRec).Shape n n D → (⟨[], [], [], Rem⟩ : TRec).Def63 →
    (G14.solveRec n K 𝒬 Rem).Shape n n D ∧ (G14.solveRec n K 𝒬 Rem).Def63

/-- [II, Def 3.2 (7)] and its dotted-block form for `G14.solveRec`: the graphs of order `≤ n` of
`R` and `Q` are those of `TEqRec.solveLow`, and the graphs of order `≤ n + 1` of `R`, `A`, `Q` in
which `⊕`, `⊖` lie in one dotted block are those of `TEqRec.solvePM`. -/
def G14.solveRec_coherentStmt : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (D K : ℕ) (𝒬 : TEqRec) (Rem : Expansion 3),
    n < D → D ≤ 2 * K → 𝒬.IsTEqStruct Sig n D →
    TRec.Coherent n (𝒬.solveLow n) (G14.solveRec n K 𝒬 Rem) ∧
      TRec.CoherentPM (n + 1) (G14.solveRec n K 𝒬 Rem) (𝒬.solvePM n)

/-- The graphs of order `≤ D` of `G14.solveRec` do not depend on the error order: for
`T`-equations with error orders `D ≤ D'` whose graphs of order `≤ D` agree, iteration numbers
`D ≤ 2K`, `K ≤ K'` and remainders of order `> D`. -/
def G14.solveRec_agreeStmt : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (D D' K K' : ℕ) (𝒬 𝒬' : TEqRec)
    (Rem Rem' : Expansion 3),
    n < D → D ≤ D' → D ≤ 2 * K → K ≤ K' → 𝒬.IsTEqStruct Sig n D → 𝒬'.IsTEqStruct Sig n D' →
    𝒬.toTRec.AgreeTo D 𝒬'.toTRec → (∀ g ∈ Rem, (D : ℤ) < g.2.ord) →
    (∀ g ∈ Rem', (D : ℤ) < g.2.ord) →
    (G14.solveRec n K 𝒬 Rem).AgreeTo D (G14.solveRec n K' 𝒬' Rem')

/-- **The graph properties of the solved `T`-equation** ([II, Def 3.2] and [II, Def 6.3]): the
record `G14.solveRec n K 𝒬 Rem` has the kinds, the normal regular, doubly connected graphs with the
external atoms (9), (10), the recollision graphs of orders `3, …, n` in `R`, the label-free graphs
of order `> n` in `A`, the `Q`-graphs in `Q`, the graphs of order `> D` in `Err`, and the clauses of
[II, Def 6.3]. Of `𝒬` it reads `n < D`, the properties of [II, Def 3.2] with labels in
`[4, n - 1]`, the form (4) of every graph and [II, Def 6.3]. -/
theorem G14.solveRec_struct : G14.solveRec_structStmt := by
  intro n hn _ D K 𝒬 Rem _ _ hS hs hd
  exact Struct.shape_def63 hn (Struct.Parts.of_struct hS) hs hd

/-- **[II, Def 3.2 (7)] for the solved `T`-equation**: the graphs of order `≤ n` of `R` and `Q` of
`G14.solveRec n K 𝒬 Rem` are those of `TEqRec.solveLow`, and the graphs of order `≤ n + 1` with `⊕`,
`⊖` in one dotted block are those of `TEqRec.solvePM`. -/
theorem G14.solveRec_coherent : G14.solveRec_coherentStmt := by
  intro n hn _ D K 𝒬 Rem _ _ hS
  have hp := Struct.Parts.of_struct hS
  exact ⟨Struct.coherent_solveLow hp, Struct.coherentPM_solvePM hn hp⟩

/-- **The solved `T`-equation does not depend on the error order** ([II, Def 3.2 (8)]): the graphs
of order `≤ D` of `G14.solveRec n K 𝒬 Rem` and `G14.solveRec n K' 𝒬' Rem'` agree, up to order. -/
theorem G14.solveRec_agree : G14.solveRec_agreeStmt := by
  intro n _ _ D D' K K' 𝒬 𝒬' Rem Rem' _ hDD hDK hKK hS hS' hag hR hR'
  exact Struct.agree_solveRec hDD hDK hKK (Struct.Parts.of_struct hS)
    (Struct.Parts.of_struct hS') hag hR hR'

namespace Struct

end Struct

end RBM8D

end
