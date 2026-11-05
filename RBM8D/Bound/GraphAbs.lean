import RBM8D.TExp.Defs
import RBM8D.Kernel.ThetaDecay
import RBM8D.Kernel.ZdCancel
import RBM8D.Profile.Symbol
import RBM8D.Input.Entry
import RBM8D.Input.Sizes
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Base
import RBM8D.Bound.Norm
import RBM8D.Bound.Chain
import RBM8D.TExp.Closure
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Absolute values of graphs and the internal form

The absolute-value graph, the graph with every atom made internal, the data used for the graph bounds
of [I, §6.4] and [II, §8], and the elementary facts relating them.
-/

noncomputable section

open scoped BigOperators Matrix
open MeasureTheory Filter

namespace RBM8D

open Graphs

/-- The value of the absolute-value graph `𝒢^{abs}` of [I, Lemma 6.10]: every component and the
coefficient replaced by its absolute value, the `P`/`Q` labels ignored; a labelled `Θ` edge is one
factor `|(Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ)_{xy}|`. -/
def Graphs.Graph.absVal {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (D : Data ι) (e : Fin k → ι) : ℝ :=
  ∑ s : Fin n → ι, ‖Γ.coeff.eval D.m‖ * (Γ.comps.map fun c => ‖Comp.val D (Sum.elim e s) c‖).prod

/-- The graph `Γ` with its external atoms made internal: the graph without external atoms of
[I, Lemma 6.10] in which the external atoms of `Γ` are the fixed atoms. -/
def Graphs.Graph.internalize {k n : ℕ} (Γ : Graph k n) : Graph 0 (k + n) :=
  Γ.mapAtoms (Sum.elim (fun a => Sum.inr (Fin.castAdd n a)) (fun b => Sum.inr (Fin.natAdd k b)))

/-- The symmetrized variance matrices `(S_{W,L} + S_{W,L}ᵀ) / 2` of the profile `P`, with
`S_{xy} = f_{W,L}([x − y]_L)` as in [I, (1.5)]. They are translation invariant and symmetric for
every `(W, L)`, and equal `S_{W,L}` wherever `S_{W,L}` is symmetric; by [I, Assumption 1.1] this
includes `adm(c₀, c₁)` for `W ≥ W₀`. -/
def smatVar {d : ℕ} (P : Profile d) : VarFamily d :=
  fun W L _ => (1 / 2 : ℝ) • (Smat P.ψ W L + (Smat P.ψ W L)ᵀ)

/-- `smatVar P W L` is translation invariant, for every `W` and `L`. -/
theorem smatVar_transInv {d : ℕ} (P : Profile d) (W L : ℕ) [NeZero L] :
    TransInv (smatVar P W L) := by
  intro x y a
  have h1 := Smat_transInv d L P.ψ W x y a
  have h2 := Smat_transInv d L P.ψ W y x a
  simp only [smatVar, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, h1, h2]

/-- `smatVar P W L` is symmetric, for every `W` and `L`. -/
theorem smatVar_isSymm {d : ℕ} (P : Profile d) (W L : ℕ) [NeZero L] :
    (smatVar P W L).IsSymm := by
  ext x y
  simp only [smatVar, Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply, add_comm]

/-- [I, (1.25)] for `Σ_l` with the variance family `smatVar P`, for every `Σ` and every `l`:
`Σ_l(x, x + a) = Σ_l(0, a) = Σ_l(0, -a)` for every `(W, L)` and every `z` with `Im z > 0`. -/
theorem selfEnergySymm_smatVar :
    ∀ (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ),
      SelfEnergySymm d (smatVar P) Sig l := by
  intro d P Sig l
  refine selfEnergySymm d (smatVar P) Sig l fun W L _ => ⟨smatVar_transInv P W L, fun x y => ?_⟩
  exact (smatVar_isSymm P W L).apply y x

/-- `smatVar P W L` is `S_{W,L}` wherever `S_{W,L}` is symmetric. -/
theorem smatVar_eq_of_isSymm {d : ℕ} (P : Profile d) {W L : ℕ} [NeZero L]
    (h : (Smat P.ψ W L).IsSymm) : smatVar P W L = Smat P.ψ W L := by
  change (1 / 2 : ℝ) • (Smat P.ψ W L + (Smat P.ψ W L)ᵀ) = Smat P.ψ W L
  rw [h.eq, ← two_smul ℝ (Smat P.ψ W L), smul_smul]
  norm_num

/-- On `adm(c₀, c₁)` for `W ≥ W₀`, `smatVar P W L = S_{W,L}` ([I, Assumption 1.1]). -/
theorem smatVar_eq_on_adm :
    ∀ (d : ℕ) (P : Profile d) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ → ∃ W₀ : ℝ,
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → smatVar P W L = Smat P.ψ W L := by
  intro d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₀, h⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  exact ⟨W₀, fun W L _ hm hW => smatVar_eq_of_isSymm P (h W L hm hW).1⟩

/-- The kernel family `Σ_l` of the self-energies `Σ` for `smatVar P` is translation invariant and
symmetric for every `l`, `(W, L)` and `z` with `Im z > 0`. -/
theorem kerSymm_sigKer_smatVar :
    ∀ (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (l : ℕ),
      KerSymm (sigKer (smatVar P) Sig) l :=
  selfEnergySymm_smatVar

/-- Where `S_{W,L}` is symmetric, `Σ_l` for `smatVar P` is `Σ_l` for `S_{W,L}`. -/
theorem sigKer_smatVar_eq_of_isSymm {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) {W L : ℕ}
    [NeZero L] (h : (Smat P.ψ W L).IsSymm) (l : ℕ) (z : ℂ) :
    sigKer (smatVar P) Sig l W L z = sigMat Sig (Smat P.ψ W L) z l := by
  change sigMat Sig (smatVar P W L) z l = _
  rw [smatVar_eq_of_isSymm P h]

/-- On `adm(c₀, c₁)` for `W ≥ W₀`, `Σ_l` for `smatVar P` is `Σ_l` for `S_{W,L}`. -/
theorem sigKer_smatVar_eq_on_adm :
    ∀ (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ (l : ℕ) (z : ℂ),
        sigKer (smatVar P) Sig l W L z = sigMat Sig (Smat P.ψ W L) z l := by
  intro d P Sig c₀ c₁ hc₀ hc₁
  obtain ⟨W₀, h⟩ := Smat_symm_nonneg d P c₀ c₁ hc₀ hc₁
  exact ⟨W₀, fun W L _ hm hW l z => sigKer_smatVar_eq_of_isSymm P Sig (h W L hm hW).1 l z⟩

/-- On `adm(c₀, c₁)` for `W ≥ W₀`, the deterministic data record of `S_{W,L}` with the matrices
`Σ_l` for `smatVar P` is the one with the matrices `Σ_l` for `S_{W,L}`. -/
theorem detData_smatVar_eq_on_adm :
    ∀ (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (c₀ c₁ : ℝ), 0 < c₀ → 0 < c₁ →
      ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z : ℂ,
        detData (Smat P.ψ W L) z (fun l => sigKer (smatVar P) Sig l W L z) =
          detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z) := by
  intro d P Sig c₀ c₁ hc₀ hc₁
  obtain ⟨W₀, h⟩ := sigKer_smatVar_eq_on_adm d P Sig c₀ c₁ hc₀ hc₁
  exact ⟨W₀, fun W L _ hm hW z => by
    congr 1
    exact funext fun l => h W L hm hW l z⟩

/-- The data record at `S`, `z`, the self-energies `Sig` and a matrix `G`: the deterministic
fields of `detData` with the matrices `Σ_l` of `Sig`, and `G` in place of the resolvent and of
all its minors. -/
def gData {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (Sig : ℕ → Expansion 2) (G : Matrix ι ι ℂ) : Data ι :=
  { detData S z (sigMat Sig S z) with Gm := fun _ => G }

/-- The entries `|G_{xy} - δ_{xy} m(z)|`. -/
def errAbs {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℝ :=
  fun x y => ‖entryErr G (msc z) x y‖

/-- The normalized value `W^{(n_{xy} - 3)d/2} |𝒢^{abs}_{xy}| / B_{xy}` of a graph with two
external atoms `x = 0`, `y = 1`, with `n_{xy}` its scaling order. -/
def normGraph2 (d L W : ℕ) [NeZero L] {n : ℕ} (Γ : Graph 2 n) (D : Data (Zd d L)) :
    Matrix (Zd d L) (Zd d L) ℝ :=
  fun x y => (W : ℝ) ^ (((Γ.ord : ℝ) - 3) * d / 2) * Γ.absVal D ![x, y] / bB d L W x y

/-- The components of the graphs `𝒢'` of [I, Cor 6.13]: waved edges and diffusive auxiliary
edges of scaling order `2`, without minor and without label. -/
def Graphs.Comp.isBKind {V : Type*} (c : Comp V) : Bool :=
  c.minor.isEmpty && c.label.isNone &&
    match c.kind with
    | .waved _ => true
    | .aux _ r b => decide (r = 2) && b
    | _ => false

/-- The data record of [I, Cor 6.13]: `m = m(z)`, `s = S`, `S^± = S^±(m)` and the matrices `M`
of the auxiliary edges; the other fields are `0`. -/
def auxData {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (M : ℕ → Matrix ι ι ℂ) : Data ι :=
  { detData S z 0 with aux := M }

/-- The value of a graph is bounded by the value of its absolute-value graph. -/
theorem norm_val_le_absVal :
  ∀ (k n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Graph k n) (D : Data ι)
    (e : Fin k → ι), ‖Γ.val D e‖ ≤ Γ.absVal D e := by
  intro k n ι _ _ Γ D e
  unfold Graph.val Graph.absVal Graph.term
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  gcongr
  calc ‖(Γ.comps.map (Comp.val D (Sum.elim e s))).prod‖
      ≤ ((Γ.comps.map (Comp.val D (Sum.elim e s))).map norm).prod := List.norm_prod_le _
    _ = _ := by rw [List.map_map]; rfl

/-- A list of entries that are all at least `4` has sum at least `4` times its length. -/
private theorem graphAbs_four_mul_length_le_sum (o : List ℕ) (h : ∀ j ∈ o, 4 ≤ j) :
    4 * o.length ≤ o.sum := by
  induction o with
  | nil => simp
  | cons a o ih =>
    have ha := h a (by simp)
    have := ih fun j hj => h j (by simp [hj])
    simp only [List.length_cons, List.sum_cons]
    omega

/-- A component of the kinds of [II, Def 3.2] has nonnegative scaling order, and order at least
`2` when it is waved or diffusive. -/
private theorem graphAbs_ord_of_isTKind {V : Type*} (N : ℕ) (c : Comp V)
    (h : c.isTKind N = true) :
    0 ≤ c.kind.ord ∧ ((c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) →
      2 ≤ c.kind.ord) := by
  obtain ⟨κ, x, y, m, l⟩ := c
  cases κ with
  | theta o =>
    have hl : labelOK N o = true := by
      have := h
      simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at this
      exact this.2
    have h4 : ∀ j ∈ o, 4 ≤ j := by
      intro j hj
      simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
      exact (hl j hj).1.1
    have := graphAbs_four_mul_length_le_sum o h4
    simp only [Kind.ord]
    refine ⟨by omega, fun _ => by omega⟩
  | thetaErr n D => simp [Comp.isTKind] at h
  | ghost => simp [Comp.isTKind] at h
  | inv c => simp [Comp.isTKind] at h
  | wD c D => simp [Comp.isTKind] at h
  | aux j r b => simp [Comp.isTKind] at h
  | G c => simp [Kind.ord, Kind.joinsMol, Kind.isDiffusive]
  | weight c => simp [Kind.ord, Kind.joinsMol, Kind.isDiffusive]
  | light c => simp [Kind.ord, Kind.joinsMol, Kind.isDiffusive]
  | waved w => simp [Kind.ord, Kind.joinsMol, Kind.isDiffusive]
  | dot => simp [Kind.ord, Kind.joinsMol, Kind.isDiffusive]
  | xdot => simp [Kind.ord, Kind.joinsMol, Kind.isDiffusive]

/-- The sum of the scaling orders of components of the kinds of [II, Def 3.2] is at least twice
the number of waved and diffusive ones. -/
private theorem graphAbs_two_mul_length_le_sum {V : Type*} (N : ℕ) (cs : List (Comp V))
    (h : cs.all (Comp.isTKind N) = true) :
    2 * (cs.filter fun c => decide (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨
      c.kind.isDiffusive = true)).length ≤ (cs.map fun c => c.kind.ord).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := ih h.2
    obtain ⟨h0, h2⟩ := graphAbs_ord_of_isTKind N c h.1
    by_cases hc : c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true
    · have := h2 hc
      simp only [List.filter_cons, hc, decide_true, ite_true, List.length_cons, List.map_cons,
        List.sum_cons]
      omega
    · simp only [List.filter_cons, hc, decide_false, List.map_cons, List.sum_cons]
      simp only [Bool.false_eq_true, ite_false]
      omega

/-- For a graph with two fixed atoms whose internal form is regular with the kinds of
[II, Def 3.2 (2)], `n_{xy} ≥ 2`. -/
theorem two_le_ord :
  ∀ (n C N : ℕ) (Γ : Graph 2 n), Γ.internalize.Regular C → Γ.TKinds N → 2 ≤ Γ.ord := by
  intro n C N Γ hR hT
  set Γ' : Graph 0 (2 + n) := Γ.internalize with hΓ'
  have hmap : ∀ c ∈ Γ'.comps, ∃ c₀ ∈ Γ.comps, c.kind = c₀.kind ∧ c.isTKind N = c₀.isTKind N := by
    intro c hc
    simp only [hΓ', Graph.internalize, Graph.mapAtoms, List.mem_map] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact ⟨c₀, hc₀, rfl, by simp [Comp.isTKind, Comp.map]⟩
  have hall : Γ'.comps.all (Comp.isTKind N) = true := by
    unfold Graph.TKinds at hT
    rw [List.all_eq_true] at hT ⊢
    intro c hc
    obtain ⟨c₀, hc₀, -, h⟩ := hmap c hc
    rw [h]; exact hT c₀ hc₀
  have hsum : (Γ'.comps.map fun c => c.kind.ord).sum = (Γ.comps.map fun c => c.kind.ord).sum := by
    simp [hΓ', Graph.internalize, Graph.mapAtoms, Comp.map, List.map_map, Function.comp_def]
  have hord : Γ.ord = (Γ'.comps.map fun c => c.kind.ord).sum - 2 * n := by
    rw [hsum]; rfl
  have hne : Nonempty (Atom 0 (2 + n)) := ⟨Sum.inr ⟨0, by omega⟩⟩
  have hconn : Γ'.wavedThetaGraph.Connected := by
    refine ⟨fun u v => ?_⟩
    rcases u with a | a
    · exact a.elim0
    rcases v with b | b
    · exact b.elim0
    exact hR.internal a b
  have hcard := hconn.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card (Atom 0 (2 + n)) = 2 + n := by simp [Nat.card_eq_fintype_card]
  rw [hV] at hcard
  set F := Γ'.comps.filter fun c => decide (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨
    c.kind.isDiffusive = true) with hF
  have hsub : Γ'.wavedThetaGraph.edgeSet ⊆ ↑((F.map fun c => s(c.x, c.y)).toFinset) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      simp only [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at he
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, hF, List.mem_filter,
        decide_eq_true_eq]
      rcases he.2 with ⟨c, hc, hP, rfl, rfl⟩ | ⟨c, hc, hP, rfl, rfl⟩
      · exact ⟨c, ⟨hc, hP⟩, rfl⟩
      · exact ⟨c, ⟨hc, hP⟩, Sym2.eq_swap⟩
  have hedge : Nat.card Γ'.wavedThetaGraph.edgeSet ≤ F.length := by
    rw [Nat.card_coe_set_eq]
    calc Set.ncard Γ'.wavedThetaGraph.edgeSet
        ≤ Set.ncard (↑((F.map fun c => s(c.x, c.y)).toFinset) : Set (Sym2 (Atom 0 (2 + n)))) :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (F.map fun c => s(c.x, c.y)).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (F.map fun c => s(c.x, c.y)).length := List.toFinset_card_le _
      _ = F.length := List.length_map _
  have hge : 2 * (F.length : ℤ) ≤ (Γ'.comps.map fun c => c.kind.ord).sum :=
    graphAbs_two_mul_length_le_sum N Γ'.comps hall
  omega

/-! ## Decidability instances for concrete graphs -/

section Instances

/-- Adjacency in the graph of all components is decidable. -/
private instance instDecAdjEdgeGraph {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.edgeGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.x = u ∧ c.y = v) ∨ (∃ c ∈ Γ.comps, c.x = v ∧ c.y = u))))

/-- Adjacency in the graph of waved and diffusive components is decidable. -/
private instance instDecAdjWavedTheta {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.wavedThetaGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = v ∧ c.y = u))))

/-- Adjacency in the graph of waved and dotted components is decidable. -/
private instance instDecAdjMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

/-- Being in one molecule is decidable. -/
private instance instDecSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjMol Γ) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

/-- Adjacency in a net is decidable. -/
private instance instDecAdjNet {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    DecidableRel (Γ.net B).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧
    ((Γ.SameMol (.inr a) (.inr b) ∨ ∃ i ∈ B, Γ.comps[i].x = .inr a ∧ Γ.comps[i].y = .inr b) ∨
      (Γ.SameMol (.inr b) (.inr a) ∨ ∃ i ∈ B, Γ.comps[i].x = .inr b ∧ Γ.comps[i].y = .inr a))))

/-- Regularity with a given bound is decidable. -/
private instance instDecRegular {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Decidable (Γ.Regular C) :=
  haveI : DecidableRel Γ.edgeGraph.Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjEdgeGraph Γ)
  haveI : DecidableRel Γ.wavedThetaGraph.Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjWavedTheta Γ)
  haveI : Decidable Γ.edgeGraph.Preconnected :=
    inferInstanceAs (Decidable (∀ u v, Γ.edgeGraph.Reachable u v))
  decidable_of_iff (k + n + Γ.comps.length ≤ C ∧ Γ.edgeGraph.Preconnected ∧
      (∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (.inr a) (.inr b)) ∧
      ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

set_option synthInstance.maxSize 1024 in
/-- Normal regularity with a given bound is decidable. -/
private instance instDecNormal {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Decidable (Γ.Normal C) :=
  inferInstanceAs (Decidable (Γ.Regular C ∧ (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧
    ∀ u v : Atom k n, u ≠ v →
      ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))))

/-- Spanning the internal molecules is decidable. -/
private instance instDecSpans {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    Decidable (Γ.Spans B) :=
  haveI : DecidableRel (Γ.net B).Reachable :=
    @SimpleGraph.instDecidableRelReachable _ _ _ _ (instDecAdjNet Γ B)
  inferInstanceAs (Decidable (∀ a b, (Γ.net B).Reachable a b))

namespace G9

end G9

end Instances

end RBM8D
