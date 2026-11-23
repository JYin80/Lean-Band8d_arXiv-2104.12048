module

public import RBM8D.Graph.Glue

@[expose] public section

/-!
# The transposed record and the transposed graph

The data record with every resolvent minor matrix transposed, the graph with the two atoms of
every solid edge exchanged, the model relations at the transposed record, the value of the
transposed graph, and [II, (4.15)] for the `t`-variable `t_{y₁y₂,x}` ([II, Strategy 6.6, Step 3]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The data record with every resolvent minor matrix transposed, `G^{(T)} ↦ (G^{(T)})ᵀ`; the other
fields are kept. For the record of the model at `H` it is the record of the model at `Hᵀ`, whose
resolvent is `Gᵀ`. -/
def Data.transposeG {ι : Type*} (D : Data ι) : Data ι :=
  { D with Gm := fun T => (D.Gm T).transpose }

/-- The component with its two atoms exchanged if it is a solid edge, and unchanged otherwise. -/
def Comp.swapSolid {V : Type*} (c : Comp V) : Comp V :=
  if c.kind.isSolid then { c with x := c.y, y := c.x } else c

/-- The graph with the two atoms of every solid edge exchanged (every `G` entry transposed); the
other components are kept. -/
def Graph.swapSolid {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map Comp.swapSolid, Γ.coeff⟩

/-- The formal sum with the two atoms of every solid edge exchanged. -/
def Expansion.swapSolid {k : ℕ} (E : Expansion k) : Expansion k :=
  E.map fun g => ⟨g.1, g.2.swapSolid⟩

section Transpose

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `(Hᵀ - z)⁻¹ = ((H - z)⁻¹)ᵀ`. -/
private theorem green_transpose (H : Matrix ι ι ℂ) (z : ℂ) :
    green H.transpose z = (green H z).transpose := by
  unfold green
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]

/-- The model relations at the transposed record, from those at the record: `H ↦ Hᵀ`, `G ↦ Gᵀ`,
`∂_{h_{ab}} ↦ ∂_{h_{ba}}`, with the same `S`, conditional expectations and classes of random
variables. -/
private def ModelAdm.transposeAdm {Ω : Type} {PF : PFamily Ω ι} {D : Ω → Data ι}
    (A : ModelAdm Ω ι PF D) : ModelAdm Ω ι PF fun ω => (D ω).transposeG where
  H ω := (A.H ω).transpose
  z := A.z
  S := A.S
  E := A.E
  Meas := A.Meas
  Good := A.Good
  Test := A.Test
  dh a b := A.dh b a
  isHermitian ω := (A.isHermitian ω).transpose
  im_pos := A.im_pos
  isSymm := A.isSymm
  nonneg := A.nonneg
  rowSum := A.rowSum
  data_m := A.data_m
  data_G ω := by
    change ((D ω).Gm ∅).transpose = _
    rw [A.data_G, green_transpose]
  data_minor ω x := by
    change ((D ω).Gm {x}).transpose = _
    rw [A.data_minor, green_transpose]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.of_apply, greenMinor]
    ring
  data_S := A.data_S
  data_Sp := A.data_Sp
  data_Sm := A.data_Sm
  data_Theta := A.data_Theta
  laws := A.laws
  meas_add := A.meas_add
  meas_mul := A.meas_mul
  meas_minor x a b := A.meas_minor x b a
  P_star := A.P_star
  good_star := A.good_star
  good_entry T a b := A.good_entry T b a
  good_inv a := A.good_inv a
  good_H a b := A.good_H b a
  test_good := A.test_good
  test_const := A.test_const
  test_add := A.test_add
  test_mul := A.test_mul
  test_star := A.test_star
  test_entry a b := A.test_entry b a
  test_dh a b F h := A.test_dh b a F h
  dh_add a b := A.dh_add b a
  dh_mul a b := A.dh_mul b a
  dh_const a b := A.dh_const b a
  dh_green a b x y := by
    simp only [green_transpose, Matrix.transpose_apply]
    rw [A.dh_green b a y x]
    funext ω
    ring
  dh_conj_green a b x y := by
    simp only [green_transpose, Matrix.transpose_apply]
    rw [A.dh_conj_green b a y x]
    funext ω
    ring
  ibp x a b h F hF := by
    have h' := A.ibp x b a h.symm F hF
    simp only [Matrix.transpose_apply]
    rw [h', A.isSymm.apply a b]

/-- The factor of a component with a transposed solid edge is the factor of the component at the
transposed record. -/
private theorem comp_val_swapSolid {V : Type*} (D : Data ι) (σ : V → ι) (c : Comp V) :
    Comp.val D σ c.swapSolid = Comp.val D.transposeG σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ with
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem swapSolid_label {V : Type*} (c : Comp V) : c.swapSolid.label = c.label := by
  unfold Comp.swapSolid
  split <;> rfl

/-- The term of a graph with all solid edges transposed is its term at the transposed record. -/
private theorem termR_swapSolid {k n : ℕ} {Ω : Type} (Γ : Graph k n) (PF : PFamily Ω ι)
    (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) :
    Γ.swapSolid.termR PF D σ ω = Γ.termR PF (fun ω => (D ω).transposeG) σ ω := by
  have hL : Γ.swapSolid.labels = Γ.labels := by
    simp only [Graph.labels, Graph.swapSolid, List.filterMap_map]
    congr 1
    exact List.filterMap_congr fun c _ => swapSolid_label c
  have hF : ∀ (p : Comp (Atom k n) → Bool) (D' : Data ι),
      (∀ c, p c.swapSolid = p c) →
      (Γ.swapSolid.comps.filter p).map (Comp.val D' σ) =
        (Γ.comps.filter p).map (Comp.val D'.transposeG σ) := by
    intro p D' hp
    simp only [Graph.swapSolid, List.filter_map, List.map_map]
    have : (p ∘ Comp.swapSolid) = p := funext hp
    rw [this]
    exact List.map_congr_left fun c _ => comp_val_swapSolid D' σ c
  unfold Graph.termR
  rw [hL, hF _ _ fun c => by rw [swapSolid_label]]
  congr 2
  refine List.map_congr_left fun ℓ _ => ?_
  congr 1
  funext ω'
  rw [hF _ _ fun c => by rw [swapSolid_label]]

/-- The value of a graph with all solid edges transposed is its value at the transposed record. -/
private theorem swapSolid_valR {k n : ℕ} {Ω : Type} (Γ : Graph k n) (PF : PFamily Ω ι)
    (D : Ω → Data ι) (e : Fin k → ι) :
    Γ.swapSolid.valR PF D e = Γ.valR PF (fun ω => (D ω).transposeG) e := by
  funext ω
  simp only [Graph.valR, termR_swapSolid]

/-- The value of the formal sum with all solid edges transposed is its value at the transposed
record. -/
private theorem expansion_swapSolid_value {k : ℕ} {Ω : Type} (E : Expansion k)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) :
    E.swapSolid.valR PF D e = E.valR PF (fun ω => (D ω).transposeG) e := by
  funext ω
  simp only [Expansion.valR, Expansion.swapSolid, List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun g _ => ?_
  exact congrFun (swapSolid_valR g.2 PF D e) ω

/-- The factor of a component other than a solid edge is the same at the transposed record. -/
private theorem comp_val_transposeG {V : Type*} (D : Data ι) (σ : V → ι) (c : Comp V)
    (h : c.kind.isSolid = false) : Comp.val D.transposeG σ c = Comp.val D σ c := by
  rw [← comp_val_swapSolid]
  unfold Comp.swapSolid
  simp [h]

/-- A graph without solid edges has the same value at the transposed record. -/
private theorem graph_val_transposeG {k n : ℕ} (Γ : Graph k n) (D : Data ι) (e : Fin k → ι)
    (h : ∀ c ∈ Γ.comps, c.kind.isSolid = false) : Γ.val D.transposeG e = Γ.val D e := by
  unfold Graph.val Graph.term
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 2
  exact List.map_congr_left fun c hc => comp_val_transposeG D _ c (h c hc)

/-- The self-energy matrices of a record consistent with `Sig` are consistent with `Sig` at the
transposed record, when the self-energies have the shape of [II, Def 2.7 (i)]. -/
private theorem sigConsistent_transposeG (Sig : ℕ → Expansion 2) (n : ℕ)
    (hsh : SelfEnergyShapesUpTo Sig n) (D : Data ι) (h : SigConsistent Sig (n + 1) D) :
    SigConsistent Sig (n + 1) D.transposeG := by
  intro k h4 hlt hev
  change D.Sig k = _
  rw [h k h4 hlt hev]
  ext x y
  simp only [Matrix.of_apply, Expansion.val]
  congr 1
  refine List.map_congr_left fun g hg => ?_
  have hall := (hsh k h4 (by omega) hev g hg).2.1
  refine (graph_val_transposeG g.2 D _ fun c hc => ?_).symm
  have hc' := List.all_eq_true.1 hall c hc
  rcases c with ⟨κ, _, _, _, _⟩
  cases κ <;> simp_all [Comp.isDetKind, Kind.isSolid]

/-- `t_{y₁y₂,x}` has the value of `t_{x,y₁y₂}` at the transposed record (`s` is symmetric). -/
private theorem tVar_true_value {Ω : Type} {PF : PFamily Ω ι} {D : Ω → Data ι}
    (A : ModelAdm Ω ι PF D) (e : Fin 3 → ι) :
    (tVar true).valR PF D e = tVarGraph.valR PF (fun ω => (D ω).transposeG) e := by
  rw [← swapSolid_valR]
  funext ω
  simp only [Graph.valR]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Graph.termR, tVar, ↓reduceIte, Graph.swapEnds, tVarGraph, mkC, Fin.isValue,
    List.map_cons, List.map_nil, Option.isNone_none, List.filter_cons_of_pos, List.filter_nil,
    Comp.val, Sum.elim_inr, Sum.elim_inl, A.data_S, Matrix.map_apply, List.toFinset_nil,
    List.prod_cons, List.prod_nil, mul_one, reduceCtorEq, decide_false, Bool.false_eq_true,
    not_false_eq_true, List.filter_cons_of_neg, Graph.labels, List.filterMap_cons_none,
    List.filterMap_nil, List.dedup_nil, Graph.swapSolid, Comp.swapSolid, Kind.isSolid,
    mul_eq_mul_left_iff]
  rw [A.isSymm.apply]
  simp only [eq_comm]
  left
  by_cases h1 : s 0 = e 1 <;> by_cases h2 : s 0 = e 2 <;> simp [h1, h2]

end Transpose

/-- **The model relations at the transposed record** ([II, Strategy 6.6, Step 3]): if the model
relations hold for the records `D ω`, they hold for the records with every resolvent minor matrix
transposed, with `H ↦ Hᵀ`, `∂_{h_{ab}} ↦ ∂_{h_{ba}}` and the same `S`; the integration by parts
uses the symmetry of `S`. -/
theorem modelAdm_transpose :
  ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
    modelAdm Ω ι PF D → modelAdm Ω ι PF fun ω => (D ω).transposeG := by
  intro Ω ι _ _ PF D ⟨A⟩
  exact ⟨A.transposeAdm⟩

/-- **The value of the transposed graph**: the value of the graph with the two atoms of every solid
edge exchanged is the value of the graph at the record with every resolvent minor matrix
transposed, for every record and every family of conditional expectations; the labels are
unchanged. -/
theorem swapSolid_value :
  ∀ (k n : ℕ) (Γ : Graph k n) (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) (e : Fin k → ι),
    Γ.swapSolid.valR PF D e = Γ.valR PF (fun ω => (D ω).transposeG) e := by
  intro k n Γ Ω ι _ _ PF D e
  exact swapSolid_valR Γ PF D e

/-- **[II, (4.15)] for `t_{y₁y₂,x}`** ([II, Strategy 6.6, Step 3]): for an `n`-th order
`T`-expansion `𝒯` over `Sig` whose self-energies of order `≤ n` have the shape of
[II, Def 2.7 (i)], the right side of [II, (4.15)] with all `G` entries transposed has the value of
`t_{y₁y₂,x}`, under the model relations and the consistency of `Sig`. -/
theorem tSubstT_value' :
  ∀ (Sig : ℕ → Expansion 2) (n : ℕ) (𝒯 : TRec), 𝒯.Identity Sig n → SelfEnergyShapesUpTo Sig n →
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
      modelAdm Ω ι PF D → (∀ ω, SigConsistent Sig (n + 1) (D ω)) → ∀ e : Fin 3 → ι,
        (𝒯.tSubst n).swapSolid.valR PF D e = (tVar true).valR PF D e := by
  intro Sig n 𝒯 hid hsh Ω ι _ _ PF D hA hS e
  obtain ⟨A⟩ := hA
  rw [expansion_swapSolid_value, tVar_true_value A e]
  exact tSubst_value Sig n 𝒯 hid Ω ι PF _ ⟨A.transposeAdm⟩
    (fun ω => sigConsistent_transposeG Sig n hsh (D ω) (hS ω)) e

section Instances

open Complex

end Instances

end RBM8D.Graphs
