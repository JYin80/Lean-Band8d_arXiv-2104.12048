module

public import RBM8D.Kernel.Lattice
public import RBM8D.Bound.AuxTree
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-!
# The momentum form of a graph value on `ℤ^d` ([I, (7.29)–(7.30)])

A graph has a finite vertex set `V` with a pinned vertex `v₀`, edges `c ∈ ι` with tail and head
`e c = (t_c, h_c)`, a kernel `k_c` on `ℤ^d` and a symbol `f_c` on `ℝ^d` for every edge. For a
spanning tree `T` (a list of edges with `TreeEdges`) and an edge `f ∈ T`, the cut `C_f`
(`FT1a.cutSide`) is the set of vertices joined to `h_f` in `T ∖ {f}`, and
`N_{fc} = FT1a.cutCoef e T f c = 1_{h_c ∈ C_f} − 1_{t_c ∈ C_f}`. The loop momenta are
`q_c ∈ [−π, π]^d` for `c ∉ T`; the momentum of a tree edge `f` is `λ_f(P) − Σ_{c ∉ T} N_{fc} q_c`,
with `λ_f(P) = Σ_{v ∈ C_f} P_v` (`FT1a.edgeMom`). For `Σ_v P_v = 0` these are the momenta of
[I, (7.29)]: at every vertex `v` the momenta of the edges entering `v` minus those of the edges
leaving `v` sum to `P_v`.

* `FT1a.graphFourier`: [I, (7.29)–(7.30)] directly on `ℤ^d`: for two spanning trees `T₁`, `T₂`,
  kernels `k_c` with symbols `f_c ∈ L²([−π, π]^d)`, `ℓ¹` kernels on `T₁ ∩ T₂`, and an absolutely
  summable graph value,
  `Σ_{σ, σ_{v₀} = 0} Π_c k_c(σ_{h_c} − σ_{t_c}) e^{i Σ_v P_v·σ_v}
    = (2π)^{-dL} ∫_{[−π,π]^{dL}} Π_c f_c(ℓ_c(q) + λ_c(P)) dq`,
  with an integrable integrand, `L = |E| − |V| + 1`.
* `FT1a.momentumCS`: the Cauchy–Schwarz bound
  `∫ Π_c g_c(ℓ_c(q) + λ_c(P)) dq
    ≤ Π_{T₁∩T₂} ‖g_c‖_∞ Π_{c ∉ T₁} ‖g_c‖₂ (2π)^{d(L−m)/2} Π_{T₁∖T₂} ‖g_f‖₂`
  for nonnegative periodic `g_c`, `m = |T₁ ∖ T₂|`.
* `FT1a.cutMatrix_det_ne_zero`: the integer matrix `N_{fc}`, `f ∈ T₁ ∖ T₂`, `c ∈ T₂ ∖ T₁`, is
  square with nonzero determinant.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace RBM8D

/-! ## Cuts of a spanning tree -/

section Tree

variable {V ι : Type*} [Fintype V] [DecidableEq ι]

/-- For an edge `f` of a list `T` of edges, `C_f` is the set of vertices joined to the head `h_f`
by edges of `T` other than (one copy of) `f`. -/
def FT1a.cutSide (e : ι → V × V) (T : List ι) (f : ι) (v : V) : Prop :=
  (SimpleGraph.fromRel fun u w => (u, w) ∈ (T.erase f).map e).Reachable (e f).2 v

open Classical in
/-- The indicator `1_{v ∈ C_f}`. -/
def FT1a.cutInd (e : ι → V × V) (T : List ι) (f : ι) (v : V) : ℤ :=
  if FT1a.cutSide e T f v then 1 else 0

/-- `N_{fc} = 1_{h_c ∈ C_f} − 1_{t_c ∈ C_f}`: the signed crossing of the cut `C_f` by the edge
`c`. -/
def FT1a.cutCoef (e : ι → V × V) (T : List ι) (f c : ι) : ℤ :=
  FT1a.cutInd e T f (e c).2 - FT1a.cutInd e T f (e c).1

variable {e : ι → V × V} {T : List ι}

private theorem FT1a_cutInd_head (f : ι) : FT1a.cutInd e T f (e f).2 = 1 := by
  unfold FT1a.cutInd
  simp only [show FT1a.cutSide e T f (e f).2 from SimpleGraph.Reachable.refl _, ↓reduceIte]

/-- Every other tree edge has both ends on the same side of `C_f`. -/
private theorem FT1a_cutInd_other {f g : ι} (hg : g ∈ T) (hgf : g ≠ f) :
    FT1a.cutInd e T f (e g).2 = FT1a.cutInd e T f (e g).1 := by
  have hreach : (SimpleGraph.fromRel fun u w => (u, w) ∈ (T.erase f).map e).Reachable
      (e g).1 (e g).2 := by
    by_cases h : (e g).1 = (e g).2
    · rw [h]
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.fromRel_adj]
      refine ⟨h, Or.inl ?_⟩
      exact List.mem_map.2 ⟨g, (List.mem_erase_of_ne hgf).2 hg, rfl⟩
  have : FT1a.cutSide e T f (e g).2 ↔ FT1a.cutSide e T f (e g).1 :=
    ⟨fun h => h.trans hreach.symm, fun h => h.trans hreach⟩
  unfold FT1a.cutInd
  by_cases h : FT1a.cutSide e T f (e g).1
  · simp only [h, this.2 h, ↓reduceIte]
  · simp only [h, mt this.1 h, ↓reduceIte]

/-- The number of edges of the graph of an edge list is at most the length of the list. -/
private theorem FT1a_card_edgeSet_le (es : List (V × V)) :
    Nat.card (SimpleGraph.fromRel fun u w => (u, w) ∈ es).edgeSet ≤ es.length := by
  classical
  set s : Finset (Sym2 V) := (es.map fun p => s(p.1, p.2)).toFinset
  have hsub : (SimpleGraph.fromRel fun u w => (u, w) ∈ es).edgeSet ⊆ (s : Set (Sym2 V)) := by
    intro z hz
    induction z using Sym2.ind with
    | h u w =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hz
      simp only [s, Finset.mem_coe, List.mem_toFinset, List.mem_map]
      rcases hz.2 with h | h
      · exact ⟨(u, w), h, rfl⟩
      · exact ⟨(w, u), h, Sym2.eq_swap⟩
  calc Nat.card (SimpleGraph.fromRel fun u w => (u, w) ∈ es).edgeSet
      = (SimpleGraph.fromRel fun u w => (u, w) ∈ es).edgeSet.ncard := Nat.card_coe_set_eq _
    _ ≤ (s : Set (Sym2 V)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet s)
    _ = s.card := Set.ncard_coe_finset s
    _ ≤ (es.map fun p => s(p.1, p.2)).length := List.toFinset_card_le _
    _ = es.length := List.length_map _

/-- The two ends of a tree edge lie on different sides of its cut. -/
private theorem FT1a_cutInd_tail (hT : TreeEdges (T.map e)) {f : ι} (hf : f ∈ T) :
    FT1a.cutInd e T f (e f).1 = 0 := by
  unfold FT1a.cutInd
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  intro hr
  let H := SimpleGraph.fromRel fun u w => (u, w) ∈ (T.erase f).map e
  have hlift : ∀ a b, (SimpleGraph.fromRel fun u w => (u, w) ∈ T.map e).Reachable a b →
      H.Reachable a b := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => rfl
    | @cons u w z hadj _ ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      rw [SimpleGraph.fromRel_adj] at hadj
      have key : ∀ x y, (x, y) ∈ T.map e → x ≠ y → H.Reachable x y := by
        intro x y hxy hne
        obtain ⟨g, hg, hge⟩ := List.mem_map.1 hxy
        by_cases hgf : g = f
        · subst hgf
          have h1 : (e g).1 = x := by rw [hge]
          have h2 : (e g).2 = y := by rw [hge]
          rw [← h1, ← h2]
          exact hr.symm
        · refine SimpleGraph.Adj.reachable ?_
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inl (List.mem_map.2 ⟨g, (List.mem_erase_of_ne hgf).2 hg, hge⟩)⟩
      rcases hadj.2 with h | h
      · exact key u w h hadj.1
      · exact (key w u h hadj.1.symm).symm
  have hne : Nonempty V := ⟨(e f).1⟩
  have hconn : H.Connected := ⟨fun a b => hlift a b (hT.2 a b)⟩
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have h2 : Nat.card H.edgeSet ≤ ((T.erase f).map e).length := FT1a_card_edgeSet_le _
  rw [List.length_map, List.length_erase_of_mem hf] at h2
  have h3 := hT.1
  rw [List.length_map] at h3
  rw [Nat.card_eq_fintype_card] at h1
  have hpos : 0 < T.length := List.length_pos_of_mem hf
  omega

/-- The edges of a spanning tree are distinct. -/
private theorem FT1a_nodup (hT : TreeEdges (T.map e)) : T.Nodup := by
  rw [List.nodup_iff_forall_not_duplicate]
  intro g hdup
  have hcount := List.duplicate_iff_two_le_count.1 hdup
  have hmem : g ∈ T.erase g := by
    rw [← List.count_pos_iff, List.count_erase_self]
    omega
  have h0 := FT1a_cutInd_tail hT (List.mem_of_mem_erase hmem)
  have h1 : FT1a.cutSide e T g (e g).1 := by
    by_cases heq : (e g).2 = (e g).1
    · unfold FT1a.cutSide
      rw [← heq]
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.fromRel_adj]
      exact ⟨heq, Or.inr (List.mem_map.2 ⟨g, hmem, rfl⟩)⟩
  unfold FT1a.cutInd at h0
  simp [h1] at h0

/-- The cut coefficient of a tree edge `g` at the cut of a tree edge `f` is `δ_{fg}`. -/
private theorem FT1a_cutCoef_tree (hT : TreeEdges (T.map e)) {f g : ι} (hf : f ∈ T) (hg : g ∈ T) :
    FT1a.cutCoef e T f g = if g = f then 1 else 0 := by
  unfold FT1a.cutCoef
  by_cases hgf : g = f
  · subst hgf
    rw [FT1a_cutInd_head, FT1a_cutInd_tail hT hf]
    simp
  · rw [FT1a_cutInd_other hg hgf, sub_self]
    simp [hgf]

/-- A function on the vertices that agrees at the two ends of every tree edge is constant. -/
private theorem FT1a_const_of_tree {A : Type*} (hT : TreeEdges (T.map e)) (G : V → A)
    (hG : ∀ g ∈ T, G (e g).2 = G (e g).1) (a b : V) : G a = G b := by
  obtain ⟨p⟩ := hT.2 a b
  induction p with
  | nil => rfl
  | @cons u w z hadj _ ih =>
    rw [← ih]
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · obtain ⟨g, hg, hge⟩ := List.mem_map.1 h
      have := hG g hg
      rw [hge] at this
      exact this.symm
    · obtain ⟨g, hg, hge⟩ := List.mem_map.1 h
      have := hG g hg
      rw [hge] at this
      exact this

/-- The potential of a vertex function relative to a vertex `v` is the sum of its increments along
the tree edges whose cut separates the two vertices:
`σ_w − σ_v = Σ_{f ∈ T} (1_{w ∈ C_f} − 1_{v ∈ C_f}) Δ_f σ`. -/
private theorem FT1a_pot_eq {A : Type*} [AddCommGroup A] [Fintype ι]
    (hT : TreeEdges (T.map e)) (σ : V → A) (w v : V) :
    σ w - σ v = ∑ f : {f // f ∈ T},
      (FT1a.cutInd e T f.1 w - FT1a.cutInd e T f.1 v) • (σ (e f.1).2 - σ (e f.1).1) := by
  set G : V → A := fun u =>
    σ u - ∑ f : {f // f ∈ T}, FT1a.cutInd e T f.1 u • (σ (e f.1).2 - σ (e f.1).1)
  have hG : ∀ g ∈ T, G (e g).2 = G (e g).1 := by
    intro g hg
    simp only [G]
    rw [sub_eq_sub_iff_sub_eq_sub, ← Finset.sum_sub_distrib]
    simp_rw [← sub_smul]
    rw [Finset.sum_eq_single ⟨g, hg⟩]
    · rw [← FT1a.cutCoef.eq_def, FT1a_cutCoef_tree hT hg hg]
      simp
    · intro f _ hf
      have hgf : g ≠ f.1 := fun h => hf (Subtype.ext h.symm)
      rw [FT1a_cutInd_other hg hgf, sub_self, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := FT1a_const_of_tree hT G hG w v
  simp only [G] at h
  rw [sub_eq_sub_iff_sub_eq_sub] at h
  rw [h, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]

/-- The increment of any vertex function along any edge `c` is the sum of its increments along the
tree edges, weighted by the cut coefficients: `Δ_c σ = Σ_{f ∈ T} N_{fc} Δ_f σ`. -/
private theorem FT1a_incr_eq {A : Type*} [AddCommGroup A] [Fintype ι]
    (hT : TreeEdges (T.map e)) (σ : V → A) (c : ι) :
    σ (e c).2 - σ (e c).1 =
      ∑ f : {f // f ∈ T}, FT1a.cutCoef e T f.1 c • (σ (e f.1).2 - σ (e f.1).1) := by
  rw [FT1a_pot_eq hT σ]
  rfl

end Tree

/-! ## Momenta of the edges -/

section Mom

variable {d : ℕ} {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The external momentum `λ_f(P) = Σ_{v ∈ C_f} P_v` carried by an edge `f` of `T`. -/
def FT1a.extMom (e : ι → V × V) (T : List ι) (P : V → Fin d → ℝ) (f : ι) : Fin d → ℝ :=
  ∑ v, (FT1a.cutInd e T f v : ℝ) • P v

/-- The momentum `ℓ_c(q) + λ_c(P)` of an edge `c` for the loop momenta `q_c`, `c ∉ T`: `q_c` for
`c ∉ T`, and `λ_c(P) − Σ_{c' ∉ T} N_{c c'} q_{c'}` for `c ∈ T`. For `Σ_v P_v = 0`, at every vertex
`v` the momenta of the edges entering `v` minus those of the edges leaving `v` sum to `P_v`
([I, (7.29)]). -/
def FT1a.edgeMom (e : ι → V × V) (T : List ι) (P : V → Fin d → ℝ)
    (q : {c // c ∉ T} → Fin d → ℝ) (c : ι) : Fin d → ℝ :=
  if h : c ∈ T then FT1a.extMom e T P c - ∑ c' : {c // c ∉ T}, (FT1a.cutCoef e T c c'.1 : ℝ) • q c'
  else q ⟨c, h⟩

variable {e : ι → V × V} {T : List ι}

/-- The momentum of an edge outside the tree is its loop momentum. -/
theorem FT1a.edgeMom_of_not_mem (P : V → Fin d → ℝ) (q : {c // c ∉ T} → Fin d → ℝ) {c : ι}
    (hc : c ∉ T) : FT1a.edgeMom e T P q c = q ⟨c, hc⟩ := by
  unfold FT1a.edgeMom
  simp [hc]

/-- The momentum of a tree edge `c` is `λ_c(P) − Σ_{c' ∉ T} N_{c c'} q_{c'}`. -/
theorem FT1a.edgeMom_of_mem (P : V → Fin d → ℝ) (q : {c // c ∉ T} → Fin d → ℝ) {c : ι}
    (hc : c ∈ T) : FT1a.edgeMom e T P q c =
      FT1a.extMom e T P c - ∑ c' : {c // c ∉ T}, (FT1a.cutCoef e T c c'.1 : ℝ) • q c' := by
  unfold FT1a.edgeMom
  simp [hc]

private theorem FT1a_continuous_edgeMom (P : V → Fin d → ℝ) (c : ι) :
    Continuous fun q : {c // c ∉ T} → Fin d → ℝ => FT1a.edgeMom e T P q c := by
  by_cases hc : c ∈ T
  · simp_rw [FT1a.edgeMom_of_mem P _ hc]
    fun_prop
  · simp_rw [FT1a.edgeMom_of_not_mem P _ hc]
    fun_prop

/-- A product over the edges splits into the tree edges and the other edges. -/
private theorem FT1a_prod_split {M : Type*} [CommMonoid M] (T : List ι) (F : ι → M) :
    ∏ c, F c = (∏ f : {f // f ∈ T}, F f.1) * ∏ c : {c // c ∉ T}, F c.1 := by
  have h := (Fintype.prod_subtype_mul_prod_subtype (fun c => c ∈ T) F).symm
  rw [h]
  refine congrArg₂ (· * ·) ?_ ?_
  · convert rfl
  · convert rfl

/-- A product over the edges splits into the edges of `T₁ ∩ T₂`, of `T₁ ∖ T₂` and outside `T₁`. -/
private theorem FT1a_prod_split3 {M : Type*} [CommMonoid M] (T₁ T₂ : List ι) (F : ι → M) :
    ∏ c, F c = (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, F c.1) * (∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, F c.1) *
      ∏ c : {c // c ∉ T₁}, F c.1 := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun c => c ∈ T₁ ∧ c ∈ T₂) (by simp) F,
    ← Finset.prod_subtype (Finset.univ.filter fun c => c ∈ T₁ ∧ c ∉ T₂) (by simp) F,
    ← Finset.prod_subtype (Finset.univ.filter fun c => c ∉ T₁) (by simp) F,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun c => c ∈ T₁),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter fun c => c ∈ T₁)
      (fun c => c ∈ T₂)]
  simp only [Finset.filter_filter]

/-- A sum over the edges splits into the tree edges and the other edges. -/
private theorem FT1a_sum_split {M : Type*} [AddCommMonoid M] (T : List ι) (F : ι → M) :
    ∑ c, F c = (∑ f : {f // f ∈ T}, F f.1) + ∑ c : {c // c ∉ T}, F c.1 := by
  have h := (Fintype.sum_subtype_add_sum_subtype (fun c => c ∈ T) F).symm
  rw [h]
  refine congrArg₂ (· + ·) ?_ ?_
  · convert rfl
  · convert rfl

/-- The pairing `p·x = Σ_i p_i x_i`, so that `zexp p x = e^{i p·x}`. -/
private def FT1a_dot (p : Fin d → ℝ) (x : Fin d → ℤ) : ℝ := ∑ i, p i * (x i : ℝ)

private theorem FT1a_zexp_eq (p : Fin d → ℝ) (x : Fin d → ℤ) :
    zexp p x = Complex.exp (((FT1a_dot p x : ℝ) : ℂ) * Complex.I) := rfl

private theorem FT1a_prod_zexp {κ : Type*} (s : Finset κ) (p : κ → Fin d → ℝ)
    (x : κ → Fin d → ℤ) :
    ∏ j ∈ s, zexp (p j) (x j) =
      Complex.exp (((∑ j ∈ s, FT1a_dot (p j) (x j) : ℝ) : ℂ) * Complex.I) := by
  simp_rw [FT1a_zexp_eq]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]

private theorem FT1a_dot_sum_left {κ : Type*} (s : Finset κ) (p : κ → Fin d → ℝ)
    (x : Fin d → ℤ) : FT1a_dot (∑ j ∈ s, p j) x = ∑ j ∈ s, FT1a_dot (p j) x := by
  unfold FT1a_dot
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem FT1a_dot_sum_right {κ : Type*} (s : Finset κ) (p : Fin d → ℝ)
    (x : κ → Fin d → ℤ) : FT1a_dot p (∑ j ∈ s, x j) = ∑ j ∈ s, FT1a_dot p (x j) := by
  unfold FT1a_dot
  simp only [Finset.sum_apply, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_comm

private theorem FT1a_dot_smul_left (a : ℝ) (p : Fin d → ℝ) (x : Fin d → ℤ) :
    FT1a_dot (a • p) x = a * FT1a_dot p x := by
  unfold FT1a_dot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem FT1a_dot_zsmul_right (n : ℤ) (p : Fin d → ℝ) (x : Fin d → ℤ) :
    FT1a_dot p (n • x) = n * FT1a_dot p x := by
  unfold FT1a_dot
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private theorem FT1a_dot_sub_left (p p' : Fin d → ℝ) (x : Fin d → ℤ) :
    FT1a_dot (p - p') x = FT1a_dot p x - FT1a_dot p' x := by
  unfold FT1a_dot
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem FT1a_dot_neg_right (p : Fin d → ℝ) (x : Fin d → ℤ) :
    FT1a_dot p (-x) = - FT1a_dot p x := by
  unfold FT1a_dot
  simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

/-- The vertex positions with `σ_{v₀} = 0` and prescribed increments `y_f` along the tree edges. -/
private def FT1a_ofY (e : ι → V × V) (T : List ι) (v₀ : V) (y : {f // f ∈ T} → Fin d → ℤ)
    (w : V) : Fin d → ℤ :=
  ∑ f, (FT1a.cutInd e T f.1 w - FT1a.cutInd e T f.1 v₀) • y f

private theorem FT1a_ofY_incr (v₀ : V) (y : {f // f ∈ T} → Fin d → ℤ) (c : ι) :
    FT1a_ofY e T v₀ y (e c).2 - FT1a_ofY e T v₀ y (e c).1 =
      ∑ f : {f // f ∈ T}, FT1a.cutCoef e T f.1 c • y f := by
  unfold FT1a_ofY FT1a.cutCoef
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← sub_smul]
  congr 1
  ring

private theorem FT1a_ofY_incr_tree (hT : TreeEdges (T.map e)) (v₀ : V)
    (y : {f // f ∈ T} → Fin d → ℤ) (g : {f // f ∈ T}) :
    FT1a_ofY e T v₀ y (e g.1).2 - FT1a_ofY e T v₀ y (e g.1).1 = y g := by
  rw [FT1a_ofY_incr, Finset.sum_eq_single g]
  · rw [FT1a_cutCoef_tree hT g.2 g.2]
    simp
  · intro f _ hf
    have hgf : g.1 ≠ f.1 := fun h => hf (Subtype.ext h.symm)
    rw [FT1a_cutCoef_tree hT f.2 g.2]
    simp [hgf]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Vertex positions pinned at `v₀` correspond to their increments along the tree edges. -/
private def FT1a_equivY (hT : TreeEdges (T.map e)) (v₀ : V) :
    {σ : V → Fin d → ℤ // σ v₀ = 0} ≃ ({f // f ∈ T} → Fin d → ℤ) where
  toFun σ f := σ.1 (e f.1).2 - σ.1 (e f.1).1
  invFun y := ⟨FT1a_ofY e T v₀ y, by simp [FT1a_ofY]⟩
  left_inv σ := by
    refine Subtype.ext (funext fun w => ?_)
    have h := FT1a_pot_eq hT σ.1 w v₀
    rw [σ.2, sub_zero] at h
    exact h.symm
  right_inv y := funext fun g => FT1a_ofY_incr_tree hT v₀ y g

/-- The phase: `Σ_v P_v·σ_v = Σ_{f ∈ T} λ_f(P)·y_f` for the positions with increments `y`, when
`Σ_v P_v = 0`. -/
private theorem FT1a_phase (v₀ : V) (P : V → Fin d → ℝ) (hP : ∑ v, P v = 0)
    (y : {f // f ∈ T} → Fin d → ℤ) :
    ∑ v, FT1a_dot (P v) (FT1a_ofY e T v₀ y v) =
      ∑ f : {f // f ∈ T}, FT1a_dot (FT1a.extMom e T P f.1) (y f) := by
  unfold FT1a_ofY FT1a.extMom
  simp_rw [FT1a_dot_sum_right, FT1a_dot_zsmul_right, FT1a_dot_sum_left, FT1a_dot_smul_left]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h0 : ∑ v, (FT1a.cutInd e T f.1 v₀ : ℝ) * FT1a_dot (P v) (y f) = 0 := by
    rw [← Finset.mul_sum, ← FT1a_dot_sum_left, hP]
    simp [FT1a_dot]
  rw [← sub_zero (∑ v, (FT1a.cutInd e T f.1 v : ℝ) * FT1a_dot (P v) (y f)), ← h0,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  push_cast
  ring

/-- The exponent of the momentum side: `Σ_{f ∈ T} ℓ_f(q)·y_f = Σ_f λ_f·y_f − Σ_{c ∉ T} q_c·x_c`
with `x_c = Σ_f N_{fc} y_f`. -/
private theorem FT1a_mom_phase (P : V → Fin d → ℝ) (q : {c // c ∉ T} → Fin d → ℝ)
    (y : {f // f ∈ T} → Fin d → ℤ) :
    ∑ f : {f // f ∈ T}, FT1a_dot (FT1a.edgeMom e T P q f.1) (y f) =
      ∑ f : {f // f ∈ T}, FT1a_dot (FT1a.extMom e T P f.1) (y f) +
        ∑ c : {c // c ∉ T},
          FT1a_dot (q c) (-∑ f : {f // f ∈ T}, FT1a.cutCoef e T f.1 c.1 • y f) := by
  simp_rw [fun f : {f // f ∈ T} => FT1a.edgeMom_of_mem (e := e) P q f.2, FT1a_dot_sub_left,
    FT1a_dot_sum_left, FT1a_dot_smul_left, FT1a_dot_neg_right, FT1a_dot_sum_right,
    FT1a_dot_zsmul_right, Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 2
  rw [Finset.sum_comm]

end Mom

/-! ## Products of absolutely summable families -/

/-- For finitely many absolutely summable families `a_j`, the products `Π_j a_j(y_j)` are absolutely
summable over `y`, with sum `Π_j Σ_x a_j(x)`. -/
private def FT1a_PiSum (X : Type*) (J : Type*) [Fintype J] : Prop :=
  ∀ (a : J → X → ℂ), (∀ j, Summable fun x => ‖a j x‖) →
      Summable (fun y : J → X => ‖∏ j, a j (y j)‖) ∧
        HasSum (fun y : J → X => ∏ j, a j (y j)) (∏ j, ∑' x, a j x)

private theorem FT1a_piSum {X : Type*} : ∀ (J : Type*) [Fintype J], FT1a_PiSum X J := by
  intro J _
  refine Fintype.induction_empty_option (P := fun J _ => FT1a_PiSum X J) ?_ ?_ ?_ J
  · intro α β _ eqv h a ha
    let _ : Fintype α := Fintype.ofEquiv β eqv.symm
    obtain ⟨h1, h2⟩ := h (fun i => a (eqv i)) (fun i => ha (eqv i))
    let E : (α → X) ≃ (β → X) := Equiv.arrowCongr eqv (Equiv.refl X)
    have key : ∀ z : α → X, ∏ j, a j ((E z) j) = ∏ i, a (eqv i) (z i) := by
      intro z
      exact (Fintype.prod_equiv eqv (fun i => a (eqv i) (z i)) _
        (fun i => by simp [E, Equiv.arrowCongr_apply])).symm
    have hp : ∏ j, ∑' x, a j x = ∏ i, ∑' x, a (eqv i) x :=
      (Fintype.prod_equiv eqv (fun i => ∑' x, a (eqv i) x) _ (fun _ => rfl)).symm
    have hs : Summable ((fun y : β → X => ‖∏ j, a j (y j)‖) ∘ E) := by
      have : ((fun y : β → X => ‖∏ j, a j (y j)‖) ∘ E) = fun z => ‖∏ i, a (eqv i) (z i)‖ :=
        funext fun z => by simp only [Function.comp_apply, key]
      rw [this]; exact h1
    have hh : HasSum ((fun y : β → X => ∏ j, a j (y j)) ∘ E) (∏ j, ∑' x, a j x) := by
      have : ((fun y : β → X => ∏ j, a j (y j)) ∘ E) = fun z => ∏ i, a (eqv i) (z i) :=
        funext fun z => by simp only [Function.comp_apply, key]
      rw [this, hp]; exact h2
    constructor
    · have := (Equiv.summable_iff E).mp hs
      exact this
    · have := (Equiv.hasSum_iff E).mp hh
      exact this
  · intro a _
    have h0 : ∀ b' : _ → X, b' = fun j => PEmpty.elim j := fun b' =>
      funext fun j => j.elim
    have h1 := hasSum_single (f := fun y : _ → X => ‖∏ j, a j (y j)‖)
      (fun j => PEmpty.elim j) (fun b' hb' => absurd (h0 b') hb')
    have h2 := hasSum_single (f := fun y : _ → X => ∏ j, a j (y j))
      (fun j => PEmpty.elim j) (fun b' hb' => absurd (h0 b') hb')
    refine ⟨h1.summable, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty] at h2 ⊢
    exact h2
  · intro α _ h a ha
    obtain ⟨h1, h2⟩ := h (fun i => a (some i)) (fun i => ha (some i))
    let E := (Equiv.piOptionEquivProd (β := fun _ : Option α => X)).symm
    have hprod : ∀ z : X × (α → X), ∏ j, a j (E z j) = a none z.1 * ∏ i, a (some i) (z.2 i) := by
      intro z
      rw [Fintype.prod_option]
      rfl
    have hs1 : Summable fun z : X × (α → X) => ‖a none z.1‖ * ‖∏ i, a (some i) (z.2 i)‖ :=
      summable_mul_of_summable_norm (f := fun x => ‖a none x‖)
        (g := fun z : α → X => ‖∏ i, a (some i) (z i)‖) (by simpa using ha none) (by simpa using h1)
    have hs : Summable ((fun y : Option α → X => ‖∏ j, a j (y j)‖) ∘ E) := by
      have : ((fun y : Option α → X => ‖∏ j, a j (y j)‖) ∘ E) =
          fun z => ‖a none z.1‖ * ‖∏ i, a (some i) (z.2 i)‖ :=
        funext fun z => by simp only [Function.comp_apply, hprod, norm_mul]
      rw [this]; exact hs1
    have hm := HasSum.mul (f := a none) (g := fun z : α → X => ∏ i, a (some i) (z i))
      (ha none).of_norm.hasSum h2
      (summable_mul_of_summable_norm (R := ℂ) (f := a none)
        (g := fun z : α → X => ∏ i, a (some i) (z i)) (ha none) h1)
    have hh : HasSum ((fun y : Option α → X => ∏ j, a j (y j)) ∘ E) (∏ j, ∑' x, a j x) := by
      have : ((fun y : Option α → X => ∏ j, a j (y j)) ∘ E) =
          fun z => a none z.1 * ∏ i, a (some i) (z.2 i) :=
        funext fun z => by simp only [Function.comp_apply, hprod]
      rw [this, Fintype.prod_option]; exact hm
    constructor
    · have := (Equiv.summable_iff E).mp hs
      exact this
    · have := (Equiv.hasSum_iff E).mp hh
      exact this

/-! ## The identity for `ℓ¹` kernels on the tree edges -/

section L1

variable {d : ℕ}

/-- The Fourier series of an `ℓ¹` kernel is continuous. -/
private theorem FT1a_continuous_zdSeries (K : (Fin d → ℤ) → ℂ) (hK : Summable fun x => ‖K x‖) :
    Continuous (zdSeries K) := by
  unfold zdSeries
  refine continuous_tsum (fun x => ?_) hK (fun x p => ?_)
  · unfold zexp
    fun_prop
  · rw [norm_mul, norm_zexp, mul_one]

/-- The Fourier series of an `ℓ¹` kernel is bounded by its `ℓ¹` norm. -/
private theorem FT1a_norm_zdSeries_le (K : (Fin d → ℤ) → ℂ) (hK : Summable fun x => ‖K x‖)
    (p : Fin d → ℝ) : ‖zdSeries K p‖ ≤ ∑' x, ‖K x‖ := by
  unfold zdSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · simpa only [norm_mul, norm_zexp, mul_one] using hK
  · simp only [norm_mul, norm_zexp, mul_one]

/-- The restriction of Lebesgue measure to `([−π, π]^d)^A` is the product of the restrictions. -/
private theorem FT1a_restrict_cube (A : Type*) [Fintype A] :
    (volume : Measure (A → Fin d → ℝ)).restrict (Set.univ.pi fun _ => cubePi d) =
      Measure.pi fun _ => volume.restrict (cubePi d) := by
  rw [volume_pi, Measure.restrict_pi_pi]

/-- `∫_{[−π,π]^d} f(p) e^{-ip·x} dp = (2π)^d k(x)` for `k = latticeFourier f`. -/
private theorem FT1a_integral_eq_lf (φ : (Fin d → ℝ) → ℂ) (x : Fin d → ℤ) :
    ∫ p in cubePi d, φ p * zexp p (-x) = (2 * Real.pi : ℂ) ^ d * latticeFourier φ x := by
  unfold latticeFourier
  have hne : ((2 * Real.pi : ℂ) ^ d) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Real.two_pi_pos.ne')
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]
variable {e : ι → V × V} {T : List ι}

/-- [I, (7.29)–(7.30)] when the kernels of the tree edges are in `ℓ¹` with symbols their Fourier
series, and the symbols of the other edges are integrable. -/
private theorem FT1a_l1 (v₀ : V) (hT : TreeEdges (T.map e)) (P : V → Fin d → ℝ)
    (hP : ∑ v, P v = 0) (k : ι → (Fin d → ℤ) → ℂ) (φ : ι → (Fin d → ℝ) → ℂ)
    (hk : ∀ f ∈ T, Summable fun x => ‖k f x‖) (hφT : ∀ f ∈ T, φ f = zdSeries (k f))
    (hφi : ∀ c, c ∉ T → IntegrableOn (φ c) (cubePi d))
    (hlf : ∀ c, c ∉ T → k c = latticeFourier (φ c)) :
    IntegrableOn (fun q => ∏ c, φ c (FT1a.edgeMom e T P q c))
        (Set.univ.pi fun _ : {c // c ∉ T} => cubePi d) ∧
      ∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
          (∏ c, k c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v) =
        ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T}))⁻¹ *
          ∫ q in Set.univ.pi (fun _ : {c // c ∉ T} => cubePi d),
            ∏ c, φ c (FT1a.edgeMom e T P q c) := by
  set μ : Measure ({c // c ∉ T} → Fin d → ℝ) :=
    Measure.pi fun _ => volume.restrict (cubePi d) with hμ
  simp only [IntegrableOn]
  rw [FT1a_restrict_cube {c // c ∉ T}]
  -- the term of the tree sum
  let x : ({f // f ∈ T} → Fin d → ℤ) → {c // c ∉ T} → Fin d → ℤ := fun y c =>
    ∑ f : {f // f ∈ T}, FT1a.cutCoef e T f.1 c.1 • y f
  let C : ({f // f ∈ T} → Fin d → ℤ) → ℂ := fun y =>
    ∏ f : {f // f ∈ T}, k f.1 (y f) * zexp (FT1a.extMom e T P f.1) (y f)
  let t : ({f // f ∈ T} → Fin d → ℤ) → ℂ := fun y => C y * ∏ c : {c // c ∉ T}, k c.1 (x y c)
  -- the position side in tree variables
  have hL : ∀ y, (∏ c, k c (FT1a_ofY e T v₀ y (e c).2 - FT1a_ofY e T v₀ y (e c).1)) *
      ∏ v, zexp (P v) (FT1a_ofY e T v₀ y v) = t y := by
    intro y
    rw [FT1a_prod_split T]
    have h1 : ∀ f : {f // f ∈ T},
        k f.1 (FT1a_ofY e T v₀ y (e f.1).2 - FT1a_ofY e T v₀ y (e f.1).1) =
        k f.1 (y f) := fun f => by rw [FT1a_ofY_incr_tree hT v₀ y f]
    have h2 : ∀ c : {c // c ∉ T},
        k c.1 (FT1a_ofY e T v₀ y (e c.1).2 - FT1a_ofY e T v₀ y (e c.1).1) =
        k c.1 (x y c) := fun c => by rw [FT1a_ofY_incr]
    have h3 : ∏ v, zexp (P v) (FT1a_ofY e T v₀ y v) =
        ∏ f : {f // f ∈ T}, zexp (FT1a.extMom e T P f.1) (y f) := by
      rw [FT1a_prod_zexp, FT1a_prod_zexp, FT1a_phase v₀ P hP y]
    simp only [t, C]
    simp only [h1, h2, h3, Finset.prod_mul_distrib]
    ring
  have hLHS : ∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
      (∏ c, k c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v) = ∑' y, t y := by
    rw [← (FT1a_equivY (d := d) hT v₀).symm.tsum_eq]
    exact tsum_congr fun y => hL y
  -- the momentum side
  let g : ({f // f ∈ T} → Fin d → ℤ) → {c // c ∉ T} → (Fin d → ℝ) → ℂ := fun y c p =>
    φ c.1 p * zexp p (-x y c)
  let u : ({f // f ∈ T} → Fin d → ℤ) → ({c // c ∉ T} → Fin d → ℝ) → ℂ := fun y q =>
    (∏ c : {c // c ∉ T}, φ c.1 (q c)) *
      ∏ f : {f // f ∈ T}, k f.1 (y f) * zexp (FT1a.edgeMom e T P q f.1) (y f)
  have hu : ∀ y q, u y q = C y * ∏ c : {c // c ∉ T}, g y c (q c) := by
    intro y q
    have hph : ∏ f : {f // f ∈ T}, zexp (FT1a.edgeMom e T P q f.1) (y f) =
        (∏ f : {f // f ∈ T}, zexp (FT1a.extMom e T P f.1) (y f)) *
          ∏ c : {c // c ∉ T}, zexp (q c) (-x y c) := by
      rw [FT1a_prod_zexp, FT1a_prod_zexp, FT1a_prod_zexp, FT1a_mom_phase P q y, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [u, C, g]
    rw [Finset.prod_mul_distrib, hph, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  have hgi : ∀ y c, Integrable (g y c) (volume.restrict (cubePi d)) := by
    intro y c
    refine (hφi c.1 c.2).mul_bdd (c := 1) ?_ ?_
    · exact (show Continuous fun p : Fin d → ℝ => zexp p (-x y c) by unfold zexp; fun_prop)
        |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => by rw [norm_zexp]
  have hui : ∀ y, Integrable (u y) μ := by
    intro y
    have : u y = fun q => C y * ∏ c : {c // c ∉ T}, g y c (q c) := funext (hu y)
    rw [this]
    exact (Integrable.fintype_prod (f := g y) (hgi y)).const_mul _
  have hint : ∀ y, ∫ q, u y q ∂μ =
      (2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T}) * t y := by
    intro y
    have : u y = fun q => C y * ∏ c : {c // c ∉ T}, g y c (q c) := funext (hu y)
    rw [this, integral_const_mul, integral_fintype_prod_eq_prod]
    have hg : ∀ c : {c // c ∉ T}, ∫ p, g y c p ∂(volume.restrict (cubePi d)) =
        (2 * Real.pi : ℂ) ^ d * k c.1 (x y c) := by
      intro c
      simp only [g]
      rw [FT1a_integral_eq_lf, ← hlf c.1 c.2]
    rw [Fintype.prod_congr _ _ hg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← pow_mul]
    simp only [t]
    ring
  -- absolute summability over the tree variables
  obtain ⟨hks, -⟩ := FT1a_piSum (X := Fin d → ℤ) {f // f ∈ T} (fun f => k f.1) (fun f => hk f.1 f.2)
  have hnu : ∀ y q, ‖u y q‖ =
      (∏ f : {f // f ∈ T}, ‖k f.1 (y f)‖) * ∏ c : {c // c ∉ T}, ‖φ c.1 (q c)‖ := by
    intro y q
    simp only [u, norm_mul, norm_prod, norm_zexp, mul_one]
    ring
  have hnorm_int :
      Integrable (fun q : {c // c ∉ T} → Fin d → ℝ => ∏ c : {c // c ∉ T}, ‖φ c.1 (q c)‖) μ :=
    Integrable.fintype_prod (f := fun (c : {c // c ∉ T}) p => ‖φ c.1 p‖) fun c => (hφi c.1 c.2).norm
  have hsumi : Summable fun y => ∫ q, ‖u y q‖ ∂μ := by
    simp_rw [hnu, integral_const_mul]
    refine Summable.mul_right _ ?_
    simpa only [norm_prod] using hks
  have hpt : ∀ q, HasSum (fun y => u y q) (∏ c, φ c (FT1a.edgeMom e T P q c)) := by
    intro q
    obtain ⟨-, h⟩ := FT1a_piSum (X := Fin d → ℤ) {f // f ∈ T}
      (fun f x => k f.1 x * zexp (FT1a.edgeMom e T P q f.1) x)
      (fun f => by simpa only [norm_mul, norm_zexp, mul_one] using hk f.1 f.2)
    have h' := h.mul_left (∏ c : {c // c ∉ T}, φ c.1 (q c))
    rw [FT1a_prod_split T]
    have e1 : ∀ c : {c // c ∉ T}, φ c.1 (FT1a.edgeMom e T P q c.1) = φ c.1 (q c) := fun c => by
      rw [FT1a.edgeMom_of_not_mem P q c.2]
    have e2 : ∀ f : {f // f ∈ T}, φ f.1 (FT1a.edgeMom e T P q f.1) =
        ∑' x, k f.1 x * zexp (FT1a.edgeMom e T P q f.1) x := fun f => by
      rw [hφT f.1 f.2]; rfl
    simp only [e1, e2]
    rw [mul_comm]
    exact h'
  refine ⟨?_, ?_⟩
  · -- integrability: a bounded continuous factor times an integrable product
    have hfac : ∀ q, ∏ c, φ c (FT1a.edgeMom e T P q c) =
        (∏ f : {f // f ∈ T}, φ f.1 (FT1a.edgeMom e T P q f.1)) *
          ∏ c : {c // c ∉ T}, φ c.1 (q c) := by
      intro q
      rw [FT1a_prod_split T]
      congr 1
      exact Finset.prod_congr rfl fun c _ => by rw [FT1a.edgeMom_of_not_mem P q c.2]
    simp_rw [hfac]
    refine (Integrable.fintype_prod (f := fun (c : {c // c ∉ T}) p => φ c.1 p)
      fun c => hφi c.1 c.2).bdd_mul
      (c := ∏ f : {f // f ∈ T}, ∑' x, ‖k f.1 x‖) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine continuous_finsetProd _ fun f _ => ?_
      rw [hφT f.1 f.2]
      exact (FT1a_continuous_zdSeries _ (hk f.1 f.2)).comp (FT1a_continuous_edgeMom P f.1)
    · refine Filter.Eventually.of_forall fun q => ?_
      rw [norm_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun f _ => ?_
      rw [hφT f.1 f.2]
      exact FT1a_norm_zdSeries_le _ (hk f.1 f.2) _
  · rw [hLHS]
    have hfub := integral_tsum_of_summable_integral_norm hui hsumi
    have hint' : ∫ q, ∏ c, φ c (FT1a.edgeMom e T P q c) ∂μ = ∫ q, ∑' y, u y q ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun q => ((hpt q).tsum_eq).symm)
    rw [hint', ← hfub]
    simp_rw [hint]
    rw [tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _
      (by exact_mod_cast Real.two_pi_pos.ne')), one_mul]

end L1

/-! ## The cube `[−π, π]^d` and the torus -/

section Torus

variable {d : ℕ}

/-- The quotient map `t ↦ t/(2π) mod 1` from `ℝ` to `ℝ/ℤ`. -/
private def FT1a_tor1 : ℝ →+ UnitAddCircle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    (AddMonoidHom.mulRight (2 * Real.pi)⁻¹)

private theorem FT1a_tor1_apply (t : ℝ) :
    FT1a_tor1 t = ((t * (2 * Real.pi)⁻¹ : ℝ) : UnitAddCircle) := rfl

private theorem FT1a_measurable_tor1 : Measurable FT1a_tor1 :=
  AddCircle.measurable_mk'.comp (measurable_mul_const _)

/-- `(2π)^{-1}` -/
private def FT1a_c1 : ℝ≥0 := (Real.toNNReal (2 * Real.pi))⁻¹

/-- The normalized Lebesgue measure `(2π)^{-1} dt` on `[−π, π]`. -/
private def FT1a_μ1 : Measure ℝ := FT1a_c1 • volume.restrict (Set.Icc (-Real.pi) Real.pi)

private theorem FT1a_mp1 : MeasurePreserving FT1a_tor1 FT1a_μ1 AddCircle.haarAddCircle := by
  refine ⟨FT1a_measurable_tor1, ?_⟩
  set r : ℝ := (2 * Real.pi)⁻¹ with hr_def
  have hr : r ≠ 0 := inv_ne_zero Real.two_pi_pos.ne'
  have hrpos : 0 < r := inv_pos.2 Real.two_pi_pos
  let S : ℝ ≃ᵐ ℝ := (Homeomorph.mulRight₀ r hr).toMeasurableEquiv
  have hS : ∀ t, S t = t * r := fun t => rfl
  have hpre : S ⁻¹' Set.Icc (-(1 / 2)) (1 / 2) = Set.Icc (-Real.pi) Real.pi := by
    ext t
    simp only [Set.mem_preimage, hS, Set.mem_Icc, hr_def]
    have hp := Real.two_pi_pos
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have := mul_le_mul_of_nonneg_right h1 hp.le
        rw [mul_assoc, inv_mul_cancel₀ hp.ne', mul_one] at this
        linarith
      · have := mul_le_mul_of_nonneg_right h2 hp.le
        rw [mul_assoc, inv_mul_cancel₀ hp.ne', mul_one] at this
        linarith
    · rintro ⟨h1, h2⟩
      constructor
      · rw [le_mul_inv_iff₀ hp]; linarith
      · rw [mul_inv_le_iff₀ hp]; linarith
  have hmapS : Measure.map S volume = ENNReal.ofReal (2 * Real.pi) • volume := by
    have h := Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr
    have hfun : (fun x : ℝ => r • x) = S := funext fun t => by rw [hS, smul_eq_mul, mul_comm]
    rw [hfun, Module.finrank_self, pow_one, hr_def, inv_inv,
      abs_of_pos Real.two_pi_pos] at h
    exact h
  have h1 : Measure.map S (volume.restrict (Set.Icc (-Real.pi) Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) • volume.restrict (Set.Icc (-(1 / 2)) (1 / 2)) := by
    rw [← hpre, ← MeasurableEquiv.restrict_map, hmapS, Measure.restrict_smul]
  have h2 : Measure.map (fun t : ℝ => (t : UnitAddCircle))
      (volume.restrict (Set.Icc (-(1 / 2)) (1 / 2))) = AddCircle.haarAddCircle := by
    have := (AddCircle.measurePreserving_mk (1 : ℝ) (-(1 / 2))).map_eq
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      Measure.restrict_congr_set Ioc_ae_eq_Icc] at this
    rw [this, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  have hcomp : (FT1a_tor1 : ℝ → UnitAddCircle) = (fun t : ℝ => (t : UnitAddCircle)) ∘ S :=
    funext fun t => rfl
  rw [hcomp, ← Measure.map_map AddCircle.measurable_mk' S.measurable, FT1a_μ1,
    Measure.map_smul _ S.measurable.aemeasurable, h1, ENNReal.smul_def FT1a_c1, smul_smul,
    Measure.map_smul _ AddCircle.measurable_mk'.aemeasurable, h2]
  have hc : ((FT1a_c1 : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi)) = 1 := by
    have hne : Real.toNNReal (2 * Real.pi) ≠ 0 := by simp [Real.pi_pos]
    rw [FT1a_c1, ENNReal.coe_inv hne]
    exact ENNReal.inv_mul_cancel (by simpa using hne) ENNReal.coe_ne_top
  rw [hc, one_smul]

/-- The product of scaled copies of a measure is the scaled product measure. -/
private theorem FT1a_pi_smul {J X : Type*} [Fintype J] [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (c : ℝ≥0) :
    Measure.pi (fun _ : J => c • μ) = (c ^ Fintype.card J) • Measure.pi (fun _ : J => μ) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/-- The normalized Lebesgue measure `(2π)^{-d} dp` on `[−π, π]^d`. -/
private def FT1a_μQ (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => FT1a_μ1

private theorem FT1a_μQ_eq :
    FT1a_μQ d = (FT1a_c1 ^ d) • volume.restrict (cubePi d) := by
  unfold FT1a_μQ FT1a_μ1 cubePi
  rw [FT1a_pi_smul, Fintype.card_fin, volume_pi, Measure.restrict_pi_pi]

/-- The Haar probability measure on `(ℝ/ℤ)^{A × d}`. -/
private def FT1a_ρ (A : Type*) [Fintype A] (d : ℕ) : Measure (A → UnitAddTorus (Fin d)) :=
  Measure.pi fun _ : A => Measure.pi fun _ : Fin d => AddCircle.haarAddCircle

private theorem FT1a_borel (A : Type*) [Fintype A] : BorelSpace (A → UnitAddTorus (Fin d)) :=
  Pi.borelSpace

attribute [local instance] FT1a_borel

private theorem FT1a_haar (A : Type*) [Fintype A] : (FT1a_ρ A d).IsAddHaarMeasure := by
  have : ∀ _ : A, (Measure.pi fun _ : Fin d =>
      (AddCircle.haarAddCircle : Measure UnitAddCircle)).IsAddHaarMeasure := fun _ => inferInstance
  exact Measure.pi.isAddHaarMeasure _

private theorem FT1a_prob (A : Type*) [Fintype A] : IsProbabilityMeasure (FT1a_ρ A d) := by
  unfold FT1a_ρ; infer_instance

/-- The quotient map `([−π, π]^d)^A → (ℝ/ℤ)^{A × d}` pushes the normalized measure to the Haar
measure. -/
private theorem FT1a_mpA (A : Type*) [Fintype A] :
    MeasurePreserving (fun (q : A → Fin d → ℝ) a i => FT1a_tor1 (q a i))
      (Measure.pi fun _ : A => FT1a_μQ d) (FT1a_ρ A d) := by
  have h1 : MeasurePreserving (fun (p : Fin d → ℝ) i => FT1a_tor1 (p i)) (FT1a_μQ d)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
    measurePreserving_pi _ _ fun _ => FT1a_mp1
  exact measurePreserving_pi _ _ fun _ => h1

private theorem FT1a_piQ_eq (A : Type*) [Fintype A] :
    Measure.pi (fun _ : A => FT1a_μQ d) =
      ((FT1a_c1 ^ d) ^ Fintype.card A) •
        (volume : Measure (A → Fin d → ℝ)).restrict (Set.univ.pi fun _ => cubePi d) := by
  rw [FT1a_μQ_eq, FT1a_pi_smul, FT1a_restrict_cube]

/-- A representative in `[0, 1)` of a point of `ℝ/ℤ`. -/
private def FT1a_rep (z : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 z : ℝ)

private theorem FT1a_measurable_rep : Measurable FT1a_rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

private theorem FT1a_rep_tor1 (t : ℝ) :
    2 * Real.pi * FT1a_rep (FT1a_tor1 t) =
      t + 2 * Real.pi * ((-⌊t * (2 * Real.pi)⁻¹⌋ : ℤ) : ℝ) := by
  rw [FT1a_tor1_apply, FT1a_rep, AddCircle.coe_equivIco_mk_apply, div_one, mul_one,
    Int.fract]
  push_cast
  field_simp
  ring

/-- A function on `(ℝ^d)^F` that is `2π`-periodic in every coordinate factors through the torus. -/
private theorem FT1a_lift {F β : Type*} (H : (F → Fin d → ℝ) → β)
    (hH : ∀ v (z : F → Fin d → ℤ), H (v + fun f i => 2 * Real.pi * z f i) = H v)
    (v : F → Fin d → ℝ) :
    H (fun f i => 2 * Real.pi * FT1a_rep (FT1a_tor1 (v f i))) = H v := by
  have : (fun f i => 2 * Real.pi * FT1a_rep (FT1a_tor1 (v f i))) =
      v + fun f i => 2 * Real.pi * ((-⌊v f i * (2 * Real.pi)⁻¹⌋ : ℤ) : ℝ) := by
    funext f i
    rw [FT1a_rep_tor1]
    rfl
  rw [this, hH]

/-- A continuous surjective homomorphism of tori pushes the Haar measure to the Haar measure. -/
private theorem FT1a_map_haar {A F : Type*} [Fintype A] [Fintype F]
    (ψ : (A → UnitAddTorus (Fin d)) →+ (F → UnitAddTorus (Fin d))) (hc : Continuous ψ)
    (hs : Function.Surjective ψ) : Measure.map ψ (FT1a_ρ A d) = FT1a_ρ F d := by
  have := FT1a_haar (d := d) A
  have := FT1a_haar (d := d) F
  have := FT1a_prob (d := d) A
  have := FT1a_prob (d := d) F
  have := Measure.isAddHaarMeasure_map_of_isFiniteMeasure (FT1a_ρ A d) ψ hc hs
  have : IsProbabilityMeasure (Measure.map ψ (FT1a_ρ A d)) :=
    (Measure.isProbabilityMeasure_map_iff hc.measurable.aemeasurable).2 inferInstance
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Division in `ℝ/ℤ`: every point is an `n`-th multiple, `n ≠ 0`. -/
private theorem FT1a_div (n : ℤ) (hn : n ≠ 0) (y : UnitAddTorus (Fin d)) :
    ∃ w : UnitAddTorus (Fin d), n • w = y := by
  choose t ht using fun i => QuotientAddGroup.mk_surjective (y i)
  refine ⟨fun i => ((t i / n : ℝ) : UnitAddCircle), funext fun i => ?_⟩
  simp only [Pi.smul_apply]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hn)]
  exact ht i

/-- The homomorphism `x ↦ (Σ_a N_{fa} x_a)_f` of tori. -/
private def FT1a_psi {A F : Type*} [Fintype A] (N : F → A → ℤ) :
    (A → UnitAddTorus (Fin d)) →+ (F → UnitAddTorus (Fin d)) where
  toFun x f := ∑ a, N f a • x a
  map_zero' := by funext f; simp
  map_add' x y := by funext f; simp [smul_add, Finset.sum_add_distrib]

private theorem FT1a_continuous_psi {A F : Type*} [Fintype A] (N : F → A → ℤ) :
    Continuous (FT1a_psi (d := d) N) := by
  refine continuous_pi fun f => ?_
  exact continuous_finsetSum _ fun a _ => (continuous_apply a).zsmul _

/-- If a square submatrix `N_{f, j(f')}` has nonzero determinant, `x ↦ N x` is onto. -/
private theorem FT1a_psi_surj {A F : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [DecidableEq A] (N : F → A → ℤ) (j : F → A)
    (hdet : (Matrix.of fun f f' => N f (j f')).det ≠ 0) :
    Function.Surjective (FT1a_psi (d := d) N) := by
  intro y
  set M : Matrix F F ℤ := Matrix.of fun f f' => N f (j f')
  choose w hw using fun f => FT1a_div (d := d) M.det hdet (y f)
  let w' : F → UnitAddTorus (Fin d) := fun f' => ∑ f'', M.adjugate f' f'' • w f''
  refine ⟨∑ f', Pi.single (j f') (w' f'), funext fun f => ?_⟩
  simp only [FT1a_psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply]
  have h1 : ∀ a, N f a • ∑ f', (Pi.single (j f') (w' f') : A → UnitAddTorus (Fin d)) a =
      ∑ f', if j f' = a then N f a • w' f' else 0 := by
    intro a
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun f' _ => ?_
    by_cases h : j f' = a
    · subst h; simp
    · simp [Ne.symm h, h]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h2 : ∑ f', N f (j f') • w' f' = ∑ f'', (M * M.adjugate) f f'' • w f'' := by
    simp only [w', Finset.smul_sum, smul_smul, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f'' _ => ?_
    rw [Finset.sum_smul]
    rfl
  rw [h2, Matrix.mul_adjugate]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact hw f

/-- The change of variables `q ↦ b − N q` on the tori: for a surjective integer matrix `N` and a
function `H` on `(ℝ^d)^F`, `2π`-periodic in every coordinate,
`∫ H(b − N q) dq = ∫ H(v) dv` for the normalized measures on `([−π, π]^d)^A` and `([−π, π]^d)^F`. -/
private theorem FT1a_cov {A F : Type*} [Fintype A] [Fintype F] (N : F → A → ℤ)
    (hsurj : Function.Surjective (FT1a_psi (d := d) N))
    (H : (F → Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hper : ∀ v (z : F → Fin d → ℤ), H (v + fun f i => 2 * Real.pi * z f i) = H v)
    (b : F → Fin d → ℝ) :
    ∫⁻ q, H (fun f => b f - ∑ a, (N f a : ℝ) • q a) ∂(Measure.pi fun _ : A => FT1a_μQ d) =
      ∫⁻ v, H v ∂(Measure.pi fun _ : F => FT1a_μQ d) := by
  have := FT1a_haar (d := d) F
  let Ht : (F → UnitAddTorus (Fin d)) → ℝ≥0∞ := fun y =>
    H (fun f i => 2 * Real.pi * FT1a_rep (y f i))
  have hHt : ∀ v : F → Fin d → ℝ, Ht (fun f i => FT1a_tor1 (v f i)) = H v := fun v =>
    FT1a_lift H hper v
  have hmHt : Measurable Ht := by
    refine hH.comp (measurable_pi_iff.2 fun f => measurable_pi_iff.2 fun i => ?_)
    exact measurable_const.mul (FT1a_measurable_rep.comp
      ((measurable_pi_apply i).comp (measurable_pi_apply f)))
  let ψ' := FT1a_psi (d := d) (fun f a => -N f a)
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨-x, ?_⟩
    rw [← hx]
    funext f
    simp only [ψ', FT1a_psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.neg_apply, neg_smul,
      smul_neg, neg_neg]
  have hΦ : ∀ q : A → Fin d → ℝ, (fun f i => FT1a_tor1 ((b f - ∑ a, (N f a : ℝ) • q a) i)) =
      (fun f i => FT1a_tor1 (b f i)) + ψ' (fun a i => FT1a_tor1 (q a i)) := by
    intro q
    funext f i
    simp only [ψ', FT1a_psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply]
    rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_apply, map_sub, map_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ← zsmul_eq_mul, map_zsmul, neg_smul]
  calc ∫⁻ q, H (fun f => b f - ∑ a, (N f a : ℝ) • q a) ∂(Measure.pi fun _ : A => FT1a_μQ d)
      = ∫⁻ q, Ht ((fun f i => FT1a_tor1 (b f i)) + ψ' (fun a i => FT1a_tor1 (q a i)))
          ∂(Measure.pi fun _ : A => FT1a_μQ d) := by
        refine lintegral_congr fun q => ?_
        rw [← hΦ q, hHt]
    _ = ∫⁻ x, Ht ((fun f i => FT1a_tor1 (b f i)) + ψ' x) ∂(FT1a_ρ A d) :=
        (FT1a_mpA A).lintegral_comp (hmHt.comp
          ((FT1a_continuous_psi _).measurable.const_add _))
    _ = ∫⁻ y, Ht ((fun f i => FT1a_tor1 (b f i)) + y) ∂(Measure.map ψ' (FT1a_ρ A d)) :=
        (lintegral_map (hmHt.comp (measurable_const_add _))
          (FT1a_continuous_psi _).measurable).symm
    _ = ∫⁻ y, Ht ((fun f i => FT1a_tor1 (b f i)) + y) ∂(FT1a_ρ F d) := by
        rw [FT1a_map_haar ψ' (FT1a_continuous_psi _) hψ']
    _ = ∫⁻ y, Ht y ∂(FT1a_ρ F d) := lintegral_add_left_eq_self Ht _
    _ = ∫⁻ v, Ht (fun f i => FT1a_tor1 (v f i)) ∂(Measure.pi fun _ : F => FT1a_μQ d) :=
        ((FT1a_mpA F).lintegral_comp hmHt).symm
    _ = ∫⁻ v, H v ∂(Measure.pi fun _ : F => FT1a_μQ d) :=
        lintegral_congr fun v => hHt v

end Torus

/-! ## The cut matrix between two spanning trees -/

section Det

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

private theorem FT1a_card_tree {T : List ι} (hT : T.Nodup) :
    Fintype.card {f // f ∈ T} = T.length := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun f => f ∈ T) = T.toFinset := by ext; simp
  rw [this, List.toFinset_card_of_nodup hT]

private theorem FT1a_card_split (T T' : List ι) :
    Fintype.card {f // f ∈ T ∧ f ∉ T'} + Fintype.card {f // f ∈ T ∧ f ∈ T'} =
      Fintype.card {f // f ∈ T} := by
  simp only [Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun f => f ∈ T)
    (fun f => f ∈ T'), Finset.filter_filter, Finset.filter_filter, add_comm]

/-- **The cut matrix of two spanning trees.** For two spanning trees `T₁`, `T₂` (lists of edges with
`TreeEdges`), the integer matrix `N_{fc} = 1_{h_c ∈ C_f} − 1_{t_c ∈ C_f}` (cuts of `T₁`),
`f ∈ T₁ ∖ T₂`, `c ∈ T₂ ∖ T₁`, is square, and its determinant is nonzero for every identification of
the two index sets. The proof: a kernel vector `u` extends to a circulation supported on `T₂`, which
vanishes. -/
theorem FT1a.cutMatrix_det_ne_zero (e : ι → V × V) (T₁ T₂ : List ι)
    (hTr₁ : TreeEdges (T₁.map e)) (hTr₂ : TreeEdges (T₂.map e)) :
    Fintype.card {f // f ∈ T₁ ∧ f ∉ T₂} = Fintype.card {c // c ∈ T₂ ∧ c ∉ T₁} ∧
      ∀ eqv : {f // f ∈ T₁ ∧ f ∉ T₂} ≃ {c // c ∈ T₂ ∧ c ∉ T₁},
        (Matrix.of fun f f' => FT1a.cutCoef e T₁ f.1 (eqv f').1).det ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have h1 := FT1a_card_split T₁ T₂
    have h2 := FT1a_card_split T₂ T₁
    rw [FT1a_card_tree (FT1a_nodup hTr₁)] at h1
    rw [FT1a_card_tree (FT1a_nodup hTr₂)] at h2
    have hl : T₁.length = T₂.length := by
      have a := hTr₁.1
      have b := hTr₂.1
      rw [List.length_map] at a b
      omega
    have hS : Fintype.card {f // f ∈ T₁ ∧ f ∈ T₂} = Fintype.card {f // f ∈ T₂ ∧ f ∈ T₁} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
    omega
  intro eqv hdet0
  set M : Matrix {f // f ∈ T₁ ∧ f ∉ T₂} {f // f ∈ T₁ ∧ f ∉ T₂} ℤ :=
    Matrix.of fun f f' => FT1a.cutCoef e T₁ f.1 (eqv f').1 with hM
  have hdetR : (M.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have := RingHom.map_det (Int.castRingHom ℝ) M
    rw [hdet0, map_zero] at this
    rw [this]
    rfl
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetR
  -- the loop variables: `v` on `T₂ ∖ T₁`, `0` on the other edges outside `T₁`
  let q : {c // c ∉ T₁} → ℝ := fun a =>
    ∑ u : {c // c ∈ T₂ ∧ c ∉ T₁}, if u.1 = a.1 then v (eqv.symm u) else 0
  let x : ι → ℝ := fun c => if hc : c ∈ T₁ then
      -∑ a : {c // c ∉ T₁}, (FT1a.cutCoef e T₁ c a.1 : ℝ) * q a else q ⟨c, hc⟩
  have hqU : ∀ u : {c // c ∈ T₂ ∧ c ∉ T₁}, q ⟨u.1, u.2.2⟩ = v (eqv.symm u) := by
    intro u
    simp only [q]
    rw [Finset.sum_eq_single u]
    · simp
    · intro u' _ hu'
      have : u'.1 ≠ u.1 := fun h => hu' (Subtype.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hq0 : ∀ a : {c // c ∉ T₁}, a.1 ∉ T₂ → q a = 0 := by
    intro a ha
    simp only [q]
    refine Finset.sum_eq_zero fun u _ => ?_
    have : u.1 ≠ a.1 := fun h => ha (h ▸ u.2.1)
    simp [this]
  -- `x` vanishes on `T₁ ∖ T₂`
  have hxF : ∀ f (hf : f ∈ T₁), f ∉ T₂ → x f = 0 := by
    intro f hf hf2
    simp only [x, hf, ↓reduceDIte, neg_eq_zero]
    have h := congrFun hv ⟨f, hf, hf2⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM, Matrix.of_apply,
      Pi.zero_apply] at h
    have hsum : ∑ a : {c // c ∉ T₁}, (FT1a.cutCoef e T₁ f a.1 : ℝ) * q a =
        ∑ u : {c // c ∈ T₂ ∧ c ∉ T₁}, (FT1a.cutCoef e T₁ f u.1 : ℝ) * v (eqv.symm u) := by
      simp only [q, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_eq_single (⟨u.1, u.2.2⟩ : {c // c ∉ T₁})]
      · simp
      · intro a _ ha
        have : u.1 ≠ a.1 := fun h' => ha (Subtype.ext h'.symm)
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    rw [hsum, ← h]
    exact Fintype.sum_equiv eqv.symm _ _ fun u => by simp
  -- `x` is a circulation
  have hcirc : ∀ σ : V → ℝ, ∑ c, x c * (σ (e c).2 - σ (e c).1) = 0 := by
    intro σ
    rw [FT1a_sum_split T₁]
    have h1 : ∀ f : {f // f ∈ T₁}, x f.1 * (σ (e f.1).2 - σ (e f.1).1) =
        -∑ a : {c // c ∉ T₁}, q a * ((FT1a.cutCoef e T₁ f.1 a.1 : ℝ) *
          (σ (e f.1).2 - σ (e f.1).1)) := by
      intro f
      simp only [x, f.2, ↓reduceDIte, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun a _ => by ring
    have h2 : ∀ a : {c // c ∉ T₁}, x a.1 * (σ (e a.1).2 - σ (e a.1).1) =
        q a * ∑ f : {f // f ∈ T₁}, (FT1a.cutCoef e T₁ f.1 a.1 : ℝ) *
          (σ (e f.1).2 - σ (e f.1).1) := by
      intro a
      simp only [x, a.2, ↓reduceDIte]
      congr 1
      rw [FT1a_incr_eq hTr₁ σ a.1]
      simp only [zsmul_eq_mul]
    simp only [h1, h2, Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact neg_add_cancel _
  -- a circulation supported on the tree `T₂` vanishes
  have hxT2 : ∀ g ∈ T₂, x g = 0 := by
    intro g hg
    have h := hcirc fun w => (FT1a.cutInd e T₂ g w : ℝ)
    rw [Finset.sum_eq_single g] at h
    · rw [← Int.cast_sub, ← FT1a.cutCoef.eq_def, FT1a_cutCoef_tree hTr₂ hg hg] at h
      simpa using h
    · intro c _ hcg
      rw [← Int.cast_sub, ← FT1a.cutCoef.eq_def]
      by_cases hc2 : c ∈ T₂
      · rw [FT1a_cutCoef_tree hTr₂ hg hc2]
        simp [hcg]
      · by_cases hc1 : c ∈ T₁
        · rw [hxF c hc1 hc2, zero_mul]
        · have : x c = 0 := by
            simp only [x, hc1, ↓reduceDIte]
            exact hq0 ⟨c, hc1⟩ hc2
          rw [this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  apply hv0
  funext f'
  have h := hxT2 (eqv f').1 (eqv f').2.1
  simp only [x, (eqv f').2.2, ↓reduceDIte] at h
  rw [hqU (eqv f'), Equiv.symm_apply_apply] at h
  exact h

end Det

/-! ## The momentum Cauchy–Schwarz bound -/

section CS

variable {d : ℕ}

attribute [local instance] FT1a_borel

/-- The change of variables `q ↦ b − N q` on `([−π, π]^d)^A` for a surjective integer matrix, with
Lebesgue measure: the factor is `(2π)^{d(|A| − |F|)}`. -/
private theorem FT1a_cov' {A F : Type*} [Fintype A] [Fintype F] (N : F → A → ℤ)
    (hsurj : Function.Surjective (FT1a_psi (d := d) N))
    (hFA : Fintype.card F ≤ Fintype.card A)
    (H : (F → Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hper : ∀ v (z : F → Fin d → ℤ), H (v + fun f i => 2 * Real.pi * z f i) = H v)
    (b : F → Fin d → ℝ) :
    ∫⁻ q in Set.univ.pi (fun _ : A => cubePi d), H (fun f => b f - ∑ a, (N f a : ℝ) • q a) =
      ENNReal.ofReal ((2 * Real.pi) ^ (d * (Fintype.card A - Fintype.card F))) *
        ∫⁻ v in Set.univ.pi (fun _ : F => cubePi d), H v := by
  have h := FT1a_cov N hsurj H hH hper b
  rw [FT1a_piQ_eq, FT1a_piQ_eq, lintegral_smul_measure, lintegral_smul_measure] at h
  have hne : Real.toNNReal (2 * Real.pi) ≠ 0 := by simp [Real.pi_pos]
  have hc0 : (FT1a_c1 : ℝ≥0∞) ≠ 0 := by
    rw [FT1a_c1, ENNReal.coe_inv hne]
    exact ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top
  set κ : ℝ≥0∞ := (FT1a_c1 : ℝ≥0∞) ^ d with hκ
  have hκ0 : κ ≠ 0 := pow_ne_zero _ hc0
  have hκt : κ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hκinv : κ⁻¹ = ENNReal.ofReal ((2 * Real.pi) ^ d) := by
    rw [hκ, ENNReal.inv_pow, FT1a_c1, ENNReal.coe_inv hne, inv_inv,
      ENNReal.ofReal_pow Real.two_pi_pos.le]
    rfl
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow] at h
  rw [← hκ] at h
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hFA
  rw [hn, pow_add, mul_assoc] at h
  have h' := (ENNReal.mul_right_inj (pow_ne_zero _ hκ0) (ENNReal.pow_ne_top hκt)).1 h
  have hR : ENNReal.ofReal ((2 * Real.pi) ^ (d * n)) = (κ ^ n)⁻¹ := by
    rw [pow_mul, ENNReal.ofReal_pow (by positivity), ← hκinv, ← ENNReal.inv_pow]
  rw [hn, Nat.add_sub_cancel_left, hR, ← h', ← mul_assoc, ENNReal.inv_mul_cancel
    (pow_ne_zero _ hκ0) (ENNReal.pow_ne_top hκt), one_mul]

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- **The momentum Cauchy–Schwarz bound** (the integrability step of [I, (7.29)–(7.30)]). For two
spanning trees `T₁`, `T₂` and nonnegative Borel `2π`-periodic `g_c`, bounded by `M_c` on
`T₁ ∩ T₂` and square integrable on `[−π, π]^d` otherwise, the integrand
`Π_c g_c(ℓ_c(q) + λ_c(P))` on `([−π, π]^d)^L`, `L = |E| − |V| + 1`, with the momenta fixed by
the tree `T₁`, is integrable and
`∫ Π_c g_c ≤ Π_{T₁∩T₂} M_c · Π_{c ∉ T₁} ‖g_c‖₂ · (2π)^{d(L−m)/2} · Π_{T₁∖T₂} ‖g_f‖₂`,
`m = |T₁ ∖ T₂|`, `‖g‖₂ = (∫_{[−π,π]^d} g²)^{1/2}`. -/
theorem FT1a.momentumCS (e : ι → V × V) (T₁ T₂ : List ι)
    (hTr₁ : TreeEdges (T₁.map e)) (hTr₂ : TreeEdges (T₂.map e)) (P : V → Fin d → ℝ)
    (g : ι → (Fin d → ℝ) → ℝ) (hg0 : ∀ c p, 0 ≤ g c p) (hgm : ∀ c, Measurable (g c))
    (hgp : ∀ c p (z : Fin d → ℤ), g c (p + fun i => 2 * Real.pi * z i) = g c p)
    (M : ι → ℝ) (hM : ∀ c, c ∈ T₁ → c ∈ T₂ → ∀ p, g c p ≤ M c)
    (hL2 : ∀ c, ¬ (c ∈ T₁ ∧ c ∈ T₂) → IntegrableOn (fun p => g c p ^ 2) (cubePi d)) :
    IntegrableOn (fun q => ∏ c, g c (FT1a.edgeMom e T₁ P q c))
        (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) ∧
      ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
          ∏ c, g c (FT1a.edgeMom e T₁ P q c) ≤
        (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, M c.1) *
          (∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, g c.1 p ^ 2)) *
          √((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
            Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂}))) *
          ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, √(∫ p in cubePi d, g c.1 p ^ 2) := by
  set μ : Measure ({c // c ∉ T₁} → Fin d → ℝ) :=
    volume.restrict (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) with hμ
  have hμpi : μ = Measure.pi fun _ => volume.restrict (cubePi d) := FT1a_restrict_cube _
  -- the three factors
  let Gs : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ := fun q =>
    ∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, g c.1 (FT1a.edgeMom e T₁ P q c.1)
  let Gb : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ := fun q =>
    ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, g c.1 (FT1a.edgeMom e T₁ P q c.1)
  let Ga : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ := fun q => ∏ c : {c // c ∉ T₁}, g c.1 (q c)
  have hsplit : ∀ q, ∏ c, g c (FT1a.edgeMom e T₁ P q c) = Gs q * Gb q * Ga q := by
    intro q
    rw [FT1a_prod_split3 T₁ T₂]
    congr 1
    exact Finset.prod_congr rfl fun c _ => by rw [FT1a.edgeMom_of_not_mem P q c.2]
  have hmeas : ∀ c, Measurable fun q : {c // c ∉ T₁} → Fin d → ℝ =>
      g c (FT1a.edgeMom e T₁ P q c) := fun c =>
    (hgm c).comp (FT1a_continuous_edgeMom P c).measurable
  have hGs_m : Measurable Gs := Finset.measurable_prod _ fun c _ => hmeas c.1
  have hGb_m : Measurable Gb := Finset.measurable_prod _ fun c _ => hmeas c.1
  have hGa_m : Measurable Ga := Finset.measurable_prod _ fun c _ =>
    (hgm c.1).comp (measurable_pi_apply c)
  have hGs0 : ∀ q, 0 ≤ Gs q := fun q => Finset.prod_nonneg fun c _ => hg0 _ _
  have hGb0 : ∀ q, 0 ≤ Gb q := fun q => Finset.prod_nonneg fun c _ => hg0 _ _
  have hGa0 : ∀ q, 0 ≤ Ga q := fun q => Finset.prod_nonneg fun c _ => hg0 _ _
  have hM0 : ∀ c : {c // c ∈ T₁ ∧ c ∈ T₂}, 0 ≤ M c.1 := fun c =>
    (hg0 c.1 0).trans (hM c.1 c.2.1 c.2.2 0)
  have hGsM : ∀ q, Gs q ≤ ∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, M c.1 := fun q =>
    Finset.prod_le_prod₀ (fun c _ => hg0 _ _) fun c _ => hM c.1 c.2.1 c.2.2 _
  -- `∫ Ga²`
  have hga2 : ∀ c : {c // c ∉ T₁}, Integrable (fun p => g c.1 p ^ 2)
      (volume.restrict (cubePi d)) := fun c => hL2 c.1 fun h => c.2 h.1
  have hGa2 : Integrable (fun q => Ga q ^ 2) μ := by
    rw [hμpi]
    simp only [Ga, ← Finset.prod_pow]
    exact Integrable.fintype_prod (f := fun (c : {c // c ∉ T₁}) p => g c.1 p ^ 2) hga2
  have hGa2_int : ∫ q, Ga q ^ 2 ∂μ = ∏ c : {c // c ∉ T₁}, ∫ p in cubePi d, g c.1 p ^ 2 := by
    rw [hμpi]
    simp only [Ga, ← Finset.prod_pow]
    exact integral_fintype_prod_eq_prod (fun (c : {c // c ∉ T₁}) p => g c.1 p ^ 2)
  -- `∫ Gb²`, by the change of variables on the torus
  obtain ⟨hcard, hdet⟩ := FT1a.cutMatrix_det_ne_zero e T₁ T₂ hTr₁ hTr₂
  let eqv := Fintype.equivOfCardEq hcard
  let N : {c // c ∈ T₁ ∧ c ∉ T₂} → {c // c ∉ T₁} → ℤ := fun f a => FT1a.cutCoef e T₁ f.1 a.1
  have hsurj : Function.Surjective (FT1a_psi (d := d) N) :=
    FT1a_psi_surj N (fun f' => ⟨(eqv f').1, (eqv f').2.2⟩) (hdet eqv)
  have hFA : Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂} ≤ Fintype.card {c // c ∉ T₁} := by
    rw [hcard]
    refine Fintype.card_le_of_injective (fun u => ⟨u.1, u.2.2⟩) fun u u' h => ?_
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  let H : ({c // c ∈ T₁ ∧ c ∉ T₂} → Fin d → ℝ) → ℝ := fun v =>
    ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, g c.1 (v c) ^ 2
  have hHm : Measurable H := Finset.measurable_prod _ fun c _ =>
    ((hgm c.1).comp (measurable_pi_apply c)).pow_const 2
  have hHp : ∀ v (z : {c // c ∈ T₁ ∧ c ∉ T₂} → Fin d → ℤ),
      (fun v => ENNReal.ofReal (H v)) (v + fun f i => 2 * Real.pi * z f i) =
        ENNReal.ofReal (H v) := by
    intro v z
    simp only [H, Pi.add_apply]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [hgp c.1 (v c) (z c)]
  have hgb2 : ∀ c : {c // c ∈ T₁ ∧ c ∉ T₂}, Integrable (fun p => g c.1 p ^ 2)
      (volume.restrict (cubePi d)) := fun c => hL2 c.1 fun h => c.2.2 h.2
  have hHi : Integrable H (volume.restrict (Set.univ.pi fun _ : {c // c ∈ T₁ ∧ c ∉ T₂} =>
      cubePi d)) := by
    rw [FT1a_restrict_cube]
    exact Integrable.fintype_prod (f := fun (c : {c // c ∈ T₁ ∧ c ∉ T₂}) p => g c.1 p ^ 2) hgb2
  have hHint : ∫ v in Set.univ.pi (fun _ : {c // c ∈ T₁ ∧ c ∉ T₂} => cubePi d), H v =
      ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, ∫ p in cubePi d, g c.1 p ^ 2 := by
    rw [FT1a_restrict_cube]
    exact integral_fintype_prod_eq_prod (fun (c : {c // c ∈ T₁ ∧ c ∉ T₂}) p => g c.1 p ^ 2)
  have hGbH : ∀ q, Gb q ^ 2 = H (fun f => FT1a.extMom e T₁ P f.1 - ∑ a, (N f a : ℝ) • q a) := by
    intro q
    simp only [Gb, H, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [FT1a.edgeMom_of_mem P q c.2.1]
  have hGb_lint : ∫⁻ q, ENNReal.ofReal (Gb q ^ 2) ∂μ =
      ENNReal.ofReal ((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
        Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂})) *
          ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, ∫ p in cubePi d, g c.1 p ^ 2) := by
    simp only [hGbH]
    rw [hμ, FT1a_cov' N hsurj hFA (fun v => ENNReal.ofReal (H v)) hHm.ennreal_ofReal hHp,
      ← ofReal_integral_eq_lintegral_ofReal hHi (Filter.Eventually.of_forall fun v =>
        Finset.prod_nonneg fun c _ => sq_nonneg _), hHint, ENNReal.ofReal_mul (by positivity)]
  have hGb2 : Integrable (fun q => Gb q ^ 2) μ := by
    refine ⟨(hGb_m.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q => sq_nonneg _),
      hGb_lint]
    exact ENNReal.ofReal_lt_top
  have hGb2_int : ∫ q, Gb q ^ 2 ∂μ = (2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
      Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂})) *
        ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, ∫ p in cubePi d, g c.1 p ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => sq_nonneg _)
      (hGb_m.pow_const 2).aestronglyMeasurable, hGb_lint, ENNReal.toReal_ofReal]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun c _ =>
      integral_nonneg fun p => sq_nonneg _)
  -- Cauchy–Schwarz
  have hGbGa : Integrable (fun q => Gb q * Ga q) μ := by
    refine (hGb2.add hGa2).div_const 2 |>.mono' (hGb_m.mul hGa_m).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun q => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hGb0 q) (hGa0 q))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Gb q - Ga q)]
  have hmem : ∀ G : ({c // c ∉ T₁} → Fin d → ℝ) → ℝ, Measurable G →
      Integrable (fun q => G q ^ 2) μ → MemLp G (ENNReal.ofReal 2) μ := by
    intro G hG h2
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs, sq_abs] using h2
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hGb0) (Filter.Eventually.of_forall hGa0)
    (hmem Gb hGb_m hGb2) (hmem Ga hGa_m hGa2)
  simp only [Real.rpow_two] at hCS
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have hInt : Integrable (fun q => ∏ c, g c (FT1a.edgeMom e T₁ P q c)) μ := by
    refine (hGbGa.const_mul (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, M c.1)).mono'
      (Finset.measurable_prod _ fun c _ => hmeas c).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun q => ?_
    rw [hsplit, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hGs0 q) (hGb0 q))
      (hGa0 q)), mul_assoc]
    exact mul_le_mul_of_nonneg_right (hGsM q) (mul_nonneg (hGb0 q) (hGa0 q))
  refine ⟨hInt, ?_⟩
  calc ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d), ∏ c, g c (FT1a.edgeMom e T₁ P q c)
      ≤ ∫ q, (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, M c.1) * (Gb q * Ga q) ∂μ := by
        refine integral_mono hInt (hGbGa.const_mul _) fun q => ?_
        simp only
        rw [hsplit, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hGsM q) (mul_nonneg (hGb0 q) (hGa0 q))
    _ = (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, M c.1) * ∫ q, Gb q * Ga q ∂μ := integral_const_mul _ _
    _ ≤ (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, M c.1) *
          (√(∫ q, Gb q ^ 2 ∂μ) * √(∫ q, Ga q ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hCS (Finset.prod_nonneg fun c _ => hM0 c)
    _ = _ := by
        rw [hGb2_int, hGa2_int, Real.sqrt_mul (by positivity),
          Real.sqrt_prod _ fun c _ => integral_nonneg fun p => sq_nonneg _,
          Real.sqrt_prod _ fun c _ => integral_nonneg fun p => sq_nonneg _]
        ring

end CS

/-! ## Parseval on `[−π, π]^d` and the `L²` convergence of the box partial sums -/

section Parseval

variable {d : ℕ}

private theorem FT1a_isFinite_cube : IsFiniteMeasure (volume.restrict (cubePi d)) :=
  ⟨by rw [Measure.restrict_apply_univ]
      exact (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top⟩

attribute [local instance] FT1a_isFinite_cube

private theorem FT1a_mpQ : MeasurePreserving (fun (p : Fin d → ℝ) i => FT1a_tor1 (p i))
    (FT1a_μQ d) (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
  measurePreserving_pi _ _ fun _ => FT1a_mp1

private theorem FT1a_lift1 {β : Type*} (H : (Fin d → ℝ) → β)
    (hH : ∀ p (z : Fin d → ℤ), H (p + fun i => 2 * Real.pi * z i) = H p) (p : Fin d → ℝ) :
    H (fun i => 2 * Real.pi * FT1a_rep (FT1a_tor1 (p i))) = H p := by
  have : (fun i => 2 * Real.pi * FT1a_rep (FT1a_tor1 (p i))) =
      p + fun i => 2 * Real.pi * ((-⌊p i * (2 * Real.pi)⁻¹⌋ : ℤ) : ℝ) := by
    funext i
    rw [FT1a_rep_tor1]
    rfl
  rw [this, hH]

private theorem FT1a_mFourier_tor (n : Fin d → ℤ) (p : Fin d → ℝ) :
    UnitAddTorus.mFourier n (fun i => FT1a_tor1 (p i)) = zexp p n := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, FT1a_tor1_apply, fourier_coe_apply]
  unfold zexp
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Integrals over the torus are normalized integrals over `[−π, π]^d`. -/
private theorem FT1a_integral_tor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : UnitAddTorus (Fin d) → E)
    (hG : AEStronglyMeasurable G
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))) :
    ∫ y, G y ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      ((2 * Real.pi) ^ d)⁻¹ • ∫ p in cubePi d, G (fun i => FT1a_tor1 (p i)) := by
  rw [← FT1a_mpQ.map_eq] at hG ⊢
  rw [integral_map FT1a_mpQ.measurable.aemeasurable hG, FT1a_μQ_eq,
    integral_smul_nnreal_measure, NNReal.smul_def]
  congr 1
  rw [NNReal.coe_pow, FT1a_c1, NNReal.coe_inv, Real.coe_toNNReal _ Real.two_pi_pos.le, inv_pow]

private theorem FT1a_zexp_neg (p : Fin d → ℝ) (x : Fin d → ℤ) :
    zexp p (-x) = conj (zexp p x) := by
  rw [FT1a_zexp_eq, FT1a_zexp_eq, FT1a_dot_neg_right, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

/-- **Parseval** on `[−π, π]^d`: `Σ_x |k(x)|² = (2π)^{-d} ∫ |f|²` for `k = latticeFourier f`. -/
private theorem FT1a_parseval (φ : (Fin d → ℝ) → ℂ) (hm : Measurable φ)
    (hper : ∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p)
    (hL2 : MemLp φ 2 (volume.restrict (cubePi d))) :
    HasSum (fun n => ‖latticeFourier φ n‖ ^ 2)
      (((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖φ p‖ ^ 2) := by
  let φt : UnitAddTorus (Fin d) → ℂ := fun y => φ (fun i => 2 * Real.pi * FT1a_rep (y i))
  have hφt : ∀ p, φt (fun i => FT1a_tor1 (p i)) = φ p := FT1a_lift1 φ hper
  have hmt : Measurable φt := hm.comp (measurable_pi_iff.2 fun i =>
    measurable_const.mul (FT1a_measurable_rep.comp (measurable_pi_apply i)))
  have hLt : MemLp φt 2
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    have hae : AEStronglyMeasurable φt (Measure.map (fun (p : Fin d → ℝ) i => FT1a_tor1 (p i))
        (FT1a_μQ d)) := by
      rw [FT1a_mpQ.map_eq]
      exact hmt.aestronglyMeasurable
    rw [← FT1a_mpQ.map_eq, memLp_map_measure_iff hae FT1a_mpQ.measurable.aemeasurable]
    have : φt ∘ (fun (p : Fin d → ℝ) i => FT1a_tor1 (p i)) = φ := funext hφt
    rw [this, FT1a_μQ_eq, ENNReal.smul_def]
    exact hL2.smul_measure ENNReal.coe_ne_top
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin d) (hLt.toLp φt)
  have hcoef : ∀ n, UnitAddTorus.mFourierCoeff (hLt.toLp φt : UnitAddTorus (Fin d) → ℂ) n =
      latticeFourier φ n := by
    intro n
    have h1 : UnitAddTorus.mFourierCoeff (hLt.toLp φt : UnitAddTorus (Fin d) → ℂ) n =
        UnitAddTorus.mFourierCoeff φt n :=
      integral_congr_ae ((hLt.coeFn_toLp).mono fun t ht => by simp only [ht])
    rw [h1]
    change ∫ t, UnitAddTorus.mFourier (-n) t • φt t
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) = _
    rw [FT1a_integral_tor (fun t => UnitAddTorus.mFourier (-n) t • φt t)
      ((UnitAddTorus.mFourier (-n)).continuous.measurable.smul hmt).aestronglyMeasurable]
    simp only [FT1a_mFourier_tor, hφt, smul_eq_mul]
    unfold latticeFourier
    rw [Complex.real_smul]
    push_cast
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have hnorm : ∫ t, ‖(hLt.toLp φt : UnitAddTorus (Fin d) → ℂ) t‖ ^ 2
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      ((2 * Real.pi) ^ d)⁻¹ * ∫ p in cubePi d, ‖φ p‖ ^ 2 := by
    rw [integral_congr_ae (g := fun t => ‖φt t‖ ^ 2)
      ((hLt.coeFn_toLp).mono fun t ht => by simp only [ht]),
      FT1a_integral_tor (fun t => ‖φt t‖ ^ 2) (hmt.norm.pow_const 2).aestronglyMeasurable]
    simp only [hφt, smul_eq_mul]
  simp only [hcoef] at h
  convert h using 1
  exact hnorm.symm

/-- **Bessel's identity** on `[−π, π]^d`:
`∫ |f − Σ_{x ∈ s} k(x) e^{ip·x}|² = ∫ |f|² − (2π)^d Σ_{x ∈ s} |k(x)|²` for
`k = latticeFourier f`. -/
private theorem FT1a_bessel (φ : (Fin d → ℝ) → ℂ) (hL2 : MemLp φ 2 (volume.restrict (cubePi d)))
    (s : Finset (Fin d → ℤ)) :
    ∫ p in cubePi d, ‖φ p - ∑ x ∈ s, latticeFourier φ x * zexp p x‖ ^ 2 =
      (∫ p in cubePi d, ‖φ p‖ ^ 2) - (2 * Real.pi) ^ d * ∑ x ∈ s, ‖latticeFourier φ x‖ ^ 2 := by
  set k := latticeFourier φ
  set g : (Fin d → ℝ) → ℂ := fun p => ∑ x ∈ s, k x * zexp p x with hg
  have hzc : ∀ x : Fin d → ℤ, Continuous fun p : Fin d → ℝ => zexp p x := fun x => by
    unfold zexp; fun_prop
  have hgc : Continuous g := continuous_finsetSum _ fun x _ => continuous_const.mul (hzc x)
  have hφi : Integrable φ (volume.restrict (cubePi d)) := hL2.integrable one_le_two
  have hφ2 : Integrable (fun p => ‖φ p‖ ^ 2) (volume.restrict (cubePi d)) :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  have hbdd : ∀ G : (Fin d → ℝ) → ℂ, Continuous G →
      Integrable G (volume.restrict (cubePi d)) := fun G hG =>
    hG.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)
  have hzi : ∀ x, ∫ p in cubePi d, φ p * conj (zexp p x) = (2 * Real.pi : ℂ) ^ d * k x := by
    intro x
    simp_rw [← FT1a_zexp_neg]
    exact FT1a_integral_eq_lf φ x
  have horth : ∀ x y : Fin d → ℤ, ∫ p in cubePi d, zexp p x * conj (zexp p y) =
      if y = x then (2 * Real.pi : ℂ) ^ d else 0 := by
    intro x y
    simp_rw [← FT1a_zexp_neg]
    have := latticeFourier_zexp y x
    unfold latticeFourier at this
    have hne : ((2 * Real.pi : ℂ) ^ d) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast Real.two_pi_pos.ne')
    by_cases hxy : y = x
    · simp only [hxy, ↓reduceIte] at this ⊢
      field_simp at this
      exact this
    · simp only [hxy, ↓reduceIte] at this ⊢
      exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero hne)
  -- the cross term
  have hcross : ∫ p in cubePi d, φ p * conj (g p) =
      (2 * Real.pi : ℂ) ^ d * ∑ x ∈ s, ((‖k x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hg, map_sum, map_mul, Finset.mul_sum]
    rw [integral_finsetSum _ fun x _ => ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      have : ∀ p, φ p * (conj (k x) * conj (zexp p x)) = conj (k x) * (φ p * conj (zexp p x)) :=
        fun p => by ring
      simp_rw [this]
      rw [integral_const_mul, hzi, Complex.ofReal_pow, ← Complex.mul_conj']
      ring
    · refine (hφi.mul_bdd (c := ‖k x‖) ((continuous_const.mul
        ((hzc x).star)).aestronglyMeasurable) ?_)
      refine Filter.Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_conj, Complex.norm_conj, norm_zexp, mul_one]
  have hsq : ∫ p in cubePi d, g p * conj (g p) =
      (2 * Real.pi : ℂ) ^ d * ∑ x ∈ s, ((‖k x‖ ^ 2 : ℝ) : ℂ) := by
    have hexp : ∀ p, g p * conj (g p) =
        ∑ x ∈ s, ∑ y ∈ s, (k x * conj (k y)) * (zexp p x * conj (zexp p y)) := by
      intro p
      simp only [hg, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have hci : ∀ x y : Fin d → ℤ, Integrable
        (fun p => k x * conj (k y) * (zexp p x * conj (zexp p y))) (volume.restrict (cubePi d)) :=
      fun x y => hbdd _ (continuous_const.mul ((hzc x).mul (Complex.continuous_conj.comp (hzc y))))
    simp_rw [hexp]
    rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hci x y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [integral_finsetSum _ fun y _ => hci x y]
    simp_rw [integral_const_mul, horth, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [hx, ↓reduceIte]
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  -- assemble: `|f − g|² = |f|² + |g|² − 2 Re(f ḡ)`
  have hpt : ∀ p, ‖φ p - g p‖ ^ 2 =
      ‖φ p‖ ^ 2 + (g p * conj (g p)).re - 2 * (φ p * conj (g p)).re := by
    intro p
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.mul_conj]
    simp
  have hgi : Integrable (fun p => g p * conj (g p)) (volume.restrict (cubePi d)) :=
    hbdd _ (hgc.mul hgc.star)
  have hfgi : Integrable (fun p => φ p * conj (g p)) (volume.restrict (cubePi d)) := by
    obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ => isCompact_Icc).exists_bound_of_continuousOn
      (hgc.star.continuousOn (s := cubePi d))
    refine hφi.mul_bdd (c := C) (hgc.star.aestronglyMeasurable) ?_
    exact (ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).2
      (Filter.Eventually.of_forall fun p hp => hC p hp)
  change ∫ p in cubePi d, ‖φ p - g p‖ ^ 2 = _
  simp_rw [hpt]
  have hgr : Integrable (fun p => (g p * conj (g p)).re) (volume.restrict (cubePi d)) := hgi.re
  have hfr : Integrable (fun p => (φ p * conj (g p)).re) (volume.restrict (cubePi d)) := hfgi.re
  have hA : Integrable (fun p => ‖φ p‖ ^ 2 + (g p * conj (g p)).re)
      (volume.restrict (cubePi d)) := hφ2.add hgr
  have hB : Integrable (fun p => 2 * (φ p * conj (g p)).re) (volume.restrict (cubePi d)) :=
    hfr.const_mul 2
  rw [integral_sub hA hB, integral_add hφ2 hgr, integral_const_mul]
  have e1 : ∫ p in cubePi d, (g p * conj (g p)).re = (2 * Real.pi) ^ d * ∑ x ∈ s, ‖k x‖ ^ 2 := by
    have := integral_re hgi
    simp only [RCLike.re_to_complex] at this
    rw [this, hsq]
    norm_cast
  have e2 : ∫ p in cubePi d, (φ p * conj (g p)).re = (2 * Real.pi) ^ d * ∑ x ∈ s, ‖k x‖ ^ 2 := by
    have := integral_re hfgi
    simp only [RCLike.re_to_complex] at this
    rw [this, hcross]
    norm_cast
  rw [e1, e2]
  ring

/-- The kernel `k` restricted to the box `⟦−n, n⟧^d`. -/
private def FT1a_trunc (k : (Fin d → ℤ) → ℂ) (n : ℕ) (x : Fin d → ℤ) : ℂ :=
  if x ∈ boxZ d n then k x else 0

private theorem FT1a_zdSeries_trunc (k : (Fin d → ℤ) → ℂ) (n : ℕ) (p : Fin d → ℝ) :
    zdSeries (FT1a_trunc k n) p = ∑ x ∈ boxZ d n, k x * zexp p x := by
  unfold zdSeries FT1a_trunc
  rw [tsum_eq_sum (s := boxZ d n) fun x hx => by simp [hx]]
  exact Finset.sum_congr rfl fun x hx => by simp [hx]

private theorem FT1a_summable_trunc (k : (Fin d → ℤ) → ℂ) (n : ℕ) :
    Summable fun x => ‖FT1a_trunc k n x‖ :=
  summable_of_ne_finset_zero (s := boxZ d n) fun x hx => by simp [FT1a_trunc, hx]

private theorem FT1a_mem_boxZ (x : Fin d → ℤ) : ∃ n, ∀ m, n ≤ m → x ∈ boxZ d m := by
  refine ⟨∑ i, (x i).natAbs, fun m hm => ?_⟩
  simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : (x i).natAbs ≤ m :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans hm
  have h2 : ((x i).natAbs : ℤ) ≤ m := by exact_mod_cast h1
  constructor <;> cases (x i).natAbs_eq <;> omega

private theorem FT1a_tendsto_boxZ : Tendsto (fun n : ℕ => boxZ d n) atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) fun x => ?_
  · intro x hx
    simp only [boxZ, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
    intro i
    have : (m : ℤ) ≤ n := by exact_mod_cast hmn
    exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  · obtain ⟨n, hn⟩ := FT1a_mem_boxZ x
    exact ⟨n, hn n le_rfl⟩

/-- The symbols of the box truncations converge in `L²([−π, π]^d)`. -/
private theorem FT1a_L2_tendsto (φ : (Fin d → ℝ) → ℂ) (hm : Measurable φ)
    (hper : ∀ p (z : Fin d → ℤ), φ (p + fun i => 2 * Real.pi * z i) = φ p)
    (hL2 : MemLp φ 2 (volume.restrict (cubePi d))) :
    Tendsto (fun n : ℕ => ∫ p in cubePi d,
      ‖φ p - zdSeries (FT1a_trunc (latticeFourier φ) n) p‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [FT1a_zdSeries_trunc, FT1a_bessel φ hL2]
  have h := ((FT1a_parseval φ hm hper hL2).comp FT1a_tendsto_boxZ).const_mul ((2 * Real.pi) ^ d)
  have h' := h.const_sub (∫ p in cubePi d, ‖φ p‖ ^ 2)
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ Real.two_pi_pos.ne'), one_mul, sub_self] at h'
  exact h'.congr fun n => rfl

end Parseval

/-! ## The graph Fourier identity -/

section Main

variable {d : ℕ}

attribute [local instance] FT1a_isFinite_cube

private theorem FT1a_zexp_periodic (p : Fin d → ℝ) (z x : Fin d → ℤ) :
    zexp (p + fun i => 2 * Real.pi * z i) x = zexp p x := by
  unfold zexp
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨∑ i, z i * x i, ?_⟩
  have h : (∑ i, (p + fun i => 2 * Real.pi * z i) i * (x i : ℝ)) =
      (∑ i, p i * x i) + 2 * Real.pi * ((∑ i, z i * x i : ℤ) : ℝ) := by
    push_cast
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  push_cast
  ring

private theorem FT1a_zdSeries_periodic (K : (Fin d → ℤ) → ℂ) (p : Fin d → ℝ) (z : Fin d → ℤ) :
    zdSeries K (p + fun i => 2 * Real.pi * z i) = zdSeries K p := by
  unfold zdSeries
  simp_rw [FT1a_zexp_periodic]

private theorem FT1a_memLp_zdSeries (K : (Fin d → ℤ) → ℂ) (hK : Summable fun x => ‖K x‖) :
    MemLp (zdSeries K) 2 (volume.restrict (cubePi d)) :=
  MemLp.of_bound (FT1a_continuous_zdSeries K hK).aestronglyMeasurable (∑' x, ‖K x‖)
    (Filter.Eventually.of_forall fun p => FT1a_norm_zdSeries_le K hK p)

private theorem FT1a_sq_integrable {φ : (Fin d → ℝ) → ℂ}
    (h : MemLp φ 2 (volume.restrict (cubePi d))) :
    IntegrableOn (fun p => ‖φ p‖ ^ 2) (cubePi d) :=
  (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

private theorem FT1a_norm_prod_sub {κ : Type*} [Fintype κ] [DecidableEq κ] (F G : κ → ℂ) (b : κ)
    (hFG : ∀ c, c ≠ b → G c = F c) :
    ‖∏ c, F c - ∏ c, G c‖ = ‖F b - G b‖ * ∏ c ∈ Finset.univ.erase b, ‖F c‖ := by
  rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ b),
    ← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ b),
    Finset.prod_congr rfl fun c hc => hFG c (Finset.ne_of_mem_erase hc), ← sub_mul, norm_mul,
    norm_prod]

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]
variable {e : ι → V × V}

/-- Under the hypotheses of the induction, every symbol is square integrable on `[−π, π]^d`. -/
private theorem FT1a_memLp_all {T₁ : List ι} (B : Finset ι)
    (k : ι → (Fin d → ℤ) → ℂ) (φ : ι → (Fin d → ℝ) → ℂ)
    (h1 : ∀ c, (c ∉ T₁ ∨ c ∈ B) →
      k c = latticeFourier (φ c) ∧ MemLp (φ c) 2 (volume.restrict (cubePi d)))
    (h2 : ∀ c, c ∈ T₁ → c ∉ B → Summable (fun x => ‖k c x‖) ∧ φ c = zdSeries (k c)) (c : ι) :
    MemLp (φ c) 2 (volume.restrict (cubePi d)) := by
  by_cases h : c ∉ T₁ ∨ c ∈ B
  · exact (h1 c h).2
  · push Not at h
    rw [(h2 c h.1 h.2).2]
    exact FT1a_memLp_zdSeries _ (h2 c h.1 h.2).1

/-- The integrand of the momentum side is integrable, by the momentum Cauchy–Schwarz bound. -/
private theorem FT1a_integrable_main {T₁ T₂ : List ι}
    (hTr₁ : TreeEdges (T₁.map e)) (hTr₂ : TreeEdges (T₂.map e)) (P : V → Fin d → ℝ)
    (B : Finset ι) (hB : ∀ c ∈ B, c ∈ T₁ ∧ c ∉ T₂)
    (k : ι → (Fin d → ℤ) → ℂ) (φ : ι → (Fin d → ℝ) → ℂ) (hm : ∀ c, Measurable (φ c))
    (hper : ∀ c p (z : Fin d → ℤ), φ c (p + fun i => 2 * Real.pi * z i) = φ c p)
    (h1 : ∀ c, (c ∉ T₁ ∨ c ∈ B) →
      k c = latticeFourier (φ c) ∧ MemLp (φ c) 2 (volume.restrict (cubePi d)))
    (h2 : ∀ c, c ∈ T₁ → c ∉ B → Summable (fun x => ‖k c x‖) ∧ φ c = zdSeries (k c)) :
    IntegrableOn (fun q => ∏ c, φ c (FT1a.edgeMom e T₁ P q c))
      (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) := by
  have hcs := FT1a.momentumCS e T₁ T₂ hTr₁ hTr₂ P (fun c p => ‖φ c p‖)
    (fun c p => norm_nonneg _) (fun c => (hm c).norm)
    (fun c p z => by simp only [hper c p z]) (fun c => ∑' x, ‖k c x‖)
    (fun c hc1 hc2 p => by
      have hcB : c ∉ B := fun h => (hB c h).2 hc2
      change ‖φ c p‖ ≤ _
      rw [(h2 c hc1 hcB).2]
      exact FT1a_norm_zdSeries_le _ (h2 c hc1 hcB).1 p)
    (fun c _ => FT1a_sq_integrable (FT1a_memLp_all B k φ h1 h2 c))
  refine hcs.1.mono' ((Finset.measurable_prod _ fun c _ =>
    (hm c).comp (FT1a_continuous_edgeMom P c).measurable).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun q => by rw [norm_prod]

/-- The induction on the tree edges of `T₁ ∖ T₂` whose kernels are not assumed in `ℓ¹`: each is
replaced by its box truncations, with the position side converging by dominated convergence and
the momentum side by the Cauchy–Schwarz bound and Parseval. -/
private theorem FT1a_main (v₀ : V) {T₁ T₂ : List ι}
    (hTr₁ : TreeEdges (T₁.map e)) (hTr₂ : TreeEdges (T₂.map e)) (P : V → Fin d → ℝ)
    (hP : ∑ v, P v = 0) :
    ∀ (B : Finset ι), (∀ c ∈ B, c ∈ T₁ ∧ c ∉ T₂) →
    ∀ (k : ι → (Fin d → ℤ) → ℂ) (φ : ι → (Fin d → ℝ) → ℂ),
      (∀ c, Measurable (φ c)) →
      (∀ c p (z : Fin d → ℤ), φ c (p + fun i => 2 * Real.pi * z i) = φ c p) →
      (∀ c, (c ∉ T₁ ∨ c ∈ B) →
        k c = latticeFourier (φ c) ∧ MemLp (φ c) 2 (volume.restrict (cubePi d))) →
      (∀ c, c ∈ T₁ → c ∉ B → Summable (fun x => ‖k c x‖) ∧ φ c = zdSeries (k c)) →
      Summable (fun σ : {σ : V → Fin d → ℤ // σ v₀ = 0} =>
        ∏ c, ‖k c (σ.1 (e c).2 - σ.1 (e c).1)‖) →
      ∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
          (∏ c, k c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v) =
        ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T₁}))⁻¹ *
          ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
            ∏ c, φ c (FT1a.edgeMom e T₁ P q c) := by
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _ k φ _ _ h1 h2 _
    exact (FT1a_l1 v₀ hTr₁ P hP k φ (fun f hf => (h2 f hf (Finset.notMem_empty f)).1)
      (fun f hf => (h2 f hf (Finset.notMem_empty f)).2)
      (fun c hc => (h1 c (Or.inl hc)).2.integrable one_le_two)
      (fun c hc => (h1 c (Or.inl hc)).1)).2
  | @insert b B₀ hb ih =>
    intro hB k φ hm hper h1 h2 h3
    have hbT : b ∈ T₁ ∧ b ∉ T₂ := hB b (Finset.mem_insert_self b B₀)
    have hB₀ : ∀ c ∈ B₀, c ∈ T₁ ∧ c ∉ T₂ := fun c hc => hB c (Finset.mem_insert_of_mem hc)
    have hkb : k b = latticeFourier (φ b) := (h1 b (Or.inr (Finset.mem_insert_self b B₀))).1
    -- the truncated families
    let kn : ℕ → ι → (Fin d → ℤ) → ℂ := fun n => Function.update k b (FT1a_trunc (k b) n)
    let φn : ℕ → ι → (Fin d → ℝ) → ℂ := fun n =>
      Function.update φ b (zdSeries (FT1a_trunc (k b) n))
    have hkn_ne : ∀ n c, c ≠ b → kn n c = k c := fun n c hc => Function.update_of_ne hc _ _
    have hφn_ne : ∀ n c, c ≠ b → φn n c = φ c := fun n c hc => Function.update_of_ne hc _ _
    have hkn_b : ∀ n, kn n b = FT1a_trunc (k b) n := fun n => Function.update_self _ _ _
    have hφn_b : ∀ n, φn n b = zdSeries (FT1a_trunc (k b) n) := fun n =>
      Function.update_self _ _ _
    have hle : ∀ n c x, ‖kn n c x‖ ≤ ‖k c x‖ := by
      intro n c x
      by_cases hc : c = b
      · subst hc
        rw [hkn_b]
        unfold FT1a_trunc
        split_ifs <;> simp
      · rw [hkn_ne n c hc]
    have hm' : ∀ n c, Measurable (φn n c) := by
      intro n c
      by_cases hc : c = b
      · subst hc
        rw [hφn_b]
        exact (FT1a_continuous_zdSeries _ (FT1a_summable_trunc _ _)).measurable
      · rw [hφn_ne n c hc]; exact hm c
    have hper' : ∀ n c p (z : Fin d → ℤ),
        φn n c (p + fun i => 2 * Real.pi * z i) = φn n c p := by
      intro n c p z
      by_cases hc : c = b
      · subst hc
        rw [hφn_b]
        exact FT1a_zdSeries_periodic _ p z
      · rw [hφn_ne n c hc]; exact hper c p z
    have h1' : ∀ n c, (c ∉ T₁ ∨ c ∈ B₀) →
        kn n c = latticeFourier (φn n c) ∧ MemLp (φn n c) 2 (volume.restrict (cubePi d)) := by
      intro n c hc
      have hcb : c ≠ b := by
        rintro rfl
        rcases hc with hc | hc
        · exact hc hbT.1
        · exact hb hc
      rw [hkn_ne n c hcb, hφn_ne n c hcb]
      exact h1 c (hc.imp id Finset.mem_insert_of_mem)
    have h2' : ∀ n c, c ∈ T₁ → c ∉ B₀ →
        Summable (fun x => ‖kn n c x‖) ∧ φn n c = zdSeries (kn n c) := by
      intro n c hc1 hc2
      by_cases hcb : c = b
      · subst hcb
        rw [hkn_b, hφn_b]
        exact ⟨FT1a_summable_trunc _ _, rfl⟩
      · rw [hkn_ne n c hcb, hφn_ne n c hcb]
        exact h2 c hc1 fun h => (Finset.mem_insert.1 h).elim hcb hc2
    have h3' : ∀ n, Summable (fun σ : {σ : V → Fin d → ℤ // σ v₀ = 0} =>
        ∏ c, ‖kn n c (σ.1 (e c).2 - σ.1 (e c).1)‖) := fun n =>
      h3.of_nonneg_of_le (fun σ => Finset.prod_nonneg fun c _ => norm_nonneg _)
        fun σ => Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hle n c _
    have hid : ∀ n, ∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
        (∏ c, kn n c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v) =
          ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T₁}))⁻¹ *
            ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
              ∏ c, φn n c (FT1a.edgeMom e T₁ P q c) := fun n =>
      ih hB₀ (kn n) (φn n) (hm' n) (hper' n) (h1' n) (h2' n) (h3' n)
    -- the position side converges
    have hL : Tendsto (fun n => ∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
        (∏ c, kn n c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v)) atTop
        (𝓝 (∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
          (∏ c, k c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v))) := by
      refine tendsto_tsum_of_dominated_convergence h3 (fun σ => ?_) ?_
      · obtain ⟨N, hN⟩ := FT1a_mem_boxZ (σ.1 (e b).2 - σ.1 (e b).1)
        refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        congr 1
        refine Finset.prod_congr rfl fun c _ => ?_
        by_cases hc : c = b
        · subst hc
          rw [hkn_b]
          unfold FT1a_trunc
          simp only [hN n hn, ↓reduceIte]
        · rw [hkn_ne n c hc]
      · refine Filter.Eventually.of_forall fun n σ => ?_
        rw [norm_mul, norm_prod, norm_prod]
        simp only [norm_zexp, Finset.prod_const_one, mul_one]
        exact Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) fun c _ => hle n c _
    -- the momentum side converges
    have hint : IntegrableOn (fun q => ∏ c, φ c (FT1a.edgeMom e T₁ P q c))
        (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) :=
      FT1a_integrable_main hTr₁ hTr₂ P _ hB k φ hm hper h1 h2
    have hint' : ∀ n, IntegrableOn (fun q => ∏ c, φn n c (FT1a.edgeMom e T₁ P q c))
        (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) := fun n =>
      FT1a_integrable_main hTr₁ hTr₂ P _ hB₀ (kn n) (φn n) (hm' n) (hper' n) (h1' n)
        (h2' n)
    have hL2b : MemLp (φ b) 2 (volume.restrict (cubePi d)) :=
      (h1 b (Or.inr (Finset.mem_insert_self b B₀))).2
    -- the Cauchy–Schwarz bound for the difference
    let gn : ℕ → ι → (Fin d → ℝ) → ℝ := fun n =>
      Function.update (fun c p => ‖φ c p‖) b (fun p => ‖φ b p - φn n b p‖)
    have hgn_ne : ∀ n c, c ≠ b → gn n c = fun p => ‖φ c p‖ := fun n c hc =>
      Function.update_of_ne hc _ _
    have hgn_b : ∀ n, gn n b = fun p => ‖φ b p - φn n b p‖ := fun n => Function.update_self _ _ _
    have hMemAll := FT1a_memLp_all (insert b B₀) k φ h1 h2
    have hcs : ∀ n, _ := fun n => FT1a.momentumCS e T₁ T₂ hTr₁ hTr₂ P (gn n)
      (fun c p => by
        by_cases hc : c = b
        · subst hc; rw [hgn_b]; exact norm_nonneg _
        · rw [hgn_ne n c hc]; exact norm_nonneg _)
      (fun c => by
        by_cases hc : c = b
        · subst hc; rw [hgn_b]; exact ((hm c).sub (hm' n c)).norm
        · rw [hgn_ne n c hc]; exact (hm c).norm)
      (fun c p z => by
        by_cases hc : c = b
        · subst hc; rw [hgn_b]; simp only [hper c p z, hper' n c p z]
        · rw [hgn_ne n c hc]; simp only [hper c p z])
      (fun c => ∑' x, ‖k c x‖)
      (fun c hc1 hc2 p => by
        have hcb : c ≠ b := fun h => hbT.2 (h ▸ hc2)
        have hcB : c ∉ insert b B₀ := fun h => (hB c h).2 hc2
        rw [hgn_ne n c hcb]
        change ‖φ c p‖ ≤ _
        rw [(h2 c hc1 hcB).2]
        exact FT1a_norm_zdSeries_le _ (h2 c hc1 hcB).1 p)
      (fun c _ => by
        by_cases hc : c = b
        · subst hc
          rw [hgn_b]
          refine FT1a_sq_integrable (hL2b.sub ?_)
          rw [hφn_b]
          exact FT1a_memLp_zdSeries _ (FT1a_summable_trunc _ _)
        · rw [hgn_ne n c hc]
          exact FT1a_sq_integrable (hMemAll c))
    have hdiff : ∀ n, ‖(∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
        ∏ c, φ c (FT1a.edgeMom e T₁ P q c)) -
          ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
            ∏ c, φn n c (FT1a.edgeMom e T₁ P q c)‖ ≤
        ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
          ∏ c, gn n c (FT1a.edgeMom e T₁ P q c) := by
      intro n
      rw [← integral_sub hint (hint' n)]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only
      rw [FT1a_norm_prod_sub _ _ b fun c hc => by rw [hφn_ne n c hc],
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), hgn_b]
      congr 1
      refine Finset.prod_congr rfl fun c hc => ?_
      rw [hgn_ne n c (Finset.ne_of_mem_erase hc)]
    -- the bound tends to `0`
    have hL2t := FT1a_L2_tendsto (φ b) (hm b) (hper b) hL2b
    rw [← hkb] at hL2t
    have hfac : Tendsto (fun n => √(∫ p in cubePi d, gn n b p ^ 2)) atTop (𝓝 0) := by
      have : (fun n => √(∫ p in cubePi d, gn n b p ^ 2)) =
          fun n => √(∫ p in cubePi d, ‖φ b p - zdSeries (FT1a_trunc (k b) n) p‖ ^ 2) := by
        funext n
        rw [hgn_b, hφn_b]
      rw [this, ← Real.sqrt_zero]
      exact (Real.continuous_sqrt.tendsto 0).comp hL2t
    have hbound : Tendsto (fun n =>
        (∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, ∑' x, ‖k c.1 x‖) *
          (∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, gn n c.1 p ^ 2)) *
          √((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
            Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂}))) *
          ∏ c : {c // c ∈ T₁ ∧ c ∉ T₂}, √(∫ p in cubePi d, gn n c.1 p ^ 2)) atTop (𝓝 0) := by
      have hA : ∀ n, ∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, gn n c.1 p ^ 2) =
          ∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, ‖φ c.1 p‖ ^ 2) := fun n =>
        Finset.prod_congr rfl fun c _ => by
          rw [hgn_ne n c.1 fun h => c.2 (h ▸ hbT.1)]
      simp_rw [hA]
      rw [← mul_zero ((∏ c : {c // c ∈ T₁ ∧ c ∈ T₂}, ∑' x, ‖k c.1 x‖) *
          (∏ c : {c // c ∉ T₁}, √(∫ p in cubePi d, ‖φ c.1 p‖ ^ 2)) *
          √((2 * Real.pi) ^ (d * (Fintype.card {c // c ∉ T₁} -
            Fintype.card {c // c ∈ T₁ ∧ c ∉ T₂}))))]
      refine tendsto_const_nhds.mul ?_
      rw [← Finset.prod_eq_zero (Finset.mem_univ (⟨b, hbT⟩ : {c // c ∈ T₁ ∧ c ∉ T₂}))
        (f := fun c : {c // c ∈ T₁ ∧ c ∉ T₂} =>
          if c.1 = b then (0 : ℝ) else √(∫ p in cubePi d, ‖φ c.1 p‖ ^ 2)) (by simp)]
      refine tendsto_finsetProd _ fun c _ => ?_
      by_cases hc : c.1 = b
      · simp only [hc, ↓reduceIte]
        exact hfac
      · simp only [hc, ↓reduceIte]
        refine tendsto_const_nhds.congr fun n => ?_
        rw [hgn_ne n c.1 hc]
    have hR : Tendsto (fun n => ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
        ∏ c, φn n c (FT1a.edgeMom e T₁ P q c)) atTop
        (𝓝 (∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
          ∏ c, φ c (FT1a.edgeMom e T₁ P q c))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbound
      rw [norm_sub_rev]
      exact (hdiff n).trans ((hcs n).2)
    have hR' := hR.const_mul ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T₁}))⁻¹
    simp_rw [← hid] at hR'
    exact tendsto_nhds_unique hL hR'

variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- **[I, (7.29)–(7.30)] on `ℤ^d`: the graph Fourier identity.** A graph on the vertices `V` with
`v₀` pinned at `0` and edges `c` from `t_c` to `h_c` (`e c = (t_c, h_c)`), with two spanning trees
`T₁`, `T₂` and external momenta `P`, `Σ_v P_v = 0`. Each edge carries a kernel `k_c` on `ℤ^d` and
a Borel `2π`-periodic symbol `f_c` such that
* (H1) `k_c = latticeFourier f_c` and `f_c ∈ L²([−π, π]^d)`;
* (H2) for `c ∈ T₁ ∩ T₂`, `k_c ∈ ℓ¹` and `f_c = zdSeries k_c`;
* (H3) `σ ↦ Π_c |k_c(σ_{h_c} − σ_{t_c})|` is summable over `σ` with `σ_{v₀} = 0`.

Then the momentum integrand `Π_c f_c(ℓ_c(q) + λ_c(P))` (`FT1a.edgeMom`, momenta fixed by the tree
`T₁`) is integrable on `([−π, π]^d)^L`, `L = |E| − |V| + 1`, and
`Σ_{σ, σ_{v₀} = 0} Π_c k_c(σ_{h_c} − σ_{t_c}) e^{i Σ_v P_v·σ_v}
  = (2π)^{-dL} ∫_{([−π,π]^d)^L} Π_c f_c(ℓ_c(q) + λ_c(P)) dq`.

This is [I, (7.29)–(7.30)] taken directly on `ℤ^d`, with external momenta; the integrability is the
momentum Cauchy–Schwarz bound `FT1a.momentumCS`. -/
theorem FT1a.graphFourier (v₀ : V) (e : ι → V × V) (T₁ T₂ : List ι)
    (hTr₁ : TreeEdges (T₁.map e)) (hTr₂ : TreeEdges (T₂.map e)) (P : V → Fin d → ℝ)
    (hP : ∑ v, P v = 0) (k : ι → (Fin d → ℤ) → ℂ) (f : ι → (Fin d → ℝ) → ℂ)
    (hfm : ∀ c, Measurable (f c))
    (hfp : ∀ c p (z : Fin d → ℤ), f c (p + fun i => 2 * Real.pi * z i) = f c p)
    (H1 : ∀ c, k c = latticeFourier (f c) ∧ MemLp (f c) 2 (volume.restrict (cubePi d)))
    (H2 : ∀ c, c ∈ T₁ → c ∈ T₂ → Summable (fun x => ‖k c x‖) ∧ f c = zdSeries (k c))
    (H3 : Summable fun σ : {σ : V → Fin d → ℤ // σ v₀ = 0} =>
      ∏ c, ‖k c (σ.1 (e c).2 - σ.1 (e c).1)‖) :
    IntegrableOn (fun q => ∏ c, f c (FT1a.edgeMom e T₁ P q c))
        (Set.univ.pi fun _ : {c // c ∉ T₁} => cubePi d) ∧
      ∑' σ : {σ : V → Fin d → ℤ // σ v₀ = 0},
          (∏ c, k c (σ.1 (e c).2 - σ.1 (e c).1)) * ∏ v, zexp (P v) (σ.1 v) =
        ((2 * Real.pi : ℂ) ^ (d * Fintype.card {c // c ∉ T₁}))⁻¹ *
          ∫ q in Set.univ.pi (fun _ : {c // c ∉ T₁} => cubePi d),
            ∏ c, f c (FT1a.edgeMom e T₁ P q c) := by
  set B : Finset ι := Finset.univ.filter fun c => c ∈ T₁ ∧ c ∉ T₂
  have hB : ∀ c ∈ B, c ∈ T₁ ∧ c ∉ T₂ := fun c hc => (Finset.mem_filter.1 hc).2
  have h1 : ∀ c, (c ∉ T₁ ∨ c ∈ B) →
      k c = latticeFourier (f c) ∧ MemLp (f c) 2 (volume.restrict (cubePi d)) := fun c _ => H1 c
  have h2 : ∀ c, c ∈ T₁ → c ∉ B → Summable (fun x => ‖k c x‖) ∧ f c = zdSeries (k c) := by
    intro c hc1 hcB
    refine H2 c hc1 ?_
    by_contra hc2
    exact hcB (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc1, hc2⟩)
  exact ⟨FT1a_integrable_main hTr₁ hTr₂ P B hB k f hfm hfp h1 h2,
    FT1a_main v₀ hTr₁ hTr₂ P hP B hB k f hfm hfp h1 h2 H3⟩

end Main

section Examples

end Examples

end RBM8D
