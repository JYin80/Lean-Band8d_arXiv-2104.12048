import RBM8D.TExp.Defs
import RBM8D.Kernel.ThetaDecay
import RBM8D.Kernel.ZdCancel
import RBM8D.Profile.Symbol
import RBM8D.Input.Entry
import RBM8D.Input.Sizes
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Base
import RBM8D.Bound.KeySum

/-!
# Auxiliary graphs with a black and a blue spanning tree ([I, Claim 6.11])
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

/-- An auxiliary graph of [I, Claim 6.11] with two external atoms `x = 0`, `y = 1` and `ℓ`
internal atoms: black double-line edges, each a factor `B`, and blue solid edges, each the
absolute value of an entry of the matrix with the given index. -/
structure AuxGraph (ℓ : ℕ) where
  black : List (Atom 2 ℓ × Atom 2 ℓ)
  blue : List (Atom 2 ℓ × Atom 2 ℓ × ℕ)

/-- The edges `es` form a spanning tree of the vertex type: their number is one less than the
number of vertices, and they connect all vertices. -/
def TreeEdges {V : Type*} [Fintype V] (es : List (V × V)) : Prop :=
  es.length + 1 = Fintype.card V ∧ (SimpleGraph.fromRel fun u v => (u, v) ∈ es).Preconnected

/-- The value of an auxiliary graph at `x, y`: the sum over the internal atoms of the product of
`B` over the black edges and of `|A_j|` over the blue edges. -/
def AuxGraph.val {ℓ : ℕ} (Γ : AuxGraph ℓ) (d L W : ℕ) [NeZero L]
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) : ℝ :=
  ∑ s : Fin ℓ → Zd d L,
    (Γ.black.map fun e => bB d L W (Sum.elim ![x, y] s e.1) (Sum.elim ![x, y] s e.2)).prod *
      (Γ.blue.map fun e =>
        |A e.2.2 (Sum.elim ![x, y] s e.1) (Sum.elim ![x, y] s e.2.1)|).prod

/-- The normalized value `W^{aℓd/2} Γ̃_{xy} / B_{xy}`, the variable `𝒜_{xy}` of [I, (6.31)]. -/
def AuxGraph.normVal {ℓ : ℕ} (Γ : AuxGraph ℓ) (d L W : ℕ) [NeZero L] (a : ℝ)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) : Matrix (Zd d L) (Zd d L) ℝ :=
  fun x y => (W : ℝ) ^ (a * ℓ * d / 2) * Γ.val d L W A x y / bB d L W x y

section SumS
variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]

private def sumS (S : Finset V) (F : (V → α) → ℝ) (ψ : V → α) : ℝ :=
  ∑ g, if ∀ w, w ∉ S → g w = ψ w then F g else 0

private theorem sumS_empty (F : (V → α) → ℝ) (ψ : V → α) : sumS ∅ F ψ = F ψ := by
  unfold sumS
  have h : ∀ g : V → α, (∀ w, w ∉ (∅ : Finset V) → g w = ψ w) ↔ g = ψ := fun g =>
    ⟨fun h => funext fun w => h w (Finset.notMem_empty w), fun h w _ => h ▸ rfl⟩
  simp only [h]
  simp

private theorem sumS_insert {S : Finset V} {v : V} (hv : v ∉ S) (F : (V → α) → ℝ)
    (ψ : V → α) : sumS (insert v S) F ψ = ∑ z, sumS S F (Function.update ψ v z) := by
  unfold sumS
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have key : ∀ z, (∀ w, w ∉ S → g w = Function.update ψ v z w) ↔
      ((∀ w, w ∉ insert v S → g w = ψ w) ∧ g v = z) := by
    intro z
    constructor
    · intro h
      refine ⟨fun w hw => ?_, ?_⟩
      · have hwv : w ≠ v := fun h' => hw (h' ▸ Finset.mem_insert_self _ _)
        rw [h w (fun h' => hw (Finset.mem_insert_of_mem h')), Function.update_of_ne hwv]
      · rw [h v hv, Function.update_self]
    · rintro ⟨h1, h2⟩ w hw
      by_cases hwv : w = v
      · subst hwv; rw [Function.update_self, h2]
      · rw [Function.update_of_ne hwv]; exact h1 w (by simp [hwv, hw])
  have key' : ∀ z, (if ∀ w, w ∉ S → g w = Function.update ψ v z w then F g else 0) =
      if g v = z then (if ∀ w, w ∉ insert v S → g w = ψ w then F g else 0) else 0 := by
    intro z
    by_cases h1 : ∀ w, w ∉ insert v S → g w = ψ w <;> by_cases h2 : g v = z
    · simp only [eq_true ((key z).2 ⟨h1, h2⟩), eq_true h1, h2, ↓reduceIte]
    · simp only [eq_false (fun h => h2 ((key z).1 h).2), h2, ↓reduceIte]
    · simp only [eq_false (fun h => h1 ((key z).1 h).1), eq_false h1, h2, ↓reduceIte]
    · simp only [eq_false (fun h => h2 ((key z).1 h).2), h2, ↓reduceIte]
  rw [Finset.sum_congr rfl fun z _ => key' z, Finset.sum_ite_eq]
  simp

private theorem sumS_mono (S : Finset V) {F G : (V → α) → ℝ} (h : ∀ g, F g ≤ G g)
    (ψ : V → α) : sumS S F ψ ≤ sumS S G ψ := by
  unfold sumS
  refine Finset.sum_le_sum fun g _ => ?_
  split_ifs
  · exact h g
  · exact le_rfl

private theorem sumS_sum {ι : Type*} (S : Finset V) (I : Finset ι) (F : ι → (V → α) → ℝ)
    (ψ : V → α) : sumS S (fun g => ∑ i ∈ I, F i g) ψ = ∑ i ∈ I, sumS S (F i) ψ := by
  unfold sumS
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

private theorem sumS_mul (S : Finset V) (c : ℝ) (F : (V → α) → ℝ) (ψ : V → α) :
    sumS S (fun g => c * F g) ψ = c * sumS S F ψ := by
  unfold sumS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

private theorem sumS_comp_update {S : Finset V} {v : V} (hv : v ∉ S) (F : (V → α) → ℝ)
    (z : α) (ψ : V → α) :
    sumS S (fun g => F (Function.update g v z)) ψ = sumS S F (Function.update ψ v z) := by
  induction S using Finset.induction_on generalizing ψ with
  | empty => simp only [sumS_empty]
  | insert w S hw ih =>
    have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self _ _)
    have hvS : v ∉ S := fun h => hv (Finset.mem_insert_of_mem h)
    rw [sumS_insert hw, sumS_insert hw]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [ih hvS, Function.update_comm hvw]

private theorem sumS_inner {S : Finset V} {v : V} (hv : v ∉ S) (F : (V → α) → ℝ)
    (ψ : V → α) :
    sumS (insert v S) F ψ = sumS S (fun g => ∑ z, F (Function.update g v z)) ψ := by
  rw [sumS_insert hv, sumS_sum]
  exact Finset.sum_congr rfl fun z _ => (sumS_comp_update hv F z ψ).symm

end SumS

section Lists
variable {β : Type*}

private theorem prod_map_eraseIdx (l : List β) (f : β → ℝ) (i : ℕ) (hi : i < l.length) :
    (l.map f).prod = f l[i] * ((l.eraseIdx i).map f).prod := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.map_cons, List.prod_cons, List.eraseIdx_cons_succ, List.getElem_cons_succ]
      rw [ih i (by simpa using hi)]
      ring

private theorem prod_map_nonneg (l : List β) (f : β → ℝ) (h : ∀ e ∈ l, 0 ≤ f e) :
    0 ≤ (l.map f).prod :=
  List.prod_nonneg (by simpa using h)

private theorem prod_map_le_one (l : List β) (f : β → ℝ) (h0 : ∀ e ∈ l, 0 ≤ f e)
    (h1 : ∀ e ∈ l, f e ≤ 1) : (l.map f).prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha0 := h0 a List.mem_cons_self
    have ha1 := h1 a List.mem_cons_self
    have ih' := ih (fun e he => h0 e (List.mem_cons_of_mem _ he))
      (fun e he => h1 e (List.mem_cons_of_mem _ he))
    calc f a * (l.map f).prod ≤ 1 * 1 :=
          mul_le_mul ha1 ih' (prod_map_nonneg l f fun e he => h0 e (List.mem_cons_of_mem _ he))
            zero_le_one
      _ = 1 := one_mul 1

private theorem prod_map_le_pow (l : List β) (f f' : β → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ e ∈ l, 0 ≤ f e ∧ 0 ≤ f' e ∧ f e ≤ c * f' e) :
    (l.map f).prod ≤ c ^ l.length * (l.map f').prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have ha := h a List.mem_cons_self
    have ih' := ih fun e he => h e (List.mem_cons_of_mem _ he)
    have h0 : 0 ≤ (l.map f).prod :=
      prod_map_nonneg l f fun e he => (h e (List.mem_cons_of_mem _ he)).1
    have h0' : 0 ≤ (l.map f').prod :=
      prod_map_nonneg l f' fun e he => (h e (List.mem_cons_of_mem _ he)).2.1
    calc f a * (l.map f).prod ≤ (c * f' a) * (c ^ l.length * (l.map f').prod) :=
          mul_le_mul ha.2.2 ih' h0 (mul_nonneg hc ha.2.1)
      _ = _ := by ring

/-- A product of factors in `[0, 1]` is at most the product over the factors picked out by an
injective choice of indices. -/
private theorem prod_map_le_sub (l : List β) (f : β → ℝ) (h0 : ∀ e ∈ l, 0 ≤ f e)
    (h1 : ∀ e ∈ l, f e ≤ 1) {T : Type*} (s : Finset T) (κ : T → Fin l.length)
    (hκ : ∀ t ∈ s, ∀ t' ∈ s, κ t = κ t' → t = t') :
    (l.map f).prod ≤ ∏ t ∈ s, f l[κ t] := by
  classical
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  have hsub : s.image κ ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.prod_sdiff hsub, Finset.prod_image hκ]
  have hA : 0 ≤ ∏ t ∈ s, f l[κ t] :=
    Finset.prod_nonneg fun t _ => h0 _ (List.getElem_mem _)
  have hB : ∏ i ∈ Finset.univ \ s.image κ, f l[i] ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => h0 _ (List.getElem_mem _))
      (fun i _ => h1 _ (List.getElem_mem _))
  calc (∏ i ∈ Finset.univ \ s.image κ, f l[i]) * ∏ t ∈ s, f l[κ t]
      ≤ 1 * ∏ t ∈ s, f l[κ t] := mul_le_mul_of_nonneg_right hB hA
    _ = _ := one_mul _

end Lists

section Graphs
variable {V : Type*}

/-- The edge `e` joins a vertex of `U` to a vertex outside `U`. -/
private def Cross (e : V × V) (U : V → Prop) : Prop := (U e.1 ∧ ¬ U e.2) ∨ (U e.2 ∧ ¬ U e.1)

/-- Parent data of an edge list rooted at the vertices `A`: the parent `q v`, the height `h v`
(the graph distance to `A`), and the index `ι v` of an edge joining `v` and `q v`. -/
private structure PD (E : List (V × V)) (A : V → Prop) (q : V → V) (h ι : V → ℕ) : Prop where
  anch : ∀ v, A v → h v = 0 ∧ q v = v
  step : ∀ v, ¬ A v → h (q v) + 1 = h v
  idx : ∀ v, ¬ A v → ∃ hi : ι v < E.length, E[ι v] = (v, q v) ∨ E[ι v] = (q v, v)

variable {E : List (V × V)} {A : V → Prop} {q : V → V} {h ι : V → ℕ}

private theorem PD.zero_iff (P : PD E A q h ι) (v : V) : h v = 0 ↔ A v := by
  constructor
  · intro hv
    by_contra hA
    have := P.step v hA
    omega
  · exact fun hA => (P.anch v hA).1

private theorem PD.q_ne (P : PD E A q h ι) {v : V} (hv : ¬ A v) : q v ≠ v := by
  intro he
  have := P.step v hv
  rw [he] at this
  omega

private theorem PD.inj (P : PD E A q h ι) {v w : V} (hv : ¬ A v) (hw : ¬ A w)
    (he : ι v = ι w) : v = w := by
  obtain ⟨hi, h1⟩ := P.idx v hv
  obtain ⟨hj, h2⟩ := P.idx w hw
  have hsv := P.step v hv
  have hsw := P.step w hw
  have heq : E[ι v] = E[ι w] := by simp only [he]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at heq <;>
    simp only [Prod.mk.injEq] at heq
  · exact heq.1
  · rw [heq.2] at hsv; rw [← heq.1] at hsw; omega
  · rw [heq.1] at hsv; rw [← heq.2] at hsw; omega
  · exact heq.2

private theorem PD.iter (P : PD E A q h ι) (v : V) :
    ∀ j, j ≤ h v → h (q^[j] v) = h v - j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have hA : ¬ A (q^[j] v) := fun hA => by
      have := (P.zero_iff _).2 hA
      omega
    rw [Function.iterate_succ_apply', ← P.step _ hA] at *
    omega

/-- In an anchored set of vertices, a vertex of least height has its parent outside the set. -/
private theorem PD.exists_min (P : PD E A q h ι) (U : V → Prop) (hU : ∃ u, U u)
    (hUA : ∀ u, U u → ¬ A u) : ∃ u, U u ∧ ¬ U (q u) ∧ ∀ u', U u' → h u ≤ h u' := by
  classical
  have hex : ∃ n, ∃ u, U u ∧ h u = n := by
    obtain ⟨u, hu⟩ := hU
    exact ⟨h u, u, hu, rfl⟩
  obtain ⟨u, hu, hun⟩ := Nat.find_spec hex
  refine ⟨u, hu, fun hq => ?_, fun u' hu' => ?_⟩
  · have := Nat.find_min' hex ⟨q u, hq, rfl⟩
    have := P.step u (hUA u hu)
    omega
  · rw [hun]
    exact Nat.find_min' hex ⟨u', hu', rfl⟩

private theorem PD.cross_idx (P : PD E A q h ι) {U : V → Prop} {u : V} (hA : ¬ A u)
    (hu : U u) (hq : ¬ U (q u)) : ∃ hi : ι u < E.length, Cross E[ι u] U := by
  obtain ⟨hi, he⟩ := P.idx u hA
  refine ⟨hi, ?_⟩
  rcases he with he | he <;> rw [he] <;> simp [Cross, hu, hq]

/-- Parent data exist whenever every vertex is joined to `A`. -/
private theorem PD.exists' (E : List (V × V)) (A : V → Prop)
    (hreach : ∀ v, ∃ a, A a ∧ (SimpleGraph.fromRel fun u w => (u, w) ∈ E).Reachable v a) :
    ∃ q h ι, PD E A q h ι := by
  classical
  set G := SimpleGraph.fromRel fun u w => (u, w) ∈ E with hG
  have hP : ∀ v, ∃ n, ∃ a, A a ∧ ∃ p : G.Walk v a, p.length = n := fun v => by
    obtain ⟨a, ha, ⟨p⟩⟩ := hreach v
    exact ⟨p.length, a, ha, p, rfl⟩
  have hstep : ∀ v, ¬ A v → ∃ w, G.Adj v w ∧ Nat.find (hP w) + 1 = Nat.find (hP v) := by
    intro v hv
    obtain ⟨a, ha, p, hp⟩ := Nat.find_spec (hP v)
    cases p with
    | nil => exact absurd ha hv
    | @cons _ w _ hadj p' =>
      refine ⟨w, hadj, ?_⟩
      have h1 : Nat.find (hP w) ≤ p'.length := Nat.find_min' (hP w) ⟨a, ha, p', rfl⟩
      have h2 : Nat.find (hP v) ≤ Nat.find (hP w) + 1 := by
        obtain ⟨a', ha', p'', hp''⟩ := Nat.find_spec (hP w)
        exact Nat.find_min' (hP v) ⟨a', ha', SimpleGraph.Walk.cons hadj p'', by simp [hp'']⟩
      simp only [SimpleGraph.Walk.length_cons] at hp
      omega
  choose qf hqf using hstep
  let q : V → V := fun v => if hv : A v then v else qf v hv
  have hqe : ∀ v (hv : ¬ A v), q v = qf v hv := fun v hv => by simp [q, hv]
  have hq : ∀ v (hv : ¬ A v), G.Adj v (q v) ∧ Nat.find (hP (q v)) + 1 = Nat.find (hP v) := by
    intro v hv
    rw [hqe v hv]
    exact hqf v hv
  have hidx : ∀ v, ¬ A v → ∃ i, ∃ hi : i < E.length, E[i] = (v, q v) ∨ E[i] = (q v, v) := by
    intro v hv
    have hadj := (hq v hv).1
    rw [hG, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hm | hm
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
      exact ⟨i, hi, Or.inl he⟩
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
      exact ⟨i, hi, Or.inr he⟩
  choose ιf hιf using hidx
  let ι : V → ℕ := fun v => if hv : A v then 0 else ιf v hv
  have hιe : ∀ v (hv : ¬ A v), ι v = ιf v hv := fun v hv => by simp [ι, hv]
  refine ⟨q, fun v => Nat.find (hP v), ι, ⟨fun v hv => ⟨?_, by simp [q, hv]⟩,
    fun v hv => (hq v hv).2, fun v hv => ?_⟩⟩
  · exact (Nat.find_eq_zero (hP v)).2 ⟨v, hv, SimpleGraph.Walk.nil, rfl⟩
  · obtain ⟨hi, he⟩ := hιf v hv
    rw [hιe v hv]
    exact ⟨hi, he⟩


private theorem PD.cross_idx' (P : PD E A q h ι) {U : V → Prop} {u : V} (hA : ¬ A u)
    (hu : (U u ∧ ¬ U (q u)) ∨ (¬ U u ∧ U (q u))) : ∃ hi : ι u < E.length, Cross E[ι u] U := by
  obtain ⟨hi, he⟩ := P.idx u hA
  refine ⟨hi, ?_⟩
  rcases he with he | he <;> rw [he] <;> rcases hu with hu | hu <;> simp [Cross, hu]

private theorem PD.iter_anch (P : PD E A q h ι) {a : V} (ha : A a) : ∀ m, q^[m] a = a := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, (P.anch a ha).2]

private theorem PD.not_anch_iter (P : PD E A q h ι) (v : V) {j : ℕ} (hj : j < h v) :
    ¬ A (q^[j] v) := fun hA => by
  have h1 := P.iter v j hj.le
  have h2 := (P.zero_iff _).2 hA
  omega

private theorem mem_eraseIdx_of_ne {β : Type*} (l : List β) {i k : ℕ} (hi : i < l.length)
    (hik : i ≠ k) : l[i] ∈ l.eraseIdx k :=
  List.mem_eraseIdx_iff_getElem.2 ⟨i, hi, hik, rfl⟩

/-- After removing the edge `w — q w` from the path of `Y` to the root, every set of vertices
avoiding the roots and `Y` is left by an edge. -/
private theorem PD.anch_erase (P : PD E A q h ι) (Y : V) {k : ℕ} (hk : k < h Y)
    (U : V → Prop) (hU : ∃ u, U u) (hUA : ∀ u, U u → ¬ A u ∧ u ≠ Y) :
    ∃ e ∈ E.eraseIdx (ι (q^[k] Y)), Cross e U := by
  classical
  obtain ⟨u, hu, hqu, -⟩ := P.exists_min U hU (fun u hu => (hUA u hu).1)
  have hwA : ¬ A (q^[k] Y) := P.not_anch_iter Y hk
  by_cases huw : u = q^[k] Y
  · have hex : ∃ m, U (q^[m] Y) := ⟨k, huw ▸ hu⟩
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      exact (hUA Y this).2 rfl
    have hmk : Nat.find hex ≤ k := Nat.find_min' hex (huw ▸ hu)
    set m := Nat.find hex - 1 with hm
    have hm1 : m + 1 = Nat.find hex := by omega
    have hy1 : ¬ U (q^[m] Y) := Nat.find_min hex (by omega)
    have hy2 : U (q (q^[m] Y)) := by
      rw [← Function.iterate_succ_apply' q m Y, Nat.succ_eq_add_one, hm1]
      exact Nat.find_spec hex
    have hyA : ¬ A (q^[m] Y) := P.not_anch_iter Y (by omega)
    have hyw : q^[m] Y ≠ q^[k] Y := fun he => hy1 (he ▸ huw ▸ hu)
    have hne : ι (q^[m] Y) ≠ ι (q^[k] Y) := fun he => hyw (P.inj hyA hwA he)
    obtain ⟨hi, hc⟩ := P.cross_idx' hyA (U := U) (Or.inr ⟨hy1, hy2⟩)
    exact ⟨_, mem_eraseIdx_of_ne E hi hne, hc⟩
  · have huA := (hUA u hu).1
    have hne : ι u ≠ ι (q^[k] Y) := fun he => huw (P.inj huA hwA he)
    obtain ⟨hi, hc⟩ := P.cross_idx' huA (U := U) (Or.inl ⟨hu, hqu⟩)
    exact ⟨_, mem_eraseIdx_of_ne E hi hne, hc⟩

/-- After removing the edge `w — q w`, no remaining edge leaves the subtree of `w`, when every
edge is a parent edge. -/
private theorem PD.sep_erase (P : PD E A q h ι)
    (hsurj : ∀ i, i < E.length → ∃ u, ¬ A u ∧ ι u = i) (w : V) (hw : ¬ A w) :
    (∀ v, (∃ m, q^[m] v = w) → ¬ A v) ∧
      ∀ e ∈ E.eraseIdx (ι w), ¬ Cross e (fun v => ∃ m, q^[m] v = w) := by
  refine ⟨fun v ⟨m, hm⟩ hA => hw (by rw [← hm, P.iter_anch hA]; exact hA), fun e he => ?_⟩
  obtain ⟨i, hi, hiw, rfl⟩ := List.mem_eraseIdx_iff_getElem.1 he
  obtain ⟨u, huA, rfl⟩ := hsurj i hi
  have huw : u ≠ w := fun h' => hiw (h' ▸ rfl)
  have key : (∃ m, q^[m] u = w) ↔ (∃ m, q^[m] (q u) = w) := by
    constructor
    · rintro ⟨m, hm⟩
      cases m with
      | zero => exact absurd hm huw
      | succ m => exact ⟨m, by rwa [← Function.iterate_succ_apply]⟩
    · rintro ⟨m, hm⟩
      exact ⟨m + 1, by rwa [Function.iterate_succ_apply]⟩
  obtain ⟨hi', he'⟩ := P.idx u huA
  rcases he' with he' | he' <;> simp only [he', Cross] <;> tauto

/-- Walking up the parents from `v` for `m` steps uses no removed edge. -/
private theorem PD.reach_iter (P : PD E A q h ι) (f : ℕ) (v : V) :
    ∀ m, (∀ j < m, ¬ A (q^[j] v) ∧ ι (q^[j] v) ≠ f) →
      (SimpleGraph.fromRel fun a b => (a, b) ∈ E.eraseIdx f).Reachable v (q^[m] v) := by
  intro m
  induction m with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    intro hm
    refine (ih fun j hj => hm j (by omega)).trans ?_
    rw [Function.iterate_succ_apply']
    obtain ⟨hA, hf⟩ := hm m (by omega)
    obtain ⟨hi, he⟩ := P.idx _ hA
    have hmem := mem_eraseIdx_of_ne E hi hf
    refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromRel_adj]
    refine ⟨(P.q_ne hA).symm, ?_⟩
    rcases he with he | he <;> rw [he] at hmem
    · exact Or.inl hmem
    · exact Or.inr hmem

private theorem PD.surj [Fintype V] {X : V} (P : PD E (· = X) q h ι)
    (hcard : E.length + 1 = Fintype.card V) :
    ∀ i, i < E.length → ∃ u, ¬ u = X ∧ ι u = i := by
  classical
  let f : {u // u ≠ X} → Fin E.length := fun u => ⟨ι u, (P.idx u u.2).1⟩
  have hf : Function.Injective f := fun u u' he =>
    Subtype.ext (P.inj u.2 u'.2 (congrArg Fin.val he))
  have hc : Fintype.card {u // u ≠ X} = Fintype.card (Fin E.length) := by
    rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  have hb := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hc⟩
  intro i hi
  obtain ⟨u, hu⟩ := hb.2 ⟨i, hi⟩
  exact ⟨u, u.2, congrArg Fin.val hu⟩

end Graphs

section Geometry
variable {d L W : ℕ} [NeZero L]

private theorem zd_comm (x y : Zd d L) : zdistInf d L (x - y) = zdistInf d L (y - x) := by
  rw [← zdistInf_neg d L (x - y), neg_sub]

private theorem zd_tri (x y z : Zd d L) :
    zdistInf d L (x - z) ≤ zdistInf d L (x - y) + zdistInf d L (y - z) := by
  have := zdistInf_add_le d L (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

omit [NeZero L] in
private theorem brk_pos (hW : 1 ≤ W) (x y : Zd d L) : 0 < brk d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold brk; positivity

omit [NeZero L] in
private theorem W_le_brk (x y : Zd d L) : (W : ℝ) ≤ brk d L W x y := by
  unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (x - y))]

private theorem brk_comm (x y : Zd d L) : brk d L W x y = brk d L W y x := by
  unfold brk; rw [zd_comm]

omit [NeZero L] in
private theorem bB_eq_brk (x y : Zd d L) :
    bB d L W x y = (W : ℝ) ^ (-2 : ℝ) * brk d L W x y ^ (-((d : ℝ) - 2)) := by
  unfold bB brk; congr 2; ring

private theorem bB_comm' (x y : Zd d L) : bB d L W x y = bB d L W y x := by
  unfold bB; rw [zd_comm]

omit [NeZero L] in
private theorem bB_nonneg' (x y : Zd d L) : 0 ≤ bB d L W x y := by
  unfold bB; positivity

omit [NeZero L] in
private theorem bB_pos' (hW : 1 ≤ W) (x y : Zd d L) : 0 < bB d L W x y := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold bB; positivity

omit [NeZero L] in
private theorem bB_self (x y : Zd d L) : bB d L W x x = bB d L W y y := by
  unfold bB; simp

omit [NeZero L] in
private theorem bB_le_one (hd : 2 ≤ d) (hW : 1 ≤ W) (x y : Zd d L) : bB d L W x y ≤ 1 := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : (1 : ℝ) ≤ brk d L W x y := hW1.trans (W_le_brk x y)
  rw [bB_eq_brk]
  have h1 : (W : ℝ) ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  have h2 : brk d L W x y ^ (-((d : ℝ) - 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

omit [NeZero L] in
/-- If `⟨x' - y'⟩ ≤ 2 ⟨x - y⟩` then `B_{xy} ≤ 2^{d-2} B_{x'y'}`, for `d ≥ 2`. -/
private theorem bB_le_of_brk (hd : 2 ≤ d) (hW : 1 ≤ W) {x y x' y' : Zd d L}
    (h : brk d L W x' y' ≤ 2 * brk d L W x y) :
    bB d L W x y ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * bB d L W x' y' := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 := brk_pos hW x y
  have h0' := brk_pos hW x' y'
  rw [bB_eq_brk, bB_eq_brk]
  have h1 : brk d L W x y ^ (-((d : ℝ) - 2)) ≤ (brk d L W x' y' / 2) ^ (-((d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : (brk d L W x' y' / 2) ^ (-((d : ℝ) - 2)) =
      (2 : ℝ) ^ ((d : ℝ) - 2) * brk d L W x' y' ^ (-((d : ℝ) - 2)) := by
    rw [Real.div_rpow h0'.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  rw [h2] at h1
  calc _ ≤ (W : ℝ) ^ (-2 : ℝ) * ((2 : ℝ) ^ ((d : ℝ) - 2) * brk d L W x' y' ^ (-((d : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- Moving an edge `z — w` to the point `u` nearest to `z`: `B_{zw} ≤ 2^{d-2} B_{uw}`. -/
private theorem bB_rehang (hd : 2 ≤ d) (hW : 1 ≤ W) {z u w : Zd d L}
    (h : zdistInf d L (z - u) ≤ zdistInf d L (z - w)) :
    bB d L W z w ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * bB d L W u w := by
  refine bB_le_of_brk hd hW ?_
  have h1 := zd_tri u z w
  rw [zd_comm u z] at h1
  have h2 : (zdistInf d L (u - w) : ℝ) ≤ 2 * zdistInf d L (z - w) := by exact_mod_cast (by omega)
  have : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  unfold brk; linarith

/-- An edge from `z ∈ box(x₀, K)` to a point `u` outside `box(x₀, 2K)`: `B_{zu} ≤ 2^{d-2}
B_{x₀u}`. -/
private theorem bB_far (hd : 2 ≤ d) (hW : 1 ≤ W) {z u x₀ : Zd d L} {K : ℕ}
    (hz : zdistInf d L (z - x₀) ≤ K) (hu : ¬ zdistInf d L (u - x₀) ≤ 2 * K) :
    bB d L W z u ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * bB d L W x₀ u := by
  refine bB_le_of_brk hd hW ?_
  have h1 := zd_tri u z x₀
  rw [zd_comm u z] at h1
  rw [zd_comm u x₀] at hu h1
  have h2 : (zdistInf d L (x₀ - u) : ℝ) ≤ 2 * zdistInf d L (z - u) := by
    exact_mod_cast (by omega)
  have : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  unfold brk; linarith

end Geometry

section Elim
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge `e` meets `v` in exactly one endpoint. -/
private def Inc (v : V) (e : V × V) : Prop := (e.1 = v ∧ e.2 ≠ v) ∨ (e.2 = v ∧ e.1 ≠ v)

private instance (v : V) (e : V × V) : Decidable (Inc v e) := by unfold Inc; infer_instance

/-- The endpoint of `e` other than `v`. -/
private def oth (v : V) (e : V × V) : V := if e.1 = v then e.2 else e.1

/-- The vertex `a` with `v` replaced by `u`. -/
private def sub (v u a : V) : V := if a = v then u else a

/-- The edges `E` without the edge `i`, with `v` replaced by the other endpoint of the edge `i`. -/
private def rehang (E : List (V × V)) (v : V) (i : Fin E.length) : List (V × V) :=
  (E.eraseIdx i).map fun e => (sub v (oth v E[i]) e.1, sub v (oth v E[i]) e.2)

/-- The edges `E` with `v` replaced by `O`. -/
private def moveTo (E : List (V × V)) (v O : V) : List (V × V) :=
  E.map fun e => (sub v O e.1, sub v O e.2)

/-- The indices of the edges meeting `v` in exactly one endpoint. -/
private def incI (E : List (V × V)) (v : V) : Finset (Fin E.length) :=
  Finset.univ.filter fun i => Inc v E[i]

omit [Fintype V] in
private theorem inc_oth {v : V} {e : V × V} (h : Inc v e) :
    oth v e ≠ v ∧ (e = (v, oth v e) ∨ e = (oth v e, v)) := by
  obtain ⟨a, b⟩ := e
  unfold Inc at h
  unfold oth
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

omit [Fintype V] in
private theorem sub_ne {v u a : V} (h : a ≠ v) : sub v u a = a := by simp [sub, h]

omit [Fintype V] in
private theorem sub_self' (v u : V) : sub v u v = u := by simp [sub]

omit [Fintype V] [DecidableEq V] in
private theorem cross_sub (σ : V → V) (U' U : V → Prop) (h : ∀ a, U' (σ a) ↔ U a)
    (e : V × V) : Cross (σ e.1, σ e.2) U' ↔ Cross e U := by
  simp only [Cross, h]

omit [Fintype V] in
private theorem length_rehang (E : List (V × V)) (v : V) (i : Fin E.length) :
    (rehang E v i).length ≤ E.length := by
  unfold rehang
  rw [List.length_map]
  exact List.length_eraseIdx_le _ _

omit [Fintype V] in
private theorem mem_rehang {E : List (V × V)} {v : V} {i : Fin E.length} {e : V × V}
    (he : e ∈ E) (hne : ∀ j : Fin E.length, E[j] = e → j ≠ i) :
    (sub v (oth v E[i]) e.1, sub v (oth v E[i]) e.2) ∈ rehang E v i := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
  exact List.mem_map.2 ⟨E[j], mem_eraseIdx_of_ne E hj
    (fun h' => hne ⟨j, hj⟩ rfl (Fin.ext h')), rfl⟩

variable (d L W : ℕ) [NeZero L]

/-- The product of `B` over the edges `E` at the positions `g`. -/
private def bProd (E : List (V × V)) (g : V → Zd d L) : ℝ :=
  (E.map fun e => bB d L W (g e.1) (g e.2)).prod

/-- The indicator of the box of the box vertex, centred at the position of `O`. -/
private def boxF (O : V) (bx : Option (V × ℕ)) (g : V → Zd d L) : ℝ :=
  match bx with
  | none => 1
  | some p => if zdistInf d L (g p.1 - g O) ≤ p.2 then 1 else 0

/-- The summand of an elimination state. -/
private def stF (β : V → (V → Zd d L) → ℝ) (O : V) (S : Finset V) (E : List (V × V))
    (bx : Option (V × ℕ)) (g : V → Zd d L) : ℝ :=
  bProd d L W E g * (∏ v ∈ S, β v g) * boxF d L O bx g

variable {d L W}

omit [Fintype V] [DecidableEq V] [NeZero L] in
private theorem bProd_nonneg (E : List (V × V)) (g : V → Zd d L) : 0 ≤ bProd d L W E g :=
  prod_map_nonneg _ _ fun _ _ => bB_nonneg' _ _

omit [Fintype V] [DecidableEq V] [NeZero L] in
private theorem bProd_le_one (hd : 2 ≤ d) (hW : 1 ≤ W) (E : List (V × V)) (g : V → Zd d L) :
    bProd d L W E g ≤ 1 :=
  prod_map_le_one _ _ (fun _ _ => bB_nonneg' _ _) fun _ _ => bB_le_one hd hW _ _

omit [Fintype V] [DecidableEq V] [NeZero L] in
private theorem boxF_nonneg (O : V) (bx : Option (V × ℕ)) (g : V → Zd d L) :
    0 ≤ boxF d L O bx g := by
  unfold boxF; split
  · exact zero_le_one
  · split_ifs <;> norm_num

omit [Fintype V] in
/-- Moving all edges at `v` to the nearest neighbour of the position `z` of `v`. -/
private theorem bProd_rehang (hd : 2 ≤ d) (hW : 1 ≤ W) (E : List (V × V)) (v : V)
    (hI : (incI E v).Nonempty) (g : V → Zd d L) (z : Zd d L) :
    bProd d L W E (Function.update g v z) ≤ ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ E.length *
      ∑ i ∈ incI E v, bB d L W z (g (oth v E[i])) * bProd d L W (rehang E v i) g := by
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hc
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) (by linarith)
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (incI E v)
    (fun i => zdistInf d L (z - g (oth v E[i]))) hI
  have hinc : Inc v E[i] := (Finset.mem_filter.1 hi).2
  obtain ⟨hu, hcase⟩ := inc_oth hinc
  set u := oth v E[i] with hudef
  set g' := Function.update g v z with hg'
  have hgu : g' u = g u := Function.update_of_ne hu _ _
  have hgv : g' v = z := Function.update_self _ _ _
  have hfirst : bB d L W (g' E[i].1) (g' E[i].2) = bB d L W z (g u) := by
    rcases hcase with h | h <;> rw [h] <;> simp only [hgu, hgv]
    exact bB_comm' _ _
  have hrest : ((E.eraseIdx i).map fun e => bB d L W (g' e.1) (g' e.2)).prod ≤
      c ^ (E.eraseIdx i).length * bProd d L W (rehang E v i) g := by
    unfold bProd rehang
    rw [List.map_map]
    refine prod_map_le_pow _ _ _ c (by linarith) fun e he => ⟨bB_nonneg' _ _, bB_nonneg' _ _, ?_⟩
    have heE : e ∈ E := List.mem_of_mem_eraseIdx he
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 heE
    simp only [Function.comp]
    by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v
    · rw [h1, h2, sub_self', hgv]
      calc bB d L W z z = bB d L W (g u) (g u) := bB_self _ _
        _ ≤ c * bB d L W (g u) (g u) := le_mul_of_one_le_left (bB_nonneg' _ _) hc1
    · have hjI : (⟨j, hj⟩ : Fin E.length) ∈ incI E v := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        change Inc v E[j]
        rw [hje]; exact Or.inl ⟨h1, h2⟩
      have hm := hmin _ hjI
      have hoth : oth v E[(⟨j, hj⟩ : Fin E.length)] = e.2 := by
        change oth v E[j] = e.2
        rw [hje]; simp [oth, h1]
      rw [hoth] at hm
      rw [h1, sub_self', sub_ne h2, hgv, (show g' e.2 = g e.2 from Function.update_of_ne h2 _ _)]
      exact bB_rehang hd hW hm
    · have hjI : (⟨j, hj⟩ : Fin E.length) ∈ incI E v := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        change Inc v E[j]
        rw [hje]; exact Or.inr ⟨h2, h1⟩
      have hm := hmin _ hjI
      have hoth : oth v E[(⟨j, hj⟩ : Fin E.length)] = e.1 := by
        change oth v E[j] = e.1
        rw [hje]; simp [oth, h1]
      rw [hoth] at hm
      rw [h2, sub_self', sub_ne h1, hgv, (show g' e.1 = g e.1 from Function.update_of_ne h1 _ _),
      bB_comm' (g e.1),
        bB_comm' (g e.1)]
      exact bB_rehang hd hW hm
    · rw [sub_ne h1, sub_ne h2, (show g' e.1 = g e.1 from Function.update_of_ne h1 _ _),
      (show g' e.2 = g e.2 from Function.update_of_ne h2 _ _)]
      exact le_mul_of_one_le_left (bB_nonneg' _ _) hc1
  have hlen : (E.eraseIdx i).length ≤ E.length := List.length_eraseIdx_le _ _
  have hpow : c ^ (E.eraseIdx i).length ≤ c ^ E.length := pow_le_pow_right₀ hc1 hlen
  have hterm : ∀ j ∈ incI E v,
      0 ≤ bB d L W z (g (oth v E[j])) * bProd d L W (rehang E v j) g :=
    fun j _ => mul_nonneg (bB_nonneg' _ _) (bProd_nonneg _ _)
  calc bProd d L W E g' = bB d L W z (g u) *
        ((E.eraseIdx i).map fun e => bB d L W (g' e.1) (g' e.2)).prod := by
        unfold bProd
        rw [prod_map_eraseIdx _ _ i i.2]
        exact congrArg (· * _) hfirst
    _ ≤ bB d L W z (g u) * (c ^ E.length * bProd d L W (rehang E v i) g) := by
        refine mul_le_mul_of_nonneg_left (hrest.trans ?_) (bB_nonneg' _ _)
        exact mul_le_mul_of_nonneg_right hpow (bProd_nonneg _ _)
    _ = c ^ E.length * (bB d L W z (g u) * bProd d L W (rehang E v i) g) := by ring
    _ ≤ c ^ E.length * ∑ j ∈ incI E v, bB d L W z (g (oth v E[j])) *
          bProd d L W (rehang E v j) g :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum hterm hi) (by positivity)

omit [Fintype V] in
/-- Moving all edges at `v`, with position `z ∈ box(x₀, K)`, to `O` at `x₀`, when all neighbours
of `v` lie outside `box(x₀, 2K)`. -/
private theorem bProd_far (hd : 2 ≤ d) (hW : 1 ≤ W) (E : List (V × V)) (v O : V)
    (g : V → Zd d L) (z : Zd d L) (K : ℕ) (hz : zdistInf d L (z - g O) ≤ K)
    (hfar : ∀ i ∈ incI E v, ¬ zdistInf d L (g (oth v E[i]) - g O) ≤ 2 * K) :
    bProd d L W E (Function.update g v z) ≤ ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ E.length *
      bProd d L W (moveTo E v O) g := by
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hc
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) (by linarith)
  set g' := Function.update g v z with hg'
  have hgv : g' v = z := Function.update_self _ _ _
  unfold bProd moveTo
  rw [List.map_map]
  refine prod_map_le_pow _ _ _ c (by linarith) fun e he => ⟨bB_nonneg' _ _, bB_nonneg' _ _, ?_⟩
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 he
  simp only [Function.comp]
  by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v
  · rw [h1, h2, sub_self', hgv]
    calc bB d L W z z = bB d L W (g O) (g O) := bB_self _ _
      _ ≤ c * bB d L W (g O) (g O) := le_mul_of_one_le_left (bB_nonneg' _ _) hc1
  · have hjI : (⟨j, hj⟩ : Fin E.length) ∈ incI E v := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change Inc v E[j]
      rw [hje]; exact Or.inl ⟨h1, h2⟩
    have hm := hfar _ hjI
    have hoth : oth v E[(⟨j, hj⟩ : Fin E.length)] = e.2 := by
      change oth v E[j] = e.2
      rw [hje]; simp [oth, h1]
    rw [hoth] at hm
    rw [h1, sub_self', sub_ne h2, hgv, (show g' e.2 = g e.2 from Function.update_of_ne h2 _ _)]
    exact bB_far hd hW hz hm
  · have hjI : (⟨j, hj⟩ : Fin E.length) ∈ incI E v := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change Inc v E[j]
      rw [hje]; exact Or.inr ⟨h2, h1⟩
    have hm := hfar _ hjI
    have hoth : oth v E[(⟨j, hj⟩ : Fin E.length)] = e.1 := by
      change oth v E[j] = e.1
      rw [hje]; simp [oth, h1]
    rw [hoth] at hm
    rw [h2, sub_self', sub_ne h1, hgv, (show g' e.1 = g e.1 from Function.update_of_ne h1 _ _),
      bB_comm' (g e.1),
      bB_comm' (g e.1)]
    exact bB_far hd hW hz hm
  · rw [sub_ne h1, sub_ne h2, (show g' e.1 = g e.1 from Function.update_of_ne h1 _ _),
      (show g' e.2 = g e.2 from Function.update_of_ne h2 _ _)]
    exact le_mul_of_one_le_left (bB_nonneg' _ _) hc1

end Elim

section Inv
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertex `u` is not yet summed: fixed, or still to be summed. -/
private def InR (S₀ S : Finset V) (u : V) : Prop := u ∉ S₀ ∨ u ∈ S

/-- The invariant of an elimination state: the edges join unsummed vertices; every set of
unsummed vertices avoiding the anchors `A` and the box vertex is left by an edge; the box vertex
is unsummed, its radius lies in `[K₀, 2^j K₀]` after `j` steps, and its component consists of
vertices to be summed. -/
private structure Inv (S₀ : Finset V) (A : V → Prop) (L K₀ : ℕ) (S : Finset V)
    (E : List (V × V)) (bx : Option (V × ℕ)) : Prop where
  edges : ∀ e ∈ E, InR S₀ S e.1 ∧ InR S₀ S e.2
  anch : ∀ U : V → Prop, (∃ u, U u) →
    (∀ u, U u → InR S₀ S u ∧ ¬ A u ∧ ∀ K, bx ≠ some (u, K)) → ∃ e ∈ E, Cross e U
  box : ∀ z K, bx = some (z, K) → z ∈ S ∧ K₀ ≤ K ∧ K ≤ 2 ^ (S₀.card - S.card) * K₀ ∧
    2 * K ≤ L ∧ ∃ U : V → Prop, U z ∧ (∀ u, U u → u ∈ S) ∧ ∀ e ∈ E, ¬ Cross e U

omit [Fintype V] in
private theorem inR_erase {S₀ S : Finset V} {v u : V} (h : InR S₀ S u) (hu : u ≠ v) :
    InR S₀ (S.erase v) u := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_erase.2 ⟨hu, h⟩)

omit [Fintype V] in
private theorem inR_of_erase {S₀ S : Finset V} {v u : V} (h : InR S₀ (S.erase v) u) :
    InR S₀ S u := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_of_mem_erase h)

omit [Fintype V] in
private theorem not_inR_erase {S₀ S : Finset V} {v : V} (hv : v ∈ S₀) :
    ¬ InR S₀ (S.erase v) v := by
  rintro (h | h)
  · exact h hv
  · exact (Finset.notMem_erase v S) h

omit [Fintype V] in
/-- Membership after replacing `v` by `u` and removing `v`, when `U` does not separate `v`
from `u`. -/
private theorem sub_mem_iff {U : V → Prop} {v u : V} (huv : U v ↔ U u) (hu : u ≠ v) (a : V) :
    (U (sub v u a) ∧ sub v u a ≠ v) ↔ U a := by
  by_cases ha : a = v
  · subst ha; rw [sub_self']; exact ⟨fun h => huv.2 h.1, fun h => ⟨huv.1 h, hu⟩⟩
  · rw [sub_ne ha]; exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem edge_uncross {U : V → Prop} {v u : V} {e : V × V}
    (he : e = (v, u) ∨ e = (u, v)) (hc : ¬ Cross e U) : U v ↔ U u := by
  rcases he with rfl | rfl <;> simp only [Cross, not_or, not_and, not_not] at hc <;> tauto

omit [Fintype V] [DecidableEq V] in
private theorem getElem_mem_E {E : List (V × V)} (i : Fin E.length) : E[i] ∈ E :=
  List.getElem_mem _

omit [Fintype V] in
/-- The invariant after summing a vertex `v` that is not the box vertex. -/
private theorem inv_rehang {S₀ : Finset V} {A : V → Prop} {L K₀ : ℕ} {S : Finset V}
    {E : List (V × V)} {bx : Option (V × ℕ)} (I : Inv S₀ A L K₀ S E bx) {v : V} (hvS : v ∈ S)
    (hvS₀ : v ∈ S₀) (hvA : ¬ A v) (hvb : ∀ K, bx ≠ some (v, K)) {i : Fin E.length}
    (hi : i ∈ incI E v) : Inv S₀ A L K₀ (S.erase v) (rehang E v i) bx := by
  have hinc : Inc v E[i] := (Finset.mem_filter.1 hi).2
  obtain ⟨hu, hcase⟩ := inc_oth hinc
  set u := oth v E[i] with hudef
  have huR : InR S₀ S u := by
    rcases hcase with h | h
    · have := (I.edges _ (getElem_mem_E i)).2; rw [h] at this; exact this
    · have := (I.edges _ (getElem_mem_E i)).1; rw [h] at this; exact this
  refine ⟨fun e' he' => ?_, fun U' hU' hUA => ?_, fun z K hz => ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    have heE := I.edges e (List.mem_of_mem_eraseIdx he)
    constructor
    · by_cases h1 : e.1 = v
      · simp only [h1, sub_self']; exact inR_erase huR hu
      · simp only [sub_ne h1]; exact inR_erase heE.1 h1
    · by_cases h2 : e.2 = v
      · simp only [h2, sub_self']; exact inR_erase huR hu
      · simp only [sub_ne h2]; exact inR_erase heE.2 h2
  · have hnv : ¬ U' v := fun h => not_inR_erase hvS₀ (hUA v h).1
    set U₁ : V → Prop := fun a => U' a ∨ (a = v ∧ U' u) with hU₁
    have h1 : ∀ a, U' (sub v u a) ↔ U₁ a := by
      intro a
      by_cases ha : a = v
      · subst ha; rw [sub_self']; simp [hU₁, hnv]
      · rw [sub_ne ha]; simp [hU₁, ha]
    obtain ⟨w, hw⟩ := hU'
    obtain ⟨e, he, hc⟩ := I.anch U₁ ⟨w, Or.inl hw⟩ (by
      rintro a (ha | ⟨rfl, -⟩)
      · exact ⟨inR_of_erase (hUA a ha).1, (hUA a ha).2.1, (hUA a ha).2.2⟩
      · exact ⟨Or.inr hvS, hvA, hvb⟩)
    have hU1vu : U₁ v ↔ U₁ u := by simp [hU₁, hnv, hu]
    have hne : ∀ j : Fin E.length, E[j] = e → j ≠ i := by
      rintro j rfl rfl
      rcases hcase with h | h <;> rw [h] at hc <;> simp only [Cross] at hc <;> tauto
    exact ⟨_, mem_rehang he hne, (cross_sub (sub v u) U' U₁ h1 e).2 hc⟩
  · obtain ⟨hzS, hK1, hK2, hK3, U, hUz, hUS, hUc⟩ := I.box z K hz
    have hzv : z ≠ v := fun h => hvb K (h ▸ hz)
    have huv : U v ↔ U u := edge_uncross hcase (hUc _ (getElem_mem_E i))
    have hcard : S₀.card - S.card ≤ S₀.card - (S.erase v).card := by
      rw [Finset.card_erase_of_mem hvS]; omega
    refine ⟨Finset.mem_erase.2 ⟨hzv, hzS⟩, hK1,
      hK2.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hcard)), hK3,
      fun a => U a ∧ a ≠ v, ⟨hUz, hzv⟩,
      fun a ha => Finset.mem_erase.2 ⟨ha.2, hUS a ha.1⟩, fun e' he' hc => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact hUc e (List.mem_of_mem_eraseIdx he)
      ((cross_sub (sub v u) (fun a => U a ∧ a ≠ v) U (sub_mem_iff huv hu) e).1 hc)

omit [Fintype V] in
/-- The invariant after summing the box vertex `v` over its box, its edges moved to `O`. -/
private theorem inv_far {S₀ : Finset V} {A : V → Prop} {L K₀ : ℕ} {S : Finset V}
    {E : List (V × V)} {v O : V} {K : ℕ} (I : Inv S₀ A L K₀ S E (some (v, K)))
    (hvS₀ : v ∈ S₀) (hO : A O) (hOS : O ∉ S₀) :
    Inv S₀ A L K₀ (S.erase v) (moveTo E v O) none := by
  refine ⟨fun e' he' => ?_, fun U' hU' hUA => ?_, fun z K' hz => by simp at hz⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    have heE := I.edges e he
    constructor
    · by_cases h1 : e.1 = v
      · simp only [h1, sub_self']; exact Or.inl hOS
      · simp only [sub_ne h1]; exact inR_erase heE.1 h1
    · by_cases h2 : e.2 = v
      · simp only [h2, sub_self']; exact Or.inl hOS
      · simp only [sub_ne h2]; exact inR_erase heE.2 h2
  · have hnv : ¬ U' v := fun h => not_inR_erase hvS₀ (hUA v h).1
    have hnO : ¬ U' O := fun h => (hUA O h).2.1 hO
    have h1 : ∀ a, U' (sub v O a) ↔ U' a := by
      intro a
      by_cases ha : a = v
      · subst ha; rw [sub_self']; simp [hnv, hnO]
      · rw [sub_ne ha]
    obtain ⟨e, he, hc⟩ := I.anch U' hU' (fun a ha => ⟨inR_of_erase (hUA a ha).1,
      (hUA a ha).2.1, fun K' h => hnv (by
        rw [show v = a from congrArg Prod.fst (Option.some.inj h)]; exact ha)⟩)
    exact ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, (cross_sub (sub v O) U' U' h1 e).2 hc⟩

omit [Fintype V] in
/-- The invariant after summing the box vertex `v` over the torus, the box passing to its
neighbour `oth v E[n]` with radius `min (2K) (L/2)`. -/
private theorem inv_near {S₀ : Finset V} {A : V → Prop} {L K₀ : ℕ} {S : Finset V}
    {E : List (V × V)} {v : V} {K : ℕ} (I : Inv S₀ A L K₀ S E (some (v, K)))
    (hSS₀ : S ⊆ S₀) (hvS₀ : v ∈ S₀) {n r : Fin E.length} (hn : n ∈ incI E v) (hr : r ∈ incI E v) :
    Inv S₀ A L K₀ (S.erase v) (rehang E v r) (some (oth v E[n], min (2 * K) (L / 2))) := by
  obtain ⟨hvS, hK1, hK2, hK3, Us, hUsv, hUsS, hUsc⟩ := I.box v K rfl
  obtain ⟨hun, hcn⟩ := inc_oth (Finset.mem_filter.1 hn).2
  obtain ⟨hur, hcr⟩ := inc_oth (Finset.mem_filter.1 hr).2
  set un := oth v E[n] with hundef
  set ur := oth v E[r] with hurdef
  have hUsn : Us un := (edge_uncross hcn (hUsc _ (getElem_mem_E n))).1 hUsv
  have hUsr : Us ur := (edge_uncross hcr (hUsc _ (getElem_mem_E r))).1 hUsv
  have hurR : InR S₀ S ur := Or.inr (hUsS ur hUsr)
  refine ⟨fun e' he' => ?_, fun U' hU' hUA => ?_, fun z K' hz => ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    have heE := I.edges e (List.mem_of_mem_eraseIdx he)
    constructor
    · by_cases h1 : e.1 = v
      · simp only [h1, sub_self']; exact inR_erase hurR hur
      · simp only [sub_ne h1]; exact inR_erase heE.1 h1
    · by_cases h2 : e.2 = v
      · simp only [h2, sub_self']; exact inR_erase hurR hur
      · simp only [sub_ne h2]; exact inR_erase heE.2 h2
  · have hnv : ¬ U' v := fun h => not_inR_erase hvS₀ (hUA v h).1
    have hnun : ¬ U' un := fun h => (hUA un h).2.2 _ rfl
    by_cases hU'r : U' ur
    · have hrn : un ≠ ur := fun h => hnun (h ▸ hU'r)
      have hnr : (n : ℕ) ≠ r := fun h => hrn (by rw [hundef, hurdef]; congr 2; exact Fin.ext h)
      have hmem : (sub v ur E[n].1, sub v ur E[n].2) ∈ rehang E v r :=
        List.mem_map.2 ⟨E[n], mem_eraseIdx_of_ne E n.2 hnr, rfl⟩
      refine ⟨_, hmem, ?_⟩
      rcases hcn with h | h <;> rw [h] <;> simp only [sub_self', sub_ne hun, Cross] <;> tauto
    · have h1 : ∀ a, U' (sub v ur a) ↔ U' a := by
        intro a
        by_cases ha : a = v
        · subst ha; rw [sub_self']; simp [hnv, hU'r]
        · rw [sub_ne ha]
      obtain ⟨e, he, hc⟩ := I.anch U' hU' (fun a ha => ⟨inR_of_erase (hUA a ha).1,
        (hUA a ha).2.1, fun K' h => hnv (by
          rw [show v = a from congrArg Prod.fst (Option.some.inj h)]; exact ha)⟩)
      have hne : ∀ j : Fin E.length, E[j] = e → j ≠ r := by
        rintro j rfl rfl
        rcases hcr with h | h <;> rw [h] at hc <;> simp only [Cross] at hc <;> tauto
      exact ⟨_, mem_rehang he hne, (cross_sub (sub v ur) U' U' h1 e).2 hc⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    have hle := Finset.card_le_card hSS₀
    have h0 : 0 < S.card := Finset.card_pos.2 ⟨v, hvS⟩
    have hcard : S₀.card - (S.erase v).card = S₀.card - S.card + 1 := by
      rw [Finset.card_erase_of_mem hvS]; omega
    have huv : Us v ↔ Us ur := ⟨fun _ => hUsr, fun _ => hUsv⟩
    refine ⟨Finset.mem_erase.2 ⟨hun, hUsS un hUsn⟩, le_min (by omega) (by omega), ?_,
      by have := min_le_right (2 * K) (L / 2); omega, fun a => Us a ∧ a ≠ v, ⟨hUsn, hun⟩,
      fun a ha => Finset.mem_erase.2 ⟨ha.2, hUsS a ha.1⟩, fun e' he' hc => ?_⟩
    · rw [hcard, pow_succ]
      calc min (2 * K) (L / 2) ≤ 2 * K := min_le_left _ _
        _ ≤ 2 * (2 ^ (S₀.card - S.card) * K₀) := by omega
        _ = _ := by ring
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      exact hUsc e (List.mem_of_mem_eraseIdx he)
        ((cross_sub (sub v ur) (fun a => Us a ∧ a ≠ v) Us (sub_mem_iff huv hur) e).1 hc)

end Inv

section ElimMain
variable {V : Type*} [Fintype V] [DecidableEq V] {d L W : ℕ} [NeZero L]

/-- The weight of a state with `n` vertices left: `c₁^n` without a box vertex, `c₁^{n-1} cb`
with one. -/
private def wt (c₁ cb : ℝ) (bx : Option (V × ℕ)) (n : ℕ) : ℝ :=
  match bx with
  | none => c₁ ^ n
  | some _ => c₁ ^ (n - 1) * cb

omit [Fintype V] [DecidableEq V] in
private theorem wt_nonneg {c₁ cb : ℝ} (hc₁ : 0 ≤ c₁) (hcb : 0 ≤ cb) (bx : Option (V × ℕ))
    (n : ℕ) : 0 ≤ wt c₁ cb bx n := by
  unfold wt; split <;> positivity

omit [Fintype V] [DecidableEq V] [NeZero L] in
private theorem stF_nonneg {β : V → (V → Zd d L) → ℝ} (hβ0 : ∀ v g, 0 ≤ β v g) (O : V)
    (S : Finset V) (E : List (V × V)) (bx : Option (V × ℕ)) (g : V → Zd d L) :
    0 ≤ stF d L W β O S E bx g :=
  mul_nonneg (mul_nonneg (bProd_nonneg _ _) (Finset.prod_nonneg fun v _ => hβ0 v g))
    (boxF_nonneg _ _ _)

/-- Summing the vertices of `S` one at a time, the one of largest rank first: the sum of the
summand of a state is at most `M^n` times the product of the single-vertex bounds times the bound
`Φ` of the final edges. -/
private theorem elim (hd : 2 ≤ d) (hW : 1 ≤ W) (S₀ : Finset V) (A : V → Prop) (O : V) (hO : A O)
    (hAS : ∀ a, A a → a ∉ S₀) (rk : V → ℕ) (β : V → (V → Zd d L) → ℝ) (hβ0 : ∀ v g, 0 ≤ β v g)
    (hβdep : ∀ w ∈ S₀, ∀ v ∈ S₀, w ≠ v → rk w ≤ rk v →
      ∀ g z, β w (Function.update g v z) = β w g)
    (c₁ cb : ℝ) (hc₁ : 0 ≤ c₁) (hcb : 0 ≤ cb) (K₀ : ℕ)
    (hfull : ∀ v ∈ S₀, ∀ (g : V → Zd d L) (u : Zd d L),
      ∑ z, bB d L W z u * β v (Function.update g v z) ≤ c₁)
    (hbox : ∀ v ∈ S₀, ∀ (g : V → Zd d L) (K : ℕ), K₀ ≤ K → K ≤ 2 ^ S₀.card * K₀ → 2 * K ≤ L →
      ∑ z, (if zdistInf d L (z - g O) ≤ K then (1 : ℝ) else 0) *
        β v (Function.update g v z) ≤ cb)
    (Φ : (V → Zd d L) → ℝ) (hΦ : ∀ g, 0 ≤ Φ g)
    (hfinal : ∀ E, Inv S₀ A L K₀ ∅ E none → ∀ g, bProd d L W E g ≤ Φ g) (m : ℕ) :
    ∀ n, ∀ S ⊆ S₀, S.card = n → ∀ E bx, E.length ≤ m → Inv S₀ A L K₀ S E bx → ∀ ψ,
      sumS S (stF d L W β O S E bx) ψ ≤
        (((m : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ m) ^ n * wt c₁ cb bx n * Φ ψ := by
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hc
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc1 : 1 ≤ c := Real.one_le_rpow (by norm_num) (by linarith)
  have hc0 : 0 ≤ c := by linarith
  set M : ℝ := ((m : ℝ) + 1) ^ 2 * c ^ m with hM
  have hM0 : 0 ≤ M := by positivity
  intro n
  induction n with
  | zero =>
    intro S hS hn E bx hE I ψ
    have hS0 : S = ∅ := Finset.card_eq_zero.1 hn
    subst hS0
    cases bx with
    | some p => exact absurd (I.box p.1 p.2 rfl).1 (Finset.notMem_empty _)
    | none =>
      rw [sumS_empty]
      simp only [stF, boxF, Finset.prod_empty, mul_one, pow_zero, wt, one_mul]
      exact hfinal E I ψ
  | succ n ih =>
    intro S hS hn E bx hE I ψ
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S rk hSne
    have hvS₀ : v ∈ S₀ := hS hvS
    have hvA : ¬ A v := fun h => hAS v h hvS₀
    have hOv : O ≠ v := fun h => hAS O hO (h ▸ hvS₀)
    set S' := S.erase v with hS'
    have hS'card : S'.card = n := by rw [Finset.card_erase_of_mem hvS]; omega
    have hS'S₀ : S' ⊆ S₀ := (Finset.erase_subset v S).trans hS
    have hvS' : v ∉ S' := Finset.notMem_erase v S
    have hSins : S = insert v S' := (Finset.insert_erase hvS).symm
    rw [hSins, sumS_inner hvS']
    have hprod : ∀ g z, ∏ w ∈ insert v S', β w (Function.update g v z) =
        β v (Function.update g v z) * ∏ w ∈ S', β w g := by
      intro g z
      rw [Finset.prod_insert hvS']
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      have hwS := Finset.mem_of_mem_erase hw
      exact hβdep w (hS hwS) v hvS₀ (Finset.ne_of_mem_erase hw) (hvmax w hwS) g z
    have hP0 : ∀ g, 0 ≤ ∏ w ∈ S', β w g := fun g => Finset.prod_nonneg fun w _ => hβ0 w g
    have hIcard : ((incI E v).card : ℝ) ≤ m := by
      have := Finset.card_le_univ (incI E v)
      rw [Fintype.card_fin] at this
      exact_mod_cast this.trans hE
    have hcm : c ^ E.length ≤ c ^ m := pow_le_pow_right₀ hc1 hE
    have hstF0 := stF_nonneg (W := W) hβ0 O
    by_cases hbv : ∃ K, bx = some (v, K)
    · obtain ⟨K, rfl⟩ := hbv
      obtain ⟨-, hK1, hK2, hK3, Us, hUsv, hUsS, hUsc⟩ := I.box v K rfl
      have hK2' : K ≤ 2 ^ S₀.card * K₀ := hK2.trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)))
      have hboxeq : ∀ g z, boxF d L O (some (v, K)) (Function.update g v z) =
          if zdistInf d L (z - g O) ≤ K then 1 else 0 := by
        intro g z
        simp only [boxF, Function.update_self, Function.update_of_ne hOv]
      set K' := min (2 * K) (L / 2) with hK'
      have hnpos : ∀ i ∈ incI E v, 1 ≤ n := by
        intro i hi
        obtain ⟨hu, hcase⟩ := inc_oth (Finset.mem_filter.1 hi).2
        have hUu := (edge_uncross hcase (hUsc _ (getElem_mem_E i))).1 hUsv
        have : oth v E[i] ∈ S' := Finset.mem_erase.2 ⟨hu, hUsS _ hUu⟩
        rw [← hS'card]
        exact Finset.card_pos.2 ⟨_, this⟩
      have hpt : ∀ g, ∑ z, stF d L W β O (insert v S') E (some (v, K)) (Function.update g v z) ≤
          (c ^ m * cb) * stF d L W β O S' (moveTo E v O) none g +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v,
              (c ^ m * c₁) * stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g := by
        intro g
        have h1 : ∀ z, stF d L W β O (insert v S') E (some (v, K)) (Function.update g v z) ≤
            c ^ m * ((if zdistInf d L (z - g O) ≤ K then (1 : ℝ) else 0) *
              β v (Function.update g v z)) * stF d L W β O S' (moveTo E v O) none g +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v, c ^ m *
              (bB d L W z (g (oth v E[r])) * β v (Function.update g v z)) *
              stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g := by
          intro z
          have hβv := hβ0 v (Function.update g v z)
          have hsec : 0 ≤ ∑ i ∈ incI E v, ∑ r ∈ incI E v, c ^ m *
              (bB d L W z (g (oth v E[r])) * β v (Function.update g v z)) *
              stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g :=
            Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun r _ =>
              mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (bB_nonneg' _ _) hβv))
                (hstF0 _ _ _ _)
          simp only [stF]
          rw [hprod g z, hboxeq g z]
          by_cases hfar : ∀ i ∈ incI E v, ¬ zdistInf d L (g (oth v E[i]) - g O) ≤ 2 * K
          · refine le_trans ?_ (le_add_of_nonneg_right hsec)
            by_cases hz : zdistInf d L (z - g O) ≤ K
            · have hf := bProd_far hd hW E v O g z K hz hfar
              simp only [hz, ite_true, boxF, mul_one]
              calc bProd d L W E (Function.update g v z) * (β v (Function.update g v z) *
                    ∏ w ∈ S', β w g)
                  ≤ (c ^ m * bProd d L W (moveTo E v O) g) * (β v (Function.update g v z) *
                    ∏ w ∈ S', β w g) :=
                    mul_le_mul_of_nonneg_right (hf.trans (mul_le_mul_of_nonneg_right hcm
                      (bProd_nonneg _ _))) (mul_nonneg hβv (hP0 g))
                _ = _ := by ring
            · simp only [hz, ite_false, mul_zero, zero_mul, le_refl]
          · push Not at hfar
            obtain ⟨i, hi, hnear⟩ := hfar
            have hI : (incI E v).Nonempty := ⟨i, hi⟩
            have hr := bProd_rehang hd hW E v hI g z
            have hbox1 : boxF d L O (some (oth v E[i], K')) g = 1 := by
              simp only [boxF, show zdistInf d L (g (oth v E[i]) - g O) ≤ K' from
                le_min hnear (zdistInf_le_half d L _), ite_true]
            refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by positivity)
              (mul_nonneg (by split_ifs <;> norm_num) hβv)) (hstF0 _ _ _ _)))
            refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ r ∈ incI E v, c ^ m *
              (bB d L W z (g (oth v E[r])) * β v (Function.update g v z)) *
              stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g)
              (fun i _ => Finset.sum_nonneg fun r _ =>
                mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (bB_nonneg' _ _) hβv))
                  (hstF0 _ _ _ _)) hi)
            simp only [stF, hbox1, mul_one]
            have hind : (if zdistInf d L (z - g O) ≤ K then (1 : ℝ) else 0) ≤ 1 := by
              split_ifs <;> norm_num
            calc bProd d L W E (Function.update g v z) * (β v (Function.update g v z) *
                  ∏ w ∈ S', β w g) * (if zdistInf d L (z - g O) ≤ K then (1 : ℝ) else 0)
                ≤ bProd d L W E (Function.update g v z) * (β v (Function.update g v z) *
                  ∏ w ∈ S', β w g) * 1 :=
                  mul_le_mul_of_nonneg_left hind
                    (mul_nonneg (bProd_nonneg _ _) (mul_nonneg hβv (hP0 g)))
              _ ≤ (c ^ m * ∑ r ∈ incI E v, bB d L W z (g (oth v E[r])) *
                    bProd d L W (rehang E v r) g) * (β v (Function.update g v z) *
                    ∏ w ∈ S', β w g) * 1 := by
                  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (hr.trans (mul_le_mul_of_nonneg_right hcm ?_)) (mul_nonneg hβv (hP0 g)))
                    zero_le_one
                  exact Finset.sum_nonneg fun r _ => mul_nonneg (bB_nonneg' _ _)
                    (bProd_nonneg _ _)
              _ = _ := by
                  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun r _ => ?_
                  ring
        calc ∑ z, stF d L W β O (insert v S') E (some (v, K)) (Function.update g v z)
            ≤ ∑ z, (c ^ m * ((if zdistInf d L (z - g O) ≤ K then (1 : ℝ) else 0) *
              β v (Function.update g v z)) * stF d L W β O S' (moveTo E v O) none g +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v, c ^ m *
              (bB d L W z (g (oth v E[r])) * β v (Function.update g v z)) *
              stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g) :=
              Finset.sum_le_sum fun z _ => h1 z
          _ = c ^ m * (∑ z, (if zdistInf d L (z - g O) ≤ K then (1 : ℝ) else 0) *
              β v (Function.update g v z)) * stF d L W β O S' (moveTo E v O) none g +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v, c ^ m *
              (∑ z, bB d L W z (g (oth v E[r])) * β v (Function.update g v z)) *
              stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g := by
              rw [Finset.sum_add_distrib]
              congr 1
              · rw [Finset.mul_sum, Finset.sum_mul]
              · rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ c ^ m * cb * stF d L W β O S' (moveTo E v O) none g +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v, c ^ m * c₁ *
              stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g := by
              refine add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (hbox v hvS₀ g K hK1 hK2' hK3) (by positivity)) (hstF0 _ _ _ _))
                (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun r _ => ?_)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (hfull v hvS₀ g _) (by positivity)) (hstF0 _ _ _ _)
      calc sumS S' (fun g => ∑ z, stF d L W β O (insert v S') E (some (v, K))
            (Function.update g v z)) ψ
          ≤ sumS S' (fun g => (c ^ m * cb) * stF d L W β O S' (moveTo E v O) none g +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v,
              (c ^ m * c₁) * stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g) ψ :=
            sumS_mono _ hpt ψ
        _ = (c ^ m * cb) * sumS S' (stF d L W β O S' (moveTo E v O) none) ψ +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v,
              (c ^ m * c₁) *
                sumS S' (stF d L W β O S' (rehang E v r) (some (oth v E[i], K'))) ψ := by
            have e1 := sumS_sum S' (Finset.univ : Finset (Fin 2))
              (fun k g => if k = 0 then (c ^ m * cb) * stF d L W β O S' (moveTo E v O) none g
                else ∑ i ∈ incI E v, ∑ r ∈ incI E v,
                  (c ^ m * c₁) * stF d L W β O S' (rehang E v r) (some (oth v E[i], K')) g) ψ
            simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false] at e1
            rw [e1, sumS_mul, sumS_sum]
            refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
            rw [sumS_sum]
            exact Finset.sum_congr rfl fun r _ => sumS_mul _ _ _ _
        _ ≤ (c ^ m * cb) * (M ^ n * wt c₁ cb (none : Option (V × ℕ)) n * Φ ψ) +
            ∑ i ∈ incI E v, ∑ r ∈ incI E v,
              (c ^ m * c₁) * (M ^ n * wt c₁ cb (some (oth v E[i], K')) n * Φ ψ) := by
            refine add_le_add (mul_le_mul_of_nonneg_left (ih S' hS'S₀ hS'card _ _
              ((List.length_map _).le.trans hE) (inv_far I hvS₀ hO (hAS O hO)) ψ) (by positivity))
              (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun r hr =>
                mul_le_mul_of_nonneg_left (ih S' hS'S₀ hS'card _ _
                  ((length_rehang E v r).trans hE) (inv_near I hS hvS₀ hi hr) ψ) (by positivity))
        _ ≤ M ^ (n + 1) * wt c₁ cb (some (v, K)) (n + 1) * Φ ψ := by
            have hterm : ∀ i ∈ incI E v, ∑ r ∈ incI E v,
                (c ^ m * c₁) * (M ^ n * wt c₁ cb (some (oth v E[i], K')) n * Φ ψ) =
                (incI E v).card * (c ^ m * (M ^ n * (c₁ ^ n * cb) * Φ ψ)) := by
              intro i hi
              rw [Finset.sum_const, nsmul_eq_mul]
              have h1 := hnpos i hi
              simp only [wt]
              have : c₁ * c₁ ^ (n - 1) = c₁ ^ n := by
                rw [← pow_succ']; congr 1; omega
              rw [← this]; ring
            rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
            simp only [wt, Nat.add_sub_cancel]
            have hX : 0 ≤ c ^ m * (M ^ n * (c₁ ^ n * cb) * Φ ψ) := by
              have := hΦ ψ; positivity
            have hsq : 1 + ((incI E v).card : ℝ) * (incI E v).card ≤ ((m : ℝ) + 1) ^ 2 := by
              have h0 : (0 : ℝ) ≤ (incI E v).card := Nat.cast_nonneg _
              nlinarith
            calc c ^ m * cb * (M ^ n * c₁ ^ n * Φ ψ) +
                  ((incI E v).card : ℝ) * ((incI E v).card * (c ^ m * (M ^ n * (c₁ ^ n * cb) *
                    Φ ψ)))
                = (1 + ((incI E v).card : ℝ) * (incI E v).card) *
                    (c ^ m * (M ^ n * (c₁ ^ n * cb) * Φ ψ)) := by ring
              _ ≤ ((m : ℝ) + 1) ^ 2 * (c ^ m * (M ^ n * (c₁ ^ n * cb) * Φ ψ)) :=
                  mul_le_mul_of_nonneg_right hsq hX
              _ = M ^ (n + 1) * (c₁ ^ n * cb) * Φ ψ := by rw [hM]; ring
    · push Not at hbv
      have hboxeq : ∀ g z, boxF d L O bx (Function.update g v z) = boxF d L O bx g := by
        intro g z
        cases bx with
        | none => rfl
        | some p =>
          have hp : p.1 ≠ v := fun h => hbv p.2 (by rw [← h])
          simp only [boxF, Function.update_of_ne hp, Function.update_of_ne hOv]
      have hI : (incI E v).Nonempty := by
        obtain ⟨e, he, hc'⟩ := I.anch (· = v) ⟨v, rfl⟩
          (by rintro u rfl; exact ⟨Or.inr hvS, hvA, hbv⟩)
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
        refine ⟨⟨j, hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
        change Inc v E[j]
        unfold Cross at hc'
        unfold Inc
        tauto
      have hpt : ∀ g, ∑ z, stF d L W β O (insert v S') E bx (Function.update g v z) ≤
          ∑ i ∈ incI E v, (c ^ m * c₁) * stF d L W β O S' (rehang E v i) bx g := by
        intro g
        have h1 : ∀ z, stF d L W β O (insert v S') E bx (Function.update g v z) ≤
            ∑ i ∈ incI E v, c ^ m * (bB d L W z (g (oth v E[i])) * β v (Function.update g v z)) *
              stF d L W β O S' (rehang E v i) bx g := by
          intro z
          have hβv := hβ0 v (Function.update g v z)
          have hr := bProd_rehang hd hW E v hI g z
          simp only [stF]
          rw [hprod g z, hboxeq g z]
          calc bProd d L W E (Function.update g v z) * (β v (Function.update g v z) *
                ∏ w ∈ S', β w g) * boxF d L O bx g
              ≤ (c ^ m * ∑ i ∈ incI E v, bB d L W z (g (oth v E[i])) *
                  bProd d L W (rehang E v i) g) * (β v (Function.update g v z) *
                  ∏ w ∈ S', β w g) * boxF d L O bx g := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  (hr.trans (mul_le_mul_of_nonneg_right hcm ?_)) (mul_nonneg hβv (hP0 g)))
                  (boxF_nonneg _ _ _)
                exact Finset.sum_nonneg fun r _ => mul_nonneg (bB_nonneg' _ _)
                  (bProd_nonneg _ _)
            _ = _ := by
                rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun r _ => ?_
                ring
        calc ∑ z, stF d L W β O (insert v S') E bx (Function.update g v z)
            ≤ ∑ z, ∑ i ∈ incI E v, c ^ m * (bB d L W z (g (oth v E[i])) *
                β v (Function.update g v z)) * stF d L W β O S' (rehang E v i) bx g :=
              Finset.sum_le_sum fun z _ => h1 z
          _ = ∑ i ∈ incI E v, c ^ m * (∑ z, bB d L W z (g (oth v E[i])) *
                β v (Function.update g v z)) * stF d L W β O S' (rehang E v i) bx g := by
              refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => ?_)
              rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ ∑ i ∈ incI E v, (c ^ m * c₁) * stF d L W β O S' (rehang E v i) bx g := by
              refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hfull v hvS₀ g (g (oth v E[i]))) ?_) (hstF0 _ _ _ _)
              exact pow_nonneg hc0 m
      have hwt : c₁ * wt c₁ cb bx n = wt c₁ cb bx (n + 1) := by
        cases bx with
        | none => simp only [wt]; ring
        | some p =>
          obtain ⟨hz, -⟩ := I.box p.1 p.2 rfl
          have hzv : p.1 ≠ v := fun h => hbv p.2 (by rw [← h])
          have : 1 ≤ n := by
            rw [← hS'card]
            exact Finset.card_pos.2 ⟨p.1, Finset.mem_erase.2 ⟨hzv, hz⟩⟩
          simp only [wt, Nat.add_sub_cancel]
          rw [← mul_assoc, ← pow_succ']
          congr 2
          omega
      calc sumS S' (fun g => ∑ z, stF d L W β O (insert v S') E bx (Function.update g v z)) ψ
          ≤ sumS S' (fun g => ∑ i ∈ incI E v,
              (c ^ m * c₁) * stF d L W β O S' (rehang E v i) bx g) ψ := sumS_mono _ hpt ψ
        _ = ∑ i ∈ incI E v, (c ^ m * c₁) * sumS S' (stF d L W β O S' (rehang E v i) bx) ψ := by
            rw [sumS_sum]
            exact Finset.sum_congr rfl fun i _ => sumS_mul _ _ _ _
        _ ≤ ∑ i ∈ incI E v, (c ^ m * c₁) * (M ^ n * wt c₁ cb bx n * Φ ψ) :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (ih S' hS'S₀ hS'card _ _
              ((length_rehang E v i).trans hE) (inv_rehang I hvS hvS₀ hvA hbv hi) ψ)
              (by positivity)
        _ = ((incI E v).card : ℝ) * c ^ m * M ^ n * (c₁ * wt c₁ cb bx n) * Φ ψ := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ((m : ℝ) + 1) ^ 2 * c ^ m * M ^ n * (c₁ * wt c₁ cb bx n) * Φ ψ := by
            have h1 : ((incI E v).card : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
            have := hΦ ψ
            have := wt_nonneg hc₁ hcb bx n
            gcongr
        _ = M ^ (n + 1) * wt c₁ cb bx (n + 1) * Φ ψ := by rw [← hwt, hM]; ring

end ElimMain

section Vertex

/-- The ball `{y : ‖y - x₀‖_L ≤ ρ}` of `Z_L^d` has at most `(2ρ + 1)^d` points. -/
private theorem AuxTree_card_ball (d L : ℕ) [NeZero L] (x₀ : Zd d L) (ρ : ℕ) :
    (Finset.univ.filter (fun y : Zd d L => zdistInf d L (y - x₀) ≤ ρ)).card ≤ (2 * ρ + 1) ^ d := by
  have h : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(ρ : ℤ)) ρ).card = (2 * ρ + 1) ^ d := by
    rw [Fintype.card_piFinset]
    simp [Int.card_Icc]
    congr 1; omega
  rw [← h]
  refine Finset.card_le_card_of_injOn (fun y i => (y - x₀) i |>.valMinAbs) ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := zdist_le_zdistInf d L (y - x₀) i
    rw [zdist_eq_natAbs_valMinAbs] at h1
    omega
  · intro y _ z _ hyz
    have : y - x₀ = z - x₀ := funext fun i => ZMod.valMinAbs_inj.1 (congrFun hyz i)
    exact sub_left_injective this

/-- Dyadic shells around `y`: if the ball sums of a nonnegative `g` satisfy
`2^q K^{-q} Σ_{‖x - y‖_L ≤ K} g(x) ≤ c` for all integers `K ∈ [W, L/2]`, then
`Σ_x g(x) ⟨x - y⟩^{-q} ≤ (log₂(L/W) + 2) c`, for `q ≥ 0`, `W ≥ 1`, `L ≥ 2W`. -/
private theorem AuxTree_shell (d L W : ℕ) [NeZero L] (hW : 1 ≤ W) (hWL : 2 * W ≤ L)
    (y : Zd d L) (q c : ℝ) (hq : 0 ≤ q) (g : Zd d L → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hc : ∀ K : ℕ, W ≤ K → 2 * K ≤ L →
      (2 : ℝ) ^ q * (K : ℝ) ^ (-q) *
        ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L (x - y) ≤ K), g x ≤ c) :
    ∑ x, g x * brk d L W x y ^ (-q) ≤ logF L W * c := by
  have hW0 : 0 < W := hW
  set H := L / 2 with hH
  have hWH : W ≤ H := by omega
  set ρ : ℕ → ℕ := fun n => min (2 ^ n * W) H with hρ
  have hρW : ∀ n, W ≤ ρ n := fun n =>
    le_min (Nat.le_mul_of_pos_left _ (by positivity)) hWH
  have hρH : ∀ n, ρ n ≤ H := fun n => min_le_right _ _
  have hρ2 : ∀ n, 2 * ρ n ≤ L := fun n => by have := hρH n; omega
  have hρs : ∀ n, ρ (n + 1) ≤ 2 * ρ n := fun n => by
    have e : 2 ^ (n + 1) * W = 2 * (2 ^ n * W) := by ring
    simp only [hρ, e]
    generalize 2 ^ n * W = X
    omega
  have hρ0 : ρ 0 ≤ W := by simp [hρ]
  set N := Nat.log 2 (L / W) with hN
  have hLW : L < 2 ^ (N + 1) * W :=
    (Nat.div_lt_iff_lt_mul hW0).1 (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hρN : ρ N = H := by
    have e : 2 ^ (N + 1) * W = 2 * (2 ^ N * W) := by ring
    have : H ≤ 2 ^ N * W := by omega
    exact min_eq_right this
  have hN1 : ((N : ℝ) + 1) ≤ logF L W := by
    unfold logF
    have hLW0 : L / W ≠ 0 := by
      have : 0 < L / W := Nat.div_pos (by omega) hW0
      omega
    have h1 : 2 ^ N ≤ L / W := Nat.pow_log_le_self 2 hLW0
    have h2 : ((2 : ℝ)) ^ N ≤ (L : ℝ) / W := by
      have h := (by exact_mod_cast h1 : ((2 ^ N : ℕ) : ℝ) ≤ ((L / W : ℕ) : ℝ)).trans
        Nat.cast_div_le
      simpa using h
    have h3 : (N : ℝ) ≤ Real.logb 2 ((L : ℝ) / W) := by
      have hpos : (0 : ℝ) < (L : ℝ) / W := by
        have : (1 : ℝ) ≤ W := by exact_mod_cast hW
        have : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
        positivity
      rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
      exact h2
    linarith
  have hcover : ∀ n x, zdistInf d L (x - y) ≤ ρ n →
      ∃ m ≤ n, zdistInf d L (x - y) ≤ ρ m ∧ ρ m ≤ 2 * (zdistInf d L (x - y) + W) := by
    intro n
    induction n with
    | zero => exact fun x hx => ⟨0, le_rfl, hx, by omega⟩
    | succ n ih =>
      intro x hx
      by_cases h : zdistInf d L (x - y) ≤ ρ n
      · obtain ⟨m, hm, h1, h2⟩ := ih x h
        exact ⟨m, by omega, h1, h2⟩
      · refine ⟨n + 1, le_rfl, hx, ?_⟩
        have := hρs n
        omega
  have hc0 : 0 ≤ c := by
    refine le_trans ?_ (hc W le_rfl hWL)
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Finset.sum_nonneg fun x _ => hg x)
  have hpt : ∀ x, g x * brk d L W x y ^ (-q) ≤ ∑ n ∈ Finset.range (N + 1),
      ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
        (if zdistInf d L (x - y) ≤ ρ n then g x else 0) := by
    intro x
    obtain ⟨m, hm, hxm, hρm⟩ := hcover N x (by rw [hρN]; exact zdistInf_le_half d L (x - y))
    have hρpos : (0 : ℝ) < ρ m := by
      have : (1 : ℝ) ≤ W := by exact_mod_cast hW
      have : (W : ℝ) ≤ ρ m := by exact_mod_cast hρW m
      linarith
    have hb : (ρ m : ℝ) / 2 ≤ brk d L W x y := by
      unfold brk
      have : (ρ m : ℝ) ≤ 2 * ((zdistInf d L (x - y) : ℝ) + W) := by exact_mod_cast hρm
      linarith
    have h1 : brk d L W x y ^ (-q) ≤ (2 : ℝ) ^ q * (ρ m : ℝ) ^ (-q) := by
      refine (Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)).trans (le_of_eq ?_)
      rw [Real.div_rpow hρpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    have hterm : ∀ n ∈ Finset.range (N + 1), 0 ≤ ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
        (if zdistInf d L (x - y) ≤ ρ n then g x else 0) := by
      intro n _
      refine mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
      split_ifs
      · exact hg x
      · exact le_rfl
    refine le_trans ?_ (Finset.single_le_sum hterm (Finset.mem_range.2 (by omega : m < N + 1)))
    simp only [hxm, ite_true]
    rw [mul_comm (g x)]
    exact mul_le_mul_of_nonneg_right h1 (hg x)
  calc ∑ x, g x * brk d L W x y ^ (-q)
      ≤ ∑ x, ∑ n ∈ Finset.range (N + 1), ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
          (if zdistInf d L (x - y) ≤ ρ n then g x else 0) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ n ∈ Finset.range (N + 1), ((2 : ℝ) ^ q * (ρ n : ℝ) ^ (-q)) *
          ∑ x ∈ Finset.univ.filter (fun x : Zd d L => zdistInf d L (x - y) ≤ ρ n), g x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.mul_sum, Finset.sum_filter]
    _ ≤ ∑ n ∈ Finset.range (N + 1), c :=
        Finset.sum_le_sum fun n _ => hc (ρ n) (hρW n) (hρ2 n)
    _ = ((N : ℝ) + 1) * c := by simp
    _ ≤ logF L W * c := mul_le_mul_of_nonneg_right hN1 hc0

/-- For `p ≥ d`, `Σ_z ⟨z - x⟩^{-p} ≤ C (log₂(L/W) + 2) W^{d-p}` with `C` depending on `d, p`
only, for `W ≥ 1` and `L ≥ 2W`. -/
private theorem AuxTree_tail (d : ℕ) (p : ℝ) (hp : (d : ℝ) ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L → ∀ x : Zd d L,
      ∑ z, brk d L W z x ^ (-p) ≤ C * logF L W * (W : ℝ) ^ ((d : ℝ) - p) := by
  have hp0 : 0 ≤ p := le_trans (Nat.cast_nonneg _) hp
  refine ⟨2 ^ p * 3 ^ d, by positivity, fun L W _ hW hWL x => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have key := AuxTree_shell d L W hW hWL x p ((2 : ℝ) ^ p * 3 ^ d * (W : ℝ) ^ ((d : ℝ) - p)) hp0
    (fun _ => 1) (fun _ => zero_le_one) (fun K hK1 hK2 => ?_)
  · simp only [one_mul] at key
    calc _ ≤ _ := key
      _ = _ := by ring
  · have hK1' : (W : ℝ) ≤ K := by exact_mod_cast hK1
    have hK0 : (0 : ℝ) < K := by linarith
    have hcard : ((Finset.univ.filter (fun z : Zd d L => zdistInf d L (z - x) ≤ K)).card : ℝ) ≤
        (3 * K) ^ d := by
      calc _ ≤ ((2 * K + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast AuxTree_card_ball d L x K
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by push_cast; linarith) d
    have hKp : (K : ℝ) ^ (-p) * (K : ℝ) ^ d = (K : ℝ) ^ ((d : ℝ) - p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hK0]; congr 1; ring
    have hKW : (K : ℝ) ^ ((d : ℝ) - p) ≤ (W : ℝ) ^ ((d : ℝ) - p) :=
      Real.rpow_le_rpow_of_nonpos hW0 hK1' (by linarith)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    calc (2 : ℝ) ^ p * (K : ℝ) ^ (-p) * _ ≤ (2 : ℝ) ^ p * (K : ℝ) ^ (-p) * (3 * K) ^ d :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = (2 : ℝ) ^ p * 3 ^ d * ((K : ℝ) ^ (-p) * (K : ℝ) ^ d) := by rw [mul_pow]; ring
      _ ≤ _ := by
          rw [hKp]
          exact mul_le_mul_of_nonneg_left hKW (by positivity)

private theorem logF_nonneg' {L W : ℕ} (hW : 1 ≤ W) (hWL : W ≤ L) : 0 ≤ logF L W := by
  unfold logF
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : (1 : ℝ) ≤ (L : ℝ) / W := by
    rw [le_div_iff₀ hW0, one_mul]; exact_mod_cast hWL
  have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h1
  linarith

private theorem weakNorm_nonneg' {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (a b : ℝ)
    (M : Matrix (Zd d L) (Zd d L) ℝ) : 0 ≤ weakNorm d L W a b M := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := (normBasic d L W hW a b M).1 0 0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).1 ((abs_nonneg _).trans h)

private theorem le_iSup₂' {ι κ : Type*} [Finite ι] [Finite κ] (f : ι → κ → ℝ) (i : ι) (j : κ) :
    f i j ≤ ⨆ i, ⨆ j, f i j :=
  (le_ciSup (Finite.bddAbove_range _) j).trans
    (le_ciSup (f := fun i => ⨆ j, f i j) (Finite.bddAbove_range _) i)

private theorem weakNorm_transpose {d L W : ℕ} [NeZero L] (a b : ℝ)
    (M : Matrix (Zd d L) (Zd d L) ℝ) : weakNorm d L W a b M.transpose = weakNorm d L W a b M := by
  unfold weakNorm
  congr 1
  · congr 1
    simp only [Matrix.transpose_apply]
    have h0 : ∀ N : Matrix (Zd d L) (Zd d L) ℝ, 0 ≤ ⨆ x, ⨆ y, |N x y| :=
      fun N => (abs_nonneg (N 0 0)).trans (le_iSup₂' (fun x y => |N x y|) 0 0)
    refine le_antisymm (Real.iSup_le (fun x => Real.iSup_le (fun y => ?_) (h0 M)) (h0 M))
      (Real.iSup_le (fun x => Real.iSup_le (fun y => ?_) (h0 M.transpose)) (h0 M.transpose))
    · exact le_iSup₂' (fun x y => |M x y|) y x
    · exact le_iSup₂' (fun x y => |M y x|) y x
  · congr 1
    ext K
    congr 1
    congr 1
    ext x
    congr 1
    ext x₀
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Matrix.transpose_apply]
    ring

private theorem gammaB_one' {d L W : ℕ} [NeZero L] (y : Fin 1 → Zd d L) : gammaB d L W y = 1 := by
  unfold gammaB
  simp

/-- The sum over one vertex joined by one `B` edge and one blue edge, either orientation:
`Σ_z B_{zu} |M_{zp}| ≤ C (log₂(L/W) + 2) W^{-ad/2} ‖M‖_{w;(a,b)}` ([I, (6.32)] with `k = 1`). -/
private theorem vertexWeak (d : ℕ) (a b : ℝ) (hd : 2 ≤ d) (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ a * d / 2 - b - 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L →
      ∀ (M : Matrix (Zd d L) (Zd d L) ℝ) (p u : Zd d L),
        (∑ z, bB d L W z u * |M z p| ≤
          C * logF L W * (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b M) ∧
        (∑ z, bB d L W z u * |M p z| ≤
          C * logF L W * (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b M) := by
  obtain ⟨C, hC⟩ := keyobs3 d a b hd ha hb he 1 le_rfl
  refine ⟨max C 0, le_max_right _ _, fun L W _ hW hWL M p u => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hlog := logF_nonneg' hW (by omega : W ≤ L)
  have one : ∀ N : Matrix (Zd d L) (Zd d L) ℝ, ∑ z, bB d L W z u * |N z p| ≤
      max C 0 * logF L W * (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b N := by
    intro N
    have h := hC L W hW hWL N p (fun _ => u)
    simp only [Fin.prod_univ_one, pow_one, gammaB_one', mul_one] at h
    have hw := weakNorm_nonneg' hW a b N
    calc ∑ z, bB d L W z u * |N z p| = ∑ z, |N z p| * bB d L W z u :=
          Finset.sum_congr rfl fun z _ => mul_comm _ _
      _ ≤ C * logF L W * (W : ℝ) ^ (-(a * d / 2)) * weakNorm d L W a b N := h
      _ ≤ _ := by gcongr; exact le_max_left _ _
  refine ⟨one M, ?_⟩
  have h := one M.transpose
  simp only [Matrix.transpose_apply, weakNorm_transpose] at h
  exact h

/-- The sum of one blue entry over a box: `Σ_{z ∈ box(x₀, K)} |M_{zp}| ≤ K^d W^{-b} K^{-(ad/2-b)}
‖M‖_{w;(a,b)}`, either orientation ([I, (6.12)]). -/
private theorem vertexBox {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (a b : ℝ)
    (M : Matrix (Zd d L) (Zd d L) ℝ) (p x₀ : Zd d L) (K : ℕ) (hK : W ≤ K) (hKL : 2 * K ≤ L) :
    (∑ z, (if zdistInf d L (z - x₀) ≤ K then (1 : ℝ) else 0) * |M z p| ≤
      (K : ℝ) ^ d * ((W : ℝ) ^ (-b) * (K : ℝ) ^ (-(a * d / 2 - b)) * weakNorm d L W a b M)) ∧
    (∑ z, (if zdistInf d L (z - x₀) ≤ K then (1 : ℝ) else 0) * |M p z| ≤
      (K : ℝ) ^ d * ((W : ℝ) ^ (-b) * (K : ℝ) ^ (-(a * d / 2 - b)) * weakNorm d L W a b M)) := by
  have hK0 : (0 : ℝ) < K := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hW.trans hK
    linarith
  have h := (normBasic d L W hW a b M).2.1 K hK hKL p x₀
  rw [div_le_iff₀ (by positivity)] at h
  have e : ∀ f : Zd d L → ℝ, ∑ z, (if zdistInf d L (z - x₀) ≤ K then (1 : ℝ) else 0) * f z =
      ∑ z ∈ Finset.univ.filter (fun z => zdistInf d L (z - x₀) ≤ K), f z := by
    intro f
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
  rw [e, e, mul_comm ((K : ℝ) ^ d)]
  constructor
  · refine le_trans (Finset.sum_le_sum fun z _ => ?_) h
    linarith [abs_nonneg (M p z)]
  · refine le_trans (Finset.sum_le_sum fun z _ => ?_) h
    linarith [abs_nonneg (M z p)]

private theorem strongNorm_nonneg' {d L W : ℕ} [NeZero L] (hW : 1 ≤ W) (a b : ℝ)
    (M : Matrix (Zd d L) (Zd d L) ℝ) : 0 ≤ strongNorm d L W a b M := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := (normBasic d L W hW a b M).2.2 0 0
  have ht := brk_pos (L := L) hW (0 : Zd d L) 0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).1 ((abs_nonneg _).trans h)

/-- The sum over one vertex joined by one `B` edge and one edge `W^{-b} ⟨z - p⟩^{-(ad/2-b)}`:
`≤ C (log₂(L/W) + 2) W^{-ad/2}`, for `d ≥ 2` and `ad/2 - b - 2 ≥ 0`. -/
private theorem vertexStrong (d : ℕ) (a b : ℝ) (hd : 2 ≤ d) (hb : 0 < b)
    (he : 0 ≤ a * d / 2 - b - 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W → 2 * W ≤ L → ∀ p u : Zd d L,
      ∑ z, bB d L W z u * ((W : ℝ) ^ (-b) * brk d L W z p ^ (-(a * d / 2 - b))) ≤
        C * logF L W * (W : ℝ) ^ (-(a * d / 2)) := by
  rcases Nat.lt_or_ge 2 d with hd3 | hd2
  · have hd3' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    have hdpos : (0 : ℝ) < d := by linarith
    set a' : ℝ := 2 * (b + 2) / d with ha'
    have ha'd : a' * d / 2 = b + 2 := by rw [ha']; field_simp
    have ha'0 : 0 < a' := by positivity
    obtain ⟨C₃, hC₃⟩ := keyobs3 d a' b hd ha'0 hb (by rw [ha'd]; norm_num) 1 le_rfl
    obtain ⟨Cw, hCw⟩ := weak_le_strong d a' b (by rw [ha'd]; linarith) (by rw [ha'd]; linarith)
    refine ⟨max C₃ 0 * max Cw 0, by positivity, fun L W _ hW hWL p u => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have hW0 : (0 : ℝ) < W := by linarith
    have hlog := logF_nonneg' hW (by omega : W ≤ L)
    set S' : Matrix (Zd d L) (Zd d L) ℝ :=
      fun z q => (W : ℝ) ^ (-b) * brk d L W z q ^ (-(2 : ℝ)) with hS'
    have hS'0 : ∀ z q, 0 ≤ S' z q := fun z q => by
      have := brk_pos (L := L) hW z q
      simp only [hS']; positivity
    have hsn : strongNorm d L W a' b S' ≤ 1 := by
      unfold strongNorm
      refine Real.iSup_le (fun x => Real.iSup_le (fun y => le_of_eq ?_) zero_le_one) zero_le_one
      have ht := brk_pos (L := L) hW x y
      rw [abs_of_nonneg (hS'0 x y), ha'd]
      simp only [hS']
      rw [Real.div_rpow hW0.le ht.le, Real.rpow_add ht, Real.rpow_neg hW0.le,
        Real.rpow_neg ht.le]
      have h1 : (0 : ℝ) < (W : ℝ) ^ b := by positivity
      have h2 : (0 : ℝ) < brk d L W x y ^ b := by positivity
      have h3 : (0 : ℝ) < brk d L W x y ^ (2 : ℝ) := by positivity
      field_simp
    have hwn : weakNorm d L W a' b S' ≤ max Cw 0 := by
      have h1 := hCw L W hW S'
      have h2 := strongNorm_nonneg' hW a' b S'
      calc _ ≤ Cw * strongNorm d L W a' b S' := h1
        _ ≤ max Cw 0 * strongNorm d L W a' b S' :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) h2
        _ ≤ max Cw 0 * 1 := mul_le_mul_of_nonneg_left hsn (le_max_right _ _)
        _ = _ := mul_one _
    have hk := hC₃ L W hW hWL S' p (fun _ => u)
    simp only [Fin.prod_univ_one, pow_one, gammaB_one', mul_one] at hk
    have hpt : ∀ z, (W : ℝ) ^ (-b) * brk d L W z p ^ (-(a * d / 2 - b)) ≤
        (W : ℝ) ^ (2 - (a * d / 2 - b)) * |S' z p| := by
      intro z
      have ht := brk_pos (L := L) hW z p
      have hWt := W_le_brk (L := L) (W := W) z p
      rw [abs_of_nonneg (hS'0 z p)]
      have e : brk d L W z p ^ (-(a * d / 2 - b)) =
          brk d L W z p ^ (-(2 : ℝ)) * brk d L W z p ^ (2 - (a * d / 2 - b)) := by
        rw [← Real.rpow_add ht]; ring_nf
      have h1 : brk d L W z p ^ (2 - (a * d / 2 - b)) ≤ (W : ℝ) ^ (2 - (a * d / 2 - b)) :=
        Real.rpow_le_rpow_of_nonpos hW0 hWt (by linarith)
      calc (W : ℝ) ^ (-b) * brk d L W z p ^ (-(a * d / 2 - b))
          = (W : ℝ) ^ (-b) * brk d L W z p ^ (-(2 : ℝ)) *
              brk d L W z p ^ (2 - (a * d / 2 - b)) := by rw [e]; ring
        _ ≤ (W : ℝ) ^ (-b) * brk d L W z p ^ (-(2 : ℝ)) * (W : ℝ) ^ (2 - (a * d / 2 - b)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by simp only [hS']; ring
    have hWe : (W : ℝ) ^ (2 - (a * d / 2 - b)) * (W : ℝ) ^ (-(a' * d / 2)) =
        (W : ℝ) ^ (-(a * d / 2)) := by
      rw [← Real.rpow_add hW0, ha'd]; congr 1; ring
    calc ∑ z, bB d L W z u * ((W : ℝ) ^ (-b) * brk d L W z p ^ (-(a * d / 2 - b)))
        ≤ ∑ z, bB d L W z u * ((W : ℝ) ^ (2 - (a * d / 2 - b)) * |S' z p|) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpt z) (bB_nonneg' _ _)
      _ = (W : ℝ) ^ (2 - (a * d / 2 - b)) * ∑ z, |S' z p| * bB d L W z u := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ (W : ℝ) ^ (2 - (a * d / 2 - b)) * (C₃ * logF L W * (W : ℝ) ^ (-(a' * d / 2)) *
            weakNorm d L W a' b S') := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ (W : ℝ) ^ (2 - (a * d / 2 - b)) * (max C₃ 0 * logF L W * (W : ℝ) ^ (-(a' * d / 2)) *
            max Cw 0) := by
          have hw0 := weakNorm_nonneg' hW a' b S'
          gcongr
          exact le_max_left _ _
      _ = max C₃ 0 * max Cw 0 * logF L W *
            ((W : ℝ) ^ (2 - (a * d / 2 - b)) * (W : ℝ) ^ (-(a' * d / 2))) := by ring
      _ = _ := by rw [hWe]
  · have hd2' : d = 2 := by omega
    subst hd2'
    have hs : (2 : ℝ) ≤ a * ((2 : ℕ) : ℝ) / 2 - b := by linarith
    obtain ⟨Ct, hCt0, hCt⟩ := AuxTree_tail 2 (a * ((2 : ℕ) : ℝ) / 2 - b) (by simpa using hs)
    refine ⟨Ct, hCt0, fun L W _ hW hWL p u => ?_⟩
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
    have hB : ∀ z, bB 2 L W z u = (W : ℝ) ^ (-2 : ℝ) := fun z => by
      unfold bB; norm_num
    have ht := hCt L W hW hWL p
    have hcomm : ∀ z, brk 2 L W z p = brk 2 L W z p := fun z => rfl
    calc ∑ z, bB 2 L W z u * ((W : ℝ) ^ (-b) * brk 2 L W z p ^ (-(a * ((2 : ℕ) : ℝ) / 2 - b)))
        = (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-b) *
            ∑ z, brk 2 L W z p ^ (-(a * ((2 : ℕ) : ℝ) / 2 - b)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by rw [hB]; ring
      _ ≤ (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-b) *
            (Ct * logF L W * (W : ℝ) ^ (((2 : ℕ) : ℝ) - (a * ((2 : ℕ) : ℝ) / 2 - b))) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = Ct * logF L W * ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-b) *
            (W : ℝ) ^ (((2 : ℕ) : ℝ) - (a * ((2 : ℕ) : ℝ) / 2 - b))) := by ring
      _ = _ := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
          congr 2
          push_cast
          ring

end Vertex

section Path
variable {V : Type*} {d L W : ℕ} [NeZero L]

private theorem brk_tri (p q r : Zd d L) :
    brk d L W p r ≤ brk d L W p q + brk d L W q r - W := by
  unfold brk
  have := zd_tri p q r
  have h : (zdistInf d L (p - r) : ℝ) ≤ zdistInf d L (p - q) + zdistInf d L (q - r) := by
    exact_mod_cast this
  linarith

private theorem PD.brk_chain {E : List (V × V)} {A : V → Prop} {q : V → V} {h ι : V → ℕ}
    (_P : PD E A q h ι) (g : V → Zd d L) (Y : V) : ∀ k,
    brk d L W (g Y) (g (q^[k] Y)) ≤
      W + ∑ j ∈ Finset.range k, brk d L W (g (q^[j] Y)) (g (q (q^[j] Y))) := by
  intro k
  induction k with
  | zero => simp [brk, (zdistInf_eq_zero_iff d L).2 rfl]
  | succ k ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply']
    have := brk_tri (W := W) (g Y) (g (q^[k] Y)) (g (q (q^[k] Y)))
    linarith

/-- Pulling a long edge out of the path from `Y` to the root `X`: for an edge weight
`κ ⟨·⟩^{-r}` with `r ≥ 0`, the product over `E` is at most `(h Y + 1)^r κ ⟨X - Y⟩^{-r}` times
the sum over the path edges of the product over the other edges. -/
private theorem PD.path_prod {E : List (V × V)} {X : V} {q : V → V} {h ι : V → ℕ}
    (P : PD E (· = X) q h ι) (hW : 1 ≤ W) (Y : V) (hY : Y ≠ X) (g : V → Zd d L) (κ r : ℝ)
    (hκ : 0 ≤ κ) (hr : 0 ≤ r) :
    (E.map fun e => κ * brk d L W (g e.1) (g e.2) ^ (-r)).prod ≤
      ((h Y : ℝ) + 1) ^ r * (κ * brk d L W (g X) (g Y) ^ (-r)) *
        ∑ j ∈ Finset.range (h Y),
          ((E.eraseIdx (ι (q^[j] Y))).map fun e => κ * brk d L W (g e.1) (g e.2) ^ (-r)).prod := by
  set f : V × V → ℝ := fun e => κ * brk d L W (g e.1) (g e.2) ^ (-r) with hf
  have hf0 : ∀ e, 0 ≤ f e := fun e => by
    have := brk_pos (L := L) hW (g e.1) (g e.2); simp only [hf]; positivity
  have hH : 1 ≤ h Y := by
    by_contra h0
    exact hY ((P.zero_iff Y).1 (by omega))
  have hqX : q^[h Y] Y = X := (P.zero_iff _).1 (by rw [P.iter Y (h Y) le_rfl]; simp)
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range (h Y))
    (fun j => brk d L W (g (q^[j] Y)) (g (q (q^[j] Y)))) ⟨0, Finset.mem_range.2 hH⟩
  have hjH := Finset.mem_range.1 hj
  set u := q^[j] Y with hu
  have huA : ¬ u = X := P.not_anch_iter Y hjH
  have hchain := P.brk_chain (W := W) g Y (h Y)
  rw [hqX] at hchain
  have hsum : ∑ i ∈ Finset.range (h Y), brk d L W (g (q^[i] Y)) (g (q (q^[i] Y))) ≤
      (h Y : ℝ) * brk d L W (g u) (g (q u)) := by
    have := Finset.sum_le_card_nsmul (Finset.range (h Y))
      (fun i => brk d L W (g (q^[i] Y)) (g (q (q^[i] Y)))) _ hjmax
    simpa using this
  have hWu : (W : ℝ) ≤ brk d L W (g u) (g (q u)) := W_le_brk _ _
  have hXY : brk d L W (g X) (g Y) ≤ ((h Y : ℝ) + 1) * brk d L W (g u) (g (q u)) := by
    rw [brk_comm]; nlinarith
  have hpos := brk_pos (L := L) hW (g X) (g Y)
  have hupos := brk_pos (L := L) hW (g u) (g (q u))
  have hH1 : (0 : ℝ) < (h Y : ℝ) + 1 := by positivity
  have hfe : f (u, q u) ≤ ((h Y : ℝ) + 1) ^ r * (κ * brk d L W (g X) (g Y) ^ (-r)) := by
    simp only [hf]
    have h1 : brk d L W (g u) (g (q u)) ^ (-r) ≤
        (brk d L W (g X) (g Y) / ((h Y : ℝ) + 1)) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) ((div_le_iff₀ hH1).2 (by linarith))
        (by linarith)
    rw [Real.div_rpow hpos.le hH1.le, Real.rpow_neg hH1.le, div_inv_eq_mul] at h1
    calc κ * brk d L W (g u) (g (q u)) ^ (-r)
        ≤ κ * (brk d L W (g X) (g Y) ^ (-r) * ((h Y : ℝ) + 1) ^ r) :=
          mul_le_mul_of_nonneg_left h1 hκ
      _ = _ := by ring
  obtain ⟨hi, he⟩ := P.idx u huA
  have hfi : f E[ι u] = f (u, q u) := by
    rcases he with he | he <;> rw [he]
    simp only [hf, brk_comm]
  have hterm : ∀ i ∈ Finset.range (h Y),
      0 ≤ ((E.eraseIdx (ι (q^[i] Y))).map f).prod := fun i _ =>
    prod_map_nonneg _ _ fun e _ => hf0 e
  calc (E.map f).prod = f E[ι u] * ((E.eraseIdx (ι u)).map f).prod := prod_map_eraseIdx _ _ _ hi
    _ ≤ (((h Y : ℝ) + 1) ^ r * (κ * brk d L W (g X) (g Y) ^ (-r))) *
          ((E.eraseIdx (ι u)).map f).prod :=
        mul_le_mul_of_nonneg_right (hfi ▸ hfe) (prod_map_nonneg _ _ fun e _ => hf0 e)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.single_le_sum hterm hj) (by positivity)

end Path

section Blue
variable {V : Type*} {d L : ℕ}

/-- The blue factor `|A_j(g e.1, g e.2)|` of the edge `e = (e.1, e.2, j)`. -/
private def blueF (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (g : V → Zd d L) (e : V × V × ℕ) : ℝ :=
  |A e.2.2 (g e.1) (g e.2.1)|

/-- The endpoints of the blue edges. -/
private def bluePairs (Ub : List (V × V × ℕ)) : List (V × V) := Ub.map fun e => (e.1, e.2.1)

variable {Ub : List (V × V × ℕ)} {A' : V → Prop} {q : V → V} {h ι : V → ℕ}

private theorem blue_shape (P : PD (bluePairs Ub) A' q h ι) {v : V} (hv : ¬ A' v)
    (dflt : V × V × ℕ) : ι v < Ub.length ∧
      (((Ub.getD (ι v) dflt).1 = v ∧ (Ub.getD (ι v) dflt).2.1 = q v) ∨
        ((Ub.getD (ι v) dflt).1 = q v ∧ (Ub.getD (ι v) dflt).2.1 = v)) := by
  obtain ⟨hi, he⟩ := P.idx v hv
  have hi' : ι v < Ub.length := by simpa [bluePairs] using hi
  refine ⟨hi', ?_⟩
  rw [List.getD_eq_getElem _ _ hi']
  simp only [bluePairs, List.getElem_map, Prod.mk.injEq] at he
  exact he

private theorem blue_dep [DecidableEq V] (P : PD (bluePairs Ub) A' q h ι)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (dflt : V × V × ℕ) {w v : V} (hw : ¬ A' w)
    (hvw : v ≠ w) (hvq : v ≠ q w) (g : V → Zd d L) (z : Zd d L) :
    blueF A (Function.update g v z) (Ub.getD (ι w) dflt) = blueF A g (Ub.getD (ι w) dflt) := by
  obtain ⟨-, he⟩ := blue_shape P hw dflt
  unfold blueF
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    simp only [Function.update_of_ne hvw.symm, Function.update_of_ne hvq.symm]

private theorem blue_sum [DecidableEq V] [NeZero L] (P : PD (bluePairs Ub) A' q h ι)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (dflt : V × V × ℕ) {v : V} (hv : ¬ A' v)
    (wz : Zd d L → ℝ) (c : ℝ)
    (hA : ∀ j p, ∑ z, wz z * |A j z p| ≤ c ∧ ∑ z, wz z * |A j p z| ≤ c) (g : V → Zd d L) :
    ∑ z, wz z * blueF A (Function.update g v z) (Ub.getD (ι v) dflt) ≤ c := by
  obtain ⟨-, he⟩ := blue_shape P hv dflt
  have hq : q v ≠ v := P.q_ne hv
  unfold blueF
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    simp only [Function.update_self, Function.update_of_ne hq]
  · exact (hA _ _).1
  · exact (hA _ _).2

/-- The product of the blue factors is at most the product over the parent edges of `s`, when
all factors lie in `[0, 1]`. -/
private theorem blue_prod (P : PD (bluePairs Ub) A' q h ι)
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (dflt : V × V × ℕ) (hA1 : ∀ j p r, |A j p r| ≤ 1)
    (s : Finset V) (hs : ∀ v ∈ s, ¬ A' v) (g : V → Zd d L) :
    (Ub.map (blueF A g)).prod ≤ ∏ v ∈ s, blueF A g (Ub.getD (ι v) dflt) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · rw [Finset.prod_empty]
    exact prod_map_le_one _ _ (fun e _ => abs_nonneg _) (fun e _ => hA1 _ _ _)
  have hpos : 0 < Ub.length := lt_of_le_of_lt (Nat.zero_le _) (blue_shape P (hs v₀ hv₀) dflt).1
  have key := prod_map_le_sub Ub (blueF A g) (fun e _ => abs_nonneg _)
    (fun e _ => hA1 _ _ _) s (fun v => ⟨ι v % Ub.length, Nat.mod_lt _ hpos⟩) ?_
  · refine key.trans (le_of_eq (Finset.prod_congr rfl fun v hv => ?_))
    have hi := (blue_shape P (hs v hv) dflt).1
    simp only [Nat.mod_eq_of_lt hi]
    rw [List.getD_eq_getElem _ _ hi]
    rfl
  · intro v hv w hw hvw
    have hi := (blue_shape P (hs v hv) dflt).1
    have hj := (blue_shape P (hs w hw) dflt).1
    simp only [Fin.mk.injEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hvw
    exact P.inj (hs v hv) (hs w hw) hvw

end Blue

section Bridge
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The internal atoms. -/
private def intA (ℓ : ℕ) : Finset (Atom 2 ℓ) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

private theorem inl_notMem_intA {ℓ : ℕ} (i : Fin 2) : (Sum.inl i : Atom 2 ℓ) ∉ intA ℓ := by
  simp [intA]

private theorem inr_mem_intA {ℓ : ℕ} (k : Fin ℓ) : (Sum.inr k : Atom 2 ℓ) ∈ intA ℓ := by
  simp [intA]

private theorem card_intA (ℓ : ℕ) : (intA ℓ).card = ℓ := by simp [intA]

private theorem fin2_eq {X Y i : Fin 2} (hXY : X ≠ Y) (hi : i ≠ X) : i = Y := by
  have h1 : X.val ≠ Y.val := fun h => hXY (Fin.ext h)
  have h2 : i.val ≠ X.val := fun h => hi (Fin.ext h)
  exact Fin.ext (by omega)

/-- The sum over the internal positions is the sum over the positions fixed off the internal
atoms. -/
private theorem sum_atom {ℓ : ℕ} (G : (Atom 2 ℓ → α) → ℝ) (ψ : Atom 2 ℓ → α) :
    ∑ s : Fin ℓ → α, G (Sum.elim (ψ ∘ Sum.inl) s) = sumS (intA ℓ) G ψ := by
  unfold sumS
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun s => Sum.elim (ψ ∘ Sum.inl) s) (fun g => g ∘ Sum.inr)
    ?_ (fun _ _ => Finset.mem_univ _) (fun s _ => rfl) ?_ (fun _ _ => rfl)
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hw
    cases w with
    | inl i => rfl
    | inr k => exact absurd (inr_mem_intA k) hw
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    funext w
    cases w with
    | inl i => exact (hg (Sum.inl i) (inl_notMem_intA i)).symm
    | inr k => rfl

/-- The atoms other than `inl X`, as vertices of `Option (Atom 2 ℓ)`. -/
private def avgS (ℓ : ℕ) (X : Fin 2) : Finset (Option (Atom 2 ℓ)) :=
  (Finset.univ.filter fun v : Atom 2 ℓ => v ≠ Sum.inl X).map Function.Embedding.some

/-- The positions with the box atom `Y` at `y` and the internal atoms at `s`. -/
private def liftPos {ℓ : ℕ} (X : Fin 2) (ψ : Option (Atom 2 ℓ) → α) (y : α) (s : Fin ℓ → α) :
    Option (Atom 2 ℓ) → α
  | none => ψ none
  | some (Sum.inl i) => if i = X then ψ (some (Sum.inl X)) else y
  | some (Sum.inr k) => s k

/-- The sum over the positions fixed at `none` and `inl X` is the sum over the position of the
other external atom and over the internal positions. -/
private theorem sum_opt {ℓ : ℕ} {X Y : Fin 2} (hXY : X ≠ Y) (F : (Option (Atom 2 ℓ) → α) → ℝ)
    (ψ : Option (Atom 2 ℓ) → α) :
    sumS (avgS ℓ X) F ψ = ∑ y, ∑ s : Fin ℓ → α, F (liftPos X ψ y s) := by
  unfold sumS
  rw [← Finset.sum_filter, ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_nbij' (fun p => liftPos X ψ p.1 p.2)
    (fun g => (g (some (Sum.inl Y)), fun k => g (some (Sum.inr k))))
    ?_ (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hw
    match w with
    | none => rfl
    | some (Sum.inl i) =>
      have hiX : i = X := by
        by_contra h
        exact hw (Finset.mem_map.2 ⟨Sum.inl i, by simp [h], rfl⟩)
      subst hiX
      simp [liftPos]
    | some (Sum.inr k) => exact absurd (Finset.mem_map.2 ⟨Sum.inr k, by simp, rfl⟩) hw
  · intro p _
    simp [liftPos, Ne.symm hXY]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    funext w
    match w with
    | none => exact (hg none (by simp [avgS])).symm
    | some (Sum.inl i) =>
      by_cases hi : i = X
      · subst hi
        simp only [liftPos, ite_true]
        exact (hg _ (by simp [avgS])).symm
      · simp only [liftPos, hi, ite_false]
        rw [fin2_eq hXY hi]
    | some (Sum.inr k) => rfl

end Bridge

section Cores

private theorem inR_self {V : Type*} (S₀ : Finset V) (u : V) : InR S₀ S₀ u := by
  by_cases h : u ∈ S₀
  · exact Or.inr h
  · exact Or.inl h

private theorem card_atom (ℓ : ℕ) : Fintype.card (Atom 2 ℓ) = ℓ + 2 := by
  simp [Atom, Fintype.card_sum]; omega

/-- The value of an auxiliary graph in terms of `bProd` and `blueF`. -/
private theorem val_eq {ℓ : ℕ} (Γ : AuxGraph ℓ) (d L W : ℕ) [NeZero L]
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) :
    Γ.val d L W A x y = ∑ s : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![x, y] s) *
      (Γ.blue.map (blueF A (Sum.elim ![x, y] s))).prod := rfl

/-- In the invariant, a set of vertices avoiding the anchors is left by an edge of a tree rooted
at the anchors. -/
private theorem inv_tree {V : Type*} {E : List (V × V)}
    {A' : V → Prop} {q : V → V} {h ι : V → ℕ} (P : PD E A' q h ι) (U : V → Prop)
    (hU : ∃ u, U u) (hUA : ∀ u, U u → ¬ A' u) : ∃ e ∈ E, Cross e U := by
  obtain ⟨u, hu, hqu, -⟩ := P.exists_min U hU hUA
  obtain ⟨hi, hc⟩ := P.cross_idx (hUA u hu) hu hqu
  exact ⟨_, List.getElem_mem _, hc⟩

/-- [I, Claim 6.11], the maximum: `Γ̃_{xy} ≤ C c₁^ℓ μ B_{xy}` when each one-vertex sum
`Σ_z B_{zu} |A_j|` is at most `c₁` and `|A_j| ≤ μ ≤ 1`. -/
private theorem coreMax (d : ℕ) (hd : 2 ≤ d) {ℓ : ℕ} (Γ : AuxGraph ℓ) (hT : TreeEdges Γ.black)
    (hU : TreeEdges (Γ.blue.map fun e => (e.1, e.2.1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W →
      ∀ (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (c₁ μ : ℝ), 0 ≤ c₁ → μ ≤ 1 →
      (∀ j p u, ∑ z, bB d L W z u * |A j z p| ≤ c₁ ∧ ∑ z, bB d L W z u * |A j p z| ≤ c₁) →
      (∀ j p r, |A j p r| ≤ μ) →
      ∀ x y, Γ.val d L W A x y ≤ C * c₁ ^ ℓ * μ * bB d L W x y := by
  set X : Atom 2 ℓ := Sum.inl 0 with hX
  set Y : Atom 2 ℓ := Sum.inl 1 with hY
  have hYX : Y ≠ X := by simp [hX, hY]
  obtain ⟨qb, hb, ιb, Pb⟩ := PD.exists' Γ.black (· = X) (fun v => ⟨X, rfl, hT.2 v X⟩)
  obtain ⟨qu, hu, ιu, Pu⟩ := PD.exists' (bluePairs Γ.blue) (· = X) (fun v => ⟨X, rfl, hU.2 v X⟩)
  set m := Γ.black.length with hm
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hc
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hc0 : 0 ≤ c := by positivity
  refine ⟨(((m : ℝ) + 1) ^ 2 * c ^ m) ^ ℓ, by positivity,
    fun L W _ hW A c₁ μ hc₁ hμ1 hA1 hAμ x y => ?_⟩
  have hAone : ∀ j p r, |A j p r| ≤ 1 := fun j p r => (hAμ j p r).trans hμ1
  set dflt : Atom 2 ℓ × Atom 2 ℓ × ℕ := (X, X, 0) with hdflt
  set β : Atom 2 ℓ → (Atom 2 ℓ → Zd d L) → ℝ :=
    fun v g => blueF A g (Γ.blue.getD (ιu v) dflt) with hβ
  have hfilt : Finset.univ.filter (fun v : Atom 2 ℓ => ¬ v = X) = insert Y (intA ℓ) := by
    ext v
    cases v with
    | inl i =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        inl_notMem_intA, or_false, hX, hY, Sum.inl.injEq]
      exact ⟨fun h => fin2_eq (by decide) h, fun h => by rw [h]; decide⟩
    | inr k => simp [hX, inr_mem_intA]
  have hYint : Y ∉ intA ℓ := inl_notMem_intA 1
  have hblue : ∀ g : Atom 2 ℓ → Zd d L, (Γ.blue.map (blueF A g)).prod ≤
      μ * ∏ v ∈ intA ℓ, β v g := by
    intro g
    have h1 := blue_prod Pu A dflt hAone (Finset.univ.filter fun v => ¬ v = X)
      (fun v hv => (Finset.mem_filter.1 hv).2) g
    rw [hfilt, Finset.prod_insert hYint] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right (hAμ _ _ _)
      (Finset.prod_nonneg fun v _ => abs_nonneg _))
  set ψ : Atom 2 ℓ → Zd d L := Sum.elim ![x, y] (fun _ => x) with hψ
  have hstep : Γ.val d L W A x y ≤
      μ * sumS (intA ℓ) (stF d L W β X (intA ℓ) Γ.black none) ψ := by
    rw [val_eq, ← sum_atom, Finset.mul_sum]
    simp only [show ψ ∘ Sum.inl = ![x, y] from rfl]
    refine Finset.sum_le_sum fun s _ => ?_
    have := hblue (Sum.elim ![x, y] s)
    simp only [stF, boxF, mul_one]
    calc bProd d L W Γ.black (Sum.elim ![x, y] s) * (Γ.blue.map (blueF A
          (Sum.elim ![x, y] s))).prod
        ≤ bProd d L W Γ.black (Sum.elim ![x, y] s) * (μ * ∏ v ∈ intA ℓ, β v
          (Sum.elim ![x, y] s)) := mul_le_mul_of_nonneg_left this (bProd_nonneg _ _)
      _ = _ := by ring
  -- the hypotheses of `elim`
  have hAS : ∀ a, a = X → a ∉ intA ℓ := fun a ha => ha ▸ inl_notMem_intA 0
  have hint : ∀ v ∈ intA ℓ, ¬ v = X := fun v hv h => hAS v h hv
  have hβdep : ∀ w ∈ intA ℓ, ∀ v ∈ intA ℓ, w ≠ v → hu w ≤ hu v →
      ∀ g z, β w (Function.update g v z) = β w g := by
    intro w hw v _ hwv hle g z
    have hs := Pu.step w (hint w hw)
    exact blue_dep Pu A dflt (hint w hw) (Ne.symm hwv)
      (fun h => by rw [← h] at hs; omega) g z
  have hfull : ∀ v ∈ intA ℓ, ∀ (g : Atom 2 ℓ → Zd d L) (u : Zd d L),
      ∑ z, bB d L W z u * β v (Function.update g v z) ≤ c₁ := fun v hv g u =>
    blue_sum Pu A dflt (hint v hv) (fun z => bB d L W z u) c₁ (fun j p => hA1 j p u) g
  have hbox : ∀ v ∈ intA ℓ, ∀ (g : Atom 2 ℓ → Zd d L) (K : ℕ), L ≤ K →
      K ≤ 2 ^ (intA ℓ).card * L → 2 * K ≤ L →
      ∑ z, (if zdistInf d L (z - g X) ≤ K then (1 : ℝ) else 0) *
        β v (Function.update g v z) ≤ 0 := by
    intro v _ g K h1 _ h3
    have := NeZero.ne L
    omega
  have hfinal : ∀ E, Inv (intA ℓ) (· = X) L L ∅ E none →
      ∀ g, bProd d L W E g ≤ bB d L W (g X) (g Y) := by
    intro E I g
    obtain ⟨e, he, hce⟩ := I.anch (· = Y) ⟨Y, rfl⟩
      (fun u hu => ⟨Or.inl (hu ▸ hYint), hu ▸ hYX, fun K h => by simp at h⟩)
    have hE := I.edges e he
    have hleft : ∀ u, InR (intA ℓ) ∅ u → u ≠ Y → u = X := by
      intro u hu huY
      rcases hu with hu | hu
      · cases u with
        | inl i =>
          simp only [hX, hY, ne_eq, Sum.inl.injEq] at huY ⊢
          exact fin2_eq (by decide) huY
        | inr k => exact absurd (inr_mem_intA k) hu
      · exact absurd hu (Finset.notMem_empty _)
    have hbe : bB d L W (g e.1) (g e.2) = bB d L W (g X) (g Y) := by
      rcases hce with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, hleft _ hE.2 h2]; exact bB_comm' _ _
      · rw [h1, hleft _ hE.1 h2]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    unfold bProd
    rw [prod_map_eraseIdx _ _ i hi, hbe]
    calc bB d L W (g X) (g Y) * _ ≤ bB d L W (g X) (g Y) * 1 :=
          mul_le_mul_of_nonneg_left (prod_map_le_one _ _ (fun _ _ => bB_nonneg' _ _)
            (fun _ _ => bB_le_one hd hW _ _)) (bB_nonneg' _ _)
      _ = _ := mul_one _
  have hInv : Inv (intA ℓ) (· = X) L L (intA ℓ) Γ.black none := by
    exact ⟨fun e _ => ⟨inR_self _ _, inR_self _ _⟩,
      fun U hU hUA => inv_tree Pb U hU (fun u hu => (hUA u hu).2.1), fun z K h => by simp at h⟩
  have hel := elim hd hW (intA ℓ) (· = X) X rfl hAS hu β (fun v g => abs_nonneg _) hβdep c₁ 0
    hc₁ le_rfl L hfull hbox (fun g => bB d L W (g X) (g Y)) (fun g => bB_nonneg' _ _) hfinal m
    ℓ (intA ℓ) le_rfl (card_intA ℓ) Γ.black none le_rfl hInv ψ
  have hμ0 : 0 ≤ μ := (abs_nonneg _).trans (hAμ 0 0 0)
  calc Γ.val d L W A x y ≤ μ * sumS (intA ℓ) (stF d L W β X (intA ℓ) Γ.black none) ψ := hstep
    _ ≤ μ * ((((m : ℝ) + 1) ^ 2 * c ^ m) ^ ℓ * wt c₁ 0 (none : Option (Atom 2 ℓ × ℕ)) ℓ *
          bB d L W (ψ X) (ψ Y)) := mul_le_mul_of_nonneg_left hel hμ0
    _ = _ := by simp only [wt, hψ, hX, hY]; simp; ring

end Cores

section Lift
variable {V : Type*} {E : List (V × V)} {A : V → Prop} {q : V → V} {h ι : V → ℕ}

/-- The edges `E` on the vertices `Option V`. -/
private def liftE (E : List (V × V)) : List (Option V × Option V) :=
  E.map fun e => (some e.1, some e.2)

/-- The anchors `A` together with `none`. -/
private def liftA (A : V → Prop) (u : Option V) : Prop := u = none ∨ ∃ a, A a ∧ u = some a

private theorem PD.lift (P : PD E A q h ι) :
    PD (liftE E) (liftA A) (Option.map q) (fun u => u.elim 0 h) (fun u => u.elim 0 ι) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rcases hu with rfl | ⟨a, ha, rfl⟩
    · simp
    · simp [(P.anch a ha).1, (P.anch a ha).2]
  · cases u with
    | none => exact absurd (Or.inl rfl) hu
    | some v =>
      have hv : ¬ A v := fun h' => hu (Or.inr ⟨v, h', rfl⟩)
      simpa using P.step v hv
  · cases u with
    | none => exact absurd (Or.inl rfl) hu
    | some v =>
      have hv : ¬ A v := fun h' => hu (Or.inr ⟨v, h', rfl⟩)
      obtain ⟨hi, he⟩ := P.idx v hv
      refine ⟨by simpa [liftE] using hi, ?_⟩
      simp only [liftE, List.getElem_map, Option.elim, Option.map_some]
      rcases he with he | he <;> simp [he]

private theorem iterate_map_some (q : V → V) (v : V) :
    ∀ m, (Option.map q)^[m] (some v) = some (q^[m] v) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

end Lift

section CoreAvg

/-- [I, Claim 6.11], the ball averages: for `y` in a box of radius `K`, the sum of
`Γ̃_{xy} / B_{xy}` is at most `C c₁^ℓ cb`, when each one-vertex sum `Σ_z B_{zu} |A_j|` is at most
`c₁` and each box sum of `|A_j|` over a box of radius in `[K, 2^{ℓ+1} K]` is at most `cb`. The
external atom `X` is at `x`, the other one is summed over the box. -/
private theorem coreAvg (d : ℕ) (hd : 2 ≤ d) {ℓ : ℕ} (Γ : AuxGraph ℓ) (hT : TreeEdges Γ.black)
    (hU : TreeEdges (Γ.blue.map fun e => (e.1, e.2.1))) (X Y : Fin 2) (hXY : X ≠ Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W →
      ∀ (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (c₁ cb : ℝ) (K : ℕ), 0 ≤ c₁ → 0 ≤ cb →
      2 * K ≤ L →
      (∀ j p u, ∑ z, bB d L W z u * |A j z p| ≤ c₁ ∧ ∑ z, bB d L W z u * |A j p z| ≤ c₁) →
      (∀ j p x₀ K', K ≤ K' → K' ≤ 2 ^ (ℓ + 1) * K → 2 * K' ≤ L →
        ∑ z, (if zdistInf d L (z - x₀) ≤ K' then (1 : ℝ) else 0) * |A j z p| ≤ cb ∧
        ∑ z, (if zdistInf d L (z - x₀) ≤ K' then (1 : ℝ) else 0) * |A j p z| ≤ cb) →
      (∀ j p r, |A j p r| ≤ 1) →
      ∀ x x₀ : Zd d L, ∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
        ((∑ s : Fin ℓ → Zd d L,
          bProd d L W Γ.black (Sum.elim (fun i => if i = X then x else y) s) *
          (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod) /
          bB d L W x y) ≤ C * c₁ ^ ℓ * cb := by
  set Xa : Atom 2 ℓ := Sum.inl X with hXa
  set Ya : Atom 2 ℓ := Sum.inl Y with hYa
  have hYX : Ya ≠ Xa := by simp [hXa, hYa, Ne.symm hXY]
  obtain ⟨qb, hb, ιb, Pb⟩ := PD.exists' Γ.black (· = Xa) (fun v => ⟨Xa, rfl, hT.2 v Xa⟩)
  obtain ⟨qu, hu, ιu, Pu⟩ :=
    PD.exists' (bluePairs Γ.blue) (· = Xa) (fun v => ⟨Xa, rfl, hU.2 v Xa⟩)
  have hsurj := Pb.surj (by rw [hT.1])
  set H := hb Ya with hH
  set m := Γ.black.length with hm
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hc
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set M : ℝ := ((m : ℝ) + 1) ^ 2 * c ^ m with hM
  refine ⟨((H : ℝ) + 1) ^ ((d : ℝ) - 2) * H * M ^ (ℓ + 1), by positivity,
    fun L W _ hW A c₁ cb K hc₁ hcb hKL hA1 hAbox hAone x x₀ => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  -- the lifted parent data
  have Pb' := Pb.lift
  set Ub : List (Option (Atom 2 ℓ) × Option (Atom 2 ℓ) × ℕ) :=
    Γ.blue.map fun e => (some e.1, some e.2.1, e.2.2) with hUb
  have hUbp : bluePairs Ub = liftE (bluePairs Γ.blue) := by
    simp [bluePairs, liftE, hUb, List.map_map, Function.comp_def]
  have Pu' : PD (bluePairs Ub) (liftA (· = Xa)) (Option.map qu) (fun u => u.elim 0 hu)
      (fun u => u.elim 0 ιu) := hUbp ▸ Pu.lift
  set dflt : Option (Atom 2 ℓ) × Option (Atom 2 ℓ) × ℕ := (none, none, 0) with hdflt
  set β : Option (Atom 2 ℓ) → (Option (Atom 2 ℓ) → Zd d L) → ℝ :=
    fun v g => blueF A g (Ub.getD ((fun u => u.elim 0 ιu) v) dflt) with hβ
  set A' := liftA (fun v : Atom 2 ℓ => v = Xa) with hA'
  have hS₀A : ∀ v ∈ avgS ℓ X, ¬ A' v := by
    intro v hv hvA
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rcases hvA with h | ⟨a, ha, h⟩
    · exact absurd h (by simp)
    · simp only [Function.Embedding.some_apply, Option.some.injEq] at h
      exact (Finset.mem_filter.1 hw).2 (h.trans ha)
  have hAS : ∀ a, A' a → a ∉ avgS ℓ X := fun a ha h => hS₀A a h ha
  have hnone : A' none := Or.inl rfl
  have hcard : (avgS ℓ X).card = ℓ + 1 := by
    rw [avgS, Finset.card_map, Finset.filter_ne' Finset.univ, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, card_atom]
    omega
  -- the positions
  set ψ : Option (Atom 2 ℓ) → Zd d L := fun u => if u = none then x₀ else x with hψ
  have hlift : ∀ y s, (liftPos X ψ y s) ∘ some =
      Sum.elim (fun i => if i = X then x else y) s := by
    intro y s
    funext w
    cases w with
    | inl i => simp [liftPos, hψ]
    | inr k => rfl
  have hliftY : ∀ y s, liftPos X ψ y s (some Ya) = y := by
    intro y s; simp [liftPos, hYa, Ne.symm hXY]
  have hliftO : ∀ y s, liftPos X ψ y s none = x₀ := by
    intro y s; simp [liftPos, hψ]
  -- the elimination bound for each removed path edge
  have hj : ∀ j < H, sumS (avgS ℓ X) (stF d L W β none (avgS ℓ X)
      (liftE (Γ.black.eraseIdx (ιb (qb^[j] Ya)))) (some (some Ya, K))) ψ ≤
      M ^ (ℓ + 1) * (c₁ ^ ℓ * cb) := by
    intro j hjH
    have hsep := Pb'.sep_erase (fun i hi => by
      obtain ⟨u, hu', hui⟩ := hsurj i (by simpa [liftE] using hi)
      exact ⟨some u, fun h' => by
        rcases h' with h' | ⟨a, ha, h'⟩
        · simp at h'
        · simp only [Option.some.injEq] at h'; exact hu' (h'.trans ha), hui⟩)
      (some (qb^[j] Ya)) (fun h' => by
        rcases h' with h' | ⟨a, ha, h'⟩
        · simp at h'
        · simp only [Option.some.injEq] at h'
          exact Pb.not_anch_iter Ya hjH (h'.trans ha))
    have hiter : (Option.map qb)^[j] (some Ya) = some (qb^[j] Ya) := iterate_map_some qb Ya j
    have hE : liftE (Γ.black.eraseIdx (ιb (qb^[j] Ya))) =
        (liftE Γ.black).eraseIdx ((fun u => u.elim 0 ιb) (some (qb^[j] Ya))) := by
      simp [liftE, List.eraseIdx_map]
    have hInv : Inv (avgS ℓ X) A' L K (avgS ℓ X) (liftE (Γ.black.eraseIdx (ιb (qb^[j] Ya))))
        (some (some Ya, K)) := by
      refine ⟨fun e _ => ⟨inR_self _ _, inR_self _ _⟩, fun U hU hUA => ?_, fun z K' hz => ?_⟩
      · have hk : j < (fun u => u.elim 0 hb) (some Ya) := hjH
        obtain ⟨e, he, hce⟩ := Pb'.anch_erase (some Ya) hk U hU (fun u hu' =>
          ⟨(hUA u hu').2.1, fun h' => (hUA u hu').2.2 K (by rw [h'])⟩)
        rw [hiter] at he
        exact ⟨e, hE ▸ he, hce⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hz
        obtain ⟨rfl, rfl⟩ := hz
        refine ⟨Finset.mem_map.2 ⟨Ya, Finset.mem_filter.2 ⟨Finset.mem_univ _, hYX⟩, rfl⟩, le_rfl,
          by simp, hKL,
          fun u => ∃ m, (Option.map qb)^[m] u = some (qb^[j] Ya), ⟨j, hiter⟩, ?_, ?_⟩
        · intro u hu'
          have hnA := hsep.1 u hu'
          cases u with
          | none => exact absurd (Or.inl rfl) hnA
          | some v =>
            refine Finset.mem_map.2 ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h' => ?_⟩, rfl⟩
            exact hnA (Or.inr ⟨v, h', rfl⟩)
        · intro e he
          exact hsep.2 e (hE ▸ he)
    have hdep : ∀ w ∈ avgS ℓ X, ∀ v ∈ avgS ℓ X, w ≠ v →
        (fun u => u.elim 0 hu) w ≤ (fun u => u.elim 0 hu) v →
        ∀ g z, β w (Function.update g v z) = β w g := by
      intro w hw v _ hwv hle g z
      have hs := Pu'.step w (hS₀A w hw)
      exact blue_dep Pu' A dflt (hS₀A w hw) (Ne.symm hwv)
        (fun h' => by subst h'; simp only at hs hle; omega) g z
    have hfull : ∀ v ∈ avgS ℓ X, ∀ (g : Option (Atom 2 ℓ) → Zd d L) (u : Zd d L),
        ∑ z, bB d L W z u * β v (Function.update g v z) ≤ c₁ := fun v hv g u =>
      blue_sum Pu' A dflt (hS₀A v hv) (fun z => bB d L W z u) c₁ (fun j p => hA1 j p u) g
    have hbox : ∀ v ∈ avgS ℓ X, ∀ (g : Option (Atom 2 ℓ) → Zd d L) (K' : ℕ), K ≤ K' →
        K' ≤ 2 ^ (avgS ℓ X).card * K → 2 * K' ≤ L →
        ∑ z, (if zdistInf d L (z - g none) ≤ K' then (1 : ℝ) else 0) *
          β v (Function.update g v z) ≤ cb := by
      intro v hv g K' h1 h2 h3
      rw [hcard] at h2
      exact blue_sum Pu' A dflt (hS₀A v hv) _ cb (fun j p => hAbox j p (g none) K' h1 h2 h3) g
    have hel := elim hd hW (avgS ℓ X) A' none hnone hAS (fun u => u.elim 0 hu) β
      (fun v g => abs_nonneg _) hdep c₁ cb hc₁ hcb K hfull hbox (fun _ => 1)
      (fun _ => zero_le_one) (fun E _ g => bProd_le_one hd hW E g) m (ℓ + 1) (avgS ℓ X) le_rfl
      hcard _ (some (some Ya, K))
      (by simp only [liftE, List.length_map]; exact List.length_eraseIdx_le _ _) hInv ψ
    simpa [wt] using hel
  -- the path decomposition of `B` over the black edges
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have hpath : ∀ y (s : Fin ℓ → Zd d L),
      bProd d L W Γ.black (Sum.elim (fun i => if i = X then x else y) s) ≤
        ((H : ℝ) + 1) ^ ((d : ℝ) - 2) * bB d L W x y * ∑ j ∈ Finset.range H,
          bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya)))
            (Sum.elim (fun i => if i = X then x else y) s) := by
    intro y s
    set g := Sum.elim (fun i => if i = X then x else y) s with hg
    have hgX : g Xa = x := by simp [hg, hXa]
    have hgY : g Ya = y := by simp [hg, hYa, Ne.symm hXY]
    have h := Pb.path_prod hW Ya hYX g ((W : ℝ) ^ (-2 : ℝ)) ((d : ℝ) - 2) (by positivity) hd2
    have e1 : ∀ E : List (Atom 2 ℓ × Atom 2 ℓ), bProd d L W E g =
        (E.map fun e => (W : ℝ) ^ (-2 : ℝ) * brk d L W (g e.1) (g e.2) ^ (-((d : ℝ) - 2))).prod :=
      fun E => by unfold bProd; simp only [bB_eq_brk]
    have hB : (W : ℝ) ^ (-2 : ℝ) * brk d L W (g Xa) (g Ya) ^ (-((d : ℝ) - 2)) = bB d L W x y := by
      rw [hgX, hgY, bB_eq_brk]
    rw [hB] at h
    simp only [e1]
    exact h
  have hjsum : ∀ j < H, ∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
      ∑ s : Fin ℓ → Zd d L,
        bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya)))
          (Sum.elim (fun i => if i = X then x else y) s) *
        (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod ≤
      M ^ (ℓ + 1) * (c₁ ^ ℓ * cb) := by
    intro j hjH
    refine le_trans ?_ (hj j hjH)
    rw [sum_opt hXY]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    set g' := liftPos X ψ y s with hg'
    have hb' : bProd d L W (liftE (Γ.black.eraseIdx (ιb (qb^[j] Ya)))) g' =
        bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya))) (g' ∘ some) := by
      unfold bProd liftE; rw [List.map_map]; rfl
    have hu' : (Ub.map (blueF A g')).prod = (Γ.blue.map (blueF A (g' ∘ some))).prod := by
      rw [hUb, List.map_map]; rfl
    have hbl := blue_prod Pu' A dflt hAone (avgS ℓ X) hS₀A g'
    rw [hu'] at hbl
    have hbx : boxF d L none (some (some Ya, K)) g' =
        if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0 := by
      simp only [boxF, hg', hliftY, hliftO]
    simp only [stF, hb', hbx, ← hlift y s]
    have h0 := bProd_nonneg (W := W) (Γ.black.eraseIdx (ιb (qb^[j] Ya))) (g' ∘ some)
    have h1 : (0 : ℝ) ≤ if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0 := by
      split_ifs <;> norm_num
    calc (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
          (bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya))) (g' ∘ some) *
            (Γ.blue.map (blueF A (g' ∘ some))).prod)
        ≤ (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
          (bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya))) (g' ∘ some) *
            ∏ v ∈ avgS ℓ X, β v g') :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbl h0) h1
      _ = _ := by ring
  have hB0 : 0 < bB d L W x x₀ := bB_pos' hW _ _
  calc ∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
        ((∑ s : Fin ℓ → Zd d L,
          bProd d L W Γ.black (Sum.elim (fun i => if i = X then x else y) s) *
          (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod) /
          bB d L W x y)
      ≤ ∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
        (((H : ℝ) + 1) ^ ((d : ℝ) - 2) * ∑ j ∈ Finset.range H, ∑ s : Fin ℓ → Zd d L,
          bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya)))
            (Sum.elim (fun i => if i = X then x else y) s) *
          (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod) := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> norm_num)
        have hBy := bB_pos' (L := L) hW x y
        rw [div_le_iff₀ hBy, Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun s _ => ?_
        have hbl0 :
            0 ≤ (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod :=
          prod_map_nonneg _ _ fun _ _ => abs_nonneg _
        calc bProd d L W Γ.black (Sum.elim (fun i => if i = X then x else y) s) *
              (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod
            ≤ (((H : ℝ) + 1) ^ ((d : ℝ) - 2) * bB d L W x y * ∑ j ∈ Finset.range H,
              bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya)))
                (Sum.elim (fun i => if i = X then x else y) s)) *
              (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod :=
              mul_le_mul_of_nonneg_right (hpath y s) hbl0
          _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
                      refine Finset.sum_congr rfl fun j _ => ?_; ring
    _ = ((H : ℝ) + 1) ^ ((d : ℝ) - 2) * ∑ j ∈ Finset.range H,
        ∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
        ∑ s : Fin ℓ → Zd d L,
          bProd d L W (Γ.black.eraseIdx (ιb (qb^[j] Ya)))
            (Sum.elim (fun i => if i = X then x else y) s) *
          (Γ.blue.map (blueF A (Sum.elim (fun i => if i = X then x else y) s))).prod := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ((H : ℝ) + 1) ^ ((d : ℝ) - 2) * ∑ j ∈ Finset.range H, M ^ (ℓ + 1) * (c₁ ^ ℓ * cb) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj' =>
          hjsum j (Finset.mem_range.1 hj')) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end CoreAvg

section CoreStrong

/-- Summing the internal atoms of an auxiliary graph whose black edges contain a spanning tree
rooted at `x = 0`: at most `M^ℓ c₁^ℓ B_{xy}`, when each one-vertex sum is at most `c₁`. -/
private theorem treeElim (d : ℕ) (hd : 2 ≤ d) {ℓ : ℕ} (T : List (Atom 2 ℓ × Atom 2 ℓ))
    {qb : Atom 2 ℓ → Atom 2 ℓ} {hb ιb : Atom 2 ℓ → ℕ} (Pb : PD T (· = Sum.inl 0) qb hb ιb)
    {L W : ℕ} [NeZero L] (hW : 1 ≤ W) (rk : Atom 2 ℓ → ℕ)
    (β : Atom 2 ℓ → (Atom 2 ℓ → Zd d L) → ℝ) (hβ0 : ∀ v g, 0 ≤ β v g)
    (hβdep : ∀ w ∈ intA ℓ, ∀ v ∈ intA ℓ, w ≠ v → rk w ≤ rk v →
      ∀ g z, β w (Function.update g v z) = β w g)
    (c₁ : ℝ) (hc₁ : 0 ≤ c₁)
    (hfull : ∀ v ∈ intA ℓ, ∀ (g : Atom 2 ℓ → Zd d L) (u : Zd d L),
      ∑ z, bB d L W z u * β v (Function.update g v z) ≤ c₁)
    (ψ : Atom 2 ℓ → Zd d L) :
    sumS (intA ℓ) (stF d L W β (Sum.inl 0) (intA ℓ) T none) ψ ≤
      (((T.length : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ ((d : ℝ) - 2)) ^ T.length) ^ ℓ * c₁ ^ ℓ *
        bB d L W (ψ (Sum.inl 0)) (ψ (Sum.inl 1)) := by
  set X : Atom 2 ℓ := Sum.inl 0 with hX
  set Y : Atom 2 ℓ := Sum.inl 1 with hY
  have hYX : Y ≠ X := by simp [hX, hY]
  have hYint : Y ∉ intA ℓ := inl_notMem_intA 1
  have hAS : ∀ a, a = X → a ∉ intA ℓ := fun a ha => ha ▸ inl_notMem_intA 0
  have hbox : ∀ v ∈ intA ℓ, ∀ (g : Atom 2 ℓ → Zd d L) (K : ℕ), L ≤ K →
      K ≤ 2 ^ (intA ℓ).card * L → 2 * K ≤ L →
      ∑ z, (if zdistInf d L (z - g X) ≤ K then (1 : ℝ) else 0) *
        β v (Function.update g v z) ≤ 0 := by
    intro v _ g K h1 _ h3
    have := NeZero.ne L
    omega
  have hfinal : ∀ E, Inv (intA ℓ) (· = X) L L ∅ E none →
      ∀ g, bProd d L W E g ≤ bB d L W (g X) (g Y) := by
    intro E I g
    obtain ⟨e, he, hce⟩ := I.anch (· = Y) ⟨Y, rfl⟩
      (fun u hu => ⟨Or.inl (hu ▸ hYint), hu ▸ hYX, fun K h => by simp at h⟩)
    have hE := I.edges e he
    have hleft : ∀ u, InR (intA ℓ) ∅ u → u ≠ Y → u = X := by
      intro u hu huY
      rcases hu with hu | hu
      · cases u with
        | inl i =>
          simp only [hX, hY, ne_eq, Sum.inl.injEq] at huY ⊢
          exact fin2_eq (by decide) huY
        | inr k => exact absurd (inr_mem_intA k) hu
      · exact absurd hu (Finset.notMem_empty _)
    have hbe : bB d L W (g e.1) (g e.2) = bB d L W (g X) (g Y) := by
      rcases hce with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, hleft _ hE.2 h2]; exact bB_comm' _ _
      · rw [h1, hleft _ hE.1 h2]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    unfold bProd
    rw [prod_map_eraseIdx _ _ i hi, hbe]
    calc bB d L W (g X) (g Y) * _ ≤ bB d L W (g X) (g Y) * 1 :=
          mul_le_mul_of_nonneg_left (prod_map_le_one _ _ (fun _ _ => bB_nonneg' _ _)
            (fun _ _ => bB_le_one hd hW _ _)) (bB_nonneg' _ _)
      _ = _ := mul_one _
  have hInv : Inv (intA ℓ) (· = X) L L (intA ℓ) T none :=
    ⟨fun e _ => ⟨inR_self _ _, inR_self _ _⟩,
      fun U hU hUA => inv_tree Pb U hU (fun u hu => (hUA u hu).2.1), fun z K h => by simp at h⟩
  have hel := elim hd hW (intA ℓ) (· = X) X rfl hAS rk β hβ0 hβdep c₁ 0
    hc₁ le_rfl L hfull hbox (fun g => bB d L W (g X) (g Y)) (fun g => bB_nonneg' _ _) hfinal
    T.length ℓ (intA ℓ) le_rfl (card_intA ℓ) T none le_rfl hInv ψ
  simpa [wt] using hel

/-- [I, Claim 6.11], strong form: `Γ̃_{xy} ≤ C c₁^ℓ W^{-b} ⟨x - y⟩^{-s} B_{xy}` when
`|A_j(p, r)| ≤ W^{-b} ⟨p - r⟩^{-s}` and each one-vertex sum `Σ_z B_{zu} W^{-b} ⟨z - p⟩^{-s}` is at
most `c₁`. -/
private theorem coreStrong (d : ℕ) (hd : 2 ≤ d) (b s : ℝ) (hb : 0 ≤ b) (hs : 0 ≤ s) {ℓ : ℕ}
    (Γ : AuxGraph ℓ) (hT : TreeEdges Γ.black)
    (hU : TreeEdges (Γ.blue.map fun e => (e.1, e.2.1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L W : ℕ) [NeZero L], 1 ≤ W →
      ∀ (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (c₁ : ℝ), 0 ≤ c₁ →
      (∀ p u : Zd d L, ∑ z, bB d L W z u * ((W : ℝ) ^ (-b) * brk d L W z p ^ (-s)) ≤ c₁) →
      (∀ j p r, |A j p r| ≤ (W : ℝ) ^ (-b) * brk d L W p r ^ (-s)) →
      ∀ x y, Γ.val d L W A x y ≤
        C * c₁ ^ ℓ * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-s)) * bB d L W x y := by
  set X : Atom 2 ℓ := Sum.inl 0 with hX
  set Y : Atom 2 ℓ := Sum.inl 1 with hY
  have hYX : Y ≠ X := by simp [hX, hY]
  obtain ⟨qb, hb', ιb, Pb⟩ := PD.exists' Γ.black (· = X) (fun v => ⟨X, rfl, hT.2 v X⟩)
  obtain ⟨qu, hu, ιu, Pu⟩ :=
    PD.exists' (bluePairs Γ.blue) (· = X) (fun v => ⟨X, rfl, hU.2 v X⟩)
  set H := hu Y with hH
  -- the blue forests after removing one edge of the path from `y` to `x`
  have hreach : ∀ j < H, ∀ v, ∃ a, (a = X ∨ a = Y) ∧
      (SimpleGraph.fromRel fun a c => (a, c) ∈
        (bluePairs Γ.blue).eraseIdx (ιu (qu^[j] Y))).Reachable v a := by
    intro j hj v
    classical
    have hwA : ¬ qu^[j] Y = X := Pu.not_anch_iter Y hj
    by_cases hex : ∃ m, qu^[m] v = qu^[j] Y
    · refine ⟨Y, Or.inr rfl, ?_⟩
      have h1 : (SimpleGraph.fromRel fun a c => (a, c) ∈
          (bluePairs Γ.blue).eraseIdx (ιu (qu^[j] Y))).Reachable v (qu^[Nat.find hex] v) := by
        refine Pu.reach_iter _ v _ fun i hi => ?_
        have hne : qu^[i] v ≠ qu^[j] Y := Nat.find_min hex hi
        have hA : ¬ qu^[i] v = X := by
          intro hA
          have := Nat.find_spec hex
          rw [show Nat.find hex = (Nat.find hex - i) + i by omega, Function.iterate_add_apply,
            hA, Pu.iter_anch rfl] at this
          exact hwA this.symm
        exact ⟨hA, fun h' => hne (Pu.inj hA hwA h')⟩
      have h2 : (SimpleGraph.fromRel fun a c => (a, c) ∈
          (bluePairs Γ.blue).eraseIdx (ιu (qu^[j] Y))).Reachable Y (qu^[j] Y) := by
        refine Pu.reach_iter _ Y _ fun i hi => ?_
        have hA : ¬ qu^[i] Y = X := Pu.not_anch_iter Y (by omega)
        refine ⟨hA, fun h' => ?_⟩
        have he := Pu.inj hA hwA h'
        have e1 := Pu.iter Y i (by omega)
        have e2 := Pu.iter Y j (by omega)
        rw [he] at e1
        omega
      rw [Nat.find_spec hex] at h1
      exact h1.trans h2.symm
    · push Not at hex
      refine ⟨X, Or.inl rfl, ?_⟩
      have h1 := Pu.reach_iter (ιu (qu^[j] Y)) v (hu v) fun i hi => by
        have hA : ¬ qu^[i] v = X := Pu.not_anch_iter v hi
        exact ⟨hA, fun h' => hex i (Pu.inj hA hwA h')⟩
      have hX' : qu^[hu v] v = X := (Pu.zero_iff _).1 (by rw [Pu.iter v (hu v) le_rfl]; simp)
      rw [hX'] at h1
      exact h1
  have hPD : ∀ j, ∃ (q' : Atom 2 ℓ → Atom 2 ℓ) (h' ι' : Atom 2 ℓ → ℕ), j < H →
      PD (bluePairs (Γ.blue.eraseIdx (ιu (qu^[j] Y)))) (fun a => a = X ∨ a = Y) q' h' ι' := by
    intro j
    by_cases hj : j < H
    · obtain ⟨q', h', ι', P'⟩ := PD.exists' _ _ (hreach j hj)
      refine ⟨q', h', ι', fun _ => ?_⟩
      have e : bluePairs (Γ.blue.eraseIdx (ιu (qu^[j] Y))) =
          (bluePairs Γ.blue).eraseIdx (ιu (qu^[j] Y)) := by
        simp [bluePairs, List.eraseIdx_map]
      rw [e]; exact P'
    · exact ⟨id, fun _ => 0, fun _ => 0, fun h' => absurd h' hj⟩
  choose q' h' ι' hP' using hPD
  set m := Γ.black.length with hm
  set c : ℝ := (2 : ℝ) ^ ((d : ℝ) - 2) with hc
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set M : ℝ := ((m : ℝ) + 1) ^ 2 * c ^ m with hM
  refine ⟨((H : ℝ) + 1) ^ s * H * M ^ ℓ, by positivity,
    fun L W _ hW A c₁ hc₁ hS hAS x y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  set Sf : ℕ → Matrix (Zd d L) (Zd d L) ℝ := fun _ p r => (W : ℝ) ^ (-b) * brk d L W p r ^ (-s)
    with hSf
  have hSf0 : ∀ j p r, 0 ≤ Sf j p r := fun j p r => by
    have := brk_pos (L := L) hW p r; simp only [hSf]; positivity
  have hSf1 : ∀ j p r, |Sf j p r| ≤ 1 := fun j p r => by
    rw [abs_of_nonneg (hSf0 j p r)]
    have hb1 := hW1.trans (W_le_brk (L := L) (W := W) p r)
    calc (W : ℝ) ^ (-b) * brk d L W p r ^ (-s) ≤ 1 * 1 :=
          mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
            (Real.rpow_le_one_of_one_le_of_nonpos hb1 (by linarith)) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  set ψ : Atom 2 ℓ → Zd d L := Sum.elim ![x, y] (fun _ => x) with hψ
  set dflt : Atom 2 ℓ × Atom 2 ℓ × ℕ := (X, X, 0) with hdflt
  -- each forest
  have hj : ∀ j < H, ∑ t : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![x, y] t) *
      ((Γ.blue.eraseIdx (ιu (qu^[j] Y))).map (blueF Sf (Sum.elim ![x, y] t))).prod ≤
      M ^ ℓ * c₁ ^ ℓ * bB d L W x y := by
    intro j hjH
    have P' := hP' j hjH
    set Ub := Γ.blue.eraseIdx (ιu (qu^[j] Y)) with hUb
    set β : Atom 2 ℓ → (Atom 2 ℓ → Zd d L) → ℝ :=
      fun v g => blueF Sf g (Ub.getD (ι' j v) dflt) with hβ
    have hint : ∀ v ∈ intA ℓ, ¬ (v = X ∨ v = Y) := by
      intro v hv h''
      rcases h'' with h'' | h'' <;> rw [h''] at hv <;> exact inl_notMem_intA _ hv
    have hdep : ∀ w ∈ intA ℓ, ∀ v ∈ intA ℓ, w ≠ v → h' j w ≤ h' j v →
        ∀ g z, β w (Function.update g v z) = β w g := by
      intro w hw v _ hwv hle g z
      have hs' := P'.step w (hint w hw)
      exact blue_dep P' Sf dflt (hint w hw) (Ne.symm hwv)
        (fun h'' => by rw [← h''] at hs'; omega) g z
    have hfull : ∀ v ∈ intA ℓ, ∀ (g : Atom 2 ℓ → Zd d L) (u : Zd d L),
        ∑ z, bB d L W z u * β v (Function.update g v z) ≤ c₁ := by
      intro v hv g u
      refine blue_sum P' Sf dflt (hint v hv) (fun z => bB d L W z u) c₁ (fun i p => ?_) g
      constructor
      · calc ∑ z, bB d L W z u * |Sf i z p| =
              ∑ z, bB d L W z u * ((W : ℝ) ^ (-b) * brk d L W z p ^ (-s)) :=
              Finset.sum_congr rfl fun z _ => by rw [abs_of_nonneg (hSf0 i z p)]
          _ ≤ c₁ := hS p u
      · calc ∑ z, bB d L W z u * |Sf i p z| =
              ∑ z, bB d L W z u * ((W : ℝ) ^ (-b) * brk d L W z p ^ (-s)) :=
              Finset.sum_congr rfl fun z _ => by
                rw [abs_of_nonneg (hSf0 i p z)]; simp only [hSf]; rw [brk_comm]
          _ ≤ c₁ := hS p u
    have hel := treeElim d hd Γ.black Pb hW (h' j) β (fun v g => abs_nonneg _) hdep c₁ hc₁
      hfull ψ
    rw [← sum_atom] at hel
    simp only [show ψ ∘ Sum.inl = ![x, y] from rfl] at hel
    refine le_trans (Finset.sum_le_sum fun t _ => ?_) hel
    simp only [stF, boxF, mul_one]
    exact mul_le_mul_of_nonneg_left (blue_prod P' Sf dflt hSf1 (intA ℓ) hint _)
      (bProd_nonneg _ _)
  -- the path decomposition of the blue edges
  have hbl : ∀ t : Fin ℓ → Zd d L, (Γ.blue.map (blueF A (Sum.elim ![x, y] t))).prod ≤
      ((H : ℝ) + 1) ^ s * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-s)) *
        ∑ j ∈ Finset.range H,
          ((Γ.blue.eraseIdx (ιu (qu^[j] Y))).map (blueF Sf (Sum.elim ![x, y] t))).prod := by
    intro t
    set g := Sum.elim ![x, y] t with hg
    have h1 : (Γ.blue.map (blueF A g)).prod ≤ (Γ.blue.map (blueF Sf g)).prod := by
      have := prod_map_le_pow Γ.blue (blueF A g) (blueF Sf g) 1 zero_le_one
        (fun e _ => ⟨abs_nonneg _, abs_nonneg _, by
          rw [one_mul]; unfold blueF; rw [abs_of_nonneg (hSf0 e.2.2 _ _)]; exact hAS _ _ _⟩)
      simpa using this
    have e1 : ∀ l : List (Atom 2 ℓ × Atom 2 ℓ × ℕ), (l.map (blueF Sf g)).prod =
        ((bluePairs l).map fun e => (W : ℝ) ^ (-b) * brk d L W (g e.1) (g e.2) ^ (-s)).prod := by
      intro l
      unfold bluePairs blueF
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun e _ => ?_
      rw [abs_of_nonneg (hSf0 e.2.2 _ _)]
      rfl
    have h2 := Pu.path_prod hW Y hYX g ((W : ℝ) ^ (-b)) s (by positivity) hs
    have hgX : g X = x := rfl
    have hgY : g Y = y := rfl
    rw [hgX, hgY] at h2
    refine h1.trans ?_
    rw [e1]
    refine h2.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e1]
    simp [bluePairs, List.eraseIdx_map]
  calc Γ.val d L W A x y = ∑ t : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![x, y] t) *
        (Γ.blue.map (blueF A (Sum.elim ![x, y] t))).prod := val_eq Γ d L W A x y
    _ ≤ ∑ t : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![x, y] t) *
        (((H : ℝ) + 1) ^ s * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-s)) *
        ∑ j ∈ Finset.range H,
          ((Γ.blue.eraseIdx (ιu (qu^[j] Y))).map (blueF Sf (Sum.elim ![x, y] t))).prod) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hbl t) (bProd_nonneg _ _)
    _ = ((H : ℝ) + 1) ^ s * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-s)) *
        ∑ j ∈ Finset.range H, ∑ t : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![x, y] t) *
          ((Γ.blue.eraseIdx (ιu (qu^[j] Y))).map (blueF Sf (Sum.elim ![x, y] t))).prod := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => by ring
    _ ≤ ((H : ℝ) + 1) ^ s * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-s)) *
        ∑ j ∈ Finset.range H, M ^ ℓ * c₁ ^ ℓ * bB d L W x y := by
        have := brk_pos (L := L) hW x y
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj' =>
          hj j (Finset.mem_range.1 hj')) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end CoreStrong

section Asymptotics

/-- Along `adm(c₀, c₁)` and for `W ≥ W₀`: `W ≥ 1`, `L ≥ 2W`, and
`C (log₂(L/W) + 2)^m ≤ W^τ`, for `C ≥ 0` and `τ > 0`. -/
private theorem adm_eventually (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (C : ℝ) (hC : 0 ≤ C)
    (m : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ), (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → 1 ≤ L →
      1 ≤ W ∧ 2 * W ≤ L ∧ C * logF L W ^ m ≤ (W : ℝ) ^ τ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a' : ℝ := (1 / c₁ + 2) / Real.log 2 with ha'
  have ha'0 : 0 ≤ a' := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hτ).const_mul_left (C * a' ^ m)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 (hlo.bound zero_lt_one)
  refine ⟨max (max 3 X₀) ((2 : ℝ) ^ ((1 - c₀) / c₀)), fun W L hadm hW hL => ?_⟩
  have hW3 : (3 : ℝ) ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWX : X₀ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW2c : (2 : ℝ) ^ ((1 - c₀) / c₀) ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨h1, h2⟩ := hadm
  simp only at h1 h2
  have hc01 : c₀ < 1 := by
    by_contra h
    have : (L : ℝ) ^ (1 - c₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    linarith
  have hLW : (W : ℝ) ^ (1 / (1 - c₀)) ≤ L := by
    calc (W : ℝ) ^ (1 / (1 - c₀)) ≤ ((L : ℝ) ^ (1 - c₀)) ^ (1 / (1 - c₀)) :=
          Real.rpow_le_rpow hW0.le h2 (by have h' : 0 < 1 - c₀ := (by linarith); positivity)
      _ = L := by
          rw [← Real.rpow_mul (by linarith), mul_one_div_cancel (by linarith), Real.rpow_one]
  have h2W : 2 * (W : ℝ) ≤ (W : ℝ) ^ (1 / (1 - c₀)) := by
    have e : (W : ℝ) ^ (1 / (1 - c₀)) = (W : ℝ) ^ (1 : ℝ) * (W : ℝ) ^ (c₀ / (1 - c₀)) := by
      rw [← Real.rpow_add hW0]; congr 1; field_simp; linarith
    have h3 : (2 : ℝ) ≤ (W : ℝ) ^ (c₀ / (1 - c₀)) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ ((1 - c₀) / c₀)) ^ (c₀ / (1 - c₀)) := by
            rw [← Real.rpow_mul (by norm_num)]
            rw [show (1 - c₀) / c₀ * (c₀ / (1 - c₀)) = 1 by field_simp]
            simp
        _ ≤ (W : ℝ) ^ (c₀ / (1 - c₀)) :=
            Real.rpow_le_rpow (by positivity) hW2c
              (by have h' : 0 < 1 - c₀ := (by linarith); positivity)
    rw [e, Real.rpow_one]
    nlinarith
  have hWL : 2 * W ≤ L := by exact_mod_cast h2W.trans hLW
  refine ⟨by exact_mod_cast (by linarith : (1 : ℝ) ≤ W), hWL, ?_⟩
  have hLle : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
    calc (L : ℝ) = ((L : ℝ) ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ (1 / c₁) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hlogW : Real.log 2 ≤ Real.log W := Real.log_le_log (by norm_num) (by linarith)
  have hlogF : logF L W ≤ a' * Real.log W := by
    unfold logF Real.logb
    have hLW0 : (0 : ℝ) < (L : ℝ) / W := by positivity
    have e1 : Real.log ((L : ℝ) / W) ≤ Real.log L := by
      rw [Real.log_div (by positivity) hW0.ne']
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ W)]
    have e2 : Real.log L ≤ (1 / c₁) * Real.log W := by
      calc Real.log L ≤ Real.log ((W : ℝ) ^ (1 / c₁)) := Real.log_le_log (by positivity) hLle
        _ = _ := Real.log_rpow hW0 _
    have e3 : Real.log ((L : ℝ) / W) / Real.log 2 ≤ (1 / c₁) * Real.log W / Real.log 2 :=
      div_le_div_of_nonneg_right (e1.trans e2) hl2.le
    have e4 : (2 : ℝ) ≤ 2 * Real.log W / Real.log 2 := by
      rw [le_div_iff₀ hl2]; linarith
    calc Real.log ((L : ℝ) / W) / Real.log 2 + 2
        ≤ (1 / c₁) * Real.log W / Real.log 2 + 2 * Real.log W / Real.log 2 := by linarith
      _ = a' * Real.log W := by rw [ha']; ring
  have hlogF0 : 0 ≤ logF L W := logF_nonneg' (by exact_mod_cast (by linarith : (1 : ℝ) ≤ W))
    (by omega)
  have hlog0 : 0 ≤ Real.log W := le_trans hl2.le hlogW
  have key := hX₀ W hWX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), one_mul, Real.rpow_natCast] at key
  calc C * logF L W ^ m ≤ C * (a' * Real.log W) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogF0 hlogF m) hC
    _ = C * a' ^ m * Real.log W ^ m := by rw [mul_pow, mul_assoc]
    _ ≤ _ := key

end Asymptotics

section Main

private theorem val_nonneg {ℓ : ℕ} (Γ : AuxGraph ℓ) (d L W : ℕ) [NeZero L]
    (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) : 0 ≤ Γ.val d L W A x y := by
  rw [val_eq]
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (bProd_nonneg _ _) (prod_map_nonneg _ _ fun _ _ => abs_nonneg _)

private theorem normVal_nonneg {ℓ : ℕ} (Γ : AuxGraph ℓ) (d L W : ℕ) [NeZero L] (hW : 1 ≤ W)
    (a : ℝ) (A : ℕ → Matrix (Zd d L) (Zd d L) ℝ) (x y : Zd d L) :
    0 ≤ Γ.normVal d L W a A x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold AuxGraph.normVal
  exact div_nonneg (mul_nonneg (by positivity) (val_nonneg Γ d L W A x y))
    (bB_pos' hW x y).le

private theorem W_pow_cancel {W : ℝ} (hW0 : 0 < W) (a : ℝ) (ℓ d : ℕ) :
    W ^ (a * ℓ * d / 2) * (W ^ (-(a * d / 2))) ^ ℓ = 1 := by
  rw [← Real.rpow_mul_natCast hW0.le, ← Real.rpow_add hW0,
    show a * ℓ * d / 2 + -(a * d / 2) * ℓ = 0 by ring, Real.rpow_zero]

private theorem box_alg {W K : ℝ} (hW : 0 < W) (hK : 0 < K) (b t : ℝ) (d : ℕ) :
    (W / K) ^ b * K ^ t * (W ^ (-b) * K ^ ((d : ℝ) - (t - b))) / K ^ d = 1 := by
  have e1 : K ^ t * K ^ ((d : ℝ) - (t - b)) = K ^ b * K ^ d := by
    rw [← Real.rpow_add hK, ← Real.rpow_natCast, ← Real.rpow_add hK]; congr 1; ring
  rw [Real.div_rpow hW.le hK.le, Real.rpow_neg hW.le]
  have h1 : 0 < W ^ b := by positivity
  have h2 : 0 < K ^ b := by positivity
  have h3 : 0 < K ^ d := by positivity
  calc W ^ b / K ^ b * K ^ t * ((W ^ b)⁻¹ * K ^ ((d : ℝ) - (t - b))) / K ^ d
      = W ^ b / K ^ b * (W ^ b)⁻¹ * (K ^ t * K ^ ((d : ℝ) - (t - b))) / K ^ d := by ring
    _ = 1 := by rw [e1]; field_simp

private theorem strong_alg {W t : ℝ} (hW : 0 < W) (ht : 0 < t) (b u : ℝ) :
    (W / t) ^ b * t ^ u * (W ^ (-b) * t ^ (-(u - b))) = 1 := by
  have e1 : t ^ u * t ^ (-(u - b)) = t ^ b := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [Real.div_rpow hW.le ht.le, Real.rpow_neg hW.le]
  have h1 : 0 < W ^ b := by positivity
  have h2 : 0 < t ^ b := by positivity
  calc W ^ b / t ^ b * t ^ u * ((W ^ b)⁻¹ * t ^ (-(u - b)))
      = W ^ b / t ^ b * (W ^ b)⁻¹ * (t ^ u * t ^ (-(u - b))) := by ring
    _ = 1 := by rw [e1]; field_simp

private theorem pow_ratio {K K' R : ℝ} (hK : 0 < K) (hKK : K ≤ K') (hR : 1 ≤ R)
    (hKR : K' ≤ R * K) (e : ℝ) : K' ^ e ≤ K ^ e * R ^ |e| := by
  have hK' : 0 < K' := lt_of_lt_of_le hK hKK
  have hq : K' = K * (K' / K) := by field_simp
  have hq1 : 1 ≤ K' / K := by rw [le_div_iff₀ hK]; linarith
  have hqR : K' / K ≤ R := by rw [div_le_iff₀ hK]; linarith
  rw [hq, Real.mul_rpow hK.le (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he]
    exact Real.rpow_le_rpow (by linarith) hqR he
  · calc (K' / K) ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 he.le
      _ ≤ R ^ |e| := Real.one_le_rpow hR (abs_nonneg _)

private theorem fin2_vec01 {α : Type*} (x y : α) :
    (fun i : Fin 2 => if i = 0 then x else y) = ![x, y] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

private theorem fin2_vec10 {α : Type*} (x y : α) :
    (fun i : Fin 2 => if i = 1 then x else y) = ![y, x] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- [I, Claim 6.11], weak form ([I, (6.31)]): for `d ≥ 2`, `a, b > 0` with `ad/2 - b - 2 ≥ 0`,
an auxiliary graph whose black and blue edges form spanning trees, and blue matrices of
weak-`(a, b)` norm at most `1`: `‖W^{aℓd/2} Γ̃ / B‖_{w;(a,b)} ≤ W^τ` for every `τ > 0` and
`W ≥ W₀` along `adm(c₀, c₁)`. -/
theorem auxTreeWeak :
  ∀ (d : ℕ) (a b : ℝ), 2 ≤ d → 0 < a → 0 < b → 0 ≤ a * d / 2 - b - 2 →
    ∀ c₀ c₁ : ℝ, 0 < c₀ → 0 < c₁ →
    ∀ (ℓ : ℕ) (Γ : AuxGraph ℓ), TreeEdges Γ.black → TreeEdges (Γ.blue.map fun e => (e.1, e.2.1)) →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ A : ℕ → Matrix (Zd d L) (Zd d L) ℝ, (∀ j, weakNorm d L W a b (A j) ≤ 1) →
          weakNorm d L W a b (Γ.normVal d L W a A) ≤ (W : ℝ) ^ τ := by
  intro d a b hd ha hb he c₀ c₁ hc₀ hc₁ ℓ Γ hT hU τ hτ
  obtain ⟨C₃, hC₃0, hC₃⟩ := vertexWeak d a b hd ha hb he
  obtain ⟨CM, hCM0, hCM⟩ := coreMax d hd Γ hT hU
  obtain ⟨C01, hC010, hC01⟩ := coreAvg d hd Γ hT hU 0 1 (by decide)
  obtain ⟨C10, hC100, hC10⟩ := coreAvg d hd Γ hT hU 1 0 (by decide)
  set s := a * d / 2 - b with hs
  set κ : ℝ := ((2 : ℝ) ^ (ℓ + 1)) ^ |(d : ℝ) - s| with hκ
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) := one_le_pow₀ (by norm_num)
  have hκ1 : 1 ≤ κ := Real.one_le_rpow hR1 (abs_nonneg _)
  obtain ⟨W₀, hW₀⟩ := adm_eventually c₀ c₁ hc₀ hc₁ ((CM + (C01 + C10) * κ) * C₃ ^ ℓ)
    (by positivity) ℓ τ hτ
  refine ⟨W₀, fun W L _ hadm hWW A hA => ?_⟩
  obtain ⟨hW1, hWL, hlog⟩ := hW₀ W L hadm hWW (Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog0 := logF_nonneg' hW1 (by omega : W ≤ L)
  set μ : ℝ := (W : ℝ) ^ (-(a * d / 2)) with hμ
  have hμ0 : 0 < μ := by positivity
  have had : 0 ≤ a * d / 2 := by positivity
  have hμ1 : μ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1' (by linarith)
  set c₁' := C₃ * logF L W * μ with hc₁'
  have hc₁'0 : 0 ≤ c₁' := by positivity
  have hcancel : (W : ℝ) ^ (a * ℓ * d / 2) * μ ^ ℓ = 1 := W_pow_cancel hW0 a ℓ d
  have hA1 : ∀ j p u, ∑ z, bB d L W z u * |A j z p| ≤ c₁' ∧
      ∑ z, bB d L W z u * |A j p z| ≤ c₁' := by
    intro j p u
    obtain ⟨h1, h2⟩ := hC₃ L W hW1 hWL (A j) p u
    have : C₃ * logF L W * μ * weakNorm d L W a b (A j) ≤ c₁' := by
      calc _ ≤ C₃ * logF L W * μ * 1 := mul_le_mul_of_nonneg_left (hA j) (by positivity)
        _ = c₁' := mul_one _
    exact ⟨h1.trans this, h2.trans this⟩
  have hAμ : ∀ j p r, |A j p r| ≤ μ := fun j p r =>
    ((normBasic d L W hW1 a b (A j)).1 p r).trans
      (by calc μ * weakNorm d L W a b (A j) ≤ μ * 1 := mul_le_mul_of_nonneg_left (hA j) hμ0.le
            _ = μ := mul_one _)
  have hAone : ∀ j p r, |A j p r| ≤ 1 := fun j p r => (hAμ j p r).trans hμ1
  set G : ℝ := C₃ ^ ℓ * logF L W ^ ℓ with hG
  have hG0 : 0 ≤ G := by positivity
  -- the maximum
  have hNmax : ∀ x y, |Γ.normVal d L W a A x y| ≤ μ * (CM * G) := by
    intro x y
    rw [abs_of_nonneg (normVal_nonneg Γ d L W hW1 a A x y)]
    have hv := hCM L W hW1 A c₁' μ hc₁'0 hμ1 hA1 hAμ x y
    have hB := bB_pos' (L := L) hW1 x y
    unfold AuxGraph.normVal
    rw [div_le_iff₀ hB]
    calc (W : ℝ) ^ (a * ℓ * d / 2) * Γ.val d L W A x y
        ≤ (W : ℝ) ^ (a * ℓ * d / 2) * (CM * c₁' ^ ℓ * μ * bB d L W x y) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = μ * (CM * G) * bB d L W x y * ((W : ℝ) ^ (a * ℓ * d / 2) * μ ^ ℓ) := by
          rw [hc₁', hG, mul_pow, mul_pow]; ring
      _ = _ := by rw [hcancel, mul_one]
  -- the ball averages
  have hNavg : ∀ K : ℕ, W ≤ K → 2 * K ≤ L → ∀ x x₀ : Zd d L,
      ∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K),
        (|Γ.normVal d L W a A x y| + |Γ.normVal d L W a A y x|) ≤
      (C01 + C10) * G * ((W : ℝ) ^ (-b) * (K : ℝ) ^ ((d : ℝ) - s) * κ) := by
    intro K hK hKL x x₀
    have hK0 : (0 : ℝ) < K := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hW1.trans hK
      linarith
    set cb : ℝ := (W : ℝ) ^ (-b) * (K : ℝ) ^ ((d : ℝ) - s) * κ with hcb
    have hcb0 : 0 ≤ cb := by positivity
    have hAbox : ∀ j p x₀' K', K ≤ K' → K' ≤ 2 ^ (ℓ + 1) * K → 2 * K' ≤ L →
        ∑ z, (if zdistInf d L (z - x₀') ≤ K' then (1 : ℝ) else 0) * |A j z p| ≤ cb ∧
        ∑ z, (if zdistInf d L (z - x₀') ≤ K' then (1 : ℝ) else 0) * |A j p z| ≤ cb := by
      intro j p x₀' K' h1 h2 h3
      have hK'0 : (0 : ℝ) < K' := lt_of_lt_of_le hK0 (by exact_mod_cast h1)
      obtain ⟨b1, b2⟩ := vertexBox hW1 a b (A j) p x₀' K' (hK.trans h1) h3
      have hb : (K' : ℝ) ^ d * ((W : ℝ) ^ (-b) * (K' : ℝ) ^ (-(a * d / 2 - b)) *
          weakNorm d L W a b (A j)) ≤ cb := by
        have hw := weakNorm_nonneg' hW1 a b (A j)
        have e1 : (K' : ℝ) ^ d * (K' : ℝ) ^ (-(a * d / 2 - b)) = (K' : ℝ) ^ ((d : ℝ) - s) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hK'0]; congr 1
        have h1' : (K : ℝ) ≤ (K' : ℝ) := by exact_mod_cast h1
        have h2' : (K' : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) * (K : ℝ) := by exact_mod_cast h2
        have hr := pow_ratio hK0 h1' hR1 h2' ((d : ℝ) - s)
        calc (K' : ℝ) ^ d * ((W : ℝ) ^ (-b) * (K' : ℝ) ^ (-(a * d / 2 - b)) *
              weakNorm d L W a b (A j))
            ≤ (K' : ℝ) ^ d * ((W : ℝ) ^ (-b) * (K' : ℝ) ^ (-(a * d / 2 - b)) * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA j) (by positivity))
                (by positivity)
          _ = (W : ℝ) ^ (-b) * (K' : ℝ) ^ ((d : ℝ) - s) := by rw [← e1]; ring
          _ ≤ (W : ℝ) ^ (-b) * ((K : ℝ) ^ ((d : ℝ) - s) * κ) :=
              mul_le_mul_of_nonneg_left hr (by positivity)
          _ = cb := by rw [hcb]; ring
      exact ⟨b1.trans hb, b2.trans hb⟩
    have h01 := hC01 L W hW1 A c₁' cb K hc₁'0 hcb0 hKL hA1 hAbox hAone x x₀
    have h10 := hC10 L W hW1 A c₁' cb K hc₁'0 hcb0 hKL hA1 hAbox hAone x x₀
    simp only [fin2_vec01] at h01
    simp only [fin2_vec10] at h10
    have hsplit : ∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K),
        (|Γ.normVal d L W a A x y| + |Γ.normVal d L W a A y x|) =
        (W : ℝ) ^ (a * ℓ * d / 2) * (∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
          ((∑ s : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![x, y] s) *
            (Γ.blue.map (blueF A (Sum.elim ![x, y] s))).prod) / bB d L W x y) +
          ∑ y, (if zdistInf d L (y - x₀) ≤ K then (1 : ℝ) else 0) *
          ((∑ s : Fin ℓ → Zd d L, bProd d L W Γ.black (Sum.elim ![y, x] s) *
            (Γ.blue.map (blueF A (Sum.elim ![y, x] s))).prod) / bB d L W x y)) := by
      rw [Finset.sum_filter, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [abs_of_nonneg (normVal_nonneg Γ d L W hW1 a A x y),
        abs_of_nonneg (normVal_nonneg Γ d L W hW1 a A y x)]
      unfold AuxGraph.normVal
      rw [val_eq, val_eq, bB_comm' y x]
      split_ifs <;> ring
    rw [hsplit]
    calc (W : ℝ) ^ (a * ℓ * d / 2) * (_ + _)
        ≤ (W : ℝ) ^ (a * ℓ * d / 2) * (C01 * c₁' ^ ℓ * cb + C10 * c₁' ^ ℓ * cb) :=
          mul_le_mul_of_nonneg_left (add_le_add h01 h10) (by positivity)
      _ = (C01 + C10) * G * cb * ((W : ℝ) ^ (a * ℓ * d / 2) * μ ^ ℓ) := by
          rw [hc₁', hG, mul_pow, mul_pow]; ring
      _ = _ := by rw [hcancel, mul_one]
  -- the weak norm
  have hmaxt : (W : ℝ) ^ (a * d / 2) * (⨆ x, ⨆ y, |Γ.normVal d L W a A x y|) ≤ CM * G := by
    have hb0 : 0 ≤ μ * (CM * G) := by positivity
    have h := Real.iSup_le (fun x => Real.iSup_le (fun y => hNmax x y) hb0) hb0
    calc (W : ℝ) ^ (a * d / 2) * (⨆ x, ⨆ y, |Γ.normVal d L W a A x y|)
        ≤ (W : ℝ) ^ (a * d / 2) * (μ * (CM * G)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = CM * G := by
          rw [← mul_assoc, hμ, ← Real.rpow_add hW0, add_neg_cancel, Real.rpow_zero, one_mul]
  have havgt : (⨆ K : {K : ℕ // W ≤ K ∧ 2 * K ≤ L}, ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) *
      ⨆ x, ⨆ x₀ : Zd d L,
        (∑ y ∈ Finset.univ.filter (fun y => zdistInf d L (y - x₀) ≤ K),
          (|Γ.normVal d L W a A x y| + |Γ.normVal d L W a A y x|)) / (K : ℝ) ^ d) ≤
      (C01 + C10) * κ * G := by
    have hb0 : 0 ≤ (C01 + C10) * κ * G := by positivity
    refine Real.iSup_le (fun ⟨K, hK, hKL⟩ => ?_) hb0
    have hK0 : (0 : ℝ) < K := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hW1.trans hK
      linarith
    have hb1 : 0 ≤ (C01 + C10) * G * ((W : ℝ) ^ (-b) * (K : ℝ) ^ ((d : ℝ) - s) * κ) /
        (K : ℝ) ^ d := by positivity
    have hin := Real.iSup_le (fun x => Real.iSup_le (fun x₀ =>
      div_le_div_of_nonneg_right (hNavg K hK hKL x x₀) (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ d))
        hb1) hb1
    calc ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) * _
        ≤ ((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) *
          ((C01 + C10) * G * ((W : ℝ) ^ (-b) * (K : ℝ) ^ ((d : ℝ) - s) * κ) / (K : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = (C01 + C10) * κ * G * (((W : ℝ) / K) ^ b * (K : ℝ) ^ (a * d / 2) *
          ((W : ℝ) ^ (-b) * (K : ℝ) ^ ((d : ℝ) - (a * d / 2 - b))) / (K : ℝ) ^ d) := by
          rw [hs]; ring
      _ = (C01 + C10) * κ * G := by rw [box_alg hW0 hK0, mul_one]
  unfold weakNorm
  calc _ ≤ CM * G + (C01 + C10) * κ * G := add_le_add hmaxt havgt
    _ = (CM + (C01 + C10) * κ) * C₃ ^ ℓ * logF L W ^ ℓ := by rw [hG]; ring
    _ ≤ _ := hlog

/-- [I, Claim 6.11], strong form: the same with strong-`(a, b)` norms. -/
theorem auxTreeStrong :
  ∀ (d : ℕ) (a b : ℝ), 2 ≤ d → 0 < a → 0 < b → 0 ≤ a * d / 2 - b - 2 →
    ∀ c₀ c₁ : ℝ, 0 < c₀ → 0 < c₁ →
    ∀ (ℓ : ℕ) (Γ : AuxGraph ℓ), TreeEdges Γ.black → TreeEdges (Γ.blue.map fun e => (e.1, e.2.1)) →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
        ∀ A : ℕ → Matrix (Zd d L) (Zd d L) ℝ, (∀ j, strongNorm d L W a b (A j) ≤ 1) →
          strongNorm d L W a b (Γ.normVal d L W a A) ≤ (W : ℝ) ^ τ := by
  intro d a b hd ha hb he c₀ c₁ hc₀ hc₁ ℓ Γ hT hU τ hτ
  obtain ⟨CE, hCE0, hCE⟩ := vertexStrong d a b hd hb he
  obtain ⟨CS, hCS0, hCS⟩ := coreStrong d hd b (a * d / 2 - b) hb.le (by linarith) Γ hT hU
  obtain ⟨W₀, hW₀⟩ := adm_eventually c₀ c₁ hc₀ hc₁ (CS * CE ^ ℓ) (by positivity) ℓ τ hτ
  refine ⟨W₀, fun W L _ hadm hWW A hA => ?_⟩
  obtain ⟨hW1, hWL, hlog⟩ := hW₀ W L hadm hWW (Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog0 := logF_nonneg' hW1 (by omega : W ≤ L)
  set μ : ℝ := (W : ℝ) ^ (-(a * d / 2)) with hμ
  have hμ0 : 0 < μ := by positivity
  set c₁' := CE * logF L W * μ with hc₁'
  have hc₁'0 : 0 ≤ c₁' := by positivity
  have hcancel : (W : ℝ) ^ (a * ℓ * d / 2) * μ ^ ℓ = 1 := W_pow_cancel hW0 a ℓ d
  have hS : ∀ p u : Zd d L, ∑ z, bB d L W z u *
      ((W : ℝ) ^ (-b) * brk d L W z p ^ (-(a * d / 2 - b))) ≤ c₁' :=
    fun p u => hCE L W hW1 hWL p u
  have hAS : ∀ j p r, |A j p r| ≤ (W : ℝ) ^ (-b) * brk d L W p r ^ (-(a * d / 2 - b)) := by
    intro j p r
    have h := (normBasic d L W hW1 a b (A j)).2.2 p r
    have ht := brk_pos (L := L) hW1 p r
    calc |A j p r| ≤ (W : ℝ) ^ (-b) * brk d L W p r ^ (-(a * d / 2 - b)) *
          strongNorm d L W a b (A j) := h
      _ ≤ (W : ℝ) ^ (-b) * brk d L W p r ^ (-(a * d / 2 - b)) * 1 :=
          mul_le_mul_of_nonneg_left (hA j) (by positivity)
      _ = _ := mul_one _
  set G : ℝ := CS * CE ^ ℓ * logF L W ^ ℓ with hG
  have hG0 : 0 ≤ G := by positivity
  unfold strongNorm
  refine le_trans (Real.iSup_le (fun x => Real.iSup_le (fun y => ?_) hG0) hG0)
    (by rw [hG]; exact hlog)
  have ht := brk_pos (L := L) hW1 x y
  have hB := bB_pos' (L := L) hW1 x y
  have hv := hCS L W hW1 A c₁' hc₁'0 hS hAS x y
  have hN : |Γ.normVal d L W a A x y| ≤
      G * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b))) := by
    rw [abs_of_nonneg (normVal_nonneg Γ d L W hW1 a A x y)]
    unfold AuxGraph.normVal
    rw [div_le_iff₀ hB]
    calc (W : ℝ) ^ (a * ℓ * d / 2) * Γ.val d L W A x y
        ≤ (W : ℝ) ^ (a * ℓ * d / 2) * (CS * c₁' ^ ℓ *
          ((W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b))) * bB d L W x y) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = G * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b))) * bB d L W x y *
          ((W : ℝ) ^ (a * ℓ * d / 2) * μ ^ ℓ) := by
          rw [hc₁', hG, mul_pow, mul_pow]; ring
      _ = _ := by rw [hcancel, mul_one]
  calc ((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) * |Γ.normVal d L W a A x y|
      ≤ ((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) *
        (G * ((W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b)))) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = G * (((W : ℝ) / brk d L W x y) ^ b * brk d L W x y ^ (a * d / 2) *
        ((W : ℝ) ^ (-b) * brk d L W x y ^ (-(a * d / 2 - b)))) := by ring
    _ = G := by rw [strong_alg hW0 ht, mul_one]

end Main

section Instances

namespace G9

end G9

end Instances

end RBM8D
