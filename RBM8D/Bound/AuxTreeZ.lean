module

public import RBM8D.Bound.AuxTree

@[expose] public section

/-!
# Auxiliary graphs on `ℤ^d` ([I, Claim 6.11], pointwise strong form)

On `ℤ^d` let `⟨x - y⟩ = |x - y|_∞ + W` and `B^β_{xy} = W^{-2} ⟨x - y⟩^{-β}`; the exponent
`β = d - 2` gives `B` of [I, (1.18)] on `ℤ^d`. An auxiliary graph of [I, Claim 6.11] is evaluated
on `ℤ^d` by summing its internal atoms over `ℤ^d`, with a factor `B^β` on each black edge and
`|A_j|` on each blue edge.

* `AuxTreeZ.vertex`: the one-vertex sum `Σ_z B^β_{zu} W^{-b} ⟨z - p⟩^{-s}` is finite and at most
  `C W^{-2-b} W^{d-β-s}` when `β + s > d`; there is no `log(L/W)` factor.
* `AuxTreeZ.core`: [I, Claim 6.11], strong form ([I, (6.31)]) on `ℤ^d`, pointwise: if the black
  and blue edges form spanning trees, `|A_j(p, r)| ≤ W^{-b} ⟨p - r⟩^{-s}` and every one-vertex sum
  is at most `c₁`, then the value is a summable series bounded by
  `C c₁^ℓ W^{-b} ⟨x - y⟩^{-s} B^β_{xy}`.
* `auxTreeZStrong`: the case `β = s = d - 2 - τ₁`, `b = 2`, `d ≥ 6`, in the form
  `W^{-ord·d/2} W^{2d-4} ⟨x - y⟩^{-(2d-4-τ)}` of [I, Cor 7.6], with `ord = 2ℓ + 4`.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace RBM8D

open Graphs

namespace AuxTreeZ

/-- The bracket `⟨x - y⟩ = |x - y|_∞ + W` on `ℤ^d`. -/
def brk (d W : ℕ) (x y : Fin d → ℤ) : ℝ := (zdInf (x - y) : ℝ) + W

/-- `B^β_{xy} = W^{-2} ⟨x - y⟩^{-β}` on `ℤ^d`. -/
def bB (d W : ℕ) (β : ℝ) (x y : Fin d → ℤ) : ℝ := (W : ℝ) ^ (-2 : ℝ) * brk d W x y ^ (-β)

variable {d W : ℕ}

/-- `⟨x - y⟩ ≥ W`. -/
theorem W_le_brk (x y : Fin d → ℤ) : (W : ℝ) ≤ brk d W x y := by
  unfold brk
  have := Nat.cast_nonneg (α := ℝ) (zdInf (x - y))
  linarith

/-- `⟨x - y⟩ > 0` for `W ≥ 1`. -/
theorem brk_pos (hW : 1 ≤ W) (x y : Fin d → ℤ) : 0 < brk d W x y := by
  have h1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  linarith [W_le_brk (W := W) x y]

/-- `⟨x - y⟩ = ⟨y - x⟩`. -/
theorem brk_comm (x y : Fin d → ℤ) : brk d W x y = brk d W y x := by
  unfold brk
  rw [← neg_sub, zdInf_neg]

/-- `⟨x - z⟩ ≤ ⟨x - y⟩ + ⟨y - z⟩`. -/
theorem brk_tri (x y z : Fin d → ℤ) : brk d W x z ≤ brk d W x y + brk d W y z := by
  unfold brk
  have h : x - z = (x - y) + (y - z) := by abel
  have h2 := zdInf_add_le (x - y) (y - z)
  rw [← h] at h2
  have h3 : ((zdInf (x - z) : ℕ) : ℝ) ≤ (zdInf (x - y) : ℝ) + (zdInf (y - z) : ℝ) := by
    exact_mod_cast h2
  have h4 := Nat.cast_nonneg (α := ℝ) W
  linarith

private theorem brk_self (x y : Fin d → ℤ) : brk d W x x = brk d W y y := by
  simp [brk]

/-- `B^β_{xy} > 0` for `W ≥ 1`. -/
theorem bB_pos (hW : 1 ≤ W) (β : ℝ) (x y : Fin d → ℤ) : 0 < bB d W β x y := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold bB
  have := brk_pos hW x y
  positivity

/-- The kernel `c₀ ⟨p - q⟩^{-s}` rehangs: if `z` is at least as close to `v` as to `u` (in the
kernel), then the factor of `z–u` is at most `2^s` times the factor of `v–u`. -/
private theorem ker_rehang (hW : 1 ≤ W) {c₀ s : ℝ} (hc₀ : 0 ≤ c₀) (hs : 0 ≤ s)
    (z u v : Fin d → ℤ) (h : c₀ * brk d W z u ^ (-s) ≤ c₀ * brk d W z v ^ (-s)) :
    c₀ * brk d W z u ^ (-s) ≤ (2 : ℝ) ^ s * (c₀ * brk d W v u ^ (-s)) := by
  set M := max (brk d W z u) (brk d W z v) with hM
  have hzu := brk_pos hW z u
  have hvu := brk_pos hW v u
  have hM0 : 0 < M := lt_max_of_lt_left hzu
  have h1 : c₀ * brk d W z u ^ (-s) ≤ c₀ * M ^ (-s) := by
    rcases max_cases (brk d W z u) (brk d W z v) with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hM, hm]
    · rw [hM, hm]; exact h
  have h2 : brk d W v u / 2 ≤ M := by
    have := brk_tri (W := W) v z u
    rw [brk_comm v z] at this
    have := le_max_left (brk d W z u) (brk d W z v)
    have := le_max_right (brk d W z u) (brk d W z v)
    linarith
  have h3 : M ^ (-s) ≤ (brk d W v u / 2) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have h4 : (brk d W v u / 2) ^ (-s) = (2 : ℝ) ^ s * brk d W v u ^ (-s) := by
    rw [Real.div_rpow hvu.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  calc c₀ * brk d W z u ^ (-s) ≤ c₀ * M ^ (-s) := h1
    _ ≤ c₀ * ((2 : ℝ) ^ s * brk d W v u ^ (-s)) := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left h3 hc₀
    _ = _ := by ring

end AuxTreeZ

/-- The summand of the value of an auxiliary graph on `ℤ^d` at the positions `σ` of the internal
atoms: the product of `B^β` over the black edges and of `|A_j|` over the blue edges, the external
atoms sitting at `x` and `y`. -/
def AuxGraph.termZ {ℓ : ℕ} (Γ : AuxGraph ℓ) (d W : ℕ) (β : ℝ)
    (A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (x y : Fin d → ℤ) (σ : Fin ℓ → Fin d → ℤ) : ℝ :=
  (Γ.black.map fun e =>
      AuxTreeZ.bB d W β (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2)).prod *
    (Γ.blue.map fun e => |A e.2.2 (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2.1)|).prod

/-- The value of an auxiliary graph on `ℤ^d` at `x, y`: the sum over the positions in `ℤ^d` of
the internal atoms of `AuxGraph.termZ`, the `ℤ^d` analogue of `AuxGraph.val`. -/
def AuxGraph.valZ {ℓ : ℕ} (Γ : AuxGraph ℓ) (d W : ℕ) (β : ℝ)
    (A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (x y : Fin d → ℤ) : ℝ :=
  ∑' σ : Fin ℓ → Fin d → ℤ, Γ.termZ d W β A x y σ

/-- The summand of `AuxGraph.valZ` is nonnegative for `W ≥ 1`. -/
theorem AuxTreeZ.termZ_nonneg {ℓ : ℕ} (Γ : AuxGraph ℓ) {d W : ℕ} (hW : 1 ≤ W) (β : ℝ)
    (A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (x y : Fin d → ℤ) (σ : Fin ℓ → Fin d → ℤ) :
    0 ≤ Γ.termZ d W β A x y σ := by
  unfold AuxGraph.termZ
  refine mul_nonneg (List.prod_nonneg fun a ha => ?_) (List.prod_nonneg fun a ha => ?_)
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
    exact (AuxTreeZ.bB_pos hW β _ _).le
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg _

namespace AuxTreeZ

/-! ## Products over edge lists -/

section Lists

variable {γ : Type*}

private theorem prod_map_eraseIdx (l : List γ) (f : γ → ℝ) (i : ℕ) (hi : i < l.length) :
    (l.map f).prod = f l[i] * ((l.eraseIdx i).map f).prod := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < t.length := by simpa using hi
      simp only [List.map_cons, List.prod_cons, List.eraseIdx_cons_succ, List.getElem_cons_succ]
      rw [ih j hj]
      ring

private theorem prod_map_le_pow (l : List γ) (f g : γ → ℝ) (c : ℝ)
    (h : ∀ e ∈ l, 0 ≤ f e ∧ f e ≤ c * g e) :
    (l.map f).prod ≤ c ^ l.length * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht : ∀ e ∈ t, 0 ≤ f e ∧ f e ≤ c * g e := fun e he => h e (List.mem_cons_of_mem _ he)
    have hft : 0 ≤ (t.map f).prod := List.prod_nonneg fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact (ht e he).1
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    calc f a * (t.map f).prod ≤ (c * g a) * (c ^ t.length * (t.map g).prod) :=
          mul_le_mul ha.2 (ih ht) hft (ha.1.trans ha.2)
      _ = _ := by ring

end Lists

/-! ## Elimination of one vertex -/

section Elim

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency through an edge list, in either direction. -/
private def adjE (E : List (V × V)) (a b : V) : Prop := (a, b) ∈ E ∨ (b, a) ∈ E

/-- The vertex map sending `z` to `u` and fixing the other vertices. -/
private def subV (z u a : V) : V := if a = z then u else a

/-- The product of the kernel `k` over the edges `E` at the positions `p`. -/
private def kprod (k : X → X → ℝ) (p : V → X) (E : List (V × V)) : ℝ :=
  (E.map fun e => k (p e.1) (p e.2)).prod

omit [Fintype V] [DecidableEq V] in
private theorem rtg_stuck {r : V → V → Prop} {z b : V} (h : ∀ c, r z c → c = z)
    (hr : Relation.ReflTransGen r z b) : b = z := by
  induction hr with
  | refl => rfl
  | tail _ hbc ih => subst ih; exact h _ hbc

omit [Fintype V] in
/-- One elimination step: a vertex `z ≠ O` of a connected edge list is joined to its neighbour `u`
with the largest kernel; contracting `z` into `u` keeps the list connected, removes one edge, and
costs at most a factor `c` per edge. -/
private theorem elimStep (k : X → X → ℝ) (c : ℝ) (hc : 1 ≤ c) (hk0 : ∀ p q, 0 ≤ k p q)
    (hks : ∀ p q, k p q = k q p) (hkd : ∀ p q, k p p = k q q)
    (hkr : ∀ z u v, k z u ≤ k z v → k z u ≤ c * k v u)
    (p : V → X) (R : Finset V) (O z : V) (hz : z ∈ R) (hzO : z ≠ O)
    (E : List (V × V)) (hE : ∀ e ∈ E, e.1 ∈ R ∧ e.2 ∈ R)
    (hR : ∀ v ∈ R, Relation.ReflTransGen (adjE E) v O) :
    ∃ u ∈ R.erase z, ∃ E' : List (V × V), E'.length + 1 = E.length ∧
      (∀ e ∈ E', e.1 ∈ R.erase z ∧ e.2 ∈ R.erase z) ∧
      (∀ v ∈ R.erase z, Relation.ReflTransGen (adjE E') v O) ∧
      kprod k p E ≤ c ^ E.length * k (p z) (p u) * kprod k p E' := by
  classical
  have hnbR : ∀ w, adjE E z w → w ∈ R := by
    rintro w (h | h)
    · exact (hE _ h).2
    · exact (hE _ h).1
  set N := R.filter fun w => w ≠ z ∧ adjE E z w with hN
  have hNne : N.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hst : ∀ c', adjE E z c' → c' = z := by
      intro c' hc'
      by_contra hcz
      have : c' ∈ N := Finset.mem_filter.2 ⟨hnbR _ hc', hcz, hc'⟩
      simp [hne] at this
    exact hzO (rtg_stuck hst (hR z hz)).symm
  obtain ⟨u, huN, hu⟩ := N.exists_max_image (fun w => k (p z) (p w)) hNne
  have huz : u ≠ z := (Finset.mem_filter.1 huN).2.1
  have hzu : adjE E z u := (Finset.mem_filter.1 huN).2.2
  have hNmem : ∀ w, w ≠ z → adjE E z w → k (p z) (p w) ≤ k (p z) (p u) := fun w hw hzw =>
    hu w (Finset.mem_filter.2 ⟨hnbR _ hzw, hw, hzw⟩)
  obtain ⟨e₀, he₀E, he₀⟩ : ∃ e₀ ∈ E, e₀ = (z, u) ∨ e₀ = (u, z) := by
    rcases hzu with h | h
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  obtain ⟨i, hi, hiE⟩ := List.mem_iff_getElem.1 he₀E
  have huR : u ∈ R := by
    rcases he₀ with rfl | rfl
    · exact (hE _ he₀E).2
    · exact (hE _ he₀E).1
  have hsz : subV z u z = u := by simp [subV]
  have hsu : subV z u u = u := by simp [subV, huz]
  have hsne : ∀ a, a ≠ z → subV z u a = a := fun a ha => by simp [subV, ha]
  set f : V × V → V × V := fun e => (subV z u e.1, subV z u e.2) with hf
  have hmem' : ∀ e ∈ E, subV z u e.1 ≠ subV z u e.2 → f e ∈ (E.eraseIdx i).map f := by
    intro e he hne
    apply List.mem_map_of_mem
    rw [List.mem_eraseIdx_iff_getElem]
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.1 he
    refine ⟨j, hj, ?_, hjE⟩
    rintro rfl
    apply hne
    have : e = e₀ := hjE.symm.trans hiE
    subst this
    rcases he₀ with rfl | rfl
    · simp [hsz, hsu]
    · simp [hsz, hsu]
  refine ⟨u, Finset.mem_erase.2 ⟨huz, huR⟩, (E.eraseIdx i).map f, ?_, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_eraseIdx_of_lt hi]
    omega
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have hmem := hE e' (List.mem_of_mem_eraseIdx he')
    have key : ∀ a ∈ R, subV z u a ∈ R.erase z := by
      intro a ha
      by_cases h : a = z
      · rw [h, hsz]; exact Finset.mem_erase.2 ⟨huz, huR⟩
      · rw [hsne a h]; exact Finset.mem_erase.2 ⟨h, ha⟩
    exact ⟨key _ hmem.1, key _ hmem.2⟩
  · intro v hv
    have hvz := (Finset.mem_erase.1 hv).1
    have h1 := hR v (Finset.mem_erase.1 hv).2
    have hl := Relation.ReflTransGen.lift' (p := adjE ((E.eraseIdx i).map f)) (subV z u)
      (fun a b hab => ?_) v O h1
    · simpa [Function.onFun, hsne v hvz, hsne O hzO.symm] using hl
    · by_cases hab' : subV z u a = subV z u b
      · change Relation.ReflTransGen _ (subV z u a) (subV z u b)
        rw [hab']
      · apply Relation.ReflTransGen.single
        rcases hab with h | h
        · exact Or.inl (hmem' _ h hab')
        · exact Or.inr (hmem' _ h (Ne.symm hab'))
  · have hk₀ : k (p E[i].1) (p E[i].2) = k (p z) (p u) := by
      rw [hiE]
      rcases he₀ with rfl | rfl
      · rfl
      · exact hks _ _
    have hP0 : 0 ≤ kprod k p ((E.eraseIdx i).map f) :=
      List.prod_nonneg fun a ha => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
        exact hk0 _ _
    have hle : ((E.eraseIdx i).map fun e => k (p e.1) (p e.2)).prod ≤
        c ^ (E.eraseIdx i).length * kprod k p ((E.eraseIdx i).map f) := by
      have := prod_map_le_pow (E.eraseIdx i) (fun e => k (p e.1) (p e.2))
        (fun e => k (p (f e).1) (p (f e).2)) c ?_
      · simpa [kprod, List.map_map, Function.comp_def] using this
      intro e he
      have heE := List.mem_of_mem_eraseIdx he
      refine ⟨hk0 _ _, ?_⟩
      simp only [hf]
      by_cases h1 : e.1 = z <;> by_cases h2 : e.2 = z
      · rw [h1, h2, hsz, hkd (p z) (p u)]
        exact le_mul_of_one_le_left (hk0 _ _) hc
      · rw [h1, hsz, hsne _ h2]
        have hadj : adjE E z e.2 := Or.inl (by rw [← h1]; exact heE)
        exact hkr _ _ _ (hNmem _ h2 hadj)
      · rw [h2, hsz, hsne _ h1]
        have hadj : adjE E z e.1 := Or.inr (by rw [← h2]; exact heE)
        rw [hks (p e.1) (p z), hks (p e.1) (p u)]
        exact hkr _ _ _ (hNmem _ h1 hadj)
      · rw [hsne _ h1, hsne _ h2]
        exact le_mul_of_one_le_left (hk0 _ _) hc
    have hlen : (E.eraseIdx i).length + 1 = E.length := by
      rw [List.length_eraseIdx_of_lt hi]; omega
    have hpow : c ^ (E.eraseIdx i).length ≤ c ^ E.length :=
      pow_le_pow_right₀ hc (by omega)
    unfold kprod
    rw [prod_map_eraseIdx E _ i hi, hk₀]
    calc k (p z) (p u) * ((E.eraseIdx i).map fun e => k (p e.1) (p e.2)).prod
        ≤ k (p z) (p u) * (c ^ (E.eraseIdx i).length * kprod k p ((E.eraseIdx i).map f)) :=
          mul_le_mul_of_nonneg_left hle (hk0 _ _)
      _ ≤ k (p z) (p u) * (c ^ E.length * kprod k p ((E.eraseIdx i).map f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hP0) (hk0 _ _)
      _ = _ := by unfold kprod; ring

end Elim

/-! ## Elimination of all internal atoms -/

section Iter

variable {ℓ : ℕ} {X : Type*}

/-- The external atoms and the internal atoms of index at least `ℓ - n`. -/
private def Rn (ℓ n : ℕ) : Finset (Atom 2 ℓ) :=
  Finset.univ.filter fun v => ∀ j : Fin ℓ, v = Sum.inr j → ℓ ≤ j.val + n

/-- The external atoms and the internal atoms of index larger than `j`. -/
private def later (j : Fin ℓ) : Finset (Atom 2 ℓ) :=
  Finset.univ.filter fun v => ∀ m : Fin ℓ, v = Sum.inr m → j < m

private theorem mem_Rn_inl (n : ℕ) (a : Fin 2) : (Sum.inl a : Atom 2 ℓ) ∈ Rn ℓ n := by
  simp [Rn]

private theorem mem_Rn_inr (n : ℕ) (j : Fin ℓ) :
    (Sum.inr j : Atom 2 ℓ) ∈ Rn ℓ n ↔ ℓ ≤ j.val + n := by
  simp [Rn]

private theorem Rn_erase (n : ℕ) (hn : n + 1 ≤ ℓ) :
    (Rn ℓ (n + 1)).erase (Sum.inr ⟨ℓ - (n + 1), by omega⟩) = Rn ℓ n := by
  ext v
  rcases v with a | j
  · simp [mem_Rn_inl]
  · rw [Finset.mem_erase, mem_Rn_inr, mem_Rn_inr]
    constructor
    · rintro ⟨h1, h2⟩
      have : j.val ≠ ℓ - (n + 1) := fun h => h1 (by rw [Sum.inr.injEq]; exact Fin.ext h)
      omega
    · intro h
      refine ⟨fun h' => ?_, by omega⟩
      rw [Sum.inr.injEq] at h'
      have := congrArg Fin.val h'
      simp at this
      omega

private theorem card_later_le (j : Fin ℓ) : (later j).card ≤ ℓ + 2 := by
  calc (later j).card ≤ (Finset.univ : Finset (Atom 2 ℓ)).card := Finset.card_le_univ _
    _ = ℓ + 2 := by simp [add_comm]

private theorem rtg_eq {r : Atom 2 ℓ → Atom 2 ℓ → Prop} (h : ∀ a b, r a b → a = b) {a b : Atom 2 ℓ}
    (hr : Relation.ReflTransGen r a b) : a = b := by
  induction hr with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

/-- Eliminating the internal atoms of indices `ℓ - n, …, ℓ - 1` of a connected list of `n + 1`
edges, one at a time in increasing order: the product of the kernel over the list is at most
`c^{(n+1)²} k(x, y)` times the product over these atoms `j` of `Σ_{w later than j} k(j, w)`. -/
private theorem elimIter (k : X → X → ℝ) (c : ℝ) (hc : 1 ≤ c) (hk0 : ∀ p q, 0 ≤ k p q)
    (hks : ∀ p q, k p q = k q p) (hkd : ∀ p q, k p p = k q q)
    (hkr : ∀ z u v, k z u ≤ k z v → k z u ≤ c * k v u) (p : Atom 2 ℓ → X) :
    ∀ n, n ≤ ℓ → ∀ E : List (Atom 2 ℓ × Atom 2 ℓ), E.length = n + 1 →
      (∀ e ∈ E, e.1 ∈ Rn ℓ n ∧ e.2 ∈ Rn ℓ n) →
      (∀ v ∈ Rn ℓ n, Relation.ReflTransGen (adjE E) v (Sum.inl 0)) →
      kprod k p E ≤ c ^ ((n + 1) ^ 2) * k (p (Sum.inl 0)) (p (Sum.inl 1)) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + n),
          ∑ w ∈ later j, k (p (Sum.inr j)) (p w) := by
  intro n
  induction n with
  | zero =>
    intro _ E hlen hE hR
    obtain ⟨e, rfl⟩ := List.length_eq_one_iff.1 hlen
    have hempty : Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + 0) = ∅ := by
      ext j; simp
    rw [hempty, Finset.prod_empty, mul_one, zero_add, one_pow, pow_one]
    have hin : ∀ v ∈ Rn ℓ 0, ∃ a : Fin 2, v = Sum.inl a := by
      intro v hv
      rcases v with a | j
      · exact ⟨a, rfl⟩
      · rw [mem_Rn_inr] at hv; omega
    obtain ⟨a, ha⟩ := hin _ (hE e (List.mem_singleton_self _)).1
    obtain ⟨b, hb⟩ := hin _ (hE e (List.mem_singleton_self _)).2
    have hab : a ≠ b := by
      intro hab
      have h := hR (Sum.inl 1) (mem_Rn_inl 0 1)
      have := rtg_eq (r := adjE [e]) (fun r s hrs => by
        rcases hrs with h | h
        · rw [List.mem_singleton] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only at h1 h2
          rw [h1, h2, ha, hb, hab]
        · rw [List.mem_singleton] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only at h1 h2
          rw [h1, h2, ha, hb, hab]) h
      simp at this
    have hk : kprod k p [e] = k (p (Sum.inl 0)) (p (Sum.inl 1)) := by
      simp only [kprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [ha, hb]
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · rfl
      · exact hks _ _
      · exact absurd rfl hab
    rw [hk]
    exact le_mul_of_one_le_left (hk0 _ _) hc
  | succ n ih =>
    intro hn E hlen hE hR
    set z : Fin ℓ := ⟨ℓ - (n + 1), by omega⟩ with hzdef
    have hz : (Sum.inr z : Atom 2 ℓ) ∈ Rn ℓ (n + 1) := by
      rw [mem_Rn_inr]; simp [hzdef]; omega
    obtain ⟨u, hu, E', hlen', hE', hR', hle⟩ := elimStep k c hc hk0 hks hkd hkr p (Rn ℓ (n + 1))
      (Sum.inl 0) (Sum.inr z) hz (by simp) E hE hR
    rw [Rn_erase n hn] at hu hE' hR'
    have hIH := ih (by omega) E' (by omega) hE' hR'
    have hul : u ∈ later z := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun m hm => ?_⟩
      rw [hm, mem_Rn_inr] at hu
      change z.val < m.val
      simp [hzdef]; omega
    have hS : k (p (Sum.inr z)) (p u) ≤ ∑ w ∈ later z, k (p (Sum.inr z)) (p w) :=
      Finset.single_le_sum (f := fun w => k (p (Sum.inr z)) (p w)) (fun w _ => hk0 _ _) hul
    have hfil : Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + (n + 1)) =
        insert z (Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + n)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hj : j = z
        · exact Or.inl hj
        · right
          have : j.val ≠ ℓ - (n + 1) := fun h' => hj (Fin.ext h')
          omega
      · rintro (rfl | h)
        · simp [hzdef]; omega
        · omega
    have hzn : z ∉ Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + n) := by
      simp [hzdef]; omega
    rw [hfil, Finset.prod_insert hzn]
    set P := ∏ j ∈ Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + n),
      ∑ w ∈ later j, k (p (Sum.inr j)) (p w) with hP
    set S := ∑ w ∈ later z, k (p (Sum.inr z)) (p w) with hSdef
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun w _ => hk0 _ _
    have hc0 : 0 ≤ c := by linarith
    have hkxy := hk0 (p (Sum.inl 0)) (p (Sum.inl 1))
    have hpow : c ^ E.length * c ^ ((n + 1) ^ 2) ≤ c ^ ((n + 1 + 1) ^ 2) := by
      rw [← pow_add, hlen]
      exact pow_le_pow_right₀ hc (by nlinarith)
    calc kprod k p E ≤ c ^ E.length * k (p (Sum.inr z)) (p u) * kprod k p E' := hle
      _ ≤ c ^ E.length * S * (c ^ ((n + 1) ^ 2) * k (p (Sum.inl 0)) (p (Sum.inl 1)) * P) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hS (pow_nonneg hc0 _)) hIH
            (List.prod_nonneg fun a ha => by
              obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
              exact hk0 _ _)
          exact mul_nonneg (pow_nonneg hc0 _) (Finset.sum_nonneg fun w _ => hk0 _ _)
      _ = (c ^ E.length * c ^ ((n + 1) ^ 2)) * k (p (Sum.inl 0)) (p (Sum.inl 1)) * (S * P) := by
          ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hkxy)
          exact mul_nonneg (Finset.sum_nonneg fun w _ => hk0 _ _) hP0

/-- For a spanning tree `E` of the atoms, the product of the kernel over `E` is at most
`c^{(ℓ+1)²} k(x, y) ∏_j Σ_{w later than j} k(j, w)`. -/
private theorem treeBound (k : X → X → ℝ) (c : ℝ) (hc : 1 ≤ c) (hk0 : ∀ p q, 0 ≤ k p q)
    (hks : ∀ p q, k p q = k q p) (hkd : ∀ p q, k p p = k q q)
    (hkr : ∀ z u v, k z u ≤ k z v → k z u ≤ c * k v u) (p : Atom 2 ℓ → X)
    (E : List (Atom 2 ℓ × Atom 2 ℓ)) (hT : TreeEdges E) :
    kprod k p E ≤ c ^ ((ℓ + 1) ^ 2) * k (p (Sum.inl 0)) (p (Sum.inl 1)) *
      ∏ j : Fin ℓ, ∑ w ∈ later j, k (p (Sum.inr j)) (p w) := by
  have hlen : E.length = ℓ + 1 := by
    have := hT.1
    simp at this
    omega
  have hall : ∀ v, v ∈ Rn ℓ ℓ := by
    intro v
    rcases v with a | j
    · exact mem_Rn_inl _ _
    · rw [mem_Rn_inr]; omega
  have hR : ∀ v ∈ Rn ℓ ℓ, Relation.ReflTransGen (adjE E) v (Sum.inl 0) := by
    intro v _
    have h := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (hT.2 v (Sum.inl 0))
    refine Relation.ReflTransGen.mono (fun a b (hab : (SimpleGraph.fromRel _).Adj a b) => ?_) _ _ h
    rw [SimpleGraph.fromRel_adj] at hab
    exact hab.2
  have h := elimIter k c hc hk0 hks hkd hkr p ℓ le_rfl E hlen (fun e _ => ⟨hall _, hall _⟩) hR
  have hfil : Finset.univ.filter (fun j : Fin ℓ => ℓ ≤ j.val + ℓ) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ => by omega
  rwa [hfil] at h

end Iter

/-! ## Sums over the internal positions, one atom at a time -/

/-- If the `i`-th factor depends only on the coordinates `j ≥ i` and its sum over the `i`-th
coordinate is at most `c`, the sum of the product over all coordinates is at most `c^ℓ`. -/
private theorem tsum_prod_le {Y : Type*} [Inhabited Y] : ∀ (ℓ : ℕ)
    (G : Fin ℓ → (Fin ℓ → Y) → ℝ≥0∞) (c : ℝ≥0∞),
    (∀ i σ τ, (∀ j, i ≤ j → σ j = τ j) → G i σ = G i τ) →
    (∀ i σ, ∑' z, G i (Function.update σ i z) ≤ c) →
    ∑' σ, ∏ i, G i σ ≤ c ^ ℓ
  | 0, G, c, _, _ => by simp
  | ℓ + 1, G, c, hdep, hsum => by
    rw [← (Fin.consEquiv fun _ => Y).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
    set G' : Fin ℓ → (Fin ℓ → Y) → ℝ≥0∞ := fun i τ => G i.succ (Fin.cons default τ) with hG'
    have hkey : ∀ (τ : Fin ℓ → Y) (z : Y),
        ∏ i, G i ((Fin.consEquiv fun _ => Y) (z, τ)) = G 0 (Fin.cons z τ) * ∏ i, G' i τ := by
      intro τ z
      rw [Fin.prod_univ_succ]
      congr 1
      refine Finset.prod_congr rfl fun i _ => hdep _ _ _ fun j hj => ?_
      cases j using Fin.cases with
      | zero => exact absurd hj (not_le.2 (Fin.succ_pos i))
      | succ k => simp
    have hdep' : ∀ i σ τ, (∀ j, i ≤ j → σ j = τ j) → G' i σ = G' i τ := by
      intro i σ τ h
      refine hdep _ _ _ fun j hj => ?_
      cases j using Fin.cases with
      | zero => exact absurd hj (not_le.2 (Fin.succ_pos i))
      | succ k => simpa using h k (Fin.succ_le_succ_iff.1 hj)
    have hsum' : ∀ i σ, ∑' z, G' i (Function.update σ i z) ≤ c := by
      intro i σ
      simp only [hG', Fin.cons_update]
      exact hsum i.succ _
    have h0 : ∀ τ : Fin ℓ → Y, ∑' z, G 0 (Fin.cons z τ) ≤ c := by
      intro τ
      have := hsum 0 (Fin.cons default τ)
      simpa [Fin.update_cons_zero] using this
    simp_rw [hkey, ENNReal.tsum_mul_right]
    calc ∑' τ, (∑' z, G 0 (Fin.cons z τ)) * ∏ i, G' i τ ≤ ∑' τ, c * ∏ i, G' i τ :=
          ENNReal.tsum_le_tsum fun τ => mul_le_mul_left (h0 τ) _
      _ = c * ∑' τ, ∏ i, G' i τ := ENNReal.tsum_mul_left
      _ ≤ c * c ^ ℓ := mul_le_mul_right (tsum_prod_le ℓ G' c hdep' hsum') c
      _ = c ^ (ℓ + 1) := (pow_succ' c ℓ).symm

/-- A nonnegative family whose `ℝ≥0∞`-sum is at most `B` is summable with sum at most `B`. -/
private theorem summable_of_ennreal {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {B : ℝ}
    (hB : 0 ≤ B) (h : ∑' i, ENNReal.ofReal (f i) ≤ ENNReal.ofReal B) :
    Summable f ∧ ∑' i, f i ≤ B := by
  have hne : ∑' i, ENNReal.ofReal (f i) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hB, ENNReal.ofReal_tsum_of_nonneg hf hs]
  exact h

/-! ## Lattice sums -/

private theorem oneD_lower {W : ℕ} (q : ℤ) (r : ℕ) (hr : r < W) :
    (W : ℝ) * max |(q : ℝ)| 1 ≤ |((q * W + r : ℤ) : ℝ)| + W := by
  rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg W), mul_one]
  refine max_le ?_ (by linarith [abs_nonneg ((q * W + r : ℤ) : ℝ)])
  have hr' : (r : ℝ) < W := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  push_cast
  rcases le_or_gt 0 q with hq | hq
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    rw [abs_of_nonneg hq']
    have := le_abs_self ((q : ℝ) * W + r)
    nlinarith
  · have hq' : (q : ℝ) < 0 := by exact_mod_cast hq
    rw [abs_of_neg hq']
    have := neg_le_abs ((q : ℝ) * W + r)
    nlinarith

/-- `Σ_{n ∈ ℤ} (|n| + W)^{-α} ≤ C W^{1-α}` for `α > 1`. -/
private theorem oneD (α : ℝ) (hα : 1 < α) : ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W →
    Summable (fun n : ℤ => (|(n : ℝ)| + W) ^ (-α)) ∧
      ∑' n : ℤ, (|(n : ℝ)| + W) ^ (-α) ≤ C * (W : ℝ) ^ (1 - α) := by
  set m : ℤ → ℝ := fun q => (max |(q : ℝ)| 1) ^ (-α) with hm
  have hm0 : ∀ q, 0 ≤ m q := fun q => Real.rpow_nonneg (le_max_of_le_right zero_le_one) _
  have hms : Summable m := by
    refine Summable.of_nonneg_of_le hm0 (fun q => ?_)
      ((Real.summable_abs_int_rpow hα).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable)
    by_cases hq : q = 0
    · subst hq
      simp [hm, Real.zero_rpow (by linarith : -α ≠ 0)]
    · have h1 : (1 : ℝ) ≤ |(q : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hq
      simp only [hm, max_eq_left h1, hq, ite_false, add_zero, le_refl]
  refine ⟨∑' q, m q, tsum_nonneg hm0, fun W hW => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hsurj : Function.Surjective (fun qr : ℤ × Fin W => qr.1 * (W : ℤ) + ((qr.2 : ℕ) : ℤ)) := by
    intro n
    have hWz : (0 : ℤ) < W := by exact_mod_cast hW
    have h0 := Int.emod_nonneg n hWz.ne'
    have h1 := Int.emod_lt_of_pos n hWz
    refine ⟨(n / W, ⟨(n % W).toNat, by omega⟩), ?_⟩
    simp only
    rw [Int.toNat_of_nonneg h0]
    exact Int.ediv_mul_add_emod n W
  have hbd : ∀ qr : ℤ × Fin W, (|((qr.1 * (W : ℤ) + ((qr.2 : ℕ) : ℤ) : ℤ) : ℝ)| + W) ^ (-α) ≤
      (W : ℝ) ^ (-α) * m qr.1 := by
    intro qr
    have hl := oneD_lower (W := W) qr.1 qr.2 qr.2.2
    have hpos : 0 < (W : ℝ) * max |(qr.1 : ℝ)| 1 :=
      mul_pos hW0 (lt_max_of_lt_right one_pos)
    calc (|((qr.1 * (W : ℤ) + ((qr.2 : ℕ) : ℤ) : ℤ) : ℝ)| + W) ^ (-α)
        ≤ ((W : ℝ) * max |(qr.1 : ℝ)| 1) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hpos hl (by linarith)
      _ = _ := Real.mul_rpow hW0.le (le_max_of_le_right zero_le_one)
  have hE : ∑' n : ℤ, ENNReal.ofReal ((|(n : ℝ)| + W) ^ (-α)) ≤
      ENNReal.ofReal ((∑' q, m q) * (W : ℝ) ^ (1 - α)) := by
    calc ∑' n : ℤ, ENNReal.ofReal ((|(n : ℝ)| + W) ^ (-α))
        ≤ ∑' qr : ℤ × Fin W, ENNReal.ofReal
            ((|((qr.1 * (W : ℤ) + ((qr.2 : ℕ) : ℤ) : ℤ) : ℝ)| + W) ^ (-α)) :=
          ENNReal.tsum_le_tsum_comp_of_surjective hsurj
            (fun n : ℤ => ENNReal.ofReal ((|(n : ℝ)| + W) ^ (-α)))
      _ ≤ ∑' qr : ℤ × Fin W, ENNReal.ofReal ((W : ℝ) ^ (-α) * m qr.1) :=
          ENNReal.tsum_le_tsum fun qr => ENNReal.ofReal_le_ofReal (hbd qr)
      _ = ∑' q : ℤ, ∑' _r : Fin W, ENNReal.ofReal ((W : ℝ) ^ (-α) * m q) := ENNReal.tsum_prod'
      _ = ∑' q : ℤ, ENNReal.ofReal ((W : ℝ) * ((W : ℝ) ^ (-α) * m q)) := by
          congr 1; ext q
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg W), ENNReal.ofReal_natCast]
      _ = ∑' q : ℤ, ENNReal.ofReal ((W : ℝ) ^ (1 - α)) * ENNReal.ofReal (m q) := by
          congr 1; ext q
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
          congr 2
          rw [sub_eq_add_neg, Real.rpow_add hW0, Real.rpow_one]
      _ = ENNReal.ofReal ((W : ℝ) ^ (1 - α)) * ENNReal.ofReal (∑' q, m q) := by
          rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg hm0 hms]
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  exact summable_of_ennreal (fun n => Real.rpow_nonneg (by positivity) _)
    (mul_nonneg (tsum_nonneg hm0) (by positivity)) hE

private theorem exists_exp (d : ℕ) (γ : ℝ) (hγ : (d : ℝ) < γ) :
    ∃ α : ℝ, 1 < α ∧ (d : ℝ) * α ≤ γ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨2, by norm_num, by simp at hγ ⊢; linarith⟩
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    refine ⟨γ / d, ?_, ?_⟩
    · rw [lt_div_iff₀ hd']; linarith
    · rw [mul_div_cancel₀ _ hd'.ne']

/-- `Σ_{v ∈ ℤ^d} ⟨v⟩^{-γ} ≤ C W^{d-γ}` for `γ > d`. -/
private theorem latSum (d : ℕ) (γ : ℝ) (hγ : (d : ℝ) < γ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W →
    Summable (fun v : Fin d → ℤ => ((zdInf v : ℝ) + W) ^ (-γ)) ∧
      ∑' v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-γ) ≤ C * (W : ℝ) ^ ((d : ℝ) - γ) := by
  obtain ⟨α, hα, hdα⟩ := exists_exp d γ hγ
  obtain ⟨C₁, hC₁, h1⟩ := oneD α hα
  refine ⟨C₁ ^ d, pow_nonneg hC₁ d, fun W hW => ?_⟩
  obtain ⟨hs1, hb1⟩ := h1 W hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set f : ℤ → ℝ := fun n => (|(n : ℝ)| + W) ^ (-α) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => Real.rpow_nonneg (by positivity) _
  set F : (Fin d → ℤ) → ℝ := fun v => ∏ i, f (v i) with hF
  have hF0 : ∀ v, 0 ≤ F v := fun v => Finset.prod_nonneg fun i _ => hf0 _
  have hFs : ∀ S : Finset (Fin d → ℤ), ∑ v ∈ S, F v ≤ (∑' n, f n) ^ d := by
    intro S
    classical
    set t : Fin d → Finset ℤ := fun i => S.image fun v => v i
    have hsub : S ⊆ Fintype.piFinset t := fun v hv =>
      Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hv
    calc ∑ v ∈ S, F v ≤ ∑ v ∈ Fintype.piFinset t, F v :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hF0 v)
      _ = ∏ i, ∑ n ∈ t i, f n := (Finset.prod_univ_sum t (fun _ => f)).symm
      _ ≤ ∏ _i : Fin d, ∑' n, f n :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun n _ => hf0 n)
            (fun i _ => hs1.sum_le_tsum _ (fun n _ => hf0 n))
      _ = (∑' n, f n) ^ d := by simp
  have hFsum : Summable F := summable_of_sum_le hF0 hFs
  have hFt : ∑' v, F v ≤ (∑' n, f n) ^ d := Real.tsum_le_of_sum_le hF0 hFs
  have hpt : ∀ v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-γ) ≤ (W : ℝ) ^ (-(γ - d * α)) * F v := by
    intro v
    set M : ℝ := (zdInf v : ℝ) + W with hM
    have hWM : (W : ℝ) ≤ M := by
      have := Nat.cast_nonneg (α := ℝ) (zdInf v); linarith
    have hM0 : 0 < M := lt_of_lt_of_le hW0 hWM
    have hsplit : M ^ (-γ) = M ^ (-(γ - d * α)) * (M ^ (-α)) ^ d := by
      rw [← Real.rpow_mul_natCast hM0.le, ← Real.rpow_add hM0]
      congr 1; ring
    rw [hsplit]
    apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hW0 hWM (by linarith))
      _ (pow_nonneg (Real.rpow_nonneg hM0.le _) _) (Real.rpow_nonneg hW0.le _)
    rw [← Fin.prod_const]
    refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hM0.le _) fun i _ => ?_
    have hvi : |((v i : ℤ) : ℝ)| ≤ (zdInf v : ℝ) := by
      have h := Finset.le_sup (f := fun i => (v i).natAbs) (Finset.mem_univ i)
      have h' : (((v i).natAbs : ℕ) : ℝ) ≤ (zdInf v : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_natAbs, Int.cast_abs] at h'
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hs : Summable (fun v : Fin d → ℤ => ((zdInf v : ℝ) + W) ^ (-γ)) :=
    Summable.of_nonneg_of_le (fun v => Real.rpow_nonneg (by positivity) _) hpt
      (hFsum.mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-γ) ≤ ∑' v, (W : ℝ) ^ (-(γ - d * α)) * F v :=
        hs.tsum_le_tsum hpt (hFsum.mul_left _)
    _ = (W : ℝ) ^ (-(γ - d * α)) * ∑' v, F v := tsum_mul_left
    _ ≤ (W : ℝ) ^ (-(γ - d * α)) * (C₁ * (W : ℝ) ^ (1 - α)) ^ d := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hW0.le _)
        exact hFt.trans (pow_le_pow_left₀ (tsum_nonneg hf0) hb1 d)
    _ = C₁ ^ d * (W : ℝ) ^ ((d : ℝ) - γ) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hW0.le, mul_left_comm, ← Real.rpow_add hW0]
        congr 2; ring

/-! ## The one-vertex sum -/

/-- The one-vertex sum on `ℤ^d`: for `β, s ≥ 0` with `β + s > d`, the sum over `z ∈ ℤ^d` of
`B^β_{zu} W^{-b} ⟨z - p⟩^{-s}` is finite and at most `C W^{-2-b} W^{d-β-s}`, uniformly in `W ≥ 1`,
`b` and `p, u`. -/
theorem vertex : ∀ (d : ℕ) (β s : ℝ), 0 ≤ β → 0 ≤ s → (d : ℝ) < β + s →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W → ∀ (b : ℝ) (p u : Fin d → ℤ),
      Summable (fun z => bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s))) ∧
        ∑' z, bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s)) ≤
          C * (W : ℝ) ^ (-2 - b) * (W : ℝ) ^ ((d : ℝ) - β - s) := by
  intro d β s hβ hs hd
  obtain ⟨CL, hCL, hL⟩ := latSum d (β + s) hd
  refine ⟨2 * CL, by positivity, fun W hW b p u => ?_⟩
  obtain ⟨hLs, hLb⟩ := hL W hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set h : (Fin d → ℤ) → ℝ := fun v => ((zdInf v : ℝ) + W) ^ (-(β + s)) with hh
  have hshift : ∀ a : Fin d → ℤ, (fun z => brk d W z a ^ (-(β + s))) = fun z => h (z - a) := by
    intro a; rfl
  have hsa : ∀ a : Fin d → ℤ, Summable (fun z => brk d W z a ^ (-(β + s))) := by
    intro a
    rw [hshift]
    exact (Equiv.subRight a).summable_iff.2 hLs
  have hta : ∀ a : Fin d → ℤ, ∑' z, brk d W z a ^ (-(β + s)) = ∑' v, h v := by
    intro a
    rw [hshift]
    exact (Equiv.subRight a).tsum_eq h
  have hpt : ∀ z, bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s)) ≤
      (W : ℝ) ^ (-2 - b) * (brk d W z u ^ (-(β + s)) + brk d W z p ^ (-(β + s))) := by
    intro z
    have hu0 := brk_pos hW z u
    have hp0 := brk_pos hW z p
    have hWb : (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-b) = (W : ℝ) ^ (-2 - b) := by
      rw [← Real.rpow_add hW0]; ring_nf
    have hprod : brk d W z u ^ (-β) * brk d W z p ^ (-s) ≤
        brk d W z u ^ (-(β + s)) + brk d W z p ^ (-(β + s)) := by
      rcases le_total (brk d W z u) (brk d W z p) with hle | hle
      · have h1 : brk d W z p ^ (-s) ≤ brk d W z u ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hu0 hle (by linarith)
        calc brk d W z u ^ (-β) * brk d W z p ^ (-s) ≤ brk d W z u ^ (-β) * brk d W z u ^ (-s) :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hu0.le _)
          _ = brk d W z u ^ (-(β + s)) := by rw [← Real.rpow_add hu0]; ring_nf
          _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg hp0.le _)
      · have h1 : brk d W z u ^ (-β) ≤ brk d W z p ^ (-β) :=
          Real.rpow_le_rpow_of_nonpos hp0 hle (by linarith)
        calc brk d W z u ^ (-β) * brk d W z p ^ (-s) ≤ brk d W z p ^ (-β) * brk d W z p ^ (-s) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp0.le _)
          _ = brk d W z p ^ (-(β + s)) := by rw [← Real.rpow_add hp0]; ring_nf
          _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg hu0.le _)
    unfold bB
    calc (W : ℝ) ^ (-2 : ℝ) * brk d W z u ^ (-β) * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s))
        = ((W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-b)) * (brk d W z u ^ (-β) * brk d W z p ^ (-s)) := by
          ring
      _ ≤ _ := by
          rw [hWb]
          exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hW0.le _)
  have h0 : ∀ z, 0 ≤ bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s)) := fun z =>
    mul_nonneg (bB_pos hW β z u).le
      (mul_nonneg (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg (brk_pos hW z p).le _))
  have hsb : Summable (fun z => (W : ℝ) ^ (-2 - b) *
      (brk d W z u ^ (-(β + s)) + brk d W z p ^ (-(β + s)))) :=
    ((hsa u).add (hsa p)).mul_left _
  have hs' := Summable.of_nonneg_of_le h0 hpt hsb
  refine ⟨hs', ?_⟩
  calc ∑' z, bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s))
      ≤ ∑' z, (W : ℝ) ^ (-2 - b) * (brk d W z u ^ (-(β + s)) + brk d W z p ^ (-(β + s))) :=
        hs'.tsum_le_tsum hpt hsb
    _ = (W : ℝ) ^ (-2 - b) * (2 * ∑' v, h v) := by
        rw [tsum_mul_left, (hsa u).tsum_add (hsa p), hta, hta]; ring
    _ ≤ (W : ℝ) ^ (-2 - b) * (2 * (CL * (W : ℝ) ^ ((d : ℝ) - (β + s)))) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hW0.le _)
    _ = _ := by rw [show (d : ℝ) - β - s = (d : ℝ) - (β + s) by ring]; ring

/-! ## The core estimate -/

private theorem kerProps {d W : ℕ} (hW : 1 ≤ W) {c₀ t : ℝ} (hc₀ : 0 ≤ c₀) (ht : 0 ≤ t) :
    (∀ p q : Fin d → ℤ, 0 ≤ c₀ * brk d W p q ^ (-t)) ∧
    (∀ p q : Fin d → ℤ, c₀ * brk d W p q ^ (-t) = c₀ * brk d W q p ^ (-t)) ∧
    (∀ p q : Fin d → ℤ, c₀ * brk d W p p ^ (-t) = c₀ * brk d W q q ^ (-t)) ∧
    (∀ z u v : Fin d → ℤ, c₀ * brk d W z u ^ (-t) ≤ c₀ * brk d W z v ^ (-t) →
      c₀ * brk d W z u ^ (-t) ≤ (2 : ℝ) ^ t * (c₀ * brk d W v u ^ (-t))) :=
  ⟨fun p q => mul_nonneg hc₀ (Real.rpow_nonneg (brk_pos hW p q).le _),
    fun p q => by rw [brk_comm],
    fun p q => by rw [brk_self p q],
    fun z u v h => ker_rehang hW hc₀ ht z u v h⟩

/-- [I, Claim 6.11], strong form ([I, (6.31)]), on `ℤ^d` and pointwise: let the black and the blue
edges of `Γ` form spanning trees, `|A_j(p, r)| ≤ W^{-b} ⟨p - r⟩^{-s}`, and every one-vertex sum
`Σ_z B^β_{zu} W^{-b} ⟨z - p⟩^{-s}` be finite and at most `c₁`. Then for all `x, y` the summand of
the value is summable and `Γ̃_{xy} ≤ C c₁^ℓ W^{-b} ⟨x - y⟩^{-s} B^β_{xy}`, with `C` independent
of `W`, `A`, `c₁`, `x` and `y`. -/
theorem core : ∀ (d : ℕ) (β s b : ℝ), 0 ≤ β → 0 ≤ s → ∀ {ℓ : ℕ} (Γ : AuxGraph ℓ),
    TreeEdges Γ.black → TreeEdges (Γ.blue.map fun e => (e.1, e.2.1)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W →
      ∀ (A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (c₁ : ℝ), 0 ≤ c₁ →
      (∀ p u : Fin d → ℤ,
        Summable (fun z => bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s))) ∧
          ∑' z, bB d W β z u * ((W : ℝ) ^ (-b) * brk d W z p ^ (-s)) ≤ c₁) →
      (∀ j p r, |A j p r| ≤ (W : ℝ) ^ (-b) * brk d W p r ^ (-s)) →
      ∀ x y : Fin d → ℤ, Summable (Γ.termZ d W β A x y) ∧
        Γ.valZ d W β A x y ≤
          C * c₁ ^ ℓ * ((W : ℝ) ^ (-b) * brk d W x y ^ (-s)) * bB d W β x y := by
  intro d β s b hβ hs ℓ Γ hT hU
  set cB : ℝ := (2 : ℝ) ^ β with hcBdef
  set cK : ℝ := (2 : ℝ) ^ s with hcKdef
  have hcB : 1 ≤ cB := Real.one_le_rpow (by norm_num) hβ
  have hcK : 1 ≤ cK := Real.one_le_rpow (by norm_num) hs
  refine ⟨cB ^ ((ℓ + 1) ^ 2) * cK ^ ((ℓ + 1) ^ 2) * (((ℓ : ℝ) + 2) ^ 2) ^ ℓ, by positivity, ?_⟩
  intro W hW A c₁ hc₁ hV hA x y
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set kB : (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun p q => (W : ℝ) ^ (-2 : ℝ) * brk d W p q ^ (-β)
    with hkB
  set kK : (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun p q => (W : ℝ) ^ (-b) * brk d W p q ^ (-s)
    with hkK
  obtain ⟨hB0, hBs, hBd, hBr⟩ := kerProps (d := d) hW (Real.rpow_nonneg hW0.le (-2 : ℝ)) hβ
  obtain ⟨hK0, hKs, hKd, hKr⟩ := kerProps (d := d) hW (Real.rpow_nonneg hW0.le (-b)) hs
  set P : (Fin ℓ → Fin d → ℤ) → Atom 2 ℓ → Fin d → ℤ := fun σ => Sum.elim ![x, y] σ with hP
  set SB : Fin ℓ → (Fin ℓ → Fin d → ℤ) → ℝ :=
    fun j σ => ∑ w ∈ later j, kB (P σ (Sum.inr j)) (P σ w) with hSB
  set SK : Fin ℓ → (Fin ℓ → Fin d → ℤ) → ℝ :=
    fun j σ => ∑ w ∈ later j, kK (P σ (Sum.inr j)) (P σ w) with hSK
  have hSB0 : ∀ j σ, 0 ≤ SB j σ := fun j σ => Finset.sum_nonneg fun w _ => hB0 _ _
  have hSK0 : ∀ j σ, 0 ≤ SK j σ := fun j σ => Finset.sum_nonneg fun w _ => hK0 _ _
  set K₀ : ℝ := cB ^ ((ℓ + 1) ^ 2) * cK ^ ((ℓ + 1) ^ 2) * (kK x y * bB d W β x y) with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have := hK0 x y
    have := bB_pos hW β x y
    positivity
  -- the pointwise bound
  have hpt : ∀ σ, Γ.termZ d W β A x y σ ≤ K₀ * ∏ j, (SB j σ * SK j σ) := by
    intro σ
    have hb := treeBound kB cB hcB hB0 hBs hBd hBr (P σ) Γ.black hT
    have hu := treeBound kK cK hcK hK0 hKs hKd hKr (P σ) _ hU
    have hblack : (Γ.black.map fun e =>
        bB d W β (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2)).prod =
        kprod kB (P σ) Γ.black := rfl
    have hblue : (Γ.blue.map fun e =>
        |A e.2.2 (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2.1)|).prod ≤
        kprod kK (P σ) (Γ.blue.map fun e => (e.1, e.2.1)) := by
      have := prod_map_le_pow Γ.blue
        (fun e => |A e.2.2 (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2.1)|)
        (fun e => kK (P σ e.1) (P σ e.2.1)) 1 (fun e _ => ⟨abs_nonneg _, by
          rw [one_mul]; exact hA _ _ _⟩)
      rw [one_pow, one_mul] at this
      simpa [kprod, List.map_map, Function.comp_def] using this
    have hx : P σ (Sum.inl 0) = x := rfl
    have hy : P σ (Sum.inl 1) = y := rfl
    rw [hx, hy] at hb hu
    have hbl0 : 0 ≤ (Γ.blue.map fun e =>
        |A e.2.2 (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2.1)|).prod :=
      List.prod_nonneg fun a ha => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
        exact abs_nonneg _
    have hbk0 : 0 ≤ kprod kB (P σ) Γ.black := List.prod_nonneg fun a ha => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha
        exact hB0 _ _
    unfold AuxGraph.termZ
    rw [hblack]
    calc kprod kB (P σ) Γ.black * (Γ.blue.map fun e =>
          |A e.2.2 (Sum.elim ![x, y] σ e.1) (Sum.elim ![x, y] σ e.2.1)|).prod
        ≤ (cB ^ ((ℓ + 1) ^ 2) * kB x y * ∏ j, SB j σ) *
          (cK ^ ((ℓ + 1) ^ 2) * kK x y * ∏ j, SK j σ) :=
          mul_le_mul hb (hblue.trans hu) hbl0
            (mul_nonneg (mul_nonneg (by positivity) (hB0 _ _))
              (Finset.prod_nonneg fun j _ => hSB0 j σ))
      _ = K₀ * ∏ j, (SB j σ * SK j σ) := by
          rw [Finset.prod_mul_distrib, hK₀]
          simp only [hkB, bB]
          ring
  -- dependence of the factors on the coordinates
  have hPw : ∀ (j : Fin ℓ) (σ τ : Fin ℓ → Fin d → ℤ), (∀ m, j ≤ m → σ m = τ m) →
      P σ (Sum.inr j) = P τ (Sum.inr j) ∧ ∀ w ∈ later j, P σ w = P τ w := by
    intro j σ τ h
    refine ⟨h j le_rfl, fun w hw => ?_⟩
    rcases w with a | m
    · rfl
    · have hjm : j < m := (Finset.mem_filter.1 hw).2 m rfl
      exact h m hjm.le
  have hupd : ∀ (j : Fin ℓ) (σ : Fin ℓ → Fin d → ℤ) (z : Fin d → ℤ),
      P (Function.update σ j z) (Sum.inr j) = z ∧
        ∀ w ∈ later j, P (Function.update σ j z) w = P σ w := by
    intro j σ z
    refine ⟨by simp [hP], fun w hw => ?_⟩
    rcases w with a | m
    · rfl
    · have hjm : j < m := (Finset.mem_filter.1 hw).2 m rfl
      simp [hP, Function.update_of_ne hjm.ne']
  set G : Fin ℓ → (Fin ℓ → Fin d → ℤ) → ℝ≥0∞ :=
    fun j σ => ENNReal.ofReal (SB j σ * SK j σ) with hG
  have hdep : ∀ j σ τ, (∀ m, j ≤ m → σ m = τ m) → G j σ = G j τ := by
    intro j σ τ h
    obtain ⟨h1, h2⟩ := hPw j σ τ h
    have e1 : SB j σ = SB j τ := Finset.sum_congr rfl fun w hw => by rw [h1, h2 w hw]
    have e2 : SK j σ = SK j τ := Finset.sum_congr rfl fun w hw => by rw [h1, h2 w hw]
    simp only [hG, e1, e2]
  have hsum : ∀ j σ, ∑' z, G j (Function.update σ j z) ≤
      ENNReal.ofReal (((ℓ : ℝ) + 2) ^ 2 * c₁) := by
    intro j σ
    have hexp : ∀ z, G j (Function.update σ j z) = ∑ w ∈ later j, ∑ w' ∈ later j,
        ENNReal.ofReal (kB z (P σ w) * kK z (P σ w')) := by
      intro z
      obtain ⟨h1, h2⟩ := hupd j σ z
      have e1 : SB j (Function.update σ j z) = ∑ w ∈ later j, kB z (P σ w) :=
        Finset.sum_congr rfl fun w hw => by rw [h1, h2 w hw]
      have e2 : SK j (Function.update σ j z) = ∑ w ∈ later j, kK z (P σ w) :=
        Finset.sum_congr rfl fun w hw => by rw [h1, h2 w hw]
      simp only [hG, e1, e2]
      rw [Finset.sum_mul_sum,
        ENNReal.ofReal_sum_of_nonneg fun w _ =>
          Finset.sum_nonneg fun w' _ => mul_nonneg (hB0 _ _) (hK0 _ _)]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun w' _ => mul_nonneg (hB0 _ _) (hK0 _ _)]
    simp_rw [hexp]
    rw [Summable.tsum_finsetSum fun w _ => ENNReal.summable]
    have hone : ∀ u q : Fin d → ℤ, ∑' z, ENNReal.ofReal (kB z u * kK z q) ≤ ENNReal.ofReal c₁ := by
      intro u q
      obtain ⟨hsq, hbq⟩ := hV q u
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hB0 _ _) (hK0 _ _)) hsq]
      exact ENNReal.ofReal_le_ofReal hbq
    calc ∑ w ∈ later j, ∑' z, ∑ w' ∈ later j, ENNReal.ofReal (kB z (P σ w) * kK z (P σ w'))
        = ∑ w ∈ later j, ∑ w' ∈ later j, ∑' z, ENNReal.ofReal (kB z (P σ w) * kK z (P σ w')) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Summable.tsum_finsetSum fun w' _ => ENNReal.summable]
      _ ≤ ∑ w ∈ later j, ∑ w' ∈ later j, ENNReal.ofReal c₁ :=
          Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun w' _ => hone _ _
      _ = ENNReal.ofReal ((later j).card * ((later j).card * c₁)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hcard : ((later j).card : ℝ) ≤ (ℓ : ℝ) + 2 := by
            exact_mod_cast card_later_le j
          have hc0 : (0 : ℝ) ≤ (later j).card := Nat.cast_nonneg _
          nlinarith [mul_le_mul hcard hcard hc0 (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) + 2)]
  have hE : ∑' σ, ENNReal.ofReal (Γ.termZ d W β A x y σ) ≤
      ENNReal.ofReal (K₀ * (((ℓ : ℝ) + 2) ^ 2 * c₁) ^ ℓ) := by
    calc ∑' σ, ENNReal.ofReal (Γ.termZ d W β A x y σ)
        ≤ ∑' σ, ENNReal.ofReal K₀ * ∏ j, G j σ := by
          refine ENNReal.tsum_le_tsum fun σ => ?_
          rw [hG, ← ENNReal.ofReal_prod_of_nonneg fun j _ => mul_nonneg (hSB0 j σ) (hSK0 j σ),
            ← ENNReal.ofReal_mul hK₀0]
          exact ENNReal.ofReal_le_ofReal (hpt σ)
      _ = ENNReal.ofReal K₀ * ∑' σ, ∏ j, G j σ := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal K₀ * ENNReal.ofReal (((ℓ : ℝ) + 2) ^ 2 * c₁) ^ ℓ :=
          mul_le_mul_right (tsum_prod_le ℓ G _ hdep hsum) _
      _ = _ := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hK₀0]
  obtain ⟨hsum', hbound⟩ := summable_of_ennreal
    (fun σ => termZ_nonneg Γ hW β A x y σ) (by positivity) hE
  refine ⟨hsum', ?_⟩
  unfold AuxGraph.valZ
  calc ∑' σ, Γ.termZ d W β A x y σ ≤ K₀ * (((ℓ : ℝ) + 2) ^ 2 * c₁) ^ ℓ := hbound
    _ = _ := by rw [hK₀, mul_pow]; ring

/-- [I, Claim 6.11] on `ℤ^d` for `d ≥ 6` in the form of [I, Cor 7.6]: for an auxiliary graph whose
black and blue edges form spanning trees and every `τ > 0` there are `τ₁ > 0` and `W₀` such that
for `W ≥ W₀`, black edges `B^{d-2-τ₁}` and blue kernels with `|A_j| ≤ B^{d-2-τ₁}`, the summand
of the value is summable and
`Γ̃_{xy} ≤ W^{-(2ℓ+4)d/2} W^{2d-4} ⟨x - y⟩^{-(2d-4-τ)}`; `2ℓ + 4` is the order of the graph. -/
theorem _root_.RBM8D.auxTreeZStrong : ∀ (d : ℕ), 6 ≤ d → ∀ {ℓ : ℕ} (Γ : AuxGraph ℓ),
    TreeEdges Γ.black → TreeEdges (Γ.blue.map fun e => (e.1, e.2.1)) →
    ∀ τ : ℝ, 0 < τ → ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W →
      ∀ A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ,
        (∀ j p r, |A j p r| ≤ bB d W ((d : ℝ) - 2 - τ₁) p r) →
        ∀ x y : Fin d → ℤ, Summable (Γ.termZ d W ((d : ℝ) - 2 - τ₁) A x y) ∧
          Γ.valZ d W ((d : ℝ) - 2 - τ₁) A x y ≤
            (W : ℝ) ^ (-((2 * (ℓ : ℝ) + 4) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
              brk d W x y ^ (-(2 * (d : ℝ) - 4 - τ)) := by
  intro d hd ℓ Γ hT hU τ hτ
  have hd6 : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set τ' : ℝ := min τ 1 with hτ'
  have hτ'0 : 0 < τ' := lt_min hτ one_pos
  have hτ'τ : τ' ≤ τ := min_le_left _ _
  have hτ'1 : τ' ≤ 1 := min_le_right _ _
  set τ₁ : ℝ := τ' / (2 * ℓ + 4) with hτ₁
  have hden : (0 : ℝ) < 2 * ℓ + 4 := by positivity
  have hτ₁0 : 0 < τ₁ := div_pos hτ'0 hden
  have hτ₁m : (2 * ℓ + 4) * τ₁ = τ' := by rw [hτ₁]; field_simp
  have hτ₁le : τ₁ ≤ 1 / 4 := by
    rw [hτ₁, div_le_iff₀ hden]; nlinarith
  set β : ℝ := (d : ℝ) - 2 - τ₁ with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  obtain ⟨C₃, hC₃, hV⟩ := vertex d β β hβ0 hβ0 (by rw [hβ]; linarith)
  obtain ⟨C₄, hC₄, hC⟩ := core d β β 2 hβ0 hβ0 Γ hT hU
  set σ' : ℝ := τ - (2 * ℓ + 2) * τ₁ with hσ'
  have hσ'0 : 0 < σ' := by rw [hσ']; nlinarith
  set C' : ℝ := C₄ * C₃ ^ ℓ with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC₄ (pow_nonneg hC₃ ℓ)
  refine ⟨τ₁, hτ₁0, max 1 (C' ^ (1 / σ')), fun W hW A hA x y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set c₁ : ℝ := C₃ * (W : ℝ) ^ ((-2 : ℝ) - 2) * (W : ℝ) ^ ((d : ℝ) - β - β) with hc₁
  have hc₁0 : 0 ≤ c₁ :=
    mul_nonneg (mul_nonneg hC₃ (Real.rpow_nonneg hW0.le _)) (Real.rpow_nonneg hW0.le _)
  obtain ⟨hsum, hval⟩ := hC W hWn A c₁ hc₁0 (fun p u => hV W hWn 2 p u) hA x y
  refine ⟨hsum, hval.trans ?_⟩
  set t : ℝ := brk d W x y with ht
  have ht0 : 0 < t := brk_pos hWn x y
  have hWt : (W : ℝ) ≤ t := W_le_brk x y
  have hc₁' : c₁ ^ ℓ = C₃ ^ ℓ * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ) := by
    rw [hc₁, mul_assoc, ← Real.rpow_add hW0, mul_pow, ← Real.rpow_mul_natCast hW0.le]
    congr 3
    rw [hβ]; ring
  have hWexp : (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ) * (W : ℝ) ^ (-2 : ℝ) * (W : ℝ) ^ (-2 : ℝ) =
      (W : ℝ) ^ (-((2 * (ℓ : ℝ) + 4) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
        (W : ℝ) ^ (2 * τ₁ * ℓ) := by
    simp only [← Real.rpow_add hW0]
    congr 1; ring
  have htexp : t ^ (-β) * t ^ (-β) = t ^ (-(2 * (d : ℝ) - 4 - τ)) * t ^ (2 * τ₁ - τ) := by
    rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
    congr 1; rw [hβ]; ring
  have hkey : C' * (W : ℝ) ^ (2 * τ₁ * ℓ) * t ^ (2 * τ₁ - τ) ≤ 1 := by
    have h1 : (W : ℝ) ^ (2 * τ₁ * ℓ) ≤ t ^ (2 * τ₁ * ℓ) :=
      Real.rpow_le_rpow hW0.le hWt (by positivity)
    have h2 : t ^ (2 * τ₁ * ℓ) * t ^ (2 * τ₁ - τ) = t ^ (-σ') := by
      rw [← Real.rpow_add ht0]; congr 1; rw [hσ']; ring
    have h3 : t ^ (-σ') ≤ (W : ℝ) ^ (-σ') :=
      Real.rpow_le_rpow_of_nonpos hW0 hWt (by linarith)
    have h4 : C' ≤ (W : ℝ) ^ σ' := by
      have h5 : C' ^ (1 / σ') ≤ (W : ℝ) := (le_max_right _ _).trans hW
      calc C' = (C' ^ (1 / σ')) ^ σ' := by
            rw [one_div, Real.rpow_inv_rpow hC'0 hσ'0.ne']
        _ ≤ (W : ℝ) ^ σ' := Real.rpow_le_rpow (Real.rpow_nonneg hC'0 _) h5 hσ'0.le
    have h6 : C' * (W : ℝ) ^ (-σ') ≤ 1 := by
      rw [Real.rpow_neg hW0.le, ← div_eq_mul_inv]
      exact div_le_one_of_le₀ h4 (Real.rpow_nonneg hW0.le _)
    calc C' * (W : ℝ) ^ (2 * τ₁ * ℓ) * t ^ (2 * τ₁ - τ)
        ≤ C' * t ^ (2 * τ₁ * ℓ) * t ^ (2 * τ₁ - τ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC'0)
            (Real.rpow_nonneg ht0.le _)
      _ = C' * t ^ (-σ') := by rw [mul_assoc, h2]
      _ ≤ C' * (W : ℝ) ^ (-σ') := mul_le_mul_of_nonneg_left h3 hC'0
      _ ≤ 1 := h6
  have hR0 : 0 ≤ (W : ℝ) ^ (-((2 * (ℓ : ℝ) + 4) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      t ^ (-(2 * (d : ℝ) - 4 - τ)) := by positivity
  calc C₄ * c₁ ^ ℓ * ((W : ℝ) ^ (-2 : ℝ) * t ^ (-β)) * bB d W β x y
      = ((W : ℝ) ^ (-((2 * (ℓ : ℝ) + 4) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          t ^ (-(2 * (d : ℝ) - 4 - τ))) * (C' * (W : ℝ) ^ (2 * τ₁ * ℓ) * t ^ (2 * τ₁ - τ)) := by
        rw [hc₁']
        unfold bB
        rw [← ht]
        calc C₄ * (C₃ ^ ℓ * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ)) * ((W : ℝ) ^ (-2 : ℝ) * t ^ (-β)) *
              ((W : ℝ) ^ (-2 : ℝ) * t ^ (-β))
            = C' * ((W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ) * (W : ℝ) ^ (-2 : ℝ) *
                (W : ℝ) ^ (-2 : ℝ)) * (t ^ (-β) * t ^ (-β)) := by rw [hC']; ring
          _ = _ := by rw [hWexp, htexp]; ring
    _ ≤ ((W : ℝ) ^ (-((2 * (ℓ : ℝ) + 4) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          t ^ (-(2 * (d : ℝ) - 4 - τ))) * 1 := mul_le_mul_of_nonneg_left hkey hR0
    _ = _ := mul_one _

end AuxTreeZ

end RBM8D
