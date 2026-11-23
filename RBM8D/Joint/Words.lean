module

public import RBM8D.TExp.Defs

@[expose] public section

/-!
# Words of self-energy orders and the labelled `Θ` edges they give

The iteration of [II, (3.5)] ([II, (6.1)–(6.3)]) expands `(Θ Σ̃^{(n)})^k Θ` as the sum of the
labelled `Θ` edges `Θ^{[o]}` over the words `o = (o₁, …, o_k)` in the even orders `4, …, n` of
`Σ̃^{(n)}` ([II, (3.14)]). This file has

* the words of length `≤ K` (`G14.sigOrders`, `G14.words`, `G14.wordsUpTo`), the words that are not
  labels of `Σ_T^{(n)}` (`G14.extra`, [II, (3.3)–(3.4)]), the relabelling of a graph at `⊗`
  (`G14.relabels`), the leading graphs beyond `Σ_T^{(n)}` (`G14.overflow`) and the record of the
  solution of an `n`-th order `T`-equation (`G14.solveRec`);
* the graphs `Σ_x Θ_{⊗x} 𝒢_x` with `𝒢` not reading `⊗` (`G14.RootedTheta`);
* membership, nodup and the split `wordsUpTo n K ~ ([] :: chainLabels n) ++ extra n K` for
  `(n − 2)/2 ≤ K`;
* the excess `Words.labelInc o = Σ (oᵢ − 2)` of a label: the scaling order of `Θ^{[o]}` is
  `2 + labelInc o`, `labelInc o ≥ n − 1` on `G14.extra n K`, and the order of a graph
  `Σ_x Θ_{⊗x} 𝒢_x` with its `Θ` edge relabelled by `o` is the order of the graph plus
  `Σ oᵢ − 2|o|`.
-/

noncomputable section

namespace RBM8D

open Graphs

/-! ## Words, relabelling and the record of the solution -/

/-- The even orders `4 ≤ l ≤ n`: the orders of the self-energies in
`Σ̃^{(n)} = Σ_n + Σ_{l=4}^{n-1} Σ_l` of [II, (3.14)] (the odd orders vanish, [II, (2.6)]). -/
def G14.sigOrders (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter fun l => decide (4 ≤ l) && l % 2 == 0

/-- The words of length `k` in the orders `G14.sigOrders n`: the labels `o` of the terms
`Θ Σ_{o₁} Θ ⋯ Σ_{o_k} Θ` of `(Θ Σ̃^{(n)})^k Θ`. -/
def G14.words (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (G14.words n k).flatMap fun o => (G14.sigOrders n).map fun l => o ++ [l]

/-- The words of length `≤ K` in the orders `G14.sigOrders n`, by increasing length. -/
def G14.wordsUpTo (n K : ℕ) : List (List ℕ) := (List.range (K + 1)).flatMap (G14.words n)

/-- The words of length `≤ K` other than the empty word and the labels `chainLabels n` of order
`≤ n`. -/
def G14.extra (n K : ℕ) : List (List ℕ) :=
  (G14.wordsUpTo n K).filter fun o => decide (o ∉ [] :: chainLabels n)

/-- Every graph of `S` with its `Θ` edge at `⊗` relabelled by each word of `W`. -/
def G14.relabels (W : List (List ℕ)) (S : Expansion 3) : Expansion 3 :=
  S.flatMap fun g => W.map fun o => ⟨g.1, g.2.relabelRoot o⟩

/-- The leading term beyond `Σ_T^{(n)}` ([II, §6.1]): the `O_dot` forms of
`m Θ^{[o]}_{⊗⊕} Ḡ_{⊕⊖}` for the words `o` of `G14.extra n K`. -/
def G14.overflow (n K : ℕ) : Expansion 3 :=
  (G14.extra n K).flatMap fun o => oDot (thetaLabelGraph o)

/-- The record of the `n`-th order `T`-expansion obtained from the `n`-th order `T`-equation `𝒬`
by the `K`-fold iteration of [II, (3.5)] ([II, (6.1)–(6.3)]), with the remainder `Rem` of
`(Θ Σ̃)^{K+1} T`:
* `R`: the graphs of `TEqRec.solveLow` from `R_IT` of order `≤ n`;
* `A`: those of order `> n`, the graphs of `R_IT` relabelled by `G14.extra`, the graphs of
  `A_IT` relabelled by every word, and `G14.overflow`;
* `Q`: the graphs of `TEqRec.solveLow` from `Q_IT` and those relabelled by `G14.extra`;
* `Err`: the graphs of `Err'` relabelled by every word, and `Rem`. -/
def G14.solveRec (n K : ℕ) (𝒬 : TEqRec) (Rem : Expansion 3) : TRec where
  R := (𝒬.solveLow n).R.filter fun g => decide (g.2.ord ≤ (n : ℤ))
  A := (𝒬.solveLow n).R.filter (fun g => decide ((n : ℤ) < g.2.ord)) ++
    G14.relabels (G14.extra n K) 𝒬.R ++ G14.relabels (G14.wordsUpTo n K) 𝒬.A ++
    G14.overflow n K
  Q := (𝒬.solveLow n).Q ++ G14.relabels (G14.extra n K) 𝒬.Q
  Err := G14.relabels (G14.wordsUpTo n K) 𝒬.Err ++ Rem

/-- The graph is `Σ_x Θ_{⊗x} 𝒢_x` with `𝒢` not reading `⊗` ([II, Def 3.3 (4)] without the normal
form of `𝒢`): one plain `Θ` edge without minor and label has first index `⊗` and second index
`≠ ⊗`, and the rest does not mention `⊗` (neither in the ends, the minor atoms, nor the atom of a
label). The leading graph `m Θ_{⊗⊕} Ḡ_{⊕⊖}` and every graph of the form `Graph.ThetaRooted` have
it. -/
def G14.RootedTheta {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ∃ j : Fin Γ.comps.length, Γ.comps[j].kind = .theta [] ∧ Γ.comps[j].minor = [] ∧
    Γ.comps[j].label = none ∧ Γ.comps[j].x = .inl 0 ∧ Γ.comps[j].y ≠ .inl 0 ∧
    ∀ c ∈ (Γ.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0)

/-- A graph of the form [II, Def 3.3 (4)] (`Graph.ThetaRooted`) is `Σ_x Θ_{⊗x} 𝒢_x` with `𝒢` not
reading `⊗`. -/
theorem G14.rootedTheta_of_thetaRooted {n : ℕ} {Γ : Graph 3 n} (h : Γ.ThetaRooted) :
    G14.RootedTheta Γ := by
  obtain ⟨j, v, hv, hk, hm, hl, ⟨hx, hy⟩, hrest, -⟩ := h
  exact ⟨j, hk, hm, hl, hx, hy ▸ hv, hrest⟩

namespace Words

/-! ## The excess of a label -/

/-- The excess `Σ (oᵢ − 2)` of a label `o`: for entries `≥ 2` the scaling order of the `Θ` edge
with label `o` is `2 + labelInc o` ([II, (2.5)]). -/
def labelInc (o : List ℕ) : ℕ := (o.map (· - 2)).sum

@[simp] theorem labelInc_nil : labelInc [] = 0 := rfl

/-- The excess of a nonempty label. -/
theorem labelInc_cons (e : ℕ) (o : List ℕ) : labelInc (e :: o) = (e - 2) + labelInc o := by
  simp [labelInc]

/-- Each entry `e` of a label contributes `e - 2` to its excess. -/
theorem le_labelInc_of_mem {e : ℕ} {o : List ℕ} (h : e ∈ o) : e - 2 ≤ labelInc o := by
  induction o with
  | nil => simp at h
  | cons a o ih =>
    rw [labelInc_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- The excess of a label with entries `≥ 2`, as an integer: `Σ oᵢ − 2|o|`. -/
theorem labelInc_cast : ∀ o : List ℕ, (∀ e ∈ o, 2 ≤ e) →
    ((labelInc o : ℕ) : ℤ) = (o.sum : ℤ) - 2 * o.length := by
  intro o
  induction o with
  | nil => intro _; simp
  | cons e o ih =>
    intro h
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h e (List.mem_cons_self ..)
    rw [labelInc_cons, Nat.cast_add, Nat.cast_sub h2, h1, List.sum_cons, List.length_cons]
    push_cast
    ring

/-- A label with entries `≥ 4` has excess `≥ 2|o|`. -/
theorem two_mul_length_le_labelInc : ∀ o : List ℕ, (∀ e ∈ o, 4 ≤ e) →
    2 * o.length ≤ labelInc o := by
  intro o
  induction o with
  | nil => intro _; simp
  | cons e o ih =>
    intro h
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h e (List.mem_cons_self ..)
    rw [labelInc_cons, List.length_cons]
    omega

/-! ## Membership -/

/-- The orders of `G14.sigOrders n` are the even `l` with `4 ≤ l ≤ n`. -/
theorem mem_sigOrders {n l : ℕ} : l ∈ G14.sigOrders n ↔ 4 ≤ l ∧ l ≤ n ∧ l % 2 = 0 := by
  simp only [G14.sigOrders, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  omega

/-- The words of `G14.words n k` are the lists of length `k` with entries in `G14.sigOrders n`. -/
theorem mem_words {n : ℕ} : ∀ (k : ℕ) (o : List ℕ),
    o ∈ G14.words n k ↔ o.length = k ∧ ∀ e ∈ o, e ∈ G14.sigOrders n
  | 0, o => by
    simp only [G14.words, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      simp
    · exact fun h => h.1
  | k + 1, o => by
    simp only [G14.words, List.mem_flatMap, List.mem_map, mem_words k]
    constructor
    · rintro ⟨o', ⟨h1, h2⟩, l, hl, rfl⟩
      refine ⟨by simp [h1], ?_⟩
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact h2 e he
      · rw [List.mem_singleton.1 he]
        exact hl
    · rintro ⟨h1, h2⟩
      rcases List.eq_nil_or_concat o with rfl | ⟨o', l, rfl⟩
      · simp at h1
      · rw [List.concat_eq_append] at h1 h2 ⊢
        refine ⟨o', ⟨by simpa using h1, fun e he => h2 e (by simp [he])⟩, l,
          h2 l (by simp), rfl⟩

/-- The words of `G14.wordsUpTo n K` are the lists of length `≤ K` with entries in
`G14.sigOrders n`. -/
theorem mem_wordsUpTo {n K : ℕ} {o : List ℕ} :
    o ∈ G14.wordsUpTo n K ↔ o.length ≤ K ∧ ∀ e ∈ o, e ∈ G14.sigOrders n := by
  simp only [G14.wordsUpTo, List.mem_flatMap, List.mem_range, mem_words]
  constructor
  · rintro ⟨k, hk, rfl, h⟩
    exact ⟨by omega, h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨o.length, by omega, rfl, h2⟩

/-- The labels of `chainLabelsAux f b` are the nonempty lists of even entries `≥ 4`, of length
`≤ f` and excess `≤ b`. -/
theorem mem_chainLabelsAux : ∀ (f b : ℕ) (o : List ℕ), o ∈ chainLabelsAux f b ↔
    o ≠ [] ∧ (∀ e ∈ o, 4 ≤ e ∧ e % 2 = 0) ∧ o.length ≤ f ∧ labelInc o ≤ b
  | 0, b, o => by
    simp only [chainLabelsAux, List.not_mem_nil, false_iff, not_and]
    intro h1 _ h2
    exact absurd (List.length_eq_zero_iff.1 (by omega)) h1
  | f + 1, b, o => by
    simp only [chainLabelsAux, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
      List.mem_map, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, mem_chainLabelsAux f]
    constructor
    · rintro ⟨j, ⟨hjb, h2j, hje⟩, rfl | ⟨o', ⟨hne, hent, hlen, hinc⟩, rfl⟩⟩
      · refine ⟨by simp, ?_, by simp, ?_⟩
        · intro e he
          rw [List.mem_singleton.1 he]
          omega
        · simp only [labelInc_cons, labelInc_nil]
          omega
      · refine ⟨by simp, ?_, ?_, ?_⟩
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · omega
          · exact hent e he
        · simp only [List.length_cons]
          omega
        · rw [labelInc_cons]
          omega
    · rintro ⟨hne, hent, hlen, hinc⟩
      rcases o with _ | ⟨e, o'⟩
      · exact absurd rfl hne
      · have he := hent e (List.mem_cons_self ..)
        rw [labelInc_cons] at hinc
        refine ⟨e - 2, ⟨by omega, by omega, by omega⟩, ?_⟩
        by_cases ho' : o' = []
        · subst ho'
          left
          have : e - 2 + 2 = e := by omega
          simp [this]
        · right
          refine ⟨o', ⟨ho', fun x hx => hent x (List.mem_cons_of_mem _ hx), ?_, ?_⟩, ?_⟩
          · simp only [List.length_cons] at hlen
            omega
          · omega
          · have : e - 2 + 2 = e := by omega
            simp [this]

/-- The labels of `Σ_T^{(n)}` ([II, (3.3)–(3.4)]): nonempty, entries even and `≥ 4`, scaling order
`2 + labelInc o ≤ n`. -/
theorem mem_chainLabels {n : ℕ} {o : List ℕ} : o ∈ chainLabels n ↔
    o ≠ [] ∧ (∀ e ∈ o, 4 ≤ e ∧ e % 2 = 0) ∧ labelInc o + 2 ≤ n := by
  rw [chainLabels, mem_chainLabelsAux]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have := two_mul_length_le_labelInc o fun e he => (h2 e he).1
    have : 0 < o.length := List.length_pos_iff.2 h1
    exact ⟨h1, h2, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    have := two_mul_length_le_labelInc o fun e he => (h2 e he).1
    exact ⟨h1, h2, by omega, by omega⟩

/-! ## No repetitions -/

/-- `G14.sigOrders n` has no repetitions. -/
theorem nodup_sigOrders (n : ℕ) : (G14.sigOrders n).Nodup :=
  List.nodup_range.filter _

/-- `G14.words n k` has no repetitions. -/
theorem nodup_words (n : ℕ) : ∀ k, (G14.words n k).Nodup
  | 0 => by simp [G14.words]
  | k + 1 => by
    rw [G14.words, List.nodup_flatMap]
    refine ⟨fun o _ => (nodup_sigOrders n).map fun a b h => ?_, ?_⟩
    · simpa using h
    · refine (nodup_words n k).imp ?_
      intro o o' hne x hx hx'
      simp only [List.mem_map] at hx hx'
      obtain ⟨l, -, rfl⟩ := hx
      obtain ⟨l', -, h⟩ := hx'
      exact hne (by simpa using (congrArg List.dropLast h).symm)

/-- `G14.wordsUpTo n K` has no repetitions. -/
theorem nodup_wordsUpTo (n K : ℕ) : (G14.wordsUpTo n K).Nodup := by
  rw [G14.wordsUpTo, List.nodup_flatMap]
  refine ⟨fun k _ => nodup_words n k, List.nodup_range.imp ?_⟩
  intro k k' hne x hx hx'
  exact hne (by rw [← (mem_words k x).1 hx |>.1, ← (mem_words k' x).1 hx' |>.1])

/-- `chainLabelsAux f b` has no repetitions. -/
theorem nodup_chainLabelsAux : ∀ f b, (chainLabelsAux f b).Nodup
  | 0, b => by simp [chainLabelsAux]
  | f + 1, b => by
    simp only [chainLabelsAux]
    rw [List.nodup_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, (nodup_chainLabelsAux f (b - j)).map fun a b h => ?_⟩
      · simp only [List.mem_map, not_exists, not_and]
        intro o' ho' h
        have h1 := ((mem_chainLabelsAux f (b - j) o').1 ho').1
        have h2 : o' = [] := by simpa using h
        exact h1 h2
      · simpa using h
    · refine ((List.nodup_range.filter _).imp ?_)
      intro j j' hne x hx hx'
      have key : ∀ (i : ℕ) (x : List ℕ), x ∈ [i + 2] :: (chainLabelsAux f (b - i)).map
          ((i + 2) :: ·) → x.head? = some (i + 2) := by
        intro i x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · rfl
        · obtain ⟨o', -, rfl⟩ := List.mem_map.1 hx
          rfl
      have h1 := key j x hx
      have h2 := key j' x hx'
      exact hne (by rw [h1] at h2; simpa using h2)

/-- `chainLabels n` has no repetitions. -/
theorem nodup_chainLabels (n : ℕ) : (chainLabels n).Nodup := nodup_chainLabelsAux _ _

/-- The empty label is not a label of `chainLabels n`. -/
theorem nil_not_mem_chainLabels (n : ℕ) : [] ∉ chainLabels n := fun h =>
  (mem_chainLabels.1 h).1 rfl

/-- The plain label and the labels of `chainLabels n` have no repetitions. -/
theorem nodup_nil_cons_chainLabels (n : ℕ) : ([] :: chainLabels n).Nodup :=
  List.nodup_cons.2 ⟨nil_not_mem_chainLabels n, nodup_chainLabels n⟩

/-! ## The words of the labels of `Σ_T^{(n)}` and the others -/

/-- The words of `G14.extra n K` are the nonempty words of length `≤ K` that are not labels of
`chainLabels n`. -/
theorem mem_extra {n K : ℕ} {o : List ℕ} : o ∈ G14.extra n K ↔
    o ∈ G14.wordsUpTo n K ∧ o ≠ [] ∧ o ∉ chainLabels n := by
  simp only [G14.extra, List.mem_filter, decide_eq_true_eq, List.mem_cons, not_or]

/-- `G14.extra n K` has no repetitions. -/
theorem nodup_extra (n K : ℕ) : (G14.extra n K).Nodup :=
  (nodup_wordsUpTo n K).filter _

/-- `[] :: chainLabels n` lies in `G14.wordsUpTo n K` once `K ≥ (n − 2)/2`. -/
theorem nil_cons_chainLabels_subset {n K : ℕ} (hK : (n - 2) / 2 ≤ K) :
    ∀ o ∈ [] :: chainLabels n, o ∈ G14.wordsUpTo n K := by
  intro o ho
  rw [mem_wordsUpTo]
  rcases List.mem_cons.1 ho with rfl | ho
  · simp
  · obtain ⟨h1, h2, h3⟩ := mem_chainLabels.1 ho
    have h4 := two_mul_length_le_labelInc o fun e he => (h2 e he).1
    refine ⟨by omega, fun e he => mem_sigOrders.2 ⟨(h2 e he).1, ?_, (h2 e he).2⟩⟩
    have := le_labelInc_of_mem he
    have := (h2 e he).1
    omega

/-- The words of length `≤ K` are the plain label, the labels of `Σ_T^{(n)}` and the words of
`G14.extra n K` (for `K ≥ (n − 2)/2`), each once ([II, (3.3)–(3.4)]). -/
theorem wordsUpTo_perm {n K : ℕ} (hK : (n - 2) / 2 ≤ K) :
    (G14.wordsUpTo n K).Perm (([] :: chainLabels n) ++ G14.extra n K) := by
  have hsub := nil_cons_chainLabels_subset hK
  refine (List.perm_ext_iff_of_nodup (nodup_wordsUpTo n K) ?_).2 fun o => ?_
  · refine List.nodup_append.2 ⟨nodup_nil_cons_chainLabels n, nodup_extra n K, ?_⟩
    intro a ha b hb hab
    subst hab
    have := (mem_extra.1 hb).2
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact this.1 rfl
    · exact this.2 ha
  · rw [List.mem_append, mem_extra]
    constructor
    · intro ho
      by_cases h : o ∈ [] :: chainLabels n
      · exact Or.inl h
      · simp only [List.mem_cons, not_or] at h
        exact Or.inr ⟨ho, h.1, h.2⟩
    · rintro (h | h)
      · exact hsub o h
      · exact h.1

/-- Every word of `G14.extra n K` has excess `≥ n − 1`: the labelled `Θ` edge has scaling order
`≥ n + 1`. -/
theorem le_labelInc_of_mem_extra {n K : ℕ} {o : List ℕ} (ho : o ∈ G14.extra n K) :
    n ≤ labelInc o + 1 := by
  obtain ⟨h1, h2, h3⟩ := mem_extra.1 ho
  obtain ⟨-, h4⟩ := mem_wordsUpTo.1 h1
  by_contra hlt
  refine h3 (mem_chainLabels.2 ⟨h2, fun e he => ?_, by omega⟩)
  obtain ⟨a, -, c⟩ := mem_sigOrders.1 (h4 e he)
  exact ⟨a, c⟩

/-! ## Words and the labels of the graphs -/

/-- The words of length `≤ K` are labels of even entries in `[4, n]`, hence `labelOK N` for
`N ≥ n`. -/
theorem labelOK_of_mem_wordsUpTo {n K N : ℕ} {o : List ℕ} (ho : o ∈ G14.wordsUpTo n K)
    (hN : n ≤ N) : labelOK N o = true := by
  obtain ⟨-, h⟩ := mem_wordsUpTo.1 ho
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro e he
  obtain ⟨a, b, c⟩ := mem_sigOrders.1 (h e he)
  exact ⟨⟨a, by omega⟩, c⟩

/-- A word of length `≤ K` has excess `≥ 2 |o|`. -/
theorem two_mul_length_le_labelInc_of_mem {n K : ℕ} {o : List ℕ} (ho : o ∈ G14.wordsUpTo n K) :
    2 * o.length ≤ labelInc o :=
  two_mul_length_le_labelInc o fun e he => (mem_sigOrders.1 ((mem_wordsUpTo.1 ho).2 e he)).1

/-- The words of length `≤ K` are words of length `≤ K'` for `K ≤ K'`. -/
theorem wordsUpTo_subset {n K K' : ℕ} (h : K ≤ K') : G14.wordsUpTo n K ⊆ G14.wordsUpTo n K' := by
  intro o ho
  obtain ⟨h1, h2⟩ := mem_wordsUpTo.1 ho
  exact mem_wordsUpTo.2 ⟨by omega, h2⟩

/-- `G14.extra n K ⊆ G14.extra n K'` for `K ≤ K'`. -/
theorem extra_subset {n K K' : ℕ} (h : K ≤ K') : G14.extra n K ⊆ G14.extra n K' := by
  intro o ho
  obtain ⟨h1, h2, h3⟩ := mem_extra.1 ho
  exact mem_extra.2 ⟨wordsUpTo_subset h h1, h2, h3⟩

/-- A word of length `≤ K'` that is not of length `≤ K` has excess `≥ 2K + 2`. -/
theorem two_mul_add_two_le_labelInc {n K K' : ℕ} {o : List ℕ} (ho : o ∈ G14.wordsUpTo n K')
    (ho' : o ∉ G14.wordsUpTo n K) : 2 * K + 2 ≤ labelInc o := by
  have h1 := two_mul_length_le_labelInc_of_mem ho
  have h2 : K < o.length := by
    by_contra h
    exact ho' (mem_wordsUpTo.2 ⟨by omega, (mem_wordsUpTo.1 ho).2⟩)
  omega

/-! ## The relabelling of a sum of graphs by a list of words -/

/-- The graphs of `G14.relabels W S` are those of `S` with the `Θ` edge at `⊗` relabelled by a
word of `W`. -/
theorem mem_relabels {W : List (List ℕ)} {S : Expansion 3} {g : Σ m : ℕ, Graph 3 m} :
    g ∈ G14.relabels W S ↔
      ∃ h ∈ S, ∃ o ∈ W, g = ⟨h.1, h.2.relabelRoot o⟩ := by
  simp only [G14.relabels, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨h, hh, o, ho, rfl⟩
    exact ⟨h, hh, o, ho, rfl⟩
  · rintro ⟨h, hh, o, ho, rfl⟩
    exact ⟨h, hh, o, ho, rfl⟩

/-- Relabelling by the concatenation of two lists of words gives, up to order, the concatenation
of the relabellings. -/
theorem relabels_append_perm (W₁ W₂ : List (List ℕ)) (S : Expansion 3) :
    (G14.relabels (W₁ ++ W₂) S).Perm (G14.relabels W₁ S ++ G14.relabels W₂ S) := by
  simp only [G14.relabels, List.map_append]
  exact (List.flatMap_append_perm S _ _).symm

/-- Relabelling by two lists of words that agree up to order gives the same graphs up to order. -/
theorem relabels_perm {W W' : List (List ℕ)} (h : W.Perm W') (S : Expansion 3) :
    (G14.relabels W S).Perm (G14.relabels W' S) :=
  List.Perm.flatMap_left S fun _ _ => h.map _

/-- The graphs of `solveLow` obtained from `R_IT` are the graphs of `R_IT` relabelled by the plain
label and the labels of `Σ_T^{(n)}`. -/
theorem solveLow_R (n : ℕ) (𝒬 : TEqRec) :
    (𝒬.solveLow n).R = G14.relabels ([] :: chainLabels n) 𝒬.R := rfl

/-- The graphs of `solveLow` obtained from `Q_IT` are the graphs of `Q_IT` relabelled by the plain
label and the labels of `Σ_T^{(n)}`. -/
theorem solveLow_Q (n : ℕ) (𝒬 : TEqRec) :
    (𝒬.solveLow n).Q = G14.relabels ([] :: chainLabels n) 𝒬.Q := rfl

/-- Relabelling by all words of length `≤ K` is, up to order, relabelling by the plain label and
the labels of `Σ_T^{(n)}` followed by relabelling by `G14.extra n K` (`K ≥ (n − 2)/2`). -/
theorem relabels_wordsUpTo_perm {n K : ℕ} (hK : (n - 2) / 2 ≤ K) (S : Expansion 3) :
    (G14.relabels (G14.wordsUpTo n K) S).Perm
      (G14.relabels ([] :: chainLabels n) S ++ G14.relabels (G14.extra n K) S) :=
  (relabels_perm (wordsUpTo_perm hK) S).trans (relabels_append_perm _ _ S)

/-! ## The scaling order of a relabelled graph -/

/-- Relabelling the `Θ` edge at `⊗` of a graph `Σ_x Θ_{⊗x} 𝒢_x` by `o` changes the scaling order
by `Σ oᵢ − 2|o|` ([II, (2.5)]). -/
theorem ord_relabelRoot {n : ℕ} {Γ : Graph 3 n} (hΓ : G14.RootedTheta Γ) (o : List ℕ) :
    (Γ.relabelRoot o).ord = Γ.ord + ((o.sum : ℤ) - 2 * o.length) := by
  obtain ⟨j, hk, -, -, hx0, -, hrest⟩ := hΓ
  have hl : Γ.comps = Γ.comps.take j ++ Γ.comps[j] :: Γ.comps.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j Γ.comps, List.drop_eq_getElem_cons j.2]
    rfl
  have hrest' : ∀ c ∈ Γ.comps.take j ++ Γ.comps.drop (j + 1), c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc
    have h := hrest c (by simpa [Graph.dropComp, List.eraseIdx_eq_take_drop_succ] using hc)
    exact ⟨h.1, h.2.1⟩
  have hx : Γ.comps[j].x = .inl 0 ∨ Γ.comps[j].y = .inl 0 := Or.inl hx0
  have hrel : (Γ.relabelRoot o).comps = Γ.comps.map fun c =>
      if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := Kind.theta o }
      else c := rfl
  generalize Γ.comps.take j = A at hl hrest'
  generalize Γ.comps.drop (j + 1) = B at hl hrest'
  generalize Γ.comps[j] = cj at hl hk hx
  simp only [Graph.ord]
  rw [hrel, hl]
  have hρ : ∀ c ∈ A ++ B,
      (if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := Kind.theta o }
        else c) = c := by
    intro c hc
    have := hrest' c hc
    have hn : ¬ (c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)) := by
      rintro ⟨-, h | h⟩
      · exact this.1 h
      · exact this.2 h
    simp only [hn, ↓reduceIte]
  have hmapA : A.map (fun c => if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
      then { c with kind := Kind.theta o } else c) = A := by
    conv_rhs => rw [← List.map_id A]
    exact List.map_congr_left fun c hc => hρ c (List.mem_append_left _ hc)
  have hmapB : B.map (fun c => if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
      then { c with kind := Kind.theta o } else c) = B := by
    conv_rhs => rw [← List.map_id B]
    exact List.map_congr_left fun c hc => hρ c (List.mem_append_right _ hc)
  have hρj : (if cj.kind = .theta [] ∧ (cj.x = .inl 0 ∨ cj.y = .inl 0)
      then { cj with kind := Kind.theta o } else cj) = { cj with kind := Kind.theta o } :=
    by simp only [hk, hx, and_self, ↓reduceIte]
  simp only [List.map_append, List.map_cons, hmapA, hmapB, hρj, List.sum_append, List.sum_cons]
  simp only [hk, Kind.ord, List.sum_nil, List.length_nil]
  push_cast
  ring

/-- For a label with entries `≥ 2` the change of order is the excess `labelInc o`. -/
theorem ord_relabelRoot_of_entries {n : ℕ} {Γ : Graph 3 n} (hΓ : G14.RootedTheta Γ) {o : List ℕ}
    (ho : ∀ e ∈ o, 2 ≤ e) : (Γ.relabelRoot o).ord = Γ.ord + (labelInc o : ℤ) := by
  rw [ord_relabelRoot hΓ, labelInc_cast o ho]

/-- Relabelling by a word of length `≤ K` raises the order by `labelInc o`. -/
theorem ord_relabelRoot_of_mem_wordsUpTo {n K m : ℕ} {Γ : Graph 3 m} (hΓ : G14.RootedTheta Γ)
    {o : List ℕ} (ho : o ∈ G14.wordsUpTo n K) :
    (Γ.relabelRoot o).ord = Γ.ord + (labelInc o : ℤ) :=
  ord_relabelRoot_of_entries hΓ fun e he => by
    have := (mem_sigOrders.1 ((mem_wordsUpTo.1 ho).2 e he)).1
    omega

/-- Relabelling by a word of `G14.extra n K` raises the order by at least `n − 1`. -/
theorem ord_relabelRoot_of_mem_extra {n K m : ℕ} {Γ : Graph 3 m} (hΓ : G14.RootedTheta Γ)
    {o : List ℕ} (ho : o ∈ G14.extra n K) :
    Γ.ord + ((n : ℤ) - 1) ≤ (Γ.relabelRoot o).ord := by
  rw [ord_relabelRoot_of_mem_wordsUpTo hΓ (mem_extra.1 ho).1]
  have := le_labelInc_of_mem_extra ho
  omega

/-! ## The leading graph -/

/-- The leading graph `m Θ_{⊗⊕} Ḡ_{⊕⊖}` with the plain `Θ` edge is `Σ_x Θ_{⊗x} 𝒢_x`. -/
theorem rootedTheta_thetaLabelGraph : G14.RootedTheta (thetaLabelGraph []) := by
  refine ⟨⟨0, by decide⟩, rfl, rfl, rfl, rfl, by decide, ?_⟩
  intro c hc
  simp only [Graph.dropComp, thetaLabelGraph, List.eraseIdx_cons_zero, List.mem_singleton] at hc
  subst hc
  decide

/-- Relabelling the plain `Θ` edge of the leading graph by `o` gives the leading graph with the
labelled edge `Θ^{[o]}`. -/
theorem relabelRoot_thetaLabelGraph (o : List ℕ) :
    (thetaLabelGraph []).relabelRoot o = thetaLabelGraph o := by
  simp [Graph.relabelRoot, thetaLabelGraph, mkC]

end Words

end RBM8D
