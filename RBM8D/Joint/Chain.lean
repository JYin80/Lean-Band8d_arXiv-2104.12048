import RBM8D.Joint.Words
import RBM8D.TExp.Second

/-!
# The labelled `Θ` edge at `⊗` and the identity of the solved `T`-equation

[II, (2.10)], [II, (3.1)], [II, (3.5)], [II, (3.14)] and [II, (6.1)–(6.3)].

* The chains `Θ Σ_{o₁} Θ ⋯ Σ_{o_k} Θ` over the words `o` of length `k` in the even orders
  `4, …, n` sum to `(Θ Σ̃^{(n)})^k Θ` on every record whose self-energy matrices of even order
  `≤ n` are the values of `Sig` with `Σ_n = E` (`Chain.sum_chain_words`,
  `Chain.sum_sig_eq_sigTilde`).
* A graph `Σ_x Θ_{⊗x} 𝒢_x` (`G14.RootedTheta`) with its `Θ` edge at `⊗` relabelled by `o` has the
  value `Σ_x Θ^{[o]}_{⊗x} 𝒢_x`, and `𝒢` does not read `⊗`. So the sum over the words of length `k`
  is `Σ_x ((Θ Σ̃^{(n)})^k)_{⊗x} Γ_{x,⊕⊖}` (`G14.chainValue`).
* The identity [II, (3.5)] iterated `K` times gives
  `T = Σ_{k ≤ K} (Θ Σ̃^{(n)})^k X + (Θ Σ̃^{(n)})^{K+1} T` with `X = m Θ Ḡ + R + A + Q + Err'`; with
  the value of each `(Θ Σ̃^{(n)})^k X` as a sum of relabelled graphs and the split of the words of
  length `≤ K` into the plain label, the labels of `Σ_T^{(n)}` and the others, this is the
  identity [II, (3.1)] for `G14.solveRec` (`Chain.solveRec_identity_of`, `G14.solveRec_identity`).
-/

noncomputable section

open scoped BigOperators Matrix

namespace RBM8D

open Graphs

namespace Chain

/-! ## Sums of lists -/

/-- The sum of a list of matrices, read at one entry. -/
private theorem list_sum_apply {α ι : Type} (l : List α) (f : α → Matrix ι ι ℂ) (a b : ι) :
    (l.map f).sum a b = (l.map fun x => f x a b).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

/-- A list sum of finite sums is the finite sum of the list sums. -/
private theorem list_sum_finset_sum {α β : Type} [Fintype β] (l : List α) (f : α → β → ℂ) :
    (l.map fun a => ∑ b, f a b).sum = ∑ b, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

/-- Two list sums commute. -/
private theorem list_sum_comm {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → ℂ) :
    (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, List.sum_map_add]

/-- The sum of a `flatMap` is the sum of the sums. -/
private theorem sum_flatMap {α β : Type} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-! ## Values of formal sums -/

section Values

variable {k : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
  (e : Fin k → ι) (ω : Ω)

/-- The value of a concatenation is the sum of the values. -/
theorem valR_append (E₁ E₂ : Expansion k) :
    (E₁ ++ E₂).valR PF D e ω = E₁.valR PF D e ω + E₂.valR PF D e ω := by
  simp [Expansion.valR]

/-- The value of a formal sum does not depend on the order of its graphs. -/
theorem valR_perm {E₁ E₂ : Expansion k} (h : E₁.Perm E₂) :
    E₁.valR PF D e ω = E₂.valR PF D e ω := by
  simp only [Expansion.valR]
  exact (h.map _).sum_eq

/-- The value of a `flatMap` is the sum of the values. -/
theorem valR_flatMap {α : Type} (l : List α) (f : α → Expansion k) :
    Expansion.valR (l.flatMap f) PF D e ω = (l.map fun a => (f a).valR PF D e ω).sum := by
  induction l with
  | nil => simp [Expansion.valR]
  | cons a l ih => rw [List.flatMap_cons, valR_append, ih, List.map_cons, List.sum_cons]

/-- The graphs of a formal sum that satisfy `p` and those that do not have together the value of
the formal sum. -/
theorem valR_filter_add (E : Expansion k) (p : (Σ m : ℕ, Graph k m) → Bool) :
    Expansion.valR (E.filter p) PF D e ω + Expansion.valR (E.filter fun g => !p g) PF D e ω =
      E.valR PF D e ω := by
  rw [← valR_append]
  exact valR_perm PF D e ω (List.filter_append_perm p E)

end Values

/-! ## The chains over the words -/

section Chains

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The chain of the label `o ++ [l]` is the chain of `o` followed by `Σ_l Θ`. -/
theorem chain_append (D : Data ι) (o : List ℕ) (l : ℕ) :
    D.chain (o ++ [l]) = D.chain o * D.Sig l * D.Theta := by
  simp [Data.chain, List.foldl_append]

/-- The chains `Θ Σ_{o₁} Θ ⋯ Σ_{o_k} Θ` over the words of length `k` in the orders
`G14.sigOrders n` sum to `(Θ Σ')^k Θ`, with `Σ'` the sum of the self-energy matrices of these
orders ([II, (6.3)]). -/
theorem sum_chain_words (D : Data ι) (n : ℕ) : ∀ k : ℕ,
    ((G14.words n k).map D.chain).sum =
      (D.Theta * ((G14.sigOrders n).map D.Sig).sum) ^ k * D.Theta
  | 0 => by simp [G14.words, Data.chain]
  | k + 1 => by
    rw [G14.words, List.map_flatMap, sum_flatMap]
    simp only [List.map_map, Function.comp_def, chain_append]
    have h : ∀ o : List ℕ, ((G14.sigOrders n).map fun l => D.chain o * D.Sig l * D.Theta).sum =
        D.chain o * ((G14.sigOrders n).map D.Sig).sum * D.Theta := by
      intro o
      rw [List.sum_map_mul_right, List.sum_map_mul_left]
    simp only [h]
    rw [List.sum_map_mul_right, List.sum_map_mul_right, sum_chain_words D n k, pow_succ]
    simp only [mul_assoc]

/-- The sum of the entries of a list of naturals with even entries is even. -/
private theorem even_sum_nat : ∀ l : List ℕ, (∀ j ∈ l, j % 2 = 0) → Even l.sum
  | [], _ => ⟨0, by simp⟩
  | a :: l, h => by
    rw [List.sum_cons]
    exact (Nat.even_iff.2 (h a (List.mem_cons_self ..))).add
      (even_sum_nat l fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The sum of a list of even integers is even. -/
private theorem even_sum_int : ∀ l : List ℤ, (∀ j ∈ l, Even j) → Even l.sum
  | [], _ => ⟨0, by simp⟩
  | a :: l, h => by
    rw [List.sum_cons]
    exact (h a (List.mem_cons_self ..)).add
      (even_sum_int l fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The components of deterministic graphs have even scaling order: `2` for waved and dotted
edges, `0` for `×`-dotted edges, `Σ oᵢ + 2 − 2|o|` with even `oᵢ` for labelled `Θ` edges. -/
theorem even_ord_of_isDetKind {V : Type} {N : ℕ} (c : Comp V) (h : c.isDetKind N = true) :
    Even c.kind.ord := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ with
  | waved w => exact ⟨1, by simp [Kind.ord]⟩
  | dot => exact ⟨1, by simp [Kind.ord]⟩
  | xdot => exact ⟨0, by simp [Kind.ord]⟩
  | theta o =>
    have hl : labelOK N o = true := by
      simp only [Comp.isDetKind, Bool.and_eq_true] at h
      exact h.2
    have he : Even o.sum := even_sum_nat o fun j hj => by
      simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at hl
      exact (hl j hj).2
    obtain ⟨r, hr⟩ := he
    refine ⟨(r : ℤ) + 1 - o.length, ?_⟩
    simp only [Kind.ord, hr]
    push_cast
    ring
  | _ => simp [Comp.isDetKind] at h

/-- An `n`-th order self-energy of odd order `n` is the empty formal sum: deterministic graphs
have even scaling order ([II, (2.6)]). -/
theorem eq_nil_of_odd {n : ℕ} {E : Expansion 2} (hE : SelfEnergyShape n E) (hn : ¬ Even n) :
    E = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun g hg => hn ?_
  obtain ⟨-, hdet, hord, -⟩ := hE g hg
  have hsum : Even (g.2.comps.map fun c => c.kind.ord).sum := by
    refine even_sum_int _ fun j hj => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hj
    exact even_ord_of_isDetKind c (List.all_eq_true.1 hdet c hc)
  have : Even g.2.ord := by
    simp only [Graph.ord]
    exact hsum.sub (even_two_mul _)
  rw [hord] at this
  exact Int.even_coe_nat n |>.1 this

/-- The sum of the self-energy matrices of the orders `G14.sigOrders n` is `Σ̃^{(n)}`
([II, (3.14)]) on a record whose self-energy matrices of even order `≤ n` are the values of `Sig`
with `Σ_n = E`: for even `n` the matrix of order `n` is the value of `E`, for odd `n` the
self-energy `E` is empty. -/
theorem sum_sig_eq_sigTilde {n : ℕ} (hn : 3 ≤ n) (Sig : ℕ → Expansion 2) {E : Expansion 2}
    (hE : SelfEnergyShape n E) (D : Data ι)
    (hD : SigConsistent (Function.update Sig n E) (n + 1) D) :
    ((G14.sigOrders n).map D.Sig).sum = sigTilde n E D := by
  rw [← List.sum_toFinset _ (Words.nodup_sigOrders n), sigTilde]
  by_cases hev : Even n
  · have hset : (G14.sigOrders n).toFinset = insert n ((Finset.Ico 4 n).filter Even) := by
      ext l
      simp only [List.mem_toFinset, Words.mem_sigOrders, Finset.mem_insert, Finset.mem_filter,
        Finset.mem_Ico, Nat.even_iff]
      rw [Nat.even_iff] at hev
      omega
    have hnot : n ∉ (Finset.Ico 4 n).filter Even := by simp
    have h := hD n (by rw [Nat.even_iff] at hev; omega) (by omega) hev
    rw [Function.update_self] at h
    rw [hset, Finset.sum_insert hnot, h]
  · have hset : (G14.sigOrders n).toFinset = (Finset.Ico 4 n).filter Even := by
      ext l
      simp only [List.mem_toFinset, Words.mem_sigOrders, Finset.mem_filter, Finset.mem_Ico,
        Nat.even_iff]
      rw [Nat.even_iff] at hev
      omega
    rw [hset, eq_nil_of_odd hE hev]
    have h0 : (Matrix.of fun x y => Expansion.val ([] : Expansion 2) D ![x, y]) = 0 := by
      ext x y
      simp [Expansion.val]
    rw [h0, zero_add]

end Chains


/-! ## Splitting off the `Θ` edge at `⊗` -/

section Split

variable {k m : ℕ} {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)

/-- The factor of a component depends on the labelling only through its ends and minor atoms. -/
theorem val_congr {V : Type} (D₀ : Data ι) {σ σ' : V → ι} (c : Comp V) (hx : σ c.x = σ' c.x)
    (hy : σ c.y = σ' c.y) (hm : ∀ u ∈ c.minor, σ u = σ' u) :
    Comp.val D₀ σ c = Comp.val D₀ σ' c := by
  have hmin : c.minor.map σ = c.minor.map σ' := List.map_congr_left hm
  unfold Comp.val
  rw [hx, hy, hmin]

/-- The term of a labelled graph depends on the labelling only through the ends, the minor atoms
and the atoms of the labels of its components. -/
theorem termR_congr (Γ : Graph k m) {σ σ' : Atom k m → ι} (ω : Ω)
    (h : ∀ c ∈ Γ.comps, σ c.x = σ' c.x ∧ σ c.y = σ' c.y ∧ (∀ u ∈ c.minor, σ u = σ' u) ∧
      ∀ ℓ, c.label = some ℓ → σ ℓ.2 = σ' ℓ.2) :
    Γ.termR PF D σ ω = Γ.termR PF D σ' ω := by
  have hv : ∀ (ω' : Ω) (c : Comp (Atom k m)), c ∈ Γ.comps →
      Comp.val (D ω') σ c = Comp.val (D ω') σ' c := fun ω' c hc =>
    val_congr (D ω') c (h c hc).1 (h c hc).2.1 (h c hc).2.2.1
  unfold Graph.termR
  congr 1
  · congr 1
    exact congrArg List.prod (List.map_congr_left fun c hc => hv ω c (List.mem_filter.1 hc).1)
  · refine congrArg List.prod (List.map_congr_left fun ℓ hℓ => ?_)
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 (List.mem_dedup.1 hℓ)
    rw [(h c hc).2.2.2 ℓ hcl]
    congr 1
    funext ω'
    exact congrArg List.prod
      (List.map_congr_left fun c' hc' => hv ω' c' (List.mem_filter.1 hc').1)

/-- The term of a graph with a component without label is the factor of that component times the
term of the graph without it. -/
theorem termR_split (Γ : Graph k m) {A B : List (Comp (Atom k m))} {c : Comp (Atom k m)}
    (hΓ : Γ.comps = A ++ c :: B) (hc : c.label = none) (σ : Atom k m → ι) (ω : Ω) :
    Γ.termR PF D σ ω =
      Comp.val (D ω) σ c * (⟨A ++ B, Γ.coeff⟩ : Graph k m).termR PF D σ ω := by
  obtain ⟨cs, co⟩ := Γ
  simp only at hΓ
  subst hΓ
  simp only [Graph.termR, Graph.labels, List.filterMap_append, List.filterMap_cons, hc,
    List.filter_append, List.filter_cons, Option.isNone_none, ↓reduceIte, List.map_append,
    List.map_cons, List.prod_append, List.prod_cons, reduceCtorEq, decide_false,
    Bool.false_eq_true]
  ring

/-- A graph `Σ_x Θ_{⊗x} 𝒢_x` is `A ++ Θ_{⊗v} :: B` with `v ≠ ⊗` and `A ++ B` not reading `⊗`, and
the graph with its `Θ` edge at `⊗` relabelled by `o` is `A ++ Θ^{[o]}_{⊗v} :: B`. -/
theorem rootedTheta_split {Γ : Graph 3 m} (hΓ : G14.RootedTheta Γ) :
    ∃ (A B : List (Comp (Atom 3 m))) (v : Atom 3 m), v ≠ .inl 0 ∧
      (∀ c ∈ A ++ B, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
        c.label.map Prod.snd ≠ some (.inl 0)) ∧
      Γ.comps = A ++ ⟨.theta [], .inl 0, v, [], none⟩ :: B ∧
      ∀ o, (Γ.relabelRoot o).comps = A ++ ⟨.theta o, .inl 0, v, [], none⟩ :: B ∧
        (Γ.relabelRoot o).coeff = Γ.coeff := by
  obtain ⟨j, hk, hm, hl, hx, hy, hrest⟩ := hΓ
  have hd : Γ.comps = Γ.comps.take j ++ Γ.comps[j] :: Γ.comps.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j Γ.comps, List.drop_eq_getElem_cons j.2]
    rfl
  have hrest' : ∀ c ∈ Γ.comps.take j ++ Γ.comps.drop (j + 1), c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧
      .inl 0 ∉ c.minor ∧ c.label.map Prod.snd ≠ some (.inl 0) := fun c hc =>
    hrest c (by simpa [Graph.dropComp, List.eraseIdx_eq_take_drop_succ] using hc)
  have hrel : ∀ o, (Γ.relabelRoot o).comps = Γ.comps.map fun c =>
      if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := Kind.theta o }
      else c := fun o => rfl
  generalize Γ.comps.take j = A at hd hrest'
  generalize Γ.comps.drop (j + 1) = B at hd hrest'
  generalize Γ.comps[j] = cj at hd hk hm hl hx hy
  obtain ⟨κ, x, y, mi, lab⟩ := cj
  simp only at hk hm hl hx hy
  subst hk hm hl hx
  refine ⟨A, B, y, hy, hrest', hd, fun o => ⟨?_, rfl⟩⟩
  have hρ : ∀ c ∈ A ++ B,
      (if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := Kind.theta o }
        else c) = c := by
    intro c hc
    have := hrest' c hc
    have hn : ¬ (c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)) := by
      rintro ⟨-, h | h⟩
      · exact this.1 h
      · exact this.2.1 h
    simp only [hn, ↓reduceIte]
  rw [hrel, hd, List.map_append, List.map_cons]
  have hA : A.map (fun c => if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
      then { c with kind := Kind.theta o } else c) = A := by
    conv_rhs => rw [← List.map_id A]
    exact List.map_congr_left fun c hc => hρ c (List.mem_append_left _ hc)
  have hB : B.map (fun c => if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
      then { c with kind := Kind.theta o } else c) = B := by
    conv_rhs => rw [← List.map_id B]
    exact List.map_congr_left fun c hc => hρ c (List.mem_append_right _ hc)
  rw [hA, hB]
  simp

omit [Fintype ι] [DecidableEq ι] in
/-- The labelling of the atoms with external atoms `![x, e 1, e 2]` agrees with the labelling with
external atoms `e` away from `⊗`. -/
theorem elim_agree (e : Fin 3 → ι) (s : Fin m → ι) (x : ι) {u : Atom 3 m} (hu : u ≠ .inl 0) :
    Sum.elim ![x, e 1, e 2] s u = Sum.elim e s u := by
  rcases u with i | i
  · fin_cases i
    · exact absurd rfl hu
    · rfl
    · rfl
  · rfl

end Split

end Chain

/-! ## The value of the relabelled graphs -/

/-- The value identity of the labelled `Θ` edge at `⊗` ([II, (2.10)], [II, (6.1)]): for a graph
`Γ = Σ_x Θ_{⊗x} 𝒢_x` (`G14.RootedTheta`) and `n ≥ 3`, the sum over the words `o` of length `k` of
`Γ` with its `Θ` edge at `⊗` relabelled by `o` is `Σ_x ((Θ Σ̃^{(n)})^k)_{⊗x} Γ_{x,⊕⊖}`, on every
record whose self-energy matrices of even order `≤ n` are the values of `Sig` with `Σ_n = E`. -/
def G14.chainValueStmt : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (E : Expansion 2) {m : ℕ} (Γ : Graph 3 m),
    G14.RootedTheta Γ → SelfEnergyShape n E →
    ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
      (∀ ω, SigConsistent (Function.update Sig n E) (n + 1) (Dt ω)) →
      ∀ (k : ℕ) (e : Fin 3 → ι) (ω : Ω),
        Expansion.valR ((G14.words n k).map fun o => (⟨m, Γ.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m))
            PF Dt e ω =
          ∑ x, (((Dt ω).Theta * sigTilde n E (Dt ω)) ^ k) (e 0) x * Γ.valR PF Dt ![x, e 1, e 2] ω

/-- **The labelled `Θ` edge at `⊗`** ([II, (2.10)], [II, (6.1)–(6.3)]): the sum over the words of
length `k` of a graph `Σ_x Θ_{⊗x} 𝒢_x` relabelled at `⊗` is `Σ_x ((Θ Σ̃^{(n)})^k)_{⊗x} Γ_{x,⊕⊖}`. -/
theorem G14.chainValue : G14.chainValueStmt := by
  intro n hn Sig E m Γ hΓ hE Ω ι _ _ PF Dt hSig k e ω
  obtain ⟨A, B, v, hv, hAB, hΓc, hrel⟩ := Chain.rootedTheta_split hΓ
  set G0 : Graph 3 m := ⟨A ++ B, Γ.coeff⟩ with hG0
  set M := (Dt ω).Theta * sigTilde n E (Dt ω) with hM
  have hterm : ∀ (o : List ℕ) (σ : Atom 3 m → ι), (Γ.relabelRoot o).termR PF Dt σ ω =
      (Dt ω).chain o (σ (.inl 0)) (σ v) * G0.termR PF Dt σ ω := by
    intro o σ
    rw [Chain.termR_split PF Dt _ (hrel o).1 rfl σ ω, (hrel o).2]
    rfl
  have hterm0 : ∀ σ : Atom 3 m → ι, Γ.termR PF Dt σ ω =
      (Dt ω).Theta (σ (.inl 0)) (σ v) * G0.termR PF Dt σ ω := by
    intro σ
    rw [Chain.termR_split PF Dt _ hΓc rfl σ ω]
    rfl
  have hF : ∀ (x : ι) (s : Fin m → ι),
      G0.termR PF Dt (Sum.elim ![x, e 1, e 2] s) ω = G0.termR PF Dt (Sum.elim e s) ω := by
    intro x s
    refine Chain.termR_congr PF Dt G0 ω fun c hc => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hAB c hc
    refine ⟨Chain.elim_agree e s x h1, Chain.elim_agree e s x h2,
      fun u hu => Chain.elim_agree e s x fun h => h3 (h ▸ hu), fun ℓ hℓ => ?_⟩
    refine Chain.elim_agree e s x fun h => h4 ?_
    rw [hℓ, Option.map_some, h]
  have hv' : ∀ (x : ι) (s : Fin m → ι), Sum.elim ![x, e 1, e 2] s v = Sum.elim e s v :=
    fun x s => Chain.elim_agree e s x hv
  have hP := Chain.sum_chain_words (Dt ω) n k
  rw [Chain.sum_sig_eq_sigTilde hn Sig hE (Dt ω) (hSig ω)] at hP
  have hL : Expansion.valR ((G14.words n k).map fun o =>
      (⟨m, Γ.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m)) PF Dt e ω =
      ∑ s : Fin m → ι, (M ^ k * (Dt ω).Theta) (e 0) (Sum.elim e s v) *
        G0.termR PF Dt (Sum.elim e s) ω := by
    simp only [Expansion.valR, List.map_map, Function.comp_def, Graph.valR, hterm,
      Sum.elim_inl]
    refine (Chain.list_sum_finset_sum (G14.words n k) fun o (s : Fin m → ι) =>
      (Dt ω).chain o (e 0) (Sum.elim e s v) * G0.termR PF Dt (Sum.elim e s) ω).trans ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [List.sum_map_mul_right (G14.words n k) (fun o => (Dt ω).chain o (e 0) (Sum.elim e s v)),
      ← Chain.list_sum_apply, hP]
  rw [hL]
  simp only [Graph.valR, hterm0, Sum.elim_inl, Matrix.cons_val_zero, hv', hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-! ## The identity of the solved `T`-equation -/

namespace Chain

/-- A list sum of functions, read at one point. -/
private theorem list_sum_fun_apply {α ι : Type} (l : List α) (f : α → ι → ℂ) (x : ι) :
    (l.map f).sum x = (l.map fun a => f a x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The external labelling `![e 0, e 1, e 2]` is `e`. -/
theorem vec_eta {ι : Type} (e : Fin 3 → ι) : ![e 0, e 1, e 2] = e := by
  funext i
  fin_cases i <;> rfl

/-- Relabelling the leading graph by the plain label and the labels of `Σ_T^{(n)}` gives the
leading term and `Σ_T^{(n)}` of [II, (3.1)]. -/
theorem relabels_leadExp (n : ℕ) :
    G14.relabels ([] :: chainLabels n) leadExp = leadExp ++ sigmaTExp n := by
  simp [G14.relabels, leadExp, sigmaTExp, Words.relabelRoot_thetaLabelGraph]

/-- Relabelling the leading graph by the words of `G14.extra n K` gives the value of
`G14.overflow n K`, the `O_dot` forms of these graphs. -/
theorem valR_relabels_leadExp_extra {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) (e : Fin 3 → ι) (ω : Ω) (n K : ℕ) :
    (G14.relabels (G14.extra n K) leadExp).valR PF D e ω = (G14.overflow n K).valR PF D e ω := by
  rw [G14.overflow, valR_flatMap]
  simp only [G14.relabels, leadExp, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Words.relabelRoot_thetaLabelGraph, Expansion.valR, List.map_map, Function.comp_def]
  refine congrArg List.sum (List.map_congr_left fun o _ => ?_)
  exact (congrFun (oDot_value 3 0 Ω ι PF D trivial (thetaLabelGraph o) e) ω).symm

/-- **The identity of the solved `T`-equation from three of its properties**: from the identity
[II, (3.5)] of `𝒬`, the shape of `Σ_n` and the form `Σ_x Θ_{⊗x} 𝒢_x` of the graphs of `R`, `A`,
`Q`, `Err` of `𝒬`, for `K ≥ (n − 2)/2` and a remainder with the value of `(Θ Σ̃^{(n)})^{K+1} T`,
the identity [II, (3.1)] holds for `G14.solveRec n K 𝒬 Rem` ([II, (6.1)–(6.3)]). -/
theorem solveRec_identity_of {n : ℕ} (hn : 3 ≤ n) (Sig : ℕ → Expansion 2) (K : ℕ) (𝒬 : TEqRec)
    (Rem : Expansion 3) (hK : (n - 2) / 2 ≤ K) (hI : 𝒬.Identity Sig n)
    (hE : SelfEnergyShape n 𝒬.SigN)
    (hR : ∀ g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err, G14.RootedTheta g.2)
    (hRem : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
        modelAdm Ω ι PF Dt → (∀ ω, SigConsistent (Function.update Sig n 𝒬.SigN) (n + 1) (Dt ω)) →
        ∀ (e : Fin 3 → ι) (ω : Ω),
          Rem.valR PF Dt e ω =
            ∑ x, (((Dt ω).Theta * sigTilde n 𝒬.SigN (Dt ω)) ^ (K + 1)) (e 0) x *
              tGraph.valR PF Dt ![x, e 1, e 2] ω) :
    (G14.solveRec n K 𝒬 Rem).Identity (Function.update Sig n 𝒬.SigN) n := by
  intro Ω ι _ _ PF Dt hA hSc e ω
  have hSc' : ∀ ω, SigConsistent Sig n (Dt ω) := by
    intro ω' j h4 hj hev
    have h := hSc ω' j h4 (by omega) hev
    rwa [Function.update_of_ne (by omega)] at h
  set M := (Dt ω).Theta * sigTilde n 𝒬.SigN (Dt ω) with hM
  set X : Expansion 3 := leadExp ++ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err with hX
  set fT : ι → ℂ := fun x => tGraph.valR PF Dt ![x, e 1, e 2] ω with hfT
  set fX : ι → ℂ := fun x => X.valR PF Dt ![x, e 1, e 2] ω with hfX
  have hXr : ∀ g ∈ X, G14.RootedTheta g.2 := by
    intro g hg
    simp only [hX, List.mem_append] at hg
    rcases hg with (((h | h) | h) | h) | h
    · simp only [leadExp, List.mem_singleton] at h
      subst h
      exact Words.rootedTheta_thetaLabelGraph
    all_goals exact hR g (by simp [h])
  -- the identity [II, (3.5)] as a fixed point equation in the first index
  have hfix : fT = fX + M *ᵥ fT := by
    funext x
    have h := hI Ω ι PF Dt hA hSc' ![x, e 1, e 2] ω
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    simp only [hfT, hfX, Pi.add_apply, Matrix.mulVec, dotProduct, hX]
    exact h
  -- `K + 1` iterations
  have hiter : ∀ j, fT = ((List.range j).map fun i => (M ^ i) *ᵥ fX).sum + (M ^ j) *ᵥ fT := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc fT = ((List.range j).map fun i => (M ^ i) *ᵥ fX).sum + (M ^ j) *ᵥ fT := ih
        _ = ((List.range j).map fun i => (M ^ i) *ᵥ fX).sum + (M ^ j) *ᵥ (fX + M *ᵥ fT) := by
          rw [← hfix]
        _ = _ := by
          rw [List.range_succ, List.map_append, List.sum_append, Matrix.mulVec_add,
            Matrix.mulVec_mulVec, ← pow_succ]
          simp [add_assoc]
  -- each term `(Θ Σ̃)^i X` as a sum of relabelled graphs
  have hmain : ∀ i, ((M ^ i) *ᵥ fX) (e 0) = (X.map fun g => Expansion.valR
      ((G14.words n i).map fun o => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m))
        PF Dt e ω).sum := by
    intro i
    have h1 : ((M ^ i) *ᵥ fX) (e 0) =
        ∑ x, (X.map fun g => (M ^ i) (e 0) x * g.2.valR PF Dt ![x, e 1, e 2] ω).sum := by
      simp only [Matrix.mulVec, dotProduct, hfX, Expansion.valR]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [List.sum_map_mul_left]
    rw [h1, ← list_sum_finset_sum]
    refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
    exact (G14.chainValue n hn Sig 𝒬.SigN g.2 (hXr g hg) hE Ω ι PF Dt hSc i e ω).symm
  -- the value of `T` as the relabelled graphs and the remainder
  have hT : tGraph.valR PF Dt e ω =
      (G14.relabels (G14.wordsUpTo n K) X).valR PF Dt e ω + Rem.valR PF Dt e ω := by
    have h := congrFun (hiter (K + 1)) (e 0)
    have h1 : fT (e 0) = tGraph.valR PF Dt e ω := by simp only [hfT, vec_eta]
    rw [← h1, h, Pi.add_apply, hRem Ω ι PF Dt hA hSc e ω, list_sum_fun_apply]
    congr 1
    · simp only [hmain]
      rw [list_sum_comm, G14.relabels, valR_flatMap]
      refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
      rw [G14.wordsUpTo, List.map_flatMap, valR_flatMap]
  -- the rearrangement into the right side of [II, (3.1)]
  have hK' := Words.relabels_wordsUpTo_perm hK
  have hW : ∀ S : Expansion 3, (G14.relabels (G14.wordsUpTo n K) S).valR PF Dt e ω =
      (G14.relabels ([] :: chainLabels n) S).valR PF Dt e ω +
        (G14.relabels (G14.extra n K) S).valR PF Dt e ω := fun S => by
    rw [← valR_append]
    exact valR_perm PF Dt e ω (hK' S)
  have happ : ∀ (W : List (List ℕ)) (S₁ S₂ : Expansion 3),
      G14.relabels W (S₁ ++ S₂) = G14.relabels W S₁ ++ G14.relabels W S₂ := fun W S₁ S₂ => by
    simp [G14.relabels]
  have hfilt : ((𝒬.solveLow n).R.filter fun g => decide ((n : ℤ) < g.2.ord)) =
      (𝒬.solveLow n).R.filter fun g => !decide (g.2.ord ≤ (n : ℤ)) :=
    List.filter_congr fun g _ => by
      by_cases h : g.2.ord ≤ (n : ℤ) <;> simp [h, not_le.1]
  have h1 := valR_filter_add PF Dt e ω (𝒬.solveLow n).R fun g => decide (g.2.ord ≤ (n : ℤ))
  rw [← hfilt] at h1
  have hlead := hW leadExp
  rw [relabels_leadExp, valR_append, valR_relabels_leadExp_extra] at hlead
  have hRR := hW 𝒬.R
  have hQQ := hW 𝒬.Q
  rw [← Words.solveLow_R] at hRR
  rw [← Words.solveLow_Q] at hQQ
  rw [hT, hX]
  simp only [happ, valR_append, TRec.rhs, G14.solveRec]
  rw [hlead, hRR, hQQ]
  linear_combination h1

end Chain

/-- The identity [II, (3.1)] for `G14.solveRec` ([II, (6.1)–(6.3)]): from the `n`-th order
`T`-equation `𝒬` with error order `D ≤ 2K` and a remainder with the value of
`(Θ Σ̃^{(n)})^{K+1} T`, on the records whose self-energy matrices of even order `≤ n` are the
values of `Sig` with `Σ_n` of `𝒬`. -/
def G14.solveRec_identityStmt : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (D K : ℕ) (𝒬 : TEqRec) (Rem : Expansion 3),
    n < D → D ≤ 2 * K → 𝒬.IsTEqStruct Sig n D →
    (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (Dt : Ω → Data ι),
        modelAdm Ω ι PF Dt → (∀ ω, SigConsistent (Function.update Sig n 𝒬.SigN) (n + 1) (Dt ω)) →
        ∀ (e : Fin 3 → ι) (ω : Ω),
          Rem.valR PF Dt e ω =
            ∑ x, (((Dt ω).Theta * sigTilde n 𝒬.SigN (Dt ω)) ^ (K + 1)) (e 0) x *
              tGraph.valR PF Dt ![x, e 1, e 2] ω) →
    (G14.solveRec n K 𝒬 Rem).Identity (Function.update Sig n 𝒬.SigN) n

/-- **The identity of the solved `T`-equation** ([II, (3.1)] by [II, (6.1)–(6.3)]): the record
`G14.solveRec n K 𝒬 Rem` of an `n`-th order `T`-equation with error order `n < D ≤ 2K` satisfies
the identity [II, (3.1)]. Of [II, Def 3.3] it reads the identity [II, (3.5)], the shape of `Σ_n`
and the form (4) of the graphs. -/
theorem G14.solveRec_identity : G14.solveRec_identityStmt := by
  intro n hn Sig D K 𝒬 Rem hD hDK hS hRem
  exact Chain.solveRec_identity_of hn Sig K 𝒬 Rem (by omega) hS.2.1 hS.2.2.2.1
    (fun g hg => G14.rootedTheta_of_thetaRooted (hS.2.2.2.2.2.1 g hg)) hRem


namespace Chain

end Chain

namespace Chain

end Chain

end RBM8D
