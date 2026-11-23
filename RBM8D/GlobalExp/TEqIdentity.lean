module

public import RBM8D.GlobalExp.TEqShape
public import RBM8D.Graph.ValueLemmas

@[expose] public section

/-!
# The identity [II, (3.5)] of the construction of [II, (6.8)] and the classes of its correction graphs

For the construction `TEqSigma.Strat` of the `n`-th order `T`-equation from the run of
[II, Strategy 6.6] (the proof of [II, Theorem 3.7], [II, (6.7)–(6.8)]):

* the value of an output graph `Θ_{⊗x} 𝒮_{xy} t_{y,⊕⊖}` of [II, Lemma 6.7] in the leaf form
  `TEqSigma.LeafOf`, and the value of its correction graphs `Θ_{⊗x} 𝒮_{xy} τ_{y,⊕⊖}`, `τ` the three
  recollision terms of [II, (4.15)], with `t = T + (t - T)`;
* **[II, (3.5)]** for `TEqSigma.Strat` (`TEqSigma.identity`): with `Σ̃^{(n)} = Σ_n + Σ_{l=4}^{n-1} Σ_l`
  ([II, (3.14)]), the `T`-equation read off the output graphs satisfies the identity of
  `TEqRec.Identity`;
* the molecular graph of a correction graph is that of its output graph up to names
  ([II, Def 2.11] in the block reading), so a correction graph is globally standard
  ([II, Def 6.2]);
* **the classes of the correction graphs** (`TEqSigma.corr_classes`): scaling order `ord g + 1` or
  `ord g + 2`, and the clauses read by `TRec.def63_of_leaves` on `R` (order `≤ n`) and on `A`
  (order `> n`) ([II, Def 6.3]).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Lists, sums and the three recollision terms -/

/-- A permutation of lists is a bijection of the positions. -/
private theorem TEqIdentity_perm_idx {β : Type*} {l₁ l₂ : List β} (h : l₁.Perm l₂) :
    ∃ σ : Fin l₁.length ≃ Fin l₂.length, ∀ i, l₂[σ i] = l₁[i] := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun i => rfl⟩
  | @cons x t₁ t₂ _ ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr σ).trans (finSuccEquiv _).symm), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Equiv.trans_apply, finSuccEquiv_succ, Equiv.optionCongr_apply, Option.map_some,
        finSuccEquiv_symm_some, Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ]
      exact hσ j
  | swap x y l =>
    refine ⟨Equiv.swap 0 1, fun i => ?_⟩
    rcases i with ⟨_ | _ | i, hi⟩
    · simp
    · simp
    · have h0 : (⟨i + 1 + 1, hi⟩ : Fin (y :: x :: l).length) ≠ 0 := by simp [Fin.ext_iff]
      have h1 : (⟨i + 1 + 1, hi⟩ : Fin (y :: x :: l).length) ≠ 1 := by simp [Fin.ext_iff]
      simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨σ₁, h₁⟩ := ih₁
    obtain ⟨σ₂, h₂⟩ := ih₂
    exact ⟨σ₁.trans σ₂, fun i => (h₂ (σ₁ i)).trans (h₁ i)⟩

/-- The factor of a component read through a map of the atoms. -/
private theorem TEqIdentity_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) : (c.map f).val D σ = c.val D (σ ∘ f) := by
  obtain ⟨κ, u, v, T, ℓ⟩ := c
  simp only [Comp.map, Comp.val, List.map_map]
  rfl

/-- The sum over the labellings of the internal atoms of a leaf form with `x ≠ y`, read through
the atoms `x`, `y`, `α` and the bijection `e`. -/
private theorem TEqIdentity_sum3 {ι : Type} [Fintype ι] [DecidableEq ι] {N m : ℕ} {x y α : Fin N}
    (hxy : x ≠ y) (hαx : α ≠ x) (hαy : α ≠ y)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) (F : ι → ι → ι → (Fin m → ι) → ℂ) :
    ∑ s : Fin N → ι, F (s x) (s y) (s α) (fun j => s (e j)) =
      ∑ a, ∑ b, ∑ c, ∑ t, F a b c t := by
  classical
  let E : (Fin N → ι) ≃ ι × ι × ι × (Fin m → ι) :=
    { toFun := fun s => (s x, s y, s α, fun j => s (e j))
      invFun := fun p i => if i = x then p.1 else if i = y then p.2.1 else if i = α then p.2.2.1
        else if h : i ≠ x ∧ i ≠ y ∧ i ≠ α then p.2.2.2 (e.symm ⟨i, h⟩) else p.1
      left_inv := fun s => by
        funext i
        by_cases h1 : i = x
        · simp [h1]
        by_cases h2 : i = y
        · simp [h2, hxy.symm]
        by_cases h3 : i = α
        · simp [h3, hαx, hαy]
        simp only [h1, h2, h3, ite_false, ne_eq, not_false_eq_true, and_self, dite_true,
          Equiv.apply_symm_apply]
      right_inv := fun p => by
        obtain ⟨a, b, c, t⟩ := p
        simp only [hxy.symm, hαx, hαy, ite_false, ite_true, Prod.mk.injEq, true_and]
        funext j
        have hj := (e j).2
        simp only [hj.1, hj.2.1, hj.2.2, ite_false, ne_eq, not_false_eq_true, and_self, dite_true,
          Subtype.coe_eta, Equiv.symm_apply_apply] }
  rw [Fintype.sum_equiv E (fun s => F (s x) (s y) (s α) (fun j => s (e j)))
    (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2) (fun s => rfl)]
  simp only [Fintype.sum_prod_type]

/-- The sum over the labellings of the internal atoms of a leaf form with `x = y`, read through
the atoms `x`, `α` and the bijection `e`. -/
private theorem TEqIdentity_sum2 {ι : Type} [Fintype ι] [DecidableEq ι] {N m : ℕ} {x α : Fin N}
    (hαx : α ≠ x) (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ x ∧ a ≠ α})
    (F : ι → ι → (Fin m → ι) → ℂ) :
    ∑ s : Fin N → ι, F (s x) (s α) (fun j => s (e j)) = ∑ a, ∑ c, ∑ t, F a c t := by
  classical
  let E : (Fin N → ι) ≃ ι × ι × (Fin m → ι) :=
    { toFun := fun s => (s x, s α, fun j => s (e j))
      invFun := fun p i => if i = x then p.1 else if i = α then p.2.1
        else if h : i ≠ x ∧ i ≠ x ∧ i ≠ α then p.2.2 (e.symm ⟨i, h⟩) else p.1
      left_inv := fun s => by
        funext i
        by_cases h1 : i = x
        · simp [h1]
        by_cases h3 : i = α
        · simp [h3, hαx]
        simp only [h1, h3, ite_false, ne_eq, not_false_eq_true, and_self, dite_true,
          Equiv.apply_symm_apply]
      right_inv := fun p => by
        obtain ⟨a, c, t⟩ := p
        simp only [hαx, ite_false, ite_true, Prod.mk.injEq, true_and]
        funext j
        have hj := (e j).2
        simp only [hj.1, hj.2.2, ite_false, ne_eq, not_false_eq_true, and_self, dite_true,
          Subtype.coe_eta, Equiv.symm_apply_apply] }
  rw [Fintype.sum_equiv E (fun s => F (s x) (s α) (fun j => s (e j)))
    (fun p => F p.1 p.2.1 p.2.2) (fun s => rfl)]
  simp only [Fintype.sum_prod_type]

/-- The first recollision term of [II, (4.15)]: `s_{⊗α} w⁺_α Ḡ_{α⊖} 1_{α = ⊕} 1_{α ≠ ⊖}`. -/
def TEqIdentity_T1 : List (Comp (Atom 3 1)) :=
  [mkC (.waved .s) (.inl 0) (.inr 0), mkC (.weight .plus) (.inr 0) (.inr 0),
    mkC (.G .minus) (.inr 0) (.inl 2), mkC .dot (.inr 0) (.inl 1), mkC .xdot (.inr 0) (.inl 2)]

/-- The second recollision term of [II, (4.15)]: `s_{⊗α} G_{α⊕} w⁻_α 1_{α ≠ ⊕} 1_{α = ⊖}`. -/
def TEqIdentity_T2 : List (Comp (Atom 3 1)) :=
  [mkC (.waved .s) (.inl 0) (.inr 0), mkC (.G .plus) (.inr 0) (.inl 1),
    mkC (.weight .minus) (.inr 0) (.inr 0), mkC .xdot (.inr 0) (.inl 1), mkC .dot (.inr 0) (.inl 2)]

/-- The third recollision term of [II, (4.15)]: `s_{⊗α} w⁺_α w⁻_α 1_{α = ⊕} 1_{α = ⊖}`. -/
def TEqIdentity_T3 : List (Comp (Atom 3 1)) :=
  [mkC (.waved .s) (.inl 0) (.inr 0), mkC (.weight .plus) (.inr 0) (.inr 0),
    mkC (.weight .minus) (.inr 0) (.inr 0), mkC .dot (.inr 0) (.inl 1), mkC .dot (.inr 0) (.inl 2)]

/-- Components with the same code are equal. -/
private theorem TEqIdentity_code_inj {k n : ℕ} {c d : Comp (Atom k n)} (h : c.code = d.code) :
    c = d := by
  have ha : Function.Injective
      (Sum.elim (fun i : Fin k => i.val) (fun i : Fin n => k + i.val)) := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg _ (Fin.ext hab)
    · have := a.2; omega
    · have := b.2; omega
    · exact congrArg _ (Fin.ext (by omega))
  obtain ⟨κ, u, v, T, ℓ⟩ := c
  obtain ⟨κ', u', v', T', ℓ'⟩ := d
  simp only [Comp.code, CompCode.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have h4' := List.map_injective_iff.2 ha h4
  have h5' : ℓ = ℓ' := by
    refine Option.map_injective ?_ h5
    rintro ⟨p, a⟩ ⟨q, b⟩ hpq
    simp only [Prod.map, Prod.mk.injEq, id] at hpq
    rw [hpq.1, ha hpq.2]
  rw [h1, ha h2, ha h3, h4', h5']

set_option maxHeartbeats 4000000 in
-- kernel evaluation of the recollision terms
private theorem TEqIdentity_tVarCorr_code : tVarCorr.map (fun g => (g.1, g.2.code)) =
    [(1, (⟨TEqIdentity_T1, 1⟩ : Graph 3 1).code), (1, (⟨TEqIdentity_T2, 1⟩ : Graph 3 1).code),
     (1, (⟨TEqIdentity_T3, 1⟩ : Graph 3 1).code)] := by
  decide +kernel

/-- The three graphs of `tVarCorr` (the recollision terms of [II, (4.15)]): one internal atom `α`
and the components `TEqIdentity_T1`, `TEqIdentity_T2` or `TEqIdentity_T3`. -/
private theorem TEqIdentity_tVarCorr_cases : ∀ τ ∈ tVarCorr, ∃ t : Graph 3 1, τ = ⟨1, t⟩ ∧
    (t.comps = TEqIdentity_T1 ∨ t.comps = TEqIdentity_T2 ∨ t.comps = TEqIdentity_T3) := by
  have hc := TEqIdentity_tVarCorr_code
  have key : ∀ (τ : Σ n, Graph 3 n) (L : List (Comp (Atom 3 1))),
      (τ.1, τ.2.code) = (1, (⟨L, 1⟩ : Graph 3 1).code) → ∃ t : Graph 3 1, τ = ⟨1, t⟩ ∧ t.comps = L := by
    rintro ⟨n, t⟩ L h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    refine ⟨t, rfl, ?_⟩
    simp only [Graph.code] at h
    exact List.map_injective_iff.2 (fun _ _ => TEqIdentity_code_inj) h
  intro τ hτ
  have hm : (τ.1, τ.2.code) ∈ tVarCorr.map (fun g => (g.1, g.2.code)) := List.mem_map_of_mem hτ
  rw [hc] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h
  · obtain ⟨t, rfl, ht⟩ := key τ _ h; exact ⟨t, rfl, Or.inl ht⟩
  · obtain ⟨t, rfl, ht⟩ := key τ _ h; exact ⟨t, rfl, Or.inr (Or.inl ht)⟩
  · obtain ⟨t, rfl, ht⟩ := key τ _ h; exact ⟨t, rfl, Or.inr (Or.inr ht)⟩

set_option maxHeartbeats 4000000 in
-- kernel evaluation of the recollision terms
/-- The graphs of `tVarCorr` have no labels. -/
private theorem TEqIdentity_tVarCorr_labelFree : ∀ g ∈ tVarCorr, g.2.LabelFree := by
  decide +kernel

/-! ## The value of an output graph of [II, Lemma 6.7] -/

section Value

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The factor `s_{bc} G_{c e₁} Ḡ_{c e₂} 1_{c ≠ e₁} 1_{c ≠ e₂}` of the `t`-variable. -/
private def TEqIdentity_tl (D : Data ι) (b c e₁ e₂ : ι) : ℂ :=
  D.S b c * D.Gm ∅ c e₁ * star (D.Gm ∅ c e₂) * (if c = e₁ then 0 else 1) *
    (if c = e₂ then 0 else 1)

/-- The value of the `t`-variable `t_{b,e₁e₂}`. -/
private theorem TEqIdentity_tVar_val (D : Data ι) (b e₁ e₂ : ι) :
    tVarGraph.val D ![b, e₁, e₂] = ∑ c, (cm * cmb).eval D.m * TEqIdentity_tl D b c e₁ e₂ := by
  unfold Graph.val Graph.term
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _
    (fun c => (cm * cmb).eval D.m * TEqIdentity_tl D b c e₁ e₂) (fun s => ?_)]
  simp only [tVarGraph, TEqIdentity_tl, mkC, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Comp.val, Sum.elim_inl, Sum.elim_inr, List.map_nil, List.toFinset_nil,
    Charge.apply, Equiv.funUnique_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.default_eq_zero, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one]
  by_cases h1 : s 0 = e₁ <;> by_cases h2 : s 0 = e₂ <;>
    simp only [h1, h2, ite_true, ite_false, mul_zero, zero_mul, mul_one] <;> ring

omit [Fintype ι] [DecidableEq ι] in
/-- The value of a product of coefficients. -/
private theorem TEqIdentity_eval_mul (z : ℂ) (p q : Coeff) :
    Coeff.eval z (p * q) = Coeff.eval z p * Coeff.eval z q := by
  simp [Coeff.eval]

/-- `ℓ` `×`-dotted loops have the value `0 ^ ℓ`. -/
private theorem TEqIdentity_loops {V : Type*} (D : Data ι) (σ : V → ι) (u : V) (ℓ : ℕ) :
    ((List.replicate ℓ (mkC .xdot u u)).map (Comp.val D σ)).prod = 0 ^ ℓ := by
  rw [List.map_replicate, List.prod_replicate]
  simp [Comp.val, mkC]

/-- `×`-dotted edges between `a` and `b₁` and between `a` and `b₂`, at least one of each, in
either orientation, have the value `1_{a ≠ b₁} 1_{a ≠ b₂}`. -/
private theorem TEqIdentity_xprod {V : Type*} (D : Data ι) (σ : V → ι) {X : List (Comp V)}
    {a b₁ b₂ : V}
    (hX : ∀ c ∈ X, c = mkC .xdot a b₁ ∨ c = mkC .xdot b₁ a ∨ c = mkC .xdot a b₂ ∨
      c = mkC .xdot b₂ a)
    (h1 : mkC .xdot a b₁ ∈ X ∨ mkC .xdot b₁ a ∈ X) (h2 : mkC .xdot a b₂ ∈ X ∨ mkC .xdot b₂ a ∈ X) :
    (X.map (Comp.val D σ)).prod =
      (if σ a = σ b₁ then 0 else 1) * (if σ a = σ b₂ then 0 else 1) := by
  have hv : ∀ u v : V, Comp.val D σ (mkC .xdot u v) = if σ u = σ v then 0 else 1 := by
    intro u v; rfl
  by_cases e₁ : σ a = σ b₁
  · simp only [e₁, ite_true, zero_mul]
    refine List.prod_eq_zero (List.mem_map.2 ?_)
    rcases h1 with h | h
    · exact ⟨_, h, by simp [hv, e₁]⟩
    · exact ⟨_, h, by simp [hv, e₁]⟩
  by_cases e₂ : σ a = σ b₂
  · simp only [e₂, ite_true, mul_zero]
    refine List.prod_eq_zero (List.mem_map.2 ?_)
    rcases h2 with h | h
    · exact ⟨_, h, by simp [hv, e₂]⟩
    · exact ⟨_, h, by simp [hv, e₂]⟩
  simp only [e₁, e₂, ite_false, mul_one]
  refine List.prod_eq_one fun z hz => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
  have e₁' : ¬ σ b₁ = σ a := fun h => e₁ h.symm
  have e₂' : ¬ σ b₂ = σ a := fun h => e₂ h.symm
  rcases hX c hc with rfl | rfl | rfl | rfl <;> simp [hv, e₁, e₂, e₁', e₂']

/-- The value of the graph `S` of a leaf form at `x, y`: its coefficient, the dotted edge
`δ_{xy}` when the atoms `x`, `y` of the leaf form are one atom, the components `R` and the
`×`-dotted loops. -/
private theorem TEqIdentity_S_term {N m : ℕ} (D : Data ι) {S : Graph 2 m} {x y : Fin N}
    {R : List (Comp (Atom 2 m))} {ℓ : ℕ}
    (hSp : S.comps.Perm ((if x = y then [mkC .dot (.inl 0) (.inl 1)] else []) ++ R ++
      List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0)))) (a b : ι) (t : Fin m → ι) :
    S.term D (Sum.elim ![a, b] t) = S.coeff.eval D.m *
      ((if x = y then (if a = b then 1 else 0) else 1) *
        (R.map (Comp.val D (Sum.elim ![a, b] t))).prod * 0 ^ ℓ) := by
  unfold Graph.term
  rw [(hSp.map _).prod_eq, List.map_append, List.map_append, List.prod_append, List.prod_append,
    TEqIdentity_loops]
  by_cases h : x = y
  · have hd : (([mkC .dot (.inl 0) (.inl 1)] : List (Comp (Atom 2 m))).map
        (Comp.val D (Sum.elim ![a, b] t))).prod = if a = b then 1 else 0 := by
      simp [Comp.val, mkC]
    simp only [h, ite_true, hd]
  · simp only [h, ite_false, List.map_nil, List.prod_nil]

omit [Fintype ι] [DecidableEq ι] in
/-- The atom map of the leaf form, read at the labelling `Sum.elim e₀ s`. -/
private theorem TEqIdentity_phi_comp {N m : ℕ} (e₀ : Fin 3 → ι) (s : Fin N → ι) (x y α : Fin N)
    (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}) :
    (Sum.elim e₀ s ∘ Sum.elim ![(.inr x : Atom 3 N), .inr y] fun j => .inr (e j).1) =
      Sum.elim ![s x, s y] (fun j => s (e j)) := by
  funext w
  rcases w with i | j
  · fin_cases i <;> rfl
  · rfl

/-- **The value of an output graph of [II, Lemma 6.7]** in the leaf form `TEqSigma.LeafOf g S`
(the display before [II, (6.7)]): at every data record with `m ≠ 0` and `s` symmetric,
`g = Σ_{x,y} Θ_{𝔞x} S_{xy} t_{y,𝔟₁𝔟₂}`, with `t` the `t`-variable `tVarGraph`. -/
private theorem TEqIdentity_leaf_val (D : Data ι) (hm : D.m ≠ 0)
    (hS : ∀ a b, D.S a b = D.S b a) {g : Σ n, Graph 3 n} {m : ℕ} {S : Graph 2 m}
    (h : TEqSigma.LeafOf g S) (e₀ : Fin 3 → ι) :
    g.2.val D e₀ = ∑ a, ∑ b, D.Theta (e₀ 0) a * S.val D ![a, b] *
      tVarGraph.val D ![b, e₀ 1, e₀ 2] := by
  obtain ⟨x, y, α, e, R, sy, X, ℓ, hαx, hαy, hsy, hX, hX1, hX2, hgp, hSp, hc⟩ := h
  set Rp : ι → ι → (Fin m → ι) → ℂ := fun a b t => (R.map (Comp.val D (Sum.elim ![a, b] t))).prod
    with hRp
  set c₀ : ℂ := (S.coeff * (cm * cmb)).eval D.m with hc₀
  -- the term of `g`
  have hterm : ∀ s : Fin g.1 → ι, g.2.term D (Sum.elim e₀ s) =
      c₀ * D.Theta (e₀ 0) (s x) * Rp (s x) (s y) (fun j => s (e j)) * 0 ^ ℓ *
        TEqIdentity_tl D (s y) (s α) (e₀ 1) (e₀ 2) := by
    intro s
    unfold Graph.term
    rw [hc D.m hm, (hgp.map _).prod_eq]
    simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append, List.map_map,
      List.map_nil, List.prod_nil]
    rw [TEqIdentity_loops, TEqIdentity_xprod D _ hX hX1 hX2]
    have hR : (R.map (Comp.val D (Sum.elim e₀ s) ∘ Comp.map
        (Sum.elim ![(.inr x : Atom 3 g.1), .inr y] fun j => .inr (e j).1))).prod =
        Rp (s x) (s y) (fun j => s (e j)) := by
      rw [hRp]
      congr 1
      refine List.map_congr_left fun r _ => ?_
      rw [Function.comp_apply, TEqIdentity_val_map, TEqIdentity_phi_comp]
    have hsyv : Comp.val D (Sum.elim e₀ s) sy = D.S (s y) (s α) := by
      rcases hsy with rfl | rfl
      · rfl
      · exact hS _ _
    rw [hR, hsyv, hc₀]
    simp only [TEqIdentity_tl, Comp.val, mkC, Sum.elim_inl, Sum.elim_inr, List.map_nil,
      List.toFinset_nil, Charge.apply, Data.chain, List.foldl_nil]
    by_cases h1 : s α = e₀ 1 <;> by_cases h2 : s α = e₀ 2 <;>
      simp only [h1, h2, ite_true, ite_false, mul_zero, zero_mul, mul_one] <;> ring
  -- the value of `S` and of the `t`-variable
  have hSv : ∀ a b, S.val D ![a, b] = ∑ t, S.coeff.eval D.m *
      ((if x = y then (if a = b then 1 else 0) else 1) * Rp a b t * 0 ^ ℓ) := by
    intro a b
    unfold Graph.val
    exact Finset.sum_congr rfl fun t _ => TEqIdentity_S_term D hSp a b t
  simp only [hSv, TEqIdentity_tVar_val]
  unfold Graph.val
  simp only [hterm]
  have key : ∀ (A : ℂ) (f : (Fin m → ι) → ℂ) (g : ι → ℂ),
      A * (∑ t, f t) * (∑ c, g c) = ∑ c, ∑ t, A * f t * g c := by
    intro A f g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  by_cases hxy : x = y
  · subst hxy
    rw [TEqIdentity_sum2 hαx e (fun a c t => c₀ * D.Theta (e₀ 0) a * Rp a a t * 0 ^ ℓ *
      TEqIdentity_tl D a c (e₀ 1) (e₀ 2))]
    refine Finset.sum_congr rfl fun a _ => ?_
    symm
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [ite_true, one_mul]
    rw [key]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hc₀]
    simp only [TEqIdentity_eval_mul]
    ring
  · rw [TEqIdentity_sum3 hxy hαx hαy e (fun a b c t => c₀ * D.Theta (e₀ 0) a * Rp a b t * 0 ^ ℓ *
      TEqIdentity_tl D b c (e₀ 1) (e₀ 2))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hxy, ite_false, one_mul]
    rw [key]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hc₀]
    simp only [TEqIdentity_eval_mul]
    ring

/-- The sum over the labellings of `k + m` atoms is the sum over the labellings of the first `k`
and of the last `m`. -/
private theorem TEqIdentity_sum_append {k m : ℕ} (F : (Fin k → ι) → (Fin m → ι) → ℂ) :
    ∑ s : Fin (k + m) → ι, F (fun i => s (Fin.castAdd m i)) (fun j => s (Fin.natAdd k j)) =
      ∑ u, ∑ t, F u t := by
  rw [← (Fin.appendEquiv k m).sum_comp, Fintype.sum_prod_type]
  simp [Fin.appendEquiv, Fin.append_left, Fin.append_right]

/-- The sum over the labellings of two atoms. -/
private theorem TEqIdentity_sum_two (G : (Fin 2 → ι) → ℂ) :
    ∑ u, G u = ∑ a, ∑ b, G ![a, b] := by
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => ι) G (fun p => G ![p.1, p.2]) (fun u => ?_),
    Fintype.sum_prod_type]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The sum over the labellings of one atom. -/
private theorem TEqIdentity_sum_one (G : (Fin 1 → ι) → ℂ) :
    ∑ u, G u = ∑ a, G (fun _ => a) := by
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) G (fun a => G (fun _ => a)) (fun u => ?_)]
  congr 1
  funext i
  rw [Subsingleton.elim i default]
  rfl

/-- The value of a formal sum substituted into a graph without labels at `x, ⊕, ⊖`: the sum over
the internal atoms of the term of the host times the value of the formal sum at `x, e₁, e₂`. -/
private theorem TEqIdentity_subst_val (D : Data ι) {M : ℕ} (H : Graph 3 M) (x : Atom 3 M)
    (hH : H.LabelFree) (E : Expansion 3) (hE : ∀ g ∈ E, g.2.LabelFree) (e₀ : Fin 3 → ι) :
    (H.globalSubst x (.inl 1) (.inl 2) E).val D e₀ =
      ∑ s : Fin M → ι, H.term D (Sum.elim e₀ s) *
        E.val D ![Sum.elim e₀ s x, e₀ 1, e₀ 2] := by
  let PF : PFamily Unit ι := ⟨fun _ f => f⟩
  have hgl : ∀ g ∈ E, (H.glue x (.inl 1) (.inl 2) g.2).LabelFree := by
    intro g hg c hc
    simp only [Graph.glue, liftCs, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨c', hc', rfl⟩ | ⟨c', hc', rfl⟩
    · simp [Comp.map, hH c' hc']
    · simp [Comp.map, hE g hg c' hc']
  have hlab : ∀ g ∈ E, g.2.labels.length ≤ 1 := by
    intro g hg
    have : g.2.comps.filterMap Comp.label = [] := List.filterMap_eq_nil_iff.2 (hE g hg)
    simp [Graph.labels, this]
  induction E with
  | nil => simp [Graph.globalSubst, Expansion.val]
  | cons g E ih =>
    have ih' := ih (fun g' hg' => hE g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hgl g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hlab g' (List.mem_cons_of_mem _ hg'))
    have h1 := glue_value 3 M g.1 H x (.inl 1) (.inl 2) g.2 Unit ι PF (fun _ => D) e₀ ()
      hH (hlab g List.mem_cons_self)
    rw [Graph.valR_of_labelFree _ _ _ _ _ _ _ _ (hgl g List.mem_cons_self)] at h1
    simp only [Graph.valR_of_labelFree _ _ _ _ _ _ _ _ (hE g List.mem_cons_self)] at h1
    have h2 : (H.globalSubst x (.inl 1) (.inl 2) (g :: E)).val D e₀ =
        (H.glue x (.inl 1) (.inl 2) g.2).val D e₀ +
          (H.globalSubst x (.inl 1) (.inl 2) E).val D e₀ := by
      simp [Graph.globalSubst, Expansion.val]
    rw [h2, h1, ih', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Expansion.val, List.map_cons, List.sum_cons, Sum.elim_inl, mul_add]

/-- **The value of the correction graphs** `TEqShape_corrOf ⟨m, S⟩` of a graph `S` without labels
(the `t → T` rewriting before [II, (6.7)], with [II, (4.15)]):
`Σ_{x,y} Θ_{𝔞x} S_{xy} (tVarCorr)_{y,𝔟₁𝔟₂}`; at `δ_{xy} ∈ S` the factor `1_{x = y}` reduces the
sum to `x = y`. -/
private theorem TEqIdentity_corr_val (D : Data ι) {m : ℕ} (S : Graph 2 m) (hL : S.LabelFree)
    (e₀ : Fin 3 → ι) :
    (TEqShape_corrOf ⟨m, S⟩).val D e₀ = ∑ a, ∑ b, D.Theta (e₀ 0) a * S.val D ![a, b] *
      tVarCorr.val D ![b, e₀ 1, e₀ 2] := by
  classical
  have hE := TEqIdentity_tVarCorr_labelFree
  set Tc : ι → ℂ := fun b => tVarCorr.val D ![b, e₀ 1, e₀ 2] with hTc
  unfold TEqShape_corrOf
  split_ifs with hd
  · -- `x = y`: the host `Θ_{⊗x} S_{xx}` without the dotted edge
    have hH : (TEqShape_thetaS₁ S).LabelFree := by
      intro c hc
      simp only [TEqShape_thetaS₁, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨c', hc', rfl⟩
      · rfl
      · simp [Comp.map, hL c' (List.mem_of_mem_erase hc')]
    rw [TEqIdentity_subst_val D _ _ hH _ hE]
    have hp := List.perm_cons_erase hd
    set L := S.comps.erase (mkC .dot (.inl 0) (.inl 1)) with hLdef
    set Lp : ι → (Fin m → ι) → ℂ := fun a t => (L.map (Comp.val D (Sum.elim (fun _ => a) t))).prod
      with hLp
    have hterm : ∀ s : Fin (1 + m) → ι, (TEqShape_thetaS₁ S).term D (Sum.elim e₀ s) *
        tVarCorr.val D ![Sum.elim e₀ s (.inr 0), e₀ 1, e₀ 2] =
        S.coeff.eval D.m * D.Theta (e₀ 0) (s (Fin.castAdd m 0)) *
          Lp (s (Fin.castAdd m 0)) (fun j => s (Fin.natAdd 1 j)) * Tc (s (Fin.castAdd m 0)) := by
      intro s
      unfold Graph.term
      simp only [TEqShape_thetaS₁, List.map_cons, List.prod_cons, List.map_map, hLp, hTc]
      have : L.map (Comp.val D (Sum.elim e₀ s) ∘ Comp.map (Sum.elim (fun _ => (.inr 0 : Atom 3 (1 + m)))
          fun j => .inr (Fin.natAdd 1 j))) =
          L.map (Comp.val D (Sum.elim (fun _ => s (Fin.castAdd m 0)) fun j => s (Fin.natAdd 1 j))) := by
        refine List.map_congr_left fun c _ => ?_
        rw [Function.comp_apply, TEqIdentity_val_map]
        congr 1
        funext w
        rcases w with i | j <;> rfl
      rw [← hLdef, this]
      have h0 : (Fin.castAdd m 0 : Fin (1 + m)) = 0 := Fin.ext (by simp)
      simp only [Comp.val, mkC, Sum.elim_inl, Sum.elim_inr, Data.chain, List.foldl_nil, h0]
      ring
    simp only [hterm]
    rw [TEqIdentity_sum_append (fun u t => S.coeff.eval D.m * D.Theta (e₀ 0) (u 0) * Lp (u 0) t *
      Tc (u 0)), TEqIdentity_sum_one]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)]
    · unfold Graph.val Graph.term
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [(hp.map _).prod_eq, List.map_cons, List.prod_cons]
      have h1 : Comp.val D (Sum.elim ![a, a] t) (mkC .dot (.inl 0) (.inl 1)) = 1 := by
        simp [Comp.val, mkC]
      have h2 : Sum.elim ![a, a] t = Sum.elim (fun _ => a) t := by
        funext w
        rcases w with i | j
        · fin_cases i <;> rfl
        · rfl
      rw [h1, h2]
      simp only [hLp, ← hLdef]
      ring
    · unfold Graph.val Graph.term
      have h0 : ∀ t : Fin m → ι, (S.comps.map (Comp.val D (Sum.elim ![a, b] t))).prod = 0 := by
        intro t
        rw [(hp.map _).prod_eq, List.map_cons, List.prod_cons]
        have : Comp.val D (Sum.elim ![a, b] t) (mkC .dot (.inl 0) (.inl 1)) = 0 := by
          simp [Comp.val, mkC, Ne.symm hb]
        rw [this, zero_mul]
      simp [h0]
  · -- `x ≠ y`: the host `Θ_{⊗x} S_{xy}`
    have hH : (TEqShape_thetaS S).LabelFree := by
      intro c hc
      simp only [TEqShape_thetaS, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨c', hc', rfl⟩
      · rfl
      · simp [Comp.map, hL c' hc']
    rw [TEqIdentity_subst_val D _ _ hH _ hE]
    set Sp : (Fin 2 → ι) → (Fin m → ι) → ℂ := fun u t =>
      (S.comps.map (Comp.val D (Sum.elim u t))).prod with hSp
    have hterm : ∀ s : Fin (2 + m) → ι, (TEqShape_thetaS S).term D (Sum.elim e₀ s) *
        tVarCorr.val D ![Sum.elim e₀ s (.inr 1), e₀ 1, e₀ 2] =
        S.coeff.eval D.m * D.Theta (e₀ 0) (s (Fin.castAdd m 0)) *
          Sp (fun i => s (Fin.castAdd m i)) (fun j => s (Fin.natAdd 2 j)) *
            Tc (s (Fin.castAdd m 1)) := by
      intro s
      unfold Graph.term
      simp only [TEqShape_thetaS, List.map_cons, List.prod_cons, List.map_map, hSp, hTc]
      have : S.comps.map (Comp.val D (Sum.elim e₀ s) ∘ Comp.map (Sum.elim
          (fun i => (.inr (Fin.castAdd m i) : Atom 3 (2 + m))) fun j => .inr (Fin.natAdd 2 j))) =
          S.comps.map (Comp.val D (Sum.elim (fun i => s (Fin.castAdd m i))
            fun j => s (Fin.natAdd 2 j))) := by
        refine List.map_congr_left fun c _ => ?_
        rw [Function.comp_apply, TEqIdentity_val_map]
        congr 1
        funext w
        rcases w with i | j <;> rfl
      rw [this]
      have h0 : (Fin.castAdd m 0 : Fin (2 + m)) = 0 := Fin.ext (by simp)
      have h1 : (Fin.castAdd m 1 : Fin (2 + m)) = 1 :=
        Fin.ext (by simpa [Fin.val_one'] using (Nat.mod_eq_of_lt (show 1 < 2 + m by omega)).symm)
      simp only [Comp.val, mkC, Sum.elim_inl, Sum.elim_inr, Data.chain, List.foldl_nil, h0, h1]
      ring
    simp only [hterm]
    rw [TEqIdentity_sum_append (fun u t => S.coeff.eval D.m * D.Theta (e₀ 0) (u 0) * Sp u t *
      Tc (u 1)), TEqIdentity_sum_two]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    unfold Graph.val Graph.term
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hSp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring

/-- The value of a formal sum of graphs without labels, read with any family of conditional
expectations. -/
private theorem TEqIdentity_expValR {k : ℕ} {Ω : Type} (PF : PFamily Ω ι) (D : Ω → Data ι)
    (E : Expansion k) (hE : ∀ g ∈ E, g.2.LabelFree) (e₀ : Fin k → ι) (ω : Ω) :
    E.valR PF D e₀ ω = E.val (D ω) e₀ := by
  unfold Expansion.valR Expansion.val
  congr 1
  refine List.map_congr_left fun g hg => ?_
  rw [Graph.valR_of_labelFree _ _ _ _ _ _ _ _ (hE g hg)]

set_option maxHeartbeats 4000000 in
-- kernel evaluation of the `O_dot` forms of `T_{x,y₁y₂}`
/-- The `O_dot` forms of `T_{x,y₁y₂}` have no labels. -/
private theorem TEqIdentity_oDot_labelFree : ∀ g ∈ oDot tGraph, g.2.LabelFree := by
  decide +kernel

/-- **`t = T + (t - T)`** ([II, (4.15)]): the value of the `t`-variable is the value of
`T_{x,y₁y₂}` plus the value of the three recollision terms `tVarCorr`. -/
private theorem TEqIdentity_tVar_split (D : Data ι) (e₀ : Fin 3 → ι) :
    tVarGraph.val D e₀ = tGraph.val D e₀ + tVarCorr.val D e₀ := by
  let PF : PFamily Unit ι := ⟨fun _ f => f⟩
  have h2 := congrFun (oDot_value 3 1 Unit ι PF (fun _ => D) trivial tGraph e₀) ()
  rw [TEqIdentity_expValR PF _ _ TEqIdentity_oDot_labelFree,
    Graph.valR_of_labelFree _ _ _ _ _ _ _ _ (by decide)] at h2
  have hhead : (oDot tGraph).take 1 =
      [⟨1, ⟨tVarGraph.comps, (-1 : Coeff) ^ 0 * (cm * cmb)⟩⟩] := by
    rfl
  have hsplit : oDot tGraph = [⟨1, ⟨tVarGraph.comps, (-1 : Coeff) ^ 0 * (cm * cmb)⟩⟩] ++
      (oDot tGraph).drop 1 := by
    rw [← hhead, List.take_append_drop]
  have h3 : Expansion.val [⟨1, ⟨tVarGraph.comps, (-1 : Coeff) ^ 0 * (cm * cmb)⟩⟩] D e₀ =
      tVarGraph.val D e₀ := by
    simp [Expansion.val, Graph.val, Graph.term, tVarGraph]
  have hneg : ∀ (L : Expansion 3) (f : (Σ n, Graph 3 n) → ℂ),
      (L.map fun g => -f g).sum = -(L.map f).sum := by
    intro L f
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  have h4 : tVarCorr.val D e₀ = -Expansion.val ((oDot tGraph).drop 1) D e₀ := by
    unfold tVarCorr Expansion.smul Expansion.val
    rw [List.map_map, ← hneg]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, Graph.val, Graph.smul, Graph.term, TEqIdentity_eval_mul,
      Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [Coeff.eval]
  rw [hsplit] at h2
  simp only [Expansion.val, List.map_append, List.sum_append] at h2
  simp only [Expansion.val] at h3 h4 ⊢
  rw [h4, ← h3, ← h2]
  ring

end Value

/-! ## Lists of output graphs -/

section Lists

variable {β : Type*}

/-- The sum over a filter is the sum of the terms that pass it. -/
private theorem TEqIdentity_sum_filter (L : List β) (p : β → Bool) (f : β → ℂ) :
    ((L.filter p).map f).sum = (L.map fun b => if p b then f b else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih]

/-- The sum over a `flatMap`. -/
private theorem TEqIdentity_sum_flatMap {γ : Type*} (L : List β) (h : β → List γ) (f : γ → ℂ) :
    ((L.flatMap h).map f).sum = (L.map fun b => ((h b).map f).sum).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- The sum of a sum of two functions. -/
private theorem TEqIdentity_sum_add (L : List β) (f g : β → ℂ) :
    (L.map fun b => f b + g b).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- A sum over a list of terms of orders in `[0, n]` is the sum over the orders of the sums over
the terms of each order. -/
private theorem TEqIdentity_sum_ord (L : List β) (o : β → ℤ) (n : ℕ) (f : β → ℂ)
    (h : ∀ b ∈ L, 0 ≤ o b ∧ o b ≤ n) :
    (L.map f).sum = ∑ l ∈ Finset.range (n + 1),
      ((L.filter fun b => decide (o b = (l : ℤ))).map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    obtain ⟨h0, h1⟩ := h a List.mem_cons_self
    have hsplit : ∀ l : ℕ, ((List.filter (fun b => decide (o b = (l : ℤ))) (a :: L)).map f).sum =
        (if o a = (l : ℤ) then f a else 0) +
          ((L.filter fun b => decide (o b = (l : ℤ))).map f).sum := by
      intro l
      by_cases hl : o a = (l : ℤ) <;> simp [List.filter_cons, hl]
    simp only [hsplit, Finset.sum_add_distrib, List.map_cons, List.sum_cons, ← ih']
    congr 1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, o a = k := ⟨(o a).toNat, by omega⟩
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hk, Ne.symm hl]) (fun hk' => ?_)]
    · simp [hk]
    · exfalso
      exact hk' (Finset.mem_range.2 (by omega))

end Lists

/-! ## The identity [II, (3.5)] -/

/-- The value of a formal sum of graphs read through a `flatMap`. -/
private theorem TEqIdentity_val_flatMap {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Expansion 3) (h : (Σ n, Graph 3 n) → Expansion k) (D : Data ι) (u : Fin k → ι) :
    Expansion.val (L.flatMap h) D u = (L.map fun g => (h g).val D u).sum :=
  TEqIdentity_sum_flatMap L h _

/-- The graph `S` of a leaf form of a graph without labels has no labels. -/
private theorem TEqIdentity_leafOf_labelFree {g : Σ n, Graph 3 n} {m : ℕ} {S : Graph 2 m}
    (h : TEqSigma.LeafOf g S) (hL : g.2.LabelFree) : S.LabelFree := by
  obtain ⟨x, y, α, e, R, sy, X, ℓ, -, -, -, -, -, -, hgp, hSp, -⟩ := h
  intro c hc
  rcases List.mem_append.1 (hSp.mem_iff.1 hc) with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · split_ifs at hc
      · rw [List.mem_singleton] at hc; rw [hc]; rfl
      · simp at hc
    · have hm : c.map (Sum.elim ![(.inr x : Atom 3 g.1), .inr y] fun j => .inr (e j).1) ∈
          g.2.comps :=
        hgp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map_of_mem hc)))))
      have := hL _ hm
      simp only [Comp.map, Option.map_eq_none_iff] at this
      exact this
  · rw [List.eq_of_mem_replicate hc]; rfl

/-- The correction graphs of a graph `S` without labels have no labels. -/
private theorem TEqIdentity_corr_labelFree {m : ℕ} {S : Graph 2 m} (hL : S.LabelFree) :
    ∀ c ∈ TEqShape_corrOf ⟨m, S⟩, c.2.LabelFree := by
  classical
  have hE := TEqIdentity_tVarCorr_labelFree
  intro c hc
  unfold TEqShape_corrOf at hc
  split_ifs at hc
  all_goals
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hc
    intro d hd
    simp only [Graph.glue, liftCs, List.mem_append, List.mem_map, TEqShape_thetaS₁,
      TEqShape_thetaS, List.mem_cons] at hd
    rcases hd with ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · rcases hd' with rfl | ⟨d'', hd'', rfl⟩
      · rfl
      · simp [Comp.map, hL d'' (by first | exact hd'' | exact List.mem_of_mem_erase hd'')]
    · simp [Comp.map, hE τ hτ d' hd']

/-- **The value of an output graph of [II, Lemma 6.7] of the run** (the `t → T` rewriting before
[II, (6.7)]): for a graph `g` of the class `Graph.LeafDet` of the run, not a `⊕/⊖`-recollision
graph, of order `≤ n`, at every data record with `m ≠ 0` and `s` symmetric,
`g = Σ_{x,y} Θ_{𝔞x} (σ' g)_{xy} T_{y,𝔟₁𝔟₂} + corr g`, with `σ' g = TEqSigma.sigma' g`. -/
private theorem TEqIdentity_det_val {ι : Type} [Fintype ι] [DecidableEq ι] {n D : ℕ}
    {Sig : ℕ → Expansion 2} {𝒯 : TRec} (hn : 3 ≤ n) (hT : 𝒯.IsTExpStruct Sig (n - 1) D)
    {g : Σ m, Graph 3 m} (hg : g ∈ RunCompare.run TEqSigma.qFam n D 𝒯) (hdet : g.2.LeafDet)
    (hNR : ¬ g.2.IsRecollision {1, 2}) (hord : g.2.ord ≤ n) (Dd : Data ι) (hm : Dd.m ≠ 0)
    (hS : ∀ a b, Dd.S a b = Dd.S b a) (e₀ : Fin 3 → ι) :
    g.2.val Dd e₀ = (TEqSigma.corr g).val Dd e₀ + ∑ a, ∑ b, Dd.Theta (e₀ 0) a *
      (TEqSigma.sigma' g).val Dd ![a, b] * tGraph.val Dd ![b, e₀ 1, e₀ 2] := by
  obtain ⟨m, 𝒮, hσ, hL, -⟩ := TEqSigma.detLeaf_form n D Sig 𝒯 hn hT g hg hdet hNR hord
  have hdot := TEqSigma.detLeaf_dotFree n D Sig 𝒯 hn hT g hg hdet hNR hord
  obtain ⟨hL', -, -⟩ := TEqSigma.normS_leafOf hL hdot
  obtain ⟨S', hS'⟩ : ∃ S' : Graph 2 m, TEqSigma.normS ⟨m, 𝒮⟩ = ⟨m, S'⟩ := ⟨_, rfl⟩
  rw [hS'] at hL'
  have hσ' : TEqSigma.sigma' g = [⟨m, S'⟩] := by
    rw [TEqSigma.sigma', hσ, List.map_singleton, hS']
  have hc : TEqSigma.corr g = TEqShape_corrOf ⟨m, S'⟩ := by
    unfold TEqSigma.corr
    rw [if_pos ⟨hdet, hNR⟩, hσ', List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hlf := TEqIdentity_leafOf_labelFree hL' hdet.1
  rw [hσ', hc, TEqIdentity_corr_val Dd _ hlf, TEqIdentity_leaf_val Dd hm hS hL']
  simp only [TEqIdentity_tVar_split, Expansion.val, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, mul_add, Finset.sum_add_distrib]
  ring

/-! ## The output classes -/

section Classes

variable {N : ℕ} {Γ : Graph 3 N}

/-- A walk from a set to its complement has an edge with one end in the set and one outside. -/
private theorem TEqIdentity_reach_cross {V : Type*} {r : V → V → Prop} {P : V → Prop} {u v : V}
    (h : (SimpleGraph.fromRel r).Reachable u v) (hu : P u) (hv : ¬ P v) :
    ∃ a b, r a b ∧ (P a ∧ ¬ P b ∨ P b ∧ ¬ P a) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact absurd hu hv
  | @cons a b c hab _ ih =>
    by_cases hb : P b
    · exact ih hb hv
    · rw [SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with h | h
      · exact ⟨a, b, h, Or.inl ⟨hu, hb⟩⟩
      · exact ⟨b, a, h, Or.inr ⟨hu, hb⟩⟩

/-- In a graph with only diffusive edges at `⊗` that is not a `⊕/⊖`-recollision graph, no
external atom lies in the dotted block of an internal atom. -/
private theorem TEqIdentity_unp (hTD : Γ.TensorDiffusive) (hNR : ¬ Γ.IsRecollision {1, 2})
    (a : Fin 3) (b : Fin N) : ¬ Γ.SameBlock (.inl a) (.inr b) := by
  intro h
  obtain ⟨u, v, ⟨c, hc, hd, rfl, rfl⟩, hcr⟩ :=
    TEqIdentity_reach_cross (P := fun w : Atom 3 N => w.isLeft = true) h rfl (by simp)
  have htd := List.all_eq_true.1 hTD c hc
  have key : ∀ (a' : Fin 3), (c.x = .inl a' ∧ c.y.isRight = true) ∨
      (c.y = .inl a' ∧ c.x.isRight = true) → False := by
    intro a' h'
    fin_cases a'
    · rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, hd, Kind.isDiffusive] at htd
    · exact hNR ⟨c, hc, hd, by
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨⟨1, by simp, h1⟩, h2⟩
        · exact Or.inr ⟨⟨1, by simp, h1⟩, h2⟩⟩
    · exact hNR ⟨c, hc, hd, by
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨⟨2, by simp, h1⟩, h2⟩
        · exact Or.inr ⟨⟨2, by simp, h1⟩, h2⟩⟩
  rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨a', ha'⟩ := Sum.isLeft_iff.1 h1
    exact key a' (Or.inl ⟨ha', by simpa using h2⟩)
  · obtain ⟨a', ha'⟩ := Sum.isLeft_iff.1 h1
    exact key a' (Or.inr ⟨ha', by simpa using h2⟩)

/-- A graph of the class `Graph.LeafR` of scaling order `> n` is of the class `Graph.LeafA n`. -/
private theorem TEqIdentity_leafA_of_leafR {n : ℕ} (h : Γ.LeafR) (ho : (n : ℤ) < Γ.ord) :
    Γ.LeafA n := by
  obtain ⟨hR, hL, hgs, hE, hC, hPM⟩ := h
  exact ⟨by omega, hL, hgs.1, hE, hC, fun _ => hgs, hPM⟩

/-- An output graph of the class `Graph.LeafDet` with only diffusive edges at `⊗`, not a
`⊕/⊖`-recollision graph, of scaling order `> n`, is of the class `Graph.LeafA n`: `⊕` and `⊖`
do not lie in one block, since that block would contain an internal atom. -/
private theorem TEqIdentity_leafA_of_det {n : ℕ} (h : Γ.LeafDet) (hTD : Γ.TensorDiffusive)
    (hNR : ¬ Γ.IsRecollision {1, 2}) (ho : (n : ℤ) < Γ.ord) : Γ.LeafA n := by
  obtain ⟨hL, hgs, -, hE, hC⟩ := h
  refine ⟨by omega, hL, hgs.1, hE, hC, fun _ => hgs, fun hPM => ?_⟩
  rw [Graph.pmBlock_iff_sameBlock] at hPM
  obtain ⟨b, hb⟩ := hE.1 (.inl 1) (.inl 2) (by simp) hPM
  exact absurd hb (TEqIdentity_unp hTD hNR 1 b)

/-- A `Q`-graph carries a label. -/
private theorem TEqIdentity_not_labelFree_of_leafQ (h : Γ.LeafQ) : ¬ Γ.LabelFree := by
  obtain ⟨⟨u, ⟨c, hc, hl⟩, -⟩, -⟩ := h
  intro hL
  rw [hL c hc] at hl
  cases hl

/-- **The five output classes of the construction** ([II, §6.4], (6.7)–(6.8)): an output graph of
the run of scaling order `≤ D` is in exactly one of the classes `R` (`Graph.LeafR`, order `≤ n`),
`A` (`Graph.LeafA n`, not in `R`), `Q` (`Graph.LeafQ`) and the output graphs of [II, Lemma 6.7]
(`Graph.LeafDet`, not a `⊕/⊖`-recollision graph, order `≤ n`). -/
private theorem TEqIdentity_classes {n D : ℕ} (hnD : n < D) (hTD : Γ.TensorDiffusive)
    (hO : Γ.LeafR ∨ Γ.LeafA n ∨ Γ.LeafQ ∨ Γ.LeafDet)
    (hR3 : Γ.LeafDet → Γ.IsRecollision {1, 2} → Γ.LeafR) :
    ((Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ ¬ (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ Γ.LeafA n) ∧ ¬ Γ.LeafQ ∧
        ¬ (Γ.LeafDet ∧ ¬ Γ.IsRecollision {1, 2} ∧ Γ.ord ≤ (n : ℤ))) ∨
      (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ Γ.LeafA n) ∧
        ¬ Γ.LeafQ ∧ ¬ (Γ.LeafDet ∧ ¬ Γ.IsRecollision {1, 2} ∧ Γ.ord ≤ (n : ℤ))) ∨
      (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ ¬ (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ Γ.LeafA n) ∧
        Γ.LeafQ ∧ ¬ (Γ.LeafDet ∧ ¬ Γ.IsRecollision {1, 2} ∧ Γ.ord ≤ (n : ℤ))) ∨
      (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ ¬ (¬ (Γ.LeafR ∧ Γ.ord ≤ (n : ℤ)) ∧ Γ.LeafA n) ∧
        ¬ Γ.LeafQ ∧ (Γ.LeafDet ∧ ¬ Γ.IsRecollision {1, 2} ∧ Γ.ord ≤ (n : ℤ))) := by
  set pR := Γ.LeafR ∧ Γ.ord ≤ (n : ℤ) with hpR
  set pA := ¬ pR ∧ Γ.LeafA n with hpA
  set pD := Γ.LeafDet ∧ ¬ Γ.IsRecollision {1, 2} ∧ Γ.ord ≤ (n : ℤ) with hpD
  have hQL := @TEqIdentity_not_labelFree_of_leafQ N Γ
  have hRQ : Γ.LeafR → ¬ Γ.LeafQ := fun h hQ => hQL hQ h.2.1
  have hAQ : Γ.LeafA n → ¬ Γ.LeafQ := fun h hQ => hQL hQ h.2.1
  have hDQ : Γ.LeafDet → ¬ Γ.LeafQ := fun h hQ => hQL hQ h.1
  have hRA : Γ.LeafR → Γ.LeafA n ∨ Γ.ord ≤ (n : ℤ) := by
    intro h
    by_cases ho : Γ.ord ≤ (n : ℤ)
    · exact Or.inr ho
    · exact Or.inl (TEqIdentity_leafA_of_leafR h (by omega))
  have hAo : Γ.LeafA n → ¬ Γ.ord ≤ (n : ℤ) := fun h ho => by have := h.1; omega
  have fromR : Γ.LeafR → (pR ∧ ¬ pA ∧ ¬ Γ.LeafQ ∧ ¬ pD) ∨ (¬ pR ∧ pA ∧ ¬ Γ.LeafQ ∧ ¬ pD) := by
    intro h
    have hnd : ¬ pD := fun hD => hD.2.1 h.1
    rcases hRA h with hA | ho
    · exact Or.inr ⟨fun hR => hAo hA hR.2, ⟨fun hR => hAo hA hR.2, hA⟩, hRQ h, hnd⟩
    · exact Or.inl ⟨⟨h, ho⟩, fun hA => hA.1 ⟨h, ho⟩, hRQ h, hnd⟩
  rcases hO with h | h | h | h
  · rcases fromR h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · by_cases hR : pR
    · exact Or.inl ⟨hR, fun hA => hA.1 hR, hAQ h, fun hD => hD.2.1 hR.1.1⟩
    · exact Or.inr (Or.inl ⟨hR, ⟨hR, h⟩, hAQ h, fun hD => hAo h hD.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨fun hR => hRQ hR.1 h, fun hA => hAQ hA.2 h, h,
      fun hD => hDQ hD.1 h⟩))
  · by_cases hRc : Γ.IsRecollision {1, 2}
    · rcases fromR (hR3 h hRc) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · by_cases ho : Γ.ord ≤ (n : ℤ)
      · exact Or.inr (Or.inr (Or.inr ⟨fun hR => hRc hR.1.1, fun hA => hAo hA.2 ho, hDQ h,
          ⟨h, hRc, ho⟩⟩))
      · have hA := TEqIdentity_leafA_of_det h hTD hRc (n := n) (by omega)
        exact Or.inr (Or.inl ⟨fun hR => hRc hR.1.1, ⟨fun hR => hRc hR.1.1, hA⟩, hDQ h,
          fun hD => ho hD.2.2⟩)

end Classes

/-! ## The identity [II, (3.5)] for the construction -/

/-- A term is the sum of its restrictions to five exclusive and covering conditions. -/
private theorem TEqIdentity_ite5 (x : ℂ) {a b c d e : Prop} [Decidable a] [Decidable b]
    [Decidable c] [Decidable d] [Decidable e]
    (h : (a ∧ ¬ b ∧ ¬ c ∧ ¬ d ∧ ¬ e) ∨ (¬ a ∧ b ∧ ¬ c ∧ ¬ d ∧ ¬ e) ∨ (¬ a ∧ ¬ b ∧ c ∧ ¬ d ∧ ¬ e) ∨
      (¬ a ∧ ¬ b ∧ ¬ c ∧ d ∧ ¬ e) ∨ (¬ a ∧ ¬ b ∧ ¬ c ∧ ¬ d ∧ e)) :
    x = (if a then x else 0) + (if b then x else 0) + (if c then x else 0) +
      (if d then x else 0) + (if e then x else 0) := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ |
    ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
    simp only [h1, h2, h3, h4, h5, ite_true, ite_false] <;> ring

/-- Sums of sums over a list. -/
private theorem TEqIdentity_sum_comm {β ι : Type*} [Fintype ι] (L : List β)
    (F : β → ι → ι → ℂ) :
    (L.map fun g => ∑ a, ∑ b, F g a b).sum = ∑ a, ∑ b, (L.map fun g => F g a b).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]

/-- A constant factor out of a sum over a list. -/
private theorem TEqIdentity_sum_mul {β : Type*} (L : List β) (c d : ℂ) (v : β → ℂ) :
    (L.map fun g => c * v g * d).sum = c * (L.map v).sum * d := by
  induction L with
  | nil => simp
  | cons g L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

open Classical in
/-- **`Σ̃^{(n)}` from the output graphs of [II, Lemma 6.7]** ([II, (3.14)], [II, (6.7)–(6.9)]):
for the run at the cutoff order `n` from `𝒯 (n - 1) D` of families of `H(n - 1)` recording
`TEqSigma.Strat`, the normal forms `TEqSigma.sigma' g` of the output graphs of [II, Lemma 6.7]
of order `≤ n` sum to `Σ̃^{(n)}` at every data record whose self-energy matrices of orders `< n`
are the values of `Sig`. -/
private theorem TEqIdentity_sigTilde {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hn : 3 ≤ n) {Sig : ℕ → Expansion 2} {𝒬 : ℕ → ℕ → TEqRec} {𝒯 : ℕ → ℕ → TRec}
    (hH : HFam TEqSigma.Strat Sig (n - 1) 𝒬 𝒯) {D : ℕ} (hD : n < D) (Dd : Data ι)
    (hSC : SigConsistent Sig n Dd) (a b : ι) :
    Expansion.val (((RunCompare.run TEqSigma.qFam n D (𝒯 (n - 1) D)).filter fun g =>
        decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (n : ℤ))).flatMap
        TEqSigma.sigma') Dd ![a, b] =
      sigTilde n (TEqSigma.Strat n D (𝒯 (n - 1) D)).SigN Dd a b := by
  have hT : (𝒯 (n - 1) D).IsTExpStruct Sig (n - 1) D :=
    (hH.1 (n - 1) D (by omega) le_rfl (by omega)).2.1
  set F := RunCompare.run TEqSigma.qFam n D (𝒯 (n - 1) D) with hF
  set DL := F.filter fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧
    g.2.ord ≤ (n : ℤ)) with hDL
  -- the orders of the output graphs of [II, Lemma 6.7]
  have hfl : ∀ l : ℕ, l ≤ n → DL.filter (fun g => decide (g.2.ord = (l : ℤ))) =
      F.filter fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord = (l : ℤ)) := by
    intro l hl
    rw [hDL, List.filter_filter]
    refine List.filter_congr fun g _ => ?_
    by_cases h3 : g.2.ord = (l : ℤ)
    · simp [h3, hl]
    · simp [h3]
  have hev : ∀ g ∈ DL, Even g.2.ord ∧ 4 ≤ g.2.ord ∧ g.2.ord ≤ n := by
    intro g hg
    rw [hDL, List.mem_filter, decide_eq_true_eq] at hg
    obtain ⟨-, -, -, -, -, h1, h2⟩ :=
      TEqSigma.detLeaf_form n D Sig _ hn hT g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
    exact ⟨h1, h2, hg.2.2.2⟩
  rw [TEqIdentity_val_flatMap, TEqIdentity_sum_ord DL (fun g => g.2.ord) n _
    (fun g hg => ⟨by have := (hev g hg).2.1; omega, (hev g hg).2.2⟩)]
  have hval : ∀ l : ℕ, l ≤ n → ((DL.filter fun g => decide (g.2.ord = (l : ℤ))).map
      fun g => (TEqSigma.sigma' g).val Dd ![a, b]).sum =
      Expansion.val ((F.filter fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧
        g.2.ord = (l : ℤ))).flatMap TEqSigma.sigma') Dd ![a, b] := by
    intro l hl
    rw [hfl l hl, TEqIdentity_val_flatMap]
  rw [Finset.sum_range_succ, hval n le_rfl]
  -- the order `n`: `Σ_n`
  have hN : Expansion.val ((F.filter fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧
      g.2.ord = (n : ℤ))).flatMap TEqSigma.sigma') Dd ![a, b] =
      Expansion.val (TEqSigma.Strat n D (𝒯 (n - 1) D)).SigN Dd ![a, b] := by
    rw [TEqSigma.Strat, TEqSigma.strat_eq hn hT]
    unfold TEqSigma.ofLeaves Expansion.val
    simp only
    refine List.Perm.sum_eq (List.Perm.map _ ?_)
    exact Multiset.coe_eq_coe.1 (Multiset.coe_toList _).symm
  rw [hN]
  -- the orders `l < n`: `Σ_l`
  have hl : ∀ l ∈ Finset.range n, ((DL.filter fun g => decide (g.2.ord = (l : ℤ))).map
      fun g => (TEqSigma.sigma' g).val Dd ![a, b]).sum =
      if 4 ≤ l ∧ Even l then Dd.Sig l a b else 0 := by
    intro l hl
    have hl' := Finset.mem_range.1 hl
    split_ifs with h
    · rw [hval l hl'.le, hSC l h.1 hl' h.2, Matrix.of_apply]
      exact List.Perm.sum_eq (List.Perm.map _ (TEqSigma.sig_perm TEqSigma.sigma' TEqSigma.corr n
        hn Sig 𝒬 𝒯 hH D hD l h.1 hl'))
    · have : DL.filter (fun g => decide (g.2.ord = (l : ℤ))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro g hg hgl
        rw [decide_eq_true_eq] at hgl
        obtain ⟨⟨r, hr⟩, h4, -⟩ := hev g hg
        exact h ⟨by omega, ⟨(r.toNat), by omega⟩⟩
      rw [this]
      rfl
  rw [Finset.sum_congr rfl hl, ← Finset.sum_filter]
  have hset : (Finset.range n).filter (fun l => 4 ≤ l ∧ Even l) = (Finset.Ico 4 n).filter Even := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h2, h1⟩, h3⟩, fun ⟨⟨h2, h1⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [hset, sigTilde, Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
  ring

open Classical in
/-- **[II, (3.5)] for the construction `TEqSigma.Strat`** (the proof of [II, Theorem 3.7],
[II, (6.7)–(6.8)]): for `n ≥ 3` and families of `H(n - 1)` that record `TEqSigma.Strat`, for every
error order `D > n`, the `T`-equation `TEqSigma.Strat n D (𝒯 (n - 1) D)` satisfies the identity
`T = m Θ Ḡ + Σ_x (Θ Σ̃^{(n)})_{𝔞x} T_{x,𝔟₁𝔟₂} + R + A + Q + Err'` with
`Σ̃^{(n)} = Σ_n + Σ_{l=4}^{n-1} Σ_l` ([II, (3.14)]). -/
theorem TEqSigma.identity : ∀ n : ℕ, 3 ≤ n → ∀ (Sig : ℕ → Expansion 2) (𝒬 : ℕ → ℕ → TEqRec)
    (𝒯 : ℕ → ℕ → TRec), HFam TEqSigma.Strat Sig (n - 1) 𝒬 𝒯 → ∀ D, n < D →
    (TEqSigma.Strat n D (𝒯 (n - 1) D)).Identity Sig n := by
  intro n hn Sig 𝒬 𝒯 hH D hD
  have hT : (𝒯 (n - 1) D).IsTExpStruct Sig (n - 1) D :=
    (hH.1 (n - 1) D (by omega) le_rfl (by omega)).2.1
  have hQ2 : (𝒬 2 D).IsTEqStruct Sig 2 D := (hH.1 2 D le_rfl (by omega) (by omega)).1
  rw [hH.2.2.2.2.1 D (by omega) (by omega)] at hQ2
  have hspec := RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig _ hn hT
  intro Ω ι _ _ PF Dt hadm hSC e ω
  have hsig := TEqIdentity_sigTilde hn hH hD (Dt ω) (hSC ω)
  obtain ⟨A⟩ := hadm
  have hm : (Dt ω).m ≠ 0 := by rw [A.data_m ω]; exact msc_ne_zero _
  have hS : ∀ a b, (Dt ω).S a b = (Dt ω).S b a := by
    intro a b
    rw [A.data_S ω]
    simp [Matrix.map_apply, A.isSymm.apply]
  set F := RunCompare.run TEqSigma.qFam n D (𝒯 (n - 1) D) with hF
  -- `T = m Θ Ḡ + A₂ + Q₂` ([I, Lemma 2.5]) and the run keeps values
  have hid2 := hQ2.2.1 Ω ι PF Dt ⟨A⟩ (fun _ k hk hk2 _ => absurd hk2 (by omega)) e ω
  have hs2 : sigTilde 2 h2TEq.SigN (Dt ω) = 0 := by
    ext x y
    simp [sigTilde, h2TEq, Expansion.val]
  simp only [hs2, mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at hid2
  have hrun := congrFun (globalRun_valueB reorder_value Sig n D (𝒯 (n - 1) D) (by omega) hT.2.1
    hT.2.2.1 (fun g hg => (hT.2.2.2.2.2.1 g hg).2.2.2) _ _ hspec.2.1 Ω ι PF Dt ⟨A⟩ hSC e) ω
  have hT0 : tGraph.LabelFree := by decide
  have hLHS : tGraph.valR PF Dt e ω = leadExp.valR PF Dt e ω + F.valR PF Dt e ω := by
    rw [hid2, ← hrun]
    simp only [h2TEq, Expansion.valR, List.map_append, List.sum_append]
    have hR : h2Rec.R = [] := rfl
    have hE : h2Rec.Err = [] := rfl
    rw [hR, hE]
    simp only [List.map_nil, List.sum_nil, add_zero]
    ring
  set f : (Σ m, Graph 3 m) → ℂ := fun g => g.2.valR PF Dt e ω with hf
  rw [hLHS, TEqSigma.Strat, TEqSigma.strat_eq hn hT]
  unfold TEqSigma.ofLeaves
  simp only [Expansion.valR, List.map_append, List.sum_append]
  rw [← hf]
  -- the det leaves
  set DL := F.filter fun g => decide (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧
    g.2.ord ≤ (n : ℤ)) with hDL
  have hcorr : (((DL.flatMap TEqSigma.corr).filter
      (fun g => decide (g.2.ord ≤ (n : ℤ)))).map f).sum + (((DL.flatMap TEqSigma.corr).filter
        (fun g => decide ((n : ℤ) < g.2.ord))).map f).sum =
      ((DL.flatMap TEqSigma.corr).map f).sum := by
    rw [TEqIdentity_sum_filter, TEqIdentity_sum_filter, ← TEqIdentity_sum_add]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    by_cases h : g.2.ord ≤ (n : ℤ)
    · simp [h, show ¬ (n : ℤ) < g.2.ord by omega]
    · simp [h, show (n : ℤ) < g.2.ord by omega]
  have hTv : ∀ x, tGraph.valR PF Dt ![x, e 1, e 2] ω = tGraph.val (Dt ω) ![x, e 1, e 2] := by
    intro x
    rw [Graph.valR_of_labelFree _ _ _ _ _ _ _ _ hT0]
  have hdet : (DL.map f).sum = ((DL.flatMap TEqSigma.corr).map f).sum +
      ∑ x, ((Dt ω).Theta * sigTilde n (TEqSigma.Strat n D (𝒯 (n - 1) D)).SigN (Dt ω)) (e 0) x *
        tGraph.valR PF Dt ![x, e 1, e 2] ω := by
    have hpt : ∀ g ∈ DL, f g = ((TEqSigma.corr g).map f).sum + ∑ a, ∑ b, (Dt ω).Theta (e 0) a *
        (TEqSigma.sigma' g).val (Dt ω) ![a, b] * tGraph.val (Dt ω) ![b, e 1, e 2] := by
      intro g hg
      rw [hDL, List.mem_filter, decide_eq_true_eq] at hg
      obtain ⟨m, 𝒮, hσ, hL, -⟩ :=
        TEqSigma.detLeaf_form n D Sig _ hn hT g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
      have hdot := TEqSigma.detLeaf_dotFree n D Sig _ hn hT g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
      obtain ⟨hL', -, -⟩ := TEqSigma.normS_leafOf hL hdot
      obtain ⟨S', hS'⟩ : ∃ S' : Graph 2 m, TEqSigma.normS ⟨m, 𝒮⟩ = ⟨m, S'⟩ := ⟨_, rfl⟩
      rw [hS'] at hL'
      have hc : TEqSigma.corr g = TEqShape_corrOf ⟨m, S'⟩ := by
        unfold TEqSigma.corr
        rw [if_pos ⟨hg.2.1, hg.2.2.1⟩, TEqSigma.sigma', hσ, List.map_singleton, hS',
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hcl := TEqIdentity_corr_labelFree (TEqIdentity_leafOf_labelFree hL' hg.2.1.1)
      rw [← hc] at hcl
      have := TEqIdentity_det_val hn hT hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (Dt ω) hm hS e
      show g.2.valR PF Dt e ω = _
      rw [Graph.valR_of_labelFree _ _ _ _ _ _ _ _ hg.2.1.1]
      show g.2.val (Dt ω) e = _
      rw [this]
      congr 1
      rw [← TEqIdentity_expValR PF Dt _ hcl]
      rfl
    rw [List.map_congr_left hpt, TEqIdentity_sum_add, ← TEqIdentity_sum_flatMap,
      TEqIdentity_sum_comm]
    congr 1
    simp only [hTv, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [TEqIdentity_sum_mul, ← TEqIdentity_val_flatMap, hsig]
  -- the partition of the output graphs
  have hpart : (F.map f).sum = ((F.filter fun g => decide (¬ (D : ℤ) < g.2.ord ∧ g.2.LeafR ∧
      g.2.ord ≤ (n : ℤ))).map f).sum + ((F.filter fun g => decide (¬ (D : ℤ) < g.2.ord ∧
      ¬ (g.2.LeafR ∧ g.2.ord ≤ (n : ℤ)) ∧ g.2.LeafA n)).map f).sum +
      ((F.filter fun g => decide (¬ (D : ℤ) < g.2.ord ∧ g.2.LeafQ)).map f).sum +
      ((F.filter fun g => decide ((D : ℤ) < g.2.ord)).map f).sum + (DL.map f).sum := by
    rw [hDL]
    simp only [TEqIdentity_sum_filter, ← TEqIdentity_sum_add]
    congr 1
    refine List.map_congr_left fun g hg => ?_
    obtain ⟨-, -, -, hLC, -, hO⟩ := hspec.2.2 g hg
    have hR3 := (RunExports.selRun_exports _ TEqSigma.qFam_spec n D Sig _ hn hT _ hspec.1 g
      hg).2.2
    show f g = (if _ then f g else 0) + (if _ then f g else 0) + (if _ then f g else 0) +
      (if _ then f g else 0) + (if _ then f g else 0)
    simp only [decide_eq_true_eq]
    refine TEqIdentity_ite5 _ ?_
    by_cases hE : (D : ℤ) < g.2.ord
    · have hnd : ¬ (g.2.LeafDet ∧ ¬ g.2.IsRecollision {1, 2} ∧ g.2.ord ≤ (n : ℤ)) :=
        fun h => by have := h.2.2; omega
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fun h => h.1 hE, fun h => h.1 hE, fun h => h.1 hE,
        hE, hnd⟩)))
    · have hO' : g.2.LeafR ∨ g.2.LeafA n ∨ g.2.LeafQ ∨ g.2.LeafDet := by
        rcases hO with h | h | h | h | h
        · exact absurd h.1 hE
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h.1))
        · exact Or.inr (Or.inr (Or.inr h))
      have hnE : ¬ (D : ℤ) < g.2.ord := hE
      rcases TEqIdentity_classes (show n < D by omega) hLC.1 hO' (fun h1 h2 => hR3 h1 h2 hE) with
        ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl ⟨⟨hnE, h1⟩, fun h => h2 h.2, fun h => h3 h.2, hE, h4⟩
      · exact Or.inr (Or.inl ⟨fun h => h1 h.2, ⟨hnE, h2⟩, fun h => h3 h.2, hE, h4⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨fun h => h1 h.2, fun h => h2 h.2, ⟨hnE, h3⟩, hE, h4⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fun h => h1 h.2, fun h => h2 h.2, fun h => h3 h.2,
          hE, h4⟩)))
  have hSN : (TEqSigma.Strat n D (𝒯 (n - 1) D)).SigN = (TEqSigma.ofLeaves n D TEqSigma.sigma'
      TEqSigma.corr F).SigN := by
    rw [TEqSigma.Strat, TEqSigma.strat_eq hn hT]
  rw [hpart, hdet, ← hcorr, ← hF, hSN]
  unfold TEqSigma.ofLeaves
  ring

/-! ## Molecular graphs up to names -/

section Transport

/-- `MGraph.Transported` is transitive. -/
private theorem TEqIdentity_tr_trans {V E V' E' V'' E'' : Type} [DecidableEq V'] [DecidableEq V'']
    {G : MGraph V E} {G' : MGraph V' E'} {G'' : MGraph V'' E''} (h₁ : G.Transported G')
    (h₂ : G'.Transported G'') : G.Transported G'' := by
  obtain ⟨f₁, g₁, hg₁, hf₁, hi₁, hx₁, hv₁, hc₁, he₁, hs₁⟩ := h₁
  obtain ⟨f₂, g₂, hg₂, hf₂, hi₂, hx₂, hv₂, hc₂, he₂, hs₂⟩ := h₂
  have hvert : ∀ v ∈ (↑G.int ∪ ↑G.ext : Set V), f₁ v ∈ (↑G'.int ∪ ↑G'.ext : Set V') := by
    rintro v (hv | hv)
    · exact Or.inl (by rw [Finset.mem_coe, hi₁]; exact Finset.mem_image_of_mem f₁ hv)
    · exact Or.inr (by rw [Finset.mem_coe, hx₁]; exact Finset.mem_image_of_mem f₁ hv)
  refine ⟨f₂ ∘ f₁, g₂ ∘ g₁, fun e₁ e₂ p₁ p₂ h => hg₁ e₁ e₂ p₁ p₂ (hg₂ _ _ (by rw [hc₁ e₁ p₁]; exact p₁)
    (by rw [hc₁ e₂ p₂]; exact p₂) h), fun v hv w hw h => hf₁ hv hw (hf₂ (hvert v hv) (hvert w hw) h),
    by rw [hi₂, hi₁, Finset.image_image], by rw [hx₂, hx₁, Finset.image_image], hv₁,
    fun e he => by
      rw [Function.comp_apply, hc₂ _ (by rw [hc₁ e he]; exact he), hc₁ e he],
    fun e he => ?_, fun e'' he'' => ?_⟩
  · have p' : G'.cls (g₁ e) ≠ none := by rw [hc₁ e he]; exact he
    rcases he₁ e he with h | h <;> rcases he₂ _ p' with h' | h' <;>
      simp only [Function.comp_apply, h', h, Prod.mk.injEq, and_self, true_or, or_true]
  · refine hs₂ e'' fun e' he' hge => ?_
    by_contra hn
    have := hs₁ e' fun e he hgee => he'' e he (by rw [Function.comp_apply, hgee, hge])
    exact he' this

/-- Graphs with the same components in another order have the same molecular graph up to the
names of the edges. -/
private theorem TEqIdentity_tr_perm {k n : ℕ} {Γ Γ' : Graph k n} (h : Γ.comps.Perm Γ'.comps) :
    Γ.toMG'.Transported Γ'.toMG' := by
  classical
  obtain ⟨σ, hσ⟩ := TEqIdentity_perm_idx h
  have hσ' : ∀ i : Fin Γ.comps.length, Γ'.comps[(σ i : ℕ)]'(σ i).2 = Γ.comps[(i : ℕ)]'i.2 :=
    fun i => hσ i
  have hM : ∀ u v, Γ.SameMol u v ↔ Γ'.SameMol u v := by
    have : Γ.molGraph = Γ'.molGraph := by
      ext u v
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj, h.mem_iff]
    intro u v
    simp only [Graph.SameMol, this]
  have hB : ∀ u v, Γ.SameBlock u v ↔ Γ'.SameBlock u v := by
    have : Γ.dotGraph = Γ'.dotGraph := by
      ext u v
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, h.mem_iff]
    intro u v
    simp only [Graph.SameBlock, this]
  have hrep : ∀ u, Γ.molRep u = Γ'.molRep u := SelRunIso_molRep_congr hM
  have hanc : ∀ u, Γ.anchor u = Γ'.anchor u := SelRunIso_anchor_congr hB
  have hflat : ∀ c, Γ.flatComp c = Γ'.flatComp c := by
    intro c
    unfold Graph.flatComp
    rw [SelRunIso_flatAtom_congr hB, SelRunIso_flatAtom_congr hB]
  let g : Fin Γ.comps.length ⊕ Fin k → Fin Γ'.comps.length ⊕ Fin k := Sum.map σ id
  have hcls : ∀ e, Γ'.toMG'.cls (g e) = Γ.toMG'.cls e := by
    rintro (i | a)
    · simp only [g, Sum.map_inl, Graph.toMG', Fin.getElem_fin, hσ' i, hflat, hrep]
    · simp only [g, Sum.map_inr, id, Graph.toMG', hanc]
  have hends : ∀ e, Γ'.toMG'.ends (g e) = Γ.toMG'.ends e := by
    rintro (i | a)
    · simp only [g, Sum.map_inl, Graph.toMG', Fin.getElem_fin, hσ' i, hflat, hrep]
    · simp only [g, Sum.map_inr, id, Graph.toMG', hanc, hrep]
  refine ⟨id, g, fun e₁ e₂ _ _ he => Sum.map_injective.2 ⟨σ.injective, Function.injective_id⟩ he,
    Set.injOn_id _, ?_, ?_, fun e he => ?_, fun e _ => hcls e,
    fun e _ => Or.inl (by rw [hends e]; rfl), fun e' he' => ?_⟩
  · rw [Finset.image_id]
    ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and, hrep]
  · rw [Finset.image_id]
    rfl
  · rcases e with i | a
    · exact ⟨MolMono_molRep_isVtx Γ _, MolMono_molRep_isVtx Γ _⟩
    · rcases hb : Γ.anchor (.inl a) with _ | b
      · exfalso; apply he; simp [Graph.toMG', hb]
      · have : Γ.toMG'.ends (.inr a) = (Γ.molRep (.inr b), .inl a) := by simp [Graph.toMG', hb]
        rw [this]
        exact ⟨MolMono_molRep_isVtx Γ (.inr b), Or.inr ((MolMono_mem_ext Γ _).2 ⟨a, rfl⟩)⟩
  · have he := he' (Sum.map σ.symm id e')
    rcases e' with j | a
    · have : g (Sum.map σ.symm id (.inl j)) = .inl j := by simp [g]
      by_contra hc
      exact he (by rw [← hcls, this]; exact hc) this
    · have : g (Sum.map σ.symm id (.inr a)) = .inr a := by simp [g]
      by_contra hc
      exact he (by rw [← hcls, this]; exact hc) this

end Transport

/-! ## The correction graphs read against their output graph -/

section Core

variable {N M m : ℕ} (x y α : Fin N) (e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α})
  (ψ : Atom 2 m → Atom 3 M)

/-- The new internal atom `α'` of a correction graph: the atom `α` of the substituted term. -/
abbrev TEqIdentity_αc : Atom 3 (M + 1) := .inr (Fin.natAdd M 0)

/-- The atom of the host `Θ_{⊗x} 𝒮_{xy}` at an internal atom of the output graph other than `α`:
`x`, `y` and `e j` go to the images under `ψ` of the atoms `0`, `1`, `j` of `𝒮`. -/
private def TEqIdentity_Λ (a : Fin N) : Atom 3 M :=
  if a = x then ψ (.inl 0) else if a = y then ψ (.inl 1) else
    if h : a ≠ x ∧ a ≠ y ∧ a ≠ α then ψ (.inr (e.symm ⟨a, h⟩)) else ψ (.inl 0)

/-- The atom map from an output graph to its correction graph: the external atoms are kept,
`α` goes to the new atom `α'` and the other internal atoms to the host. -/
private def TEqIdentity_Λc : Atom 3 N → Atom 3 (M + 1) :=
  Sum.elim .inl fun a => if a = α then TEqIdentity_αc else liftA 1 (TEqIdentity_Λ x y α e ψ a)

/-- The atom map of the leaf form. -/
private abbrev TEqIdentity_φ : Atom 2 m → Atom 3 N :=
  Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1

variable {x y α e ψ}

/-- The atom map from the output graph to the correction graph extends the atom map of the host. -/
private theorem TEqIdentity_Λc_φ (hαx : α ≠ x) (hαy : α ≠ y)
    (h01 : x = y → ψ (.inl 0) = ψ (.inl 1)) (w : Atom 2 m) :
    TEqIdentity_Λc x y α e ψ (TEqIdentity_φ x y α e w) = liftA 1 (ψ w) := by
  rcases w with i | j
  · fin_cases i
    · simp [TEqIdentity_Λc, TEqIdentity_φ, TEqIdentity_Λ, Ne.symm hαx]
    · by_cases hxy : x = y
      · subst hxy
        simp [TEqIdentity_Λc, TEqIdentity_φ, TEqIdentity_Λ, Ne.symm hαy, h01 rfl]
      · simp [TEqIdentity_Λc, TEqIdentity_φ, TEqIdentity_Λ, Ne.symm hαy, Ne.symm hxy]
  · have hj := (e j).2
    simp only [TEqIdentity_Λc, TEqIdentity_φ, Sum.elim_inr, hj.2.2, hj.1, hj.2.1,
      ite_false, TEqIdentity_Λ]
    rw [dif_pos hj]
    simp

/-- The image of `α`. -/
private theorem TEqIdentity_Λc_α : TEqIdentity_Λc x y α e ψ (.inr α) = TEqIdentity_αc := by
  simp [TEqIdentity_Λc]

/-- The atom map keeps the external atoms. -/
private theorem TEqIdentity_Λc_inl (a : Fin 3) :
    TEqIdentity_Λc x y α e ψ (.inl a) = .inl a := rfl

/-- The atom map sends an internal atom other than `α` to an atom of the host. -/
private theorem TEqIdentity_Λc_ne {a : Fin N} (ha : a ≠ α) :
    TEqIdentity_Λc x y α e ψ (.inr a) = liftA 1 (TEqIdentity_Λ x y α e ψ a) := by
  simp [TEqIdentity_Λc, ha]

/-- An internal atom of the host is not the new atom. -/
private theorem TEqIdentity_lift_ne_αc {w : Atom 3 M} (hw : w.isRight = true) :
    liftA 1 w ≠ TEqIdentity_αc := by
  rcases w with a | k
  · simp at hw
  · intro h
    simp only [liftA, Sum.map_inr, TEqIdentity_αc, Sum.inr.injEq, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd] at h
    have := k.2
    omega

/-- **The atom map is injective**, given that `ψ` is injective but for `0, 1 ↦ x` at `x = y`. -/
private theorem TEqIdentity_Λc_inj (hαx : α ≠ x) (hαy : α ≠ y)
    (hψR : ∀ w, (ψ w).isRight = true) (h01 : ψ (.inl 0) = ψ (.inl 1) ↔ x = y)
    (hinj : ∀ j j', ψ (.inr j) = ψ (.inr j') → j = j') (hne : ∀ j i, ψ (.inr j) ≠ ψ (.inl i)) :
    Function.Injective (TEqIdentity_Λc x y α e ψ) := by
  have hL : ∀ a b : Fin N, a ≠ α → b ≠ α → TEqIdentity_Λ x y α e ψ a = TEqIdentity_Λ x y α e ψ b →
      a = b := by
    have key : ∀ a : Fin N, a ≠ α → (a = x ∧ TEqIdentity_Λ x y α e ψ a = ψ (.inl 0)) ∨
        (a ≠ x ∧ a = y ∧ TEqIdentity_Λ x y α e ψ a = ψ (.inl 1)) ∨
        ∃ h : a ≠ x ∧ a ≠ y ∧ a ≠ α, TEqIdentity_Λ x y α e ψ a = ψ (.inr (e.symm ⟨a, h⟩)) := by
      intro a ha
      by_cases h1 : a = x
      · exact Or.inl ⟨h1, by simp [TEqIdentity_Λ, h1]⟩
      by_cases h2 : a = y
      · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
        subst h2
        simp [TEqIdentity_Λ, h1]
      · exact Or.inr (Or.inr ⟨⟨h1, h2, ha⟩, by simp [TEqIdentity_Λ, h1, h2, ha]⟩)
    intro a b ha hb hab
    rcases key a ha with ⟨h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases key b hb with ⟨h1', h2'⟩ | ⟨h0', h1', h2'⟩ | ⟨h1', h2'⟩ <;> rw [h2, h2'] at hab
    · rw [h1, h1']
    · exact absurd (h01.1 hab) (fun hxy => h0' (h1'.trans hxy.symm))
    · exact absurd hab.symm (hne _ _)
    · exact absurd (h01.1 hab.symm) (fun hxy => h0 (h1.trans hxy.symm))
    · rw [h1, h1']
    · exact absurd hab.symm (hne _ _)
    · exact absurd hab (hne _ _)
    · exact absurd hab (hne _ _)
    · have := congrArg Subtype.val (e.symm.injective (hinj _ _ hab))
      exact this
  have hΛR : ∀ b, ∃ k, TEqIdentity_Λ x y α e ψ b = .inr k := by
    intro b
    have : (TEqIdentity_Λ x y α e ψ b).isRight = true := by
      unfold TEqIdentity_Λ; split_ifs <;> exact hψR _
    rcases h : TEqIdentity_Λ x y α e ψ b with c | k
    · rw [h] at this; simp at this
    · exact ⟨k, rfl⟩
  rintro (a | a) (b | b) hab
  · simp only [TEqIdentity_Λc_inl, Sum.inl.injEq] at hab
    rw [hab]
  · simp only [TEqIdentity_Λc, Sum.elim_inl, Sum.elim_inr] at hab
    obtain ⟨k, hk⟩ := hΛR b
    split_ifs at hab <;> simp [liftA, hk] at hab
  · simp only [TEqIdentity_Λc, Sum.elim_inl, Sum.elim_inr] at hab
    obtain ⟨k, hk⟩ := hΛR a
    split_ifs at hab <;> simp [liftA, hk] at hab
  · by_cases ha : a = α <;> by_cases hb : b = α
    · rw [ha, hb]
    · rw [ha, TEqIdentity_Λc_α, TEqIdentity_Λc_ne hb] at hab
      have hR : (TEqIdentity_Λ x y α e ψ b).isRight = true := by
        unfold TEqIdentity_Λ; split_ifs <;> exact hψR _
      exact absurd hab.symm (TEqIdentity_lift_ne_αc hR)
    · rw [hb, TEqIdentity_Λc_α, TEqIdentity_Λc_ne ha] at hab
      have hR : (TEqIdentity_Λ x y α e ψ a).isRight = true := by
        unfold TEqIdentity_Λ; split_ifs <;> exact hψR _
      exact absurd hab (TEqIdentity_lift_ne_αc hR)
    · rw [TEqIdentity_Λc_ne ha, TEqIdentity_Λc_ne hb] at hab
      exact congrArg Sum.inr (hL a b ha hb (Sum.map_injective.2 ⟨Function.injective_id,
        Fin.castAdd_injective _ _⟩ hab))

end Core

/-- Two maps of the atoms of a component compose. -/
private theorem TEqIdentity_map_map {V W Z : Type*} (f : V → W) (g : W → Z) (c : Comp V) :
    (c.map f).map g = c.map (g ∘ f) := by
  obtain ⟨κ, u, v, T, ℓ⟩ := c
  simp only [Comp.map, List.map_map, Option.map_map]
  rfl

/-- A component without minor and label read through a map of the atoms. -/
private theorem TEqIdentity_mkC_map {V W : Type*} (f : V → W) (κ : Kind) (u v : V) :
    (mkC κ u v).map f = mkC κ (f u) (f v) := rfl

/-- **The components of a correction graph** ([II, (4.15)] substituted into `Θ_{⊗x} 𝒮_{xy}`): the
image under the atom map `TEqIdentity_Λc` of `Θ_{⊗x}` and of the components `R` of `𝒮` read in
the output graph, the `ℓ` `×`-dotted loops at `x`, and the recollision term at `y`, `α'`. -/
private theorem TEqIdentity_corr_perm {N M m : ℕ} {x y α : Fin N}
    {e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}} {ψ : Atom 2 m → Atom 3 M}
    (hαx : α ≠ x) (hαy : α ≠ y) (h01 : x = y → ψ (.inl 0) = ψ (.inl 1))
    {R Hc : List (Comp (Atom 2 m))} {ℓ : ℕ}
    (hHc : Hc.Perm (R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))))
    (τc : List (Comp (Atom 3 1))) :
    (liftCs 1 (mkC (.theta []) (.inl 0) (ψ (.inl 0)) :: Hc.map (Comp.map ψ)) ++
        τc.map (Comp.map (glueAtom (ψ (.inl 1)) (.inl 1) (.inl 2)))).Perm
      ((mkC (.theta []) (.inl 0) (.inr x) :: R.map (Comp.map (TEqIdentity_φ x y α e))).map
          (Comp.map (TEqIdentity_Λc x y α e ψ)) ++
        (List.replicate ℓ (mkC .xdot (liftA 1 (ψ (.inl 0))) (liftA 1 (ψ (.inl 0)))) ++
          τc.map (Comp.map (glueAtom (ψ (.inl 1)) (.inl 1) (.inl 2))))) := by
  have hΘ : (mkC (.theta []) (.inl 0) (ψ (.inl 0))).map (liftA 1) =
      (mkC (.theta []) (.inl 0) (.inr x)).map (TEqIdentity_Λc x y α e ψ) := by
    rw [TEqIdentity_mkC_map, TEqIdentity_mkC_map, TEqIdentity_Λc_inl]
    have := TEqIdentity_Λc_φ (e := e) hαx hαy h01 (.inl 0)
    simp only [TEqIdentity_φ, Sum.elim_inl, Matrix.cons_val_zero] at this
    rw [this]
    rfl
  have hR : R.map (Comp.map (liftA 1 ∘ ψ)) =
      (R.map (Comp.map (TEqIdentity_φ x y α e))).map (Comp.map (TEqIdentity_Λc x y α e ψ)) := by
    rw [List.map_map]
    refine List.map_congr_left fun r _ => ?_
    rw [Function.comp_apply, TEqIdentity_map_map]
    congr 1
    funext w
    exact (TEqIdentity_Λc_φ hαx hαy h01 w).symm
  unfold liftCs
  rw [List.map_cons, List.map_map, hΘ, List.map_cons, List.cons_append, List.cons_append]
  refine List.Perm.cons _ ?_
  have h1 : (Hc.map (Comp.map (liftA 1) ∘ Comp.map ψ)).Perm
      (R.map (Comp.map (liftA 1 ∘ ψ)) ++
        List.replicate ℓ (mkC .xdot (liftA 1 (ψ (.inl 0))) (liftA 1 (ψ (.inl 0))))) := by
    have := hHc.map (Comp.map (liftA 1 ∘ ψ))
    rw [List.map_append, List.map_replicate, TEqIdentity_mkC_map] at this
    refine List.Perm.trans ?_ this
    have he : (Comp.map (liftA 1) ∘ Comp.map ψ : Comp (Atom 2 m) → Comp (Atom 3 (M + 1))) =
        Comp.map (liftA 1 ∘ ψ) := funext fun c => TEqIdentity_map_map ψ (liftA 1) c
    rw [he]
  rw [← List.append_assoc]
  refine List.Perm.append_right _ ?_
  rw [← hR]
  exact h1

/-! ## The clauses of a correction graph -/

section CorrGraph

/-- The equivalence generated by dotted edges joins only atoms with a property `P` shared by the
two ends of every dotted edge. -/
private theorem TEqIdentity_eqvGen {V : Type*} [DecidableEq V] {L : List (Comp V)} {P : V → Prop}
    (hP : ∀ d ∈ L, d.kind = .dot → P d.x ∧ P d.y) {u v : V}
    (h : Relation.EqvGen (dotRel L) u v) : u = v ∨ (P u ∧ P v) := by
  induction h with
  | rel a b hab =>
    obtain ⟨d, hd, hk, rfl, rfl⟩ := hab
    exact Or.inr (hP d hd hk)
  | refl => exact Or.inl rfl
  | symm a b _ ih =>
    rcases ih with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h.2, h.1⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with rfl | h1
    · exact ih2
    rcases ih2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr ⟨h1.1, h2.2⟩

/-- The three recollision terms substituted at `y`, `⊕`, `⊖`. -/
private theorem TEqIdentity_tauhat {M : ℕ} (yh : Atom 3 M) :
    (TEqIdentity_T1.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) : List (Comp (Atom 3 (M + 1)))) =
      [mkC (.waved .s) (liftA 1 yh) TEqIdentity_αc, mkC (.weight .plus) TEqIdentity_αc TEqIdentity_αc,
        mkC (.G .minus) TEqIdentity_αc (.inl 2), mkC .dot TEqIdentity_αc (.inl 1),
        mkC .xdot TEqIdentity_αc (.inl 2)] ∧
    (TEqIdentity_T2.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) : List (Comp (Atom 3 (M + 1)))) =
      [mkC (.waved .s) (liftA 1 yh) TEqIdentity_αc, mkC (.G .plus) TEqIdentity_αc (.inl 1),
        mkC (.weight .minus) TEqIdentity_αc TEqIdentity_αc, mkC .xdot TEqIdentity_αc (.inl 1),
        mkC .dot TEqIdentity_αc (.inl 2)] ∧
    (TEqIdentity_T3.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) : List (Comp (Atom 3 (M + 1)))) =
      [mkC (.waved .s) (liftA 1 yh) TEqIdentity_αc, mkC (.weight .plus) TEqIdentity_αc TEqIdentity_αc,
        mkC (.weight .minus) TEqIdentity_αc TEqIdentity_αc, mkC .dot TEqIdentity_αc (.inl 1),
        mkC .dot TEqIdentity_αc (.inl 2)] :=
  ⟨rfl, rfl, rfl⟩

variable {M : ℕ} {Γc : Graph 3 (M + 1)} {A' : List (Comp (Atom 3 (M + 1)))}
  {xh : Atom 3 (M + 1)} {yh : Atom 3 M} {ℓ : ℕ} {τc : List (Comp (Atom 3 1))}

/-- A component of a correction graph: in the image of `Θ_{⊗x}` and of the components of `𝒮`, a
`×`-dotted loop at `x`, or a component of the recollision term. -/
private theorem TEqIdentity_mem
    (hc0 : Γc.comps.Perm (A' ++ (List.replicate ℓ (mkC .xdot xh xh) ++
      τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2)))))) (d : Comp (Atom 3 (M + 1))) :
    d ∈ Γc.comps ↔ d ∈ A' ∨ (d = mkC .xdot xh xh ∧ 0 < ℓ) ∨
      d ∈ τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) := by
  rw [hc0.mem_iff, List.mem_append, List.mem_append, List.mem_replicate]
  constructor
  · rintro (h | ⟨h1, h2⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h2, by omega⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨h1, h2⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨by omega, h1⟩)
    · exact Or.inr (Or.inr h)

variable (hc0 : Γc.comps.Perm (A' ++ (List.replicate ℓ (mkC .xdot xh xh) ++
    τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))))))
  (hA' : ∀ d ∈ A', d = mkC (.theta []) (.inl 0) xh ∨
    (d.x.isRight = true ∧ d.y.isRight = true ∧ d.x ≠ TEqIdentity_αc ∧ d.y ≠ TEqIdentity_αc ∧
      d.kind ≠ .dot))
  (hxh : xh.isRight = true ∧ xh ≠ TEqIdentity_αc) (hyh : yh.isRight = true)
  (hτc : τc = TEqIdentity_T1 ∨ τc = TEqIdentity_T2 ∨ τc = TEqIdentity_T3)
include hc0 hA' hxh hyh hτc

/-- The dotted edges of a correction graph join the new atom `α'` to `⊕` or `⊖`. -/
private theorem TEqIdentity_dots :
    ∀ d ∈ Γc.comps, d.kind = .dot → d.x = TEqIdentity_αc ∧
      ∃ a : Fin 3, d.y = .inl a ∧ a ≠ 0 ∧ mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps := by
  intro d hd hk
  have hmem := TEqIdentity_mem hc0
  rcases (hmem d).1 hd with h | ⟨rfl, -⟩ | h
  · rcases hA' d h with rfl | h'
    · cases hk
    · exact absurd hk h'.2.2.2.2
  · cases hk
  · have hd' := hd
    obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
    rcases hτc with rfl | rfl | rfl
    · rw [t1] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp_all [mkC]
    · rw [t2] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp_all [mkC]
    · rw [t3] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp_all [mkC]

/-- The blocks of a correction graph: `α'` with the external atoms joined to it by a dotted edge,
and single atoms. -/
private theorem TEqIdentity_blocks {u v : Atom 3 (M + 1)} (h : Γc.SameBlock u v) :
    u = v ∨ ((u = TEqIdentity_αc ∨ ∃ a, u = .inl a ∧ mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps) ∧
      (v = TEqIdentity_αc ∨ ∃ a, v = .inl a ∧ mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps)) := by
  rw [Graph.sameBlock_iff_eqvGen] at h
  refine TEqIdentity_eqvGen (P := fun w => w = TEqIdentity_αc ∨
    ∃ a, w = .inl a ∧ mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps) (fun d hd hk => ?_) h
  obtain ⟨hx, a, hy, -, ha⟩ := TEqIdentity_dots hc0 hA' hxh hyh hτc d hd hk
  exact ⟨Or.inl hx, Or.inr ⟨a, hy, ha⟩⟩

omit hc0 hA' hxh hyh hτc in
/-- An external atom joined to `α'` by a dotted edge lies in its block. -/
private theorem TEqIdentity_pin_block {a : Fin 3}
    (ha : mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps) :
    Γc.SameBlock (.inl a) TEqIdentity_αc := by
  refine SimpleGraph.Adj.reachable ?_
  rw [Graph.dotGraph, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inr ⟨_, ha, rfl, rfl, rfl⟩⟩

/-- An external atom not joined to `α'` by a dotted edge is unpinned. -/
private theorem TEqIdentity_unpinned {a : Fin 3}
    (ha : mkC .dot TEqIdentity_αc (.inl a) ∉ Γc.comps) : Γc.Unpinned (.inl a) := by
  refine ⟨rfl, fun b hb => ?_⟩
  rcases TEqIdentity_blocks hc0 hA' hxh hyh hτc hb with h | ⟨h | ⟨a', h1, h2⟩, -⟩
  · cases h
  · cases h
  · cases h1
    exact ha h2

/-- The anchor of an external atom joined to `α'` by a dotted edge is `α'`. -/
private theorem TEqIdentity_anchor_pin {a : Fin 3}
    (ha : mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps) : Γc.anchor (.inl a) = some (Fin.natAdd M 0) := by
  classical
  rw [MolMono_anchor_eq_find]
  rcases hf : (List.finRange (M + 1)).find? (fun b => decide (Γc.SameBlock (.inl a) (.inr b)))
    with _ | b
  · rw [List.find?_eq_none] at hf
    exact absurd (TEqIdentity_pin_block ha) (by simpa using hf _ (List.mem_finRange _))
  · have hb := List.find?_some hf
    rw [decide_eq_true_eq] at hb
    rcases TEqIdentity_blocks hc0 hA' hxh hyh hτc hb with h | ⟨-, h | ⟨a', h1, -⟩⟩
    · cases h
    · simp only [TEqIdentity_αc, Sum.inr.injEq] at h
      rw [h]
    · cases h1

omit hc0 hA' hxh hyh hτc in
/-- The anchor of an unpinned atom is `none`. -/
private theorem TEqIdentity_anchor_none {Γ : Graph 3 (M + 1)} {a : Fin 3}
    (ha : Γ.Unpinned (.inl a)) : Γ.anchor (.inl a) = none := by
  classical
  rw [MolMono_anchor_eq_find, List.find?_eq_none]
  intro b _
  simpa using ha.2 b

/-- A dotted edge from `α'` to an external atom is a component of the recollision term. -/
private theorem TEqIdentity_pin_iff (a : Fin 3) :
    mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps ↔
      mkC .dot TEqIdentity_αc (.inl a) ∈ τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) := by
  rw [TEqIdentity_mem hc0]
  constructor
  · rintro (h | ⟨h, -⟩ | h)
    · rcases hA' _ h with h' | h'
      · simp [mkC] at h'
      · exact absurd rfl h'.2.2.2.2
    · simp [mkC] at h
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- The components of a correction graph at an external atom: `Θ_{⊗x}` and components of the
recollision term. -/
private theorem TEqIdentity_at_ext : ∀ d ∈ Γc.comps, ∀ a : Fin 3, (d.x = .inl a ∨ d.y = .inl a) →
    d = mkC (.theta []) (.inl 0) xh ∨ d ∈ τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) := by
  intro d hd a ha
  rcases (TEqIdentity_mem hc0 d).1 hd with h | ⟨rfl, -⟩ | h
  · rcases hA' d h with h' | h'
    · exact Or.inl h'
    · rcases ha with ha | ha <;> simp [ha] at h'
  · rcases ha with ha | ha <;> simp only [mkC] at ha <;> rw [ha] at hxh <;> simp at hxh
  · exact Or.inr h

/-- The ends at external atoms of the components of a correction graph other than dotted edges
are unpinned. -/
private theorem TEqIdentity_nondot_unpinned : ∀ d ∈ Γc.comps, d.kind ≠ .dot → ∀ a : Fin 3,
    (d.x = .inl a ∨ d.y = .inl a) → Γc.Unpinned (.inl a) := by
  intro d hd hk a ha
  refine TEqIdentity_unpinned hc0 hA' hxh hyh hτc fun hp => ?_
  rw [TEqIdentity_pin_iff hc0 hA' hxh hyh hτc] at hp
  rcases TEqIdentity_at_ext hc0 hA' hxh hyh hτc d hd a ha with rfl | h
  · rcases ha with ha | ha
    · simp only [mkC, Sum.inl.injEq] at ha
      subst ha
      obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
      rcases hτc with rfl | rfl | rfl
      · rw [t1] at hp; simp [mkC] at hp
      · rw [t2] at hp; simp [mkC] at hp
      · rw [t3] at hp; simp [mkC] at hp
    · simp only [mkC] at ha
      rw [ha] at hxh
      simp at hxh
  · obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
    have hyl : ∀ a : Fin 3, (liftA 1 yh : Atom 3 (M + 1)) ≠ .inl a := by
      intro a h
      rcases yh with _ | _
      · simp at hyh
      · simp [liftA] at h
    rcases hτc with rfl | rfl | rfl
    · rw [t1] at hp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        rcases ha with ha | ha <;> simp [mkC] at ha hk hp <;> simp_all
    · rw [t2] at hp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        rcases ha with ha | ha <;> simp [mkC] at ha hk hp <;> simp_all
    · rw [t3] at hp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        rcases ha with ha | ha <;> simp [mkC] at ha hk hp <;> simp_all

/-- The block normal form of a correction graph is the graph itself. -/
private theorem TEqIdentity_flatComp : ∀ d ∈ Γc.comps, Γc.flatComp d = d := by
  intro d hd
  unfold Graph.flatComp
  split_ifs with hk
  · rfl
  · have hf : ∀ w, (w = d.x ∨ w = d.y) → Γc.flatAtom w = w := by
      intro w hw
      rcases w with a | b
      · have hu := TEqIdentity_nondot_unpinned hc0 hA' hxh hyh hτc d hd hk a
          (by rcases hw with hw | hw <;> [exact Or.inl hw.symm; exact Or.inr hw.symm])
        simp [Graph.flatAtom, TEqIdentity_anchor_none hu]
      · rfl
    rw [hf _ (Or.inl rfl), hf _ (Or.inr rfl)]

/-- **The charge pattern of the block normal form of a correction graph** (`Graph.ColourInvB`). -/
private theorem TEqIdentity_colourInvB : Γc.ColourInvB := by
  have hb : Γc.blockNorm = Γc := by
    obtain ⟨cs, co⟩ := Γc
    simp only [Graph.blockNorm]
    congr 1
    exact (List.map_congr_left (TEqIdentity_flatComp hc0 hA' hxh hyh hτc)).trans (List.map_id _)
  unfold Graph.ColourInvB
  rw [hb]
  intro d hd
  have hy : (liftA 1 yh : Atom 3 (M + 1)).isRight = true := by
    rcases yh with _ | _
    · simp at hyh
    · rfl
  rcases (TEqIdentity_mem hc0 d).1 hd with h | ⟨rfl, -⟩ | h
  · rcases hA' d h with rfl | ⟨h1, h2, -, -, -⟩
    · simp [mkC, Kind.isRandom]
    · refine ⟨fun _ => ⟨h1, fun h => by simp [h] at h2, fun h => by simp [h] at h2,
        fun h => by simp [h] at h2⟩, fun _ => ⟨h1, h2⟩⟩
  · simp [mkC, Kind.isRandom]
  · obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
    rcases hτc with rfl | rfl | rfl
    · rw [t1] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [mkC, Kind.isRandom, hy]
    · rw [t2] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [mkC, Kind.isRandom, hy]
    · rw [t3] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [mkC, Kind.isRandom, hy]

omit hyh hτc in
/-- A count of components with a property that no component of the host part has. -/
private theorem TEqIdentity_count (p : Comp (Atom 3 (M + 1)) → Bool)
    (hp : ∀ d, d.x.isRight = true → d.y.isRight = true → p d = false)
    (hp0 : p (mkC (.theta []) (.inl 0) xh) = false) :
    (Γc.comps.filter p).length = ((τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2)))).filter p).length := by
  rw [(hc0.filter p).length_eq, List.filter_append, List.filter_append, List.length_append,
    List.length_append]
  have h1 : A'.filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    rcases hA' d hd with rfl | ⟨h1, h2, -⟩
    · simp [hp0]
    · simp [hp d h1 h2]
  have h2 : (List.replicate ℓ (mkC .xdot xh xh)).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    rw [List.eq_of_mem_replicate hd]
    simp [hp (mkC .xdot xh xh) hxh.1 hxh.1]
  rw [h1, h2]
  simp

/-- Only diffusive edges at `⊗` (`Graph.TensorDiffusive`). -/
private theorem TEqIdentity_td : Γc.TensorDiffusive := by
  unfold Graph.TensorDiffusive
  rw [List.all_eq_true]
  intro d hd
  by_cases h0 : d.x = .inl 0 ∨ d.y = .inl 0
  · rcases TEqIdentity_at_ext hc0 hA' hxh hyh hτc d hd 0 h0 with rfl | h
    · simp [mkC, Kind.isDiffusive]
    · have hyl : (liftA 1 yh : Atom 3 (M + 1)) ≠ .inl 0 := by
        intro h'
        rcases yh with _ | _
        · simp at hyh
        · simp [liftA] at h'
      obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
      rcases hτc with rfl | rfl | rfl
      · rw [t1] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [mkC] at h0 <;> exact absurd h0 hyl
      · rw [t2] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [mkC] at h0 <;> exact absurd h0 hyl
      · rw [t3] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [mkC] at h0 <;> exact absurd h0 hyl
  · simp only [not_or] at h0
    simp [h0.1, h0.2]

omit hc0 hA' hxh hyh hτc in
/-- The dot excess of the empty list. -/
private theorem TEqIdentity_excL_nil : excL ([] : List (Comp (Atom 3 (M + 1)))) = 0 := by
  unfold excL nDotL
  rw [nBlk_nil]
  simp

omit hc0 hA' hxh hyh hτc in
/-- A dotted edge whose ends are not joined by the other dotted edges keeps the dot excess. -/
private theorem TEqIdentity_excL_out (L : List (Comp (Atom 3 (M + 1)))) (u v : Atom 3 (M + 1))
    (P : Atom 3 (M + 1) → Prop) (hP : ∀ d ∈ L, d.kind = .dot → P d.x ∧ P d.y) (huv : u ≠ v)
    (hu : ¬ P u ∨ ¬ P v) : excL (mkC .dot u v :: L) = excL L := by
  refine excL_cons_dot_out rfl L fun h => ?_
  rcases TEqIdentity_eqvGen hP h with h | ⟨h1, h2⟩
  · exact huv h
  · rcases hu with hu | hu
    · exact hu h1
    · exact hu h2

/-- The dotted edges form a forest (`Graph.dotExcess = 0`). -/
private theorem TEqIdentity_dotExcess : Γc.dotExcess = 0 := by
  rw [selStep2_dotExcess_eq, excL_perm hc0]
  rw [excL_append_nodot _ _ fun d hd => by
    rcases hA' d hd with rfl | h
    · simp [mkC]
    · exact h.2.2.2.2]
  rw [excL_append_nodot _ _ fun d hd => by rw [List.eq_of_mem_replicate hd]; simp [mkC]]
  have hne : ∀ a : Fin 3, (TEqIdentity_αc : Atom 3 (M + 1)) ≠ .inl a := by simp
  obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
  rcases hτc with rfl | rfl | rfl
  · rw [t1, excL_cons_ne (by simp [mkC]), excL_cons_ne (by simp [mkC]), excL_cons_ne (by simp [mkC]),
      TEqIdentity_excL_out _ _ _ (fun _ => False) (by simp [mkC]) (hne 1) (Or.inl id),
      excL_cons_ne (by simp [mkC]), TEqIdentity_excL_nil]
  · rw [t2, excL_cons_ne (by simp [mkC]), excL_cons_ne (by simp [mkC]), excL_cons_ne (by simp [mkC]),
      excL_cons_ne (by simp [mkC]),
      TEqIdentity_excL_out _ _ _ (fun _ => False) (by simp) (hne 2) (Or.inl id),
      TEqIdentity_excL_nil]
  · rw [t3, excL_cons_ne (by simp [mkC]), excL_cons_ne (by simp [mkC]), excL_cons_ne (by simp [mkC]),
      TEqIdentity_excL_out _ _ _ (fun w => w = TEqIdentity_αc ∨ w = .inl 2) (by simp [mkC])
        (hne 1) (Or.inr (by simp)),
      TEqIdentity_excL_out _ _ _ (fun _ => False) (by simp) (hne 2) (Or.inl id),
      TEqIdentity_excL_nil]

/-- A dotted edge joins `α'` to `⊕` or to `⊖`. -/
private theorem TEqIdentity_pin_ex :
    ∃ a : Fin 3, (a = 1 ∨ a = 2) ∧ mkC .dot TEqIdentity_αc (.inl a) ∈ Γc.comps := by
  have hmem := TEqIdentity_mem hc0
  obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
  rcases hτc with rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, (hmem _).2 (Or.inr (Or.inr (by rw [t1]; simp)))⟩
  · exact ⟨2, Or.inr rfl, (hmem _).2 (Or.inr (Or.inr (by rw [t2]; simp)))⟩
  · exact ⟨1, Or.inl rfl, (hmem _).2 (Or.inr (Or.inr (by rw [t3]; simp)))⟩

/-- A correction graph is a `⊕/⊖`-recollision graph. -/
private theorem TEqIdentity_recoll : Γc.IsRecollision {1, 2} := by
  obtain ⟨a, ha, hm⟩ := TEqIdentity_pin_ex hc0 hA' hxh hyh hτc
  refine ⟨_, hm, rfl, Or.inr ⟨⟨a, by rcases ha with rfl | rfl <;> simp, rfl⟩, rfl⟩⟩

/-- The block of `⊕` or of `⊖` contains the internal atom `α'` (`Graph.DiagRecoll`). -/
private theorem TEqIdentity_diag : Γc.DiagRecoll := by
  obtain ⟨a, ha, hm⟩ := TEqIdentity_pin_ex hc0 hA' hxh hyh hτc
  obtain ⟨B, hB, h1, h2⟩ := (Γc.sameBlock_iff_mem_dotBlocks _ _).1 (TEqIdentity_pin_block hm)
  unfold Graph.DiagRecoll
  rw [List.any_eq_true]
  refine ⟨B, hB, ?_⟩
  have hc : (B.contains (.inl 1) || B.contains (.inl 2)) = true := by
    rcases ha with rfl | rfl <;> simp [List.contains_iff_mem, h1]
  rw [hc, Bool.true_and, List.any_eq_true]
  exact ⟨_, h2, rfl⟩

/-- **The clause on the external atoms of a correction graph** (`Graph.ExtClause`). -/
private theorem TEqIdentity_extClause (hΘA : mkC (.theta []) (.inl 0) xh ∈ A') : Γc.ExtClause := by
  have hmem := TEqIdentity_mem hc0
  have hint : ∀ w : Atom 3 (M + 1), w.isRight = true → ¬ Γc.Unpinned w := by
    intro w hw hu
    have := hu.1
    rcases w with _ | _ <;> simp_all
  have hyl : ∀ a : Fin 3, (liftA 1 yh : Atom 3 (M + 1)) ≠ .inl a := by
    intro a h
    rcases yh with _ | _
    · simp at hyh
    · simp [liftA] at h
  have hy : (liftA 1 yh : Atom 3 (M + 1)).isRight = true := by
    rcases yh with _ | _
    · simp at hyh
    · rfl
  obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
  -- the components of the recollision term are not diffusive and start at an internal atom
  have hτd : ∀ d ∈ τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))),
      d.kind.isDiffusive = false ∧ d.x.isRight = true := by
    rcases hτc with rfl | rfl | rfl
    · rw [t1]; simp [mkC, Kind.isDiffusive, hy]
    · rw [t2]; simp [mkC, Kind.isDiffusive, hy]
    · rw [t3]; simp [mkC, Kind.isDiffusive, hy]
  -- the diffusive edges at an external atom
  have hdiff : ∀ d ∈ Γc.comps, d.kind.isDiffusive = true → ∀ a : Fin 3,
      (d.x = .inl a ∨ d.y = .inl a) → d = mkC (.theta []) (.inl 0) xh := by
    intro d hd hk a ha
    rcases TEqIdentity_at_ext hc0 hA' hxh hyh hτc d hd a ha with h | h
    · exact h
    · rw [(hτd d h).1] at hk; cases hk
  have hΘm : mkC (.theta []) (.inl 0) xh ∈ Γc.comps := (hmem _).2 (Or.inl hΘA)
  have hxl : ∀ a : Fin 3, xh ≠ .inl a := by
    intro a h
    have := hxh.1
    rw [h] at this
    cases this
  -- at most one component other than dotted and `×`-dotted edges at `⊕` and at `⊖`
  have hdeg : ∀ a : Fin 3, a ≠ 0 → Γc.nonDotDeg (.inl a) ≤ 1 := by
    intro a ha0
    unfold Graph.nonDotDeg
    rw [TEqIdentity_count hc0 hA' hxh _ (fun d h1 h2 => by
        rcases hx : d.x with _ | _ <;> rcases hy' : d.y with _ | _ <;> simp_all)
      (by simp [mkC, Ne.symm ha0, hxl])]
    rcases hτc with rfl | rfl | rfl
    · rw [t1]
      fin_cases a <;> simp [mkC, hyl] at ha0 ⊢
    · rw [t2]
      fin_cases a <;> simp [mkC, hyl] at ha0 ⊢
    · rw [t3]
      fin_cases a <;> simp [mkC, hyl] at ha0 ⊢
  refine ⟨fun u v huv hb => ?_, fun d hd hk hu => ?_, fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, hdeg 2 (by simp)⟩,
    fun hU => ⟨?_, ?_, hdeg 1 (by simp)⟩⟩
  · rcases TEqIdentity_blocks hc0 hA' hxh hyh hτc hb with h | ⟨hu, -⟩
    · exact absurd h huv
    · refine ⟨Fin.natAdd M 0, ?_⟩
      rcases hu with rfl | ⟨a, rfl, ha⟩
      · exact SimpleGraph.Reachable.refl _
      · exact TEqIdentity_pin_block ha
  · rcases (hmem d).1 hd with h | ⟨rfl, -⟩ | h
    · rcases hA' d h with rfl | h'
      · cases hk
      · exact hint _ h'.1 hu.1
    · exact hint _ hxh.1 hu.1
    · exact hint _ (hτd d h).2 hu.1
  · exact ⟨_, hΘm, rfl, Or.inl ⟨rfl, hint _ hxh.1⟩⟩
  · intro d hd hk
    refine ⟨fun hx => ?_, fun hy' => ?_⟩
    · rw [hdiff d hd hk 0 (Or.inl hx)]
      exact hint _ hxh.1
    · rw [hdiff d hd hk 0 (Or.inr hy')] at hy'
      exact absurd hy' (hxl 0)
  · intro d hd hk
    refine ⟨fun hx => ?_, fun hy' => ?_⟩
    · rw [hdiff d hd hk 2 (Or.inl hx)] at hx
      simp [mkC] at hx
    · rw [hdiff d hd hk 2 (Or.inr hy')] at hy'
      exact hxl 2 hy'
  · rcases hτc with rfl | rfl | rfl
    · exact absurd (TEqIdentity_pin_block ((hmem _).2 (Or.inr (Or.inr (by rw [t1]; simp)))))
        (hU.2 _)
    · exact Or.inl ⟨mkC (.G .plus) TEqIdentity_αc (.inl 1),
        (hmem _).2 (Or.inr (Or.inr (by rw [t2]; simp))), rfl, Or.inr rfl⟩
    · exact absurd (TEqIdentity_pin_block ((hmem _).2 (Or.inr (Or.inr (by rw [t3]; simp)))))
        (hU.2 _)
  · intro d hd hk
    refine ⟨fun hx => ?_, fun hy' => ?_⟩
    · rw [hdiff d hd hk 1 (Or.inl hx)] at hx
      simp [mkC] at hx
    · rw [hdiff d hd hk 1 (Or.inr hy')] at hy'
      exact absurd hy' (hxl 1)

end CorrGraph

/-! ## The molecular graph of a correction graph -/

section MolTransport

/-- Atoms of one molecule have the same representative. -/
private theorem TEqIdentity_molRep_of_sameMol {k n : ℕ} {Γ : Graph k n} {u v : Atom k n}
    (h : Γ.SameMol u v) : Γ.molRep u = Γ.molRep v := by
  rcases h with rfl | ⟨hu, hv, h⟩
  · rfl
  · rcases u with a | a
    · simp at hu
    rcases v with b | b
    · simp at hv
    exact (MolMono_molRep_eq_iff Γ a b).2 (Or.inr ⟨rfl, rfl, h⟩)

/-- Atoms with the same representative lie in one molecule. -/
private theorem TEqIdentity_sameMol_of_molRep {k n : ℕ} {Γ : Graph k n} {u v : Atom k n}
    (h : Γ.molRep u = Γ.molRep v) : Γ.SameMol u v := by
  rcases u with a | a <;> rcases v with b | b
  · exact Or.inl h
  · obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ b
    rw [hc] at h
    cases h
  · obtain ⟨c, hc, -⟩ := MolMono_molRep_inr Γ a
    rw [hc] at h
    cases h
  · exact (MolMono_molRep_eq_iff Γ a b).1 h

/-- Reachability is carried by a map sending each edge to two reachable vertices. -/
private theorem TEqIdentity_reach_map {V W : Type*} {r : V → V → Prop} {r' : W → W → Prop}
    (F : V → W) (hF : ∀ a b, r a b → (SimpleGraph.fromRel r').Reachable (F a) (F b)) {u v : V}
    (h : (SimpleGraph.fromRel r).Reachable u v) : (SimpleGraph.fromRel r').Reachable (F u) (F v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab _ ih =>
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h | h
    · exact (hF a b h).trans ih
    · exact (hF b a h).symm.trans ih

/-- In a graph without dotted edges every component is its own block normal form and no external
atom has an anchor. -/
private theorem TEqIdentity_dotFree_flat {k n : ℕ} {Γ : Graph k n}
    (hd : ∀ c ∈ Γ.comps, c.kind ≠ .dot) :
    (∀ a : Fin k, Γ.anchor (.inl a) = none) ∧ ∀ c, Γ.flatComp c = c := by
  classical
  have hB : ∀ u v, Γ.SameBlock u v ↔ u = v :=
    Graph.sameBlock_iff_eq Γ fun c hc hk => absurd hk (hd c hc)
  have han : ∀ a : Fin k, Γ.anchor (.inl a) = none := by
    intro a
    rw [MolMono_anchor_eq_find, List.find?_eq_none]
    intro b _
    simp [hB]
  refine ⟨han, fun c => ?_⟩
  unfold Graph.flatComp
  split_ifs
  · rfl
  · have hf : ∀ w, Γ.flatAtom w = w := by
      rintro (a | b)
      · simp [Graph.flatAtom, han]
      · rfl
    rw [hf, hf]

/-- A position in the middle part of a list `L₀ ++ A ++ B`. -/
private theorem TEqIdentity_idx {β : Type*} (L₀ A B : List β) (j : ℕ) (h1 : L₀.length ≤ j)
    (h2 : j < L₀.length + A.length) (h : j < (L₀ ++ A ++ B).length) :
    (L₀ ++ A ++ B)[j] = A[j - L₀.length]'(by omega) := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right h1]

/-- **The molecular graph of a correction graph is that of its output graph, up to names**
([II, Def 2.11] in the block reading): the output graph `Γ₀` lists `s_{yα}`, `G_{α⊕}`, `Ḡ_{α⊖}`,
the components `A` and `×`-dotted edges; the correction graph `Γ₁` lists the recollision term `τh`
at `y`, `α'`, the images of `A` under an injective atom map `Λc` with `Λc α = α'`, and `×`-dotted
edges. The edges `G_{α⊕}` and `Ḡ_{α⊖}` of `Γ₀` go to the edges `eP`, `eM` of `Γ₁` (a solid edge at
`α'` or the edge from the molecule of `α'` to an identified external atom). -/
private theorem TEqIdentity_tr_core {N M : ℕ} {Γ₀ : Graph 3 N} {Γ₁ : Graph 3 (M + 1)}
    {A Bt : List (Comp (Atom 3 N))} {sy : Comp (Atom 3 N)} {τh Lt : List (Comp (Atom 3 (M + 1)))}
    {Λc : Atom 3 N → Atom 3 (M + 1)} {α y : Fin N}
    (h0 : Γ₀.comps = [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++
      A ++ Bt)
    (h1 : Γ₁.comps = τh ++ A.map (Comp.map Λc) ++ Lt) (hτlen : τh.length = 5)
    (hsy : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y))
    (hA : ∀ a ∈ A, a.kind ≠ .dot ∧ a.x ≠ .inl 1 ∧ a.x ≠ .inl 2 ∧ a.y ≠ .inl 1 ∧ a.y ≠ .inl 2)
    (hd0 : ∀ c ∈ Γ₀.comps, c.kind ≠ .dot) (hBt : ∀ c ∈ Bt, c.kind = .xdot)
    (hΛinj : Function.Injective Λc) (hΛl : ∀ a, Λc (.inl a) = .inl a)
    (hΛr : ∀ a, (Λc (.inr a)).isRight = true) (hΛs : ∀ k, ∃ a, Λc (.inr a) = .inr k)
    (hΛα : Λc (.inr α) = TEqIdentity_αc)
    (hτmol : ∀ d ∈ τh, d.kind.joinsMol = true →
      d = mkC (.waved .s) (Λc (.inr y)) TEqIdentity_αc ∨
        (d.x = TEqIdentity_αc ∧ (d.y = .inl 1 ∨ d.y = .inl 2)))
    (hτs : mkC (.waved .s) (Λc (.inr y)) TEqIdentity_αc ∈ τh)
    (hLt : ∀ d ∈ Lt, d.kind.joinsMol = false)
    (hflat : ∀ d ∈ Γ₁.comps, Γ₁.flatComp d = d)
    (eP eM : Fin Γ₁.comps.length ⊕ Fin 3)
    (hP : Γ₁.toMG'.cls eP = some .plus ∧ Γ₁.toMG'.ends eP = (Γ₁.molRep TEqIdentity_αc, .inl 1))
    (hM : Γ₁.toMG'.cls eM = some .minus ∧ Γ₁.toMG'.ends eM = (Γ₁.molRep TEqIdentity_αc, .inl 2))
    (hpres : ∀ e', Γ₁.toMG'.cls e' ≠ none → e' = eP ∨ e' = eM ∨
      ∃ i : Fin Γ₁.comps.length, e' = .inl i ∧ 5 ≤ i.val ∧ i.val < 5 + A.length)
    (hPM : eP ≠ eM) (hPA : ∀ i : Fin Γ₁.comps.length, 5 ≤ i.val → eP ≠ .inl i ∧ eM ≠ .inl i) :
    Γ₀.toMG'.Transported Γ₁.toMG' := by
  classical
  obtain ⟨han0, hfl0⟩ := TEqIdentity_dotFree_flat hd0
  have hmem0 : ∀ c, c ∈ Γ₀.comps ↔ c = sy ∨ c = mkC (.G .plus) (.inr α) (.inl 1) ∨
      c = mkC (.G .minus) (.inr α) (.inl 2) ∨ c ∈ A ∨ c ∈ Bt := by
    intro c
    rw [h0]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]
  have hmem1 : ∀ c, c ∈ Γ₁.comps ↔ c ∈ τh ∨ c ∈ A.map (Comp.map Λc) ∨ c ∈ Lt := by
    intro c
    rw [h1]
    simp only [List.mem_append, or_assoc]
  -- the backward map of the atoms
  let Γb : Atom 3 (M + 1) → Atom 3 N := fun w =>
    if w = .inl 1 ∨ w = .inl 2 then .inr α else Function.invFun Λc w
  have hΓb : ∀ w, w ≠ .inl 1 → w ≠ .inl 2 → Γb (Λc w) = w := by
    intro w h1' h2'
    have : ¬ (Λc w = .inl 1 ∨ Λc w = .inl 2) := by
      rintro (h | h)
      · rcases w with a | a
        · rw [hΛl] at h; simp only [Sum.inl.injEq] at h; exact h1' (by rw [h])
        · have := hΛr a; rw [h] at this; cases this
      · rcases w with a | a
        · rw [hΛl] at h; simp only [Sum.inl.injEq] at h; exact h2' (by rw [h])
        · have := hΛr a; rw [h] at this; cases this
    simp only [Γb, this, ite_false]
    exact Function.leftInverse_invFun hΛinj w
  -- the molecules correspond
  have hsyr : (SimpleGraph.fromRel fun u v => ∃ c ∈ Γ₀.comps, c.kind.joinsMol = true ∧ c.x = u ∧
      c.y = v).Reachable (.inr y) (.inr α) := by
    rcases hsy with h | h
    · by_cases hyα : (Sum.inr y : Atom 3 N) = .inr α
      · rw [hyα]
      · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hyα, Or.inl ⟨sy, (hmem0 _).2 (Or.inl rfl), by rw [h]; rfl, by rw [h]; rfl,
            by rw [h]; rfl⟩⟩)
    · by_cases hyα : (Sum.inr y : Atom 3 N) = .inr α
      · rw [hyα]
      · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨hyα, Or.inr ⟨sy, (hmem0 _).2 (Or.inl rfl), by rw [h]; rfl, by rw [h]; rfl,
            by rw [h]; rfl⟩⟩)
  have hfwd : ∀ u v, Γ₀.molGraph.Reachable u v → Γ₁.molGraph.Reachable (Λc u) (Λc v) := by
    intro u v h
    refine TEqIdentity_reach_map Λc (fun a b ⟨c, hc, hk, hx, hy⟩ => ?_) h
    rcases (hmem0 c).1 hc with rfl | rfl | rfl | hA' | hB
    · have hs : Γ₁.molGraph.Reachable (Λc (.inr y)) TEqIdentity_αc := by
        by_cases he : Λc (.inr y) = TEqIdentity_αc
        · rw [he]
        · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
            ⟨he, Or.inl ⟨_, (hmem1 _).2 (Or.inl hτs), rfl, rfl, rfl⟩⟩)
      rcases hsy with h' | h' <;> rw [h'] at hx hy <;> simp only [mkC] at hx hy <;>
        subst hx hy <;> rw [hΛα]
      · exact hs
      · exact hs.symm
    · cases hk
    · cases hk
    · by_cases he : Λc a = Λc b
      · rw [he]
      · refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨he, Or.inl ⟨c.map Λc, (hmem1 _).2 (Or.inr (Or.inl (List.mem_map_of_mem hA'))), hk,
            by rw [← hx]; rfl, by rw [← hy]; rfl⟩⟩)
    · rw [hBt c hB] at hk
      cases hk
  have hbwd : ∀ u v, Γ₁.molGraph.Reachable u v → Γ₀.molGraph.Reachable (Γb u) (Γb v) := by
    intro u v h
    refine TEqIdentity_reach_map Γb (fun a b ⟨c, hc, hk, hx, hy⟩ => ?_) h
    rcases (hmem1 c).1 hc with hτ | hA' | hL
    · rcases hτmol c hτ hk with rfl | ⟨h1', h2'⟩
      · simp only [mkC] at hx hy
        subst hx hy
        have e1 : Γb (Λc (.inr y)) = .inr y := hΓb _ (by simp) (by simp)
        have e2 : Γb TEqIdentity_αc = .inr α := by rw [← hΛα]; exact hΓb _ (by simp) (by simp)
        rw [e1, e2]
        exact hsyr
      · have e2 : Γb TEqIdentity_αc = .inr α := by rw [← hΛα]; exact hΓb _ (by simp) (by simp)
        have e3 : Γb c.y = .inr α := by
          simp only [Γb]
          rw [if_pos h2']
        rw [← hx, ← hy, h1', e2, e3]
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hA'
      obtain ⟨-, hx1, hx2, hy1, hy2⟩ := hA a' ha'
      subst hx hy
      simp only [Comp.map]
      rw [hΓb _ hx1 hx2, hΓb _ hy1 hy2]
      by_cases he : a'.x = a'.y
      · rw [he]
      · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
          ⟨he, Or.inl ⟨a', (hmem0 _).2 (Or.inr (Or.inr (Or.inr (Or.inl ha')))), hk, rfl, rfl⟩⟩)
    · rw [hLt c hL] at hk
      cases hk
  have hR : ∀ u, (Λc u).isRight = u.isRight := by
    rintro (a | a)
    · simp [hΛl]
    · rw [hΛr a]; rfl
  have hmol : ∀ u v, Γ₀.SameMol u v ↔ Γ₁.SameMol (Λc u) (Λc v) := by
    intro u v
    constructor
    · rintro (rfl | ⟨hu, hv, h⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨by rw [hR]; exact hu, by rw [hR]; exact hv, hfwd u v h⟩
    · rintro (h | ⟨hu, hv, h⟩)
      · exact Or.inl (hΛinj h)
      · rw [hR] at hu hv
        have := hbwd _ _ h
        rcases u with a | a
        · simp at hu
        rcases v with b | b
        · simp at hv
        rw [hΓb _ (by simp) (by simp), hΓb _ (by simp) (by simp)] at this
        exact Or.inr ⟨rfl, rfl, this⟩
  have hrep : ∀ u, Γ₁.molRep (Λc (Γ₀.molRep u)) = Γ₁.molRep (Λc u) := by
    intro u
    refine TEqIdentity_molRep_of_sameMol ((hmol _ _).1 ?_)
    exact TEqIdentity_sameMol_of_molRep (MolMono_molRep_idem Γ₀ u)
  have hrepeq : ∀ u v, Γ₁.molRep (Λc u) = Γ₁.molRep (Λc v) ↔ Γ₀.molRep u = Γ₀.molRep v := by
    intro u v
    constructor
    · intro h
      exact TEqIdentity_molRep_of_sameMol ((hmol u v).2 (TEqIdentity_sameMol_of_molRep h))
    · intro h
      exact TEqIdentity_molRep_of_sameMol ((hmol u v).1 (TEqIdentity_sameMol_of_molRep h))
  -- the edges of the two molecular graphs
  have hlen1 : Γ₁.comps.length = 5 + A.length + Lt.length := by
    rw [h1]; simp [hτlen]; omega
  have hcls0 : ∀ j : Fin Γ₀.comps.length, Γ₀.toMG'.cls (.inl j) =
      if Γ₀.comps[j].kind = .dot ∨ Γ₀.molRep Γ₀.comps[j].x = Γ₀.molRep Γ₀.comps[j].y then none
      else Γ₀.comps[j].kind.mclass := by
    intro j
    simp only [Graph.toMG', hfl0]
  have hends0 : ∀ j : Fin Γ₀.comps.length, Γ₀.toMG'.ends (.inl j) =
      (Γ₀.molRep Γ₀.comps[j].x, Γ₀.molRep Γ₀.comps[j].y) := by
    intro j
    simp only [Graph.toMG', hfl0]
  have hcls0r : ∀ a, Γ₀.toMG'.cls (.inr a) = none := by
    intro a
    simp [Graph.toMG', han0]
  have hcls1 : ∀ i : Fin Γ₁.comps.length, Γ₁.toMG'.cls (.inl i) =
      if Γ₁.comps[i].kind = .dot ∨ Γ₁.molRep Γ₁.comps[i].x = Γ₁.molRep Γ₁.comps[i].y then none
      else Γ₁.comps[i].kind.mclass := by
    intro i
    have hf := hflat Γ₁.comps[(i : ℕ)] (List.getElem_mem i.2)
    simp only [Graph.toMG', Fin.getElem_fin, hf]
  have hends1 : ∀ i : Fin Γ₁.comps.length, Γ₁.toMG'.ends (.inl i) =
      (Γ₁.molRep Γ₁.comps[i].x, Γ₁.molRep Γ₁.comps[i].y) := by
    intro i
    have hf := hflat Γ₁.comps[(i : ℕ)] (List.getElem_mem i.2)
    simp only [Graph.toMG', Fin.getElem_fin, hf]
  have hA0 : ∀ j : Fin Γ₀.comps.length, ∀ h : 3 ≤ j.val ∧ j.val < 3 + A.length,
      Γ₀.comps[j] = A[j.val - 3]'(by omega) := by
    intro j h
    rw [Fin.getElem_fin, List.getElem_of_eq h0 j.2, TEqIdentity_idx _ _ _ _ (by simp; omega)
      (by simp; omega)]
    simp
  have hA1 : ∀ i : Fin Γ₁.comps.length, ∀ h : 5 ≤ i.val ∧ i.val < 5 + A.length,
      Γ₁.comps[i] = (A[i.val - 5]'(by omega)).map Λc := by
    intro i h
    rw [Fin.getElem_fin, List.getElem_of_eq h1 i.2, TEqIdentity_idx _ _ _ _ (by omega)
      (by simp; omega)]
    simp [hτlen]
  -- the present edges of the output graph
  have hpres0 : ∀ e, Γ₀.toMG'.cls e ≠ none → ∃ j : Fin Γ₀.comps.length, e = .inl j ∧
      (j.val = 1 ∨ j.val = 2 ∨ (3 ≤ j.val ∧ j.val < 3 + A.length)) := by
    rintro (j | a) he
    · refine ⟨j, rfl, ?_⟩
      by_contra hn
      push Not at hn
      apply he
      rw [hcls0]
      have hc : Γ₀.comps[j].kind.mclass = none := by
        rw [Fin.getElem_fin, List.getElem_of_eq h0 j.2]
        rcases Nat.lt_or_ge j.val 3 with hj | hj
        · have hj0 : j.val = 0 := by omega
          simp only [hj0]
          rcases hsy with rfl | rfl <;> rfl
        · have hj' : 3 + A.length ≤ j.val := by omega
          rw [List.getElem_append_right (by simp; omega)]
          rw [hBt _ (List.getElem_mem _)]
          rfl
      split_ifs
      · rfl
      · exact hc
    · exact absurd (hcls0r a) he
  -- the map of the edges
  let E : Fin Γ₀.comps.length ⊕ Fin 3 → Fin Γ₁.comps.length ⊕ Fin 3 := fun e =>
    match e with
    | .inl j => if j.val = 1 then eP else if j.val = 2 then eM else
        if h : 3 ≤ j.val ∧ j.val < 3 + A.length then .inl ⟨j.val + 2, by omega⟩ else .inr 0
    | .inr _ => .inr 0
  have hE1 : ∀ j : Fin Γ₀.comps.length, j.val = 1 → E (.inl j) = eP := by
    intro j hj; simp [E, hj]
  have hE2 : ∀ j : Fin Γ₀.comps.length, j.val = 2 → E (.inl j) = eM := by
    intro j hj; simp [E, hj]
  have hE3 : ∀ j : Fin Γ₀.comps.length, ∀ h : 3 ≤ j.val ∧ j.val < 3 + A.length,
      E (.inl j) = .inl ⟨j.val + 2, by omega⟩ := by
    intro j h
    simp only [E]
    rw [if_neg (by omega), if_neg (by omega), dif_pos h]
  have hG1 : ∀ j : Fin Γ₀.comps.length, j.val = 1 →
      Γ₀.comps[j] = mkC (.G .plus) (.inr α) (.inl 1) := by
    intro j hj
    rw [Fin.getElem_fin, List.getElem_of_eq h0 j.2]
    simp [hj]
  have hG2 : ∀ j : Fin Γ₀.comps.length, j.val = 2 →
      Γ₀.comps[j] = mkC (.G .minus) (.inr α) (.inl 2) := by
    intro j hj
    rw [Fin.getElem_fin, List.getElem_of_eq h0 j.2]
    simp [hj]
  have hrl : ∀ a : Fin 3, Γ₀.molRep (.inl a) = .inl a := fun _ => rfl
  have hαne : ∀ a : Fin 3, Γ₀.molRep (.inr α) ≠ .inl a := by
    intro a h
    obtain ⟨b, hb, -⟩ := MolMono_molRep_inr Γ₀ α
    rw [hb] at h
    cases h
  -- the classes and ends are kept
  have hmid : ∀ (j : Fin Γ₀.comps.length) (hj : 3 ≤ j.val ∧ j.val < 3 + A.length),
      Γ₁.toMG'.cls (E (.inl j)) = Γ₀.toMG'.cls (.inl j) := by
    intro j hj
    have hi := hA1 ⟨j.val + 2, by omega⟩ ⟨show 5 ≤ j.val + 2 by omega,
      show j.val + 2 < 5 + A.length by omega⟩
    rw [hE3 j hj, hcls1, hcls0]
    simp only [hi, hA0 j hj]
    have hidx : j.val + 2 - 5 = j.val - 3 := by omega
    simp only [hidx, Comp.map, hrepeq]
  have hcls : ∀ e, Γ₀.toMG'.cls e ≠ none → Γ₁.toMG'.cls (E e) = Γ₀.toMG'.cls e := by
    intro e he
    obtain ⟨j, rfl, hj⟩ := hpres0 e he
    rcases hj with hj | hj | hj
    · rw [hE1 j hj, hP.1, hcls0, hG1 j hj]
      simp [mkC, Kind.mclass, hαne, hrl]
    · rw [hE2 j hj, hM.1, hcls0, hG2 j hj]
      simp [mkC, Kind.mclass, hαne, hrl]
    · exact hmid j hj
  have hends : ∀ e, Γ₀.toMG'.cls e ≠ none →
      Γ₁.toMG'.ends (E e) = ((fun v => Γ₁.molRep (Λc v)) (Γ₀.toMG'.ends e).1,
        (fun v => Γ₁.molRep (Λc v)) (Γ₀.toMG'.ends e).2) := by
    intro e he
    obtain ⟨j, rfl, hj⟩ := hpres0 e he
    rcases hj with hj | hj | hj
    · rw [hE1 j hj, hP.2, hends0, hG1 j hj]
      simp only [mkC, hrep, hΛα, hΛl]
      rfl
    · rw [hE2 j hj, hM.2, hends0, hG2 j hj]
      simp only [mkC, hrep, hΛα, hΛl]
      rfl
    · have hi := hA1 ⟨j.val + 2, by omega⟩ ⟨show 5 ≤ j.val + 2 by omega,
        show j.val + 2 < 5 + A.length by omega⟩
      rw [hE3 j hj, hends1, hends0]
      simp only [hi, hA0 j hj]
      have hidx : j.val + 2 - 5 = j.val - 3 := by omega
      simp only [hidx, Comp.map, hrep]
  refine ⟨fun v => Γ₁.molRep (Λc v), E, fun e₁ e₂ p₁ p₂ h => ?_, fun v hv w hw h => ?_, ?_, ?_,
    fun e he => ?_, hcls, fun e he => Or.inl (hends e he), fun e' he' => ?_⟩
  · obtain ⟨j₁, rfl, hj₁⟩ := hpres0 _ p₁
    obtain ⟨j₂, rfl, hj₂⟩ := hpres0 _ p₂
    have hne : ∀ (j : Fin Γ₀.comps.length) (hj : 3 ≤ j.val ∧ j.val < 3 + A.length),
        eP ≠ E (.inl j) ∧ eM ≠ E (.inl j) := by
      intro j hj
      rw [hE3 j hj]
      exact hPA _ (by simp; omega)
    rcases hj₁ with hj₁ | hj₁ | hj₁ <;> rcases hj₂ with hj₂ | hj₂ | hj₂
    · exact congrArg _ (Fin.ext (hj₁.trans hj₂.symm))
    · rw [hE1 _ hj₁, hE2 _ hj₂] at h; exact absurd h hPM
    · rw [hE1 _ hj₁] at h; exact absurd h (hne _ hj₂).1
    · rw [hE2 _ hj₁, hE1 _ hj₂] at h; exact absurd h.symm hPM
    · exact congrArg _ (Fin.ext (hj₁.trans hj₂.symm))
    · rw [hE2 _ hj₁] at h; exact absurd h (hne _ hj₂).2
    · rw [hE1 _ hj₂] at h; exact absurd h.symm (hne _ hj₁).1
    · rw [hE2 _ hj₂] at h; exact absurd h.symm (hne _ hj₁).2
    · rw [hE3 _ hj₁, hE3 _ hj₂] at h
      simp only [Sum.inl.injEq, Fin.mk.injEq] at h
      exact congrArg _ (Fin.ext (by omega))
  · have hfix : ∀ u ∈ (↑Γ₀.toMG'.int ∪ ↑Γ₀.toMG'.ext : Set (Atom 3 N)), Γ₀.molRep u = u := by
      rintro u (hu | hu)
      · obtain ⟨b, rfl, hb⟩ := MolMono_of_mem_int Γ₀ (Finset.mem_coe.1 hu)
        exact hb
      · obtain ⟨a, rfl⟩ := (MolMono_mem_ext Γ₀ _).1 (Finset.mem_coe.1 hu)
        rfl
    rw [← hfix v hv, ← hfix w hw]
    exact (hrepeq v w).1 h
  · ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨a, ha⟩ := hΛs k
      exact ⟨Γ₀.molRep (.inr a), ⟨a, rfl⟩, by rw [hrep, ha]⟩
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      rw [hrep]
      rcases h : Λc (.inr a) with b | k
      · have := hΛr a; rw [h] at this; cases this
      · exact ⟨k, rfl⟩
  · ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨.inl a, ⟨a, rfl⟩, by rw [hΛl]; rfl⟩
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by rw [hΛl]; rfl⟩
  · obtain ⟨j, rfl, -⟩ := hpres0 e he
    rw [hends0]
    exact ⟨MolMono_molRep_isVtx Γ₀ _, MolMono_molRep_isVtx Γ₀ _⟩
  · by_contra hn
    rcases hpres e' hn with rfl | rfl | ⟨i, rfl, hi1, hi2⟩
    · obtain ⟨j, hj⟩ : ∃ j : Fin Γ₀.comps.length, j.val = 1 :=
        ⟨⟨1, by rw [h0]; simp⟩, rfl⟩
      refine he' (.inl j) ?_ (hE1 j hj)
      rw [hcls0, hG1 j hj]
      simp [mkC, Kind.mclass, hαne, hrl]
    · obtain ⟨j, hj⟩ : ∃ j : Fin Γ₀.comps.length, j.val = 2 :=
        ⟨⟨2, by rw [h0]; simp⟩, rfl⟩
      refine he' (.inl j) ?_ (hE2 j hj)
      rw [hcls0, hG2 j hj]
      simp [mkC, Kind.mclass, hαne, hrl]
    · have hj : i.val - 2 < Γ₀.comps.length := by rw [h0]; simp; omega
      have hj3 : 3 ≤ (⟨i.val - 2, hj⟩ : Fin Γ₀.comps.length).val ∧
          (⟨i.val - 2, hj⟩ : Fin Γ₀.comps.length).val < 3 + A.length := by simp; omega
      have hEi : E (.inl ⟨i.val - 2, hj⟩) = .inl i := by
        rw [hE3 _ hj3]
        congr 1
        exact Fin.ext (by simp; omega)
      refine he' (.inl ⟨i.val - 2, hj⟩) (fun h0' => hn ?_) hEi
      rw [← hEi, hmid _ hj3]
      exact h0'

/-- **A correction graph is globally standard** ([II, Def 6.2] in the block reading) when its output
graph is: the molecular graphs agree up to names (`TEqIdentity_tr_core`), the edges `G_{α⊕}`,
`Ḡ_{α⊖}` going to the solid edge at `α'` or to the edge from the molecule of `α'` to `⊕` or `⊖`. -/
private theorem TEqIdentity_gs {N M : ℕ} {Γ : Graph 3 N} {Γc : Graph 3 (M + 1)}
    {A Bt : List (Comp (Atom 3 N))} {sy : Comp (Atom 3 N)} {Λc : Atom 3 N → Atom 3 (M + 1)}
    {α y : Fin N} {xh : Atom 3 (M + 1)} {yh : Atom 3 M} {ℓ : ℕ} {τc : List (Comp (Atom 3 1))}
    (hgs : gsPM' Γ)
    (hgp : Γ.comps.Perm ([sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++
      A ++ Bt))
    (hc0 : Γc.comps.Perm (A.map (Comp.map Λc) ++ (List.replicate ℓ (mkC .xdot xh xh) ++
      τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))))))
    (hA'' : ∀ d ∈ A.map (Comp.map Λc), d = mkC (.theta []) (.inl 0) xh ∨
      (d.x.isRight = true ∧ d.y.isRight = true ∧ d.x ≠ TEqIdentity_αc ∧ d.y ≠ TEqIdentity_αc ∧
        d.kind ≠ .dot))
    (hxh : xh.isRight = true ∧ xh ≠ TEqIdentity_αc) (hyh : yh.isRight = true)
    (hτc : τc = TEqIdentity_T1 ∨ τc = TEqIdentity_T2 ∨ τc = TEqIdentity_T3)
    (hsy : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y))
    (hA : ∀ a ∈ A, a.kind ≠ .dot ∧ a.x ≠ .inl 1 ∧ a.x ≠ .inl 2 ∧ a.y ≠ .inl 1 ∧ a.y ≠ .inl 2)
    (hd0 : ∀ c ∈ Γ.comps, c.kind ≠ .dot) (hBt : ∀ c ∈ Bt, c.kind = .xdot)
    (hΛinj : Function.Injective Λc) (hΛl : ∀ a, Λc (.inl a) = .inl a)
    (hΛr : ∀ a, (Λc (.inr a)).isRight = true) (hΛs : ∀ k, ∃ a, Λc (.inr a) = .inr k)
    (hΛα : Λc (.inr α) = TEqIdentity_αc) (hΛy : Λc (.inr y) = liftA 1 yh) : gsPM' Γc := by
  classical
  set τh := τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) with hτh
  set Lt := List.replicate ℓ (mkC .xdot xh xh) with hLt
  let Γ₀ : Graph 3 N := ⟨[sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++
    A ++ Bt, Γ.coeff⟩
  let Γ₁ : Graph 3 (M + 1) := ⟨τh ++ A.map (Comp.map Λc) ++ Lt, Γc.coeff⟩
  have h01 : Γ₁.comps.Perm (A.map (Comp.map Λc) ++ (Lt ++ τh)) := by
    show (τh ++ A.map (Comp.map Λc) ++ Lt).Perm _
    rw [List.append_assoc]
    refine List.perm_append_comm.trans ?_
    rw [List.append_assoc]
  have hd0' : ∀ c ∈ Γ₀.comps, c.kind ≠ .dot := fun c hc => hd0 c (hgp.mem_iff.2 hc)
  have hflat := TEqIdentity_flatComp h01 hA'' hxh hyh hτc
  have hmem1 := TEqIdentity_mem h01
  obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
  have hτlen : τh.length = 5 := by rcases hτc with rfl | rfl | rfl <;> rfl
  have hlen1 : (τh ++ A.map (Comp.map Λc) ++ Lt).length = 5 + A.length + ℓ := by
    simp [hτlen, hLt]; omega
  have hrl : ∀ a : Fin 3, Γ₁.molRep (.inl a) = .inl a := fun _ => rfl
  have hαne : ∀ a : Fin 3, Γ₁.molRep TEqIdentity_αc ≠ .inl a := by
    intro a h
    obtain ⟨b, hb, -⟩ := MolMono_molRep_inr Γ₁ (Fin.natAdd M 0)
    rw [hb] at h
    cases h
  -- the edge from the molecule of `α'` to an identified external atom
  have hpin : ∀ a : Fin 3, mkC .dot TEqIdentity_αc (.inl a) ∈ Γ₁.comps →
      Γ₁.toMG'.cls (.inr a) = some (pinClass a) ∧
        Γ₁.toMG'.ends (.inr a) = (Γ₁.molRep TEqIdentity_αc, .inl a) := by
    intro a ha
    have := TEqIdentity_anchor_pin h01 hA'' hxh hyh hτc ha
    constructor
    · simp only [Graph.toMG', this]
    · simp only [Graph.toMG', this]
  have hunp : ∀ a : Fin 3, mkC .dot TEqIdentity_αc (.inl a) ∉ Γ₁.comps →
      Γ₁.toMG'.cls (.inr a) = none := by
    intro a ha
    have := TEqIdentity_anchor_none (TEqIdentity_unpinned h01 hA'' hxh hyh hτc ha)
    simp only [Graph.toMG', this]
  -- the edges of the components of the recollision term and of the loops
  have hcτ : ∀ (i : Fin Γ₁.comps.length) (hi : i.val < 5), Γ₁.toMG'.cls (.inl i) =
      if (τh[i.val]'(by omega)).kind = .dot ∨ Γ₁.molRep (τh[i.val]'(by omega)).x =
        Γ₁.molRep (τh[i.val]'(by omega)).y then none else (τh[i.val]'(by omega)).kind.mclass := by
    intro i hi
    have hg : Γ₁.comps[i.val] = τh[i.val]'(by omega) := by
      show (τh ++ A.map (Comp.map Λc) ++ Lt)[i.val]'(by omega) = _
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)]
    have hf := hflat _ (List.getElem_mem i.2)
    simp only [Fin.getElem_fin, hg] at hf
    simp only [Graph.toMG', Fin.getElem_fin, hg, hf]
  have heτ : ∀ (i : Fin Γ₁.comps.length) (hi : i.val < 5), Γ₁.toMG'.ends (.inl i) =
      (Γ₁.molRep (τh[i.val]'(by omega)).x, Γ₁.molRep (τh[i.val]'(by omega)).y) := by
    intro i hi
    have hg : Γ₁.comps[i.val] = τh[i.val]'(by omega) := by
      show (τh ++ A.map (Comp.map Λc) ++ Lt)[i.val]'(by omega) = _
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)]
    have hf := hflat _ (List.getElem_mem i.2)
    simp only [Fin.getElem_fin, hg] at hf
    simp only [Graph.toMG', Fin.getElem_fin, hg, hf]
  have hcL : ∀ i : Fin Γ₁.comps.length, 5 + A.length ≤ i.val → Γ₁.toMG'.cls (.inl i) = none := by
    intro i hi
    have hi2 : i.val < 5 + A.length + ℓ := by have := i.2; simp only [Γ₁] at this; omega
    have hg : Γ₁.comps[i.val] = mkC .xdot xh xh := by
      show (τh ++ A.map (Comp.map Λc) ++ Lt)[i.val]'(by omega) = _
      rw [List.getElem_append_right (by simp [hτlen]; omega)]
      simp [hLt]
    have hf := hflat _ (List.getElem_mem i.2)
    simp only [Fin.getElem_fin, hg] at hf
    simp only [Graph.toMG', Fin.getElem_fin, hg, hf]
    simp [mkC, Kind.mclass]
  have hpres : ∀ (eP eM : Fin Γ₁.comps.length ⊕ Fin 3),
      (∀ a : Fin 3, mkC .dot TEqIdentity_αc (.inl a) ∈ Γ₁.comps → Sum.inr a = eP ∨ Sum.inr a = eM) →
      (∀ (i : Fin Γ₁.comps.length) (hi : i.val < 5), Γ₁.toMG'.cls (.inl i) ≠ none →
        Sum.inl i = eP ∨ Sum.inl i = eM) →
      ∀ e', Γ₁.toMG'.cls e' ≠ none → e' = eP ∨ e' = eM ∨
        ∃ i : Fin Γ₁.comps.length, e' = .inl i ∧ 5 ≤ i.val ∧ i.val < 5 + A.length := by
    intro eP eM hr hl e' he'
    rcases e' with i | a
    · by_cases hi : i.val < 5
      · rcases hl i hi he' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · by_cases hi' : 5 + A.length ≤ i.val
        · exact absurd (hcL i hi') he'
        · exact Or.inr (Or.inr ⟨i, rfl, by omega, by omega⟩)
    · by_cases ha : mkC .dot TEqIdentity_αc (.inl a) ∈ Γ₁.comps
      · rcases hr a ha with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact absurd (hunp a ha) he'
  have hpm : ∀ a : Fin 3, mkC .dot TEqIdentity_αc (.inl a) ∈ Γ₁.comps ↔
      mkC .dot TEqIdentity_αc (.inl a) ∈ τh := TEqIdentity_pin_iff h01 hA'' hxh hyh hτc
  have hA2 : ∀ a ∈ A, a.kind ≠ .dot ∧ a.x ≠ .inl 1 ∧ a.x ≠ .inl 2 ∧ a.y ≠ .inl 1 ∧
      a.y ≠ .inl 2 := hA
  have hτmol : ∀ d ∈ τh, d.kind.joinsMol = true →
      d = mkC (.waved .s) (Λc (.inr y)) TEqIdentity_αc ∨
        (d.x = TEqIdentity_αc ∧ (d.y = .inl 1 ∨ d.y = .inl 2)) := by
    intro d hd hk
    rw [hΛy]
    rw [hτh] at hd
    rcases hτc with rfl | rfl | rfl
    · rw [t1] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr ⟨rfl, Or.inl rfl⟩ | exact Or.inr ⟨rfl, Or.inr rfl⟩ |
          simp [mkC, Kind.joinsMol] at hk
    · rw [t2] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr ⟨rfl, Or.inl rfl⟩ | exact Or.inr ⟨rfl, Or.inr rfl⟩ |
          simp [mkC, Kind.joinsMol] at hk
    · rw [t3] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr ⟨rfl, Or.inl rfl⟩ | exact Or.inr ⟨rfl, Or.inr rfl⟩ |
          simp [mkC, Kind.joinsMol] at hk
  have hτs : mkC (.waved .s) (Λc (.inr y)) TEqIdentity_αc ∈ τh := by
    rw [hΛy, hτh]; rcases hτc with rfl | rfl | rfl <;> simp [t1, t2, t3]
  have hcore := fun eP eM hP hM hpr hPM hPA => TEqIdentity_tr_core (Γ₀ := Γ₀) (Γ₁ := Γ₁)
    rfl rfl hτlen hsy hA2 hd0' hBt hΛinj hΛl hΛr hΛs hΛα hτmol hτs
    (fun d hd => by rw [hLt] at hd; rw [List.eq_of_mem_replicate hd]; rfl) hflat eP eM hP hM hpr
      hPM hPA
  have h5 : ∀ i : ℕ, i < 5 → i < Γ₁.comps.length := fun i hi => by
    show i < (τh ++ A.map (Comp.map Λc) ++ Lt).length; omega
  -- the classes of the components of the recollision term
  have hτcls : ∀ (i : ℕ) (hi : i < 5), Γ₁.toMG'.cls (.inl ⟨i, h5 i hi⟩) =
      if (τh[i]'(by omega)).kind = .dot ∨ Γ₁.molRep (τh[i]'(by omega)).x =
        Γ₁.molRep (τh[i]'(by omega)).y then none else (τh[i]'(by omega)).kind.mclass :=
    fun i hi => hcτ ⟨i, h5 i hi⟩ hi
  have hτends : ∀ (i : ℕ) (hi : i < 5), Γ₁.toMG'.ends (.inl ⟨i, h5 i hi⟩) =
      (Γ₁.molRep (τh[i]'(by omega)).x, Γ₁.molRep (τh[i]'(by omega)).y) :=
    fun i hi => heτ ⟨i, h5 i hi⟩ hi
  have hlow : ∀ (P : Fin Γ₁.comps.length → Prop),
      (∀ (i : ℕ) (hi : i < 5), Γ₁.toMG'.cls (.inl ⟨i, h5 i hi⟩) ≠ none → P ⟨i, h5 i hi⟩) →
      ∀ (i : Fin Γ₁.comps.length) (hi : i.val < 5), Γ₁.toMG'.cls (.inl i) ≠ none → P i := by
    intro P h i hi hc
    exact h i.val hi hc
  have htr : Γ₀.toMG'.Transported Γ₁.toMG' := by
    rcases hτc with rfl | rfl | rfl
    · have e2 : τh[2]'(by omega) = mkC (.G .minus) TEqIdentity_αc (.inl 2) := by
        simp [hτh, t1]
      refine hcore (.inr 1) (.inl ⟨2, h5 2 (by omega)⟩) ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ (by simp)
        (fun i hi => ⟨by simp, by simp [Fin.ext_iff]; omega⟩)
      · rw [(hpin 1 ((hpm 1).2 (by simp [hτh, t1]))).1]; rfl
      · exact (hpin 1 ((hpm 1).2 (by simp [hτh, t1]))).2
      · rw [hτcls 2 (by omega), e2]
        simp [mkC, Kind.mclass, hαne, hrl]
      · rw [hτends 2 (by omega), e2]
        rfl
      · refine hpres _ _ (fun a ha => ?_) (hlow _ fun i hi hc => ?_)
        · rw [hpm, hτh, t1] at ha
          simp [mkC] at ha
          left; rw [ha]
        · right
          rw [hτcls i hi] at hc
          interval_cases i <;> simp [hτh, t1, mkC, Kind.mclass] at hc ⊢
    · have e1 : τh[1]'(by omega) = mkC (.G .plus) TEqIdentity_αc (.inl 1) := by
        simp [hτh, t2]
      refine hcore (.inl ⟨1, h5 1 (by omega)⟩) (.inr 2) ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ (by simp)
        (fun i hi => ⟨by simp [Fin.ext_iff]; omega, by simp⟩)
      · rw [hτcls 1 (by omega), e1]
        simp [mkC, Kind.mclass, hαne, hrl]
      · rw [hτends 1 (by omega), e1]
        rfl
      · rw [(hpin 2 ((hpm 2).2 (by simp [hτh, t2]))).1]; rfl
      · exact (hpin 2 ((hpm 2).2 (by simp [hτh, t2]))).2
      · refine hpres _ _ (fun a ha => ?_) (hlow _ fun i hi hc => ?_)
        · rw [hpm, hτh, t2] at ha
          simp [mkC] at ha
          right; rw [ha]
        · left
          rw [hτcls i hi] at hc
          interval_cases i <;> simp [hτh, t2, mkC, Kind.mclass] at hc ⊢
    · refine hcore (.inr 1) (.inr 2) ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ (by simp) (fun i hi => ⟨by simp, by simp⟩)
      · rw [(hpin 1 ((hpm 1).2 (by simp [hτh, t3]))).1]; rfl
      · exact (hpin 1 ((hpm 1).2 (by simp [hτh, t3]))).2
      · rw [(hpin 2 ((hpm 2).2 (by simp [hτh, t3]))).1]; rfl
      · exact (hpin 2 ((hpm 2).2 (by simp [hτh, t3]))).2
      · refine hpres _ _ (fun a ha => ?_) (hlow _ fun i hi hc => ?_)
        · rw [hpm, hτh, t3] at ha
          simp [mkC] at ha
          rcases ha with rfl | rfl
          · left; rfl
          · right; rfl
        · exfalso
          rw [hτcls i hi] at hc
          interval_cases i <;> simp [hτh, t3, mkC, Kind.mclass] at hc
  have hall : Γ.toMG'.Transported Γc.toMG' :=
    TEqIdentity_tr_trans (TEqIdentity_tr_perm hgp)
      (TEqIdentity_tr_trans htr (TEqIdentity_tr_perm (h01.trans hc0.symm)))
  exact (SubstMol_gs_transport hall).2 hgs

end MolTransport

/-! ## The classes of the correction graphs -/

section Main

/-- The labels of a graph without labels. -/
private theorem TEqIdentity_labels_nil {k n : ℕ} {Γ : Graph k n} (h : Γ.LabelFree) :
    Γ.labels = [] := by
  have : Γ.comps.filterMap Comp.label = [] := List.filterMap_eq_nil_iff.2 h
  simp [Graph.labels, this]

/-- **The classes of a correction graph** (the `t → T` rewriting before [II, (6.7)], [II, (4.15)],
[II, Def 6.3 (1)]): for an output graph `Γ` in the leaf form, without dotted edges or labels,
globally standard and plain, of scaling order `≥ 4`, and a correction graph `Γc` built from the
components of `𝒮` read through an atom map `ψ` (injective but for `0, 1 ↦ x` at `x = y`), `Γc`
has scaling order `ord Γ + 1` or `ord Γ + 2`, is of the class `Graph.LeafR` with the clauses
`Graph.LeafC`, is plain, and the block of `⊕` or `⊖` contains an internal atom. -/
private theorem TEqIdentity_corr_main {N M m : ℕ} {Γ : Graph 3 N}
    {x y α : Fin N} {e : Fin m ≃ {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α}} {R : List (Comp (Atom 2 m))}
    {sy : Comp (Atom 3 N)} {X : List (Comp (Atom 3 N))} {ℓ : ℕ}
    (hαx : α ≠ x) (hαy : α ≠ y)
    (hsy : sy = mkC (.waved .s) (.inr y) (.inr α) ∨ sy = mkC (.waved .s) (.inr α) (.inr y))
    (hX : ∀ c ∈ X, c = mkC .xdot (.inr α) (.inl 1) ∨ c = mkC .xdot (.inl 1) (.inr α) ∨
      c = mkC .xdot (.inr α) (.inl 2) ∨ c = mkC .xdot (.inl 2) (.inr α))
    (hgp : Γ.comps.Perm (mkC (.theta []) (.inl 0) (.inr x) ::
      R.map (Comp.map (Sum.elim ![.inr x, .inr y] fun j => .inr (e j).1)) ++
      [sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++ X ++
      List.replicate ℓ (mkC .xdot (.inr α) (.inr α))))
    (hdot : ∀ c ∈ Γ.comps, c.kind ≠ .dot) (hLF : Γ.LabelFree) (hgs : gsPM' Γ) (hP : Γ.Plain)
    (h4 : 4 ≤ Γ.ord)
    {ψ : Atom 2 m → Atom 3 M} (hψR : ∀ w, (ψ w).isRight = true)
    (h01 : ψ (.inl 0) = ψ (.inl 1) ↔ x = y) (hinj : ∀ j j', ψ (.inr j) = ψ (.inr j') → j = j')
    (hne : ∀ j i, ψ (.inr j) ≠ ψ (.inl i)) (hN : N = M + 1) {Hc : List (Comp (Atom 2 m))}
    (hHc : Hc.Perm (R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))))
    {τc : List (Comp (Atom 3 1))}
    (hτc : τc = TEqIdentity_T1 ∨ τc = TEqIdentity_T2 ∨ τc = TEqIdentity_T3)
    (Γc : Graph 3 (M + 1))
    (hΓc : Γc.comps = liftCs 1 (mkC (.theta []) (.inl 0) (ψ (.inl 0)) :: Hc.map (Comp.map ψ)) ++
      τc.map (Comp.map (glueAtom (ψ (.inl 1)) (.inl 1) (.inl 2)))) :
    (Γ.ord + 1 ≤ Γc.ord ∧ Γc.ord ≤ Γ.ord + 2) ∧ Γc.LeafR ∧ Γc.LeafC ∧ Γc.Plain ∧
      Γc.DiagRecoll := by
  classical
  set Λc := TEqIdentity_Λc x y α e ψ with hΛcdef
  set φ := TEqIdentity_φ x y α e with hφdef
  set A : List (Comp (Atom 3 N)) := mkC (.theta []) (.inl 0) (.inr x) :: R.map (Comp.map φ) with hAdef
  set xh : Atom 3 (M + 1) := liftA 1 (ψ (.inl 0)) with hxhdef
  set yh : Atom 3 M := ψ (.inl 1) with hyhdef
  set τh := τc.map (Comp.map (glueAtom yh (.inl 1) (.inl 2))) with hτh
  have h01' : x = y → ψ (.inl 0) = ψ (.inl 1) := h01.2
  -- the components of the correction graph
  have hc0 : Γc.comps.Perm (A.map (Comp.map Λc) ++ (List.replicate ℓ (mkC .xdot xh xh) ++ τh)) := by
    rw [hΓc]
    exact TEqIdentity_corr_perm hαx hαy h01' hHc τc
  have hgp' : Γ.comps.Perm ([sy, mkC (.G .plus) (.inr α) (.inl 1), mkC (.G .minus) (.inr α) (.inl 2)] ++
      A ++ (X ++ List.replicate ℓ (mkC .xdot (.inr α) (.inr α)))) := by
    refine hgp.trans ?_
    rw [List.append_assoc _ X]
    exact List.perm_append_comm.append_right _
  -- the atom map
  have hΛinj : Function.Injective Λc := TEqIdentity_Λc_inj hαx hαy hψR h01 hinj hne
  have hΛl : ∀ a, Λc (.inl a) = .inl a := TEqIdentity_Λc_inl
  have hΛα : Λc (.inr α) = TEqIdentity_αc := TEqIdentity_Λc_α
  have hliftR : ∀ w : Atom 3 M, w.isRight = true → (liftA 1 w : Atom 3 (M + 1)).isRight = true := by
    rintro (a | a) h
    · simp at h
    · rfl
  have hΛr : ∀ a, (Λc (.inr a)).isRight = true := by
    intro a
    by_cases ha : a = α
    · rw [ha, hΛα]; rfl
    · rw [hΛcdef, TEqIdentity_Λc_ne ha]
      refine hliftR _ ?_
      unfold TEqIdentity_Λ; split_ifs <;> exact hψR _
  have hΛφ : ∀ w, Λc (φ w) = liftA 1 (ψ w) := TEqIdentity_Λc_φ hαx hαy h01'
  have hΛx : Λc (.inr x) = xh := hΛφ (.inl 0)
  have hΛy : Λc (.inr y) = liftA 1 yh := hΛφ (.inl 1)
  have hΛs : ∀ k, ∃ a, Λc (.inr a) = .inr k := by
    let lam : Fin N → Fin (M + 1) := fun a => Sum.elim (fun _ => 0) id (Λc (.inr a))
    have hlam : ∀ a, Λc (.inr a) = .inr (lam a) := by
      intro a
      have := hΛr a
      rcases h : Λc (.inr a) with b | b
      · rw [h] at this; cases this
      · simp [lam, h]
    have hinj' : Function.Injective lam := by
      intro a b hab
      have := hΛinj (show Λc (.inr a) = Λc (.inr b) by rw [hlam, hlam, hab])
      exact Sum.inr.inj this
    have hbij := (Fintype.bijective_iff_injective_and_card lam).2 ⟨hinj', by simp [hN]⟩
    intro k
    obtain ⟨a, ha⟩ := hbij.2 k
    exact ⟨a, by rw [hlam, ha]⟩
  have hxh : xh.isRight = true ∧ xh ≠ TEqIdentity_αc :=
    ⟨hliftR _ (hψR _), TEqIdentity_lift_ne_αc (hψR _)⟩
  have hyh : yh.isRight = true := hψR _
  -- the components of the host part
  have hRmem : ∀ r ∈ R, r.map φ ∈ Γ.comps := fun r hr =>
    hgp.mem_iff.2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_map_of_mem hr)))))
  have hAmem : ∀ a ∈ A, a ∈ Γ.comps := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hgp.mem_iff.2 (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ List.mem_cons_self)))
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
      exact hRmem r hr
  have hφR : ∀ w, (φ w).isRight = true := by
    rintro (i | j)
    · fin_cases i <;> simp [φ, TEqIdentity_φ]
    · rfl
  have hφ12 : ∀ w, φ w ≠ .inl 1 ∧ φ w ≠ .inl 2 := by
    intro w
    have := hφR w
    constructor <;> intro h <;> rw [h] at this <;> simp at this
  have hA'' : ∀ d ∈ A.map (Comp.map Λc), d = mkC (.theta []) (.inl 0) xh ∨
      (d.x.isRight = true ∧ d.y.isRight = true ∧ d.x ≠ TEqIdentity_αc ∧ d.y ≠ TEqIdentity_αc ∧
        d.kind ≠ .dot) := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hd
    rcases List.mem_cons.1 ha with rfl | ha'
    · left
      rw [TEqIdentity_mkC_map, hΛl, hΛx]
    · right
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha'
      have hk : r.kind ≠ .dot := hdot _ (hRmem r hr)
      rw [TEqIdentity_map_map]
      simp only [Comp.map, Function.comp_apply, hΛφ]
      exact ⟨hliftR _ (hψR _), hliftR _ (hψR _), TEqIdentity_lift_ne_αc (hψR _),
        TEqIdentity_lift_ne_αc (hψR _), hk⟩
  have hΘA : mkC (.theta []) (.inl 0) xh ∈ A.map (Comp.map Λc) := by
    refine List.mem_map.2 ⟨_, List.mem_cons_self, ?_⟩
    rw [TEqIdentity_mkC_map, hΛl, hΛx]
  have hA : ∀ a ∈ A, a.kind ≠ .dot ∧ a.x ≠ .inl 1 ∧ a.x ≠ .inl 2 ∧ a.y ≠ .inl 1 ∧
      a.y ≠ .inl 2 := by
    intro a ha
    refine ⟨hdot a (hAmem a ha), ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp [mkC]
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha'
      exact ⟨(hφ12 r.x).1, (hφ12 r.x).2, (hφ12 r.y).1, (hφ12 r.y).2⟩
  have hBt : ∀ c ∈ X ++ List.replicate ℓ (mkC .xdot (.inr α) (.inr α)), c.kind = .xdot := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · rcases hX c hc with rfl | rfl | rfl | rfl <;> rfl
    · rw [List.eq_of_mem_replicate hc]; rfl
  -- the clauses
  have hgs' := TEqIdentity_gs hgs hgp' hc0 hA'' hxh hyh hτc hsy hA hdot hBt hΛinj hΛl hΛr hΛs hΛα
    hΛy
  have hTD := TEqIdentity_td hc0 hA'' hxh hyh hτc
  have hDE := TEqIdentity_dotExcess hc0 hA'' hxh hyh hτc
  have hRc := TEqIdentity_recoll hc0 hA'' hxh hyh hτc
  have hDg := TEqIdentity_diag hc0 hA'' hxh hyh hτc
  have hEC := TEqIdentity_extClause hc0 hA'' hxh hyh hτc hΘA
  have hCI := TEqIdentity_colourInvB hc0 hA'' hxh hyh hτc
  have hmem := TEqIdentity_mem hc0
  obtain ⟨t1, t2, t3⟩ := TEqIdentity_tauhat (M := M) yh
  -- no labels, plain
  have hLFc : Γc.LabelFree := by
    intro d hd
    rcases (hmem d).1 hd with h | ⟨rfl, -⟩ | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
      simp [Comp.map, hLF a (hAmem a ha)]
    · rfl
    · rcases hτc with rfl | rfl | rfl
      · rw [t1] at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
      · rw [t2] at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
      · rw [t3] at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hPc : Γc.Plain := by
    intro d hd
    rcases (hmem d).1 hd with h | ⟨rfl, -⟩ | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
      obtain ⟨h1, h2, h3, -, h5⟩ := hP a (hAmem a ha)
      refine ⟨by simp [Comp.map, h1], h2, h3, fun hk => absurd hk (hdot a (hAmem a ha)),
        fun hw => ?_, fun hl => ?_⟩
      · simp only [Comp.map] at hw ⊢
        rw [h5.1 hw]
      · simp [Comp.map, hLF a (hAmem a ha)] at hl
    · exact ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC], by simp [mkC], by simp [mkC]⟩
    · have hne' : ∀ a : Fin 3, (TEqIdentity_αc : Atom 3 (M + 1)) ≠ .inl a := by simp
      rcases hτc with rfl | rfl | rfl
      · rw [t1] at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC, hne'], by simp [mkC, Kind.isWeight],
            by simp [mkC]⟩
      · rw [t2] at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC, hne'], by simp [mkC, Kind.isWeight],
            by simp [mkC]⟩
      · rw [t3] at h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC, hne'], by simp [mkC, Kind.isWeight],
            by simp [mkC]⟩
  -- the scaling order
  have hsumc : (Γc.comps.map fun c => c.kind.ord).sum = (A.map fun c => c.kind.ord).sum +
      (τh.map fun c => c.kind.ord).sum := by
    rw [(hc0.map _).sum_eq]
    simp only [List.map_append, List.sum_append, List.map_map, List.map_replicate,
      List.sum_replicate]
    simp [Function.comp_def, Comp.map, mkC, Kind.ord]
  have hsum0 : (Γ.comps.map fun c => c.kind.ord).sum = 4 + (A.map fun c => c.kind.ord).sum := by
    rw [(hgp'.map _).sum_eq]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have hB0 : ((X ++ List.replicate ℓ (mkC .xdot (.inr α) (.inr α) : Comp (Atom 3 N))).map
        fun c => c.kind.ord).sum = 0 := by
      refine List.sum_eq_zero fun z hz => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
      rw [hBt c hc]; rfl
    rw [List.map_append, List.sum_append] at hB0
    rcases hsy with rfl | rfl <;> simp [mkC, Kind.ord] at hB0 ⊢ <;> linarith
  have hτsum : (τh.map fun c => c.kind.ord).sum = 5 ∨ (τh.map fun c => c.kind.ord).sum = 6 := by
    rw [hτh]
    rcases hτc with rfl | rfl | rfl
    · left; rw [t1]; simp [mkC, Kind.ord]
    · left; rw [t2]; simp [mkC, Kind.ord]
    · right; rw [t3]; simp [mkC, Kind.ord]
  have hordc : Γc.ord = (A.map fun c => c.kind.ord).sum + (τh.map fun c => c.kind.ord).sum -
      2 * (M + 1 : ℕ) := by
    unfold Graph.ord; rw [hsumc]
  have hord0 : Γ.ord = 4 + (A.map fun c => c.kind.ord).sum - 2 * N := by
    unfold Graph.ord; rw [hsum0]
  have hwin : Γ.ord + 1 ≤ Γc.ord ∧ Γc.ord ≤ Γ.ord + 2 := by
    have hN' : (N : ℤ) = M + 1 := by exact_mod_cast hN
    rw [hordc, hord0]
    push_cast
    rcases hτsum with h | h <;> rw [h] <;> constructor <;> linarith
  refine ⟨hwin, ⟨hRc, hLFc, hgs', hEC, hCI, fun _ => by linarith [hwin.1]⟩,
    ⟨hTD, hDE, fun d hd _ => hLFc d hd, by rw [TEqIdentity_labels_nil hLFc]; simp⟩, hPc, hDg⟩

/-- The number of internal atoms other than three distinct atoms. -/
private theorem TEqIdentity_card3 {N : ℕ} {x y α : Fin N} (hxy : x ≠ y) (hαx : α ≠ x)
    (hαy : α ≠ y) : Fintype.card {a : Fin N // a ≠ x ∧ a ≠ y ∧ a ≠ α} + 3 = N := by
  classical
  rw [Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun a => a ≠ x ∧ a ≠ y ∧ a ≠ α)
  have h3 : (Finset.univ.filter fun a : Fin N => ¬ (a ≠ x ∧ a ≠ y ∧ a ≠ α)) = {x, y, α} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  rw [h3, Finset.card_univ, Fintype.card_fin] at h
  have hc : ({x, y, α} : Finset (Fin N)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, Ne.symm hαx]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hαy]), Finset.card_singleton]
  omega

/-- The number of internal atoms other than two distinct atoms. -/
private theorem TEqIdentity_card2 {N : ℕ} {x α : Fin N} (hαx : α ≠ x) :
    Fintype.card {a : Fin N // a ≠ x ∧ a ≠ x ∧ a ≠ α} + 2 = N := by
  classical
  rw [Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun a => a ≠ x ∧ a ≠ x ∧ a ≠ α)
  have h3 : (Finset.univ.filter fun a : Fin N => ¬ (a ≠ x ∧ a ≠ x ∧ a ≠ α)) = {x, α} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  rw [h3, Finset.card_univ, Fintype.card_fin] at h
  have hc : ({x, α} : Finset (Fin N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hαx]), Finset.card_singleton]
  omega

/-- **The classes of the correction graphs of an output graph in the leaf form** (the `t → T`
rewriting before [II, (6.7)], with [II, (4.15)]): for an output graph `g` in the leaf form
`TEqSigma.LeafOf g S`, without dotted edges or labels, globally standard and plain, of scaling
order `≥ 4`, every graph of `TEqShape_corrOf ⟨m, S⟩` has scaling order `ord g + 1` or
`ord g + 2`, is of the class `Graph.LeafR` with the clauses `Graph.LeafC`, is plain, has an
internal atom in the block of `⊕` or `⊖`, and has an internal atom. -/
private theorem TEqIdentity_corr_leaf {g : Σ m, Graph 3 m} {m : ℕ} {S : Graph 2 m}
    (hL : TEqSigma.LeafOf g S) (hdot : ∀ c ∈ g.2.comps, c.kind ≠ .dot) (hLF : g.2.LabelFree)
    (hgs : gsPM' g.2) (hP : g.2.Plain) (h4 : 4 ≤ g.2.ord) :
    ∀ c ∈ TEqShape_corrOf ⟨m, S⟩, (g.2.ord + 1 ≤ c.2.ord ∧ c.2.ord ≤ g.2.ord + 2) ∧
      c.2.LeafR ∧ c.2.LeafC ∧ c.2.Plain ∧ c.2.DiagRecoll ∧ c.1 ≠ 0 := by
  classical
  obtain ⟨N, Γ⟩ := g
  obtain ⟨x, y, α, e, R, sy, X, ℓ, hαx, hαy, hsy, hX, -, -, hgp, hSp, -⟩ := hL
  intro c hc
  unfold TEqShape_corrOf at hc
  simp only at hc
  split_ifs at hc with hd
  · -- `x = y`
    have hxy : x = y := by
      by_contra hxy
      rw [if_neg hxy, List.nil_append] at hSp
      rcases List.mem_append.1 (hSp.mem_iff.1 hd) with h | h
      · have := hdot _ (hgp.mem_iff.2 (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem h))))))
        exact this rfl
      · rw [List.eq_of_mem_replicate h] at hd
        have := List.eq_of_mem_replicate h
        simp [mkC] at this
    subst hxy
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hc
    obtain ⟨t, rfl, ht⟩ := TEqIdentity_tVarCorr_cases τ hτ
    have hHc : (S.comps.erase (mkC .dot (.inl 0) (.inl 1))).Perm
        (R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))) := by
      rw [if_pos rfl] at hSp
      exact (List.perm_cons_erase hd).symm.trans hSp |>.cons_inv
    have hN : N = 1 + m + 1 := by
      have := TEqIdentity_card2 hαx
      rw [← Fintype.card_congr e, Fintype.card_fin] at this
      simp only at this
      omega
    have hm := TEqIdentity_corr_main (Γ := Γ) (e := e) hαx hαy hsy hX hgp hdot hLF hgs hP h4
      (ψ := Sum.elim (fun _ => (.inr 0 : Atom 3 (1 + m))) fun j => .inr (Fin.natAdd 1 j))
      (fun w => by rcases w with _ | _ <;> rfl) (by simp)
      (fun j j' h => by simpa using h)
      (fun j i h => by simp [Fin.ext_iff] at h)
      hN hHc ht ((TEqShape_thetaS₁ S).glue (.inr 0) (.inl 1) (.inl 2) t) rfl
    exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, by simp⟩
  · -- `x ≠ y`
    have hxy : x ≠ y := by
      rintro rfl
      exact hd (hSp.mem_iff.2 (by simp))
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hc
    obtain ⟨t, rfl, ht⟩ := TEqIdentity_tVarCorr_cases τ hτ
    have hHc : S.comps.Perm (R ++ List.replicate ℓ (mkC .xdot (.inl 0) (.inl 0))) := by
      rw [if_neg hxy, List.nil_append] at hSp
      exact hSp
    have hN : N = 2 + m + 1 := by
      have := TEqIdentity_card3 hxy hαx hαy
      rw [← Fintype.card_congr e, Fintype.card_fin] at this
      simp only at this
      omega
    have h0 : (Fin.castAdd m 0 : Fin (2 + m)) = 0 := Fin.ext (by simp)
    have h1 : (Fin.castAdd m 1 : Fin (2 + m)) = 1 :=
      Fin.ext (by simpa [Fin.val_one'] using (Nat.mod_eq_of_lt (show 1 < 2 + m by omega)).symm)
    have hm := TEqIdentity_corr_main (Γ := Γ) (e := e) hαx hαy hsy hX hgp hdot hLF hgs hP h4
      (ψ := Sum.elim (fun i => (.inr (Fin.castAdd m i) : Atom 3 (2 + m)))
        fun j => .inr (Fin.natAdd 2 j))
      (fun w => by rcases w with _ | _ <;> rfl)
      (by simp [Fin.ext_iff, hxy])
      (fun j j' h => by simpa using h)
      (fun j i h => by simp [Fin.ext_iff] at h; have := i.2; omega)
      hN hHc ht ((TEqShape_thetaS S).glue (.inr 1) (.inl 1) (.inl 2) t)
      (by simp only [Graph.glue, TEqShape_thetaS, Sum.elim_inl, h0, h1])
    exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, by simp⟩

/-- **The classes of the correction graphs** ([II, (6.7)–(6.8)], [II, (4.15)], [II, Def 6.3]):
for `n ≥ 3` and a record `𝒯` that is the structural part of an `(n - 1)`-th order `T`-expansion
with error order `D`, for every output graph `g` of the run of [II, Strategy 6.6] of the class
`Graph.LeafDet`, not a `⊕/⊖`-recollision graph, of scaling order `≤ n`, every graph `c` of
`TEqSigma.corr g` has scaling order `ord g + 1` or `ord g + 2`; of order `≤ n` it has the clauses
read by `TRec.def63_of_leaves` on `R` (`Graph.LeafR`, `Graph.LeafC`, `Graph.Plain`); of order
`> n` those read on `A` (`Graph.LeafA n`, `Graph.LeafC`, rooted at the external atoms unless a
`⊕`-recollision graph at `𝔟₁ = 𝔟₂`, `Graph.Plain`, and the profile at `⊖` without internal
atom). -/
theorem TEqSigma.corr_classes : ∀ (n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 3 ≤ n →
    𝒯.IsTExpStruct Sig (n - 1) D → ∀ g ∈ RunCompare.run TEqSigma.qFam n D 𝒯, g.2.LeafDet →
    ¬ g.2.IsRecollision {1, 2} → g.2.ord ≤ n → ∀ c ∈ TEqSigma.corr g,
      (g.2.ord + 1 ≤ c.2.ord ∧ c.2.ord ≤ g.2.ord + 2) ∧
      (c.2.ord ≤ n → c.2.LeafR ∧ c.2.LeafC ∧ c.2.Plain) ∧
      ((n : ℤ) < c.2.ord → c.2.LeafA n ∧ c.2.LeafC ∧ (c.1 ≠ 0 → ¬ c.2.DiagRecoll → c.2.RootedAtExt) ∧
        c.2.Plain ∧ (c.1 = 0 → c.2.MinusProfile)) := by
  intro n D Sig 𝒯 hn hT g hg hdet hNR hord c hc
  obtain ⟨m, 𝒮, hσ, hL, -, -, h4⟩ := TEqSigma.detLeaf_form n D Sig 𝒯 hn hT g hg hdet hNR hord
  have hdot := TEqSigma.detLeaf_dotFree n D Sig 𝒯 hn hT g hg hdet hNR hord
  obtain ⟨hL', -, -⟩ := TEqSigma.normS_leafOf hL hdot
  obtain ⟨S', hS'⟩ : ∃ S' : Graph 2 m, TEqSigma.normS ⟨m, 𝒮⟩ = ⟨m, S'⟩ := ⟨_, rfl⟩
  rw [hS'] at hL'
  have hc' : c ∈ TEqShape_corrOf ⟨m, S'⟩ := by
    unfold TEqSigma.corr at hc
    rw [if_pos ⟨hdet, hNR⟩, TEqSigma.sigma', hσ, List.map_singleton, hS', List.flatMap_cons,
      List.flatMap_nil, List.append_nil] at hc
    exact hc
  have hnD : n ≤ D := by have := hT.1; omega
  obtain ⟨-, -, -, -, hPl, -⟩ :=
    (RunCompare.run_spec TEqSigma.qFam TEqSigma.qFam_spec n D Sig 𝒯 hn hT).2.2 g hg
  have hP : g.2.Plain := hPl (by omega)
  obtain ⟨hw, hR, hC, hPc, hDg, hc1⟩ :=
    TEqIdentity_corr_leaf hL' hdot hdet.1 hdet.2.1 hP h4 c hc'
  exact ⟨hw, fun _ => ⟨hR, hC, hPc⟩, fun hn' => ⟨TEqIdentity_leafA_of_leafR hR hn', hC,
    fun _ hnd => absurd hDg hnd, hPc, fun h0 => absurd h0 hc1⟩⟩

end Main

section Instances

end Instances

end RBM8D.Graphs
