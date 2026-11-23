module

public import Batteries.Tactic.OpenPrivate
public import RBM8D.Diffusion.ErrExp
public import RBM8D.Diffusion.ErrForms
public import RBM8D.LocalLaw.LabelPaths
public import RBM8D.Diffusion.ErrBound
public import RBM8D.Bound.Doubly
public import RBM8D.SelfEnergy.MainCancel
import all RBM8D.Diffusion.ErrBound
import all RBM8D.Bound.Doubly
import all RBM8D.SelfEnergy.MainCancel

@[expose] public section

/-!
# The error of the `n`-th order `T`-equation: [I, (8.17)]

`errBound : errBoundStmt`: under the local law [I, Theorem 1.4], for an `n`-th order `T`-equation
`𝒬` with error order `D ≥ n + 2` ([II, Def 3.3], [II, Def 6.3]), the expectation of the graphs of
`A` in which `⊕`, `⊖` do not lie in one dotted block and of the graphs of `Err`, rooted at
`(x, 𝔟, 𝔟)` ([I, (8.14)–(8.15)]), satisfies `|E Γ_{x, 𝔟𝔟}| ≤ W^τ W^{−(n−1)d/2}` and
`Σ_x B_{𝔞x} |E Γ_{x, 𝔟𝔟}| ≤ W^τ W^{−(n+1)d/2}` ([I, (8.17)] with [I, (8.20)]).

For one graph `g`, the expectation step `ErrExp.expBound` ([II, Claims 8.6, 8.7]) reduces the bound
to a deterministic bound `β` of the absolute-value graphs of the label-free graphs `Γ_S` of the
light-weight graph of the rooted graph `Γ = 𝒢_{x, 𝔟₁𝔟₂}`, at every single matrix `G̃` with
`|G̃ − m δ| ≤ W^{τ'} B^{1/2}`. This file supplies `β`:

* the rooted graph commutes with the light weights of `W_d` and with the replacement of labelled
  components by paths through their label atoms: the absolute-value graph of `Γ_S` is that of the
  rooted graph of `g_S`, the label-free graph of the light-weight graph of `g`, for a set of
  replaceable components of `g` (the label atom of a replaceable component of `Γ` lies in a
  dotted block of `Γ` without external atom, so also in `g`);
* `g_S` is normal regular, doubly connected, with the kinds of [II, Def 3.2], diagonal scaling
  order at least that of `g` (`labelPaths`), rooted at its root edge, and its root atom is
  internal or `𝔟` lies in a waved or dotted block of the core, with a solid or diffusive tip
  otherwise (from `Graph.RootedAtExt` and `Graph.DiagRecoll`);
* the forms of [I, (8.20)] bound the absolute-value graph of the rooted graph of `g_S`:
  `𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{−(n_𝔟 − 1)d/2} B^{1/2}_{x𝔟} + 1_{x = 𝔟} W^τ W^{−(n_𝔟 − 2)d/2}`, with
  the bounds [I, Lemma 6.10, (6.20)–(6.21)] of the pinned graphs and the convolutions of `B`.

With `n_𝔟 ≥ n + 1`, the sum over the graphs and the convolution
`Σ_x B_{𝔞x} B^{1/2}_{x𝔟} ≲ W^{−d/2} log(L/W)` give the two bounds of `errBoundStmt`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

open private comp_val_congr comp_val_map rootRest_eq isTKind_map succAbove_finDrop
  from RBM8D.Diffusion.ErrBound
open private bB_pos₁ gData_inputs im_pos_of_specDom from RBM8D.Bound.Doubly
open private MainCancel_valR_integrable_err from RBM8D.SelfEnergy.MainCancel

open ErrForms

/-! ## The absolute-value graph of the rooted graph -/

section AbsRoot

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Components that do not read `⊗` have the same factors at two labellings that agree away from
`⊗`. -/
private theorem ErrMain_map_congr (D : Data ι) (l : List (Comp (Atom 3 n)))
    (hl : ∀ c ∈ l, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor) (σ τ : Atom 3 n → ι)
    (h : ∀ u, u ≠ .inl 0 → σ u = τ u) :
    (l.map fun c => ‖Comp.val D σ c‖) = l.map fun c => ‖Comp.val D τ c‖ := by
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨hx, hy, hm⟩ := hl c hc
  rw [comp_val_congr D σ τ c (h _ hx) (h _ hy) fun u hu => h u fun e => hm (e ▸ hu)]

/-- `(x, 𝔟, 𝔟; s)` and `(𝔟, 𝔟, 𝔟; s)` agree away from `⊗`. -/
private theorem ErrMain_elim_bbb {α : Type*} (x b : α) (s : Fin n → α) (u : Atom 3 n)
    (hu : u ≠ .inl 0) :
    Sum.elim ![x, b, b] s u = Sum.elim (fun _ => b) s u := by
  rcases u with a | i
  · fin_cases a
    exacts [absurd rfl hu, rfl, rfl]
  · rfl

/-- The atom map of `Graph.rootAt i`: the internal atom `i` becomes the external atom `x = 0`. -/
private def ErrMain_rootMap {m : ℕ} (i : Fin (m + 1)) : Atom 3 (m + 1) → Atom 3 m
  | .inl j => .inl j
  | .inr j => if h : j = i then .inl 0 else .inr (finDrop i j h)

/-- `Graph.rootAt i` is the image under `ErrMain_rootMap i`. -/
private theorem ErrMain_rootAt_eq {m : ℕ} (H : Graph 3 (m + 1)) (i : Fin (m + 1)) :
    (H.rootGraph (.inr i)).2 = (H.mapAtoms (ErrMain_rootMap i) : Graph 3 m) := by
  simp only [Graph.rootGraph, Graph.rootAt]
  unfold Graph.mapAtoms
  congr 2
  funext c
  congr
  funext u
  rcases u with a | k <;> rfl

/-- **[I, (8.20)] on `𝒢^{abs}`**: if no component of `H` reads `⊗` and `v ≠ ⊗`, then
`(H.rootGraph v)^{abs}` at `(x, 𝔟, 𝔟)` is `Σ_s |1_{s_v = x}|` (`|1_{x = 𝔟}|` for `v ∈ {⊕, ⊖}`) times
the absolute values of the coefficient and of the components of `H` read with `⊕ = ⊖ = 𝔟`. -/
private theorem ErrMain_absVal_rootGraph (H : Graph 3 n) (v : Atom 3 n) (hv : v ≠ .inl 0)
    (hH : ∀ c ∈ H.comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor) (D : Data ι)
    (x b : ι) :
    (H.rootGraph v).2.absVal D ![x, b, b] = ∑ s : Fin n → ι, ‖ErrBound.rootInd v x b s‖ *
      (‖H.coeff.eval D.m‖ *
        (H.comps.map fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod) := by
  rcases v with a | i
  · have ha : (![x, b, b] : Fin 3 → ι) a = b := by
      fin_cases a
      · exact absurd rfl hv
      · rfl
      · rfl
    simp only [Graph.rootGraph, Graph.absVal, ErrBound.rootInd]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [List.map_append, List.prod_append,
      ErrMain_map_congr D H.comps hH _ _ (ErrMain_elim_bbb x b s)]
    have hdot : Comp.val D (Sum.elim ![x, b, b] s) (mkC .dot (.inl 0) (.inl a)) =
        if x = b then 1 else 0 := by
      simp [Comp.val, mkC, ha]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hdot]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    set F : (Fin (m + 1) → ι) → ℝ := fun s => ‖H.coeff.eval D.m‖ *
      (H.comps.map fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod with hF
    have hσ : ∀ s' : Fin m → ι, ∀ u : Atom 3 (m + 1), u ≠ .inl 0 →
        Sum.elim ![x, b, b] s' (ErrMain_rootMap i u) =
          Sum.elim (fun _ => b) (Fin.insertNth i x s') u := by
      intro s' u hu
      rcases u with a' | k
      · exact ErrMain_elim_bbb x b s' (.inl a') fun h => hu (by cases h; rfl)
      · by_cases hk : k = i
        · subst hk
          simp only [ErrMain_rootMap, dite_true, Sum.elim_inl]
          exact (Fin.insertNth_apply_same (α := fun _ => ι) k x s').symm
        · simp only [ErrMain_rootMap, hk, dite_false, Sum.elim_inr]
          conv_rhs => rw [← succAbove_finDrop i k hk]
          exact (Fin.insertNth_apply_succAbove (α := fun _ => ι) i x s' _).symm
    have hL : (H.rootGraph (.inr i)).2.absVal D ![x, b, b] =
        ∑ s' : Fin m → ι, F (Fin.insertNth i x s') := by
      have e : (H.rootGraph (.inr i)).2.absVal D ![x, b, b] = ∑ s' : Fin m → ι,
          ‖H.coeff.eval D.m‖ * ((H.comps.map (Comp.map (ErrMain_rootMap i))).map
            fun c => ‖Comp.val D (Sum.elim ![x, b, b] s') c‖).prod :=
        (congrArg (fun G => Graph.absVal G D ![x, b, b]) (ErrMain_rootAt_eq H i)).trans rfl
      rw [e]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [List.map_map, hF]
      congr 2
      refine List.map_congr_left fun c hc => ?_
      simp only [Function.comp_apply]
      rw [comp_val_map]
      obtain ⟨hx, hy, hm⟩ := hH c hc
      exact congrArg norm (comp_val_congr D _ _ c (hσ s' _ hx) (hσ s' _ hy)
        fun u hu => hσ s' u fun e => hm (e ▸ hu))
    rw [hL]
    symm
    calc ∑ s : Fin (m + 1) → ι, ‖ErrBound.rootInd (.inr i) x b s‖ * F s
        = ∑ p : ι × (Fin m → ι), ‖ErrBound.rootInd (.inr i) x b (Fin.insertNth i p.1 p.2)‖ *
            F (Fin.insertNth i p.1 p.2) :=
          ((Fin.insertNthEquiv (fun _ => ι) i).sum_comp fun s =>
            ‖ErrBound.rootInd (.inr i) x b s‖ * F s).symm
      _ = ∑ s' : Fin m → ι, F (Fin.insertNth i x s') := by
          rw [Fintype.sum_prod_type]
          simp [ErrBound.rootInd, apply_ite]

/-- **The absolute-value form**: `𝒢^{abs}_{x, 𝔟𝔟}` is `Σ_s |1_{s_v = x}|`
times the absolute values of the coefficient and of the components of `g` not at `⊗`. -/
private theorem ErrMain_rootAbs {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v) (D : Data ι) (x b : ι) :
    (rootRest g).2.absVal D ![x, b, b] = ∑ s : Fin n → ι, ‖ErrBound.rootInd v x b s‖ *
      (‖g.coeff.eval D.m‖ * ((g.comps.filter fun c => !atT c).map
        fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod) := by
  rw [rootRest_eq g j v hR.kind hR.ends fun c hc => (hR.rest c hc).1,
    ErrMain_absVal_rootGraph _ v hR.ne hR.rest]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [((filter_atT_perm hR).map _).prod_eq]
  rfl

/-- **The absolute-value form**: the absolute-value graph of the
rooted graph with the dotted edges split off. -/
private theorem ErrMain_rootAbs_split {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v)
    (hdot : ∀ c ∈ g.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    (D : Data ι) (x b : ι) :
    (rootRest g).2.absVal D ![x, b, b] = ∑ s : Fin n → ι, ‖ErrBound.rootInd v x b s‖ *
      ((if ∀ i, dotB g i = true → s i = b then 1 else 0) * (‖g.coeff.eval D.m‖ *
        ((g.comps.filter fun c => nd c && !atT c).map
          fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod)) := by
  rw [ErrMain_rootAbs hR D x b]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  set l := g.comps.filter fun c => !atT c
  have hp := List.filter_append_perm (fun c => !nd c) l
  have e1 : l.filter (fun c => !nd c) = g.comps.filter (fun c => !nd c && !atT c) := by
    rw [List.filter_filter]
  have e2 : l.filter (fun c => !!nd c) = g.comps.filter (fun c => nd c && !atT c) := by
    rw [List.filter_filter]; simp
  rw [e1, e2] at hp
  have hd : ((g.comps.filter fun c => !nd c && !atT c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod =
      if ∀ i, dotB g i = true → s i = b then 1 else 0 := by
    rw [show ∀ l : List (Comp (Atom 3 n)), (l.map fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖)
      = (l.map (Comp.val D (Sum.elim (fun _ => b) s))).map norm from fun l => by simp,
      ← List.norm_prod, prod_dots D _ _ fun c hc =>
      (by simpa [nd] using (List.mem_filter.1 hc).2 : _ ∧ _).1,
      if_congr (dots_iff hR hdot b s) rfl rfl]
    split_ifs <;> simp
  rw [← (hp.map _).prod_eq, List.map_append, List.prod_append, hd]
  ring

/-- **The absolute-value form**: for a root atom `v` internal and not
dotted, `𝒢^{abs}_{x, 𝔟𝔟} = (gB2)^{abs}_{x𝔟}`. -/
private theorem ErrMain_absVal_gB2 {g : Graph 3 n} {j : Fin g.comps.length} {v : Fin n}
    (hR : Rooted g j (.inr v))
    (hdot : ∀ c ∈ g.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    (hv : dotB g v = false) (D : Data ι) (x b : ι) :
    (rootRest g).2.absVal D ![x, b, b] = (gB2 g (.inr v)).absVal D ![x, b] := by
  rw [ErrMain_rootAbs_split hR hdot D x b, gB2, absVal_pin]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hC : (∀ i a, pB g (.inr v) 1 0 i = some a → s i = ![x, b] a) ↔
      s v = x ∧ ∀ i, dotB g i = true → s i = b := by
    constructor
    · intro h
      refine ⟨h v 0 (by simp [pB, hv]), fun i hi => h i 1 (by simp [pB, hi])⟩
    · rintro ⟨h1, h2⟩ i a ha
      simp only [pB] at ha
      split_ifs at ha with h3 h4
      · cases ha; exact h2 i h3
      · cases ha
        cases h4
        exact h1
  simp only [ErrBound.rootInd, if_congr hC rfl rfl]
  have hb : (![x, b] : Fin 2 → ι) 1 = b := rfl
  rw [hb]
  by_cases h1 : s v = x <;> by_cases h2 : ∀ i, dotB g i = true → s i = b <;> simp [h1, h2]

/-- **The absolute-value form**: for `v ∈ {⊕, ⊖}`, or `v` internal and
dotted, `𝒢^{abs}_{x, 𝔟𝔟} = 1_{x = 𝔟} (gB1)^{abs}_𝔟`. -/
private theorem ErrMain_absVal_gB1 {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n}
    (hR : Rooted g j v)
    (hdot : ∀ c ∈ g.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    (hv : ∀ i, v = .inr i → dotB g i = true) (D : Data ι) (x b : ι) :
    (rootRest g).2.absVal D ![x, b, b] = (if x = b then 1 else 0) * (gB1 g v).absVal D ![b] := by
  rw [ErrMain_rootAbs_split hR hdot D x b, gB1, absVal_pin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hC : (∀ i a, pB g v 0 0 i = some a → s i = ![b] a) ↔ ∀ i, dotB g i = true → s i = b := by
    constructor
    · intro h i hi
      exact h i 0 (by simp [pB, hi])
    · intro h i a ha
      have ha0 : a = 0 := Subsingleton.elim _ _
      subst ha0
      simp only [pB] at ha
      split_ifs at ha with h3 h4
      · exact h i h3
      · exact h i (hv i h4.symm)
  rw [if_congr hC rfl rfl]
  have hb : (![b] : Fin 1 → ι) 0 = b := rfl
  rw [hb]
  rcases v with a | i
  · simp only [ErrBound.rootInd]
    by_cases h2 : ∀ i, dotB g i = true → s i = b <;> by_cases h1 : x = b <;> simp [h1, h2]
  · have hdi := hv i rfl
    simp only [ErrBound.rootInd]
    by_cases h2 : ∀ i, dotB g i = true → s i = b
    · have := h2 i hdi
      by_cases h1 : x = b
      · subst h1; simp [this]
      · have : s i ≠ x := fun h => h1 (h ▸ this)
        simp [this, h1]
    · simp [h2]

/-- **The absolute-value form**: a pinned graph with a
`×`-dotted edge whose ends are pinned to one atom has absolute-value graph `0`. -/
private theorem ErrMain_absVal_pin_eq_zero {k : ℕ} (g : Graph 3 n) (p : Comp (Atom 3 n) → Bool)
    (β : Fin k) (P : Fin n → Option (Fin k))
    (h : ∃ c ∈ g.comps, (p c && !atT c) = true ∧ c.kind = .xdot ∧
      pinAtom β P c.x = pinAtom β P c.y) (D : Data ι) (e : Fin k → ι) :
    (pin g p β P).absVal D e = 0 := by
  obtain ⟨c, hc, hp, hk, he⟩ := h
  refine Finset.sum_eq_zero fun t _ => ?_
  refine mul_eq_zero_of_right _ (List.prod_eq_zero (List.mem_map.2 ⟨c.map (pinAtom β P),
    List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hp⟩, rfl⟩, ?_⟩))
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp only at hk he
  subst hk
  simp [Comp.val, Comp.map, he]

/-- **The absolute-value form** (root atom `v` internal): the
components between internal atoms and the components at `⊕`, `⊖`, over the labels with `s_v = x`. -/
private theorem ErrMain_rootAbs_le {g : Graph 3 n} {j : Fin g.comps.length} {v : Fin n}
    (hR : Rooted g j (.inr v)) (D : Data ι) (x b : ι) :
    (rootRest g).2.absVal D ![x, b, b] ≤ ∑ s : Fin n → ι, (if s v = x then 1 else 0) *
      ((‖g.coeff.eval D.m‖ * ((g.comps.filter fun c => bi c && !atT c).map
          fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod) *
        ((g.comps.filter fun c => extC c).map
          fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod) := by
  rw [ErrMain_rootAbs hR D x b]
  refine Finset.sum_le_sum fun s _ => ?_
  set l := g.comps.filter fun c => !atT c
  have hp := List.filter_append_perm (fun c => bi c) l
  have e1 : l.filter (fun c => bi c) = g.comps.filter (fun c => bi c && !atT c) := by
    rw [List.filter_filter]
  have e2 : l.filter (fun c => !bi c) = g.comps.filter (fun c => extC c) := by
    rw [List.filter_filter]; rfl
  rw [e1, e2] at hp
  rw [← (hp.map _).prod_eq, List.map_append, List.prod_append]
  have hr : ‖ErrBound.rootInd (.inr v) x b s‖ = if s v = x then 1 else 0 := by
    simp only [ErrBound.rootInd]; split_ifs <;> simp
  rw [hr]
  apply le_of_eq
  ring

end AbsRoot

/-! ## The forms of [I, (8.20)] on the absolute-value graph -/

section Forms

variable {n : ℕ}

/-- For some `τ' > 0`, `W₀`: on `adm(c₀, c₁)` with `W ≥ W₀`, `z ∈ 𝐃(κ, ε)` and
`|G_{pq} − δ_{pq} m| ≤ W^{τ'} B^{1/2}_{pq}`, `𝒢^{abs}_{x, 𝔟𝔟} ≤ F(W, L, x, 𝔟)` on `gData`. -/
private abbrev ErrMain_AbsBd (d : ℕ) (P : Profile d) (c₀ c₁ κ ε : ℝ) (Sig : ℕ → Expansion 2)
    {n : ℕ} (g : Graph 3 n) (F : ∀ (_W L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ) : Prop :=
  ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
    ∀ z ∈ specDom κ ε W L, ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
      (∀ p q, ‖entryErr G (msc z) p q‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W p q)) →
      ∀ x b : Zd d L, (rootRest g).2.absVal (gData (Smat P.ψ W L) z Sig G) ![x, b, b] ≤ F W L x b

/-- **The absolute-value form** (first form of [I, (8.20)]):
components at `⊕`, `⊖` at most `T(s_y, 𝔟)` give `𝒢^{abs}_{x, 𝔟𝔟} ≤ Σ_{y'} T(y', 𝔟) |gA2|_{x y'}`. -/
private theorem ErrMain_A2Abs {ι : Type} [Fintype ι] [DecidableEq ι] {g : Graph 3 n}
    {j : Fin g.comps.length} {v y : Fin n} (hR : Rooted g j (.inr v)) (hvy : v ≠ y)
    (hmin : ∀ c ∈ g.comps, c.minor = []) (D : Data ι) (x b : ι) (T : ι → ι → ℝ)
    (hT : ∀ s : Fin n → ι, ((g.comps.filter fun c => extC c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod ≤ T (s y) b) :
    (rootRest g).2.absVal D ![x, b, b] ≤ ∑ y' : ι, T y' b * (gA2 g v y).absVal D ![x, y'] := by
  refine (ErrMain_rootAbs_le hR D x b).trans ?_
  set F : (Fin n → ι) → ℝ := fun s => ‖g.coeff.eval D.m‖ *
    ((g.comps.filter fun c => bi c && !atT c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod with hF
  have hF0 : ∀ s, 0 ≤ F s := fun s => mul_nonneg (norm_nonneg _)
    (List.prod_nonneg fun a ha => by obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact norm_nonneg _)
  have hcongr : ∀ (f : Fin 3 → ι) (s : Fin n → ι), ((g.comps.filter fun c => bi c && !atT c).map
        fun c => ‖Comp.val D (Sum.elim f s) c‖).prod =
      ((g.comps.filter fun c => bi c && !atT c).map
        fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod := by
    intro f s
    congr 1
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨hc, hb⟩ := List.mem_filter.1 hc
    simp only [bi, Bool.and_eq_true] at hb
    rw [val_elim_congr D f (fun _ => b) s c hb.1.1 hb.1.2 (hmin c hc)]
  calc ∑ s : Fin n → ι, (if s v = x then 1 else 0) * (F s * ((g.comps.filter fun c => extC c).map
          fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod)
      ≤ ∑ s : Fin n → ι, (if s v = x then 1 else 0) * (F s * T (s y) b) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have : (0 : ℝ) ≤ if s v = x then 1 else 0 := by split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT s) (hF0 s)) this
    _ = ∑ y' : ι, T y' b * (gA2 g v y).absVal D ![x, y'] := by
        simp only [gA2, absVal_pin, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        have hC : ∀ y' : ι, (∀ i a, pA2 v y i = some a → s i = ![x, y'] a) ↔
            s v = x ∧ s y = y' := by
          intro y'
          constructor
          · intro h
            exact ⟨h v 0 (by simp [pA2]), h y 1 (by simp [pA2, hvy.symm])⟩
          · rintro ⟨h1, h2⟩ i a ha
            simp only [pA2] at ha
            split_ifs at ha with h3 h4
            · cases ha; subst h3; exact h1
            · cases ha; subst h4; exact h2
        simp only [if_congr (hC _) rfl rfl, hcongr]
        by_cases h1 : s v = x
        · simp only [h1, true_and, ite_true, one_mul]
          rw [Finset.sum_eq_single (s y)]
          · simp [hF]; ring
          · intro y' _ hy'; simp [Ne.symm hy']
          · simp
        · simp [h1]

/-- **The absolute-value form** (the form `y = x` of [I, (8.20)]):
if the components at `⊕`, `⊖` are at most `T(s_v, 𝔟)`, then `𝒢^{abs}_{x, 𝔟𝔟} ≤ T(x, 𝔟) |gA1|_x`. -/
private theorem ErrMain_A1Abs {ι : Type} [Fintype ι] [DecidableEq ι] {g : Graph 3 n}
    {j : Fin g.comps.length} {v : Fin n} (hR : Rooted g j (.inr v))
    (hmin : ∀ c ∈ g.comps, c.minor = []) (D : Data ι) (x b : ι) (T : ι → ι → ℝ)
    (hT : ∀ s : Fin n → ι, ((g.comps.filter fun c => extC c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod ≤ T (s v) b) :
    (rootRest g).2.absVal D ![x, b, b] ≤ T x b * (gA1 g v).absVal D ![x] := by
  refine (ErrMain_rootAbs_le hR D x b).trans ?_
  set F : (Fin n → ι) → ℝ := fun s => ‖g.coeff.eval D.m‖ *
    ((g.comps.filter fun c => bi c && !atT c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod with hF
  have hF0 : ∀ s, 0 ≤ F s := fun s => mul_nonneg (norm_nonneg _)
    (List.prod_nonneg fun a ha => by obtain ⟨c, -, rfl⟩ := List.mem_map.1 ha; exact norm_nonneg _)
  have hcongr : ∀ (f : Fin 3 → ι) (s : Fin n → ι), ((g.comps.filter fun c => bi c && !atT c).map
        fun c => ‖Comp.val D (Sum.elim f s) c‖).prod =
      ((g.comps.filter fun c => bi c && !atT c).map
        fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod := by
    intro f s
    congr 1
    refine List.map_congr_left fun c hc => ?_
    obtain ⟨hc, hb⟩ := List.mem_filter.1 hc
    simp only [bi, Bool.and_eq_true] at hb
    rw [val_elim_congr D f (fun _ => b) s c hb.1.1 hb.1.2 (hmin c hc)]
  calc ∑ s : Fin n → ι, (if s v = x then 1 else 0) * (F s * ((g.comps.filter fun c => extC c).map
          fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod)
      ≤ ∑ s : Fin n → ι, (if s v = x then 1 else 0) * (F s * T (s v) b) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have : (0 : ℝ) ≤ if s v = x then 1 else 0 := by split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT s) (hF0 s)) this
    _ = T x b * (gA1 g v).absVal D ![x] := by
        simp only [gA1, absVal_pin, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        have hC : (∀ i a, pA1 v i = some a → s i = ![x] a) ↔ s v = x := by
          constructor
          · intro h
            exact h v 0 (by simp [pA1])
          · intro h1 i a ha
            simp only [pA1] at ha
            split_ifs at ha with h3
            cases ha; subst h3; exact h1
        simp only [if_congr hC rfl rfl, hcongr]
        by_cases h1 : s v = x
        · simp [h1, hF]; ring
        · simp [h1]

/-- **The absolute-value form** ([I, (8.20)], fixed atoms `x`, `𝔟`;
[I, (6.20)]): `𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{-(effOrd g − 1) d/2} B^{1/2}_{x𝔟}`. -/
private theorem ErrMain_formB2Abs :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Fin n) (C : ℕ),
        Rooted g j (.inr v) → g.Normal C → g.DoublyConnected → g.TKinds N →
        dotB g v = false → CaseB g →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W L _ x b =>
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) *
                Real.sqrt (bB d L W x b) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v C hR hN hDC hT hv hB τ hτ
  have hdot := hN.1.noIntDot
  have hd2 : 2 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hZ : ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind = .xdot →
      pinAtom 1 (pB g (.inr v) (1 : Fin 2) 0) c.x ≠ pinAtom 1 (pB g (.inr v) (1 : Fin 2) 0) c.y
  swap
  · push Not at hZ
    obtain ⟨c, hc, hq, hk, he⟩ := hZ
    refine ⟨1, one_pos, 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
    beta_reduce
    rw [ErrMain_absVal_gB2 hR hdot hv, gB2, ErrMain_absVal_pin_eq_zero g nd 1 _ ⟨c, hc, hq, hk, he⟩]
    positivity
  obtain ⟨C', hNo⟩ := normal_gB2 hR hN hDC hv hB hZ
  have hDC2 := dc_gB2 hR hN hDC hv hB
  have hT2 := tKinds_pin hT nd 1 (pB g (.inr v) (1 : Fin 2) 0)
  have ho := ord_gB2 hR hv
  obtain ⟨W₁, hW₁⟩ := dcStrong d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig _ C'
    (gB2 g (.inr v)) hNo hDC2 hT2 (τ / 2) (by positivity)
  set o : ℝ := ((gB2 g (.inr v)).ord : ℝ) - 2 with hodef
  set τ' := min 1 (τ / (2 * (|o| + 1))) with hτ'
  have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
  refine ⟨τ', hτ'0, max W₁ 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
  beta_reduce
  have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hΛ1 : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hW1 hτ'0.le
  have hΛW : (W : ℝ) ^ τ' ≤ (W : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hW1 ((min_le_left _ _).trans (by linarith))
  have hs := strong_of_entry hW1n G z (by linarith) hG
  have hdc := hW₁ W L hadm ((le_max_left _ _).trans hW) z hz G _ hΛ1 hΛW hs x b
  rw [ErrMain_absVal_gB2 hR hdot hv]
  refine hdc.trans ?_
  have hΛo : ((W : ℝ) ^ τ') ^ o ≤ (W : ℝ) ^ (τ / 2) := rpow_rpow_le hW1 (tau_mul_le hτ)
  have hB32 := bB_three_halves_le hd2 hW1n x b
  rw [ho]
  have e1 : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have e2 : (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) * (W : ℝ) ^ (-(d : ℝ)) =
      (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hsq := Real.sqrt_nonneg (bB d L W x b)
  calc (W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ τ') ^ o * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
        bB d L W x b ^ ((3 : ℝ) / 2)
      ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((effOrd g : ℝ) - 3) * d / 2)) *
          ((W : ℝ) ^ (-(d : ℝ)) * Real.sqrt (bB d L W x b)) := by
        gcongr
        exact Real.rpow_nonneg (bB_pos₁ hW1n x b).le _
    _ = _ := by rw [← e1, ← e2]; ring

/-- **The absolute-value form** ([I, (8.20)], root atom forced to `𝔟`;
[I, (6.21)]): `𝒢^{abs}_{x, 𝔟𝔟} ≤ 1_{x = 𝔟} W^τ W^{-(effOrd g − 2) d/2}`. -/
private theorem ErrMain_formB1Abs :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Atom 3 n) (C : ℕ),
        Rooted g j v → g.Normal C → g.DoublyConnected → g.TKinds N →
        (∀ i, v = .inr i → dotB g i = true) → (CaseB g ∨ n = 0) →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W _L _ x b =>
              (if x = b then 1 else 0) *
                ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 2) * d / 2))) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v C hR hN hDC hT hv hB τ hτ
  have hdot := hN.1.noIntDot
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hZ : ∀ c ∈ g.comps, (nd c && !atT c) = true → c.kind = .xdot →
      pinAtom 0 (pB g v (0 : Fin 1) 0) c.x ≠ pinAtom 0 (pB g v (0 : Fin 1) 0) c.y
  swap
  · push Not at hZ
    obtain ⟨c, hc, hq, hk, he⟩ := hZ
    refine ⟨1, one_pos, 1, fun W L _ hadm hW z hz G hG x b => ?_⟩
    beta_reduce
    rw [ErrMain_absVal_gB1 hR hdot hv, gB1, ErrMain_absVal_pin_eq_zero g nd 0 _ ⟨c, hc, hq, hk, he⟩,
      mul_zero]
    have : (0 : ℝ) ≤ if x = b then 1 else 0 := by split_ifs <;> norm_num
    positivity
  obtain ⟨C', hNo⟩ := normal_gB1 hR hN hDC hB hZ
  have hDC1 := dc_gB1 hR hN hDC hB
  have hT1 := tKinds_pin hT nd 0 (pB g v (0 : Fin 1) 0)
  have ho := ord_gB1 hR hv
  obtain ⟨C₀, hC₀, hw⟩ := weak_sqrtB hd
  obtain ⟨W₁, hW₁⟩ := dcSingle d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig _ C'
    (gB1 g v) hNo hDC1 hT1 (τ / 2) (by positivity)
  set o : ℝ := ((gB1 g v).ord : ℝ) with hodef
  have ho' : o = (effOrd g : ℝ) - 2 := by rw [hodef, ho]; push_cast; ring
  set τ' := min 1 (τ / 2 / (2 * (|o| + 1))) with hτ'
  have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
  have hdd : 0 < (d : ℝ) / 2 - 1 := by linarith
  refine ⟨τ', hτ'0, max (max W₁ 1) (max ((max 1 C₀) ^ (1 / ((d : ℝ) / 2 - 1)))
    ((max 1 (C₀ ^ |o|)) ^ (1 / (τ / 4)))), fun W L _ hadm hW z hz G hG x b => ?_⟩
  beta_reduce
  have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hC0W : C₀ ≤ (W : ℝ) ^ ((d : ℝ) / 2 - 1) :=
    const_le_rpow' hdd ((le_max_left _ _).trans ((le_max_right _ _).trans hW))
  have hCoW : C₀ ^ |o| ≤ (W : ℝ) ^ (τ / 4) :=
    const_le_rpow' (by positivity) ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  set Λ := C₀ * (W : ℝ) ^ τ' with hΛdef
  have hWτ' : 1 ≤ (W : ℝ) ^ τ' := Real.one_le_rpow hW1 hτ'0.le
  have hΛ1 : 1 ≤ Λ := by nlinarith
  have hΛW : Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) := by
    calc Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2 - 1) * (W : ℝ) ^ (1 : ℝ) := by
          refine mul_le_mul hC0W (Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _))
            (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hW0]; ring_nf
  have hwk : weakNorm d L W 1 2 (errAbs G z) ≤ Λ := by
    have := hw L W hW1n ((W : ℝ) ^ τ') (by positivity) (errAbs G z) (fun p q => by
      rw [abs_of_nonneg (show 0 ≤ errAbs G z p q from norm_nonneg _)]; exact hG p q)
    rw [hΛdef]; linarith
  have hdc := hW₁ W L hadm ((le_max_left _ _).trans ((le_max_left _ _).trans hW)) z hz G Λ
    hΛ1 hΛW hwk b
  rw [ErrMain_absVal_gB1 hR hdot hv]
  have hi0 : (0 : ℝ) ≤ if x = b then 1 else 0 := by split_ifs <;> norm_num
  refine mul_le_mul_of_nonneg_left (hdc.trans ?_) hi0
  have hΛo : Λ ^ o ≤ (W : ℝ) ^ (τ / 2) := by
    rw [hΛdef, Real.mul_rpow (by linarith) (by positivity)]
    have h1 : C₀ ^ o ≤ C₀ ^ |o| := Real.rpow_le_rpow_of_exponent_le hC₀ (le_abs_self o)
    have h2 : ((W : ℝ) ^ τ') ^ o ≤ (W : ℝ) ^ (τ / 4) := by
      refine rpow_rpow_le hW1 ?_
      have := tau_mul_le (o := o) (show 0 < τ / 2 by positivity)
      linarith
    calc C₀ ^ o * ((W : ℝ) ^ τ') ^ o ≤ (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) :=
          mul_le_mul (h1.trans hCoW) h2 (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hW0]; ring_nf
  calc (W : ℝ) ^ (τ / 2) * Λ ^ o * (W : ℝ) ^ (-(o * d / 2))
      ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(o * d / 2)) := by gcongr
    _ = _ := by
        rw [← Real.rpow_add hW0, ho']
        ring_nf

/-- **The absolute-value form** (first form of [I, (8.20)]; [I, (6.20)]):
`𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{-(effOrd g − 1) d/2} B^{1/2}_{x𝔟}`. -/
private theorem ErrMain_formA2Abs :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v y : Fin n) (C : ℕ),
        Rooted g j (.inr v) → g.Normal C → g.DoublyConnected → g.TKinds N →
        ¬ CaseB g → v ≠ y → TipAt g y →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W L _ x b =>
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) *
                Real.sqrt (bB d L W x b) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v y C hR hN hDC hT hA hvy hTip τ hτ
  have hd2 : 2 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hmin : ∀ c ∈ g.comps, c.minor = [] := fun c hc => by
    have := List.all_eq_true.1 hT c hc
    simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at this
    exact this.1
  obtain ⟨C', hNo⟩ := normal_gA2 hR hN hDC hA hvy
  have hDC2 := dc_gA2 hR hDC hA hvy
  have hT2 := tKinds_pin hT bi 0 (pA2 v y)
  have ho2 := ord_gA2 hR hvy
  have heff := effOrd_of_not_caseB hR hN hA
  set ℓ := (g.comps.filter extC).length with hℓ
  set o : ℝ := ((gA2 g v y).ord : ℝ) - 2 with hodef
  set τ₁ : ℝ := τ / (8 * ((ℓ : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  set τ' := min 1 (τ / 4 / (2 * (|o + ℓ| + 1))) with hτ'
  have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
  obtain ⟨K, Wg, hK, hWg, hin⟩ := gData_inputs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g
    hT τ₁ hτ₁0
  obtain ⟨W₁, hW₁⟩ := dcStrong d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig _ C'
    (gA2 g v y) hNo hDC2 hT2 (τ / 4) (by positivity)
  obtain ⟨C₁, hC₁0, hconv⟩ := conv1 hd
  obtain ⟨Wl, hWl1, hlog⟩ := logF_le_rpow (c₀ := c₀) hc₁ (δ := τ / 24) (by positivity)
  obtain ⟨W₂, hW₂1, htwo⟩ := two_mul_le_of_adm (c₁ := c₁) hc₀ (by linarith)
  set M := (2 * K) ^ ℓ * C₁ with hM
  refine ⟨τ', hτ'0, max (max (max W₁ Wg) (max Wl W₂)) ((max 1 M) ^ (1 / (τ / 8))),
    fun W L _ hadm hW z hz G hG x b => ?_⟩
  beta_reduce
  have hWa : max W₁ Wg ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWb : max Wl W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW1 : (1 : ℝ) ≤ W := hWg.trans ((le_max_right _ _).trans hWa)
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL2 : 2 * W ≤ L := htwo W L hadm ((le_max_right _ _).trans hWb)
  have hL1 : 1 ≤ L := by omega
  have hlogW := hlog W L hadm ((le_max_left _ _).trans hWb) hL1
  have hMW : M ≤ (W : ℝ) ^ (τ / 8) := const_le_rpow' (by positivity) ((le_max_right _ _).trans hW)
  set Λ := (W : ℝ) ^ τ' with hΛdef
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hW1 hτ'0.le
  have hΛW : Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hW1 ((min_le_left _ _).trans (by linarith))
  obtain ⟨hwav, hth⟩ := hin W L hadm ((le_max_right _ _).trans hWa) z hz G
  set D := gData (Smat P.ψ W L) z Sig G with hD
  set K₁ := K * (W : ℝ) ^ τ₁ with hK₁def
  have hK₁ : 1 ≤ K₁ := by
    have := Real.one_le_rpow hW1 hτ₁0.le; nlinarith
  have hm : ‖D.m‖ ≤ 1 := (norm_msc_lt_one (im_pos_of_specDom hW1n hz)).le
  have hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = errAbs G z p q := fun p q => rfl
  set eN : ℤ := extOrd g - 2 * (g.nDots : ℤ) with heN
  set T : Zd d L → Zd d L → ℝ := fun y' b' => (2 * K₁ * Λ) ^ ℓ *
    (W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) * Real.sqrt (bB d L W y' b') with hTdef
  have htip : ∀ s : Fin n → Zd d L, ((g.comps.filter fun c => extC c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod ≤ T (s y) b :=
    fun s => tip_prod_ext hR hN hT hTip hd2 hW1n D (errAbs G z) K₁ Λ hK₁ hΛ1 hΛW hm hEeq hG
      hwav hth b s
  have h1 := ErrMain_A2Abs hR hvy hmin D x b T htip
  have hs := strong_of_entry hW1n G z (by linarith) hG
  have hdc := fun y' => hW₁ W L hadm ((le_max_left _ _).trans hWa) z hz G Λ hΛ1 hΛW hs x y'
  have h2KΛ : 0 ≤ 2 * K₁ * Λ := mul_nonneg (by linarith) (by linarith)
  have hT0 : ∀ y', 0 ≤ T y' b := fun y' => by
    simp only [hTdef]; positivity
  have hlog0 : 0 ≤ logF L W := logF_nonneg hW1n (by omega)
  refine h1.trans ?_
  calc ∑ y' : Zd d L, T y' b * (gA2 g v y).absVal D ![x, y']
      ≤ ∑ y' : Zd d L, T y' b * ((W : ℝ) ^ (τ / 4) * Λ ^ o *
          (W : ℝ) ^ (-((((gA2 g v y).ord : ℝ) - 3) * d / 2)) * bB d L W x y' ^ ((3 : ℝ) / 2)) :=
        Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left (hdc y') (hT0 y')
    _ = (2 * K₁ * Λ) ^ ℓ * (W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) * ((W : ℝ) ^ (τ / 4) * Λ ^ o *
          (W : ℝ) ^ (-((((gA2 g v y).ord : ℝ) - 3) * d / 2))) *
          ∑ y' : Zd d L, bB d L W x y' ^ ((3 : ℝ) / 2) * Real.sqrt (bB d L W y' b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        simp only [hTdef, bB_comm y' b]
        rw [bB_comm b y']
        ring
    _ ≤ (2 * K₁ * Λ) ^ ℓ * (W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) * ((W : ℝ) ^ (τ / 4) * Λ ^ o *
          (W : ℝ) ^ (-((((gA2 g v y).ord : ℝ) - 3) * d / 2))) *
          (C₁ * logF L W ^ 3 * (W : ℝ) ^ (-((d : ℝ) / 2)) * Real.sqrt (bB d L W x b)) := by
        refine mul_le_mul_of_nonneg_left (hconv L W hW1n hL2 x b) ?_
        positivity
    _ = ((2 * K) ^ ℓ * C₁) * ((W : ℝ) ^ τ₁) ^ ℓ * (Λ ^ (ℓ : ℝ) * Λ ^ o) * logF L W ^ 3 *
          (W : ℝ) ^ (τ / 4) * ((W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) *
            (W : ℝ) ^ (-((((gA2 g v y).ord : ℝ) - 3) * d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2))) *
          Real.sqrt (bB d L W x b) := by
        rw [Real.rpow_natCast, hK₁def]
        ring
    _ ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) * Real.sqrt (bB d L W x b) := by
        have hΛℓ : Λ ^ (ℓ : ℝ) * Λ ^ o ≤ (W : ℝ) ^ (τ / 8) := by
          rw [← Real.rpow_add (by linarith), hΛdef]
          refine rpow_rpow_le hW1 ?_
          have := tau_mul_le (o := o + ℓ) (show 0 < τ / 4 by positivity)
          rw [← hτ'] at this
          linarith
        have hsmall := absorb4 hW1 hτ (by positivity) (by positivity) (by positivity)
          (by positivity) hMW (pow_tau₁_le hW1 hτ ℓ) hΛℓ (logF_cube_le hW1 hlog0 hlogW)
        have hdec : (W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) *
            (W : ℝ) ^ (-((((gA2 g v y).ord : ℝ) - 3) * d / 2)) * (W : ℝ) ^ (-((d : ℝ) / 2)) =
            (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
          congr 1
          rw [heN, ho2, heff]
          push_cast
          ring
        rw [hdec]
        have : 0 ≤ (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) * Real.sqrt (bB d L W x b) := by
          positivity
        linarith [mul_le_mul_of_nonneg_right hsmall this]

/-- **The absolute-value form** (form `y = x` of [I, (8.20)]; [I, (6.21)]):
`𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{-(effOrd g − 1) d/2} B^{1/2}_{x𝔟}`. -/
private theorem ErrMain_formA1Abs :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Fin n) (C : ℕ),
        Rooted g j (.inr v) → g.Normal C → g.DoublyConnected → g.TKinds N →
        ¬ CaseB g → TipAt g v →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W L _ x b =>
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) *
                Real.sqrt (bB d L W x b) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v C hR hN hDC hT hA hTip τ hτ
  have hd2 : 2 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hmin : ∀ c ∈ g.comps, c.minor = [] := fun c hc => by
    have := List.all_eq_true.1 hT c hc
    simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at this
    exact this.1
  obtain ⟨C', hNo⟩ := normal_gA1 hR hN hDC hA v
  have hDC1 := dc_gA1 hR hDC hA v
  have hT1 := tKinds_pin hT bi 0 (pA1 v)
  have ho1 := ord_gA1 hR (g := g) v
  have heff := effOrd_of_not_caseB hR hN hA
  set ℓ := (g.comps.filter extC).length with hℓ
  set o : ℝ := ((gA1 g v).ord : ℝ) with hodef
  set τ₁ : ℝ := τ / (8 * ((ℓ : ℝ) + 1)) with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  set τ' := min 1 (τ / 4 / (2 * (|o + ℓ| + 1))) with hτ'
  have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
  obtain ⟨K, Wg, hK, hWg, hin⟩ := gData_inputs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g
    hT τ₁ hτ₁0
  obtain ⟨W₁, hW₁⟩ := dcSingle d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig _ C'
    (gA1 g v) hNo hDC1 hT1 (τ / 4) (by positivity)
  obtain ⟨C₀, hC₀, hw⟩ := weak_sqrtB hd
  have hdd : 0 < (d : ℝ) / 2 - 1 := by linarith
  set M := (2 * K) ^ ℓ * C₀ ^ |o| with hM
  refine ⟨τ', hτ'0, max (max W₁ Wg) (max ((max 1 C₀) ^ (1 / ((d : ℝ) / 2 - 1)))
    ((max 1 M) ^ (1 / (τ / 8)))), fun W L _ hadm hW z hz G hG x b => ?_⟩
  beta_reduce
  have hWa : max W₁ Wg ≤ W := (le_max_left _ _).trans hW
  have hWb := (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := hWg.trans ((le_max_right _ _).trans hWa)
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hC0W : C₀ ≤ (W : ℝ) ^ ((d : ℝ) / 2 - 1) := const_le_rpow' hdd ((le_max_left _ _).trans hWb)
  have hMW : M ≤ (W : ℝ) ^ (τ / 8) := const_le_rpow' (by positivity) ((le_max_right _ _).trans hWb)
  set Λ := (W : ℝ) ^ τ' with hΛdef
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hW1 hτ'0.le
  have hΛW : Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hW1 ((min_le_left _ _).trans (by linarith))
  have hΛw1 : 1 ≤ C₀ * Λ := by nlinarith
  have hΛwW : C₀ * Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2) := by
    calc C₀ * Λ ≤ (W : ℝ) ^ ((d : ℝ) / 2 - 1) * (W : ℝ) ^ (1 : ℝ) := by
          refine mul_le_mul hC0W (Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _))
            (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hW0]; ring_nf
  have hwk : weakNorm d L W 1 2 (errAbs G z) ≤ C₀ * Λ := hw L W hW1n Λ (by linarith)
    (errAbs G z) (fun p q => by
      rw [abs_of_nonneg (show 0 ≤ errAbs G z p q from norm_nonneg _)]; exact hG p q)
  obtain ⟨hwav, hth⟩ := hin W L hadm ((le_max_right _ _).trans hWa) z hz G
  set D := gData (Smat P.ψ W L) z Sig G with hD
  set K₁ := K * (W : ℝ) ^ τ₁ with hK₁def
  have hK₁ : 1 ≤ K₁ := by
    have := Real.one_le_rpow hW1 hτ₁0.le; nlinarith
  have hm : ‖D.m‖ ≤ 1 := (norm_msc_lt_one (im_pos_of_specDom hW1n hz)).le
  have hEeq : ∀ p q, ‖D.Gm ∅ p q - (if p = q then D.m else 0)‖ = errAbs G z p q := fun p q => rfl
  set eN : ℤ := extOrd g - 2 * (g.nDots : ℤ) with heN
  set T : Zd d L → Zd d L → ℝ := fun y' b' => (2 * K₁ * Λ) ^ ℓ *
    (W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) * Real.sqrt (bB d L W y' b') with hTdef
  have htip : ∀ s : Fin n → Zd d L, ((g.comps.filter fun c => extC c).map
      fun c => ‖Comp.val D (Sum.elim (fun _ => b) s) c‖).prod ≤ T (s v) b :=
    fun s => tip_prod_ext hR hN hT hTip hd2 hW1n D (errAbs G z) K₁ Λ hK₁ hΛ1 hΛW hm hEeq hG
      hwav hth b s
  have h1 := ErrMain_A1Abs hR hmin D x b T htip
  have hdc := hW₁ W L hadm ((le_max_left _ _).trans hWa) z hz G (C₀ * Λ) hΛw1 hΛwW hwk x
  have h2KΛ : 0 ≤ 2 * K₁ * Λ := mul_nonneg (by linarith) (by linarith)
  have hT0 : 0 ≤ T x b := by simp only [hTdef]; positivity
  refine h1.trans ?_
  have hΛo : (C₀ * Λ) ^ o ≤ C₀ ^ |o| * Λ ^ o := by
    rw [Real.mul_rpow (by linarith) (by linarith)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hC₀ (le_abs_self o))
      (by positivity)
  calc T x b * (gA1 g v).absVal D ![x]
      ≤ T x b * ((W : ℝ) ^ (τ / 4) * (C₀ * Λ) ^ o * (W : ℝ) ^ (-(o * d / 2))) :=
        mul_le_mul_of_nonneg_left hdc hT0
    _ ≤ T x b * ((W : ℝ) ^ (τ / 4) * (C₀ ^ |o| * Λ ^ o) * (W : ℝ) ^ (-(o * d / 2))) := by
        gcongr
    _ = ((2 * K) ^ ℓ * C₀ ^ |o|) * ((W : ℝ) ^ τ₁) ^ ℓ * (Λ ^ (ℓ : ℝ) * Λ ^ o) * 1 *
          (W : ℝ) ^ (τ / 4) * ((W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) * (W : ℝ) ^ (-(o * d / 2))) *
          Real.sqrt (bB d L W x b) := by
        rw [Real.rpow_natCast, hTdef, hK₁def]
        ring
    _ ≤ (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) * Real.sqrt (bB d L W x b) := by
        have hΛℓ : Λ ^ (ℓ : ℝ) * Λ ^ o ≤ (W : ℝ) ^ (τ / 8) := by
          rw [← Real.rpow_add (by linarith), hΛdef]
          refine rpow_rpow_le hW1 ?_
          have := tau_mul_le (o := o + ℓ) (show 0 < τ / 4 by positivity)
          rw [← hτ'] at this
          linarith
        have hsmall := absorb4 hW1 hτ (by positivity) (by positivity) (by positivity)
          zero_le_one hMW (pow_tau₁_le hW1 hτ ℓ) hΛℓ
          (Real.one_le_rpow hW1 (by positivity))
        have hdec : (W : ℝ) ^ (-(((eN : ℝ) - 1) * d / 2)) * (W : ℝ) ^ (-(o * d / 2)) =
            (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) := by
          rw [← Real.rpow_add hW0]
          congr 1
          rw [hodef, heN, ho1, heff]
          push_cast
          ring
        rw [hdec]
        have : 0 ≤ (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) * Real.sqrt (bB d L W x b) := by
          positivity
        linarith [mul_le_mul_of_nonneg_right hsmall this]

/-- **The absolute-value form** (every form of [I, (8.20)]): under its
hypotheses, `𝒢^{abs}_{x, 𝔟𝔟} ≤ W^τ W^{-(e − 1) d/2} B^{1/2}_{x𝔟} + 1_{x = 𝔟} W^τ W^{-(e − 2) d/2}`
with `e = effOrd g`, under the entry hypothesis `|G_{pq} − δ_{pq} m| ≤ W^{τ'} B^{1/2}_{pq}`. -/
private theorem ErrMain_formKeyAbs :
    ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
      ∀ {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Atom 3 n) (C : ℕ),
        Rooted g j v → g.Normal C → g.DoublyConnected → g.TKinds N →
        ((∃ i, v = .inr i) ∨ CaseB g ∨ n = 0) → (¬ CaseB g → (∃ i, v = .inr i) → ∃ y, TipAt g y) →
        ∀ τ : ℝ, 0 < τ → ErrMain_AbsBd d P c₀ c₁ κ ε Sig g fun W L _ x b =>
              (W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 1) * d / 2)) *
                Real.sqrt (bB d L W x b) + (if x = b then 1 else 0) *
                ((W : ℝ) ^ τ * (W : ℝ) ^ (-(((effOrd g : ℝ) - 2) * d / 2))) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig n g j v C hR hN hDC hT hR1 hTip τ hτ
  rcases v with a | i
  · have hB : CaseB g ∨ n = 0 := by
      rcases hR1 with ⟨i, hi⟩ | h
      · cases hi
      · exact h
    obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formB1Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig g j _
      C hR hN hDC hT (fun i h => by cases h) hB τ hτ
    exact ⟨τ', hτ', W₀, fun W L _ hadm hW z hz G hG x b =>
      (h W L hadm hW z hz G hG x b).trans (le_add_of_nonneg_left (by positivity))⟩
  · by_cases hB : CaseB g
    · by_cases hdi : dotB g i = true
      · obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formB1Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig
          g j _ C hR hN hDC hT (fun i' h => by cases h; exact hdi) (Or.inl hB) τ hτ
        exact ⟨τ', hτ', W₀, fun W L _ hadm hW z hz G hG x b =>
          (h W L hadm hW z hz G hG x b).trans (le_add_of_nonneg_left (by positivity))⟩
      · obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formB2Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig
          g j i C hR hN hDC hT (by simpa using hdi) hB τ hτ
        exact ⟨τ', hτ', W₀, fun W L _ hadm hW z hz G hG x b =>
          (h W L hadm hW z hz G hG x b).trans (le_add_of_nonneg_right (by positivity))⟩
    · obtain ⟨y, hy⟩ := hTip hB ⟨i, rfl⟩
      by_cases hiy : i = y
      · subst hiy
        obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formA1Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig
          g j i C hR hN hDC hT hB hy τ hτ
        exact ⟨τ', hτ', W₀, fun W L _ hadm hW z hz G hG x b =>
          (h W L hadm hW z hz G hG x b).trans (le_add_of_nonneg_right (by positivity))⟩
      · obtain ⟨τ', hτ', W₀, h⟩ := ErrMain_formA2Abs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSig
          g j i y C hR hN hDC hT hB hiy hy τ hτ
        exact ⟨τ', hτ', W₀, fun W L _ hadm hW z hz G hG x b =>
          (h W L hadm hW z hz G hG x b).trans (le_add_of_nonneg_right (by positivity))⟩

end Forms

/-! ## The rooted graph, the light weights and the label-free graphs -/

section Transfer

/-- Absolute-value graphs with the same coefficient and the same components up to order agree. -/
private theorem ErrMain_absVal_perm {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ}
    {Γ₁ Γ₂ : Graph k n} (hc : Γ₁.comps.Perm Γ₂.comps) (he : Γ₁.coeff = Γ₂.coeff) (D : Data ι)
    (e : Fin k → ι) : Γ₁.absVal D e = Γ₂.absVal D e := by
  unfold Graph.absVal
  rw [he]
  exact Finset.sum_congr rfl fun s _ => by rw [(hc.map _).prod_eq]

/-- The components replacing one flagged component in `Graph.pathRepl`: the path through the
label atom if the flag is set, the component without its label otherwise. -/
private def ErrMain_piece {V : Type} (p : Comp V × Bool) : List (Comp V) :=
  match p.1.label with
  | some (_, w) => if p.2 then p.1.pathVia w else [{ p.1 with label := none }]
  | none => [p.1]

/-- The test of `Graph.pathRepl` keeping a component of `cs`: all but the `×`-dotted edges between
two distinct atoms that carry no solid edge of `cs`. -/
private def ErrMain_keep {V : Type} [BEq V] (cs : List (Comp V)) (c : Comp V) : Bool :=
  !(c.kind == .xdot && c.x != c.y && !cs.any fun c' => c'.kind.isSolid &&
    ((c'.x == c.x && c'.y == c.y) || (c'.x == c.y && c'.y == c.x)))

/-- The components of the label-free graph of a list of flagged components (`Graph.pathRepl`). -/
private def ErrMain_repl {V : Type} [BEq V] (l : List (Comp V × Bool)) : List (Comp V) :=
  (l.flatMap ErrMain_piece).filter (ErrMain_keep (l.flatMap ErrMain_piece))

/-- The atoms of the components that replace a list of flagged components are atoms of the ends,
minors and label atoms of the flagged components. -/
private theorem ErrMain_piece_atoms {V : Type} (P : V → Prop) (l : List (Comp V × Bool))
    (hl : ∀ p ∈ l, P p.1.x ∧ P p.1.y ∧ (∀ u ∈ p.1.minor, P u) ∧
      ∀ q w, p.1.label = some (q, w) → P w)
    (c : Comp V) (hc : c ∈ l.flatMap ErrMain_piece) : P c.x ∧ P c.y ∧ ∀ u ∈ c.minor, P u := by
  obtain ⟨⟨c₀, t⟩, hm, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨h1, h2, h3, h4⟩ := hl _ hm
  simp only [ErrMain_piece] at hc
  split at hc
  · rename_i q w hw
    have hw' := h4 q w hw
    split_ifs at hc
    · simp only [Comp.pathVia, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact ⟨by assumption, by assumption, by simp⟩
    · simp only [List.mem_singleton] at hc; subst hc; exact ⟨h1, h2, h3⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact ⟨h1, h2, h3⟩

/-- The components of `X.pathRepl S` are those of the label-free graph of the components of `X`
flagged by `S`. -/
private theorem ErrMain_pathRepl_comps {n : ℕ} (X : Graph 3 n) (S : Finset (Fin X.comps.length)) :
    (X.pathRepl S).comps = ErrMain_repl ((List.finRange X.comps.length).map fun i =>
      (X.comps[i], decide (i ∈ S))) := by
  simp only [Graph.pathRepl, ErrMain_repl, List.flatMap_map]
  have h : (List.finRange X.comps.length).flatMap
      (fun i => ErrMain_piece (X.comps[i], decide (i ∈ S)))
      = (List.finRange X.comps.length).flatMap (fun i => match X.comps[i].label with
        | some (_, v) => if i ∈ S then X.comps[i].pathVia v else [{ X.comps[i] with label := none }]
        | none => [X.comps[i]]) := by
    refine List.flatMap_congr fun i _ => ?_
    simp only [ErrMain_piece]
    split <;> simp_all
  rw [h]
  rfl

/-- The label-free graph of flagged components does not depend on their order. -/
private theorem ErrMain_repl_perm {V : Type} [BEq V] {l₁ l₂ : List (Comp V × Bool)}
    (h : l₁.Perm l₂) : (ErrMain_repl l₁).Perm (ErrMain_repl l₂) := by
  have hf := h.flatMap_right ErrMain_piece
  have hk : ErrMain_keep (l₁.flatMap ErrMain_piece) = ErrMain_keep (l₂.flatMap ErrMain_piece) := by
    funext c
    simp only [ErrMain_keep, hf.any_eq]
  unfold ErrMain_repl
  rw [hk]
  exact hf.filter _

/-- A component without label that is neither solid nor `×`-dotted is kept as it is. -/
private theorem ErrMain_repl_cons {V : Type} [BEq V] (r : Comp V) (t : Bool)
    (l : List (Comp V × Bool))
    (hl : r.label = none) (hx : r.kind ≠ .xdot) (hs : r.kind.isSolid = false) :
    ErrMain_repl ((r, t) :: l) = r :: ErrMain_repl l := by
  have hp : ErrMain_piece (r, t) = [r] := by simp [ErrMain_piece, hl]
  have hk : ErrMain_keep (r :: l.flatMap ErrMain_piece) =
      ErrMain_keep (l.flatMap ErrMain_piece) := by
    funext c
    simp [ErrMain_keep, hs]
  simp only [ErrMain_repl, List.flatMap_cons, hp, List.singleton_append, hk]
  rw [List.filter_cons_of_pos]
  simp [ErrMain_keep, hx]

/-- The label-free graph commutes with a map of the atoms that is injective on the atoms of the
flagged components. -/
private theorem ErrMain_repl_map {V W : Type} [BEq V] [LawfulBEq V] [BEq W] [LawfulBEq W]
    (φ : V → W)
    (A : Set V) (hφ : Set.InjOn φ A) (l : List (Comp V × Bool))
    (hl : ∀ p ∈ l, p.1.x ∈ A ∧ p.1.y ∈ A ∧ (∀ u ∈ p.1.minor, u ∈ A) ∧
      ∀ q w, p.1.label = some (q, w) → w ∈ A) :
    ErrMain_repl (l.map fun p => (p.1.map φ, p.2)) = (ErrMain_repl l).map (Comp.map φ) := by
  have hp : ∀ p : Comp V × Bool,
      ErrMain_piece (p.1.map φ, p.2) = (ErrMain_piece p).map (Comp.map φ) := by
    rintro ⟨c, t⟩
    obtain ⟨κ, x, y, mi, lab⟩ := c
    rcases lab with _ | ⟨q, w⟩
    · rfl
    · cases t <;> rfl
  have hf : (l.map fun p => (p.1.map φ, p.2)).flatMap ErrMain_piece =
      (l.flatMap ErrMain_piece).map (Comp.map φ) := by
    rw [List.flatMap_map, List.map_flatMap]
    simp only [hp]
  have hA : ∀ c ∈ l.flatMap ErrMain_piece, c.x ∈ A ∧ c.y ∈ A := fun c hc =>
    ⟨(ErrMain_piece_atoms (· ∈ A) l hl c hc).1, (ErrMain_piece_atoms (· ∈ A) l hl c hc).2.1⟩
  have hinj : ∀ a ∈ A, ∀ b ∈ A, (φ a == φ b) = (a == b) := fun a ha b hb => by
    by_cases h : a = b
    · subst h; simp
    · rw [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 fun e => h (hφ ha hb e)]
  rw [ErrMain_repl, ErrMain_repl, hf, List.filter_map]
  congr 1
  refine List.filter_congr fun c hc => ?_
  obtain ⟨hx, hy⟩ := hA c hc
  simp only [Function.comp_apply, ErrMain_keep, List.any_map, Function.comp_def]
  have hany : ((l.flatMap ErrMain_piece).any fun c' => (c'.map φ).kind.isSolid &&
      (((c'.map φ).x == (c.map φ).x && (c'.map φ).y == (c.map φ).y) ||
        ((c'.map φ).x == (c.map φ).y && (c'.map φ).y == (c.map φ).x))) =
      (l.flatMap ErrMain_piece).any fun c' => c'.kind.isSolid &&
        ((c'.x == c.x && c'.y == c.y) || (c'.x == c.y && c'.y == c.x)) := by
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    refine exists_congr fun c' => and_congr_right fun hc' => ?_
    obtain ⟨hx', hy'⟩ := hA c' hc'
    simp only [Comp.map, hinj _ hx' _ hx, hinj _ hy' _ hy, hinj _ hx' _ hy, hinj _ hy' _ hx]
  rw [hany]
  simp only [Comp.map, bne, hinj _ hx _ hy]

/-- Lifting a permutation of the first components to the pairs. -/
private theorem ErrMain_perm_lift {α β : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∀ p₁ : List (α × β), p₁.map Prod.fst = l₁ → ∃ p₂, p₁.Perm p₂ ∧ p₂.map Prod.fst = l₂ := by
  induction h with
  | nil => intro p₁ hp; exact ⟨p₁, List.Perm.refl _, hp⟩
  | cons x _ ih =>
    intro p₁ hp
    obtain ⟨q, p', rfl, hq, hp'⟩ := List.map_eq_cons_iff.1 hp
    obtain ⟨p₂, h₂, e₂⟩ := ih p' hp'
    exact ⟨q :: p₂, h₂.cons q, by simp [hq, e₂]⟩
  | swap x y l =>
    intro p₁ hp
    obtain ⟨q, p', rfl, hq, hp'⟩ := List.map_eq_cons_iff.1 hp
    obtain ⟨q', p'', rfl, hq', hp''⟩ := List.map_eq_cons_iff.1 hp'
    exact ⟨q' :: q :: p'', List.Perm.swap _ _ _, by simp [hq, hq', hp'']⟩
  | trans _ _ ih₁ ih₂ =>
    intro p₁ hp
    obtain ⟨p₂, h₂, e₂⟩ := ih₁ p₁ hp
    obtain ⟨p₃, h₃, e₃⟩ := ih₂ p₂ e₂
    exact ⟨p₃, h₂.trans h₃, e₃⟩

/-- A list of flagged components of `X` is the list of the components of `X` flagged by a set. -/
private theorem ErrMain_flags {n : ℕ} (X : Graph 3 n) (l : List (Comp (Atom 3 n) × Bool))
    (hl : l.map Prod.fst = X.comps) : ∃ S : Finset (Fin X.comps.length),
      (List.finRange X.comps.length).map (fun i => (X.comps[i], decide (i ∈ S))) = l := by
  have hlen : l.length = X.comps.length := by rw [← hl, List.length_map]
  refine ⟨Finset.univ.filter fun i => (l[i.1]'(by omega)).2 = true, ?_⟩
  refine List.ext_getElem (by simp [hlen]) fun k h₁ h₂ => ?_
  have e : X.comps[k]'(by simpa using h₁) = (l[k]'h₂).1 := by
    have := congrArg (fun L => L[k]?) hl
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem h₂, List.getElem?_eq_getElem (by simpa using h₁)] at this
    simpa using this.symm
  simp only [List.getElem_map, List.getElem_finRange, Fin.getElem_fin]
  ext
  · simp [e]
  · simp
/-- The first components of the flagged components of `X` are the components of `X`. -/
private theorem ErrMain_flags_fst {n : ℕ} (X : Graph 3 n) (S : Finset (Fin X.comps.length)) :
    ((List.finRange X.comps.length).map fun i => (X.comps[i], decide (i ∈ S))).map Prod.fst =
      X.comps := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp

/-- A flagged component of a set of replaceable components is replaceable. -/
private theorem ErrMain_flags_elig {n : ℕ} (X : Graph 3 n) (S : Finset (Fin X.comps.length))
    (hS : S ⊆ X.pathElig) (p : Comp (Atom 3 n) × Bool)
    (hp : p ∈ (List.finRange X.comps.length).map fun i => (X.comps[i], decide (i ∈ S)))
    (ht : p.2 = true) : X.pathEligB p.1 = true := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
  have hi : i ∈ S := by simpa using ht
  simpa [Graph.pathElig] using hS hi

/-- Two graphs with the same components and coefficient are equal. -/
private theorem ErrMain_graph_ext {k n : ℕ} {Γ₁ Γ₂ : Graph k n} (h₁ : Γ₁.comps = Γ₂.comps)
    (h₂ : Γ₁.coeff = Γ₂.coeff) : Γ₁ = Γ₂ := by
  cases Γ₁; cases Γ₂; congr

/-- The light-weight graph of `g` is, up to order, the root edge `j` and the light-weight graph of
the other components. -/
private theorem ErrMain_wDLights_perm {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length)
    (hk : g.comps[j].kind = .theta []) :
    g.wDLights.comps.Perm (g.comps[j] :: (g.dropComp j).wDLights.comps) := by
  have hp : g.comps.Perm (g.comps[j] :: g.comps.eraseIdx j) :=
    (List.getElem_cons_eraseIdx_perm j.2).symm
  have hr : g.comps[j].wDLight = g.comps[j] := by
    have : ∀ c : Comp (Atom 3 n), c.kind = .theta [] → c.wDLight = c := by
      rintro ⟨κ, x, y, mi, lab⟩ h
      simp only at h
      subst h
      rfl
    exact this _ hk
  have h1 := hp.map Comp.wDLight
  have h2 := hp.flatMap_right (fun c => List.replicate c.kind.wDDeg c.wDLight)
  rw [List.map_cons, hr] at h1
  rw [List.flatMap_cons, hk] at h2
  exact h1.append h2

/-- The light-weight graph of `Graph.rootAt i` is the image of the light-weight graph. -/
private theorem ErrMain_wDLights_map {m : ℕ} (H : Graph 3 (m + 1)) (i : Fin (m + 1)) :
    (H.mapAtoms (ErrMain_rootMap i)).wDLights.comps =
      H.wDLights.comps.map (Comp.map (ErrMain_rootMap i)) := by
  simp only [Graph.wDLights, Graph.mapAtoms, List.map_append, List.map_map, List.flatMap_map,
    List.map_flatMap, List.map_replicate]
  rfl

/-- The light-weight graph of `H` with the dotted edge `⊗–a` is, up to order, the dotted edge and
the light-weight graph of `H`. -/
private theorem ErrMain_wDLights_dot {n : ℕ} (H : Graph 3 n) (a : Fin 3) :
    (⟨H.comps ++ [mkC .dot (.inl 0) (.inl a)], H.coeff⟩ : Graph 3 n).wDLights.comps.Perm
      (mkC .dot (.inl 0) (.inl a) :: H.wDLights.comps) := by
  simp only [Graph.wDLights, List.map_append, List.flatMap_append, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil]
  have e : (mkC .dot (.inl 0) (.inl a) : Comp (Atom 3 n)).wDLight = mkC .dot (.inl 0) (.inl a) :=
    rfl
  rw [e]
  simp only [mkC, Kind.wDDeg, List.replicate_zero, List.append_nil,
    List.append_assoc, List.singleton_append]
  exact List.perm_middle

/-- `ErrMain_rootMap i` is injective away from `⊗`. -/
private theorem ErrMain_rootMap_injOn {m : ℕ} (i : Fin (m + 1)) :
    Set.InjOn (ErrMain_rootMap i) {u | u ≠ .inl 0} := by
  intro u hu w hw h
  simp only [Set.mem_ofPred_eq] at hu hw
  rcases u with a | k <;> rcases w with a' | k'
  · simpa [ErrMain_rootMap] using h
  · simp only [ErrMain_rootMap] at h
    split_ifs at h with h'
    · cases h; exact absurd rfl hu
  · simp only [ErrMain_rootMap] at h
    split_ifs at h with h'
    · cases h; exact absurd rfl hw
  · simp only [ErrMain_rootMap] at h
    split_ifs at h with h1 h2 h2
    · rw [h1, h2]
    · rw [← succAbove_finDrop i k h1, ← succAbove_finDrop i k' h2, Sum.inr.inj h]

/-- The dotted block of a label atom: if every dotted edge of `X` maps under `φ` to atoms joined
by dotted edges of `Y` and `φ` keeps the external atoms external, a label atom whose block in `X`
contains an external atom has an image whose block in `Y` contains one. -/
private theorem ErrMain_labelFixed {n n' : ℕ} (X : Graph 3 n) (Y : Graph 3 n')
    (φ : Atom 3 n → Atom 3 n') (hφ : ∀ u, u.isLeft = true → (φ u).isLeft = true)
    (hd : ∀ c ∈ X.comps, c.kind = .dot → Y.dotGraph.Reachable (φ c.x) (φ c.y)) (w : Atom 3 n)
    (h : X.labelFixedB w = true) : Y.labelFixedB (φ w) = true := by
  simp only [Graph.labelFixedB, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h ⊢
  obtain ⟨B, hB, hw, u, hu, hl⟩ := h
  have hX : X.SameBlock w u := (X.sameBlock_iff_mem_dotBlocks w u).2 ⟨B, hB, hw, hu⟩
  have hY : Y.SameBlock (φ w) (φ u) := by
    refine reach_map φ (fun a b hab => ?_) hX
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩
    · exact hd c hc hk
    · exact (hd c hc hk).symm
  obtain ⟨B', hB', h1, h2⟩ := (Y.sameBlock_iff_mem_dotBlocks _ _).1 hY
  exact ⟨B', hB', h1, φ u, h2, hφ u hl⟩

/-- A component whose image is replaceable in `Y` is replaceable in `X` (`ErrMain_labelFixed`). -/
private theorem ErrMain_pathElig {n n' : ℕ} (X : Graph 3 n) (Y : Graph 3 n')
    (φ : Atom 3 n → Atom 3 n') (hφ : ∀ u, u.isLeft = true → (φ u).isLeft = true)
    (hd : ∀ c ∈ X.comps, c.kind = .dot → Y.dotGraph.Reachable (φ c.x) (φ c.y))
    (c : Comp (Atom 3 n)) (h : Y.pathEligB (c.map φ) = true) : X.pathEligB c = true := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  rcases lab with _ | ⟨q, w⟩
  · simp [Graph.pathEligB, Comp.map] at h
  · simp only [Graph.pathEligB, Comp.map, Option.map_some, Prod.map, id, Bool.and_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq] at h ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨⟨⟨h1, ?_⟩, fun e => h3 (by rw [e])⟩, fun e => h4 (by rw [e])⟩
    by_contra hc
    have := ErrMain_labelFixed X Y φ hφ hd w (by simpa using hc)
    rw [this] at h2
    exact absurd h2 (by decide)

/-- A list of pairs whose first components are the images of `K` under `f` is the image of the
pairs of `K` with its flags. -/
private theorem ErrMain_zip_map {α β γ : Type} (f : α → β) :
    ∀ (K : List α) (l : List (β × γ)), l.map Prod.fst = K.map f →
      (K.zip (l.map Prod.snd)).map Prod.fst = K ∧
        l = (K.zip (l.map Prod.snd)).map fun p => (f p.1, p.2)
  | [], l, h => by simp_all
  | a :: K, l, h => by
    obtain ⟨q, l', rfl, hq, hl'⟩ := List.map_eq_cons_iff.1 h
    obtain ⟨h1, h2⟩ := ErrMain_zip_map f K l' hl'
    refine ⟨by simp [h1], ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
    exact ⟨by rw [← hq], h2⟩

/-- No end, minor atom or label atom of a component is `⊗`. -/
private def ErrMain_offT {n : ℕ} (c : Comp (Atom 3 n)) : Prop :=
  c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ (∀ u ∈ c.minor, u ≠ .inl 0) ∧
    ∀ q w, c.label = some (q, w) → w ≠ .inl 0

/-- **The label-free graphs of the rooted graph, root atom internal**: for `Γ₀ = H.rootAt i`, the
label-free graph `Γ_S` of the light-weight graph of `Γ₀` is the image of the label-free graph of
flagged components `lK` of the light-weight graph of `H`, whose flagged components have
replaceable images. -/
private theorem ErrMain_gamma_int {m : ℕ} (H : Graph 3 (m + 1)) (i : Fin (m + 1)) (Γ₀ : Graph 3 m)
    (hΓ₀ : Γ₀ = H.mapAtoms (ErrMain_rootMap i)) (hH : ∀ c ∈ H.wDLights.comps, ErrMain_offT c)
    (S : Finset (Fin Γ₀.wDLights.comps.length)) (hS : S ⊆ Γ₀.wDLights.pathElig) :
    ∃ lK : List (Comp (Atom 3 (m + 1)) × Bool), lK.map Prod.fst = H.wDLights.comps ∧
      (∀ p ∈ lK, p.2 = true → Γ₀.wDLights.pathEligB (p.1.map (ErrMain_rootMap i)) = true) ∧
      Γ₀.wDLights.pathRepl S =
        (⟨ErrMain_repl lK, H.coeff⟩ : Graph 3 (m + 1)).mapAtoms (ErrMain_rootMap i) := by
  have h0 : ((List.finRange Γ₀.wDLights.comps.length).map fun k =>
      (Γ₀.wDLights.comps[k], decide (k ∈ S))).map Prod.fst =
      H.wDLights.comps.map (Comp.map (ErrMain_rootMap i)) := by
    rw [ErrMain_flags_fst, hΓ₀, ErrMain_wDLights_map]
  obtain ⟨h1, h2⟩ := ErrMain_zip_map _ _ _ h0
  generalize H.wDLights.comps.zip (List.map Prod.snd _) = lK at h1 h2
  refine ⟨lK, h1, fun p hp ht => ?_, ErrMain_graph_ext ?_ (by change Γ₀.coeff = _; rw [hΓ₀]; rfl)⟩
  · refine ErrMain_flags_elig _ S hS (p.1.map (ErrMain_rootMap i), p.2) ?_ ht
    rw [h2]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  · rw [ErrMain_pathRepl_comps, h2, ErrMain_repl_map _ {u | u ≠ .inl 0}
      (ErrMain_rootMap_injOn i)]
    · rfl
    · intro p hp
      have := hH p.1 (by rw [← h1]; exact List.mem_map.2 ⟨p, hp, rfl⟩)
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩

/-- **The label-free graphs of the rooted graph, root atom `⊕` or `⊖`**: for `Γ₀` the graph `H`
with the dotted edge `⊗–a`, the label-free graph `Γ_S` of the light-weight graph of `Γ₀` is, up to
order, the dotted edge `⊗–a` and the label-free graph of flagged components `lK` of the
light-weight graph of `H`, whose flagged components are replaceable in `Γ₀`. -/
private theorem ErrMain_gamma_ext {n : ℕ} (H : Graph 3 n) (a : Fin 3) (Γ₀ : Graph 3 n)
    (hΓ₀ : Γ₀ = ⟨H.comps ++ [mkC .dot (.inl 0) (.inl a)], H.coeff⟩)
    (S : Finset (Fin Γ₀.wDLights.comps.length)) (hS : S ⊆ Γ₀.wDLights.pathElig) :
    ∃ lK : List (Comp (Atom 3 n) × Bool), lK.map Prod.fst = H.wDLights.comps ∧
      (∀ p ∈ lK, p.2 = true → Γ₀.wDLights.pathEligB p.1 = true) ∧
      (Γ₀.wDLights.pathRepl S).comps.Perm (mkC .dot (.inl 0) (.inl a) :: ErrMain_repl lK) ∧
      (Γ₀.wDLights.pathRepl S).coeff = H.coeff := by
  have hP : Γ₀.wDLights.comps.Perm (mkC .dot (.inl 0) (.inl a) :: H.wDLights.comps) := by
    rw [hΓ₀]; exact ErrMain_wDLights_dot H a
  obtain ⟨p₂, hp₂, e₂⟩ := ErrMain_perm_lift hP _ (ErrMain_flags_fst _ S)
  obtain ⟨q, lK, rfl, hq, hlK⟩ := List.map_eq_cons_iff.1 e₂
  refine ⟨lK, hlK, fun p hp ht => ErrMain_flags_elig _ S hS p
    (hp₂.mem_iff.2 (List.mem_cons_of_mem _ hp)) ht, ?_, by change Γ₀.coeff = _; rw [hΓ₀]⟩
  rw [ErrMain_pathRepl_comps]
  refine (ErrMain_repl_perm hp₂).trans ?_
  obtain ⟨c, t⟩ := q
  simp only at hq
  subst hq
  rw [ErrMain_repl_cons _ _ _ rfl (by simp [mkC]) rfl]

/-- **The graph `g_S`**: for flagged components `lK` of the light-weight graph of the components of
`g` other than the root edge `j`, whose flagged components are replaceable in the light-weight
graph of `g`, there is a set `S'` of replaceable components of the light-weight graph of `g` whose
label-free graph has the root edge and, up to order, the components of the label-free graph of
`lK` not at `⊗`. -/
private theorem ErrMain_gside {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Atom 3 n)
    (hv : v ≠ .inl 0) (hk : g.comps[j].kind = .theta []) (hlab : g.comps[j].label = none)
    (hxy : g.comps[j].x = .inl 0 ∧ g.comps[j].y = v)
    (hH : ∀ c ∈ (g.dropComp j).wDLights.comps, ErrMain_offT c)
    (lK : List (Comp (Atom 3 n) × Bool)) (hlK : lK.map Prod.fst = (g.dropComp j).wDLights.comps)
    (hel : ∀ p ∈ lK, p.2 = true → g.wDLights.pathEligB p.1 = true) :
    ∃ S' ⊆ g.wDLights.pathElig, ∃ j' : Fin (g.wDLights.pathRepl S').comps.length,
      Rooted (g.wDLights.pathRepl S') j' v ∧
      ((g.wDLights.pathRepl S').comps.filter fun c => !atT c).Perm (ErrMain_repl lK) ∧
      (g.wDLights.pathRepl S').coeff = g.coeff := by
  set r := g.comps[j] with hr
  set G := g.wDLights with hG
  have hoff : ∀ c ∈ ErrMain_repl lK, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ ∀ u ∈ c.minor, u ≠ .inl 0 :=
    fun c hc => ErrMain_piece_atoms (· ≠ .inl 0) lK (fun p hp => by
      have := hH p.1 (by rw [← hlK]; exact List.mem_map.2 ⟨p, hp, rfl⟩)
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩) c (List.mem_of_mem_filter hc)
  obtain ⟨p₂, hp₂, e₂⟩ := ErrMain_perm_lift (ErrMain_wDLights_perm g j hk).symm ((r, false) :: lK)
    (by simp [hlK, hr])
  obtain ⟨S', hS'⟩ := ErrMain_flags G p₂ e₂
  have hcomps : (G.pathRepl S').comps.Perm (r :: ErrMain_repl lK) := by
    rw [ErrMain_pathRepl_comps, hS']
    refine (ErrMain_repl_perm hp₂).symm.trans ?_
    rw [ErrMain_repl_cons _ _ _ hlab (by rw [hk]; simp) (by rw [hk]; rfl)]
  have hrm : r ∈ (G.pathRepl S').comps := hcomps.mem_iff.2 (List.mem_cons_self ..)
  obtain ⟨k, hk', ek⟩ := List.mem_iff_getElem.1 hrm
  have hrest : ((G.pathRepl S').comps.eraseIdx k).Perm (ErrMain_repl lK) := by
    have h := (List.getElem_cons_eraseIdx_perm hk').trans hcomps
    rw [ek] at h
    exact h.cons_inv
  refine ⟨S', fun i hi => ?_, ⟨k, hk'⟩, ⟨hv, by simpa [ek] using hk, by simpa [ek] using hxy,
    fun c hc => ?_⟩, ?_, rfl⟩
  · have hm : (G.comps[i], true) ∈ p₂ := by
      rw [← hS']
      exact List.mem_map.2 ⟨i, List.mem_finRange i, by simp [hi]⟩
    rcases List.mem_cons.1 (hp₂.mem_iff.2 hm) with h | h
    · simp at h
    · simpa [Graph.pathElig] using hel _ h rfl
  · have := hoff c (hrest.mem_iff.1 hc)
    exact ⟨this.1, this.2.1, fun h => this.2.2 _ h rfl⟩
  · refine (hcomps.filter _).trans ?_
    rw [List.filter_cons_of_neg (by simp [atT, hxy.1]), List.filter_eq_self.2 fun c hc => ?_]
    have := hoff c hc
    simp [atT, this.1, this.2.1]

/-- **The transfer of the rooted graph through the light weights and the label removal**: for a
graph `g` of the form [II, Def 3.3 (4)] with root edge `j` at `v ≠ ⊗` and a set `S` of replaceable
components of the light-weight graph of `𝒢 = rootRest g`, there is a set `S'` of replaceable
components of the light-weight graph of `g` such that its label-free graph `g_S` keeps the root
edge and `(𝒢_S)^{abs}_{x, 𝔟𝔟} = (rootRest g_S)^{abs}_{x, 𝔟𝔟}` on every data record. -/
private theorem ErrMain_transfer {n : ℕ} (g : Graph 3 n) (j : Fin g.comps.length) (v : Atom 3 n)
    (hv : v ≠ .inl 0) (hk : g.comps[j].kind = .theta []) (hlab : g.comps[j].label = none)
    (hxy : g.comps[j].x = .inl 0 ∧ g.comps[j].y = v)
    (hrest : ∀ c ∈ (g.dropComp j).comps, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor ∧
      c.label.map Prod.snd ≠ some (.inl 0))
    (S : Finset (Fin (rootRest g).2.wDLights.comps.length))
    (hS : S ⊆ (rootRest g).2.wDLights.pathElig) :
    ∃ S' ⊆ g.wDLights.pathElig, ∃ j' : Fin (g.wDLights.pathRepl S').comps.length,
      Rooted (g.wDLights.pathRepl S') j' v ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (x b : ι),
        ((rootRest g).2.wDLights.pathRepl S).absVal D ![x, b, b] =
          (rootRest (g.wDLights.pathRepl S')).2.absVal D ![x, b, b] := by
  set H := g.dropComp j with hHdef
  have hH : ∀ c ∈ H.wDLights.comps, ErrMain_offT c := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := (G11.mem_wDLights H c).1 hc
    obtain ⟨h1, h2, h3, h4⟩ := hrest c₀ hc₀
    refine ⟨h1, h2, fun u hu e => h3 (e ▸ hu), fun q w hw e => h4 ?_⟩
    simp only [Comp.wDLight] at hw
    simp [hw, e]
  have hdots : ∀ c ∈ g.wDLights.comps, c.kind = .dot → c ∈ H.wDLights.comps := by
    intro c hc hkc
    rcases List.mem_cons.1 ((ErrMain_wDLights_perm g j hk).mem_iff.1 hc) with h | h
    · rw [h, hk] at hkc; cases hkc
    · exact h
  have hK : ∀ lK : List (Comp (Atom 3 n) × Bool), lK.map Prod.fst = H.wDLights.comps →
      ∀ c ∈ ErrMain_repl lK, c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 ∧ .inl 0 ∉ c.minor := by
    intro lK hlK c hc
    have := ErrMain_piece_atoms (· ≠ .inl 0) lK (fun p hp => by
      have := hH p.1 (by rw [← hlK]; exact List.mem_map.2 ⟨p, hp, rfl⟩)
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩) c (List.mem_of_mem_filter hc)
    exact ⟨this.1, this.2.1, fun h => this.2.2 _ h rfl⟩
  have e : rootRest g = H.rootGraph v := rootRest_eq g j v hk hxy fun c hc => (hrest c hc).1
  revert S hS
  rw [e]
  intro S hS
  rcases v with a | i
  · obtain ⟨lK, hlK, hel, hP, hco⟩ := ErrMain_gamma_ext H a (H.rootGraph (.inl a)).2 rfl S hS
    have hel' : ∀ p ∈ lK, p.2 = true → g.wDLights.pathEligB p.1 = true := by
      intro p hp ht
      have hid : ∀ c : Comp (Atom 3 n), c.map id = c := fun c => by cases c; simp [Comp.map]
      refine ErrMain_pathElig g.wDLights (H.rootGraph (.inl a)).2.wDLights id (fun u hu => hu)
        (fun c hc hkc => ?_) p.1 (by have := hel p hp ht; rw [← hid p.1] at this; exact this)
      refine reach_of_rel _ ⟨c, ?_, hkc, rfl, rfl⟩
      exact (ErrMain_wDLights_dot H a).mem_iff.2 (List.mem_cons_of_mem _ (hdots c hc hkc))
    obtain ⟨S', hS', j', hR', hfilt, -⟩ := ErrMain_gside g j _ hv hk hlab hxy hH lK hlK hel'
    refine ⟨S', hS', j', hR', fun ι _ _ D x b => ?_⟩
    rw [ErrMain_rootAbs hR' D x b]
    refine (ErrMain_absVal_perm (Γ₂ := ((⟨ErrMain_repl lK, H.coeff⟩ : Graph 3 n).rootGraph
      (.inl a)).2) (hP.trans (List.perm_append_singleton _ _).symm) hco D _).trans ?_
    rw [ErrMain_absVal_rootGraph _ _ hv (hK lK hlK) D x b]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [((hfilt).map _).prod_eq]
    rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    obtain ⟨lK, hlK, hel, heq⟩ := ErrMain_gamma_int H i (H.rootGraph (.inr i)).2
      (ErrMain_rootAt_eq H i) hH S hS
    have hY : (H.rootGraph (.inr i)).2.wDLights.comps =
        H.wDLights.comps.map (Comp.map (ErrMain_rootMap i)) :=
      (congrArg (fun G : Graph 3 m => G.wDLights.comps) (ErrMain_rootAt_eq H i)).trans
        (ErrMain_wDLights_map H i)
    have hel' : ∀ p ∈ lK, p.2 = true → g.wDLights.pathEligB p.1 = true := by
      intro p hp ht
      refine ErrMain_pathElig g.wDLights (H.rootGraph (.inr i)).2.wDLights (ErrMain_rootMap i)
        (fun u hu => ?_) (fun c hc hkc => ?_) p.1 (hel p hp ht)
      · rcases u with a | k
        · rfl
        · simp at hu
      · refine reach_of_rel _ ⟨c.map (ErrMain_rootMap i), ?_, hkc, rfl, rfl⟩
        rw [hY]
        exact List.mem_map.2 ⟨c, hdots c hc hkc, rfl⟩
    obtain ⟨S', hS', j', hR', hfilt, -⟩ := ErrMain_gside g j _ hv hk hlab hxy hH lK hlK hel'
    refine ⟨S', hS', j', hR', fun ι _ _ D x b => ?_⟩
    rw [ErrMain_rootAbs hR' D x b]
    refine ((congrArg (fun G : Graph 3 m => G.absVal D ![x, b, b]) heq).trans
      (congrArg (fun G : Graph 3 m => G.absVal D ![x, b, b])
        (ErrMain_rootAt_eq ⟨ErrMain_repl lK, H.coeff⟩ i)).symm).trans
      ((ErrMain_absVal_rootGraph _ _ hv (hK lK hlK) D x b).trans ?_)
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [((hfilt).map _).prod_eq]
    rfl

end Transfer

/-! ## The root atom and the tip -/

section RootTip

variable {n : ℕ}

/-- A dotted block of `⊕` or `⊖` with an internal atom gives a dotted edge from `⊕` or `⊖` to an
internal atom (`ErrForms.CaseB`), when no dotted edge is at `⊗`. -/
private theorem ErrMain_caseB_of_block {g : Graph 3 n}
    (hT : ∀ c ∈ g.comps, c.kind = .dot → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0) {e : Fin 3}
    (he : e = 1 ∨ e = 2) {b : Fin n} (h : g.SameBlock (.inl e) (.inr b)) : CaseB g := by
  by_contra hB
  have key : ∀ w, g.dotGraph.Reachable (.inl e) w → w = .inl 1 ∨ w = .inl 2 := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => rcases he with rfl | rfl <;> simp
    | tail _ hadj ih =>
      rename_i u w _
      rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
      have hu : u = .inl 1 ∨ u = .inl 2 := ih
      rcases hadj.2 with ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩
      · obtain ⟨-, h0⟩ := hT c hc hk
        rcases hy : c.y with a | k
        · fin_cases a
          · exact absurd hy h0
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact absurd ⟨c, hc, by rw [hk]; rfl, Or.inl ⟨hu, by rw [hy]; rfl⟩⟩ hB
      · obtain ⟨h0, -⟩ := hT c hc hk
        rcases hx : c.x with a | k
        · fin_cases a
          · exact absurd hx h0
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact absurd ⟨c, hc, by rw [hk]; rfl, Or.inr ⟨hu, by rw [hx]; rfl⟩⟩ hB
  rcases key _ h with h' | h' <;> cases h'

/-- `⊕` or `⊖` in one dotted block with an internal atom is a `⊕`-recollision graph at
`𝔟₁ = 𝔟₂`. -/
private theorem ErrMain_diagRecoll {g : Graph 3 n} {e : Fin 3} (he : e = 1 ∨ e = 2) {b : Fin n}
    (h : g.SameBlock (.inl e) (.inr b)) : g.DiagRecoll := by
  obtain ⟨B, hB, h1, h2⟩ := (g.sameBlock_iff_mem_dotBlocks _ _).1 h
  simp only [Graph.DiagRecoll, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    List.contains_iff_mem]
  exact ⟨B, hB, by rcases he with rfl | rfl <;> simp [h1], .inr b, h2, rfl⟩

/-- **The root atom and the tip** ([II, Claim 8.6], properties (3)–(4) of the rooting at the
external atoms): for root data of `g` with the kinds of [II, Def 3.2] and the rooting at the
external atoms when `g` has an internal atom and is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`, the
root atom is internal, or `𝔟` lies in a waved or dotted block of the core, or `g` has no internal
atom; with the root atom internal and `𝔟` isolated in the core, a solid or diffusive tip ends at
an internal atom. -/
private theorem ErrMain_rootTip {g : Graph 3 n} {j : Fin g.comps.length} {v : Atom 3 n} {N : ℕ}
    (hR : Rooted g j v) (hK : g.TKinds N) (hRE : n ≠ 0 → ¬ g.DiagRecoll → g.RootedAtExt) :
    ((∃ i, v = .inr i) ∨ CaseB g ∨ n = 0) ∧
      (¬ CaseB g → (∃ i, v = .inr i) → ∃ y, TipAt g y) := by
  have hT : ∀ c ∈ g.comps, c.kind = .dot → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc hk
    have := atT_eq_false hR hc (by rw [hk]; simp)
    simp only [atT, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at this
    exact this
  -- an external atom identified with an internal one is `⊕` or `⊖` in a recollision block
  have hpin : ∀ e : Fin 3, ¬ g.Unpinned (.inl e) → ¬ g.DiagRecoll → False := by
    intro e hu hD
    simp only [Graph.Unpinned, Sum.isLeft_inl, true_and, not_forall, not_not] at hu
    obtain ⟨b, hb⟩ := hu
    fin_cases e
    · have := reach_dot_isolated (fun c hc hk => (hT c hc hk)) hb
      cases this
    · exact hD (ErrMain_diagRecoll (Or.inl rfl) hb)
    · exact hD (ErrMain_diagRecoll (Or.inr rfl) hb)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    exact ⟨Or.inr (Or.inr rfl), fun _ ⟨i, _⟩ => i.elim0⟩
  by_cases hD : g.DiagRecoll
  · have hB : CaseB g := by
      simp only [Graph.DiagRecoll, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
        List.contains_iff_mem] at hD
      obtain ⟨B, hB, he, u, hu, hr⟩ := hD
      rcases u with a | b
      · simp at hr
      rcases he with he | he
      · exact ErrMain_caseB_of_block hT (Or.inl rfl)
          ((g.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, he, hu⟩)
      · exact ErrMain_caseB_of_block hT (Or.inr rfl)
          ((g.sameBlock_iff_mem_dotBlocks _ _).2 ⟨B, hB, he, hu⟩)
    exact ⟨Or.inr (Or.inl hB), fun h => absurd hB h⟩
  obtain ⟨⟨-, hDT⟩, hplus, -⟩ := hRE hn.ne' hD
  have hroot : g.comps[j] ∈ g.comps := List.getElem_mem _
  refine ⟨?_, fun hB _ => ?_⟩
  · rcases v with a | i
    · have := (hDT _ hroot (by rw [hR.kind]; rfl)).1 hR.ends.1
      rw [hR.ends.2] at this
      exact (hpin a this hD).elim
    · exact Or.inl ⟨i, rfl⟩
  · rcases hplus with ⟨c, hc, hk, h⟩ | ⟨c, hc, hdf, h⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨y, hy⟩ := Sum.isRight_iff.1 h2
        exact ⟨y, c, hc, Or.inl (by rw [hk]; rfl), Or.inl ⟨Or.inl h1, hy⟩⟩
      · obtain ⟨y, hy⟩ := Sum.isRight_iff.1 h2
        exact ⟨y, c, hc, Or.inl (by rw [hk]; rfl), Or.inr ⟨Or.inl h1, hy⟩⟩
    · have hth : ∃ o, c.kind = .theta o := by
        have := List.all_eq_true.1 hK c hc
        simp only [Comp.isTKind, Bool.and_eq_true] at this
        generalize c.kind = κ at hdf this ⊢
        cases κ <;> simp_all [Kind.isDiffusive]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hy : c.y with e | y
        · rw [hy] at h2; exact (hpin e h2 hD).elim
        · exact ⟨y, c, hc, Or.inr hth, Or.inl ⟨Or.inl h1, hy⟩⟩
      · rcases hx : c.x with e | y
        · rw [hx] at h2; exact (hpin e h2 hD).elim
        · exact ⟨y, c, hc, Or.inr hth, Or.inr ⟨Or.inl h1, hx⟩⟩

end RootTip

/-! ## One graph of `errMat` -/

section OneGraph

/-- The rooted graph has the kinds of `Err` if the graph has them. -/
private theorem ErrMain_rootRest_tKindsErr {n N : ℕ} (g : Graph 3 n) (j : Fin g.comps.length)
    (v : Atom 3 n) (hk : g.comps[j].kind = .theta [])
    (hxy : g.comps[j].x = .inl 0 ∧ g.comps[j].y = v)
    (hrest : ∀ c ∈ (g.dropComp j).comps, c.x ≠ .inl 0) (hK : g.TKindsErr N) :
    (rootRest g).2.TKindsErr N := by
  rw [rootRest_eq g j v hk hxy hrest]
  have hK' : ∀ c ∈ (g.dropComp j).comps, c.isTKind N || (c.minor.isEmpty &&
      match c.kind with | .wD _ _ => true | _ => false) = true :=
    fun c hc => List.all_eq_true.1 hK c (List.mem_of_mem_eraseIdx hc)
  unfold Graph.TKindsErr
  rw [List.all_eq_true]
  rcases v with a | i
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hK' c hc
    · cases hc with
      | head => rfl
      | tail _ h => cases h
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    have key : ∀ {V W : Type} (f : V → W) (c : Comp V), (c.isTKind N || (c.minor.isEmpty &&
        match c.kind with | .wD _ _ => true | _ => false)) = true →
        ((c.map f).isTKind N || ((c.map f).minor.isEmpty &&
          match (c.map f).kind with | .wD _ _ => true | _ => false)) = true := by
      intro V W f c h
      rw [isTKind_map]
      simpa only [Comp.map, List.isEmpty_map] using h
    exact key _ c₀ (hK' c₀ hc₀)

/-- Along `adm(c₀, c₁)`, `W ≥ W₁` for `L` large. -/
private theorem ErrMain_L₀ {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) (W₁ : ℝ) :
    ∃ L₀ : ℕ, ∀ W L : ℕ, L₀ ≤ L → (W, L) ∈ adm c₀ c₁ → W₁ ≤ W := by
  refine ⟨⌈(max W₁ 1) ^ (1 / c₁)⌉₊, fun W L hL hadm => ?_⟩
  have h1 : (max W₁ 1) ^ (1 / c₁) ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have h2 : max W₁ 1 ≤ (L : ℝ) ^ c₁ := by
    calc max W₁ 1 = ((max W₁ 1) ^ (1 / c₁)) ^ c₁ := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (L : ℝ) ^ c₁ := Real.rpow_le_rpow (by positivity) h1 hc₁.le
  exact (le_max_left _ _).trans (h2.trans hadm.1)

/-- **One graph of `errMat`** ([I, (8.17)] for one graph, via [I, (8.20)] and [II, Claims 8.6,
8.7]): for a graph `g` of the form [II, Def 3.3 (4)], normal regular, with the kinds of `Err` with
labels in `[4, N]`, [II, Def 3.2 (9)], doubly connected, with only diffusive components at `⊗`,
dotted edges forming a forest, rooted at the external atoms when it has an internal atom and is not
a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`, and diagonal scaling order `n_𝔟 ≥ e + 1`: under the local
law there is `K ≥ 0` such that for all `τ, D' > 0`, for `L ≥ L₀` along `adm(c₀, c₁)`,
`E|𝒢_{x, 𝔟𝔟}| ≤ K W^τ (W^{−e d/2} B^{1/2}_{x𝔟} + 1_{x = 𝔟} W^{−(e − 1)d/2}) + W^{−D'}`. -/
private theorem ErrMain_graph (hLL : LocalLawStmt) {d : ℕ} (hd : 8 ≤ d) (P : Profile d)
    {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    {N : ℕ} {Sig : ℕ → Expansion 2} (hSE : SelfEnergiesUpTo d (smatVar P) Sig N) {n : ℕ}
    (g : Graph 3 n) (hTR : g.ThetaRooted) {C : ℕ} (hN : g.Normal C) (hK : g.TKindsErr N)
    (hAE : g.AtExternals) (hDC : g.DoublyConnected) (hTD : g.TensorDiffusive)
    (hDA : g.DotsAcyclic) (hRE : n ≠ 0 → ¬ g.DiagRecoll → g.RootedAtExt) (e : ℕ)
    (he : (e : ℤ) + 1 ≤ g.diagOrd) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L,
          ∫ ω, ‖(rootRest g).2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![x, b, b] ω‖
              ∂(rbmLaw d P (sizeOf W L)) ≤
            K * ((W : ℝ) ^ τ * ((W : ℝ) ^ (-((e : ℝ) * d / 2)) * Real.sqrt (bB d L W x b) +
              (if x = b then 1 else 0) * (W : ℝ) ^ (-(((e : ℝ) - 1) * d / 2)))) +
              (W : ℝ) ^ (-D') := by
  obtain ⟨j, v, hv, hk, -, hlab, hxy, hrest, -⟩ := hTR
  set Γ := (rootRest g).2 with hΓ
  have hΓK : Γ.TKindsErr N :=
    ErrMain_rootRest_tKindsErr g j v hk hxy (fun c hc => (hrest c hc).1) hK
  obtain ⟨hGN, hGT, hGAE, hGDC, hGTD, hGDA, hGDR, hGRE, -, hGdiag⟩ :=
    G11.wDLights_props g N C hK hN hAE hDC hTD hDA
  have hGRE' : n ≠ 0 → ¬ g.wDLights.DiagRecoll → g.wDLights.RootedAtExt :=
    fun h0 h1 => hGRE.2 (hRE h0 fun h2 => h1 (hGDR.2 h2))
  set F : ∀ W L : ℕ, Zd d L → Zd d L → ℝ := fun W L x b =>
    (W : ℝ) ^ (-((e : ℝ) * d / 2)) * Real.sqrt (bB d L W x b) +
      (if x = b then 1 else 0) * (W : ℝ) ^ (-(((e : ℝ) - 1) * d / 2)) with hF
  refine ⟨(Γ.wDLights.pathElig.powerset.card : ℝ), by positivity, fun τ hτ D' hD' => ?_⟩
  -- the label-free graphs `Γ_S`, one at a time
  have hS : ∀ S ∈ Γ.wDLights.pathElig.powerset, ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, 1 ≤ W₀ ∧
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ G : Matrix (Zd d L) (Zd d L) ℂ,
          (∀ p q, ‖entryErr G (msc z) p q‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W p q)) →
          ∀ x b : Zd d L, (Γ.wDLights.pathRepl S).absVal (gData (Smat P.ψ W L) z Sig G)
            ![x, b, b] ≤ (W : ℝ) ^ (τ / 2) * F W L x b := by
    intro S hSm
    obtain ⟨S', hS', j', hR', habs⟩ := ErrMain_transfer g j v hv hk hlab hxy
      (fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1, (hrest c hc).2.2.1, (hrest c hc).2.2.2⟩) S
      (Finset.mem_powerset.1 hSm)
    obtain ⟨⟨C', hN'⟩, hT', -, hDC', -, hDA', -, -, -, hRE', -, hdiag'⟩ :=
      labelPaths n _ N g.wDLights hGN hGT hGAE hGDC hGTD hGDA hGRE' S' hS'
    obtain ⟨hR1, hTip⟩ := ErrMain_rootTip hR' hT' hRE'
    obtain ⟨τ', hτ', W₁, hW₁⟩ := ErrMain_formKeyAbs d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE
      _ j' v C' hR' hN' hDC' hT' hR1 hTip (τ / 2) (by positivity)
    have heff : (e : ℤ) + 1 ≤ effOrd (g.wDLights.pathRepl S') := by
      have h1 := diagOrd_le_effOrd hR' ((Graph.dotsAcyclic_iff_dotExcess_eq_zero _).1 hDA')
      have h2 : (0 : ℤ) ≤ (S'.card : ℤ) := by positivity
      linarith
    have heff' : (e : ℝ) + 1 ≤ (effOrd (g.wDLights.pathRepl S') : ℝ) := by exact_mod_cast heff
    refine ⟨τ', hτ', max W₁ 1, le_max_right _ _, fun W L _ hadm hW z hz G hG x b => ?_⟩
    have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [habs]
    refine (hW₁ W L hadm ((le_max_left _ _).trans hW) z hz G hG x b).trans ?_
    simp only [hF]
    have e1 : (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 1) * d / 2)) ≤
        (W : ℝ) ^ (-((e : ℝ) * d / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
    have e2 : (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 2) * d / 2)) ≤
        (W : ℝ) ^ (-(((e : ℝ) - 1) * d / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
    have hi0 : (0 : ℝ) ≤ if x = b then 1 else 0 := by split_ifs <;> norm_num
    have hτ0 : (0 : ℝ) ≤ (W : ℝ) ^ (τ / 2) := by positivity
    have hs0 := Real.sqrt_nonneg (bB d L W x b)
    calc (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 1) * d / 2)) *
          Real.sqrt (bB d L W x b) + (if x = b then 1 else 0) * ((W : ℝ) ^ (τ / 2) *
          (W : ℝ) ^ (-(((effOrd (g.wDLights.pathRepl S') : ℝ) - 2) * d / 2)))
        ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-((e : ℝ) * d / 2)) * Real.sqrt (bB d L W x b) +
          (if x = b then 1 else 0) *
            ((W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(((e : ℝ) - 1) * d / 2))) := by
          gcongr
      _ = _ := by ring
  choose! τf hτf W₀f hW₀f hbd using hS
  have hne : (Γ.wDLights.pathElig.powerset).Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
  set τ' := (Γ.wDLights.pathElig.powerset).inf' hne τf with hτ'def
  have hτ' : 0 < τ' := (Finset.lt_inf'_iff hne).2 fun S hS => hτf S hS
  set W₀ := (Γ.wDLights.pathElig.powerset).sup' hne W₀f with hW₀def
  have hβ : ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ (a b : Zd d L) (G : Matrix (Zd d L) (Zd d L) ℂ),
        (∀ x y, ‖entryErr G (msc z) x y‖ ≤ (W : ℝ) ^ τ' * Real.sqrt (bB d L W x y)) →
        ∑ S ∈ Γ.wDLights.pathElig.powerset, (Γ.wDLights.pathRepl S).absVal
          (gData (Smat P.ψ W L) z Sig G) ![a, b, b] ≤
          (Γ.wDLights.pathElig.powerset.card : ℝ) * ((W : ℝ) ^ (τ / 2) * F W L a b) := by
    refine ⟨W₀, fun W L _ hadm hW z hz x b G hG => ?_⟩
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun S hSm => ?_
    have hW1 : (1 : ℝ) ≤ W := (hW₀f S hSm).trans ((Finset.le_sup' W₀f hSm).trans hW)
    refine hbd S hSm W L hadm ((Finset.le_sup' W₀f hSm).trans hW) z hz G (fun p q => ?_) x b
    refine (hG p q).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    exact Real.rpow_le_rpow_of_exponent_le hW1 (Finset.inf'_le τf hSm)
  obtain ⟨L₀, hL₀⟩ := ErrExp.expBound hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE _ Γ hΓK τ' hτ'
    (fun W L _ x b => (Γ.wDLights.pathElig.powerset.card : ℝ) * ((W : ℝ) ^ (τ / 2) * F W L x b))
    hβ (τ / 2) (by positivity) D' hD'
  refine ⟨L₀, fun W L _ hL hadm z hz x b => (hL₀ W L hL hadm z hz x b).trans (le_of_eq ?_)⟩
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add' hW0 (by positivity)]; ring_nf
  rw [← this]
  ring

end OneGraph

/-! ## The sum over the graphs: [I, (8.17)] -/

section Sum

/-- The norm of the expectation of a finite sum is at most the sum of the expectations of the
norms. -/
private theorem ErrMain_normInt {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : α → Ω → ℂ) (l : List α) (hf : ∀ a ∈ l, Integrable (f a) μ) :
    Integrable (fun ω => (l.map fun a => f a ω).sum) μ ∧
      ‖∫ ω, (l.map fun a => f a ω).sum ∂μ‖ ≤ (l.map fun a => ∫ ω, ‖f a ω‖ ∂μ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hi, hb⟩ := ih fun b hb => hf b (List.mem_cons_of_mem _ hb)
    have ha := hf a (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨ha.add hi, ?_⟩
    rw [integral_add ha hi]
    exact (norm_add_le _ _).trans (add_le_add (norm_integral_le_integral_norm _) hb)

/-- The bounds of `ErrMain_graph` add up over a list of graphs. -/
private theorem ErrMain_sumBound {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2)
    {c₀ c₁ κ ε : ℝ} (F : ∀ _W L : ℕ, Zd d L → Zd d L → ℝ) (l : Expansion 3)
    (h : ∀ g ∈ l, ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L,
          ∫ ω, ‖(rootRest g.2).2.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![x, b, b] ω‖
              ∂(rbmLaw d P (sizeOf W L)) ≤ K * ((W : ℝ) ^ τ * F W L x b) + (W : ℝ) ^ (-D')) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, 0 < τ → ∀ D' : ℝ, 0 < D' →
      ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x b : Zd d L,
          (l.map fun g => ∫ ω, ‖(rootRest g.2).2.valR ⟨Pexp (Smat P.ψ W L)⟩
              (rbmData d P Sig W L z) ![x, b, b] ω‖ ∂(rbmLaw d P (sizeOf W L))).sum ≤
            K * ((W : ℝ) ^ τ * F W L x b) + l.length * (W : ℝ) ^ (-D') := by
  induction l with
  | nil => exact ⟨0, le_rfl, fun τ _ D' _ => ⟨0, fun W L _ _ _ z _ x b => by simp⟩⟩
  | cons g l ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := h g (List.mem_cons_self ..)
    obtain ⟨K₂, hK₂, h₂⟩ := ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun τ hτ D' hD' => ?_⟩
    obtain ⟨L₁, hL₁⟩ := h₁ τ hτ D' hD'
    obtain ⟨L₂, hL₂⟩ := h₂ τ hτ D' hD'
    refine ⟨max L₁ L₂, fun W L _ hL hadm z hz x b => ?_⟩
    have e1 := hL₁ W L ((le_max_left _ _).trans hL) hadm z hz x b
    have e2 := hL₂ W L ((le_max_right _ _).trans hL) hadm z hz x b
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

end Sum

set_option maxHeartbeats 1000000 in
/-- **[I, (8.17)] with [I, (8.20)]**: under the local law [I, Theorem 1.4], for an `n`-th order
`T`-equation `𝒬` with error order `D ≥ n + 2` and self-energies `Σ_4, …, Σ_n`, the expectation of
the graphs of `A` in which `⊕`, `⊖` do not lie in one dotted block and of the graphs of `Err`,
rooted at `(x, 𝔟, 𝔟)`, satisfies `|E Γ_{x, 𝔟𝔟}| ≤ W^τ W^{−(n−1)d/2}` and
`Σ_x B_{𝔞x} |E Γ_{x, 𝔟𝔟}| ≤ W^τ W^{−(n+1)d/2}` for `L ≥ L₀` along `adm(c₀, c₁)`. -/
theorem errBound : errBoundStmt := by
  intro hLL d hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε Sig n D 𝒬 hn hnD hS hNR hSE τ hτ
  -- the window `adm(c₀', c₁')` with `c₀' + c₁' < 1` contains `adm(c₀, c₁)`
  set c₀' := min c₀ (1 / 2) with hc₀'def
  set c₁' := min c₁ (1 / 4) with hc₁'def
  have hc₀' : 0 < c₀' := lt_min hc₀ (by norm_num)
  have hc₁' : 0 < c₁' := lt_min hc₁ (by norm_num)
  have hc' : c₀' + c₁' < 1 := by
    have := min_le_right c₀ (1 / 2); have := min_le_right c₁ (1 / 4); linarith
  have hadm' : ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → (W, L) ∈ adm c₀' c₁' := by
    intro W L _ h
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hL1 (min_le_left _ _)).trans h.1,
      h.2.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_left c₀ (1 / 2)]))⟩
  have hd2 : 2 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨-, -, -, -, hShape, hTR, hDef⟩ := hS
  have hSE' : SelfEnergiesUpTo d (smatVar P) Sig (n - 1) :=
    fun k h4 hk he => hSE k h4 (by omega) he
  -- the graph facts of the graphs of `errMat`
  have hfacts : ∀ g ∈ ErrBound.errList 𝒬, g.2.ThetaRooted ∧ (∃ C, g.2.Normal C) ∧
      g.2.TKindsErr (n - 1) ∧ g.2.AtExternals ∧ g.2.DoublyConnected ∧ g.2.TensorDiffusive ∧
      g.2.DotsAcyclic ∧ (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt) ∧
      (n : ℤ) + 1 ≤ g.2.diagOrd := by
    intro g hgl
    have hall : g ∈ 𝒬.R ++ 𝒬.A ++ 𝒬.Q ++ 𝒬.Err := by
      rcases List.mem_append.1 hgl with h | h
      · simp [(List.mem_filter.1 h).1]
      · simp [h]
    have hAQE : g ∈ 𝒬.toTRec.A ++ 𝒬.toTRec.Q ++ 𝒬.toTRec.Err := by
      rcases List.mem_append.1 hgl with h | h
      · simp [TEqRec.toTRec, (List.mem_filter.1 h).1]
      · simp [TEqRec.toTRec, h]
    obtain ⟨-, -, -, -, -, -, hdiag, -⟩ := ErrBound.decomp n D 𝒬 hn hnD hShape hTR hDef g hgl
    have hG : (∃ C, g.2.Normal C) ∧ g.2.TKindsErr (n - 1) ∧ g.2.AtExternals ∧
        g.2.DoublyConnected := by
      rcases List.mem_append.1 hgl with h | h
      · obtain ⟨h1, h2, h3, h4⟩ :=
          hShape.1.1 g (by simp [TEqRec.toTRec, (List.mem_filter.1 h).1])
        exact ⟨h1, Graph.tKindsErr_of_tKinds _ _ h2, h3, h4⟩
      · exact hShape.1.2 g h
    obtain ⟨-, hDall, -, -, -, -, hDroot, -⟩ := hDef
    obtain ⟨hTD, hdx, -, -⟩ := hDall g hall
    exact ⟨hTR g hall, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2, hTD,
      (Graph.dotsAcyclic_iff_dotExcess_eq_zero _).2 hdx, hDroot g hAQE, hdiag⟩
  -- one graph at a time, then the sum
  obtain ⟨K, hK0, hsum⟩ := ErrMain_sumBound P Sig (c₀ := c₀') (c₁ := c₁') (κ := κ) (ε := ε)
    (fun W L x b => (W : ℝ) ^ (-((n : ℝ) * d / 2)) * Real.sqrt (bB d L W x b) +
      (if x = b then 1 else 0) * (W : ℝ) ^ (-(((n : ℝ) - 1) * d / 2))) (ErrBound.errList 𝒬)
    fun g hgl => by
      obtain ⟨hTR', ⟨C, hN⟩, hK, hAE, hDC, hTD, hDA, hRE, hdiag⟩ := hfacts g hgl
      exact ErrMain_graph hLL hd P hc₀' hc₁' hc' hκ hε hSE' g.2 hTR' hN hK hAE hDC hTD hDA hRE n
        hdiag
  -- the constants
  obtain ⟨len, hlen⟩ : ∃ len : ℝ, len = (ErrBound.errList 𝒬).length := ⟨_, rfl⟩
  simp only [← hlen] at hsum
  obtain ⟨W_VK, hVK⟩ := Smat_isVarKernel_adm d P c₀' c₁' hc₀' hc₁'
  obtain ⟨C₂, hC₂0, hconv⟩ := conv2 hd
  obtain ⟨Wl, -, hlog⟩ := logF_le_rpow (c₀ := c₀') hc₁' (δ := τ / 4) (by positivity)
  obtain ⟨W₂, -, htwo⟩ := two_mul_le_of_adm (c₁ := c₁') hc₀' (by linarith)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = K * C₂ + 2 * K + len := ⟨_, rfl⟩
  set D' : ℝ := ((n : ℝ) + 1) * d / 2 + d / c₁' + 1 with hD'def
  have hD' : 0 < D' := by positivity
  obtain ⟨L₁, hL₁⟩ := hsum (τ / 2) (by positivity) D' hD'
  obtain ⟨L₂, hL₂⟩ := ErrMain_L₀ (c₀ := c₀') hc₁'
    (max (max 1 W_VK) (max (max Wl W₂) ((max 1 M) ^ (1 / (τ / 4)))))
  refine ⟨max L₁ L₂, fun W L _ hL hadm z hz a b => ?_⟩
  have hadm₁ := hadm' W L hadm
  have hW := hL₂ W L ((le_max_right _ _).trans hL) hadm₁
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hVKW := hVK W L hadm₁ ((le_max_right _ _).trans ((le_max_left _ _).trans hW))
  have hzim : 0 < z.im := im_pos_of_specDom hW1n hz
  have hL2 : 2 * W ≤ L := htwo W L hadm₁
    ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hW)))
  have hlogW : logF L W ≤ (W : ℝ) ^ (τ / 4) := hlog W L hadm₁
    ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hW))) hL1
  have hMW : M ≤ (W : ℝ) ^ (τ / 4) :=
    const_le_rpow' (by positivity) ((le_max_right _ _).trans ((le_max_right _ _).trans hW))
  -- the entries of `errMat` through the graphs
  have hent : ∀ x : Zd d L, ‖errMat d P Sig 𝒬 W L z x b‖ ≤
      K * ((W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (-((n : ℝ) * d / 2)) * Real.sqrt (bB d L W x b) +
        (if x = b then 1 else 0) * (W : ℝ) ^ (-(((n : ℝ) - 1) * d / 2)))) +
        len * (W : ℝ) ^ (-D') := by
    intro x
    refine le_trans ?_ (hL₁ W L ((le_max_left _ _).trans hL) hadm₁ z hz x b)
    set f : (Σ n, Graph 3 n) → Sample (Zd d L) → ℂ := fun g => (rootRest g.2).2.valR
      ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) ![x, b, b] with hf
    have hint : ∀ g ∈ ErrBound.errList 𝒬, Integrable (f g) (gaussLaw (Smat P.ψ W L)) := by
      intro g hgl
      obtain ⟨⟨j, v, -, hk, -, -, hxy, hrest, -⟩, -, hK, -⟩ := hfacts g hgl
      exact MainCancel_valR_integrable_err P Sig W L z hVKW hzim _
        (ErrMain_rootRest_tKindsErr g.2 j v hk hxy (fun c hc => (hrest c hc).1) hK) _
    have hm : errMat d P Sig 𝒬 W L z x b = ∫ ω, ((ErrBound.errList 𝒬).map fun g => f g ω).sum
        ∂(gaussLaw (Smat P.ψ W L)) := rfl
    rw [hm]
    exact (ErrMain_normInt (gaussLaw (Smat P.ψ W L)) f _ hint).2
  -- the exponents
  have hτ2 : (W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4) = (W : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hτ1 : (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (τ / 2) = (W : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hA1 : (1 : ℝ) ≤ (W : ℝ) ^ (τ / 4) := Real.one_le_rpow hW1 (by positivity)
  have hA2 : (1 : ℝ) ≤ (W : ℝ) ^ (τ / 2) := Real.one_le_rpow hW1 (by positivity)
  set E₀ := (W : ℝ) ^ (-((n : ℝ) * d / 2)) with hE₀
  set E₁ := (W : ℝ) ^ (-(((n : ℝ) - 1) * d / 2)) with hE₁
  set E₂ := (W : ℝ) ^ (-(((n : ℝ) + 1) * d / 2)) with hE₂
  have hE₀s : E₀ * (W : ℝ) ^ (-((d : ℝ) / 2)) = E₂ := by
    rw [hE₀, hE₂, ← Real.rpow_add hW0]; ring_nf
  have hE₁d : (W : ℝ) ^ (-(d : ℝ)) * E₁ = E₂ := by
    rw [hE₁, hE₂, ← Real.rpow_add hW0]; ring_nf
  have hE₂₁ : E₂ ≤ E₁ := Real.rpow_le_rpow_of_exponent_le hW1 (by nlinarith)
  have hE₀0 : 0 ≤ E₀ := by positivity
  have hE₂0 : 0 ≤ E₂ := by positivity
  have hD₁ : (W : ℝ) ^ (-D') ≤ E₁ := Real.rpow_le_rpow_of_exponent_le hW1 (by
    rw [hD'def]; have : 0 ≤ (d : ℝ) / c₁' := by positivity
    nlinarith)
  have hD₂ : (W : ℝ) ^ (-D') * ((W : ℝ) ^ ((d : ℝ) / c₁') * (W : ℝ) ^ (-(d : ℝ))) ≤ E₂ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by rw [hD'def]; nlinarith)
  have hsq : ∀ x y : Zd d L, Real.sqrt (bB d L W x y) ≤ (W : ℝ) ^ (-((d : ℝ) / 2)) :=
    fun x y => sqrt_bB_le hd2 hW1n x y
  have hB0 : ∀ x y : Zd d L, 0 ≤ bB d L W x y := fun x y => (bB_pos₁ hW1n x y).le
  refine ⟨(hent a).trans ?_, ?_⟩
  · -- the entry
    have h1 : E₀ * Real.sqrt (bB d L W a b) ≤ E₁ :=
      (mul_le_mul_of_nonneg_left (hsq a b) hE₀0).trans (hE₀s.trans_le hE₂₁)
    have h2 : (if a = b then (1 : ℝ) else 0) * E₁ ≤ E₁ := by
      have : (0 : ℝ) ≤ E₁ := by positivity
      split_ifs <;> simp [this]
    have hlen0 : 0 ≤ len := by rw [hlen]; positivity
    calc K * ((W : ℝ) ^ (τ / 2) * (E₀ * Real.sqrt (bB d L W a b) +
          (if a = b then 1 else 0) * E₁)) + len * (W : ℝ) ^ (-D')
        ≤ K * ((W : ℝ) ^ (τ / 2) * (E₁ + E₁)) + len * ((W : ℝ) ^ (τ / 2) * E₁) := by
          gcongr
          exact hD₁.trans (le_mul_of_one_le_left (by positivity) hA2)
      _ = (2 * K + len) * ((W : ℝ) ^ (τ / 2) * E₁) := by ring
      _ ≤ (W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (τ / 2) * E₁) := by
          gcongr
          calc 2 * K + len ≤ M := by linarith [mul_nonneg hK0 hC₂0]
            _ ≤ (W : ℝ) ^ (τ / 4) := hMW
            _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = (W : ℝ) ^ τ * E₁ := by rw [← hτ1]; ring
  · -- the `B`-sum
    have hcard : (Fintype.card (Zd d L) : ℝ) ≤ (W : ℝ) ^ ((d : ℝ) / c₁') := by
      have hLW : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁') := L_le_of_adm hc₁' hadm₁
      have hc : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by simp [Zd]
      rw [hc]
      calc (L : ℝ) ^ d ≤ ((W : ℝ) ^ (1 / c₁')) ^ d := pow_le_pow_left₀ (by positivity) hLW d
        _ = (W : ℝ) ^ ((d : ℝ) / c₁') := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf
    have hrow : ∑ x, bB d L W a x ≤ (W : ℝ) ^ ((d : ℝ) / c₁') * (W : ℝ) ^ (-(d : ℝ)) := by
      calc ∑ x, bB d L W a x ≤ ∑ _x : Zd d L, (W : ℝ) ^ (-(d : ℝ)) :=
            Finset.sum_le_sum fun x _ => bB_le_rpow hd2 hW1n a x
        _ = (Fintype.card (Zd d L) : ℝ) * (W : ℝ) ^ (-(d : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
    have hab : bB d L W a b ≤ (W : ℝ) ^ (-(d : ℝ)) := bB_le_rpow hd2 hW1n a b
    have hlog0 : 0 ≤ logF L W := logF_nonneg hW1n (by omega)
    have hlen0 : 0 ≤ len := by rw [hlen]; positivity
    calc ∑ x, bB d L W a x * ‖errMat d P Sig 𝒬 W L z x b‖
        ≤ ∑ x, bB d L W a x * (K * ((W : ℝ) ^ (τ / 2) * (E₀ * Real.sqrt (bB d L W x b) +
            (if x = b then 1 else 0) * E₁)) + len * (W : ℝ) ^ (-D')) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hent x) (hB0 a x)
      _ = K * (W : ℝ) ^ (τ / 2) * E₀ * ∑ x, bB d L W a x * Real.sqrt (bB d L W x b) +
            K * (W : ℝ) ^ (τ / 2) * (bB d L W a b * E₁) +
            len * (W : ℝ) ^ (-D') * ∑ x, bB d L W a x := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · congr 1
            · exact Finset.sum_congr rfl fun x _ => by ring
            · rw [Finset.sum_eq_single b]
              · simp only [ite_true]; ring
              · intro x _ hx; simp [hx]
              · simp
          · exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ K * (W : ℝ) ^ (τ / 2) * E₀ * (C₂ * logF L W * (W : ℝ) ^ (-((d : ℝ) / 2))) +
            K * (W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (-(d : ℝ)) * E₁) +
            len * (W : ℝ) ^ (-D') * ((W : ℝ) ^ ((d : ℝ) / c₁') * (W : ℝ) ^ (-(d : ℝ))) := by
          gcongr
          · exact hconv L W hW1n hL2 a b
      _ = (K * C₂ * logF L W + K) * ((W : ℝ) ^ (τ / 2) * E₂) +
            len * ((W : ℝ) ^ (-D') * ((W : ℝ) ^ ((d : ℝ) / c₁') * (W : ℝ) ^ (-(d : ℝ)))) := by
          linear_combination (K * (W : ℝ) ^ (τ / 2) * C₂ * logF L W) * hE₀s +
            (K * (W : ℝ) ^ (τ / 2)) * hE₁d
      _ ≤ (K * C₂ * (W : ℝ) ^ (τ / 4) + K) * ((W : ℝ) ^ (τ / 2) * E₂) + len * E₂ := by
          gcongr
      _ ≤ (M * (W : ℝ) ^ (τ / 4)) * ((W : ℝ) ^ (τ / 2) * E₂) := by
          have hX : 0 ≤ (W : ℝ) ^ (τ / 2) * E₂ := by positivity
          have h1 : K * ((W : ℝ) ^ (τ / 2) * E₂) ≤
              (K * (W : ℝ) ^ (τ / 4)) * ((W : ℝ) ^ (τ / 2) * E₂) :=
            mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK0 hA1) hX
          have h2 : len * E₂ ≤ len * (((W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 2)) * E₂) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE₂0
              (one_le_mul_of_one_le_of_one_le hA1 hA2)) hlen0
          have h3 : 0 ≤ (K * (W : ℝ) ^ (τ / 4)) * ((W : ℝ) ^ (τ / 2) * E₂) := by positivity
          rw [hM]
          linarith
      _ ≤ ((W : ℝ) ^ (τ / 4) * (W : ℝ) ^ (τ / 4)) * ((W : ℝ) ^ (τ / 2) * E₂) := by
          gcongr
      _ = (W : ℝ) ^ τ * E₂ := by rw [hτ2, ← hτ1]; ring

end RBM8D
