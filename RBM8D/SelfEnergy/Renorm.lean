import RBM8D.SelfEnergy.Entrywise
import RBM8D.SelfEnergy.Step

/-!
# The renormalized self-energies of [I, Def 8.2]

In [I, Def 8.2] the labels of the `Θ` edges read, at every lower order `l`, the matrix
`Σ̊_l = Σ^{(r)}_l − [Σ_x Σ^{(r)}_l(0, x)] S` ([I, (8.3)]) in place of `Σ_l`. Here `Σ̊_l` is a formal
sum of graphs on the data record:

* `Renorm.sig Sig`: at order `l`, every graph `Γ` of `Sig l` gives a graph `Γ'` with the
  same value that is normal regular with `x`, `y` internal or diagonal (`G13.dotContract`), and
  `Γ'` is followed by its c-term graph of value `−Σ_u Γ'_{xu} S_{xy}`: the atom `y` made internal
  and an edge `s_{xy}` added (`Renorm.ctermI`), or, for a diagonal `Γ'`, `y` identified with `x`,
  the dotted edge removed and `s_{xy}` added (`Renorm.ctermII`). A graph with a `×`-dotted loop
  has value `0` and no c-term graph.
* `Renorm.sigMat_eq`: on every record, `Σ̊_l(x, y) = Σ^{(r)}_l(x, y) − [Σ_u Σ^{(r)}_l(x, u)] S_{xy}`
  with `Σ^{(r)}_l = sigMat (Function.update (Renorm.sig Sig) l (Sig l)) S z l`: the graphs of
  `Sig l` read on the record of `Σ̊` below `l`. `Renorm.sigMat_smatVar`: for `smatVar P` and
  `Im z > 0` the row sum at `x` is the row sum at `0`, as printed in [I, (8.3)].
* `Renorm.shape_sig`: `Σ̊_l` has the shape of an `l`-th order self-energy when `Σ_l` has.
* `Renorm.selfEnergiesUpTo`: for `d ≥ 8`, if the even orders `4 ≤ k ≤ N` of `Sig` are
  self-energies for `smatVar P`, so are those of `Renorm.sig Sig`; the row sum of `Σ̊_l` is `0`
  for `W ≥ W₀`. `Renorm.kerSymm_kerBound` restates it for the kernel family `sigKer`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The c-term graphs -/

/-- The atom map that makes the external atom `y = 1` the internal atom `0`: `x ↦ x`,
`y ↦ inr 0`, `inr b ↦ inr (b + 1)`. -/
def Renorm.yAtom (n : ℕ) : Atom 2 n → Atom 2 (n + 1) :=
  Sum.elim (fun a => if a = 0 then .inl 0 else .inr 0) (fun b => .inr b.succ)

/-- The waved edge `s_{xy}` between the external atoms `x = 0` and `y = 1`. -/
def Renorm.sEdge {n : ℕ} : Comp (Atom 2 n) := mkC (.waved .s) (.inl 0) (.inl 1)

/-- The c-term graph of `Γ` ([I, (8.3)]): the external atom `y` of `Γ` becomes the new internal
atom `u`, the edge `s_{xy}` is added and the coefficient changes sign. Its value is
`−Σ_u Γ_{xu} S_{xy}` (`Renorm.val_ctermI`). -/
def Renorm.ctermI {n : ℕ} (Γ : Graph 2 n) : Graph 2 (n + 1) :=
  ⟨Γ.comps.map (Comp.map (Renorm.yAtom n)) ++ [Renorm.sEdge], -Γ.coeff⟩

/-- The c-term graph of a diagonal graph `Γ` whose `i`-th component is its dotted edge between
`x` and `y`: the dotted edge of `Renorm.ctermI Γ` between `x` and the new internal atom is
contracted, so `y` is identified with `x` and `s_{xy}` is added. -/
def Renorm.ctermII {n : ℕ} (Γ : Graph 2 n) (i : ℕ) (hi : i < Γ.comps.length) : Graph 2 n :=
  Contract.graph (Renorm.ctermI Γ) ⟨i, by simp [Renorm.ctermI]; omega⟩ 0 0

private theorem Renorm_val_map {ι V W : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

private theorem Renorm_elim_cons {ι : Type*} {n : ℕ} (x y u : ι) (t : Fin n → ι) :
    Sum.elim ![x, y] (Fin.cons (α := fun _ => ι) u t) ∘ Renorm.yAtom n = Sum.elim ![x, u] t := by
  funext v
  rcases v with a | b
  · fin_cases a <;> simp [Renorm.yAtom]
  · simp [Renorm.yAtom]

/-- **Value of the c-term graph**: `(Renorm.ctermI Γ)_{xy} = −(Σ_u Γ_{xu}) S_{xy}` on every data
record. -/
theorem Renorm.val_ctermI {n : ℕ} (Γ : Graph 2 n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (x y : ι) :
    (Renorm.ctermI Γ).val D ![x, y] = -((∑ u, Γ.val D ![x, u]) * D.S x y) := by
  unfold Graph.val
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.consEquiv_apply]
  have hc : (Comp.val D (Sum.elim ![x, y] (Fin.cons (α := fun _ => ι) u t)) ∘
      Comp.map (Renorm.yAtom n)) = Comp.val D (Sum.elim ![x, u] t) := by
    funext c
    rw [Function.comp_apply, Renorm_val_map, Renorm_elim_cons]
  unfold Graph.term
  simp only [Renorm.ctermI, List.map_append, List.map_map, hc, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, Coeff.eval, map_neg]
  simp only [Renorm.sEdge, Comp.val, mkC, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

private theorem Renorm_getElem_ctermI {n : ℕ} (Γ : Graph 2 n) (i : ℕ) (hi : i < Γ.comps.length)
    (h' : i < (Renorm.ctermI Γ).comps.length) :
    (Renorm.ctermI Γ).comps[i] = Γ.comps[i].map (Renorm.yAtom n) := by
  simp only [Renorm.ctermI]
  rw [List.getElem_append_left (by simpa using hi)]
  simp

/-- **Value of the diagonal c-term graph**: if the `i`-th component of the diagonal graph `Γ` is
a dotted edge, `(Renorm.ctermII Γ i)_{xy} = −(Σ_u Γ_{xu}) S_{xy}` on every data record. -/
theorem Renorm.val_ctermII {n : ℕ} (Γ : Graph 2 n) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot) (hD : G13.IsDiag Γ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (x y : ι) :
    (Renorm.ctermII Γ i hi).val D ![x, y] = -((∑ u, Γ.val D ![x, u]) * D.S x y) := by
  have hlt : i < (Renorm.ctermI Γ).comps.length := by simp [Renorm.ctermI]; omega
  have hget := Renorm_getElem_ctermI Γ i hi hlt
  unfold Renorm.ctermII
  rw [Contract.val_eq]
  · exact Renorm.val_ctermI Γ D x y
  · change (Renorm.ctermI Γ).comps[i].kind = .dot
    rw [hget]
    exact hk
  · change (Renorm.ctermI Γ).comps[i].x = _ ∧ (Renorm.ctermI Γ).comps[i].y = _ ∨
      (Renorm.ctermI Γ).comps[i].x = _ ∧ (Renorm.ctermI Γ).comps[i].y = _
    rw [hget]
    rcases hD.2 _ (List.getElem_mem hi) hk with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · right
      simp [Comp.map, hx, hy, Renorm.yAtom]
    · left
      simp [Comp.map, hx, hy, Renorm.yAtom]

/-- A graph with a `×`-dotted loop. -/
def Renorm.HasXdotLoop {n : ℕ} (Γ : Graph 2 n) : Prop :=
  ∃ c ∈ Γ.comps, c.kind = .xdot ∧ c.x = c.y

open Classical in
/-- The c-term graphs of one graph `g` of `Σ_l` ([I, (8.3)]): none if `g` has a `×`-dotted loop
(value `0`); `Renorm.ctermII` at its dotted edge if `g` is diagonal with a forest of dotted edges
(`Diag.dot_unique`); `Renorm.ctermI` otherwise. -/
def Renorm.cterm (g : Σ n, Graph 2 n) : Expansion 2 :=
  if Renorm.HasXdotLoop g.2 then []
  else if h : G13.IsDiag g.2 ∧ g.2.DotsAcyclic then
    [⟨g.1, Renorm.ctermII g.2 (Diag.dot_unique g.2 h.1 h.2).choose
      (Diag.dot_unique g.2 h.1 h.2).choose_spec.fst⟩]
  else [⟨g.1 + 1, Renorm.ctermI g.2⟩]

/-- A graph with a `×`-dotted loop has value `0`. -/
private theorem Renorm_val_xdotLoop {n : ℕ} (Γ : Graph 2 n) (h : Renorm.HasXdotLoop Γ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin 2 → ι) : Γ.val D e = 0 := by
  obtain ⟨c, hc, hk, hxy⟩ := h
  unfold Graph.val Graph.term
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [List.prod_eq_zero, mul_zero]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk hxy
  simp [Comp.val]

/-- **Value of the c-term graphs**: the formal sum `Renorm.cterm g` has value
`−(Σ_u g_{xu}) S_{xy}` on every data record. -/
theorem Renorm.val_cterm (g : Σ n, Graph 2 n) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (x y : ι) :
    (Renorm.cterm g).val D ![x, y] = -((∑ u, g.2.val D ![x, u]) * D.S x y) := by
  unfold Renorm.cterm
  split_ifs with hx h
  · simp [Expansion.val, Renorm_val_xdotLoop g.2 hx]
  · simp only [Expansion.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact Renorm.val_ctermII g.2 _ _ (Diag.dot_unique g.2 h.1 h.2).choose_spec.snd.1 h.1 D x y
  · simp only [Expansion.val, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact Renorm.val_ctermI g.2 D x y

/-! ## The renormalized family -/

open Classical in
/-- One graph of `Σ_l` with its dotted edges between an internal and an external atom contracted
(`G13.dotContract`), when it has the shape of an `l`-th order self-energy; otherwise the graph
itself. -/
def Renorm.contr (l : ℕ) (g : Σ n, Graph 2 n) : Σ n, Graph 2 n :=
  if h : SelfEnergyShape l [g] then
    ⟨(G13.dotContract l g.1 g.2 h).choose, (G13.dotContract l g.1 g.2 h).choose_spec.choose⟩
  else g

/-- The contracted graph of a graph with the shape of an `l`-th order self-energy has that
shape, the same value on every data record, and is normal regular with `x`, `y` internal or
diagonal. -/
theorem Renorm.contr_spec (l : ℕ) (g : Σ n, Graph 2 n) (h : SelfEnergyShape l [g]) :
    SelfEnergyShape l [Renorm.contr l g] ∧
      (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin 2 → ι),
        (Renorm.contr l g).2.val D e = g.2.val D e) ∧
      ((∃ C, (Renorm.contr l g).2.internalize.Normal C) ∨ G13.IsDiag (Renorm.contr l g).2) := by
  unfold Renorm.contr
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact (G13.dotContract l g.1 g.2 h).choose_spec.choose_spec

/-- The contracted graph has the value of the graph on every data record. -/
theorem Renorm.val_contr (l : ℕ) (g : Σ n, Graph 2 n) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (e : Fin 2 → ι) : (Renorm.contr l g).2.val D e = g.2.val D e := by
  by_cases h : SelfEnergyShape l [g]
  · exact (Renorm.contr_spec l g h).2.1 ι D e
  · unfold Renorm.contr
    rw [dite_eq_right_of_eq_false (eq_false h)]

/-- **[I, Def 8.2]**: the family `Σ̊` of renormalized self-energies. At order `l` every graph `Γ`
of `Sig l` gives its contraction `Γ'` (`Renorm.contr`) followed by the c-term graphs of
`Γ'` (`Renorm.cterm`), of value `−Σ_u Γ'_{xu} S_{xy}`. On the record of `Σ̊` below `l` its value
is `Σ^{(r)}_l − [Σ_u Σ^{(r)}_l(x, u)] S` ([I, (8.3)], `Renorm.sigMat_eq`). -/
def Renorm.sig (Sig : ℕ → Expansion 2) : ℕ → Expansion 2 :=
  fun l => (Sig l).flatMap fun g => Renorm.contr l g :: Renorm.cterm (Renorm.contr l g)

/-- **The value identity on every data record**: the value of `Renorm.sig Sig l` at `(x, y)` is
`E_{xy} − (Σ_u E_{xu}) S_{xy}` with `E` the value of `Sig l`. -/
theorem Renorm.val_sig (Sig : ℕ → Expansion 2) (l : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (x y : ι) :
    (Renorm.sig Sig l).val D ![x, y] =
      (Sig l).val D ![x, y] - (∑ u, (Sig l).val D ![x, u]) * D.S x y := by
  unfold Renorm.sig
  induction Sig l with
  | nil => simp [Expansion.val]
  | cons g E ih =>
    have hc := Renorm.val_cterm (Renorm.contr l g) D x y
    simp only [Expansion.val] at ih hc ⊢
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      ih, hc, Renorm.val_contr, Finset.sum_add_distrib]
    ring

/-- The self-energy matrices below `N` depend only on the orders below `N` of the family. -/
private theorem Renorm_sigUpTo_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sig Sig' : ℕ → Expansion 2) (S : Matrix ι ι ℝ) (z : ℂ) :
    ∀ N : ℕ, (∀ k < N, Sig' k = Sig k) → sigUpTo Sig' S z N = sigUpTo Sig S z N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    have h1 : sigUpTo Sig' S z N = sigUpTo Sig S z N := ih fun k hk => h k (by omega)
    simp only [sigUpTo, h1, h N (by omega)]

/-- **[I, (8.3)] on the data record**, with the row sum at `x`: for every variance matrix `S`
and every `z`, `Σ̊_l(x, y) = Σ^{(r)}_l(x, y) − [Σ_u Σ^{(r)}_l(x, u)] S_{xy}`, where
`Σ^{(r)}_l = sigMat (Function.update (Renorm.sig Sig) l (Sig l)) S z l` is the value of `Sig l`
on the record whose lower orders are those of `Σ̊` ([I, Def 8.2]). -/
theorem Renorm.sigMat_eq {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2)
    (S : Matrix ι ι ℝ) (z : ℂ) (l : ℕ) (x y : ι) :
    sigMat (Renorm.sig Sig) S z l x y =
      sigMat (Function.update (Renorm.sig Sig) l (Sig l)) S z l x y -
        (∑ u, sigMat (Function.update (Renorm.sig Sig) l (Sig l)) S z l x u) * (S x y : ℂ) := by
  have hU : sigUpTo (Function.update (Renorm.sig Sig) l (Sig l)) S z l =
      sigUpTo (Renorm.sig Sig) S z l :=
    Renorm_sigUpTo_congr _ _ S z l fun k hk => Function.update_of_ne (by omega) _ _
  simp only [sigMat, Matrix.of_apply, Function.update_self, hU]
  rw [Renorm.val_sig]
  simp [detData, cmat]

/-- **[I, (8.3)] with the row sum at `0`**, for the variance family `smatVar P`: for every
`(W, L)` and `Im z > 0`, `Σ̊_l(x, y) = Σ^{(r)}_l(x, y) − [Σ_u Σ^{(r)}_l(0, u)] S_{xy}`, since
`Σ^{(r)}_l` is translation invariant ([I, (1.25)], `selfEnergySymm_smatVar`). -/
theorem Renorm.sigMat_smatVar {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (l W L : ℕ)
    [NeZero L] (z : ℂ) (hz : 0 < z.im) (x y : Zd d L) :
    sigMat (Renorm.sig Sig) (smatVar P W L) z l x y =
      sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l x y -
        (∑ u, sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l 0 u) *
          (smatVar P W L x y : ℂ) := by
  have hs : ∑ u, sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l x u =
      ∑ u, sigMat (Function.update (Renorm.sig Sig) l (Sig l)) (smatVar P W L) z l 0 u := by
    exact (Fintype.sum_equiv (Equiv.addLeft x) _ _
      fun a => ((selfEnergySymm_smatVar d P _ l W L z hz x a).1).symm).symm
  rw [Renorm.sigMat_eq, hs]

/-! ## Graph facts along maps of the atoms -/

/-- The atom map of `Graph.internalize`, through `finSumFinEquiv`. -/
private def Renorm_int {k n : ℕ} (u : Atom k n) : Atom 0 (k + n) := .inr (finSumFinEquiv u)

private theorem Renorm_internalize_comps {k n : ℕ} (Γ : Graph k n) :
    Γ.internalize.comps = Γ.comps.map (Comp.map Renorm_int) := by
  have : (Sum.elim (fun a => Sum.inr (Fin.castAdd n a)) (fun b => Sum.inr (Fin.natAdd k b)) :
      Atom k n → Atom 0 (k + n)) = Renorm_int := by
    funext u
    rcases u with a | b <;> simp [Renorm_int]
  simp only [Graph.internalize, Graph.mapAtoms, this]

private theorem Renorm_reach_fromRel {α : Type*} {r : α → α → Prop} {a b : α} (h : r a b) :
    (SimpleGraph.fromRel r).Reachable a b := by
  by_cases hab : a = b
  · subst hab
    rfl
  · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩).reachable

/-- A path of the graph of a relation `r` maps under `ψ` to a path of the graph of `r'` if `ψ`
maps `r` into `r'`. -/
private theorem Renorm_lift {X Y : Type*} {r : X → X → Prop} {r' : Y → Y → Prop} (ψ : X → Y)
    (h : ∀ a b, r a b → r' (ψ a) (ψ b)) {a b : X} (hr : (SimpleGraph.fromRel r).Reachable a b) :
    (SimpleGraph.fromRel r').Reachable (ψ a) (ψ b) := by
  refine reach_lift ψ (fun x y hxy => ?_) hr
  rw [SimpleGraph.fromRel_adj] at hxy
  rcases hxy.2 with h' | h'
  · exact Renorm_reach_fromRel (h _ _ h')
  · exact (Renorm_reach_fromRel (h _ _ h')).symm

/-- If every atom is an image of `φ` or `w`, the images are pairwise related and `w` is related
to an image, then all atoms are pairwise related. -/
private theorem Renorm_cover {α : Type*} {R : α → α → Prop} (hR : Equivalence R) {N N' : ℕ}
    (φ : Fin N → Fin N') (w : Fin N') (p₀ : Fin N) (f : Fin N' → α)
    (hcov : ∀ q, (∃ p, φ p = q) ∨ q = w) (hφ : ∀ a b, R (f (φ a)) (f (φ b)))
    (hw : R (f w) (f (φ p₀))) (a b : Fin N') : R (f a) (f b) := by
  have key : ∀ a, R (f a) (f (φ p₀)) := by
    intro a
    rcases hcov a with ⟨p, rfl⟩ | rfl
    · exact hφ p p₀
    · exact hw
  exact hR.trans (key a) (hR.symm (key b))

/-- A graph without dotted edge has its dotted edges a forest. -/
private theorem Renorm_dotsAcyclic {k n : ℕ} (Γ : Graph k n)
    (h : ∀ c ∈ Γ.comps, c.kind ≠ .dot) : Γ.DotsAcyclic := by
  rw [Graph.dotsAcyclic_iff_dotExcess_eq_zero]
  have hg : Γ.dotGraph = ⊥ := by
    ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, SimpleGraph.bot_adj, iff_false, not_and]
    rintro - (⟨c, hc, hk, -⟩ | ⟨c, hc, hk, -⟩) <;> exact h c hc hk
  have hn : Γ.nDots = 0 := by
    unfold Graph.nDots
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simpa using h c hc
  have hbij : Function.Bijective
      (fun v => (⊥ : SimpleGraph (Atom k n)).connectedComponentMk v) :=
    ⟨fun u v huv => SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.exact huv),
      fun C => SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) C⟩
  have hcard : Nat.card (⊥ : SimpleGraph (Atom k n)).ConnectedComponent = k + n := by
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  unfold Graph.dotExcess
  rw [hn, hg, hcard]
  simp

/-- Components of a deterministic kind are not solid edges. -/
private theorem Renorm_noSolid {V : Type*} {N : ℕ} (c : Comp V) (h : c.isDetKind N = true) :
    c.kind.isSolid = false := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ <;> first | rfl | simp [Comp.isDetKind] at h

/-- A graph whose internal form (with `x`, `y` internal) is normal regular is normal regular
with the same bound and has no dotted edge. -/
private theorem Renorm_normal_of_int {k n C : ℕ} (Γ : Graph k n) (h : Γ.internalize.Normal C) :
    Γ.Normal C ∧ ∀ c ∈ Γ.comps, c.kind ≠ .dot := by
  have hc := Renorm_internalize_comps Γ
  set ψ : Atom 0 (k + n) → Atom k n := Sum.elim (fun e => e.elim0) finSumFinEquiv.symm with hψ
  have hψi : ∀ u : Atom k n, ψ (Renorm_int u) = u := fun u => by simp [hψ, Renorm_int]
  have hmem : ∀ c ∈ Γ.comps, c.map Renorm_int ∈ Γ.internalize.comps := fun c hc' => by
    rw [hc]
    exact List.mem_map_of_mem hc'
  have hinj : Function.Injective (Renorm_int : Atom k n → Atom 0 (k + n)) := fun u v huv => by
    simpa [Renorm_int] using huv
  have hback : ∀ c' ∈ Γ.internalize.comps, ∃ c ∈ Γ.comps, c' = c.map Renorm_int :=
    fun c' hc' => by
      rw [hc] at hc'
      obtain ⟨c, hc'', rfl⟩ := List.mem_map.1 hc'
      exact ⟨c, hc'', rfl⟩
  have hnd : ∀ c ∈ Γ.comps, c.kind ≠ .dot := fun c hc' hk => by
    have := h.1.noIntDot _ (hmem c hc') hk
    simp [Comp.map, Renorm_int] at this
  have hends : ∀ (c : Comp (Atom k n)) (u v : Atom k n),
      ((c.map Renorm_int).x = Renorm_int u ∧ (c.map Renorm_int).y = Renorm_int v ∨
        (c.map Renorm_int).x = Renorm_int v ∧ (c.map Renorm_int).y = Renorm_int u) ↔
      (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
    intro c u v
    simp only [Comp.map, hinj.eq_iff]
  refine ⟨⟨⟨?_, ?_, ?_, fun c hc' hk => absurd hk (hnd c hc')⟩, ?_, ?_⟩, hnd⟩
  · have := h.1.size
    have hl : Γ.internalize.comps.length = Γ.comps.length := by rw [hc, List.length_map]
    omega
  · intro u v
    have := Renorm_lift ψ (r' := fun u v => ∃ c ∈ Γ.comps, c.x = u ∧ c.y = v)
      (fun a b ⟨c', hc', hx, hy⟩ => by
        obtain ⟨c, hcm, rfl⟩ := hback c' hc'
        exact ⟨c, hcm, by rw [← hx]; exact (hψi _).symm, by rw [← hy]; exact (hψi _).symm⟩)
      (h.1.connected (Renorm_int u) (Renorm_int v))
    rwa [hψi, hψi] at this
  · intro a b
    have := Renorm_lift ψ (r' := fun u v => ∃ c ∈ Γ.comps,
        (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v)
      (fun a b ⟨c', hc', hk, hx, hy⟩ => by
        obtain ⟨c, hcm, rfl⟩ := hback c' hc'
        exact ⟨c, hcm, hk, by rw [← hx]; exact (hψi _).symm, by rw [← hy]; exact (hψi _).symm⟩)
      (h.1.internal (finSumFinEquiv (.inr a)) (finSumFinEquiv (.inr b)))
    have e : ∀ u, ψ (Sum.inr (finSumFinEquiv u)) = u := hψi
    rwa [e, e] at this
  · intro c hc' hs hxy
    exact h.2.1 _ (hmem c hc') hs (congrArg Renorm_int hxy)
  · intro u v huv
    have key := h.2.2 (Renorm_int u) (Renorm_int v) fun e => huv (hinj e)
    constructor
    · rintro ⟨c, hc', hk, he⟩
      obtain ⟨c', hc'', hs, he'⟩ := key.1 ⟨c.map Renorm_int, hmem c hc', hk, (hends c u v).2 he⟩
      obtain ⟨e, he1, rfl⟩ := hback c' hc''
      exact ⟨e, he1, hs, (hends e u v).1 he'⟩
    · rintro ⟨c, hc', hk, he⟩
      obtain ⟨c', hc'', hs, he'⟩ := key.2 ⟨c.map Renorm_int, hmem c hc', hk, (hends c u v).2 he⟩
      obtain ⟨e, he1, rfl⟩ := hback c' hc''
      exact ⟨e, he1, hs, (hends e u v).1 he'⟩

/-- A graph without external atoms whose components are neither dotted, `×`-dotted nor solid,
and in which any two atoms are joined by waved and diffusive edges, is normal regular. -/
private theorem Renorm_normal_int {N : ℕ} (H : Graph 0 N)
    (hk : ∀ c ∈ H.comps, c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false)
    (hw : ∀ a b : Fin N, H.wavedThetaGraph.Reachable (.inr a) (.inr b)) :
    H.Normal (N + H.comps.length) := by
  have hle : H.wavedThetaGraph ≤ H.edgeGraph := by
    intro u v huv
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
    obtain ⟨hne, ⟨c, hc, -, hx, hy⟩ | ⟨c, hc, -, hx, hy⟩⟩ := huv
    · exact ⟨hne, Or.inl ⟨c, hc, hx, hy⟩⟩
    · exact ⟨hne, Or.inr ⟨c, hc, hx, hy⟩⟩
  refine ⟨⟨by simp, ?_, hw, fun c hc hd => absurd hd (hk c hc).1⟩, fun c hc hs => ?_,
    fun u v _ => ?_⟩
  · rintro (u | a) (v | b)
    · exact u.elim0
    · exact u.elim0
    · exact v.elim0
    · exact (hw a b).mono hle
  · rw [(hk c hc).2.2] at hs
    exact absurd hs (by decide)
  · constructor
    · rintro ⟨c, hc, hx, -⟩
      exact absurd hx (hk c hc).2.1
    · rintro ⟨c, hc, hs, -⟩
      rw [(hk c hc).2.2] at hs
      exact absurd hs (by decide)

/-! ## A graph with one more atom joined by a waved edge -/

section Embed

variable {N N' : ℕ} {H : Graph 0 N} {H' : Graph 0 N'} {φ : Fin N → Fin N'} {w : Fin N'}
  {p₀ : Fin N} {c₀ : Comp (Atom 0 N')}

/-- **Doubly connected.** If `H'` is `H` with its atoms mapped by `φ` and one waved edge `c₀`
added from the image of `p₀` to an atom `w`, and every atom of `H'` is an image or `w`, then
`H'` is doubly connected when `H` is: the nets of `H` are mapped, and `w` joins the molecule of
the image of `p₀`. -/
private theorem Renorm_embed_dc (hH' : H'.comps = H.comps.map (Comp.map (Sum.map id φ)) ++ [c₀])
    (hk₀ : c₀.kind = .waved .s) (hx₀ : c₀.x = .inr (φ p₀)) (hy₀ : c₀.y = .inr w)
    (hcov : ∀ q, (∃ p, φ p = q) ∨ q = w) (hDC : H.DoublyConnected) : H'.DoublyConnected := by
  obtain ⟨Lb, Lu, hsub, hb, hu, hsb, hsu⟩ := Graph.dcl_of_dc hDC
  have hmem : ∀ c ∈ H.comps, c.map (Sum.map id φ) ∈ H'.comps := fun c hc => by
    rw [hH']
    exact List.mem_append_left _ (List.mem_map_of_mem hc)
  have hmem₀ : c₀ ∈ H'.comps := by
    rw [hH']
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hsame : ∀ a b, H.SameMol (.inr a) (.inr b) → H'.SameMol (.inr (φ a)) (.inr (φ b)) := by
    rintro a b (he | ⟨-, -, hr⟩)
    · left
      rw [Sum.inr_injective he]
    · right
      refine ⟨rfl, rfl, ?_⟩
      exact Renorm_lift (Sum.map id φ)
        (r' := fun u v => ∃ c ∈ H'.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v)
        (fun u v ⟨c, hc, hj, hx, hy⟩ => ⟨c.map (Sum.map id φ), hmem c hc, hj,
          by rw [← hx]; rfl, by rw [← hy]; rfl⟩) hr
  have hw0 : H'.SameMol (.inr w) (.inr (φ p₀)) :=
    Or.inr ⟨rfl, rfl, (Renorm_reach_fromRel (r := fun u v => ∃ c ∈ H'.comps,
      c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ⟨c₀, hmem₀, by rw [hk₀]; rfl, hx₀, hy₀⟩).symm⟩
  have hlift : ∀ L : List (Comp (Atom 0 N)), (SimpleGraph.fromRel (nrel H L)).Preconnected →
      (SimpleGraph.fromRel (nrel H' (L.map (Comp.map (Sum.map id φ))))).Preconnected := by
    intro L hL
    refine Renorm_cover (SimpleGraph.reachable_is_equivalence _) φ w p₀ id hcov
      (fun a b => ?_) (Renorm_reach_fromRel (Or.inl hw0))
    refine Renorm_lift φ (fun a b hr => ?_) (hL a b)
    rcases hr with hm | ⟨c, hc, hx, hy⟩
    · exact Or.inl (hsame a b hm)
    · exact Or.inr ⟨c.map (Sum.map id φ), List.mem_map_of_mem hc, by simp [Comp.map, hx],
        by simp [Comp.map, hy]⟩
  refine Graph.dc_of_dcl ⟨Lb.map (Comp.map (Sum.map id φ)), Lu.map (Comp.map (Sum.map id φ)),
    ?_, ?_, ?_, hlift Lb hsb, hlift Lu hsu⟩
  · rw [← List.map_append]
    obtain ⟨l, hp, hs⟩ := hsub
    refine ⟨l.map (Comp.map (Sum.map id φ)), hp.map _, ?_⟩
    rw [hH']
    exact (hs.map _).trans (List.sublist_append_left _ _)
  · intro c hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    exact hb c hc'
  · intro c hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    exact hu c hc'

/-- **Waved and `Θ` paths.** Under the hypotheses of `Renorm_embed_dc`, if any two atoms of `H`
are joined by waved and diffusive edges, so are any two atoms of `H'`. -/
private theorem Renorm_embed_waved
    (hH' : H'.comps = H.comps.map (Comp.map (Sum.map id φ)) ++ [c₀])
    (hk₀ : c₀.kind = .waved .s) (hx₀ : c₀.x = .inr (φ p₀)) (hy₀ : c₀.y = .inr w)
    (hcov : ∀ q, (∃ p, φ p = q) ∨ q = w)
    (hw : ∀ a b : Fin N, H.wavedThetaGraph.Reachable (.inr a) (.inr b)) (a b : Fin N') :
    H'.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
  have hmem : ∀ c ∈ H.comps, c.map (Sum.map id φ) ∈ H'.comps := fun c hc => by
    rw [hH']
    exact List.mem_append_left _ (List.mem_map_of_mem hc)
  have hmem₀ : c₀ ∈ H'.comps := by
    rw [hH']
    exact List.mem_append_right _ (List.mem_singleton_self _)
  refine Renorm_cover (SimpleGraph.reachable_is_equivalence _) φ w p₀
    (fun a => (.inr a : Atom 0 N')) hcov (fun a b => ?_) ?_ a b
  · exact Renorm_lift (Sum.map id φ) (r' := fun u v => ∃ c ∈ H'.comps,
        (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v)
      (fun u v ⟨c, hc, hk, hx, hy⟩ => ⟨c.map (Sum.map id φ), hmem c hc, hk,
        by rw [← hx]; rfl, by rw [← hy]; rfl⟩) (hw a b)
  · exact (Renorm_reach_fromRel (r := fun u v => ∃ c ∈ H'.comps,
        (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v)
      ⟨c₀, hmem₀, Or.inl ⟨by rw [hk₀]; rfl, by rw [hk₀]; decide⟩, hx₀, hy₀⟩).symm

end Embed

/-! ## The shape of the c-term graphs -/

/-- The internal form of a graph whose components are those of `Γ` mapped by `f` followed by one
component `e`. -/
private theorem Renorm_int_comps {n : ℕ} (Γ : Graph 2 n) (f : Atom 2 n → Atom 2 (n + 1))
    (e : Comp (Atom 2 (n + 1))) (cf : Coeff) :
    (⟨Γ.comps.map (Comp.map f) ++ [e], cf⟩ : Graph 2 (n + 1)).internalize.comps =
      Γ.internalize.comps.map (Comp.map (Sum.map id
        (fun p => finSumFinEquiv (f (finSumFinEquiv.symm p))))) ++ [e.map Renorm_int] := by
  rw [Renorm_internalize_comps, Renorm_internalize_comps]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, Comp.map_comp'']
  congr 1
  funext u
  simp [Renorm_int]

private theorem Renorm_ctermI_det {n : ℕ} (Γ : Graph 2 n) (N : ℕ)
    (h : Γ.comps.all (Comp.isDetKind N) = true) :
    (Renorm.ctermI Γ).comps.all (Comp.isDetKind N) = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  simp only [Renorm.ctermI, List.mem_append, List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨e, he, rfl⟩ | rfl
  · rw [Contract.isDetKind_map]
    exact h e he
  · rfl

private theorem Renorm_ctermI_ord {n : ℕ} (Γ : Graph 2 n) : (Renorm.ctermI Γ).ord = Γ.ord := by
  unfold Graph.ord
  simp only [Renorm.ctermI, List.map_append, List.map_map, Function.comp_def, Comp.map,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Renorm.sEdge, mkC,
    Kind.ord]
  push_cast
  ring

/-- **Shape of the c-term graph.** If `Γ` has the shape of an `l`-th order self-energy, is normal
regular with `x`, `y` internal and has no `×`-dotted edge, then `Renorm.ctermI Γ` has the shape of
an `l`-th order self-energy: the internal form of `Γ` is mapped, and the new atom `y` joins the
molecule of `x` by `s_{xy}`. -/
theorem Renorm.shape_ctermI {l n : ℕ} (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩])
    (hN : ∃ C, Γ.internalize.Normal C) (hx : ∀ c ∈ Γ.comps, c.kind ≠ .xdot) :
    SelfEnergyShape l [⟨n + 1, Renorm.ctermI Γ⟩] := by
  obtain ⟨-, hdet, hord, hDC⟩ := hΓ ⟨n, Γ⟩ List.mem_cons_self
  obtain ⟨C, hN⟩ := hN
  have hnd := (Renorm_normal_of_int Γ hN).2
  have hH' := Renorm_int_comps Γ (Renorm.yAtom n) Renorm.sEdge (-Γ.coeff)
  have hcov : ∀ q : Fin (2 + (n + 1)),
      (∃ p, finSumFinEquiv (Renorm.yAtom n (finSumFinEquiv.symm p)) = q) ∨
        q = finSumFinEquiv (.inl 1) := by
    intro q
    obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective q
    rcases u with a | b
    · fin_cases a
      · exact Or.inl ⟨finSumFinEquiv (.inl 0), by simp [Renorm.yAtom]⟩
      · exact Or.inr rfl
    · refine Fin.cases ?_ (fun b => ?_) b
      · exact Or.inl ⟨finSumFinEquiv (.inl 1), by simp [Renorm.yAtom]⟩
      · exact Or.inl ⟨finSumFinEquiv (.inr b), by simp [Renorm.yAtom]⟩
  have hx₀ : (Renorm.sEdge.map Renorm_int : Comp (Atom 0 (2 + (n + 1)))).x =
      .inr (finSumFinEquiv (Renorm.yAtom n (finSumFinEquiv.symm (finSumFinEquiv (.inl 0))))) := by
    simp [Renorm.sEdge, mkC, Comp.map, Renorm_int, Renorm.yAtom]
  have hDC' : (Renorm.ctermI Γ).internalize.DoublyConnected :=
    Renorm_embed_dc (H := Γ.internalize) hH' rfl hx₀ rfl hcov hDC
  have hw' := Renorm_embed_waved (H := Γ.internalize) hH' rfl hx₀ rfl hcov hN.1.internal
  have hkinds : ∀ c ∈ (Renorm.ctermI Γ).internalize.comps,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := by
    intro c hc
    rw [Renorm_internalize_comps] at hc
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hc
    simp only [Renorm.ctermI, List.mem_append, List.mem_map, List.mem_singleton] at hc'
    rcases hc' with ⟨e, he, rfl⟩ | rfl
    · exact ⟨hnd e he, hx e he, Renorm_noSolid e (List.all_eq_true.1 hdet e he)⟩
    · exact ⟨by simp [Renorm.sEdge, mkC, Comp.map], by simp [Renorm.sEdge, mkC, Comp.map], rfl⟩
  obtain ⟨hNe, hnd'⟩ := Renorm_normal_of_int _ (Renorm_normal_int _ hkinds hw')
  intro g hg
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨⟨_, hNe, Renorm_dotsAcyclic _ hnd'⟩, Renorm_ctermI_det Γ _ hdet,
    (Renorm_ctermI_ord Γ).trans hord, hDC'⟩

/-- `x`, `y` kept and the internal atoms shifted by one. -/
private def Renorm_shift (n : ℕ) : Atom 2 n → Atom 2 (n + 1) :=
  Sum.elim Sum.inl (fun b => .inr b.succ)

/-- `Γ` with a new internal atom `0` joined to `x` by a waved edge and the coefficient negated:
the graph whose identification `x = y` (`Diag.graph`) is the diagonal c-term graph. -/
private def Renorm_pad {n : ℕ} (Γ : Graph 2 n) : Graph 2 (n + 1) :=
  ⟨Γ.comps.map (Comp.map (Renorm_shift n)) ++ [mkC (.waved .s) (.inl 0) (.inr 0)], -Γ.coeff⟩

private theorem Renorm_ctermII_eq {n : ℕ} (Γ : Graph 2 n) (i : ℕ) (hi : i < Γ.comps.length) :
    Renorm.ctermII Γ i hi = Diag.graph (Renorm_pad Γ) i := by
  have hc : ∀ b : Fin n, Contract.atomMap (0 : Fin (n + 1)) (0 : Fin 2) (.inr b.succ) = .inr b :=
    fun b => by simpa using Contract.atomMap_succAbove (0 : Fin (n + 1)) (0 : Fin 2) b
  unfold Renorm.ctermII Contract.graph Diag.graph
  simp only [Renorm.ctermI, Renorm_pad, Graph.mk.injEq, and_true]
  rw [List.eraseIdx_append_of_lt_length (by simpa using hi),
    List.eraseIdx_append_of_lt_length (by simpa using hi), List.eraseIdx_map, List.eraseIdx_map]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, Comp.map_comp'']
    congr 1
    funext u
    rcases u with a | b
    · fin_cases a <;> simp [Renorm.yAtom, Renorm_shift, Diag.atomMap]
    · simp [Renorm.yAtom, Renorm_shift, Diag.atomMap, hc]

/-- **Shape of the diagonal c-term graph.** If `Γ` has the shape of an `l`-th order
self-energy, is diagonal with its only dotted edge at index `i`, and has no `×`-dotted edge,
then `Renorm.ctermII Γ i` has the shape of an `l`-th order self-energy (`Diag.internal`). -/
theorem Renorm.shape_ctermII {l n : ℕ} (Γ : Graph 2 n) (i : ℕ) (hi : i < Γ.comps.length)
    (hΓ : SelfEnergyShape l [⟨n, Γ⟩]) (hD : G13.IsDiag Γ) (hk : Γ.comps[i].kind = .dot)
    (hrest : ∀ c ∈ Γ.comps.eraseIdx i, c.kind ≠ .dot) (hx : ∀ c ∈ Γ.comps, c.kind ≠ .xdot) :
    SelfEnergyShape l [⟨n, Renorm.ctermII Γ i hi⟩] := by
  obtain ⟨-, hdet, hord, hDC⟩ := hΓ ⟨n, Γ⟩ List.mem_cons_self
  have hi3 : i < (Renorm_pad Γ).comps.length := by simp [Renorm_pad]; omega
  have hget3 : (Renorm_pad Γ).comps[i] = Γ.comps[i].map (Renorm_shift n) := by
    simp only [Renorm_pad]
    rw [List.getElem_append_left (by simpa using hi)]
    simp
  have hk3 : (Renorm_pad Γ).comps[i].kind = .dot := by rw [hget3]; exact hk
  have hD3 : G13.IsDiag (Renorm_pad Γ) := by
    refine ⟨⟨_, List.getElem_mem hi3, hk3⟩, fun c hc hck => ?_⟩
    simp only [Renorm_pad, List.mem_append, List.mem_map, List.mem_singleton] at hc
    rcases hc with ⟨e, he, rfl⟩ | rfl
    · rcases hD.2 e he hck with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        simp [Comp.map, h1, h2, Renorm_shift]
      · right
        simp [Comp.map, h1, h2, Renorm_shift]
    · simp [mkC] at hck
  have hrest3 : ∀ c ∈ (Renorm_pad Γ).comps.eraseIdx i,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := by
    intro c hc
    simp only [Renorm_pad] at hc
    rw [List.eraseIdx_append_of_lt_length (by simpa using hi), List.eraseIdx_map] at hc
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hc
    rcases hc with ⟨e, he, rfl⟩ | rfl
    · have he' := List.mem_of_mem_eraseIdx he
      exact ⟨hrest e he, hx e he', Renorm_noSolid e (List.all_eq_true.1 hdet e he')⟩
    · exact ⟨by simp [mkC], by simp [mkC], rfl⟩
  have hcov : ∀ q : Fin (2 + (n + 1)),
      (∃ p, finSumFinEquiv (Renorm_shift n (finSumFinEquiv.symm p)) = q) ∨
        q = finSumFinEquiv (.inr 0) := by
    intro q
    obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective q
    rcases u with a | b
    · exact Or.inl ⟨finSumFinEquiv (.inl a), by simp [Renorm_shift]⟩
    · refine Fin.cases ?_ (fun b => ?_) b
      · exact Or.inr rfl
      · exact Or.inl ⟨finSumFinEquiv (.inr b), by simp [Renorm_shift]⟩
  have hH' := Renorm_int_comps Γ (Renorm_shift n) (mkC (.waved .s) (.inl 0) (.inr 0)) (-Γ.coeff)
  have hx₀ : ((mkC (.waved .s) (.inl 0) (.inr 0) : Comp (Atom 2 (n + 1))).map Renorm_int).x =
      .inr (finSumFinEquiv (Renorm_shift n (finSumFinEquiv.symm (finSumFinEquiv (.inl 0))))) := by
    simp [mkC, Comp.map, Renorm_int, Renorm_shift]
  have hDC3 : (Renorm_pad Γ).internalize.DoublyConnected :=
    Renorm_embed_dc (H := Γ.internalize) hH' rfl hx₀ rfl hcov hDC
  obtain ⟨hNI, hDCII⟩ := Diag.internal (Renorm_pad Γ) i hi3 hk3 hD3 hrest3 hDC3
  rw [← Renorm_ctermII_eq Γ i hi] at hNI hDCII
  obtain ⟨hNe, hnd'⟩ := Renorm_normal_of_int _ hNI
  have hlt : i < (Renorm.ctermI Γ).comps.length := by simp [Renorm.ctermI]; omega
  have hkI : (Renorm.ctermI Γ).comps[(⟨i, hlt⟩ : Fin _)].kind = .dot := by
    change (Renorm.ctermI Γ).comps[i].kind = .dot
    rw [Renorm_getElem_ctermI Γ i hi hlt]
    exact hk
  intro g hg
  rw [List.mem_singleton] at hg
  subst hg
  exact ⟨⟨_, hNe, Renorm_dotsAcyclic _ hnd'⟩,
    Contract.all_isDetKind (Renorm.ctermI Γ) ⟨i, hlt⟩ 0 0 _ (Renorm_ctermI_det Γ _ hdet),
    ((Contract.ord_eq (Renorm.ctermI Γ) ⟨i, hlt⟩ 0 0 hkI).trans (Renorm_ctermI_ord Γ)).trans hord,
    hDCII⟩

/-- A normal regular graph of deterministic kinds without `×`-dotted loop has no `×`-dotted
edge: a `×`-dotted edge between distinct atoms needs a solid edge. -/
private theorem Renorm_noXdot {n C N : ℕ} (Γ : Graph 2 n) (hN : Γ.Normal C)
    (hdet : Γ.comps.all (Comp.isDetKind N) = true) (hxl : ¬ Renorm.HasXdotLoop Γ) :
    ∀ c ∈ Γ.comps, c.kind ≠ .xdot := by
  intro c hc hk
  by_cases hxy : c.x = c.y
  · exact hxl ⟨c, hc, hk, hxy⟩
  · obtain ⟨e, he, hs, -⟩ := (hN.2.2 c.x c.y hxy).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    rw [Renorm_noSolid e (List.all_eq_true.1 hdet e he)] at hs
    exact absurd hs (by decide)

/-- The c-term graphs of a graph with the shape of an `l`-th order self-energy that is normal
regular with `x`, `y` internal or diagonal have the shape of an `l`-th order self-energy. -/
theorem Renorm.shape_cterm (l : ℕ) (g : Σ n, Graph 2 n) (hs : SelfEnergyShape l [g])
    (hdis : (∃ C, g.2.internalize.Normal C) ∨ G13.IsDiag g.2) :
    SelfEnergyShape l (Renorm.cterm g) := by
  obtain ⟨⟨C, hN, hA⟩, hdet, -, -⟩ := hs g List.mem_cons_self
  unfold Renorm.cterm
  split_ifs with hxl h
  · intro g' hg'
    simp at hg'
  · exact Renorm.shape_ctermII g.2 _ _ hs h.1 (Diag.dot_unique g.2 h.1 h.2).choose_spec.snd.1
      (Diag.dot_unique g.2 h.1 h.2).choose_spec.snd.2 (Renorm_noXdot g.2 hN hdet hxl)
  · exact Renorm.shape_ctermI g.2 hs (hdis.resolve_right fun hD => h ⟨hD, hA⟩)
      (Renorm_noXdot g.2 hN hdet hxl)

/-- **The shape of `Σ̊_l`**: if `Σ_l` has the shape of an `l`-th order self-energy, so has
`Σ̊_l` (`Renorm.sig Sig l`). -/
theorem Renorm.shape_sig (Sig : ℕ → Expansion 2) (l : ℕ) (h : SelfEnergyShape l (Sig l)) :
    SelfEnergyShape l (Renorm.sig Sig l) := by
  intro g' hg'
  obtain ⟨g, hg, hg''⟩ := List.mem_flatMap.1 hg'
  have hs : SelfEnergyShape l [g] := fun g₁ hg₁ => by
    rw [List.mem_singleton] at hg₁
    rw [hg₁]
    exact h g hg
  obtain ⟨hs', -, hdis⟩ := Renorm.contr_spec l g hs
  rcases List.mem_cons.1 hg'' with rfl | hc
  · exact hs' _ (List.mem_singleton_self _)
  · exact Renorm.shape_cterm l _ hs' hdis g' hc

/-! ## `Σ̊` is a family of self-energies -/

/-- For `L ≥ L₀` in `adm(c₀, c₁)`, `W ≥ W₀`. -/
private theorem Renorm_W_of_L {c₀ c₁ : ℝ} (hc₁ : 0 < c₁) (W₀ : ℝ) :
    ∃ L₀ : ℕ, ∀ W L : ℕ, L₀ ≤ L → (W, L) ∈ adm c₀ c₁ → W₀ ≤ W := by
  refine ⟨⌈(max W₀ 0) ^ (1 / c₁)⌉₊, fun W L hL hadm => ?_⟩
  have h1 : (max W₀ 0) ^ (1 / c₁) ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have h2 : ((max W₀ 0) ^ (1 / c₁)) ^ c₁ ≤ (L : ℝ) ^ c₁ :=
    Real.rpow_le_rpow (by positivity) h1 hc₁.le
  rw [← Real.rpow_mul (le_max_right _ _), one_div_mul_cancel hc₁.ne', Real.rpow_one] at h2
  exact (le_max_left _ _).trans (h2.trans hadm.1)

/-- **`Σ̊` is a family of self-energies** ([I, Def 8.2] with [II, Def 2.7]): for `d ≥ 8`, if the
even orders `4 ≤ k ≤ N` of `Sig` are self-energies for `smatVar P`, so are those of
`Renorm.sig Sig`. The shape is `Renorm.shape_sig`, [I, (1.25)] is `selfEnergySymm_smatVar`,
[I, (1.26)] is `G13.entrywise` for `Renorm.sig Sig` by induction on the order, and the row sum
of `Σ̊_k` is `0` wherever `S` has row sums `1` (`Smat_isVarKernel_adm`). -/
theorem Renorm.selfEnergiesUpTo (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (N : ℕ)
    (Sig : ℕ → Expansion 2) (h : SelfEnergiesUpTo d (smatVar P) Sig N) :
    SelfEnergiesUpTo d (smatVar P) (Renorm.sig Sig) N := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk4 hkN hke
  have hsh : SelfEnergyShape k (Renorm.sig Sig k) := Renorm.shape_sig Sig k (h k hk4 hkN hke).1
  have hlow : SelfEnergiesUpTo d (smatVar P) (Renorm.sig Sig) (k - 1) :=
    fun j hj4 hjk hje => ih j (by omega) hj4 (by omega) hje
  refine ⟨hsh, selfEnergySymm_smatVar d P _ k, ?_⟩
  intro κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  obtain ⟨L₁, hL₁⟩ :=
    G13.entrywise d hd P k (Renorm.sig Sig) hk4 hlow hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  obtain ⟨W₁, hW₁⟩ := Smat_isVarKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨W₂, hW₂⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨L₂, hL₂⟩ := Renorm_W_of_L (c₀ := c₀) hc₁ (max W₁ W₂)
  refine ⟨max L₁ L₂, fun W L _ hL hadm z hz =>
    ⟨fun x => hL₁ W L (le_of_max_le_left hL) hadm z hz x, ?_⟩⟩
  have hW := hL₂ W L (le_of_max_le_right hL) hadm
  have hrow : ∑ x, (smatVar P W L 0 x : ℂ) = 1 := by
    rw [hW₂ W L hadm (le_trans (le_max_right _ _) hW)]
    have := (hW₁ W L hadm (le_trans (le_max_left _ _) hW)).rowSum 0
    exact_mod_cast this
  have hzero : ∑ x, sigMat (Renorm.sig Sig) (smatVar P W L) z k 0 x = 0 := by
    simp_rw [Renorm.sigMat_eq Sig (smatVar P W L) z k 0]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, mul_one, sub_self]
  rw [hzero, norm_zero]
  have him : 0 ≤ z.im := le_trans (by positivity) hz.2.1
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) him)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `Renorm.selfEnergiesUpTo` for the kernel family of `Σ̊`: at every even order `4 ≤ l ≤ N`,
[I, (1.25)–(1.27)] hold for `sigKer (smatVar P) (Renorm.sig Sig)` (`KerSymm`, `KerBound`). -/
theorem Renorm.kerSymm_kerBound (d : ℕ) (hd : 8 ≤ d) (P : Profile d) (N : ℕ)
    (Sig : ℕ → Expansion 2) (h : SelfEnergiesUpTo d (smatVar P) Sig N) (l : ℕ) (hl4 : 4 ≤ l)
    (hlN : l ≤ N) (hle : Even l) :
    KerSymm (sigKer (smatVar P) (Renorm.sig Sig)) l ∧
      KerBound (sigKer (smatVar P) (Renorm.sig Sig)) l :=
  let hse := Renorm.selfEnergiesUpTo d hd P N Sig h l hl4 hlN hle
  ⟨hse.2.1, hse.2.2⟩

section Instances

end Instances

end RBM8D.Graphs
