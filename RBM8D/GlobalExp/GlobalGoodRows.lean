import RBM8D.GlobalExp.SubstSPD
import RBM8D.GlobalExp.RunClauses
import RBM8D.Graph.MolAddEdge
import Batteries.Tactic.OpenPrivate

/-!
# [II, Lemma 6.5 (3), (4)]: the graphs of `A` and the substituted `Q`-graphs in the block reading

Rows (3), (3′) and the first sentence of row (4) of [II, Lemma 6.5] in the block reading, for the
substitution of a graph `g` for the `t`-variable `t_{y₁y₂,x}` of `G = H.glue x y₁ y₂ (tVar true)`
([II, §4.3], picture (6.5)), with the hypotheses on `𝒯` of [II, Def 3.2] at order `n - 1` and of
[II, Def 6.3] (`TRec.Shape`, `TRec.Def63`) and the hypotheses of [II, Lemma 6.5] on `G`:

* `globalGood_row3`: every `O_dot` form of the substitution of a graph of `A` is normal regular
  without dotted edges and labels, and is sequentially pre-deterministic of scaling order
  `≥ n + 1`, or (3′) `y₁ = y₂`, `⊕`, `⊖` lie in one dotted block of `g` and the form is globally
  standard of scaling order `≥ ord G + 1`;
* `globalGood_row4_invB`: the substitution of every graph of `Q` has the invariant
  `Graph.InvB'`.

A graph with an internal atom satisfies the clause on the external atoms and the charge pattern of
the block normal form (`TRec.Def63`), and `substSPDB`, `substGSB` apply. A graph without internal
atoms has its diffusive edge at `⊗` ending at `⊕` (`Graph.RootAtPlus`): in the molecular graph of
the substituted graph this edge, `Θ_{xy₁}`, takes the place of `G_{y₁α}`, the red solid edge
`Ḡ_{y₂α}` is removed, and every other edge of `g` joins two of the molecules of `x`, `y₁`, `y₂`
(`MGraph.spd_addEdge`); at `y₁ = y₂` these other edges are loops.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private SubstSPD_host SubstSPD_bI SubstSPD_rI SubstSPD_Kp SubstSPD_Kp_cls SubstSPD_Kp_ends
  SubstSPD_Kp_spd SubstSPD_Kp_gs SubstSPD_Kp_crosses SubstSPD_oDotT_bal SubstSPD_glue_bal
  SubstSPD_glue_dots SubstSPD_insert_noGhost SubstSPD_swap_kind SubstSPD_swap_of_ns
  SubstSPD_swap_filter SubstSPD_swap_dotExcess SubstSPD_swap_labels SubstSPD_swap_noLabDot
  SubstSPD_swap_otimesNoDot SubstSPD_swap_labelFree SubstSPD_swap_pmBlock SubstSPD_swap_noGhost
  SubstSPD_noGhost_of_tKinds SubstSPD_oDotT_labelFree SubstSPD_diagRecoll_of SubstSPD_tVar_ord
  SubstSPD_eq_of_le_one SubstSPD_ends_inl SubstSPD_cls_inl SubstSPD_cls_dot SubstSPD_pin_unpinned
  SubstSPD_flat_unpinned SubstSPD_mclass_diff SubstSPD_mgext SubstSPD_unpinned_zero
  from RBM8D.GlobalExp.SubstSPD
open private SubstDC_swap_rgCheck from RBM8D.GlobalExp.SubstDC

/-! ## Molecular multigraphs: absent edges made present between internal vertices -/

section Drop

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The edges of `A` set absent. -/
private def GlobalGoodRows_drop (G : MGraph V E) (A : Finset E) : MGraph V E :=
  { G with cls := fun e => if e ∈ A then none else G.cls e }

/-- A graph without ghost edges is sequentially pre-deterministic when it is so with the edges of
`A` set absent, every edge of `A` being absent or a blue solid, diffusive or red solid edge
between internal vertices. -/
private theorem GlobalGoodRows_spd_of_drop (G : MGraph V E) (hng : ∀ e, G.cls e ≠ some .ghost) :
    ∀ A : Finset E, (∀ e ∈ A, G.cls e = none ∨ ((G.cls e = some .plus ∨ G.cls e = some .diff ∨
      G.cls e = some .minus) ∧ (G.ends e).1 ∈ G.int ∧ (G.ends e).2 ∈ G.int)) →
      (GlobalGoodRows_drop G A).SPD → G.SPD := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _ h
    have : GlobalGoodRows_drop G ∅ = G :=
      SubstSPD_mgext rfl rfl (fun _ => rfl) (fun e => by simp [GlobalGoodRows_drop])
    rwa [this] at h
  | insert a A ha ih =>
    intro hA h
    refine ih (fun e he => hA e (Finset.mem_insert_of_mem he)) ?_
    rcases hA a (Finset.mem_insert_self a A) with h0 | ⟨hc, h1, h2⟩
    · have : GlobalGoodRows_drop G A = GlobalGoodRows_drop G (insert a A) :=
        SubstSPD_mgext rfl rfl (fun _ => rfl) (fun e => by
          by_cases he : e = a
          · subst he; simp [GlobalGoodRows_drop, h0]
          · simp [GlobalGoodRows_drop, he])
      rw [this]; exact h
    · obtain ⟨c, hc', hcc⟩ : ∃ c, G.cls a = some c ∧ (c = .plus ∨ c = .diff ∨ c = .minus) := by
        rcases hc with h | h | h <;> exact ⟨_, h, by simp⟩
      have : GlobalGoodRows_drop G A =
          (GlobalGoodRows_drop G (insert a A)).setEdge a (G.ends a).1 (G.ends a).2 (some c) :=
        SubstSPD_mgext rfl rfl (fun e => by
          by_cases he : e = a
          · subst he; simp [MGraph.setEdge, GlobalGoodRows_drop]
          · simp [MGraph.setEdge, GlobalGoodRows_drop, he]) (fun e => by
          by_cases he : e = a
          · subst he; simp [MGraph.setEdge, GlobalGoodRows_drop, ha, hc']
          · simp [MGraph.setEdge, GlobalGoodRows_drop, he])
      rw [this]
      refine MGraph.spd_addEdge _ _ _ a _ _ c (fun e => ?_) h (by simp [GlobalGoodRows_drop]) h1 h2
        hcc
      simp only [GlobalGoodRows_drop]
      split_ifs
      · simp
      · exact hng e

end Drop

/-! ## The molecular graph of `G` with `G_{y₁α}` turned diffusive and `Ḡ_{y₂α}` removed -/

section Host2

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The edge `b` set to join `u₀` to `u₁` as a diffusive edge, and the edge `r` set absent (its
ends `u₂`, `u₀`). -/
private def GlobalGoodRows_K2 (K : MGraph V E) (b r : E) (u₀ u₁ u₂ : V) : MGraph V E :=
  (SubstSPD_Kp K b r u₀ u₁ .diff u₂ u₀).recolor r none

omit [DecidableEq V] in
private theorem GlobalGoodRows_recolor_eq (G : MGraph V E) (e : E) (c : Option MClass) :
    G.recolor e c = G.setEdge e (G.ends e).1 (G.ends e).2 c :=
  SubstSPD_mgext rfl rfl (fun f => by
    by_cases h : f = e
    · subst h; simp [MGraph.setEdge, MGraph.recolor]
    · simp [MGraph.setEdge, MGraph.recolor, h]) (fun _ => rfl)

omit [DecidableEq V] in
private theorem GlobalGoodRows_K2_cls {K : MGraph V E} {b r : E} {u₀ u₁ u₂ : V} (e : E) :
    (GlobalGoodRows_K2 K b r u₀ u₁ u₂).cls e =
      if e = r then none else if e = b then some .diff else K.cls e := by
  unfold GlobalGoodRows_K2
  by_cases h : e = r
  · subst h; simp [MGraph.recolor]
  · simp only [MGraph.recolor, Function.update_of_ne h, SubstSPD_Kp_cls, h, ite_false]

omit [DecidableEq V] in
private theorem GlobalGoodRows_K2_ends {K : MGraph V E} {b r : E} {u₀ u₁ u₂ : V} (e : E) :
    (GlobalGoodRows_K2 K b r u₀ u₁ u₂).ends e =
      if e = r then (u₂, u₀) else if e = b then (u₀, u₁) else K.ends e :=
  SubstSPD_Kp_ends e

variable {K : MGraph V E} {b r : E} {u₀ u₁ u₂ : V}

/-- `K₂` is sequentially pre-deterministic. -/
private theorem GlobalGoodRows_K2_spd (hs : K.SPD) (hbr : b ≠ r) (hu₀ : u₀ ∈ K.int)
    (hu₁ : u₁ ∈ K.int)
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus)
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2) :
    (GlobalGoodRows_K2 K b r u₀ u₁ u₂).SPD := by
  have h := SubstSPD_Kp_spd hs hbr hu₀ hu₁ hk3 hk4 (cb := .diff) (Or.inr rfl) u₂ u₀ hv
  unfold GlobalGoodRows_K2
  rw [GlobalGoodRows_recolor_eq]
  exact (MGraph.spd_red _ _ _ r _ _ none (Or.inr (by simp [SubstSPD_Kp_cls]))
    (Or.inl rfl)).2 h

/-- A red solid edge that crosses no proper isolated subset, set absent, keeps the globally
standard property. -/
private theorem GlobalGoodRows_gs_dropRed {G : MGraph V E} {e₀ : E} (hg : G.GloballyStandard)
    (hr : G.cls e₀ = some .minus)
    (hcut : ∀ P, G.IsProperIso G.int P → ¬ G.Cut P e₀) : (G.recolor e₀ none).GloballyStandard := by
  have hcr : ∀ P e, (G.recolor e₀ none).Crosses P e ↔ G.Crosses P e := by
    intro P e
    by_cases he : e = e₀
    · subst he
      constructor
      · rintro ⟨h, -⟩
        exact absurd (by simp [MGraph.recolor]) h
      · rintro ⟨-, h, -⟩
        exact absurd hr h
    · simp only [MGraph.Crosses, MGraph.recolor, Function.update_of_ne he]
  have hpi : ∀ P, (G.recolor e₀ none).IsProperIso (G.recolor e₀ none).int P ↔
      G.IsProperIso G.int P := by
    intro P
    unfold MGraph.IsProperIso MGraph.IsIsolated
    simp only [hcr]
    rfl
  refine ⟨?_, fun P hP => ?_⟩
  · rw [GlobalGoodRows_recolor_eq]
    exact (MGraph.spd_red _ _ _ e₀ _ _ none (Or.inr hr) (Or.inl rfl)).2 hg.1
  · have hP' := (hpi P).1 hP
    obtain ⟨-, e, e', hee, he, he'⟩ := hg.2 P hP'
    have hred : ∀ f, G.RedCrosses P f → (G.recolor e₀ none).RedCrosses P f := by
      rintro f ⟨h1, h2, h3, h4⟩
      have hf : f ≠ e₀ := by
        rintro rfl
        exact hcut P hP' h4
      exact ⟨by simp only [MGraph.recolor, Function.update_of_ne hf]; exact h1, h2, h3, h4⟩
    exact ⟨hP.1, e, e', hee, hred e he, hred e' he'⟩

/-- `K₂` is globally standard when `u₂ = u₁`: the edge `r` then joins `u₁` and `u₀`, which lie in
every proper isolated subset. -/
private theorem GlobalGoodRows_K2_gs (hgs : K.GloballyStandard) (hbr : b ≠ r) (hu₀ : u₀ ∈ K.int)
    (hu₁ : u₁ ∈ K.int) (hu₂ : u₂ ∈ K.int) (hm₀ : u₀ ∈ K.MIS) (hm₁ : u₁ ∈ K.MIS)
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus)
    (hr : K.ends r = (u₂, u₀) ∧ (K.cls r = some .minus ∨ u₂ = u₀)) (h21 : u₂ = u₁)
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2) :
    (GlobalGoodRows_K2 K b r u₀ u₁ u₂).GloballyStandard := by
  have h := SubstSPD_Kp_gs hgs hbr hu₀ hu₁ hu₂ hm₀ hm₁ hk3 hk4 hr (cb := .diff) (Or.inr rfl)
    (p := u₂) (q := u₀) (Or.inl ⟨rfl, Or.inl rfl⟩) hv
  have hk3' : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀)) := by
    rcases hk3 with h | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hcr := SubstSPD_Kp_crosses (cb := .diff) (p := u₂) (q := u₀) (Or.inr rfl) hbr hk3' hk4
  refine GlobalGoodRows_gs_dropRed h (by simp [SubstSPD_Kp_cls]) fun P hP hc => ?_
  have hPK : K.IsProperIso K.int P := by
    unfold MGraph.IsProperIso MGraph.IsIsolated at hP ⊢
    simp only [hcr] at hP
    exact hP
  simp only [MGraph.MIS, Finset.mem_filter] at hm₀ hm₁
  have h0 := hm₀.2 P hPK
  have h1 := hm₁.2 P hPK
  unfold MGraph.Cut at hc
  simp only [SubstSPD_Kp_ends, ite_true, h21] at hc
  tauto

end Host2

/-! ## The inserted graph of a graph without internal atoms -/

section Insert

variable {V W E F : Type} [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
  [Fintype F]

/-- The edges of `L` other than `f₀`, as edges of the inserted graph. -/
private def GlobalGoodRows_oth (f₀ : F) : Finset (E ⊕ F) :=
  (Finset.univ.filter (· ≠ f₀)).map Function.Embedding.inr

omit [DecidableEq V] [DecidableEq W] [DecidableEq E] in
private theorem GlobalGoodRows_mem_oth {f₀ : F} (e : E ⊕ F) :
    e ∈ (GlobalGoodRows_oth f₀ : Finset (E ⊕ F)) ↔ ∃ f, f ≠ f₀ ∧ e = .inr f := by
  simp only [GlobalGoodRows_oth, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.inr_apply]
  exact ⟨fun ⟨f, h, he⟩ => ⟨f, h, he.symm⟩, fun ⟨f, h, he⟩ => ⟨f, h, he.symm⟩⟩

/-- When `L` has no internal vertex, the inserted graph with the edges of `L` other than `f₀` set
absent is `K₂` up to names: the diffusive edge `f₀` of `L`, between the images of its ends, takes
the place of `b`. -/
private theorem GlobalGoodRows_tr (K : MGraph V E) (L : MGraph W F) (σ : W → V) (b r : E)
    (hbr : b ≠ r) (hLint : L.int = ∅) (u₀ u₁ u₂ : V) (hu₀ : u₀ ∈ K.int) (hu₁ : u₁ ∈ K.int)
    (f₀ : F) (hc0 : L.cls f₀ = some .diff)
    (he0 : (σ (L.ends f₀).1 = u₀ ∧ σ (L.ends f₀).2 = u₁) ∨
      (σ (L.ends f₀).1 = u₁ ∧ σ (L.ends f₀).2 = u₀))
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2) :
    (GlobalGoodRows_K2 K b r u₀ u₁ u₂).Transported
      (GlobalGoodRows_drop (K.insert L σ {b, r}) (GlobalGoodRows_oth f₀)) := by
  set Gl := GlobalGoodRows_drop (K.insert L σ {b, r}) (GlobalGoodRows_oth f₀) with hGl
  have hcl : ∀ e, Gl.cls (.inl e) = if e ∈ ({b, r} : Finset E) then none else K.cls e := by
    intro e
    change (if Sum.inl e ∈ GlobalGoodRows_oth f₀ then none else _) = _
    rw [ite_eq_right (by rw [GlobalGoodRows_mem_oth]; rintro ⟨f, -, h⟩; cases h)]
    rfl
  have hcf : ∀ f, Gl.cls (.inr f) = if f = f₀ then L.cls f else none := by
    intro f
    change (if Sum.inr f ∈ GlobalGoodRows_oth f₀ then none else L.cls f) = _
    by_cases h : f = f₀
    · rw [ite_eq_right (by
          rw [GlobalGoodRows_mem_oth]; rintro ⟨f', hf', he⟩; cases he; exact hf' h),
        ite_eq_left h]
    · rw [ite_eq_left ((GlobalGoodRows_mem_oth _).2 ⟨f, h, rfl⟩), ite_eq_right h]
  have hen : ∀ e, Gl.ends (.inl e) = (.inl (K.ends e).1, .inl (K.ends e).2) := fun e => rfl
  have hef : ∀ f, Gl.ends (.inr f) = (.inl (σ (L.ends f).1), .inl (σ (L.ends f).2)) := by
    intro f
    change ((if (L.ends f).1 ∈ L.int then (Sum.inr (L.ends f).1 : V ⊕ W)
      else .inl (σ (L.ends f).1)), (if (L.ends f).2 ∈ L.int then (Sum.inr (L.ends f).2 : V ⊕ W)
        else .inl (σ (L.ends f).2))) = _
    rw [hLint]
    simp
  let g : E → E ⊕ F := fun e => if e = b then .inr f₀ else .inl e
  have hgb : g b = .inr f₀ := by simp [g]
  have hgo : ∀ e, e ≠ b → g e = .inl e := fun e h => by simp [g, h]
  have hginj : Function.Injective g := by
    intro e₁ e₂ h
    by_cases h1 : e₁ = b <;> by_cases h2 : e₂ = b <;> simp_all [g]
  refine ⟨Sum.inl, g, fun e₁ e₂ _ _ h => hginj h, Sum.inl_injective.injOn, ?_, ?_,
    fun e he => ?_, fun e he => ?_, fun e he => ?_, fun e' he' => ?_⟩
  · ext z
    rcases z with v | w
    · simp [hGl, GlobalGoodRows_drop, MGraph.insert, GlobalGoodRows_K2, SubstSPD_Kp,
        MGraph.setEdge, MGraph.recolor]
    · simp [hGl, GlobalGoodRows_drop, MGraph.insert, hLint]
  · ext z
    simp [hGl, GlobalGoodRows_drop, MGraph.insert, GlobalGoodRows_K2, SubstSPD_Kp,
      MGraph.setEdge, MGraph.recolor]
  · rw [GlobalGoodRows_K2_cls] at he
    rw [GlobalGoodRows_K2_ends]
    split_ifs with h1 h2
    · simp [h1] at he
    · exact ⟨Or.inl hu₀, Or.inl hu₁⟩
    · rw [ite_eq_right h1, ite_eq_right h2] at he
      exact hv e he
  · rw [GlobalGoodRows_K2_cls] at he ⊢
    by_cases h1 : e = r
    · simp [h1] at he
    · by_cases h2 : e = b
      · subst h2
        rw [hgb, hcf, ite_eq_left rfl, hc0, ite_eq_right h1, ite_eq_left rfl]
      · rw [hgo e h2, hcl, ite_eq_right h1, ite_eq_right h2, ite_eq_right (by simp [h1, h2])]
  · rw [GlobalGoodRows_K2_cls] at he
    rw [GlobalGoodRows_K2_ends]
    by_cases h1 : e = r
    · simp [h1] at he
    · by_cases h2 : e = b
      · subst h2
        rw [hgb, hef, ite_eq_right h1, ite_eq_left rfl]
        rcases he0 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl (by rw [h3, h4])
        · exact Or.inr (by rw [h3, h4])
      · rw [hgo e h2, hen, ite_eq_right h1, ite_eq_right h2]
        exact Or.inl rfl
  · rcases e' with e | f
    · rw [hcl]
      split_ifs with h
      · rfl
      · have h' : e ≠ b ∧ e ≠ r := by simpa using h
        by_contra hn
        refine he' e ?_ (hgo e h'.1)
        rw [GlobalGoodRows_K2_cls, ite_eq_right h'.2, ite_eq_right h'.1]
        exact hn
    · rw [hcf]
      split_ifs with h
      · subst h
        exact absurd hgb (he' b (by
          rw [GlobalGoodRows_K2_cls, ite_eq_right hbr, ite_eq_left rfl]; simp))
      · rfl

end Insert

section InsertSPD

variable {V W E F : Type} [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
  [Finite F]

variable (K : MGraph V E) (L : MGraph W F) (σ : W → V) (b r : E) (u₀ u₁ u₂ : V) (f₀ : F)

/-- **The inserted graph of a graph without internal vertices is sequentially
pre-deterministic** when `K` is: `L` has no internal vertex, its edges are absent, blue solid,
diffusive or red solid, the images of all its vertices are internal vertices of `K`, and its
diffusive edge `f₀` joins the images `u₀`, `u₁` of the ends of the blue solid edge `b`. -/
private theorem GlobalGoodRows_ins_spd (hbr : b ≠ r) (hs : K.SPD)
    (hng : ∀ e, K.cls e ≠ some .ghost) (hu₀ : u₀ ∈ K.int) (hu₁ : u₁ ∈ K.int)
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus)
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2)
    (hLint : L.int = ∅) (hσ : ∀ w, σ w ∈ K.int)
    (hLc : ∀ f, L.cls f = none ∨ L.cls f = some .plus ∨ L.cls f = some .diff ∨
      L.cls f = some .minus)
    (hc0 : L.cls f₀ = some .diff)
    (he0 : (σ (L.ends f₀).1 = u₀ ∧ σ (L.ends f₀).2 = u₁) ∨
      (σ (L.ends f₀).1 = u₁ ∧ σ (L.ends f₀).2 = u₀)) :
    (K.insert L σ {b, r}).SPD := by
  have := Fintype.ofFinite F
  have h2 := GlobalGoodRows_K2_spd (u₂ := u₀) hs hbr hu₀ hu₁ hk3 hk4 hv
  have h3 := (MGraph.spd_transport _ _ _ _ _ _
    (GlobalGoodRows_tr K L σ b r hbr hLint u₀ u₁ u₀ hu₀ hu₁ f₀ hc0 he0 hv)).2 h2
  refine GlobalGoodRows_spd_of_drop _ (SubstSPD_insert_noGhost σ _ hng (fun f => by
    rcases hLc f with h | h | h | h <;> rw [h] <;> simp)) _ (fun e he => ?_) h3
  obtain ⟨f, -, rfl⟩ := (GlobalGoodRows_mem_oth e).1 he
  have hend : ∀ w, (if w ∈ L.int then (.inr w : V ⊕ W) else .inl (σ w)) ∈
      (K.insert L σ {b, r}).int := by
    intro w
    rw [hLint]
    simp only [Finset.notMem_empty, ite_false]
    exact Finset.inl_mem_disjSum.2 (hσ w)
  rcases hLc f with h | h | h | h
  · exact Or.inl h
  all_goals exact Or.inr ⟨by simp [MGraph.insert, h], hend _, hend _⟩

/-- **The inserted graph of a graph without internal vertices is globally standard after the
merges** when `K` is and `u₂ = u₁`: the edges of `L` other than `f₀` join vertices with the same
image, so they are loops. -/
private theorem GlobalGoodRows_ins_gs [Finite E] (hbr : b ≠ r) (hgs : K.GloballyStandard)
    (hng : ∀ e, K.cls e ≠ some .ghost) (hu₀ : u₀ ∈ K.int) (hu₁ : u₁ ∈ K.int) (hu₂ : u₂ ∈ K.int)
    (hm₀ : u₀ ∈ K.MIS) (hm₁ : u₁ ∈ K.MIS)
    (hk3 : (K.cls b = none ∧ u₀ = u₁) ∨ (K.cls b = some .plus ∧ K.ends b = (u₁, u₀) ∧
      ∃ l, (K.induce K.MIS).IsPDOrder l ∧ l.head? = some b))
    (hk4 : K.cls r = none ∨ K.cls r = some .minus)
    (hr : K.ends r = (u₂, u₀) ∧ (K.cls r = some .minus ∨ u₂ = u₀)) (h21 : u₂ = u₁)
    (hv : ∀ e, K.cls e ≠ none → K.IsVtx (K.ends e).1 ∧ K.IsVtx (K.ends e).2)
    (hLint : L.int = ∅) (hLng : ∀ f, L.cls f ≠ some .ghost)
    (hc0 : L.cls f₀ = some .diff)
    (he0 : (σ (L.ends f₀).1 = u₀ ∧ σ (L.ends f₀).2 = u₁) ∨
      (σ (L.ends f₀).1 = u₁ ∧ σ (L.ends f₀).2 = u₀))
    (hloop : ∀ f, f ≠ f₀ → L.cls f ≠ none → σ (L.ends f).1 = σ (L.ends f).2)
    (π : V ⊕ W → V ⊕ W) (hidem : ∀ v, π (π v) = π v)
    (hint : ∀ v ∈ (K.insert L σ {b, r}).int, π v ∈ (K.insert L σ {b, r}).int)
    (hext : ∀ v ∈ (K.insert L σ {b, r}).ext, π v = v)
    (hnie : ∀ v ∈ (K.insert L σ {b, r}).int, π v ∉ (K.insert L σ {b, r}).ext)
    (hdis : Disjoint (K.insert L σ {b, r}).int (K.insert L σ {b, r}).ext)
    (hR2 : ∀ e, (K.insert L σ {b, r}).cls e ≠ none →
      (K.insert L σ {b, r}).IsVtx ((K.insert L σ {b, r}).ends e).1 ∧
        (K.insert L σ {b, r}).IsVtx ((K.insert L σ {b, r}).ends e).2) :
    (((K.insert L σ {b, r}).mapV π).unloop).GloballyStandard := by
  have := Fintype.ofFinite F
  set Gl := K.insert L σ {b, r} with hGl
  set G0 := GlobalGoodRows_drop Gl (GlobalGoodRows_oth f₀) with hG0
  have h2 := GlobalGoodRows_K2_gs hgs hbr hu₀ hu₁ hu₂ hm₀ hm₁ hk3 hk4 hr h21 hv
  have h3 : G0.GloballyStandard := (SubstMol_gs_transport
    (GlobalGoodRows_tr K L σ b r hbr hLint u₀ u₁ u₂ hu₀ hu₁ f₀ hc0 he0 hv)).2 h2
  have hngl : ∀ e, Gl.cls e ≠ some .ghost := SubstSPD_insert_noGhost σ _ hng hLng
  have hng0 : ∀ e, G0.cls e ≠ some .ghost := by
    intro e
    simp only [hG0, GlobalGoodRows_drop]
    split_ifs
    · simp
    · exact hngl e
  have hR0 : ∀ e, G0.cls e ≠ none → G0.IsVtx (G0.ends e).1 ∧ G0.IsVtx (G0.ends e).2 := by
    intro e he
    have : Gl.cls e ≠ none := by
      intro h
      apply he
      simp only [hG0, GlobalGoodRows_drop, h]
      split_ifs <;> rfl
    exact hR2 e this
  have h4 := MGraph.gs_mapV_merge _ _ G0 π hidem hint hext hnie h3.1 hng0 hdis hR0
    (fun P hP _ => h3.2 P hP)
  have heq : (G0.mapV π).unloop = (Gl.mapV π).unloop := by
    refine SubstSPD_mgext rfl rfl (fun _ => rfl) (fun e => ?_)
    change (if π (Gl.ends e).1 = π (Gl.ends e).2 then none else G0.cls e) =
      (if π (Gl.ends e).1 = π (Gl.ends e).2 then none else Gl.cls e)
    by_cases he : e ∈ GlobalGoodRows_oth f₀
    · obtain ⟨f, hf, rfl⟩ := (GlobalGoodRows_mem_oth _).1 he
      have h0 : G0.cls (.inr f) = none := by simp only [hG0, GlobalGoodRows_drop, ite_eq_left he]
      rw [h0]
      by_cases hc : L.cls f = none
      · have hc' : Gl.cls (.inr f) = none := hc
        rw [hc']
      · have hends : (Gl.ends (.inr f)).1 = (Gl.ends (.inr f)).2 := by
          change (if (L.ends f).1 ∈ L.int then (Sum.inr (L.ends f).1 : V ⊕ W)
            else .inl (σ (L.ends f).1)) = (if (L.ends f).2 ∈ L.int then
              (Sum.inr (L.ends f).2 : V ⊕ W) else .inl (σ (L.ends f).2))
          rw [hLint]
          simp only [Finset.notMem_empty, ite_false]
          rw [hloop f hf hc]
        have hπ : π (Gl.ends (.inr f)).1 = π (Gl.ends (.inr f)).2 := by rw [hends]
        simp only [hπ, ↓reduceIte]
    · simp only [hG0, GlobalGoodRows_drop, ite_eq_right he]
  rw [← heq]
  exact h4

end InsertSPD

/-! ## Graphs without internal atoms -/

section NoInt

variable (Γ : Graph 3 0)

private theorem GlobalGoodRows_unp0 (a : Fin 3) : Γ.Unpinned (.inl a) :=
  ⟨rfl, fun b => b.elim0⟩

private theorem GlobalGoodRows_rep0 (u : Atom 3 0) : Γ.molRep (Γ.flatAtom u) = u := by
  rcases u with a | b
  · rw [SubstSPD_flat_unpinned Γ (GlobalGoodRows_unp0 Γ a)]
    rfl
  · exact b.elim0

private theorem GlobalGoodRows_int0 : Γ.toMG'.int = ∅ := by
  ext v
  simp [Graph.toMG']

/-- Without ghost edges, every edge of the molecular graph of a graph without internal atoms is
absent, blue solid, diffusive or red solid. -/
private theorem GlobalGoodRows_cls0 (hng : Γ.NoGhost) (f : Fin Γ.comps.length ⊕ Fin 3) :
    Γ.toMG'.cls f = none ∨ Γ.toMG'.cls f = some .plus ∨ Γ.toMG'.cls f = some .diff ∨
      Γ.toMG'.cls f = some .minus := by
  rcases f with i | a
  · by_cases hk : Γ.comps[i].kind = .dot
    · exact Or.inl (SubstSPD_cls_dot Γ i hk)
    · rw [SubstSPD_cls_inl Γ i hk]
      split_ifs
      · exact Or.inl rfl
      · have hg : Γ.comps[i].kind ≠ .ghost := hng _ (List.getElem_mem i.2)
        generalize Γ.comps[i].kind = κ at hk hg ⊢
        cases κ with
        | G c => cases c <;> simp [Kind.mclass]
        | ghost => exact absurd rfl hg
        | dot => exact absurd rfl hk
        | aux j r b => cases b <;> simp [Kind.mclass]
        | _ => simp [Kind.mclass]
  · exact Or.inl (SubstSPD_pin_unpinned Γ (GlobalGoodRows_unp0 Γ a))

/-- A diffusive edge `Θ_{⊗⊕}` is a diffusive edge between `⊗` and `⊕` of the molecular graph. -/
private theorem GlobalGoodRows_f0 (i₀ : Fin Γ.comps.length)
    (hd : Γ.comps[i₀].kind.isDiffusive = true)
    (he : (Γ.comps[i₀].x = .inl 0 ∧ Γ.comps[i₀].y = .inl 1) ∨
      (Γ.comps[i₀].x = .inl 1 ∧ Γ.comps[i₀].y = .inl 0)) :
    Γ.toMG'.cls (.inl i₀) = some .diff ∧
      (Γ.toMG'.ends (.inl i₀) = (.inl 0, .inl 1) ∨ Γ.toMG'.ends (.inl i₀) = (.inl 1, .inl 0)) := by
  have hk : Γ.comps[i₀].kind ≠ .dot := fun h => by rw [h] at hd; exact absurd hd (by decide)
  have hne : Γ.comps[i₀].x ≠ Γ.comps[i₀].y := by
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp
  rw [SubstSPD_cls_inl Γ i₀ hk, SubstSPD_ends_inl Γ i₀ hk, GlobalGoodRows_rep0,
    GlobalGoodRows_rep0, ite_eq_right hne]
  refine ⟨SubstSPD_mclass_diff hd, ?_⟩
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- When at most one component is at `⊗`, no present edge of the molecular graph other than the
one of that component has an end at `⊗`. -/
private theorem GlobalGoodRows_otimes0
    (hle : (Γ.comps.filter fun c => c.x == .inl 0 || c.y == .inl 0).length ≤ 1)
    (i₀ : Fin Γ.comps.length) (h0 : Γ.comps[i₀].x = .inl 0 ∨ Γ.comps[i₀].y = .inl 0)
    (f : Fin Γ.comps.length ⊕ Fin 3) (hf : f ≠ .inl i₀) (hc : Γ.toMG'.cls f ≠ none) :
    (Γ.toMG'.ends f).1 ≠ .inl 0 ∧ (Γ.toMG'.ends f).2 ≠ .inl 0 := by
  rcases f with i | a
  · have hk : Γ.comps[i].kind ≠ .dot := fun h => hc (SubstSPD_cls_dot Γ i h)
    rw [SubstSPD_ends_inl Γ i hk, GlobalGoodRows_rep0, GlobalGoodRows_rep0]
    have hne : i ≠ i₀ := fun h => hf (by rw [h])
    by_contra hn
    simp only [not_and_or, not_not, ne_eq] at hn
    exact hne (SubstSPD_eq_of_le_one _ hle i i₀ (by simpa using hn) (by simpa using h0))
  · exact absurd (SubstSPD_pin_unpinned Γ (GlobalGoodRows_unp0 Γ a)) hc

/-- A graph without internal atoms does not satisfy the clause on the external atoms: `⊗` is not
identified with an internal atom, and no diffusive edge joins it to an internal or identified
atom. -/
private theorem GlobalGoodRows_noExt0 : ¬ Γ.ExtClause := by
  intro hE
  obtain ⟨c, -, -, h⟩ := (hE.2.2.1 (GlobalGoodRows_unp0 Γ 0)).1
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · rcases hy : c.y with a | b
    · exact h (hy ▸ GlobalGoodRows_unp0 Γ a)
    · exact b.elim0
  · rcases hx : c.x with a | b
    · exact h (hx ▸ GlobalGoodRows_unp0 Γ a)
    · exact b.elim0

end NoInt

section DA0

variable {m : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (Γ : Graph 3 0)

/-- **The substitution of a graph without internal atoms with an edge `Θ_{⊗⊕}`** ([II, Lemma 6.5
(3), (4)] for `n' = 0`): when `G = H.glue x y₁ y₂ (tVar true)` has no dotted edge, the invariant
`Graph.InvB'` and the blue solid edge `G_{y₁α}` chosen by Step 2, and `Γ` has no ghost edge and a
diffusive component between `⊗` and `⊕`, the graph `H.glue x y₁ y₂ Γ` is sequentially
pre-deterministic in the block reading: the diffusive edge `Θ_{xy₁}` takes the place of `G_{y₁α}`,
`Ḡ_{y₂α}` is removed, and every other edge of `Γ` joins two of the molecules of `x`, `y₁`, `y₂`. -/
private theorem GlobalGoodRows_dA0_spd (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB')
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (hng : Γ.NoGhost) (i₀ : Fin Γ.comps.length) (hd : Γ.comps[i₀].kind.isDiffusive = true)
    (he : (Γ.comps[i₀].x = .inl 0 ∧ Γ.comps[i₀].y = .inl 1) ∨
      (Γ.comps[i₀].x = .inl 1 ∧ Γ.comps[i₀].y = .inl 0)) :
    spdPM' (H.glue x y₁ y₂ Γ) := by
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨π, hidem, hint, hext, hnie, hdis, hR2, -, ht⟩ :=
    toMG'_glue m 0 H x y₁ y₂ Γ hD hx hy₁ hy₂
  obtain ⟨hK1, hK2, -, hu₀, hu₁, hu₂, -, -, hk3, hk4, -, -⟩ :=
    SubstSPD_host H x y₁ y₂ hx hy₁ hy₂ hD hI hst
  obtain ⟨hc0, he0⟩ := GlobalGoodRows_f0 Γ i₀ hd he
  have hbr : (Sum.inl (SubstSPD_bI H x y₁ y₂) :
      Fin (H.glue x y₁ y₂ (tVar true)).comps.length ⊕ Fin 3) ≠ .inl (SubstSPD_rI H x y₁ y₂) := by
    simp [SubstSPD_bI, SubstSPD_rI]
  have hσ : ∀ w : Atom 3 0, (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep
      (liftA 1 (![x, y₁, y₂] i))) fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x)) w ∈
        (H.glue x y₁ y₂ (tVar true)).toMG'.int := by
    rintro (i | j)
    · fin_cases i
      · exact hu₀
      · exact hu₁
      · exact hu₂
    · exact j.elim0
  have hGl := GlobalGoodRows_ins_spd _ Γ.toMG' _ _ _ _ _ (.inl i₀) hbr hK1 hK2 hu₀ hu₁ hk3 hk4
    (fun e _ => MolInsert_toMG'_ends_vtx 3 _ _ e) (GlobalGoodRows_int0 Γ) hσ
    (GlobalGoodRows_cls0 Γ hng) hc0 (by
      rcases he0 with h | h <;> rw [h]
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩)
  have hng' := SubstSPD_insert_noGhost
    (Sum.elim (fun i => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 (![x, y₁, y₂] i)))
      fun _ => (H.glue x y₁ y₂ (tVar true)).molRep (liftA 1 x))
    {.inl (SubstSPD_bI H x y₁ y₂), .inl (SubstSPD_rI H x y₁ y₂)} hK2
    (Graph.toMG'_noGhost _ hng)
  have h1 := MGraph.spd_mapV_merge _ _ _ π hidem hint hext hnie hGl hng' hdis hR2
  exact (MGraph.spd_transport _ _ _ _ _ _ ht).2 h1

/-- **The globally standard property for `y₁ = y₂`**: under the hypotheses of
`GlobalGoodRows_dA0_spd`, with `G` globally standard in the block reading, `y₁ = y₂` and at most
one component of `Γ` at `⊗`, the graph `H.glue x y₁ y₂ Γ` is globally standard in the block
reading: the edges of `Γ` other than `Θ_{⊗⊕}` become loops at `y₁ = y₂`. -/
private theorem GlobalGoodRows_dA0_gs (hD : (H.glue x y₁ y₂ (tVar true)).DotFree)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) (hy : y₁ = y₂)
    (hng : Γ.NoGhost) (i₀ : Fin Γ.comps.length) (hd : Γ.comps[i₀].kind.isDiffusive = true)
    (he : (Γ.comps[i₀].x = .inl 0 ∧ Γ.comps[i₀].y = .inl 1) ∨
      (Γ.comps[i₀].x = .inl 1 ∧ Γ.comps[i₀].y = .inl 0))
    (hle : (Γ.comps.filter fun c => c.x == .inl 0 || c.y == .inl 0).length ≤ 1) :
    gsPM' (H.glue x y₁ y₂ Γ) := by
  subst hy
  obtain ⟨hx, hy₁, -⟩ := step2EdgeB'_internal m H x y₁ y₁ hst
  obtain ⟨π, hidem, hint, hext, hnie, hdis, hR2, -, ht⟩ :=
    toMG'_glue m 0 H x y₁ y₁ Γ hD hx hy₁ hy₁
  obtain ⟨-, hK2, -, hu₀, hu₁, hu₂, hm₀, hm₁, hk3, hk4, -, hr⟩ :=
    SubstSPD_host H x y₁ y₁ hx hy₁ hy₁ hD hI hst
  obtain ⟨hc0, he0⟩ := GlobalGoodRows_f0 Γ i₀ hd he
  have hbr : (Sum.inl (SubstSPD_bI H x y₁ y₁) :
      Fin (H.glue x y₁ y₁ (tVar true)).comps.length ⊕ Fin 3) ≠ .inl (SubstSPD_rI H x y₁ y₁) := by
    simp [SubstSPD_bI, SubstSPD_rI]
  have h0 := he.imp (fun h => h.1) (fun h => h.2)
  have hσ : ∀ w : Atom 3 0, w ≠ .inl 0 → (Sum.elim (fun i => (H.glue x y₁ y₁ (tVar true)).molRep
      (liftA 1 (![x, y₁, y₁] i))) fun _ => (H.glue x y₁ y₁ (tVar true)).molRep (liftA 1 x)) w =
        (H.glue x y₁ y₁ (tVar true)).molRep (liftA 1 y₁) := by
    rintro (i | j) h
    · fin_cases i
      · exact absurd rfl h
      · rfl
      · rfl
    · exact j.elim0
  have hG := GlobalGoodRows_ins_gs _ Γ.toMG' _ _ _ _ _ _ (.inl i₀) hbr hgs hK2 hu₀ hu₁ hu₂ hm₀ hm₁
    hk3 hk4 hr rfl (fun e _ => MolInsert_toMG'_ends_vtx 3 _ _ e) (GlobalGoodRows_int0 Γ)
    (fun f => by rcases GlobalGoodRows_cls0 Γ hng f with h | h | h | h <;> rw [h] <;> simp)
    hc0 (by
      rcases he0 with h | h <;> rw [h]
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩)
    (fun f hf hc => by
      obtain ⟨h1, h2⟩ := GlobalGoodRows_otimes0 Γ hle i₀ h0 f hf hc
      rw [hσ _ h1, hσ _ h2])
    π hidem hint hext hnie hdis hR2
  exact (SubstMol_gs_transport ht).2 hG

end DA0

/-! ## The graphs of `A` and `Q` -/

section Graphs

variable {n : ℕ} (Γ : Graph 3 n)

/-- A path of dotted edges from an external atom with the property `Q` to an internal atom
contains a dotted edge from an external atom with `Q` to an internal atom, when `Q` takes the
same value at the two ends of every dotted edge between external atoms. -/
private theorem GlobalGoodRows_walk (Q : Atom 3 n → Prop)
    (hQ : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true → c.y.isLeft = true →
      (Q c.x ↔ Q c.y)) {u v : Atom 3 n} (w : Γ.dotGraph.Walk u v) :
    u.isLeft = true → Q u → v.isRight = true →
      ∃ c ∈ Γ.comps, c.kind = .dot ∧ ((c.x.isLeft = true ∧ Q c.x ∧ c.y.isRight = true) ∨
        (c.y.isLeft = true ∧ Q c.y ∧ c.x.isRight = true)) := by
  induction w with
  | nil =>
    intro hl _ hr
    revert hl hr
    cases ‹Atom 3 n› <;> simp
  | @cons u w v hadj p ih =>
    intro hl hq hr
    rw [Graph.dotGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨c, hc, hk, hx, hy⟩ | ⟨c, hc, hk, hx, hy⟩⟩ := hadj
    · subst hx hy
      rcases hw : c.y with a | b
      · have hwl : c.y.isLeft = true := by rw [hw]; rfl
        exact ih hwl ((hQ c hc hk hl hwl).1 hq) hr
      · exact ⟨c, hc, hk, Or.inl ⟨hl, hq, by rw [hw]; rfl⟩⟩
    · subst hx hy
      rcases hw : c.x with a | b
      · have hwl : c.x.isLeft = true := by rw [hw]; rfl
        exact ih hwl ((hQ c hc hk hwl hl).2 hq) hr
      · exact ⟨c, hc, hk, Or.inr ⟨hl, hq, by rw [hw]; rfl⟩⟩

/-- An external atom identified with an internal atom has a dotted edge from an external atom to
an internal atom. -/
private theorem GlobalGoodRows_pinned {a : Fin 3} (h : ¬ Γ.Unpinned (.inl a)) :
    ∃ c ∈ Γ.comps, c.kind = .dot ∧ ((c.x.isLeft = true ∧ c.y.isRight = true) ∨
      (c.y.isLeft = true ∧ c.x.isRight = true)) := by
  have : ∃ b, Γ.SameBlock (.inl a) (.inr b) := by
    by_contra hn
    push Not at hn
    exact h ⟨rfl, hn⟩
  obtain ⟨b, ⟨w⟩⟩ := this
  obtain ⟨c, hc, hk, h⟩ :=
    GlobalGoodRows_walk Γ (fun _ => True) (fun _ _ _ _ _ => Iff.rfl) w rfl trivial rfl
  refine ⟨c, hc, hk, ?_⟩
  rcases h with ⟨h1, -, h2⟩ | ⟨h1, -, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- With the clause on the external atoms and only diffusive edges at `⊗`, some waved, diffusive
or dotted edge joins an internal atom to an external atom (`Graph.RgCheck`). -/
private theorem GlobalGoodRows_rgCheck (hE : Γ.ExtClause) (hT : Γ.TensorDiffusive) :
    Γ.RgCheck := by
  right
  obtain ⟨c, hc, hd, h⟩ := (hE.2.2.1 (SubstSPD_unpinned_zero Γ hT)).1
  have key : ∀ u : Atom 3 n, ¬ Γ.Unpinned u → u.isRight = true ∨
      ∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧
        (c.x.isRight = true ∧ c.y.isLeft = true ∨ c.x.isLeft = true ∧ c.y.isRight = true) := by
    rintro (a | b) hu
    · obtain ⟨c, hc, hk, h⟩ := GlobalGoodRows_pinned Γ hu
      refine Or.inr ⟨c, hc, Or.inl (by rw [hk]; rfl), ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨h2, h1⟩
    · exact Or.inl rfl
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rcases key _ hy with h | h
    · exact ⟨c, hc, Or.inr hd, Or.inr ⟨by rw [hx]; rfl, h⟩⟩
    · exact h
  · rcases key _ hx with h | h
    · exact ⟨c, hc, Or.inr hd, Or.inl ⟨h, by rw [hy]; rfl⟩⟩
    · exact h

/-- A graph with `⊕`, `⊖` in one dotted block, the clause on the external atoms and only
diffusive edges at `⊗` is a `⊕/⊖`-recollision graph: the block contains an internal atom, and a
dotted edge joins `⊕` or `⊖` to an internal atom. -/
private theorem GlobalGoodRows_recoll (hP : Γ.PMBlock) (hE : Γ.ExtClause)
    (hT : Γ.TensorDiffusive) : Γ.IsRecollision {1, 2} := by
  have hs := (Graph.pmBlock_iff_sameBlock Γ).1 hP
  obtain ⟨b, ⟨w⟩⟩ := hE.1 (.inl 1) (.inl 2) (by simp) hs
  have hQ : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true → c.y.isLeft = true →
      (c.x ≠ .inl 0 ↔ c.y ≠ .inl 0) := by
    intro c hc hk _ _
    have := List.all_eq_true.1 hT c hc
    have h1 : c.x ≠ .inl 0 := fun h => by simp [h, hk, Kind.isDiffusive] at this
    have h2 : c.y ≠ .inl 0 := fun h => by simp [h, hk, Kind.isDiffusive] at this
    exact ⟨fun _ => h2, fun _ => h1⟩
  obtain ⟨c, hc, hk, h⟩ := GlobalGoodRows_walk Γ (· ≠ .inl 0) hQ w rfl (by simp) rfl
  have key : ∀ u : Atom 3 n, u.isLeft = true → u ≠ .inl 0 →
      ∃ b ∈ ({1, 2} : Finset (Fin 3)), u = .inl b := by
    rintro (a | a) h1 h2
    · refine ⟨a, ?_, rfl⟩
      fin_cases a <;> simp_all
    · simp at h1
  refine ⟨c, hc, hk, ?_⟩
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨key _ h1 h2, h3⟩
  · exact Or.inr ⟨key _ h1 h2, h3⟩

/-- With `Graph.RootAtPlus`, only diffusive edges at `⊗` and [II, Def 3.2 (9)], the graph with
its solid edges reversed has a diffusive component `Θ_{⊗⊕}`, and no other component at `⊗`. -/
private theorem GlobalGoodRows_root (hR : Γ.RootAtPlus) (hT : Γ.TensorDiffusive)
    (hA : Γ.AtExternals) :
    (∃ i₀ : Fin Γ.swapSolid.comps.length, Γ.swapSolid.comps[i₀].kind.isDiffusive = true ∧
      ((Γ.swapSolid.comps[i₀].x = .inl 0 ∧ Γ.swapSolid.comps[i₀].y = .inl 1) ∨
        (Γ.swapSolid.comps[i₀].x = .inl 1 ∧ Γ.swapSolid.comps[i₀].y = .inl 0))) ∧
    (Γ.swapSolid.comps.filter fun c => c.x == .inl 0 || c.y == .inl 0).length ≤ 1 := by
  set p0 : Comp (Atom 3 n) → Bool :=
    fun c => c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0) with hp0
  have hlen : (Γ.comps.filter p0).length = 1 := hA.1
  obtain ⟨c, hc⟩ := List.length_pos_iff_exists_mem.1 (by omega : 0 < (Γ.comps.filter p0).length)
  obtain ⟨hcm, hcp⟩ := List.mem_filter.1 hc
  have hd : c.kind.isDiffusive = true := by
    simp only [hp0, Bool.and_eq_true] at hcp
    exact hcp.1
  have hends : (c.x = .inl 0 ∧ c.y = .inl 1) ∨ (c.x = .inl 1 ∧ c.y = .inl 0) := by
    have := List.all_eq_true.1 hR c hcm
    have hcp' : (c.kind.isDiffusive && (c.x == .inl 0 || c.y == .inl 0)) = true := hcp
    rw [hcp'] at this
    simpa using this
  have hns : c.swapSolid = c := by
    have : c.kind.isSolid = false := by
      cases hκ : c.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
    simp [Comp.swapSolid, this]
  have hmem : c ∈ Γ.swapSolid.comps := List.mem_map.2 ⟨c, hcm, hns⟩
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hmem
  refine ⟨⟨⟨i, hi⟩, by simp [hci, hd], by simpa [hci] using hends⟩, ?_⟩
  rw [SubstSPD_swap_filter Γ (fun c => by unfold Comp.swapSolid; split <;> simp [Bool.or_comm])]
  have : Γ.comps.filter (fun c => c.x == .inl 0 || c.y == .inl 0) = Γ.comps.filter p0 := by
    refine List.filter_congr fun c hc => ?_
    have := List.all_eq_true.1 hT c hc
    simp only [hp0]
    cases h : (c.x == .inl 0 || c.y == .inl 0) <;> simp_all
  rw [this, hlen]

end Graphs

/-! ## Rows (3), (3′) and the invariant of row (4) -/

section Rows

/-- The substituted graph of a graph `g` without labels has no labels when `H` has none. -/
private theorem GlobalGoodRows_glue_labelFree {m n₀ : ℕ} {H : Graph 3 m} {x y₁ y₂ : Atom 3 m}
    {g : Graph 3 n₀} (hL : H.LabelFree) (hg : g.LabelFree) :
    (H.glue x y₁ y₂ g.swapSolid).LabelFree := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, hL c₀ hc₀]
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, SubstSPD_swap_labelFree hg c₀ hc₀]

/-- Rows (3) and (3′) for one graph `g` of `A`: every `O_dot` form `t` of the substituted graph
is normal regular without dotted edges and labels; if `y₁ = y₂` and `⊕`, `⊖` lie in one block of
`g`, `t` is globally standard of scaling order `≥ ord G + 1`, and otherwise `t` is sequentially
pre-deterministic of scaling order `≥ n + 1`. -/
private theorem GlobalGoodRows_A (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m)
    (x y₁ y₂ : Atom 3 m) (hn : 3 ≤ n) (hcore : n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63)
    (hL : H.LabelFree) (hN : (H.glue x y₁ y₂ (tVar true)).Normal C)
    (hd : (H.glue x y₁ y₂ (tVar true)).DotFree) (ho : 4 ≤ (H.glue x y₁ y₂ (tVar true)).ord)
    (hI : (H.glue x y₁ y₂ (tVar true)).InvB') (hgs : gsPM' (H.glue x y₁ y₂ (tVar true)))
    (hst : ∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i)
    (g : Σ n₀, Graph 3 n₀) (hg : g ∈ 𝒯.A) (t : Tracked 3 (m + g.1))
    (ht : t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid)) :
    (∃ C', t.g.Normal C') ∧ t.g.DotFree ∧ t.g.LabelFree ∧
      ((y₁ = y₂ ∧ g.2.PMBlock) →
        gsPM' t.g ∧ (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord) ∧
      (¬ (y₁ = y₂ ∧ g.2.PMBlock) → (n : ℤ) + 1 ≤ t.g.ord ∧ spdPM' t.g) := by
  obtain ⟨n₀, g₀⟩ := g
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨-, hSh, hDef⟩ := hcore
  have hall : (⟨n₀, g₀⟩ : Σ n₀, Graph 3 n₀) ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by simp [hg]
  obtain ⟨⟨C', hgN⟩, hTK, hAE, -⟩ := hSh.1.1 ⟨n₀, g₀⟩ (by simp [hg])
  obtain ⟨hgL, hk⟩ := hSh.2.2.1 _ hg
  obtain ⟨hspd, hroot⟩ := hDef.1.2.1 _ hg
  obtain ⟨hT, hX, hNL, hlab⟩ := hDef.2.1 _ hall
  have hRec := hDef.2.2.1 _ hg
  have h5 := hDef.2.2.2.1 ⟨n₀, g₀⟩ (by simp [hg])
  have hG := SubstSPD_noGhost_of_tKinds hTK
  have hEx : n₀ ≠ 0 → g₀.ExtClause ∧ g₀.ColourInvB := fun h0 =>
    hroot.resolve_left fun h => h0 h.1
  have hRg : g₀.RgCheck := by
    by_cases h0 : n₀ = 0
    · exact Or.inl h0
    · exact GlobalGoodRows_rgCheck g₀ (hEx h0).1 hT
  obtain ⟨hN', hd', hε, hε', -⟩ := glue_oDotT_normal m n₀ C C' H x y₁ y₂ g₀.swapSolid hx hy₁ hy₂
    hL hN hd (Graph.swapSolid_Normal hgN) (SubstSPD_swap_otimesNoDot hT)
    (by rw [SubstSPD_swap_dotExcess]; exact hX) (SubstDC_swap_rgCheck hRg)
    (by rw [SubstSPD_swap_labels]; exact hlab) (SubstSPD_swap_noLabDot hNL) t ht
  have e1 := glue_ord 3 m n₀ H x y₁ y₂ g₀.swapSolid
  have e2 := glue_ord 3 m 1 H x y₁ y₂ (tVar true)
  have e3 : g₀.swapSolid.ord = g₀.ord := (swapSolid_basic 3 n₀ g₀).2.1
  rw [SubstSPD_tVar_ord] at e2
  have hbal := SubstSPD_oDotT_bal (SubstSPD_glue_bal H x y₁ y₂ g₀.swapSolid hN
    (Graph.swapSolid_Normal hgN)) (SubstSPD_glue_dots H x y₁ y₂ g₀.swapSolid hx hy₁ hy₂ hd) t ht
  have hroot0 : n₀ = 0 → g₀.RootAtPlus := fun h0 =>
    (hroot.resolve_right fun h => by subst h0; exact GlobalGoodRows_noExt0 g₀ h.1).2
  refine ⟨hN', hd', SubstSPD_oDotT_labelFree (GlobalGoodRows_glue_labelFree hL hgL) t ht,
    fun hε1 => ⟨?_, ?_⟩, fun hε0 => ⟨?_, ?_⟩⟩
  · by_cases h0 : n₀ = 0
    · subst h0
      obtain ⟨⟨i₀, hd₀, he₀⟩, hle⟩ := GlobalGoodRows_root g₀ (hroot0 rfl) hT hAE
      exact hbal.2.2 (GlobalGoodRows_dA0_gs H x y₁ y₂ g₀.swapSolid hd hI hgs hst hε1.1
        (SubstSPD_swap_noGhost _ hG) i₀ hd₀ he₀ hle)
    · obtain ⟨hE, hC⟩ := hEx h0
      have hrc := GlobalGoodRows_recoll g₀ hε1.2 hE hT
      exact (substGSB m n₀ H x y₁ y₂ g₀ hd hI hgs hst (hRec hrc) hE hC hT hAE hG hX
        (SubstSPD_diagRecoll_of hrc)).2 C C' hN hgN t ht
  · have := hε ⟨hε1.1, (SubstSPD_swap_pmBlock g₀).2 hε1.2⟩
    have := h5 hε1.2
    dsimp only at *
    omega
  · have := hε' (fun h => hε0 ⟨h.1, (SubstSPD_swap_pmBlock g₀).1 h.2⟩)
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hk
    dsimp only at *
    omega
  · by_cases h0 : n₀ = 0
    · subst h0
      obtain ⟨⟨i₀, hd₀, he₀⟩, -⟩ := GlobalGoodRows_root g₀ (hroot0 rfl) hT hAE
      exact hbal.1.2 (GlobalGoodRows_dA0_spd H x y₁ y₂ g₀.swapSolid hd hI hst
        (SubstSPD_swap_noGhost _ hG) i₀ hd₀ he₀)
    · obtain ⟨hE, hC⟩ := hEx h0
      exact (substSPDB m n₀ H x y₁ y₂ g₀ hd hI hst hspd hE hC hT hAE hG hX).2 C C' hN hgN t ht

/-- **Row (3) of [II, Lemma 6.5]** in the block reading (the conjunct of [II, Lemma 6.5] on the
graphs of `A`), with the hypotheses on `𝒯` of [II, Def 3.2] at order `n - 1` and of [II, Def 6.3]:
under the hypotheses of [II, Lemma 6.5] on `G = H.glue x y₁ y₂ (tVar true)`, every `O_dot` form
`t` of the substitution of a graph `g` of `A` is normal regular without dotted edges and without
labels, and is sequentially pre-deterministic in the block reading of scaling order `≥ n + 1`, or
(3′) `y₁ = y₂`, `⊕`, `⊖` lie in one dotted block of `g`, and `t` is globally standard of scaling
order `≥ ord G + 1`. -/
theorem globalGood_row3 :
  ∀ (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    3 ≤ n → (n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    (∀ g ∈ 𝒯.A, ∀ t ∈ oDotT (H.glue x y₁ y₂ g.2.swapSolid), (∃ C', t.g.Normal C') ∧
      t.g.DotFree ∧ t.g.LabelFree ∧
        (((n : ℤ) + 1 ≤ t.g.ord ∧ spdPM' t.g) ∨
          (y₁ = y₂ ∧ g.2.PMBlock ∧ gsPM' t.g ∧
            (H.glue x y₁ y₂ (tVar true)).ord + 1 ≤ t.g.ord))) := by
  intro n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho _ hI _ hgs _ _ hst g hg t ht
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    GlobalGoodRows_A n D 𝒯 m C H x y₁ y₂ hn hcore hL hN hd ho hI hgs hst g hg t ht
  refine ⟨h1, h2, h3, ?_⟩
  by_cases hε : y₁ = y₂ ∧ g.2.PMBlock
  · exact Or.inr ⟨hε.1, hε.2, h4 hε⟩
  · exact Or.inl (h5 hε)

/-- **The invariant `Graph.InvB'` of the substituted `Q`-graphs** (the first sentence of the proof
of [II, Lemma 6.5 (4)], the first conjunct of row (4) of [II, Lemma 6.5]), with the hypotheses
on `𝒯` of [II, Def 3.2] at order `n - 1` and of [II, Def 6.3], and the clause
`∀ g ∈ 𝒯.Q, g.1 = 0 ∨ g.2.ExtClause ∧ g.2.ColourInvB`: under the hypotheses of
[II, Lemma 6.5] on `G = H.glue x y₁ y₂ (tVar true)`, the substitution
`H.glue x y₁ y₂ g.swapSolid` of every graph `g` of `Q` has the invariant `Graph.InvB'`. -/
theorem globalGood_row4_invB :
  ∀ (n D : ℕ) (𝒯 : TRec) (m C : ℕ) (H : Graph 3 m) (x y₁ y₂ : Atom 3 m),
    3 ≤ n → (n - 1 < D ∧ 𝒯.Shape (n - 1) (n - 1) D ∧ 𝒯.Def63) →
    (∀ g ∈ 𝒯.Q, g.1 = 0 ∨ g.2.ExtClause ∧ g.2.ColourInvB) → H.LabelFree →
    (H.glue x y₁ y₂ (tVar true)).Normal C → (H.glue x y₁ y₂ (tVar true)).DotFree →
    4 ≤ (H.glue x y₁ y₂ (tVar true)).ord → (H.glue x y₁ y₂ (tVar true)).ord ≤ n →
    (H.glue x y₁ y₂ (tVar true)).InvB' → (H.glue x y₁ y₂ (tVar true)).TensorDiffusive →
    gsPM' (H.glue x y₁ y₂ (tVar true)) → ¬ (H.glue x y₁ y₂ (tVar true)).IsRecollision {1, 2} →
    (H.glue x y₁ y₂ (tVar true)).MISLocStdB →
    (∀ i : Fin (H.glue x y₁ y₂ (tVar true)).comps.length, i.val = H.comps.length + 1 →
      (H.glue x y₁ y₂ (tVar true)).Step2EdgeB' i) →
    ∀ g ∈ 𝒯.Q, (H.glue x y₁ y₂ g.2.swapSolid).InvB' := by
  intro n D 𝒯 m C H x y₁ y₂ _ ⟨_, hSh, hDef⟩ _ _ _ hd _ _ hI hT _ hnr _ hst g hg
  obtain ⟨n₀, g₀⟩ := g
  obtain ⟨hx, hy₁, hy₂⟩ := step2EdgeB'_internal m H x y₁ y₂ hst
  obtain ⟨-, hTK, hAE, -⟩ := hSh.1.1 ⟨n₀, g₀⟩ (by simp [hg])
  obtain ⟨hspd, -, hroot⟩ := hDef.1.2.2 _ hg
  obtain ⟨hTd, hX, -, -⟩ := hDef.2.1 ⟨n₀, g₀⟩ (by simp [hg])
  have hG := SubstSPD_noGhost_of_tKinds hTK
  have hmem : (⟨m + n₀, H.glue x y₁ y₂ g₀.swapSolid⟩ : Σ n, Graph 3 n) ∈
      H.globalSubst x y₁ y₂ [⟨n₀, g₀.swapSolid⟩] := by
    simp [Graph.globalSubst]
  obtain ⟨hC, hNG, hLI, -⟩ := globalSubst_clauses m H x y₁ y₂ _ hx hy₁ hy₂ hI.2.2.1 hI.2.1
    hI.2.2.2.1 hI.2.2.2.2 hT hnr (fun g' hg' => by
      simp only [List.mem_singleton] at hg'
      subst hg'
      exact SubstSPD_swap_noGhost _ hG) _ hmem
  have hE := globalSubst_extClause m H x y₁ y₂ _ hx hy₁ hy₂ hI.2.2.1 _ hmem
  refine ⟨?_, hC, hE, hNG, hLI⟩
  by_cases h0 : n₀ = 0
  · subst h0
    have hR := (hroot.resolve_right fun h => GlobalGoodRows_noExt0 g₀ h.1).2
    obtain ⟨⟨i₀, hd₀, he₀⟩, -⟩ := GlobalGoodRows_root g₀ hR hTd hAE
    exact GlobalGoodRows_dA0_spd H x y₁ y₂ g₀.swapSolid hd hI hst (SubstSPD_swap_noGhost _ hG) i₀
      hd₀ he₀
  · obtain ⟨hE', hC'⟩ := hroot.resolve_left fun h => h0 h.1
    exact (substSPDB m n₀ H x y₁ y₂ g₀ hd hI hst hspd hE' hC' hTd hAE hG hX).1

end Rows


set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

/-! ### Reachability by a closure computation -/

section Reach

variable {V : Type} [DecidableEq V]

/-- One step of the closure: the vertices of `U` adjacent to `S` are added to `S`. -/
private def GlobalGoodRows_grow (adj : V → V → Bool) (U S : List V) : List V :=
  S ++ U.filter fun v => !S.contains v && S.any fun u => adj u v

/-- `k` steps of the closure. -/
private def GlobalGoodRows_iter (adj : V → V → Bool) (U : List V) : ℕ → List V → List V
  | 0, S => S
  | k + 1, S => GlobalGoodRows_iter adj U k (GlobalGoodRows_grow adj U S)

/-- No vertex of `U` outside `S` is adjacent to `S`. -/
private def GlobalGoodRows_closedB (adj : V → V → Bool) (U S : List V) : Bool :=
  S.all fun u => U.all fun v => !adj u v || S.contains v

private theorem GlobalGoodRows_iter_sound (G : SimpleGraph V) [DecidableRel G.Adj] (U : List V)
    (u : V) : ∀ (k : ℕ) (S : List V), (∀ w ∈ S, G.Reachable u w) →
      ∀ w ∈ GlobalGoodRows_iter (fun a b => decide (G.Adj a b)) U k S, G.Reachable u w := by
  intro k
  induction k with
  | zero => intro S h; exact h
  | succ k ih =>
    intro S h
    apply ih
    intro w hw
    simp only [GlobalGoodRows_grow, List.mem_append, List.mem_filter, Bool.and_eq_true,
      List.any_eq_true, decide_eq_true_eq] at hw
    rcases hw with hw | ⟨-, -, v, hv, hadj⟩
    · exact h w hw
    · exact (h v hv).trans hadj.reachable

private theorem GlobalGoodRows_iter_mem (adj : V → V → Bool) (U : List V) :
    ∀ (k : ℕ) (S : List V), ∀ w ∈ S, w ∈ GlobalGoodRows_iter adj U k S := by
  intro k
  induction k with
  | zero => intro S w hw; exact hw
  | succ k ih =>
    intro S w hw
    exact ih _ w (List.mem_append_left _ hw)

private theorem GlobalGoodRows_closed (G : SimpleGraph V) [DecidableRel G.Adj] (U S : List V)
    (hU : ∀ v, v ∈ U) (hc : GlobalGoodRows_closedB (fun a b => decide (G.Adj a b)) U S = true)
    {u v : V} (hu : u ∈ S) (h : G.Reachable u v) : v ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hadj ih =>
    simp only [GlobalGoodRows_closedB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, List.contains_iff_mem] at hc
    rcases hc _ ih _ (hU _) with h | h
    · exact absurd hadj h
    · exact h

/-- Reachability decided by `fuel` steps of the closure from `u` when the result is closed, and
by the general procedure otherwise. -/
private def GlobalGoodRows_decReach [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : List V) (hU : ∀ v, v ∈ U) (fuel : ℕ) (u v : V) : Decidable (G.Reachable u v) :=
  if hc : GlobalGoodRows_closedB (fun a b => decide (G.Adj a b)) U
      (GlobalGoodRows_iter (fun a b => decide (G.Adj a b)) U fuel [u]) = true then
    if hv : v ∈ GlobalGoodRows_iter (fun a b => decide (G.Adj a b)) U fuel [u] then
      isTrue (GlobalGoodRows_iter_sound G U u fuel [u] (by simp) v hv)
    else isFalse fun h => hv (GlobalGoodRows_closed G U _ hU hc
      (GlobalGoodRows_iter_mem _ _ fuel [u] u (by simp)) h)
  else SimpleGraph.instDecidableRelReachable G u v

end Reach

private theorem GlobalGoodRows_mem_allAtoms {k n : ℕ} (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

/-! ### Decision procedures -/

private instance GlobalGoodRows_decAdjDot {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.dotGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = v ∧ c.y = u))))

private instance GlobalGoodRows_decSameBlock {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.SameBlock :=
  fun u v => @GlobalGoodRows_decReach _ _ _ _ (GlobalGoodRows_decAdjDot Γ) (allAtoms k n)
    GlobalGoodRows_mem_allAtoms (k + n) u v

private instance GlobalGoodRows_decAdjMol {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.molGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = v ∧ c.y = u))))

private instance GlobalGoodRows_decSameMol {k n : ℕ} (Γ : Graph k n) : DecidableRel Γ.SameMol :=
  fun u v =>
    haveI : Decidable (Γ.molGraph.Reachable u v) :=
      @GlobalGoodRows_decReach _ _ _ _ (GlobalGoodRows_decAdjMol Γ) (allAtoms k n)
        GlobalGoodRows_mem_allAtoms (k + n) u v
    inferInstanceAs (Decidable (u = v ∨
      (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)))

private instance GlobalGoodRows_decUnpinned {k n : ℕ} (Γ : Graph k n) (u : Atom k n) :
    Decidable (Γ.Unpinned u) := by
  unfold Graph.Unpinned; infer_instance

private instance GlobalGoodRows_decIsRecollision {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin k)) :
    Decidable (Γ.IsRecollision B) :=
  inferInstanceAs (Decidable (∃ c ∈ Γ.comps, c.kind = .dot ∧
    ((∃ b ∈ B, c.x = Sum.inl b) ∧ c.y.isRight = true ∨
      (∃ b ∈ B, c.y = Sum.inl b) ∧ c.x.isRight = true)))

private instance GlobalGoodRows_decRgCheck {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.RgCheck := by
  unfold Graph.RgCheck; infer_instance

private instance GlobalGoodRows_decAdjEdge {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.edgeGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, c.x = u ∧ c.y = v) ∨ (∃ c ∈ Γ.comps, c.x = v ∧ c.y = u))))

private instance GlobalGoodRows_decAdjWavedTheta {k n : ℕ} (Γ : Graph k n) :
    DecidableRel Γ.wavedThetaGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧
    ((∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = u ∧ c.y = v) ∨
      (∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧
        c.x = v ∧ c.y = u))))

private instance GlobalGoodRows_decRegular {k n : ℕ} (C : ℕ) (Γ : Graph k n) :
    Decidable (Γ.Regular C) :=
  haveI : DecidableRel Γ.edgeGraph.Reachable :=
    @GlobalGoodRows_decReach _ _ _ _ (GlobalGoodRows_decAdjEdge Γ) (allAtoms k n)
      GlobalGoodRows_mem_allAtoms (k + n)
  haveI : DecidableRel Γ.wavedThetaGraph.Reachable :=
    @GlobalGoodRows_decReach _ _ _ _ (GlobalGoodRows_decAdjWavedTheta Γ) (allAtoms k n)
      GlobalGoodRows_mem_allAtoms (k + n)
  haveI : Decidable Γ.edgeGraph.Preconnected :=
    inferInstanceAs (Decidable (∀ u v, Γ.edgeGraph.Reachable u v))
  decidable_of_iff (k + n + Γ.comps.length ≤ C ∧ Γ.edgeGraph.Preconnected ∧
      (∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (.inr a) (.inr b)) ∧
      ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true)
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

private instance GlobalGoodRows_decNormal {k n : ℕ} (C : ℕ) (Γ : Graph k n) :
    Decidable (Γ.Normal C) :=
  inferInstanceAs (Decidable (Γ.Regular C ∧
    (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧
    ∀ u v : Atom k n, u ≠ v →
      ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
        (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))))

section MGraphs

variable {X Z : Type}

end MGraphs

section Host

end Host

section Rows34

end Rows34

end RBM8D.Graphs
