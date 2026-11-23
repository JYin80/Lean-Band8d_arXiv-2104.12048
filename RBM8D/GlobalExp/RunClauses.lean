module

public import RBM8D.GlobalExp.Strategy
public import Batteries.Tactic.OpenPrivate
public import RBM8D.GlobalExp.Local
public import RBM8D.Graph.Local.DotNorm
public import RBM8D.Graph.Local.StrategyPart1
public import RBM8D.Graph.MolDot
import all RBM8D.GlobalExp.Local
import all RBM8D.Graph.Local.DotNorm
import all RBM8D.Graph.Local.StrategyPart1
import all RBM8D.Graph.MolDot
import all RBM8D.GlobalExp.Strategy

@[expose] public section

/-!
# The clauses of the invariant of a run

The clause on the external atoms kept by the elementary steps of the local expansions and by the
substitution of Steps 2–3 of [II, Strategy 6.6], and the charge pattern, the absence of ghost
edges, the internal label atoms and the clause on `⊗` kept by the local expansions, `O_dot`, the
substitution and the reordering of internal atoms.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

open private Local_atom_cases Local_CC Local_CC_int Local_colour_iff Local_countP_f2
  Local_countP_filterMap Local_Dec Local_DecT Local_diff_notRandom Local_f2_left Local_f2_right
  Local_flat_block Local_flat_unpinned Local_flat_isRight Local_isRandom_kinds Local_lift_flat
  Local_lift_isRight Local_lift_ne_new Local_lift_sameBlock Local_lift_unpinned Local_LiftOK
  Local_mem_liftCs Local_merge_comps Local_merge_f_inl Local_merge_flat_inl
  Local_merge_flat_isRight Local_merge_inl_iff Local_merge_mem Local_merge_sameBlock
  Local_merge_unpinned Local_mergeComp Local_mergeComp_some Local_mergeT_spec Local_MovR
  Local_movR_random Local_mrep Local_mrep_iff Local_new_block Local_NewOK Local_PathOK
  Local_pathOK_random Local_solid_kinds Local_strip Local_stripC Local_toWeight_solid
  Local_dec_liftOK Local_same3_clauses Local_strip_same3 Local_Same3 Local_tri Local_same3_fun
  Local_kept Local_added Local_addedX Local_xonly Local_dotChoice_comps Local_added_perm
  Local_sp_mem Local_sp_anch Local_anch Local_anch_of_not_unpinned Local_not_unpinned_of_anch
  Local_Same3X Local_nx Local_dropX Local_same3X_dropX Local_same3X_fun Local_colour_dropX
  Local_ext_dropX Local_addG Local_addDs Local_addDs_comps Local_dotrev Local_anch_add
  Local_MergeSpec Local_merge_f_int Local_merge_comps Local_flat_isRight Local_flat_unpinned
  Local_dec_liftOK Local_strip_same3 Local_DecT Local_diff_notRandom Local_solidC_xy
  Local_GM Local_strip_labelFree Local_mem_eraseIdxs Local_eraseIdxs2_perm Local_kind_solidC
  Local_fromRel_congr Local_dot_fun Local_countP_le2 Local_same3_all Local_tri
  Local_splitRegular_dec Local_liftA_zero Local_liftCs_zero Local_comp_proj_zero Local_rd
  Local_SameR Local_oW2_decT Local_decT_conj Local_conj_conj_comps Local_conj_labelFree
  Local_good_at Local_multiEHat_decT Local_ggPos_res Local_conj_out Local_GM_conj
  Local_sw_sw_comps Local_sw_labelFree Local_sw_out Local_decT_sw Local_GM_sw
  Local_localOp_good Local_Inv Local_Good Local_LabAt
  Local_molRep_eq_iff Local_molRep_spec Local_dot_le_mol Local_molRep_idem Local_anchor_none
  Local_anchor_some Local_rho Local_rho_vtx Local_pin Local_edMap Local_ELG_mapV Local_rdL_vok
  Local_pin_vok Local_RG_same Local_RG_perm Local_RG Local_carry_trans Local_carry_toRG
  Local_carry_ofRG Local_Same Local_Same.refl Local_Carry Local_ELG
  Local_mergeT_none Local_mergeT_spec Local_MergeSpec Local_mrep Local_mrep_iff
  Local_mergeComp
  from RBM8D.GlobalExp.Local
open private DotNorm.sameBlock_of_mem from RBM8D.Graph.Local.DotNorm
open private mem_or_of_mem from RBM8D.Graph.Local.StrategyPart1
open private MolDot_add MolDot_colour_add MolDot_ext_add from RBM8D.Graph.MolDot

/-! ## `O_dot` on graphs with the charge pattern of the block normal form -/

section ODot

variable {n : ℕ}


/-- The dotted edges of a list of pairs, each with an atom in a block with an internal atom, added
one at a time, keep the charge pattern of the block normal form and the clause on the external
atoms. -/
private theorem RunClauses_addDs : ∀ (L : List (Atom 3 n × Atom 3 n × Bool)) (Γ : Graph 3 n),
    Γ.ColourInvB → Γ.ExtClause → (∀ p ∈ L, Local_anch Γ p.1 ∨ Local_anch Γ p.2.1) →
    (Local_addDs Γ L).ColourInvB ∧ (Local_addDs Γ L).ExtClause
  | [], Γ, hC, hE, _ => ⟨hC, hE⟩
  | p :: L, Γ, hC, hE, hL => by
    have h1 : (Local_addG Γ p.1 p.2.1).ColourInvB ∧ (Local_addG Γ p.1 p.2.1).ExtClause := by
      rcases hL p List.mem_cons_self with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact ⟨MolDot_colour_add hC, MolDot_ext_add hE hb⟩
      · obtain ⟨-, c2, c3, -, -⟩ := Local_dotrev Γ p.1 p.2.1
        exact ⟨c2 (MolDot_colour_add hC), c3 (MolDot_ext_add hE hb)⟩
    have hL' : ∀ p' ∈ L, Local_anch (Local_addG Γ p.1 p.2.1) p'.1 ∨
        Local_anch (Local_addG Γ p.1 p.2.1) p'.2.1 := by
      intro p' hp'
      rcases hL p' (List.mem_cons_of_mem _ hp') with h | h
      · exact Or.inl (Local_anch_add h)
      · exact Or.inr (Local_anch_add h)
    exact RunClauses_addDs L _ h1.1 h1.2 hL'

/-- The clauses of the graph of `Graph.mergeT` from those of `G`. -/
private theorem RunClauses_merge_CE {G : Graph 3 n} {t : Tracked 3 n} (h : G.mergeT = some t)
    (hC : G.ColourInvB) (hE : G.ExtClause) :
    t.g.ColourInvB ∧ t.g.ExtClause := by
  obtain ⟨-, -, -, -, hsurj, ⟨g, hg, hgs⟩, -, -, -⟩ := Local_mergeT_spec h
  have hCC := (Local_colour_iff G).1 hC
  have flatR := Local_merge_flat_isRight h
  have flatL := Local_merge_flat_inl h
  have inlI := Local_merge_inl_iff h
  have unp := Local_merge_unpinned h
  -- every component of the graph of `Graph.mergeT`
  have mem : ∀ c' ∈ t.g.comps, ∃ c ∈ G.comps, (c.kind.isSolid = true ∧
      Local_mrep G c.x = Local_mrep G c.y ∧
      c' = { (c.map t.f) with kind := c.kind.toWeight, y := t.f c.x }) ∨ c' = c.map t.f := by
    intro c' hc'
    obtain ⟨c, hc, hm⟩ := Local_merge_mem h hc'
    rcases Local_mergeComp_some hm with h1 | ⟨h1, -, -⟩
    · exact ⟨c, hc, Or.inl h1⟩
    · exact ⟨c, hc, Or.inr h1⟩
  have memk : ∀ c ∈ G.comps, c.kind.isSolid = false → c.kind ≠ .dot →
      c.map t.f ∈ t.g.comps := by
    intro c hc hs' hd
    rw [Local_merge_comps h]
    refine List.mem_filterMap.2 ⟨c, hc, ?_⟩
    unfold Local_mergeComp
    rw [if_neg (by simp [hd]), if_neg (by simp [hs'])]
  -- the charge pattern
  have hColour : t.g.ColourInvB := by
    refine (Local_colour_iff t.g).2 fun c' hc' => ?_
    obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
    · obtain ⟨-, -, hr, -, -, -, -, -⟩ := Local_toWeight_solid hsol
      have hcr : c.kind.isRandom = true := (Local_solid_kinds hsol).2.2.1
      have a1 := ((hCC c hc).1 hcr).1
      have e : (t.g.flatAtom (t.f c.x)).isRight = true := by rw [flatR]; exact a1
      refine ⟨fun _ => ⟨e, ?_, ?_, ?_⟩, fun hw => ?_⟩
      · intro he; rw [he] at e; simp at e
      · intro he; rw [he] at e; simp at e
      · intro he; rw [he] at e; simp at e
      · exfalso
        have : c.kind.toWeight.isRandom = true := hr
        simp only at hw
        rw [hw] at this
        simp [Kind.isRandom] at this
    · obtain ⟨b1, b2⟩ := hCC c hc
      refine ⟨fun hr => ?_, fun hw => ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := b1 hr
        refine ⟨?_, ?_, ?_, ?_⟩
        · change (t.g.flatAtom (t.f c.x)).isRight = true
          rw [flatR]; exact a1
        · change t.g.flatAtom (t.f c.y) ≠ _
          rw [Ne, flatL]; exact a2
        · change t.g.flatAtom (t.f c.y) = _ → _
          rw [flatL]; exact a3
        · change t.g.flatAtom (t.f c.y) = _ → _
          rw [flatL]; exact a4
      · obtain ⟨a1, a2⟩ := b2 hw
        exact ⟨by change (t.g.flatAtom (t.f c.x)).isRight = true; rw [flatR]; exact a1,
          by change (t.g.flatAtom (t.f c.y)).isRight = true; rw [flatR]; exact a2⟩
  -- the clause on the external atoms
  obtain ⟨E1, E2, E3, E4, E5⟩ := hE
  have diffm : ∀ c' ∈ t.g.comps, c'.kind.isDiffusive = true → ∃ c ∈ G.comps, c' = c.map t.f := by
    intro c' hc' hd
    obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
    · exact absurd hd (by rw [(Local_toWeight_solid hsol).2.2.2.2.2.2.1]; simp)
    · exact ⟨c, hc, rfl⟩
  have hns : ∀ κ : Kind, κ.isDiffusive = true → κ.isSolid = false ∧ κ ≠ .dot := by
    intro κ h
    cases κ <;> simp [Kind.isDiffusive, Kind.isSolid] at h ⊢
  have hdp : ∀ a : Fin 3, G.HasDiffToPinned (.inl a) → t.g.HasDiffToPinned (.inl a) := by
    rintro a ⟨c, hc, hd, hor⟩
    refine ⟨c.map t.f, memk c hc (hns _ hd).1 (hns _ hd).2, hd, ?_⟩
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [Comp.map, h1, Local_merge_f_inl h], by
        change ¬ t.g.Unpinned (t.f c.y); rw [unp]; exact h2⟩
    · exact Or.inr ⟨by simp [Comp.map, h1, Local_merge_f_inl h], by
        change ¬ t.g.Unpinned (t.f c.x); rw [unp]; exact h2⟩
  have hdt : ∀ a : Fin 3, G.DiffToPinned (.inl a) → t.g.DiffToPinned (.inl a) := by
    intro a hdt c' hc' hd
    obtain ⟨c, hc, rfl⟩ := diffm c' hc' hd
    obtain ⟨h1, h2⟩ := hdt c hc hd
    refine ⟨fun hx => ?_, fun hy => ?_⟩
    · change ¬ t.g.Unpinned (t.f c.y)
      rw [unp]
      exact h1 ((inlI c.x a).1 hx)
    · change ¬ t.g.Unpinned (t.f c.x)
      rw [unp]
      exact h2 ((inlI c.y a).1 hy)
  have deg_le : ∀ a : Fin 3, t.g.nonDotDeg (.inl a) ≤ G.nonDotDeg (.inl a) := by
    intro a
    unfold Graph.nonDotDeg
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, Local_merge_comps h]
    refine Local_countP_filterMap _ _ _ _ fun c hc c' hm hq => ?_
    simp only [decide_eq_true_eq] at hq ⊢
    rcases Local_mergeComp_some hm with ⟨hsol, -, rfl⟩ | ⟨rfl, -, -⟩
    · obtain ⟨hdot, -, -, -, hxd, -⟩ := Local_toWeight_solid hsol
      have hk : c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
        ⟨(Local_solid_kinds hsol).1, (Local_solid_kinds hsol).2.1⟩
      refine ⟨?_, hk⟩
      simp only at hq
      rcases hq.1 with h' | h' <;> exact Or.inl ((inlI c.x a).1 h')
    · simp only [Comp.map] at hq
      refine ⟨?_, hq.2⟩
      rcases hq.1 with h' | h'
      · exact Or.inl ((inlI c.x a).1 h')
      · exact Or.inr ((inlI c.y a).1 h')
  have unpE : ∀ a : Fin 3, t.g.Unpinned (.inl a) ↔ G.Unpinned (.inl a) := fun a => by
    rw [← Local_merge_f_inl h a]
    exact unp _
  have hExt : t.g.ExtClause := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u' v' hne hb
      obtain ⟨u, rfl⟩ := hsurj u'
      obtain ⟨v, rfl⟩ := hsurj v'
      have huv : u ≠ v := fun e => hne (by rw [e])
      obtain ⟨b, hb'⟩ := E1 u v huv ((Local_merge_sameBlock h u v).1 hb)
      exact ⟨g b, by rw [← hg]; exact (Local_merge_sameBlock h u (.inr b)).2 hb'⟩
    · intro c' hc' hk
      obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
      · exact absurd hk (Local_toWeight_solid hsol).2.2.2.2.1
      · rintro ⟨h1, h2⟩
        exact E2 c hc hk ⟨(unp c.x).1 h1, (unp c.y).1 h2⟩
    · intro hU
      obtain ⟨a1, a2⟩ := E3 ((unpE 0).1 hU)
      exact ⟨hdp 0 a1, hdt 0 a2⟩
    · intro hU
      obtain ⟨a1, a2⟩ := E4 ((unpE 2).1 hU)
      refine ⟨fun c' hc' hd => ?_, le_trans (deg_le 2) a2⟩
      obtain ⟨c, hc, rfl⟩ := diffm c' hc' hd
      obtain ⟨b1, b2⟩ := a1 c hc hd
      exact ⟨fun h' => b1 ((inlI _ _).1 h'), fun h' => b2 ((inlI _ _).1 h')⟩
    · intro hU
      have hU' := (unpE 1).1 hU
      obtain ⟨a1, a2, a3⟩ := E5 hU'
      refine ⟨?_, hdt 1 a2, le_trans (deg_le 1) a3⟩
      rcases a1 with ⟨c, hc, hk, hor⟩ | h'
      · left
        have hcr : c.kind.isRandom = true := by rw [hk]; rfl
        have hcx : (G.flatAtom c.x).isRight = true := ((hCC c hc).1 hcr).1
        have hx1 : c.x ≠ .inl 1 := by
          intro hx
          rw [hx, Local_flat_unpinned hU'] at hcx
          simp at hcx
        have hy1 : c.y = .inl 1 := hor.resolve_left hx1
        have hrep : Local_mrep G c.x ≠ Local_mrep G c.y := by
          intro he
          have hsb := (Local_mrep_iff G _ _).1 he
          rw [hy1] at hsb
          obtain ⟨b, hb⟩ : ∃ b, G.flatAtom c.x = .inr b := by
            rcases hf : G.flatAtom c.x with a | b
            · rw [hf] at hcx; simp at hcx
            · exact ⟨b, rfl⟩
          have hfb : G.SameBlock c.x (.inr b) := hb ▸ Local_flat_block G c.x
          exact hU'.2 b (hsb.symm.trans hfb)
        have hm : Local_mergeComp (Local_mrep G) t.f c = some (c.map t.f) := by
          unfold Local_mergeComp
          rw [if_neg (by simp [hk]), if_neg (by simp [hrep])]
        refine ⟨c.map t.f, ?_, hk, Or.inr ?_⟩
        · rw [Local_merge_comps h]
          exact List.mem_filterMap.2 ⟨c, hc, hm⟩
        · simp [Comp.map, hy1, Local_merge_f_inl h]
      · exact Or.inr (hdp 1 h')
  exact ⟨hColour, hExt⟩

/-- `Graph.TensorDiffusive`, component by component. -/
private theorem RunClauses_td_iff (Γ : Graph 3 n) : Γ.TensorDiffusive ↔
    ∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true := by
  unfold Graph.TensorDiffusive
  rw [List.all_eq_true]
  refine forall₂_congr fun c _ => ?_
  by_cases h1 : c.x = .inl 0 <;> by_cases h2 : c.y = .inl 0 <;> simp [h1, h2]

/-- The components of `Graph.dotChoice` at `⊗` are components of the graph, when only diffusive
edges are at `⊗`. -/
private theorem RunClauses_dc_td {Γ : Graph 3 n} (hT : Γ.TensorDiffusive)
    (A : List (Atom 3 n × Atom 3 n × Bool)) :
    (Γ.dotChoice Γ.splitPairs A).TensorDiffusive := by
  rw [RunClauses_td_iff] at hT ⊢
  intro c hc h0
  rw [Local_dotChoice_comps] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hT c (List.mem_filter.1 hc).1 h0
  · exfalso
    unfold Local_added at hc
    obtain ⟨p, hp, hpc⟩ := List.mem_filterMap.1 hc
    have hpe : c.x = p.1 ∧ c.y = p.2.1 := by
      split_ifs at hpc <;> obtain rfl := Option.some.inj hpc <;> exact ⟨rfl, rfl⟩
    obtain ⟨hs1, hs2⟩ := Local_sp_mem hp
    obtain ⟨d, hd, hk, hde⟩ : ∃ d ∈ Γ.comps, d.kind.isDiffusive = false ∧
        (d.x = p.1 ∧ d.y = p.2.1 ∨ d.x = p.2.1 ∧ d.y = p.1) := by
      cases hb : p.2.2
      · obtain ⟨d, hd, hk, he⟩ := hs2 hb
        exact ⟨d, hd, by rw [hk]; rfl, he⟩
      · obtain ⟨d, hd, hk, he⟩ := hs1 hb
        refine ⟨d, hd, ?_, he⟩
        cases h : d.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
    have : d.x = .inl 0 ∨ d.y = .inl 0 := by
      rw [hpe.1, hpe.2] at h0
      rcases hde with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> tauto
    rw [hT d hd this] at hk
    cases hk

/-- `O_dot` keeps `Graph.TensorDiffusive`. -/
private theorem RunClauses_oDot_td {Γ : Graph 3 n} (hT : Γ.TensorDiffusive) :
    ∀ t ∈ oDotT Γ, t.g.TensorDiffusive := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact hT
  have hD := (RunClauses_td_iff _).1 (RunClauses_dc_td hT A)
  rw [RunClauses_td_iff]
  intro c' hc' h0
  obtain ⟨c, hc, hmc⟩ := Local_merge_mem hm hc'
  rcases Local_mergeComp_some hmc with ⟨hs, -, rfl⟩ | ⟨rfl, -, -⟩
  · exfalso
    have hx : t.f c.x = .inl 0 := by simpa [Comp.map] using h0
    have := hD c hc (Or.inl ((Local_merge_inl_iff hm c.x 0).1 hx))
    cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
  · simp only [Comp.map] at h0 ⊢
    refine hD c hc ?_
    rcases h0 with h0 | h0
    · exact Or.inl ((Local_merge_inl_iff hm c.x 0).1 h0)
    · exact Or.inr ((Local_merge_inl_iff hm c.y 0).1 h0)

/-- `O_dot` keeps the charge pattern of the block normal form and the clause on the external
atoms. -/
private theorem RunClauses_oDot_CE {Γ : Graph 3 n} (hC : Γ.ColourInvB) (hE : Γ.ExtClause) :
    ∀ t ∈ oDotT Γ, t.g.ColourInvB ∧ t.g.ExtClause := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact ⟨hC, hE⟩
  set SP := Γ.splitPairs with hSP
  set Γ₂ : Graph 3 n := ⟨Local_kept Γ SP ++ Local_addedX SP A, Γ.coeff⟩ with hΓ₂
  have hX2 : ∀ c ∈ Local_addedX SP A, c.kind = .xdot ∧ ∃ p ∈ SP, p.2.2 = true ∧
      c.x = p.1 ∧ c.y = p.2.1 := by
    intro c hc
    unfold Local_addedX at hc
    obtain ⟨p, hp, hpc⟩ := List.mem_filterMap.1 hc
    split_ifs at hpc with ha hb
    obtain rfl := Option.some.inj hpc
    exact ⟨rfl, p, hp, hb, rfl, rfl⟩
  have h3X : Local_Same3X Γ Γ₂ := by
    unfold Local_Same3X
    have e : Γ₂.comps.filter Local_nx = Γ.comps.filter Local_nx := by
      simp only [hΓ₂, List.filter_append, Local_kept, List.filter_filter]
      have e2 : (Local_addedX SP A).filter Local_nx = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        simp [Local_nx, (hX2 c hc).1]
      rw [e2, List.append_nil]
      congr 1
      funext c
      by_cases hk : c.kind = .xdot <;> simp [Local_nx, hk]
    rw [e]
  have hXok : ∀ c ∈ Γ₂.comps, c.kind = .xdot → ¬ (Γ.Unpinned c.x ∧ Γ.Unpinned c.y) := by
    intro c hc hk
    rcases List.mem_append.1 hc with hc | hc
    · exact hE.2.1 c (List.mem_filter.1 hc).1 hk
    · obtain ⟨-, p, hp, -, hx', hy'⟩ := hX2 c hc
      rw [hx', hy']
      rcases Local_sp_anch hC hE hp with h | h
      · exact fun ⟨a, _⟩ => Local_not_unpinned_of_anch h a
      · exact fun ⟨_, b⟩ => Local_not_unpinned_of_anch h b
  have hfun := Local_same3X_fun h3X
  have e := Local_same3_clauses (Local_same3X_dropX h3X)
  have hC2 : Γ₂.ColourInvB := by
    rw [Local_colour_dropX] at hC ⊢
    exact e.1.2 hC
  have hE2 : Γ₂.ExtClause := by
    rw [Local_ext_dropX] at hE ⊢
    refine ⟨e.2.1.2 hE.1, fun c hc hk => ?_⟩
    rw [hfun.2.2.2.2.2]
    exact hXok c hc hk
  set LA := SP.filter fun p => decide (p ∈ A) with hLA
  have hLA : ∀ p ∈ LA, Local_anch Γ₂ p.1 ∨ Local_anch Γ₂ p.2.1 := by
    intro p hp
    have hp' := (List.mem_filter.1 hp).1
    unfold Local_anch
    rw [hfun.1]
    exact Local_sp_anch hC hE hp'
  obtain ⟨hC3, hE3⟩ := RunClauses_addDs LA Γ₂ hC2 hE2 hLA
  have h3 : Local_Same3 (Local_addDs Γ₂ LA) (Γ.dotChoice SP A) := by
    unfold Local_Same3
    rw [Local_dotChoice_comps, (Local_addDs_comps Γ₂ LA).1]
    refine List.Perm.map _ ?_
    simp only [hΓ₂, List.append_assoc]
    exact List.Perm.append_left _ (Local_added_perm SP A)
  have e3 := Local_same3_clauses h3
  exact RunClauses_merge_CE hm (e3.1.2 hC3) (e3.2.1.2 hE3)

/-- `O_dot` maps internal atoms to internal atoms. -/
private theorem RunClauses_oDot_int {Γ : Graph 3 n} {u : Atom 3 n} (hu : u.isRight = true) :
    ∀ t ∈ oDotT Γ, (t.f u).isRight = true := by
  intro t ht
  rcases mem_oDotT_cases ht with rfl | ⟨A, -, hm⟩
  · exact hu
  · rw [Local_merge_f_int hm]
    exact hu

/-- The label of a term of `Graph.mergeT` is the image of the label of its component. -/
private theorem RunClauses_mergeComp_label {k n m : ℕ} {rep : Atom k n → Atom k n}
    {f : Atom k n → Atom k m} {c : Comp (Atom k n)} {c' : Comp (Atom k m)}
    (h : Local_mergeComp rep f c = some c') :
    c'.label = c.label.map (Prod.map id f) ∧ (c'.kind.isRandom = true → c.kind.isRandom = true) := by
  rcases Local_mergeComp_some h with ⟨hs, -, rfl⟩ | ⟨rfl, -, -⟩
  · exact ⟨rfl, fun _ => (Local_solid_kinds hs).2.2.1⟩
  · exact ⟨rfl, id⟩

/-- `O_dot` keeps the `Q`-graphs without internal atom, with no internal atom in the output. -/
private theorem RunClauses_oDot_q (Γ : Graph 3 0) (hQ : Γ.IsQGraph) :
    ∀ t ∈ oDotT Γ, t.nOut = 0 ∧ t.g.IsQGraph := by
  intro t ht
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht with h1 h2
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨rfl, hQ⟩
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨rfl, hQ⟩
  obtain ⟨A, -, hm⟩ := List.mem_filterMap.1 ht
  have hnd : ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none := by
    intro c hc hk
    by_contra hne
    apply h1
    right
    rw [List.any_eq_true]
    refine ⟨c, hc, ?_⟩
    rcases hk with hk | hk <;> simp [hk, Option.isSome_iff_ne_none.2 hne]
  obtain ⟨-, -, hle, -, -, -, -, -, -⟩ := Local_mergeT_spec hm
  refine ⟨Nat.le_zero.1 hle, ?_⟩
  obtain ⟨u, ⟨c₀, hc₀, hl₀⟩, hall⟩ := hQ
  set D := Γ.dotChoice Γ.splitPairs A with hD
  have hmemD : ∀ c ∈ D.comps, c ∈ Γ.comps ∨ (c.label = none ∧ c.kind.isRandom = false) := by
    intro c hc
    rw [hD, Local_dotChoice_comps] at hc
    rcases List.mem_append.1 hc with hc | hc
    · exact Or.inl (List.mem_filter.1 hc).1
    · right
      unfold Local_added at hc
      obtain ⟨p, -, hpc⟩ := List.mem_filterMap.1 hc
      split_ifs at hpc <;> obtain rfl := Option.some.inj hpc <;> exact ⟨rfl, rfl⟩
  refine ⟨t.f u, ?_, fun c' hc' hrl => ?_⟩
  · have hk₀ : c₀.kind ≠ .dot ∧ c₀.kind ≠ .xdot := by
      refine ⟨fun hk => ?_, fun hk => ?_⟩ <;>
        simp [hnd c₀ hc₀ (by simp [hk])] at hl₀
    have hc₀D : c₀ ∈ D.comps := by
      rw [hD, Local_dotChoice_comps]
      refine List.mem_append_left _ (List.mem_filter.2 ⟨hc₀, ?_⟩)
      simp [hk₀.2]
    cases hmc : Local_mergeComp (Local_mrep D) t.f c₀ with
    | none =>
      exfalso
      unfold Local_mergeComp at hmc
      split_ifs at hmc with hh
      simp [hk₀.1] at hh
    | some c' =>
      refine ⟨c', ?_, ?_⟩
      · rw [Local_merge_comps hm]
        exact List.mem_filterMap.2 ⟨c₀, hc₀D, hmc⟩
      · rw [(RunClauses_mergeComp_label hmc).1, hl₀]
        rfl
  · obtain ⟨c, hc, hmc⟩ := Local_merge_mem hm hc'
    obtain ⟨hl, hr⟩ := RunClauses_mergeComp_label hmc
    rcases hmemD c hc with hc | ⟨hcl, hcr⟩
    · rw [hl, hall c hc ?_]
      · rfl
      · rcases hrl with h' | h'
        · exact Or.inl (hr h')
        · rw [hl] at h'
          exact Or.inr (by simpa using h')
    · exfalso
      rcases hrl with h' | h'
      · rw [hr h'] at hcr
        cases hcr
      · rw [hl, hcl] at h'
        simp at h'

end ODot

/-! ## The clauses read on the unpinned external atoms -/

section Unpinned

variable {n : ℕ}

private theorem RunClauses_dot_adj {k : ℕ} {Γ : Graph k n} {a b : Atom k n} :
    Γ.dotGraph.Adj a b ↔
      a ≠ b ∧ ∃ c ∈ Γ.comps, c.kind = .dot ∧ (c.x = a ∧ c.y = b ∨ c.x = b ∧ c.y = a) :=
  dg_adj (L := Γ.comps)

private theorem RunClauses_flat_isRight (Γ : Graph 3 n) (u : Atom 3 n) :
    (Γ.flatAtom u).isRight = true ↔ ¬ Γ.Unpinned u := by
  refine ⟨fun h hU => ?_, Local_flat_isRight⟩
  rw [Local_flat_unpinned hU] at h
  have := hU.1
  cases u <;> simp_all

private theorem RunClauses_flat_inl (Γ : Graph 3 n) (u : Atom 3 n) (a : Fin 3) :
    Γ.flatAtom u = .inl a ↔ u = .inl a ∧ Γ.Unpinned u := by
  by_cases hU : Γ.Unpinned u
  · rw [Local_flat_unpinned hU]
    exact ⟨fun h => ⟨h, hU⟩, fun h => h.1⟩
  · have := Local_flat_isRight hU
    refine ⟨fun h => ?_, fun h => absurd h.2 hU⟩
    rw [h] at this
    simp at this

/-- The charge pattern of a component read on a predicate `P` of the unpinned atoms. -/
private def RunClauses_CCU (P : Atom 3 n → Prop) (c : Comp (Atom 3 n)) : Prop :=
  (c.kind.isRandom = true → ¬ P c.x ∧ ¬ (c.y = .inl 0 ∧ P c.y) ∧
    (c.y = .inl 1 ∧ P c.y → c.kind = .G .plus) ∧ (c.y = .inl 2 ∧ P c.y → c.kind = .G .minus)) ∧
  (c.kind = .waved .s → ¬ P c.x ∧ ¬ P c.y)

private theorem RunClauses_CC_iff (Γ : Graph 3 n) (c : Comp (Atom 3 n)) :
    Local_CC Γ c ↔ RunClauses_CCU Γ.Unpinned c := by
  unfold Local_CC RunClauses_CCU
  simp only [RunClauses_flat_isRight, RunClauses_flat_inl, Ne]

private theorem RunClauses_colour_iff (Γ : Graph 3 n) :
    Γ.ColourInvB ↔ ∀ c ∈ Γ.comps, RunClauses_CCU Γ.Unpinned c := by
  rw [Local_colour_iff]
  exact forall₂_congr fun c _ => RunClauses_CC_iff Γ c

/-- `RunClauses_CCU` along a map of the atoms that keeps the external atoms and the predicate. -/
private theorem RunClauses_CCU_map {m : ℕ} {P : Atom 3 n → Prop} {P' : Atom 3 m → Prop}
    {f : Atom 3 n → Atom 3 m} (hP : ∀ u, P' (f u) ↔ P u)
    (hf : ∀ u (a : Fin 3), f u = .inl a ↔ u = .inl a) (c : Comp (Atom 3 n)) :
    RunClauses_CCU P' (c.map f) ↔ RunClauses_CCU P c := by
  unfold RunClauses_CCU
  simp only [Comp.map, hP, hf]

/-- `RunClauses_CCU` holds on a component between atoms where the predicate fails. -/
private theorem RunClauses_CCU_of {P : Atom 3 n → Prop} {c : Comp (Atom 3 n)} (hx : ¬ P c.x)
    (hy : ¬ P c.y) : RunClauses_CCU P c :=
  ⟨fun _ => ⟨hx, fun h => hy h.2, fun h => absurd h.2 hy, fun h => absurd h.2 hy⟩,
    fun _ => ⟨hx, hy⟩⟩

private theorem RunClauses_not_unpinned_int {k : ℕ} (Γ : Graph k n) {u : Atom k n}
    (hu : u.isRight = true) : ¬ Γ.Unpinned u := fun h => by
  have := h.1
  cases u <;> simp_all

end Unpinned

/-! ## The substitution of Steps 2–3 -/

section Glue

variable {m n' : ℕ} (H : Graph 3 m) (x y₁ y₂ : Atom 3 m) (𝒢 : Graph 3 n')

private theorem RunClauses_glueAtom_int (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) (v : Atom 3 n') : (glueAtom x y₁ y₂ v : Atom 3 (m + n')).isRight = true := by
  rcases v with i | j
  · fin_cases i
    · cases x with
      | inl a => simp at hx
      | inr a => rfl
    · cases y₁ with
      | inl a => simp at hy₁
      | inr a => rfl
    · cases y₂ with
      | inl a => simp at hy₂
      | inr a => rfl
  · rfl

private theorem RunClauses_liftA_inj : Function.Injective (liftA (k := 3) (n := m) n') := by
  intro u v h
  rcases u with a | a <;> rcases v with b | b <;> simp_all [liftA, Fin.castAdd]

private theorem RunClauses_liftA_inl (u : Atom 3 m) (a : Fin 3) :
    (liftA n' u : Atom 3 (m + n')) = .inl a ↔ u = .inl a := by
  rcases u with b | b <;> simp [liftA]

private theorem RunClauses_liftA_isRight (u : Atom 3 m) :
    (liftA n' u : Atom 3 (m + n')).isRight = u.isRight := by
  rcases u with b | b <;> rfl

variable {H x y₁ y₂ 𝒢}

/-- The components of the glued graph: those of `H` lifted, and those of `𝒢` between internal
atoms. -/
private theorem RunClauses_glue_mem (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) {c : Comp (Atom 3 (m + n'))} (hc : c ∈ (H.glue x y₁ y₂ 𝒢).comps) :
    (∃ d ∈ H.comps, c = d.map (liftA n')) ∨
      (∃ d ∈ 𝒢.comps, c = d.map (glueAtom x y₁ y₂)) ∧ c.x.isRight = true ∧ c.y.isRight = true := by
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact Or.inl ⟨d, hd, rfl⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact Or.inr ⟨⟨d, hd, rfl⟩, RunClauses_glueAtom_int x y₁ y₂ hx hy₁ hy₂ _,
      RunClauses_glueAtom_int x y₁ y₂ hx hy₁ hy₂ _⟩

private theorem RunClauses_glue_lift {d : Comp (Atom 3 m)} (hd : d ∈ H.comps) :
    d.map (liftA n') ∈ (H.glue x y₁ y₂ 𝒢).comps :=
  List.mem_append_left _ (List.mem_map.2 ⟨d, hd, rfl⟩)

private theorem RunClauses_glue_reach {u v : Atom 3 m} (h : H.SameBlock u v) :
    (H.glue x y₁ y₂ 𝒢).SameBlock (liftA n' u) (liftA n' v) := by
  let φ : H.dotGraph →g (H.glue x y₁ y₂ 𝒢).dotGraph :=
    ⟨liftA n', fun {a b} hab => by
      obtain ⟨hne, d, hd, hk, he⟩ := RunClauses_dot_adj.1 hab
      refine RunClauses_dot_adj.2 ⟨fun e => hne (RunClauses_liftA_inj e), _,
        RunClauses_glue_lift hd, hk, ?_⟩
      simp only [Comp.map]
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩⟩
  exact h.map φ

/-- A path of dotted edges of the glued graph from an external atom reaches an internal atom of
`H` through dotted edges of `H`, or stays in the atoms of `H`. -/
private theorem RunClauses_glue_walk (hx : x.isRight = true) (hy₁ : y₁.isRight = true)
    (hy₂ : y₂.isRight = true) {u v : Atom 3 (m + n')}
    (w : (H.glue x y₁ y₂ 𝒢).dotGraph.Walk u v) :
    ∀ a : Fin 3, u = .inl a → (∃ b, H.SameBlock (.inl a) (.inr b)) ∨
      ∃ v₀, v = liftA n' v₀ ∧ H.SameBlock (.inl a) v₀ := by
  induction w with
  | nil => exact fun a h => Or.inr ⟨.inl a, h, SimpleGraph.Reachable.refl _⟩
  | @cons u w v hadj p ih =>
    intro a hu
    subst hu
    obtain ⟨hne, c, hc, hk, he⟩ := RunClauses_dot_adj.1 hadj
    have hcl : c.x.isLeft = true ∨ c.y.isLeft = true := by
      rcases he with ⟨h, -⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
    rcases RunClauses_glue_mem hx hy₁ hy₂ hc with ⟨d, hd, rfl⟩ | ⟨-, h1, h2⟩
    · simp only [Comp.map] at he
      obtain ⟨w₀, hw, hadj₀⟩ : ∃ w₀, w = liftA n' w₀ ∧ H.SameBlock (.inl a) w₀ := by
        have hreach := DotNorm.sameBlock_of_mem hd hk
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have : d.x = .inl a := (RunClauses_liftA_inl _ _).1 h1
          exact ⟨d.y, h2.symm, this ▸ hreach⟩
        · have : d.y = .inl a := (RunClauses_liftA_inl _ _).1 h2
          exact ⟨d.x, h1.symm, this ▸ hreach.symm⟩
      subst hw
      rcases w₀ with a' | b
      · rcases ih a' rfl with ⟨b, hb⟩ | ⟨v₀, hv, hb⟩
        · exact Or.inl ⟨b, hadj₀.trans hb⟩
        · exact Or.inr ⟨v₀, hv, hadj₀.trans hb⟩
      · exact Or.inl ⟨b, hadj₀⟩
    · exfalso
      rcases hcl with h | h
      · revert h h1; cases c.x <;> simp
      · revert h h2; cases c.y <;> simp

variable (hx : x.isRight = true) (hy₁ : y₁.isRight = true) (hy₂ : y₂.isRight = true)
include hx hy₁ hy₂

private theorem RunClauses_glue_unpinned (u : Atom 3 m) :
    (H.glue x y₁ y₂ 𝒢).Unpinned (liftA n' u) ↔ H.Unpinned u := by
  rcases u with a | b
  · refine ⟨fun h => ⟨rfl, fun b hb => h.2 _ (RunClauses_glue_reach hb)⟩, fun h => ⟨rfl, ?_⟩⟩
    rintro b' ⟨w⟩
    rcases RunClauses_glue_walk hx hy₁ hy₂ w a rfl with ⟨b, hb⟩ | ⟨v₀, hv, hb⟩
    · exact h.2 b hb
    · rcases v₀ with a' | b
      · simp [liftA] at hv
      · exact h.2 b hb
  · exact ⟨fun h => absurd h.1 (by simp [liftA]), fun h => absurd h.1 (by simp)⟩

private theorem RunClauses_glue_colour :
    (H.glue x y₁ y₂ 𝒢).ColourInvB ↔ H.ColourInvB := by
  rw [RunClauses_colour_iff, RunClauses_colour_iff]
  have hU := RunClauses_glue_unpinned (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  constructor
  · intro h c hc
    exact (RunClauses_CCU_map hU (RunClauses_liftA_inl) c).1 (h _ (RunClauses_glue_lift hc))
  · intro h c hc
    rcases RunClauses_glue_mem hx hy₁ hy₂ hc with ⟨d, hd, rfl⟩ | ⟨-, h1, h2⟩
    · exact (RunClauses_CCU_map hU (RunClauses_liftA_inl) d).2 (h d hd)
    · exact RunClauses_CCU_of (RunClauses_not_unpinned_int _ h1)
        (RunClauses_not_unpinned_int _ h2)

private theorem RunClauses_glue_atExt {c : Comp (Atom 3 (m + n'))}
    (hc : c ∈ (H.glue x y₁ y₂ 𝒢).comps) (h : c.x.isLeft = true ∨ c.y.isLeft = true) :
    ∃ d ∈ H.comps, c = d.map (liftA n') := by
  rcases RunClauses_glue_mem hx hy₁ hy₂ hc with h' | ⟨-, h1, h2⟩
  · exact h'
  · exfalso
    rcases h with h | h
    · revert h h1; cases c.x <;> simp
    · revert h h2; cases c.y <;> simp

private theorem RunClauses_glue_ex (P : Kind → Prop) (a : Fin 3) :
    (∃ c ∈ (H.glue x y₁ y₂ 𝒢).comps, P c.kind ∧ (c.x = .inl a ∨ c.y = .inl a)) ↔
      ∃ c ∈ H.comps, P c.kind ∧ (c.x = .inl a ∨ c.y = .inl a) := by
  constructor
  · rintro ⟨c, hc, hk, hat⟩
    obtain ⟨d, hd, rfl⟩ := RunClauses_glue_atExt hx hy₁ hy₂ hc
      (by rcases hat with h | h <;> rw [h] <;> simp)
    simp only [Comp.map, RunClauses_liftA_inl] at hk hat
    exact ⟨d, hd, hk, hat⟩
  · rintro ⟨d, hd, hk, hat⟩
    refine ⟨_, RunClauses_glue_lift hd, hk, ?_⟩
    simp only [Comp.map, RunClauses_liftA_inl]
    exact hat

private theorem RunClauses_glue_hasDiff (a : Fin 3) :
    (H.glue x y₁ y₂ 𝒢).HasDiffToPinned (.inl a) ↔ H.HasDiffToPinned (.inl a) := by
  have hU := RunClauses_glue_unpinned (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  constructor
  · rintro ⟨c, hc, hd, hor⟩
    obtain ⟨d, hd', rfl⟩ := RunClauses_glue_atExt hx hy₁ hy₂ hc
      (by rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp)
    simp only [Comp.map, RunClauses_liftA_inl, hU] at hd hor
    exact ⟨d, hd', hd, hor⟩
  · rintro ⟨d, hd, hk, hor⟩
    refine ⟨_, RunClauses_glue_lift hd, hk, ?_⟩
    simp only [Comp.map, RunClauses_liftA_inl, hU]
    exact hor

private theorem RunClauses_glue_diffTo (a : Fin 3) :
    (H.glue x y₁ y₂ 𝒢).DiffToPinned (.inl a) ↔ H.DiffToPinned (.inl a) := by
  have hU := RunClauses_glue_unpinned (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  constructor
  · intro h d hd hk
    have := h _ (RunClauses_glue_lift hd) hk
    simp only [Comp.map, RunClauses_liftA_inl, hU] at this
    exact this
  · intro h c hc hk
    by_cases hat : c.x.isLeft = true ∨ c.y.isLeft = true
    · obtain ⟨d, hd, rfl⟩ := RunClauses_glue_atExt hx hy₁ hy₂ hc hat
      simp only [Comp.map, RunClauses_liftA_inl, hU]
      exact h d hd hk
    · refine ⟨fun e => absurd (Or.inl (by rw [e]; rfl)) hat,
        fun e => absurd (Or.inr (by rw [e]; rfl)) hat⟩

private theorem RunClauses_glue_all (P : Kind → Prop) (a : Fin 3) :
    (∀ c ∈ (H.glue x y₁ y₂ 𝒢).comps, P c.kind → c.x ≠ .inl a ∧ c.y ≠ .inl a) ↔
      ∀ c ∈ H.comps, P c.kind → c.x ≠ .inl a ∧ c.y ≠ .inl a := by
  have e := RunClauses_glue_ex (H := H) (𝒢 := 𝒢) hx hy₁ hy₂ P a
  constructor
  · intro h c hc hk
    by_contra hn
    rw [← not_or, not_not] at hn
    obtain ⟨c', hc', hk', hat⟩ := e.2 ⟨c, hc, hk, hn⟩
    exact (not_or.2 (h c' hc' hk')) (by simpa using hat)
  · intro h c hc hk
    by_contra hn
    rw [← not_or, not_not] at hn
    obtain ⟨c', hc', hk', hat⟩ := e.1 ⟨c, hc, hk, hn⟩
    exact (not_or.2 (h c' hc' hk')) (by simpa using hat)

private theorem RunClauses_glue_deg (a : Fin 3) :
    (H.glue x y₁ y₂ 𝒢).nonDotDeg (.inl a) = H.nonDotDeg (.inl a) := by
  unfold Graph.nonDotDeg
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  change (liftCs n' H.comps ++ _).countP _ = _
  rw [List.countP_append, liftCs, List.countP_map]
  have e2 : (𝒢.comps.map (Comp.map (glueAtom x y₁ y₂))).countP (fun c : Comp (Atom 3 (m + n')) =>
      decide ((c.x = .inl a ∨ c.y = .inl a) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)) = 0 := by
    rw [List.countP_eq_zero]
    intro c hc
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
    have h1 := RunClauses_glueAtom_int x y₁ y₂ hx hy₁ hy₂ d.x
    have h2 := RunClauses_glueAtom_int x y₁ y₂ hx hy₁ hy₂ d.y
    intro h'
    obtain ⟨hat, -⟩ := of_decide_eq_true h'
    simp only [Comp.map] at hat
    rcases hat with h | h
    · rw [h] at h1; simp at h1
    · rw [h] at h2; simp at h2
  rw [e2, add_zero]
  refine List.countP_congr fun d _ => ?_
  simp only [Function.comp_apply, Comp.map, RunClauses_liftA_inl]

private theorem RunClauses_glue_ext : (H.glue x y₁ y₂ 𝒢).ExtClause ↔ H.ExtClause := by
  have hU := RunClauses_glue_unpinned (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  have hU0 : ∀ a : Fin 3, (H.glue x y₁ y₂ 𝒢).Unpinned (.inl a) ↔ H.Unpinned (.inl a) :=
    fun a => hU (.inl a)
  have hhas := RunClauses_glue_hasDiff (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  have hdt := RunClauses_glue_diffTo (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  have hall := RunClauses_glue_all (H := H) (𝒢 := 𝒢) hx hy₁ hy₂ (fun κ => κ.isDiffusive = true)
  have hex := RunClauses_glue_ex (H := H) (𝒢 := 𝒢) hx hy₁ hy₂ (fun κ => κ = .G .plus)
  have hdeg := RunClauses_glue_deg (H := H) (𝒢 := 𝒢) hx hy₁ hy₂
  unfold Graph.ExtClause
  simp only [hU0, hhas, hdt, hall, hex, hdeg]
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · constructor
    · intro h u v hne hb
      obtain ⟨b', hb'⟩ := h _ _ (fun e => hne (RunClauses_liftA_inj e)) (RunClauses_glue_reach hb)
      rcases u with a | b
      · obtain ⟨w⟩ := hb'
        rcases RunClauses_glue_walk hx hy₁ hy₂ w a rfl with ⟨b, hb⟩ | ⟨v₀, hv, hb⟩
        · exact ⟨b, hb⟩
        · rcases v₀ with a' | b
          · simp [liftA] at hv
          · exact ⟨b, hb⟩
      · exact ⟨b, SimpleGraph.Reachable.refl _⟩
    · intro h u v hne hb
      rcases u with a | b
      · obtain ⟨w⟩ := hb
        rcases RunClauses_glue_walk hx hy₁ hy₂ w a rfl with ⟨b, hb⟩ | ⟨v₀, rfl, hb⟩
        · exact ⟨Fin.castAdd n' b, RunClauses_glue_reach hb⟩
        · obtain ⟨b, hb'⟩ := h (.inl a) v₀ (fun e => hne (by rw [← e]; rfl)) hb
          exact ⟨Fin.castAdd n' b, RunClauses_glue_reach hb'⟩
      · exact ⟨b, SimpleGraph.Reachable.refl _⟩
  · constructor
    · intro h d hd hk
      have := h _ (RunClauses_glue_lift hd) hk
      simp only [Comp.map, hU] at this
      exact this
    · intro h c hc hk
      rcases RunClauses_glue_mem hx hy₁ hy₂ hc with ⟨d, hd, rfl⟩ | ⟨-, h1, -⟩
      · simp only [Comp.map, hU]
        exact h d hd hk
      · exact fun hh => RunClauses_not_unpinned_int _ h1 hh.1

private theorem RunClauses_glue_noGhost :
    (H.glue x y₁ y₂ 𝒢).NoGhost ↔ H.NoGhost ∧ 𝒢.NoGhost := by
  constructor
  · intro h
    refine ⟨fun d hd => h _ (RunClauses_glue_lift hd), fun d hd => ?_⟩
    exact h (d.map (glueAtom x y₁ y₂)) (List.mem_append_right _ (List.mem_map.2 ⟨d, hd, rfl⟩))
  · rintro ⟨h1, h2⟩ c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      exact h1 d hd
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      exact h2 d hd

private theorem RunClauses_glue_labelsInt :
    (H.glue x y₁ y₂ 𝒢).LabelsInt ↔ H.LabelsInt := by
  have e : ∀ d : Comp (Atom 3 m), ((d.map (liftA n')).label.all fun ℓ => ℓ.2.isRight) =
      d.label.all fun ℓ => ℓ.2.isRight := by
    intro d
    rcases hl : d.label with _ | ⟨pq, u⟩ <;> simp [Comp.map, hl, RunClauses_liftA_isRight]
  constructor
  · intro h d hd
    rw [← e]
    exact h _ (RunClauses_glue_lift hd)
  · intro h c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      rw [e]
      exact h d hd
    · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
      rcases hl : d.label with _ | ⟨pq, u⟩
      · simp [Comp.map, hl]
      · simp [Comp.map, hl, RunClauses_glueAtom_int x y₁ y₂ hx hy₁ hy₂]

private theorem RunClauses_glue_td :
    (H.glue x y₁ y₂ 𝒢).TensorDiffusive ↔ H.TensorDiffusive := by
  rw [RunClauses_td_iff, RunClauses_td_iff]
  constructor
  · intro h d hd h0
    exact h _ (RunClauses_glue_lift hd) (by simpa [Comp.map, RunClauses_liftA_inl] using h0)
  · intro h c hc h0
    obtain ⟨d, hd, rfl⟩ := RunClauses_glue_atExt hx hy₁ hy₂ hc
      (by rcases h0 with h0 | h0 <;> rw [h0] <;> simp)
    exact h d hd (by simpa [Comp.map, RunClauses_liftA_inl] using h0)

end Glue

/-! ## The terms of the local expansions -/

section Dec

variable {n : ℕ}

/-- The charge pattern of the block normal form and the clause on the external atoms of a term of
`Local_Dec`, on the graphs without labels. -/
private theorem RunClauses_dec_clauses_strip {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    {K D P R : List (Comp (Atom 3 n))} {D' P' N : List (Comp (Atom 3 (n + j)))}
    (h1 : (Γ.comps.map Local_stripC).Perm (K ++ D ++ P ++ R))
    (h2 : (liftCs j K ++ D' ++ P' ++ N).Perm (Γ'.comps.map Local_stripC))
    (h3 : List.Forall₂ (Local_MovR Γ x j) D D') (h4 : Local_PathOK Γ x j P P')
    (h5 : ∀ c ∈ R, c.kind.isWeight = true) (h6 : ∀ c ∈ N, Local_NewOK Γ x j c)
    (hL : Local_LiftOK (Local_strip Γ) x j (Local_strip Γ'))
    (hC : (Local_strip Γ).ColourInvB) (hE : (Local_strip Γ).ExtClause) :
    (Local_strip Γ').ColourInvB ∧ (Local_strip Γ').ExtClause := by
  set Γs := Local_strip Γ with hΓs
  set Γ's := Local_strip Γ' with hΓ's
  have hc1 : Γs.comps.Perm (K ++ D ++ P ++ R) := h1
  have hc2 : (liftCs j K ++ D' ++ P' ++ N).Perm Γ's.comps := h2
  obtain ⟨hPr, hP'r⟩ := Local_pathOK_random h4
  have hDr : ∀ d ∈ D, d.kind.isRandom = true := fun d hd => by
    obtain ⟨d', -, hm⟩ := Local_f2_left h3 hd
    exact hm.2.1
  have hD'r : ∀ d' ∈ D', d'.kind.isRandom = true := fun d' hd' => by
    obtain ⟨d, -, hm⟩ := Local_f2_right h3 hd'
    exact Local_movR_random hm.1 hm.2.1
  have hRr : ∀ c ∈ R, c.kind.isRandom = true := fun c hc => by
    have := h5 c hc
    cases hk : c.kind <;> simp_all [Kind.isWeight, Kind.isRandom]
  have memΓ : ∀ c ∈ K ++ D ++ P ++ R, c ∈ Γs.comps := fun c hc => hc1.symm.mem_iff.1 hc
  have memΓ' : ∀ c' ∈ Γ's.comps, c' ∈ liftCs j K ∨ c' ∈ D' ∨ c' ∈ P' ∨ c' ∈ N := by
    intro c' hc'
    have := hc2.mem_iff.2 hc'
    simp only [List.mem_append] at this
    tauto
  have liftmem : ∀ c ∈ K, c.map (liftA j) ∈ Γ's.comps := fun c hc =>
    hc2.mem_iff.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (Local_mem_liftCs.2 ⟨c, hc, rfl⟩))))
  have inK : ∀ c ∈ Γs.comps, c.kind.isRandom = false → c ∈ K := by
    intro c hc hr
    have := hc1.mem_iff.1 hc
    simp only [List.mem_append] at this
    rcases this with ((h | h) | h) | h
    · exact h
    · exact absurd (hDr c h) (by rw [hr]; simp)
    · exact absurd (hPr c h) (by rw [hr]; simp)
    · exact absurd (hRr c h) (by rw [hr]; simp)
  have flatL := Local_lift_flat hL
  have unpL := Local_lift_unpinned hL
  have inl_iff : ∀ (u : Atom 3 n) (a : Fin 3), liftA j u = .inl a ↔ u = .inl a := by
    intro u a
    cases u <;> simp [liftA]
  have flat_int : ∀ u : Atom 3 (n + j), u.isRight = true → Γ's.flatAtom u = u := by
    intro u hu
    cases u with
    | inl a => simp at hu
    | inr b => rfl
  have isR_ne : ∀ (u : Atom 3 (n + j)) (a : Fin 3), u.isRight = true → u ≠ .inl a := by
    rintro u a hu rfl
    simp at hu
  have hCC := (Local_colour_iff Γs).1 hC
  -- the charge pattern
  have CClift : ∀ c, Local_CC Γs c → Local_CC Γ's (c.map (liftA j)) := by
    intro c h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hr => ?_, fun hw => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := h1 hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (Γ's.flatAtom (liftA j c.x)).isRight = true
        rw [flatL, Local_lift_isRight]
        exact a1
      · change Γ's.flatAtom (liftA j c.y) ≠ _
        rw [flatL, Ne, inl_iff]
        exact a2
      · change Γ's.flatAtom (liftA j c.y) = _ → _
        rw [flatL, inl_iff]
        exact a3
      · change Γ's.flatAtom (liftA j c.y) = _ → _
        rw [flatL, inl_iff]
        exact a4
    · obtain ⟨a1, a2⟩ := h2 hw
      refine ⟨?_, ?_⟩
      · change (Γ's.flatAtom (liftA j c.x)).isRight = true
        rw [flatL, Local_lift_isRight]
        exact a1
      · change (Γ's.flatAtom (liftA j c.y)).isRight = true
        rw [flatL, Local_lift_isRight]
        exact a2
  have hColour : Γ's.ColourInvB := by
    refine (Local_colour_iff Γ's).2 fun c' hc' => ?_
    rcases memΓ' c' hc' with h | h | h | h
    · obtain ⟨c, hc, rfl⟩ := Local_mem_liftCs.1 h
      exact CClift c (hCC c (memΓ c (by simp [hc])))
    · obtain ⟨d, hd, hk, hr, hx, hy, -⟩ := Local_f2_right h3 h
      obtain ⟨b1, b2⟩ := hCC d (memΓ d (by simp [hd]))
      obtain ⟨a1, a2, a3, a4⟩ := b1 hr
      have hr' := Local_movR_random hk hr
      have hkk : ∀ ch, d.kind = .G ch → c'.kind = .G ch := by
        intro ch h'
        rcases hk with hk | ⟨hw, -⟩
        · rw [hk, h']
        · rw [h'] at hw; simp [Kind.isWeight] at hw
      refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hw => absurd hr' (by rw [hw]; simp [Kind.isRandom])⟩
      · rcases hx with hx | ⟨-, hx⟩
        · rw [hx, flatL, Local_lift_isRight]; exact a1
        · rw [flat_int _ hx]; exact hx
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, flatL, Ne, inl_iff]; exact a2
        · rw [flat_int _ hy]; exact isR_ne _ _ hy
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, flatL, inl_iff]; exact fun h' => hkk _ (a3 h')
        · rw [flat_int _ hy]; exact fun h => absurd h (isR_ne _ _ hy)
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, flatL, inl_iff]; exact fun h' => hkk _ (a4 h')
        · rw [flat_int _ hy]; exact fun h => absurd h (isR_ne _ _ hy)
    · rcases h4 with ⟨-, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, -, -, hp⟩
      · simp at h
      · have hcΓ : c ∈ Γs.comps := memΓ c (by simp)
        have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
        obtain ⟨b1, -⟩ := hCC c hcΓ
        obtain ⟨a1, a2, a3, a4⟩ := b1 hcr
        set b := (if c.kind.isWeight then c.x else c.y) with hbdef
        have hbf : Γs.flatAtom b ≠ .inl 0 ∧ (Γs.flatAtom b = .inl 1 → ch = .plus) ∧
            (Γs.flatAtom b = .inl 2 → ch = .minus) := by
          rcases hk with hk | hk | hk
          · have hw : c.kind.isWeight = false := by rw [hk]; rfl
            have hbe : b = c.y := by simp [hbdef, hw]
            rw [hbe]
            refine ⟨a2, fun h => ?_, fun h => ?_⟩
            · have := a3 h; rw [hk] at this; simpa using this
            · have := a4 h; rw [hk] at this; simpa using this
          all_goals
            have hw : c.kind.isWeight = true := by rw [hk]; rfl
            have hbe : b = c.x := by simp [hbdef, hw]
            rw [hbe]
            refine ⟨fun h => by rw [h] at a1; simp at a1, fun h => by rw [h] at a1; simp at a1,
              fun h => by rw [h] at a1; simp at a1⟩
        rw [hp.mem_iff] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · unfold solidC
          split_ifs with he
          · rw [he]
            exact Local_CC_int hu hu
          · refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hw => by simp [mkC] at hw⟩
            · change (Γ's.flatAtom (liftA j c.x)).isRight = true
              rw [flatL, Local_lift_isRight]; exact a1
            · change Γ's.flatAtom u ≠ _
              rw [flat_int _ hu]; exact isR_ne _ _ hu
            · change Γ's.flatAtom u = _ → _
              rw [flat_int _ hu]; exact fun h => absurd h (isR_ne _ _ hu)
            · change Γ's.flatAtom u = _ → _
              rw [flat_int _ hu]; exact fun h => absurd h (isR_ne _ _ hu)
        · unfold solidC
          split_ifs with he
          · exact Local_CC_int hv hv
          · refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hw => by simp [mkC] at hw⟩
            · change (Γ's.flatAtom v).isRight = true
              rw [flat_int _ hv]; exact hv
            · change Γ's.flatAtom (liftA j b) ≠ _
              rw [flatL, Ne, inl_iff]
              exact hbf.1
            · change Γ's.flatAtom (liftA j b) = _ → _
              rw [flatL, inl_iff]
              intro h
              simp [mkC, hbf.2.1 h]
            · change Γ's.flatAtom (liftA j b) = _ → _
              rw [flatL, inl_iff]
              intro h
              simp [mkC, hbf.2.2 h]
    · exact Local_CC_int (h6 c' h).1 (h6 c' h).2.1
  -- the clause on the external atoms
  obtain ⟨E1, E2, E3, E4, E5⟩ := hE
  have inK' : ∀ c' ∈ Γ's.comps, c'.kind.isRandom = false → c' ∈ liftCs j K ∨ c' ∈ N := by
    intro c' hc' hr
    rcases memΓ' c' hc' with h | h | h | h
    · exact Or.inl h
    · exact absurd (hD'r c' h) (by rw [hr]; simp)
    · exact absurd (hP'r c' h) (by rw [hr]; simp)
    · exact Or.inr h
  have diffK : ∀ c' ∈ Γ's.comps, c'.kind.isDiffusive = true → ∃ c ∈ K, c' = c.map (liftA j) := by
    intro c' hc' hd
    have hr : c'.kind.isRandom = false := Local_diff_notRandom hd
    rcases inK' c' hc' hr with h | h
    · exact Local_mem_liftCs.1 h
    · exact absurd hd (by rw [(h6 c' h).2.2.2.2.2.1]; simp)
  have hdp : ∀ a : Fin 3, Γs.HasDiffToPinned (.inl a) → Γ's.HasDiffToPinned (.inl a) := by
    rintro a ⟨c, hc, hd, hor⟩
    have hcK : c ∈ K := inK c hc (Local_diff_notRandom hd)
    refine ⟨c.map (liftA j), liftmem c hcK, hd, ?_⟩
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [Comp.map, h1, liftA], by
        change ¬ Γ's.Unpinned (liftA j c.y); rw [unpL]; exact h2⟩
    · exact Or.inr ⟨by simp [Comp.map, h1, liftA], by
        change ¬ Γ's.Unpinned (liftA j c.x); rw [unpL]; exact h2⟩
  have hdt : ∀ a : Fin 3, Γs.DiffToPinned (.inl a) → Γ's.DiffToPinned (.inl a) := by
    intro a h c' hc' hd
    obtain ⟨c, hcK, rfl⟩ := diffK c' hc' hd
    obtain ⟨h1, h2⟩ := h c (memΓ c (by simp [hcK])) hd
    refine ⟨fun hx => ?_, fun hy => ?_⟩
    · change ¬ Γ's.Unpinned (liftA j c.y)
      rw [unpL]
      exact h1 ((inl_iff c.x a).1 hx)
    · change ¬ Γ's.Unpinned (liftA j c.x)
      rw [unpL]
      exact h2 ((inl_iff c.y a).1 hy)
  -- the counts of components at an unpinned external atom
  have deg_le : ∀ a : Fin 3, Γs.Unpinned (.inl a) →
      Γ's.nonDotDeg (.inl a) ≤ Γs.nonDotDeg (.inl a) := by
    intro a hU
    let q : Comp (Atom 3 n) → Bool := fun c =>
      decide ((c.x = .inl a ∨ c.y = .inl a) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)
    let q' : Comp (Atom 3 (n + j)) → Bool := fun c =>
      decide ((c.x = .inl a ∨ c.y = .inl a) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)
    have hfx : ∀ c ∈ Γs.comps, c.kind.isRandom = true → c.x ≠ .inl a := by
      intro c hc hr hx
      have := ((hCC c hc).1 hr).1
      rw [hx, Local_flat_unpinned hU] at this
      simp at this
    have e0 : Γ's.nonDotDeg (.inl a) = Γ's.comps.countP q' := by
      unfold Graph.nonDotDeg
      rw [List.countP_eq_length_filter]
    have e1 : Γs.nonDotDeg (.inl a) = Γs.comps.countP q := by
      unfold Graph.nonDotDeg
      rw [List.countP_eq_length_filter]
    rw [e0, e1, ← hc2.countP_eq, hc1.countP_eq]
    simp only [List.countP_append]
    have cK : (liftCs j K).countP q' = K.countP q := by
      unfold liftCs
      rw [List.countP_map]
      congr 1
      funext c
      simp only [Function.comp_apply, q, q', Comp.map, inl_iff]
    have cD : D'.countP q' ≤ D.countP q := by
      refine Local_countP_f2 h3 fun d d' hm hq => ?_
      obtain ⟨hk, hr, hx, hy, -⟩ := hm
      simp only [q, q', decide_eq_true_eq] at hq ⊢
      refine ⟨?_, (Local_isRandom_kinds hr).1, (Local_isRandom_kinds hr).2.1⟩
      rcases hq.1 with h | h
      · left
        rcases hx with hx | ⟨-, hx⟩
        · exact (inl_iff _ _).1 (hx ▸ h)
        · rw [h] at hx; simp at hx
      · right
        rcases hy with hy | ⟨-, hy⟩
        · exact (inl_iff _ _).1 (hy ▸ h)
        · rw [h] at hy; simp at hy
    have cP : P'.countP q' ≤ P.countP q := by
      rcases h4 with ⟨rfl, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, -, -, hp⟩
      · simp
      · rw [hp.countP_eq]
        have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
        have hcx := hfx c (memΓ c (by simp)) hcr
        have h1 : q' (solidC ch (liftA j c.x) u) = false := by
          unfold solidC
          split_ifs with he
          · subst he
            simp only [q', mkC, decide_eq_false_iff_not]
            rintro ⟨h | h, -⟩ <;> rw [h] at hu <;> simp at hu
          · simp only [q', mkC, decide_eq_false_iff_not]
            rintro ⟨h | h, -⟩
            · exact hcx ((inl_iff _ _).1 h)
            · rw [h] at hu; simp at hu
        set b := (if c.kind.isWeight then c.x else c.y) with hbdef
        have h2 : q' (solidC ch v (liftA j b)) = true → q c = true := by
          intro h
          unfold solidC at h
          split_ifs at h with he
          · simp only [q', mkC, decide_eq_true_eq] at h
            rcases h.1 with h' | h' <;> rw [h'] at hv <;> simp at hv
          · simp only [q', mkC, decide_eq_true_eq] at h
            rcases h.1 with h' | h'
            · rw [h'] at hv; simp at hv
            · have hb := (inl_iff _ _).1 h'
              have hk' := Local_isRandom_kinds hcr
              simp only [q, decide_eq_true_eq]
              refine ⟨?_, hk'.1, hk'.2.1⟩
              by_cases hw : c.kind.isWeight = true
              · rw [hbdef, if_pos hw] at hb
                exact absurd hb hcx
              · rw [hbdef, if_neg hw] at hb
                exact Or.inr hb
        simp only [List.countP_cons, List.countP_nil, h1]
        by_cases hq : q' (solidC ch v (liftA j b)) = true
        · simp [hq, h2 hq]
        · simp [hq]
    have cN : N.countP q' = 0 := by
      rw [List.countP_eq_zero]
      intro c hc
      simp only [q', decide_eq_true_eq, not_and]
      intro h
      rcases h with h | h
      · have := (h6 c hc).1; rw [h] at this; simp at this
      · have := (h6 c hc).2.1; rw [h] at this; simp at this
    rw [cK, cN]
    omega
  have hExt : Γ's.ExtClause := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u' v' hne hb
      rcases Local_atom_cases j u' with ⟨u, rfl⟩ | ⟨i, rfl⟩
      · rcases Local_atom_cases j v' with ⟨v, rfl⟩ | ⟨i, rfl⟩
        · obtain ⟨b, hb'⟩ := E1 u v (fun h => hne (by rw [h]))
            ((Local_lift_sameBlock hL u v).1 hb)
          exact ⟨Fin.castAdd j b, (Local_lift_sameBlock hL u (.inr b)).2 hb'⟩
        · exact absurd (Local_new_block hL i hb.symm) (Local_lift_ne_new j u i)
      · exact absurd (Local_new_block hL i hb).symm hne
    · intro c' hc' hk
      have hr : c'.kind.isRandom = false := by rw [hk]; rfl
      rcases inK' c' hc' hr with h | h
      · obtain ⟨c, hcK, rfl⟩ := Local_mem_liftCs.1 h
        rintro ⟨h1, h2⟩
        exact E2 c (memΓ c (by simp [hcK])) hk ⟨(unpL c.x).1 h1, (unpL c.y).1 h2⟩
      · exact absurd hk (h6 c' h).2.2.2.1
    · intro hU
      have hU' := (unpL (.inl 0)).1 hU
      obtain ⟨a1, a2⟩ := E3 hU'
      exact ⟨hdp 0 a1, hdt 0 a2⟩
    · intro hU
      have hU' := (unpL (.inl 2)).1 hU
      obtain ⟨a1, a2⟩ := E4 hU'
      refine ⟨fun c' hc' hd => ?_, le_trans (deg_le 2 hU') a2⟩
      obtain ⟨c, hcK, rfl⟩ := diffK c' hc' hd
      obtain ⟨b1, b2⟩ := a1 c (memΓ c (by simp [hcK])) hd
      exact ⟨fun h => b1 ((inl_iff _ _).1 h), fun h => b2 ((inl_iff _ _).1 h)⟩
    · intro hU
      have hU' := (unpL (.inl 1)).1 hU
      obtain ⟨a1, a2, a3⟩ := E5 hU'
      refine ⟨?_, hdt 1 a2, le_trans (deg_le 1 hU') a3⟩
      rcases a1 with ⟨c, hc, hk, hor⟩ | h
      · left
        have hcr : c.kind.isRandom = true := by rw [hk]; rfl
        have hcx : c.x ≠ .inl 1 := by
          intro hx
          have := ((hCC c hc).1 hcr).1
          rw [hx, Local_flat_unpinned hU'] at this
          simp at this
        have hcy : c.y = .inl 1 := hor.resolve_left hcx
        have := hc1.mem_iff.1 hc
        simp only [List.mem_append] at this
        rcases this with ((h | h) | h) | h
        · exact ⟨c.map (liftA j), liftmem c h, hk, Or.inr (by simp [Comp.map, hcy, liftA])⟩
        · obtain ⟨d', hd', hm⟩ := Local_f2_left h3 h
          refine ⟨d', hc2.mem_iff.1 (by simp [hd']), by
            rcases hm.1 with h' | ⟨hw, -⟩
            · rw [h', hk]
            · rw [hk] at hw; simp [Kind.isWeight] at hw, Or.inr ?_⟩
          rcases hm.2.2.2.1 with hy | ⟨hy, -⟩
          · rw [hy, hcy]; rfl
          · rw [hcy] at hy; simp at hy
        · rcases h4 with ⟨rfl, -⟩ | ⟨c₀, ch, u, v, rfl, hk₀, hu, hv, -, -, hp⟩
          · simp at h
          · simp only [List.mem_singleton] at h
            subst h
            have hch : ch = .plus := by
              rcases hk₀ with h' | h' | h' <;> rw [hk] at h' <;> simp at h'
              exact h'.symm
            subst hch
            have hw : c.kind.isWeight = false := by rw [hk]; rfl
            refine ⟨solidC .plus v (liftA j (if c.kind.isWeight then c.x else c.y)),
              hc2.mem_iff.1 (by simp [hp.mem_iff]), ?_, Or.inr ?_⟩
            · simp only [hw, Bool.false_eq_true, ↓reduceIte, hcy]
              unfold solidC
              rw [if_neg (fun h => by rw [h] at hv; simp [liftA] at hv)]
              rfl
            · simp only [hw, Bool.false_eq_true, ↓reduceIte, hcy]
              unfold solidC
              rw [if_neg (fun h => by rw [h] at hv; simp [liftA] at hv)]
              rfl
        · exact absurd (h5 c h) (by rw [hk]; simp [Kind.isWeight])
      · exact Or.inr (hdp 1 h)
  exact ⟨hColour, hExt⟩

/-- A term `t` of an expansion of `Γ` at the atom `x`: `x` goes to an internal atom, and the
charge pattern of the block normal form with the clause on the external atoms, and only diffusive
edges at `⊗`, pass from `Γ` to the graph of `t`. -/
private def RunClauses_Good (Γ : Graph 3 n) (x : Atom 3 n) (t : Tracked 3 n) : Prop :=
  (t.f x).isRight = true ∧ (Γ.ColourInvB → Γ.ExtClause → t.g.ColourInvB ∧ t.g.ExtClause) ∧
    (Γ.TensorDiffusive → t.g.TensorDiffusive)

private theorem RunClauses_good_self {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true) :
    RunClauses_Good Γ x (Tracked.self Γ) :=
  ⟨hx, fun h1 h2 => ⟨h1, h2⟩, id⟩

private theorem RunClauses_good_bind {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n}
    {O : ∀ {n' : ℕ}, (Atom 3 n → Atom 3 n') → Graph 3 n' → TExpansion 3 n'}
    (hE : ∀ t ∈ E, RunClauses_Good Γ x t)
    (hO : ∀ t ∈ E, ∀ s ∈ O t.f t.g, RunClauses_Good t.g (t.f x) s) :
    ∀ u ∈ E.bind O, RunClauses_Good Γ x u := by
  intro u hu
  unfold TExpansion.bind at hu
  obtain ⟨t, ht, hu⟩ := List.mem_flatMap.1 hu
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
  obtain ⟨-, a2, a3⟩ := hE t ht
  obtain ⟨b1, b2, b3⟩ := hO t ht s hs
  exact ⟨b1, fun h1 h2 => (a2 h1 h2).elim b2, b3 ∘ a3⟩

private theorem RunClauses_oDot_good {Γ : Graph 3 n} {x : Atom 3 n} (hx : x.isRight = true) :
    ∀ t ∈ oDotT Γ, RunClauses_Good Γ x t :=
  fun t ht => ⟨RunClauses_oDot_int hx t ht, fun hC hE => RunClauses_oDot_CE hC hE t ht,
    fun hT => RunClauses_oDot_td hT t ht⟩

private theorem RunClauses_dot_after {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n}
    (hE : ∀ t ∈ E, RunClauses_Good Γ x t) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), RunClauses_Good Γ x t :=
  RunClauses_good_bind hE fun t ht s hs => RunClauses_oDot_good (hE t ht).1 s hs

/-- The components at `⊗` of a term of `Local_Dec` are lifted components of the graph. -/
private theorem RunClauses_dec_td {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (hd : Local_Dec Γ x j Γ') (hT : Γ.TensorDiffusive) : Γ'.TensorDiffusive := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, -, h6, -⟩ := hd
  rw [RunClauses_td_iff] at hT ⊢
  have hTs : ∀ c ∈ Γ.comps.map Local_stripC, (c.x = .inl 0 ∨ c.y = .inl 0) →
      c.kind.isDiffusive = true := by
    intro c hc h0
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact hT c₀ hc₀ h0
  have memΓ : ∀ c ∈ K ++ D ++ P ++ R, c ∈ Γ.comps.map Local_stripC :=
    fun c hc => h1.symm.subset hc
  have hrand : ∀ c ∈ K ++ D ++ P ++ R, c.kind.isRandom = true → c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc hr
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩ <;>
      [have := hTs c (memΓ c hc) (Or.inl h0); have := hTs c (memΓ c hc) (Or.inr h0)] <;>
      rw [Local_diff_notRandom this] at hr <;> cases hr
  have inl0 : ∀ u : Atom 3 n, (liftA j u : Atom 3 (n + j)) = .inl 0 ↔ u = .inl 0 := by
    intro u
    cases u <;> simp [liftA]
  have int0 : ∀ u : Atom 3 (n + j), u.isRight = true → u ≠ .inl 0 := by
    rintro u hu rfl
    simp at hu
  intro c' hc' h0
  have hs : Local_stripC c' ∈ liftCs j K ++ D' ++ P' ++ N :=
    h2.symm.subset (List.mem_map_of_mem hc')
  change (Local_stripC c').kind.isDiffusive = true
  change (Local_stripC c').x = .inl 0 ∨ (Local_stripC c').y = .inl 0 at h0
  generalize Local_stripC c' = d at hs h0
  simp only [List.mem_append] at hs
  rcases hs with ((h | h) | h) | h
  · obtain ⟨c, hc, rfl⟩ := Local_mem_liftCs.1 h
    refine hTs c (memΓ c (by simp [hc])) ?_
    simpa [Comp.map, inl0] using h0
  · exfalso
    obtain ⟨d₀, hd₀, hk, hr, hx, hy, -⟩ := Local_f2_right h3 h
    obtain ⟨n1, n2⟩ := hrand d₀ (by simp [hd₀]) hr
    rcases h0 with h0 | h0
    · rcases hx with hx | ⟨-, hx⟩
      · rw [hx, inl0] at h0; exact n1 h0
      · exact int0 _ hx h0
    · rcases hy with hy | ⟨-, hy⟩
      · rw [hy, inl0] at h0; exact n2 h0
      · exact int0 _ hy h0
  · exfalso
    rcases h4 with ⟨-, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, -, -, hp⟩
    · simp at h
    · have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
      obtain ⟨n1, n2⟩ := hrand c (by simp) hcr
      rw [hp.mem_iff] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · rw [(Local_solidC_xy _ _ _).1, (Local_solidC_xy _ _ _).2, inl0] at h0
        rcases h0 with h0 | h0
        · exact n1 h0
        · exact int0 _ hu h0
      · rw [(Local_solidC_xy _ _ _).1, (Local_solidC_xy _ _ _).2, inl0] at h0
        rcases h0 with h0 | h0
        · exact int0 _ hv h0
        · split_ifs at h0
          · exact n1 h0
          · exact n2 h0
  · exfalso
    obtain ⟨hx, hy, -⟩ := h6 d h
    rcases h0 with h0 | h0
    · exact int0 _ hx h0
    · exact int0 _ hy h0

private theorem RunClauses_good_of_dec {Γ : Graph 3 n} {x : Fin n} {j : ℕ}
    {t : Tracked 3 n} (hn : t.nOut = n + j) (hf : ∀ u, t.f u = hn ▸ liftA j u)
    (hd : Local_Dec Γ x j (hn ▸ t.g)) : RunClauses_Good Γ (.inr x) t := by
  obtain ⟨tn, tg, tf⟩ := t
  simp only at hn
  subst hn
  simp only at hf hd
  refine ⟨by show (tf (.inr x)).isRight = true; rw [hf]; rfl, fun hC hE => ?_,
    fun hT => RunClauses_dec_td hd hT⟩
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hL := Local_dec_liftOK h1 h2 h3 h4 h5 h6 h7
  have e := Local_same3_clauses (Local_strip_same3 Γ)
  have e' := Local_same3_clauses (Local_strip_same3 tg)
  obtain ⟨a1, a2⟩ := RunClauses_dec_clauses_strip h1 h2 h3 h4 h5 h6 hL (e.1.2 hC) (e.2.1.2 hE)
  exact ⟨e'.1.1 a1, e'.2.1.1 a2⟩

private theorem RunClauses_good_of_decT {Δ : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Local_DecT Δ x t) : RunClauses_Good Δ (.inr x) t := by
  obtain ⟨j, hn, hf, hd, -⟩ := h
  exact RunClauses_good_of_dec hn hf hd

/-- The main term of the `GG` expansion keeps the clauses. -/
private theorem RunClauses_good_of_GM {Δ : Graph 3 n} (hlf : Δ.LabelFree) {x : Fin n}
    {t : Tracked 3 n} (h : Local_GM Δ x t) : RunClauses_Good Δ (.inr x) t := by
  obtain ⟨Γ', rfl, i, j, hi, hj, ch, w, wv, hij, hki, hkj, hxi, hyj, hw, hperm, hlab⟩ := h
  have hf : (eraseIdxs [i, j] Δ.comps).map Local_stripC = eraseIdxs [i, j] Δ.comps :=
    Local_strip_labelFree (Γ := ⟨_, 0⟩) fun c hc => hlf c (Local_mem_eraseIdxs hc)
  rw [hf] at hperm
  have hΔ := Local_eraseIdxs2_perm Δ.comps i j hi hj hij
  generalize eraseIdxs [i, j] Δ.comps = F at hΔ hperm
  generalize Δ.comps[i] = e at hΔ hki hxi hw hperm
  generalize Δ.comps[j] = e' at hΔ hkj hyj hw hperm
  obtain ⟨hsx, hsy⟩ := Local_solidC_xy ch e'.x e.y
  have hks := Local_kind_solidC ch e'.x e.y
  have memΔ : ∀ c, c ∈ Δ.comps ↔ c ∈ F ∨ c = e ∨ c = e' := by
    intro c
    rw [hΔ.mem_iff]
    simp
  let Γ₀ : Graph 3 n := ⟨F ++ [solidC ch e'.x e.y, mkC (.waved wv) (.inr x) (.inr w)], Γ'.coeff⟩
  have memΓ₀ : ∀ c, c ∈ Γ₀.comps ↔ c ∈ F ∨ c = solidC ch e'.x e.y ∨
      c = mkC (.waved wv) (.inr x) (.inr w) := by
    intro c
    show c ∈ F ++ [_, _] ↔ _
    simp
  have hS : Local_Same3 Γ₀ Γ' := by
    unfold Local_Same3
    have e1 : Γ'.comps.map Local_tri = (Γ'.comps.map Local_stripC).map Local_tri := by
      simp [Function.comp_def, Local_tri, Local_stripC]
    rw [e1]
    exact hperm.map _
  -- the dotted graph
  have g1 : Γ₀.dotGraph = Δ.dotGraph := by
    unfold Graph.dotGraph
    refine Local_fromRel_congr (fun κ => κ = .dot) fun u v => ⟨?_, ?_⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact ⟨c, (memΔ c).2 (Or.inl hc), hk, hx, hy⟩
      · rcases hks with h | h <;> rw [h] at hk <;> cases hk
      · simp [mkC] at hk
    · rintro ⟨c, hc, hk, hx, hy⟩
      rcases (memΔ c).1 hc with hc | rfl | rfl
      · exact ⟨c, (memΓ₀ c).2 (Or.inl hc), hk, hx, hy⟩
      · rw [hki] at hk; cases hk
      · rw [hkj] at hk; cases hk
  obtain ⟨hb₀, hfl₀, hu₀⟩ := Local_dot_fun g1
  refine ⟨rfl, fun hC hE => ?_, fun hT => ?_⟩
  · -- the clauses of `Γ₀`
    have hCC := (Local_colour_iff Δ).1 hC
    have eCC : ∀ c, Local_CC Γ₀ c ↔ Local_CC Δ c := by
      intro c
      simp only [Local_CC, hfl₀]
    have ce := hCC e ((memΔ e).2 (Or.inr (Or.inl rfl)))
    have ce' := hCC e' ((memΔ e').2 (Or.inr (Or.inr rfl)))
    obtain ⟨a1, -⟩ := ce'.1 (by rw [hkj]; rfl)
    obtain ⟨b1, b2, b3, b4⟩ := ce.1 (by rw [hki]; rfl)
    have hC₀ : Γ₀.ColourInvB := by
      refine (Local_colour_iff Γ₀).2 fun c hc => ?_
      rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact (eCC c).2 (hCC c ((memΔ c).2 (Or.inl hc)))
      · rw [eCC]
        unfold solidC
        split_ifs with hab
        · have hne : ∀ a : Fin 3, Δ.flatAtom e'.x ≠ .inl a := by
            intro a h
            rw [h] at a1
            simp at a1
          refine ⟨fun _ => ⟨a1, hne 0, fun h => absurd h (hne 1), fun h => absurd h (hne 2)⟩,
            fun h => by simp [mkC] at h⟩
        · refine ⟨fun _ => ⟨a1, b2, fun h => ?_, fun h => ?_⟩, fun h => by simp [mkC] at h⟩
          · show Kind.G ch = .G .plus
            rw [← hki]
            exact b3 h
          · show Kind.G ch = .G .minus
            rw [← hki]
            exact b4 h
      · exact Local_CC_int rfl rfl
    have hdc : ∀ c, c.kind.isDiffusive = true → (c ∈ Γ₀.comps ↔ c ∈ Δ.comps) := by
      intro c hd
      constructor
      · intro hc
        rcases (memΓ₀ c).1 hc with hc | rfl | rfl
        · exact (memΔ c).2 (Or.inl hc)
        · rcases hks with h | h <;> rw [h] at hd <;> simp [Kind.isDiffusive] at hd
        · simp [mkC, Kind.isDiffusive] at hd
      · intro hc
        rcases (memΔ c).1 hc with hc | rfl | rfl
        · exact (memΓ₀ c).2 (Or.inl hc)
        · rw [hki] at hd; simp [Kind.isDiffusive] at hd
        · rw [hkj] at hd; simp [Kind.isDiffusive] at hd
    have hdiff : ∀ u, Γ₀.DiffToPinned u ↔ Δ.DiffToPinned u := by
      intro u
      unfold Graph.DiffToPinned
      rw [hu₀]
      exact ⟨fun h c hc hd => h c ((hdc c hd).2 hc) hd, fun h c hc hd => h c ((hdc c hd).1 hc) hd⟩
    have hhas : ∀ u, Γ₀.HasDiffToPinned u ↔ Δ.HasDiffToPinned u := by
      intro u
      unfold Graph.HasDiffToPinned
      rw [hu₀]
      exact ⟨fun ⟨c, hc, hd, h⟩ => ⟨c, (hdc c hd).1 hc, hd, h⟩,
        fun ⟨c, hc, hd, h⟩ => ⟨c, (hdc c hd).2 hc, hd, h⟩⟩
    have hdeg : ∀ u : Atom 3 n, u.isLeft = true → Γ₀.nonDotDeg u ≤ Δ.nonDotDeg u := by
      intro u hu
      unfold Graph.nonDotDeg
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, hΔ.countP_eq]
      refine Local_countP_le2 _ F _ _ _ _ ?_ ?_
      · exact decide_eq_false (by
          rintro ⟨h | h, -⟩ <;> simp only [mkC] at h <;> subst h <;> simp at hu)
      · simp only [decide_eq_true_eq, hsx, hsy, hki, hkj]
        rintro ⟨h | h, -⟩
        · right
          exact ⟨Or.inl h, by simp, by simp⟩
        · left
          exact ⟨Or.inr h, by simp, by simp⟩
    have hE₀ : Γ₀.ExtClause := by
      obtain ⟨x1, x2, x3, x4, x5⟩ := hE
      unfold Graph.ExtClause
      rw [hb₀, hu₀]
      refine ⟨x1, fun c hc hk => ?_, fun h => ⟨(hhas _).2 (x3 h).1, (hdiff _).2 (x3 h).2⟩,
        fun h => ⟨fun c hc hd => (x4 h).1 c ((hdc c hd).1 hc) hd, (hdeg _ rfl).trans (x4 h).2⟩,
        fun h => ⟨?_, (hdiff _).2 (x5 h).2.1, (hdeg _ rfl).trans (x5 h).2.2⟩⟩
      · rcases (memΓ₀ c).1 hc with hc | rfl | rfl
        · exact x2 c ((memΔ c).2 (Or.inl hc)) hk
        · rcases hks with h | h <;> rw [h] at hk <;> cases hk
        · simp [mkC] at hk
      · have hf1 : Δ.flatAtom (.inl 1) = .inl 1 := Local_flat_unpinned h
        rcases (x5 h).1 with ⟨c, hc, hk, hat⟩ | hd
        · rcases (memΔ c).1 hc with hc | rfl | rfl
          · exact Or.inl ⟨c, (memΓ₀ c).2 (Or.inl hc), hk, hat⟩
          · have hey : c.y = .inl 1 := hat.resolve_left (by rw [hxi]; simp)
            have hch : ch = .plus := by
              rw [hki] at hk
              cases hk
              rfl
            have hne : e'.x ≠ c.y := by
              intro heq
              rw [heq, hey, hf1] at a1
              simp at a1
            refine Or.inl ⟨solidC ch e'.x c.y, (memΓ₀ _).2 (Or.inr (Or.inl rfl)), ?_, Or.inr (hsy.trans hey)⟩
            unfold solidC
            simp only [hne, if_false, hch]
            rfl
          · have hex : c.x = .inl 1 := hat.resolve_right (by rw [hyj]; simp)
            rw [hex, hf1] at a1
            simp at a1
        · exact Or.inr ((hhas _).2 hd)

    have cl := Local_same3_clauses hS
    exact ⟨cl.1.2 hC₀, cl.2.1.2 hE₀⟩
  · rw [RunClauses_td_iff] at hT ⊢
    have hT₀ : ∀ c ∈ Γ₀.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true := by
      intro c hc h0
      rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact hT c ((memΔ c).2 (Or.inl hc)) h0
      · exfalso
        rw [hsx, hsy] at h0
        rcases h0 with h0 | h0
        · have := hT e' ((memΔ e').2 (Or.inr (Or.inr rfl))) (Or.inl h0)
          rw [hkj] at this
          cases this
        · have := hT e ((memΔ e).2 (Or.inr (Or.inl rfl))) (Or.inr h0)
          rw [hki] at this
          cases this
      · simp [mkC] at h0
    exact (Local_same3_all hS (fun κ a b => (a = .inl 0 ∨ b = .inl 0) →
      κ.isDiffusive = true)).2 hT₀

end Dec

/-! ## The local expansions at an internal atom -/

section Ops

variable {n : ℕ}

private theorem RunClauses_lf_of_plain {Γ : Graph 3 n}
    (h : ¬ (!(Γ.comps.all Comp.isPlainB)) = true) : Γ.LabelFree := by
  intro c hc
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h
  have := h c hc
  unfold Comp.isPlainB at this
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1.2

/-- The terms of `O^{(x),1}_weight`. -/
private theorem RunClauses_oWeight1_good {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeight1T (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := Local_splitRegular_dec (.inr x) Γ.comps p hp
  refine RunClauses_good_of_dec (j := 0) rfl (fun u => (Local_liftA_zero u).symm) ?_
  refine ⟨K.map Local_stripC, D.map Local_stripC, [], R.map Local_stripC,
    D'.map Local_stripC, [], [], ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, by simp, fun i => i.elim0⟩
  · have := h1.map Local_stripC
    simpa [List.map_append] using this
  · rw [Local_liftCs_zero]
    have := (h2.map Local_stripC).symm
    simpa [List.map_append] using this
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h3.imp fun d d' ⟨ch, hk, hx, hl, hd'⟩ => ?_
    subst hd'
    refine ⟨Or.inr ⟨by simp [Local_stripC, hk, Kind.isWeight], by simp [Local_stripC,
      Kind.isWeight]⟩, by simp [Local_stripC, hk, Kind.isRandom],
      Or.inl (Local_liftA_zero _).symm, Or.inl (Local_liftA_zero _).symm, ?_⟩
    unfold Local_SameR
    rw [Local_comp_proj_zero]
    left
    refine ⟨?_, ?_⟩ <;> simp [Local_rd, Local_stripC, hk, Kind.mclass]
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨ch, hk⟩, -, -⟩ := h4 c₀ hc₀
    simp [Local_stripC, hk, Kind.isWeight]

/-- The terms of `O^{(x),2}_weight`. -/
private theorem RunClauses_oWeight2_good {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeight2T (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oWeight2T at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl
  have hlf := RunClauses_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunClauses_good_of_decT (Local_oW2_decT hlf x hE t ht)
  · split at ht
    · rename_i E _ hE
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      exact RunClauses_good_of_decT (Local_decT_conj (Local_conj_conj_comps Γ)
        (Local_oW2_decT (Local_conj_labelFree hlf) x hE t₀ ht₀))
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunClauses_good_self rfl

/-- The terms of `O^{(x)}_weight`. -/
private theorem RunClauses_oWeight_good {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oWeightT (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oWeightT at ht
  split_ifs at ht with hw
  · have h1 : ∀ t ∈ oWeight1T (.inr x) Γ, RunClauses_Good Γ (.inr x) t :=
      RunClauses_oWeight1_good x
    have h2 : ∀ t ∈ (oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g),
        RunClauses_Good Γ (.inr x) t := by
      refine RunClauses_good_bind h1 fun t ht s hs => ?_
      exact Local_good_at (h1 t ht).1 (fun u => ∀ s ∈ oWeight2T u t.g, RunClauses_Good t.g u s)
        (fun x' => RunClauses_oWeight2_good x') s hs
    have h3 : ∀ t ∈ ((oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g)).bind
        (fun _ g => oDotT g), RunClauses_Good Γ (.inr x) t := RunClauses_dot_after h2
    refine RunClauses_good_bind h3 (fun t ht s hs => ?_) t ht
    exact Local_good_at (h3 t ht).1 (fun u => ∀ s ∈ oWeight1T u t.g, RunClauses_Good t.g u s)
      (fun x' => RunClauses_oWeight1_good x') s hs
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl

/-- The terms of `O^{(x)}_multi-e`. -/
private theorem RunClauses_oMultiE_good {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oMultiET (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oMultiET at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl
  have hlf := RunClauses_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunClauses_dot_after
      (fun t ht => RunClauses_good_of_decT (Local_multiEHat_decT hlf x hE t ht)) t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl

/-- The terms of `O^{(x)}_GḠ`. -/
private theorem RunClauses_oGGbar_good {Γ : Graph 3 n} (x : Fin n) :
    ∀ t ∈ oGGbarT (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oGGbarT at ht
  dsimp only at ht
  split_ifs at ht
  · exact RunClauses_oMultiE_good x t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl

private theorem RunClauses_res_good {Δ : Graph 3 n} (hlf : Δ.LabelFree) {x : Fin n}
    {t : Tracked 3 n} (h : Local_DecT Δ x t ∨ Local_GM Δ x t) : RunClauses_Good Δ (.inr x) t :=
  h.elim RunClauses_good_of_decT (RunClauses_good_of_GM hlf)

/-- The terms of `O^{(x)}_GG` at an atom whose outgoing solid edges end at internal atoms. -/
private theorem RunClauses_oGG_good {Γ : Graph 3 n} (x : Fin n)
    (hout : Γ.GGOutInt (.inr x)) : ∀ t ∈ oGGT (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oGGT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl
  have hlf := RunClauses_lf_of_plain hp
  split at ht
  · rename_i E hE
    exact RunClauses_dot_after
      (fun t ht => RunClauses_res_good hlf (Local_ggPos_res hlf x hout hE t ht)) t ht
  · split at ht
    · rename_i E _ hE
      refine RunClauses_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ
      rcases Local_ggPos_res (Local_conj_labelFree hlf) x (Local_conj_out hout) hE t₀ ht₀ with
        h | h
      · exact RunClauses_good_of_decT (Local_decT_conj hc h)
      · exact RunClauses_good_of_GM hlf (Local_GM_conj hc h)
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunClauses_good_self rfl

/-- The terms of the transposed `O^{(x)}_GG` at an atom whose incoming solid edges start at
internal atoms. -/
private theorem RunClauses_oGGT_good {Γ : Graph 3 n} (x : Fin n)
    (hin : Γ.GGInInt (.inr x)) : ∀ t ∈ oGGTT (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  intro t ht
  unfold oGGTT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact RunClauses_good_self rfl
  have hlf := RunClauses_lf_of_plain hp
  have hs := Local_sw_sw_comps Γ
  have hlfs := Local_sw_labelFree hlf
  have houts := Local_sw_out hin
  split at ht
  · rename_i E hE
    refine RunClauses_dot_after (fun t ht => ?_) t ht
    unfold TExpansion.swapSolid at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    rcases Local_ggPos_res hlfs x houts hE t₀ ht₀ with h | h
    · exact RunClauses_good_of_decT (Local_decT_sw hs h)
    · exact RunClauses_good_of_GM hlf (Local_GM_sw hs h)
  · split at ht
    · rename_i E _ hE
      refine RunClauses_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.swapSolid TExpansion.conj at ht
      rw [List.map_map] at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ.swapSolid
      rcases Local_ggPos_res (Local_conj_labelFree hlfs) x (Local_conj_out houts) hE t₀ ht₀ with
        h | h
      · exact RunClauses_good_of_decT (Local_decT_sw hs (Local_decT_conj hc h))
      · exact RunClauses_good_of_GM hlf (Local_GM_sw hs (Local_GM_conj hc h))
    · rw [List.mem_singleton] at ht
      subst ht
      exact RunClauses_good_self rfl

/-- The terms of the local expansions in the form of `Graph.LocSide`. -/
private theorem RunClauses_localOp_good {Γ : Graph 3 n} (x : Fin n) (o : Fin 5)
    (hs : Γ.LocSide o (.inr x)) : ∀ t ∈ localOp' o (.inr x) Γ, RunClauses_Good Γ (.inr x) t := by
  obtain ⟨hs2, hs4⟩ := hs
  match o with
  | 0 => exact RunClauses_oWeight_good x
  | 1 => exact RunClauses_oMultiE_good x
  | 2 => exact RunClauses_oGG_good x (hs2 rfl rfl)
  | 3 => exact RunClauses_oGGbar_good x
  | 4 => exact RunClauses_oGGT_good x (hs4 rfl rfl)

end Ops

section DotNorm

variable {n : ℕ}

end DotNorm

/-! ## Graphs equal up to the names of the internal atoms and the order of the components -/

section Iso

variable {m m' : ℕ}

/-- `c'` is `c`, or `c` with its two atoms exchanged when `c` is a waved edge `s`, a dotted or a
`×`-dotted edge. -/
private def RunClauses_SwapR {V : Type} (c c' : Comp V) : Prop :=
  c' = c ∨ ((c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) ∧
    c' = { c with x := c.y, y := c.x })

/-- The bijection of the atoms given by a bijection of the internal atoms. -/
private def RunClauses_eA (e : Fin m ≃ Fin m') : Atom 3 m ≃ Atom 3 m' :=
  Equiv.sumCongr (Equiv.refl _) e

/-- `Γ'` is `Γ` with its internal atoms relabelled by `e`, its components listed in another order and
the two atoms of some waved edges `s`, dotted and `×`-dotted edges exchanged; the coefficient is
the same. -/
private def RunClauses_Iso (e : Fin m ≃ Fin m') (Γ : Graph 3 m) (Γ' : Graph 3 m') : Prop :=
  Γ'.coeff = Γ.coeff ∧ ∃ cs, List.Forall₂ RunClauses_SwapR
    (Γ.comps.map (Comp.map (RunClauses_eA e))) cs ∧ cs.Perm Γ'.comps

private theorem RunClauses_eA_inl (e : Fin m ≃ Fin m') (a : Fin 3) :
    RunClauses_eA e (.inl a) = .inl a := rfl

private theorem RunClauses_eA_inr (e : Fin m ≃ Fin m') (i : Fin m) :
    RunClauses_eA e (.inr i) = .inr (e i) := rfl

private theorem RunClauses_eA_inl_iff (e : Fin m ≃ Fin m') (u : Atom 3 m) (a : Fin 3) :
    RunClauses_eA e u = .inl a ↔ u = .inl a := by
  cases u <;> simp [RunClauses_eA]

private theorem RunClauses_eA_isRight (e : Fin m ≃ Fin m') (u : Atom 3 m) :
    (RunClauses_eA e u).isRight = u.isRight := by
  cases u <;> rfl

private theorem RunClauses_eA_isLeft (e : Fin m ≃ Fin m') (u : Atom 3 m) :
    (RunClauses_eA e u).isLeft = u.isLeft := by
  cases u <;> rfl

private theorem RunClauses_swapR_eq {V : Type} {c c' : Comp V} (h : RunClauses_SwapR c c') :
    c'.kind = c.kind ∧ c'.label = c.label ∧ c'.minor = c.minor ∧
      ((c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)) ∧
      (c.kind.isRandom = true ∨ c.kind.isDiffusive = true → c' = c) := by
  rcases h with rfl | ⟨hk, rfl⟩
  · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, fun _ => rfl⟩
  · refine ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, fun h => ?_⟩
    exfalso
    rcases hk with hk | hk | hk <;> rw [hk] at h <;> simp [Kind.isRandom, Kind.isDiffusive] at h

private theorem RunClauses_swapR_sym {V : Type} {c c' : Comp V} (h : RunClauses_SwapR c c') :
    s(c'.x, c'.y) = s(c.x, c.y) := by
  rcases (RunClauses_swapR_eq h).2.2.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Sym2.eq_swap]

variable {e : Fin m ≃ Fin m'} {Γ : Graph 3 m} {Γ' : Graph 3 m'}

private theorem RunClauses_iso_mem' (h : RunClauses_Iso e Γ Γ') {c' : Comp (Atom 3 m')}
    (hc' : c' ∈ Γ'.comps) : ∃ c ∈ Γ.comps, RunClauses_SwapR (c.map (RunClauses_eA e)) c' := by
  obtain ⟨-, cs, h1, h2⟩ := h
  obtain ⟨d, hd, hr⟩ := Local_f2_right h1 (h2.symm.subset hc')
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  exact ⟨c, hc, hr⟩

private theorem RunClauses_iso_mem (h : RunClauses_Iso e Γ Γ') {c : Comp (Atom 3 m)}
    (hc : c ∈ Γ.comps) : ∃ c' ∈ Γ'.comps, RunClauses_SwapR (c.map (RunClauses_eA e)) c' := by
  obtain ⟨-, cs, h1, h2⟩ := h
  obtain ⟨c', hc', hr⟩ := Local_f2_left h1 (List.mem_map_of_mem hc)
  exact ⟨c', h2.subset hc', hr⟩

private theorem RunClauses_f2_map {V β : Type} (F : Comp V → β)
    (hF : ∀ c c', RunClauses_SwapR c c' → F c' = F c) {L cs : List (Comp V)}
    (h : List.Forall₂ RunClauses_SwapR L cs) : cs.map F = L.map F := by
  induction h with
  | nil => rfl
  | cons hr _ ih => rw [List.map_cons, List.map_cons, ih, hF _ _ hr]

/-- A function of the components invariant under the exchange of the atoms of `RunClauses_SwapR`, on the
components of `Γ'` and of `Γ`. -/
private theorem RunClauses_iso_map {β : Type} (h : RunClauses_Iso e Γ Γ')
    (F : Comp (Atom 3 m') → β) (hF : ∀ c c', RunClauses_SwapR c c' → F c' = F c) :
    (Γ'.comps.map F).Perm (Γ.comps.map (F ∘ Comp.map (RunClauses_eA e))) := by
  obtain ⟨-, cs, h1, h2⟩ := h
  rw [← List.map_map, ← RunClauses_f2_map F hF h1]
  exact (h2.map F).symm

private theorem RunClauses_iso_count (h : RunClauses_Iso e Γ Γ') (p : Comp (Atom 3 m') → Bool)
    (hp : ∀ c c', RunClauses_SwapR c c' → p c' = p c) :
    (Γ'.comps.filter p).length = (Γ.comps.filter (p ∘ Comp.map (RunClauses_eA e))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, ← List.countP_map]
  obtain ⟨-, cs, h1, h2⟩ := h
  rw [← h2.countP_eq]
  clear h2
  generalize Γ.comps.map (Comp.map (RunClauses_eA e)) = L at h1
  induction h1 with
  | nil => rfl
  | cons hr _ ih => rw [List.countP_cons, List.countP_cons, ih, hp _ _ hr]

private theorem RunClauses_iso_length (h : RunClauses_Iso e Γ Γ') :
    Γ'.comps.length = Γ.comps.length := by
  obtain ⟨-, cs, h1, h2⟩ := h
  rw [← h2.length_eq, ← h1.length_eq, List.length_map]

private theorem RunClauses_iso_card (_ : RunClauses_Iso e Γ Γ') : m' = m := by
  simpa using (Fintype.card_congr e).symm

/-- The components joined by a component of a kind in `P`, read on unordered pairs of atoms. -/
private theorem RunClauses_iso_ex (h : RunClauses_Iso e Γ Γ') (P : Kind → Prop)
    (z : Sym2 (Atom 3 m)) :
    (∃ c ∈ Γ'.comps, P c.kind ∧ s(c.x, c.y) = z.map (RunClauses_eA e)) ↔
      (∃ c ∈ Γ.comps, P c.kind ∧ s(c.x, c.y) = z) := by
  constructor
  · rintro ⟨c', hc', hP, hz⟩
    obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    refine ⟨c, hc, (RunClauses_swapR_eq hr).1 ▸ hP, ?_⟩
    rw [RunClauses_swapR_sym hr] at hz
    exact Sym2.map.injective (RunClauses_eA e).injective (by rw [Sym2.map_mk]; exact hz)
  · rintro ⟨c, hc, hP, hz⟩
    obtain ⟨c', hc', hr⟩ := RunClauses_iso_mem h hc
    refine ⟨c', hc', (RunClauses_swapR_eq hr).1.symm ▸ hP, ?_⟩
    rw [RunClauses_swapR_sym hr, ← hz]
    rfl

/-- The graph on the atoms whose edges are the components of a kind in `P`. -/
private def RunClauses_G {V : Type} (L : List (Comp V)) (P : Kind → Prop) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => ∃ c ∈ L, P c.kind ∧ c.x = a ∧ c.y = b

private theorem RunClauses_G_adj {V : Type} (L : List (Comp V)) (P : Kind → Prop) (u v : V) :
    (RunClauses_G L P).Adj u v ↔ u ≠ v ∧ ∃ c ∈ L, P c.kind ∧ s(c.x, c.y) = s(u, v) := by
  unfold RunClauses_G
  rw [SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ?_
  simp only [Sym2.eq_iff]
  constructor
  · rintro (⟨c, hc, hP, h1, h2⟩ | ⟨c, hc, hP, h1, h2⟩)
    · exact ⟨c, hc, hP, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨c, hc, hP, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨c, hc, hP, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨c, hc, hP, h1, h2⟩
    · exact Or.inr ⟨c, hc, hP, h1, h2⟩

/-- The graphs of the components of a kind in `P` are isomorphic. -/
private def RunClauses_isoG (h : RunClauses_Iso e Γ Γ') (P : Kind → Prop) :
    RunClauses_G Γ.comps P ≃g RunClauses_G Γ'.comps P where
  toEquiv := RunClauses_eA e
  map_rel_iff' := by
    intro u v
    rw [RunClauses_G_adj, RunClauses_G_adj, ← Sym2.map_mk (RunClauses_eA e) u v,
      RunClauses_iso_ex h, (RunClauses_eA e).injective.ne_iff]

private theorem RunClauses_iso_reach (h : RunClauses_Iso e Γ Γ') (P : Kind → Prop)
    (u v : Atom 3 m) :
    (RunClauses_G Γ'.comps P).Reachable (RunClauses_eA e u) (RunClauses_eA e v) ↔
      (RunClauses_G Γ.comps P).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := RunClauses_isoG h P)

private theorem RunClauses_iso_sameBlock (h : RunClauses_Iso e Γ Γ') (u v : Atom 3 m) :
    Γ'.SameBlock (RunClauses_eA e u) (RunClauses_eA e v) ↔ Γ.SameBlock u v :=
  RunClauses_iso_reach h (fun κ => κ = .dot) u v

private theorem RunClauses_iso_sameMol (h : RunClauses_Iso e Γ Γ') (u v : Atom 3 m) :
    Γ'.SameMol (RunClauses_eA e u) (RunClauses_eA e v) ↔ Γ.SameMol u v := by
  unfold Graph.SameMol
  rw [(RunClauses_eA e).injective.eq_iff, RunClauses_eA_isRight, RunClauses_eA_isRight]
  exact or_congr_right (and_congr_right fun _ => and_congr_right fun _ =>
    RunClauses_iso_reach h (fun κ => κ.joinsMol = true) u v)

private theorem RunClauses_iso_unpinned (h : RunClauses_Iso e Γ Γ') (u : Atom 3 m) :
    Γ'.Unpinned (RunClauses_eA e u) ↔ Γ.Unpinned u := by
  unfold Graph.Unpinned
  rw [RunClauses_eA_isLeft]
  refine and_congr_right fun _ => ⟨fun h' b hb => h' (e b) ?_, fun h' b' hb' => h' (e.symm b') ?_⟩
  · exact (RunClauses_iso_sameBlock h u (.inr b)).2 hb
  · refine (RunClauses_iso_sameBlock h u (.inr (e.symm b'))).1 ?_
    rw [RunClauses_eA_inr, Equiv.apply_symm_apply]
    exact hb'

private theorem RunClauses_iso_deg (h : RunClauses_Iso e Γ Γ') (u : Atom 3 m) :
    Γ'.nonDotDeg (RunClauses_eA e u) = Γ.nonDotDeg u := by
  unfold Graph.nonDotDeg
  rw [RunClauses_iso_count h]
  · congr 1
    refine List.filter_congr fun c _ => ?_
    simp only [Function.comp_apply, Comp.map, (RunClauses_eA e).injective.eq_iff]
  · intro c c' hr
    obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
    rw [hk]
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    simp only [or_comm]

private theorem RunClauses_iso_noGhost (h : RunClauses_Iso e Γ Γ') (hG : Γ.NoGhost) :
    Γ'.NoGhost := by
  intro c' hc'
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  rw [(RunClauses_swapR_eq hr).1]
  exact hG c hc

private theorem RunClauses_iso_labelsInt (h : RunClauses_Iso e Γ Γ') (hL : Γ.LabelsInt) :
    Γ'.LabelsInt := by
  intro c' hc'
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  rw [(RunClauses_swapR_eq hr).2.1]
  have := hL c hc
  simp only [Comp.map]
  rcases hcl : c.label with - | ⟨pq, u⟩
  · rfl
  · rw [hcl] at this
    simpa [RunClauses_eA_isRight] using this

private theorem RunClauses_iso_td (h : RunClauses_Iso e Γ Γ') (hT : Γ.TensorDiffusive) :
    Γ'.TensorDiffusive := by
  rw [RunClauses_td_iff] at hT ⊢
  intro c' hc' h0
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
  rw [hk]
  simp only [Comp.map] at hxy
  refine hT c hc ?_
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, RunClauses_eA_inl_iff,
    RunClauses_eA_inl_iff] at h0
  · exact h0
  · exact h0.symm

private theorem RunClauses_CCU_swap {P : Atom 3 m' → Prop} {c : Comp (Atom 3 m')}
    (hk : c.kind = .waved .s ∨ c.kind = .dot ∨ c.kind = .xdot) (h : RunClauses_CCU P c) :
    RunClauses_CCU P { c with x := c.y, y := c.x } := by
  refine ⟨fun hr => ?_, fun hs => ⟨(h.2 hs).2, (h.2 hs).1⟩⟩
  exfalso
  change c.kind.isRandom = true at hr
  rcases hk with hk | hk | hk <;> rw [hk] at hr <;> simp [Kind.isRandom] at hr

private theorem RunClauses_iso_colour (h : RunClauses_Iso e Γ Γ') (hC : Γ.ColourInvB) :
    Γ'.ColourInvB := by
  rw [RunClauses_colour_iff] at hC ⊢
  intro c' hc'
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  have h1 : RunClauses_CCU Γ'.Unpinned (c.map (RunClauses_eA e)) :=
    (RunClauses_CCU_map (RunClauses_iso_unpinned h) (RunClauses_eA_inl_iff e) c).2 (hC c hc)
  rcases hr with rfl | ⟨hk, rfl⟩
  · exact h1
  · exact RunClauses_CCU_swap hk h1

/-- The ends of a component of `Γ'` are the images of the ends of a component of `Γ`, in either
order. -/
private theorem RunClauses_iso_ends' (h : RunClauses_Iso e Γ Γ') {c' : Comp (Atom 3 m')}
    (hc' : c' ∈ Γ'.comps) : ∃ c ∈ Γ.comps, c'.kind = c.kind ∧
      ((c'.x = RunClauses_eA e c.x ∧ c'.y = RunClauses_eA e c.y) ∨
        (c'.x = RunClauses_eA e c.y ∧ c'.y = RunClauses_eA e c.x)) ∧
      (c.kind.isRandom = true ∨ c.kind.isDiffusive = true →
        c'.x = RunClauses_eA e c.x ∧ c'.y = RunClauses_eA e c.y) := by
  obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
  obtain ⟨hk, -, -, hxy, hrd⟩ := RunClauses_swapR_eq hr
  exact ⟨c, hc, hk, hxy, fun h' => by rw [hrd h']; exact ⟨rfl, rfl⟩⟩

private theorem RunClauses_iso_ends (h : RunClauses_Iso e Γ Γ') {c : Comp (Atom 3 m)}
    (hc : c ∈ Γ.comps) : ∃ c' ∈ Γ'.comps, c'.kind = c.kind ∧
      ((c'.x = RunClauses_eA e c.x ∧ c'.y = RunClauses_eA e c.y) ∨
        (c'.x = RunClauses_eA e c.y ∧ c'.y = RunClauses_eA e c.x)) ∧
      (c.kind.isRandom = true ∨ c.kind.isDiffusive = true →
        c'.x = RunClauses_eA e c.x ∧ c'.y = RunClauses_eA e c.y) := by
  obtain ⟨c', hc', hr⟩ := RunClauses_iso_mem h hc
  obtain ⟨hk, -, -, hxy, hrd⟩ := RunClauses_swapR_eq hr
  exact ⟨c', hc', hk, hxy, fun h' => by rw [hrd h']; exact ⟨rfl, rfl⟩⟩

private theorem RunClauses_iso_diffTo (h : RunClauses_Iso e Γ Γ') (a : Fin 3)
    (hd : Γ.DiffToPinned (.inl a)) : Γ'.DiffToPinned (.inl a) := by
  intro c' hc' hdf
  obtain ⟨c, hc, hk, -, hxy⟩ := RunClauses_iso_ends' h hc'
  rw [hk] at hdf
  obtain ⟨h1, h2⟩ := hxy (Or.inr hdf)
  have := hd c hc hdf
  rw [h1, h2, ← RunClauses_eA_inl e a, (RunClauses_eA e).injective.eq_iff,
    (RunClauses_eA e).injective.eq_iff, RunClauses_iso_unpinned h, RunClauses_iso_unpinned h]
  exact this

private theorem RunClauses_iso_hasDiff (h : RunClauses_Iso e Γ Γ') (a : Fin 3)
    (hd : Γ.HasDiffToPinned (.inl a)) : Γ'.HasDiffToPinned (.inl a) := by
  obtain ⟨c, hc, hdf, hor⟩ := hd
  obtain ⟨c', hc', hk, -, hxy⟩ := RunClauses_iso_ends h hc
  obtain ⟨h1, h2⟩ := hxy (Or.inr hdf)
  refine ⟨c', hc', hk ▸ hdf, ?_⟩
  rw [h1, h2, ← RunClauses_eA_inl e a, (RunClauses_eA e).injective.eq_iff,
    (RunClauses_eA e).injective.eq_iff, RunClauses_iso_unpinned h, RunClauses_iso_unpinned h]
  exact hor

private theorem RunClauses_iso_ext (h : RunClauses_Iso e Γ Γ') (hE : Γ.ExtClause) :
    Γ'.ExtClause := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hE
  have hU : ∀ a : Fin 3, Γ'.Unpinned (.inl a) ↔ Γ.Unpinned (.inl a) := fun a =>
    RunClauses_iso_unpinned h (.inl a)
  refine ⟨fun u' v' huv hb => ?_, fun c' hc' hk => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · obtain ⟨u, rfl⟩ := (RunClauses_eA e).surjective u'
    obtain ⟨v, rfl⟩ := (RunClauses_eA e).surjective v'
    obtain ⟨b, hb'⟩ := x1 u v (fun h' => huv (by rw [h']))
      ((RunClauses_iso_sameBlock h u v).1 hb)
    exact ⟨e b, (RunClauses_iso_sameBlock h u (.inr b)).2 hb'⟩
  · obtain ⟨c, hc, hk', hxy, -⟩ := RunClauses_iso_ends' h hc'
    have := x2 c hc (hk' ▸ hk)
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2, RunClauses_iso_unpinned h, RunClauses_iso_unpinned h]
    · exact this
    · exact fun h' => this ⟨h'.2, h'.1⟩
  · rw [hU] at h0
    exact ⟨RunClauses_iso_hasDiff h 0 (x3 h0).1, RunClauses_iso_diffTo h 0 (x3 h0).2⟩
  · rw [hU] at h0
    refine ⟨fun c' hc' hdf => ?_, ?_⟩
    · obtain ⟨c, hc, hk, -, hxy⟩ := RunClauses_iso_ends' h hc'
      rw [hk] at hdf
      obtain ⟨h1, h2⟩ := hxy (Or.inr hdf)
      obtain ⟨n1, n2⟩ := (x4 h0).1 c hc hdf
      rw [h1, h2, ← RunClauses_eA_inl e 2, (RunClauses_eA e).injective.ne_iff,
        (RunClauses_eA e).injective.ne_iff]
      exact ⟨n1, n2⟩
    · rw [← RunClauses_eA_inl e 2, RunClauses_iso_deg h]
      exact (x4 h0).2
  · rw [hU] at h0
    refine ⟨?_, RunClauses_iso_diffTo h 1 (x5 h0).2.1, ?_⟩
    · rcases (x5 h0).1 with ⟨c, hc, hk, hat⟩ | hd
      · obtain ⟨c', hc', hk', -, hxy⟩ := RunClauses_iso_ends h hc
        obtain ⟨h1, h2⟩ := hxy (Or.inl (by rw [hk]; rfl))
        refine Or.inl ⟨c', hc', hk'.trans hk, ?_⟩
        rw [h1, h2, ← RunClauses_eA_inl e 1, (RunClauses_eA e).injective.eq_iff,
          (RunClauses_eA e).injective.eq_iff]
        exact hat
      · exact Or.inr (RunClauses_iso_hasDiff h 1 hd)
    · rw [← RunClauses_eA_inl e 1, RunClauses_iso_deg h]
      exact (x5 h0).2.2

private theorem RunClauses_iso_qGraph (h : RunClauses_Iso e Γ Γ') (hQ : Γ.IsQGraph) :
    Γ'.IsQGraph := by
  obtain ⟨u, ⟨c, hc, hl⟩, hall⟩ := hQ
  refine ⟨RunClauses_eA e u, ?_, fun c' hc' hor => ?_⟩
  · obtain ⟨c', hc', hr⟩ := RunClauses_iso_mem h hc
    refine ⟨c', hc', ?_⟩
    rw [(RunClauses_swapR_eq hr).2.1]
    simp [Comp.map, hl]
  · obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    obtain ⟨hk, hlab, -⟩ := RunClauses_swapR_eq hr
    rw [hk, hlab] at hor
    rw [hlab]
    have : c.label = some (.Q, u) := hall c hc (by
      simpa [Comp.map, Option.isSome_map] using hor)
    simp [Comp.map, this]

private theorem RunClauses_iso_ord (h : RunClauses_Iso e Γ Γ') : Γ'.ord = Γ.ord := by
  unfold Graph.ord
  have hm : ((m' : ℕ) : ℤ) = (m : ℤ) := by rw [RunClauses_iso_card h]
  rw [(RunClauses_iso_map h (fun c => c.kind.ord)
    (fun c c' hr => by rw [(RunClauses_swapR_eq hr).1])).sum_eq, hm]
  rfl

private theorem RunClauses_iso_dotExcess (h : RunClauses_Iso e Γ Γ') :
    Γ'.dotExcess = Γ.dotExcess := by
  unfold Graph.dotExcess Graph.nDots
  have h1 := RunClauses_iso_count h (fun c => decide (c.kind = .dot))
    (fun c c' hr => by rw [(RunClauses_swapR_eq hr).1])
  have h2 : Nat.card Γ'.dotGraph.ConnectedComponent = Nat.card Γ.dotGraph.ConnectedComponent :=
    (Nat.card_congr (RunClauses_isoG h (fun κ => κ = .dot)).connectedComponentEquiv).symm
  have hm : (((3 + m' : ℕ)) : ℤ) = ((3 + m : ℕ) : ℤ) := by rw [RunClauses_iso_card h]
  rw [h1, h2, hm]
  rfl

private theorem RunClauses_iso_paperOrd (h : RunClauses_Iso e Γ Γ') :
    Γ'.paperOrd = Γ.paperOrd := by
  unfold Graph.paperOrd
  rw [RunClauses_iso_ord h, RunClauses_iso_dotExcess h]

private theorem RunClauses_edgeGraph_eq {k n : ℕ} (G : Graph k n) :
    G.edgeGraph = RunClauses_G G.comps (fun _ => True) := by
  unfold Graph.edgeGraph RunClauses_G
  simp only [true_and]

private theorem RunClauses_iso_normal {C : ℕ} (h : RunClauses_Iso e Γ Γ') (hN : Γ.Normal C) :
    Γ'.Normal C := by
  obtain ⟨⟨hs, hc, hi, hd⟩, hsol, hx⟩ := hN
  have hsx : ∀ (P : Kind → Prop) (u v : Atom 3 m),
      (∃ c ∈ Γ'.comps, P c.kind ∧ (c.x = RunClauses_eA e u ∧ c.y = RunClauses_eA e v ∨
        c.x = RunClauses_eA e v ∧ c.y = RunClauses_eA e u)) ↔
      (∃ c ∈ Γ.comps, P c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) := by
    intro P u v
    have := RunClauses_iso_ex h P s(u, v)
    simp only [Sym2.map_mk, Sym2.eq_iff] at this
    exact this
  refine ⟨⟨?_, ?_, fun a b => ?_, fun c' hc' hk => ?_⟩, fun c' hc' hk => ?_, fun u' v' huv => ?_⟩
  · rw [RunClauses_iso_length h, RunClauses_iso_card h]
    exact hs
  · rw [RunClauses_edgeGraph_eq] at hc ⊢
    exact (RunClauses_isoG h _).preconnected_iff.1 hc
  · obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    exact (RunClauses_iso_reach h
      (fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) (.inr a') (.inr b')).2
      (hi a' b')
  · obtain ⟨c, hc, hk', hxy, -⟩ := RunClauses_iso_ends' h hc'
    have := hd c hc (hk' ▸ hk)
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, RunClauses_eA_isLeft, RunClauses_eA_isLeft]
    · exact this
    · exact this.symm
  · obtain ⟨c, hc, hk', -, hxy⟩ := RunClauses_iso_ends' h hc'
    have hr : c.kind.isRandom = true := by
      rw [hk'] at hk
      revert hk
      cases c.kind <;> simp [Kind.isSolid, Kind.isRandom]
    obtain ⟨h1, h2⟩ := hxy (Or.inl hr)
    rw [h1, h2, (RunClauses_eA e).injective.ne_iff]
    exact hsol c hc (hk' ▸ hk)
  · obtain ⟨u, rfl⟩ := (RunClauses_eA e).surjective u'
    obtain ⟨v, rfl⟩ := (RunClauses_eA e).surjective v'
    rw [hsx (fun κ => κ = .xdot), hsx (fun κ => κ.isSolid = true)]
    exact hx u v (fun h' => huv (by rw [h']))

/-- Two atoms of one block that are equal or both internal lie in one molecule. -/
private theorem RunClauses_molRep_of_block {k n : ℕ} (G : Graph k n) {a b : Atom k n}
    (hb : G.SameBlock a b) (hor : a = b ∨ (a.isRight = true ∧ b.isRight = true)) :
    G.molRep a = G.molRep b := by
  rw [Local_molRep_eq_iff]
  rcases hor with rfl | ⟨ha, hb'⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨ha, hb', hb.mono (Local_dot_le_mol G)⟩

private theorem RunClauses_iso_molRep (h : RunClauses_Iso e Γ Γ') (u : Atom 3 m) :
    Γ'.molRep (RunClauses_eA e (Γ.molRep u)) = Γ'.molRep (RunClauses_eA e u) := by
  rw [Local_molRep_eq_iff, RunClauses_iso_sameMol h]
  exact Γ.sameMol_equivalence.symm (Local_molRep_spec Γ u)

private theorem RunClauses_iso_rho (h : RunClauses_Iso e Γ Γ') (u : Atom 3 m) :
    Local_rho Γ' (RunClauses_eA e u) = Γ'.molRep (RunClauses_eA e (Local_rho Γ u)) := by
  unfold Local_rho
  rw [RunClauses_iso_molRep h]
  refine RunClauses_molRep_of_block Γ' ?_ ?_
  · refine ((Local_flat_block Γ' _).symm).trans ?_
    exact (RunClauses_iso_sameBlock h u _).2 (Local_flat_block Γ u)
  · by_cases hU : Γ.Unpinned u
    · left
      rw [Local_flat_unpinned hU, Local_flat_unpinned ((RunClauses_iso_unpinned h u).2 hU)]
    · right
      refine ⟨Local_flat_isRight (fun h' => hU ((RunClauses_iso_unpinned h u).1 h')), ?_⟩
      rw [RunClauses_eA_isRight]
      exact Local_flat_isRight hU

/-- `spdPM'` of a graph without ghost edges passes to a graph equal up to names and order. -/
private theorem RunClauses_iso_spd (h : RunClauses_Iso e Γ Γ') (hG : Γ.NoGhost)
    (hs : spdPM' Γ) : spdPM' Γ' := by
  set F : Atom 3 m → Atom 3 m' := fun v => Γ'.molRep (RunClauses_eA e v) with hFdef
  have hFmol : ∀ v, F (Γ.molRep v) = F v := RunClauses_iso_molRep h
  have hfix : ∀ v ∈ (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext : Set (Atom 3 m)), Γ.molRep v = v := by
    intro v hv
    rcases hv with hv | hv
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      exact Local_molRep_idem Γ _
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hv
      rfl
  have hinj : Set.InjOn F (↑Γ.toMG'.int ∪ ↑Γ.toMG'.ext) := by
    intro v hv w hw hvw
    rw [← hfix v hv, ← hfix w hw, Local_molRep_eq_iff, ← RunClauses_iso_sameMol h,
      ← Local_molRep_eq_iff]
    exact hvw
  have hpin : ∀ a, Local_Same (Local_edMap F (Local_pin Γ a)) (Local_pin Γ' a) := by
    intro a
    have hU := RunClauses_iso_unpinned h (.inl a)
    unfold Local_pin
    rcases h1 : Γ.anchor (.inl a) with - | b <;> rcases h2 : Γ'.anchor (.inl a) with - | b'
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd (Local_anchor_some h2) ((hU.2 ⟨rfl, Local_anchor_none.1 h1⟩).2 b')
    · exact absurd (Local_anchor_some h1) ((hU.1 ⟨rfl, Local_anchor_none.1 h2⟩).2 b)
    · right
      refine ⟨rfl, Or.inl ?_⟩
      show (Γ'.molRep (.inr b'), (.inl a : Atom 3 m')) = (F (Γ.molRep (.inr b)), F (.inl a))
      rw [hFmol]
      refine Prod.ext ?_ rfl
      have hbl : Γ'.SameBlock (.inr b') (RunClauses_eA e (.inr b)) :=
        (Local_anchor_some h2).symm.trans
          ((RunClauses_iso_sameBlock h (.inl a) (.inr b)).2 (Local_anchor_some h1))
      exact RunClauses_molRep_of_block Γ' hbl (Or.inr ⟨rfl, rfl⟩)
  have c1 := Local_ELG_mapV (Pn := Fin 3) (pe' := Local_pin Γ') F (Γ.comps.map (Local_rd Γ))
    hinj hpin (Local_rdL_vok Γ Γ.comps) (Local_pin_vok Γ)
  have hI : Γ.toMG'.int.image F = Γ'.toMG'.int := by
    ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨e a, by rw [hFmol]; rfl⟩
    · rintro ⟨a', rfl⟩
      refine ⟨Γ.molRep (.inr (e.symm a')), ⟨_, rfl⟩, ?_⟩
      rw [hFmol]
      simp [hFdef, RunClauses_eA_inr]
  have hX : Γ.toMG'.ext.image F = Γ'.toMG'.ext := by
    ext v
    simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨.inl a, ⟨a, rfl⟩, rfl⟩
  have hL : (Γ.comps.map (Local_rd Γ)).map (Local_edMap F) =
      (Γ.comps.map (Comp.map (RunClauses_eA e))).map (Local_rd Γ') := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    have key : Γ'.molRep (RunClauses_eA e (Local_rho Γ c.x)) =
        Γ'.molRep (RunClauses_eA e (Local_rho Γ c.y)) ↔ Local_rho Γ c.x = Local_rho Γ c.y :=
      hinj.eq_iff (Local_rho_vtx Γ _) (Local_rho_vtx Γ _)
    simp only [Function.comp_apply, Local_rd, Local_edMap, Comp.map, RunClauses_iso_rho h, key]
    rfl
  rw [hI, hX, hL] at c1
  obtain ⟨-, cs, h1, h2⟩ := id h
  have c2 : Local_Carry (Local_RG Γ' (Γ.comps.map (Comp.map (RunClauses_eA e))))
      (Local_RG Γ' cs) id := by
    refine Local_RG_same Γ' (h1.imp fun c c' hr => ?_)
    rcases hr with rfl | ⟨hk, rfl⟩
    · exact Local_Same.refl _
    · right
      refine ⟨?_, Or.inr rfl⟩
      simp only [Local_rd, @eq_comm _ (Local_rho Γ' c.y)]
  have hc := Local_carry_trans (Local_carry_trans (Local_carry_trans
    (Local_carry_trans (Local_carry_toRG Γ) c1) c2) (Local_RG_perm Γ' h2)) (Local_carry_ofRG Γ')
  exact (hc (Graph.toMG'_disjoint Γ) (Graph.toMG'_noGhost Γ hG) hs).1

private theorem RunClauses_f2_filterMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → Option γ} {g : β → Option δ}
    (hfg : ∀ a b, R a b →
      (f a = none ∧ g b = none) ∨ ∃ x y, f a = some x ∧ g b = some y ∧ S x y) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S (l₁.filterMap f) (l₂.filterMap g)
  | _, _, .nil => .nil
  | _, _, .cons hab h => by
    rcases hfg _ _ hab with ⟨h1, h2⟩ | ⟨x, y, h1, h2, h3⟩
    · rw [List.filterMap_cons_none h1, List.filterMap_cons_none h2]
      exact RunClauses_f2_filterMap hfg h
    · rw [List.filterMap_cons_some h1, List.filterMap_cons_some h2]
      exact .cons h3 (RunClauses_f2_filterMap hfg h)

private theorem RunClauses_map_map {U V W : Type} (c : Comp U) (g : U → V) (h : V → W) :
    (c.map g).map h = c.map (h ∘ g) := by
  cases c with
  | mk κ x y mi l =>
    simp only [Comp.map, List.map_map, Option.map_map, Prod.map_comp_map, Function.id_comp]
    rfl

/-- The component with its two atoms exchanged. -/
private def RunClauses_sw {V : Type} (d : Comp V) : Comp V := { d with x := d.y, y := d.x }

private theorem RunClauses_comp_eq {V : Type} {a b : Comp V} (h1 : a.kind = b.kind)
    (h2 : a.x = b.x) (h3 : a.y = b.y) (h4 : a.minor = b.minor) (h5 : a.label = b.label) :
    a = b := by
  cases a
  cases b
  simp_all

/-- `O_merge` of graphs equal up to names and order: the results are equal up to names and
order. -/
private theorem RunClauses_iso_mergeT {G : Graph 3 m} {G' : Graph 3 m'} (h : RunClauses_Iso e G G')
    {t' : Tracked 3 m'} (ht' : G'.mergeT = some t') :
    ∃ t, G.mergeT = some t ∧ ∃ σ : Fin t.nOut ≃ Fin t'.nOut, RunClauses_Iso σ t.g t'.g := by
  obtain ⟨Sc', Sk', -, Sl', -, Sr', Se', Sn', Sx'⟩ := Local_mergeT_spec ht'
  have hrep : ∀ u v, Local_mrep G' (RunClauses_eA e u) = Local_mrep G' (RunClauses_eA e v) ↔
      Local_mrep G u = Local_mrep G v := by
    intro u v
    rw [Local_mrep_iff, Local_mrep_iff, RunClauses_iso_sameBlock h]
  obtain ⟨t, ht⟩ : ∃ t, G.mergeT = some t := by
    rcases hm : G.mergeT with - | t
    · exfalso
      obtain ⟨c, hc, hk, hr⟩ := Local_mergeT_none hm
      obtain ⟨c', hc', hk', hxy, -⟩ := RunClauses_iso_ends h hc
      refine Sx' c' hc' (hk'.trans hk) ?_
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact (hrep _ _).2 hr
      · exact ((hrep _ _).2 hr).symm
    · exact ⟨t, rfl⟩
  obtain ⟨Sc, Sk, -, Sl, -, ⟨g, hg, hgs⟩, Se, Sn, -⟩ := Local_mergeT_spec ht
  refine ⟨t, ht, ?_⟩
  obtain ⟨g', hg', hgs'⟩ := Sr'
  have k1 : ∀ i j : Fin m, g i = g j ↔ Local_mrep G (.inr i) = Local_mrep G (.inr j) := by
    intro i j
    constructor
    · intro hij
      by_contra hne
      exact Sn _ _ hne (by rw [hg, hg, hij])
    · intro hr
      have := Se _ _ hr rfl rfl
      rw [hg, hg] at this
      exact Sum.inr_injective this
  have k2 : ∀ i j : Fin m', g' i = g' j ↔ Local_mrep G' (.inr i) = Local_mrep G' (.inr j) := by
    intro i j
    constructor
    · intro hij
      by_contra hne
      exact Sn' _ _ hne (by rw [hg', hg', hij])
    · intro hr
      have := Se' _ _ hr rfl rfl
      rw [hg', hg'] at this
      exact Sum.inr_injective this
  have hff : ∀ i j : Fin m, g' (e i) = g' (e j) ↔ g i = g j := by
    intro i j
    rw [k1, k2]
    exact hrep (.inr i) (.inr j)
  let σf : Fin t.nOut → Fin t'.nOut := fun j => g' (e (Function.surjInv hgs j))
  have hσ : ∀ i, σf (g i) = g' (e i) := fun i => (hff _ _).2 (Function.surjInv_eq hgs (g i))
  have hinj : Function.Injective σf := by
    intro j₁ j₂ hj
    obtain ⟨i₁, rfl⟩ := hgs j₁
    obtain ⟨i₂, rfl⟩ := hgs j₂
    rw [hσ, hσ] at hj
    exact (hff _ _).1 hj
  have hsurj : Function.Surjective σf := by
    intro k
    obtain ⟨i', rfl⟩ := hgs' k
    exact ⟨g (e.symm i'), by rw [hσ, Equiv.apply_symm_apply]⟩
  let σ : Fin t.nOut ≃ Fin t'.nOut := Equiv.ofBijective σf ⟨hinj, hsurj⟩
  have hat : ∀ u, t'.f (RunClauses_eA e u) = RunClauses_eA σ (t.f u) := by
    intro u
    cases u with
    | inl a => rw [RunClauses_eA_inl, Sl', Sl]; rfl
    | inr i =>
      rw [RunClauses_eA_inr, hg', hg, RunClauses_eA_inr]
      exact congrArg Sum.inr (hσ i).symm
  have hcomp : t'.f ∘ RunClauses_eA e = RunClauses_eA σ ∘ t.f := funext hat
  have hfeq : ∀ u v, t'.f (RunClauses_eA e u) = t'.f (RunClauses_eA e v) ↔ t.f u = t.f v := by
    intro u v
    rw [hat, hat]
    exact (RunClauses_eA σ).injective.eq_iff
  have hmm : ∀ c : Comp (Atom 3 m),
      (c.map (RunClauses_eA e)).map t'.f = (c.map t.f).map (RunClauses_eA σ) := by
    intro c
    rw [RunClauses_map_map, RunClauses_map_map, hcomp]
  have hmin : ∀ L : List (Atom 3 m),
      (L.map (RunClauses_eA e)).map t'.f = (L.map t.f).map (RunClauses_eA σ) := by
    intro L
    rw [List.map_map, List.map_map, hcomp]
  have hlab : ∀ l : Option (PQ × Atom 3 m), (l.map (Prod.map id (RunClauses_eA e))).map
      (Prod.map id t'.f) = (l.map (Prod.map id t.f)).map (Prod.map id (RunClauses_eA σ)) := by
    intro l
    cases l with
    | none => rfl
    | some p =>
      obtain ⟨a, b⟩ := p
      simp [hat]
  refine ⟨σ, ?_, ?_⟩
  · rw [Sk', Sk, h.1]
  obtain ⟨-, cs, h1, h2⟩ := h
  refine ⟨cs.filterMap (Local_mergeComp (Local_mrep G') t'.f), ?_, ?_⟩
  · rw [Sc, List.map_filterMap]
    refine RunClauses_f2_filterMap ?_ (List.forall₂_map_left_iff.1 h1)
    intro c c' hr
    have e1 : (t'.f (c.map (RunClauses_eA e)).x == t'.f (c.map (RunClauses_eA e)).y) =
        (t.f c.x == t.f c.y) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact hfeq c.x c.y
    have e2 : (Local_mrep G' (c.map (RunClauses_eA e)).x ==
        Local_mrep G' (c.map (RunClauses_eA e)).y) = (Local_mrep G c.x == Local_mrep G c.y) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact hrep c.x c.y
    have ek : (c.map (RunClauses_eA e)).kind = c.kind := rfl
    have fin : ∀ (φ : Comp (Atom 3 t.nOut) → Comp (Atom 3 t'.nOut)) (c₁ : Comp (Atom 3 m')),
        (∀ d, Local_mergeComp (Local_mrep G) t.f c = some d →
          RunClauses_SwapR (d.map (RunClauses_eA σ)) (φ d)) →
        Local_mergeComp (Local_mrep G') t'.f c₁ = (Local_mergeComp (Local_mrep G) t.f c).map φ →
        ((Local_mergeComp (Local_mrep G) t.f c).map (Comp.map (RunClauses_eA σ)) = none ∧
          Local_mergeComp (Local_mrep G') t'.f c₁ = none) ∨
        ∃ x y, (Local_mergeComp (Local_mrep G) t.f c).map (Comp.map (RunClauses_eA σ)) = some x ∧
          Local_mergeComp (Local_mrep G') t'.f c₁ = some y ∧ RunClauses_SwapR x y := by
      intro φ c₁ hφ hl
      rw [hl]
      rcases hmc : Local_mergeComp (Local_mrep G) t.f c with - | d
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨_, _, rfl, rfl, hφ d hmc⟩
    rcases hr with rfl | ⟨hk, rfl⟩
    · refine fin (Comp.map (RunClauses_eA σ)) _ (fun d _ => Or.inl rfl) ?_
      unfold Local_mergeComp
      rw [e1, e2, ek]
      by_cases H1 : (c.kind == .dot && t.f c.x == t.f c.y) = true
      · simp only [H1, if_true, Option.map_none]
      · by_cases H2 : (c.kind.isSolid && Local_mrep G c.x == Local_mrep G c.y) = true
        · simp only [H1, H2, if_true, if_false, Bool.false_eq_true, Option.map_some]
          congr 1
          refine RunClauses_comp_eq rfl ?_ ?_ ?_ ?_ <;> simp [Comp.map, hat, hmin, hlab]
        · simp only [H1, H2, if_false, Bool.false_eq_true, Option.map_some]
          exact congrArg some (hmm c)
    · rw [ek] at hk
      have hs : c.kind.isSolid = false := by
        rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
      have e1' : (t'.f (c.map (RunClauses_eA e)).y == t'.f (c.map (RunClauses_eA e)).x) =
          (t.f c.x == t.f c.y) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
        exact hfeq c.x c.y
      refine fin (fun d => RunClauses_sw (d.map (RunClauses_eA σ))) _ (fun d hd => ?_) ?_
      · refine Or.inr ⟨?_, rfl⟩
        unfold Local_mergeComp at hd
        simp only [hs, Bool.false_and, Bool.false_eq_true, if_false] at hd
        split_ifs at hd
        obtain rfl := Option.some.inj hd
        exact hk
      unfold Local_mergeComp
      dsimp only
      simp only [ek, hs, e1', Bool.false_and, Bool.false_eq_true, if_false]
      by_cases H1 : (c.kind == .dot && t.f c.x == t.f c.y) = true
      · simp only [H1, if_true, Option.map_none]
      · simp only [H1, if_false, Bool.false_eq_true, Option.map_some]
        congr 1
        refine RunClauses_comp_eq rfl ?_ ?_ ?_ ?_ <;> simp [Comp.map, hat, hmin, hlab, RunClauses_sw]
  · rw [Sc']
    exact h2.filterMap _

/-! ### The pairs of `Graph.splitPairs` -/

/-- The unordered pair of the two atoms of a pair. -/
private def RunClauses_sk {V : Type} (p : V × V) : Sym2 V := s(p.1, p.2)

/-- The key of a pair of `Graph.splitPairs`: the unordered pair of its atoms and its flag. -/
private def RunClauses_key {V : Type} (p : V × V × Bool) : Sym2 V × Bool := (s(p.1, p.2.1), p.2.2)

/-- The image of a key along the bijection of the atoms. -/
private def RunClauses_kmap (e : Fin m ≃ Fin m') (q : Sym2 (Atom 3 m) × Bool) :
    Sym2 (Atom 3 m') × Bool :=
  (q.1.map (RunClauses_eA e), q.2)

/-- The image of a pair along the bijection of the atoms. -/
private def RunClauses_pmap (e : Fin m ≃ Fin m') (p : Atom 3 m × Atom 3 m × Bool) :
    Atom 3 m' × Atom 3 m' × Bool :=
  (RunClauses_eA e p.1, RunClauses_eA e p.2.1, p.2.2)

private theorem RunClauses_kmap_inj (e : Fin m ≃ Fin m') :
    Function.Injective (RunClauses_kmap e) := by
  rintro ⟨z₁, b₁⟩ ⟨z₂, b₂⟩ h
  simp only [RunClauses_kmap, Prod.mk.injEq] at h
  rw [Sym2.map.injective (RunClauses_eA e).injective h.1, h.2]

/-- Two atoms joined by a component of a kind in `p`. -/
private def RunClauses_joined {k n : ℕ} (G : Graph k n) (p : Kind → Bool) (u v : Atom k n) :
    Bool :=
  G.comps.any fun c => p c.kind && ((c.x == u && c.y == v) || (c.x == v && c.y == u))

private theorem RunClauses_joined_iff {k n : ℕ} (G : Graph k n) (p : Kind → Bool)
    (u v : Atom k n) : RunClauses_joined G p u v = true ↔
      ∃ c ∈ G.comps, p c.kind = true ∧ s(c.x, c.y) = s(u, v) := by
  unfold RunClauses_joined
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Sym2.eq_iff]

private theorem RunClauses_joined_symm {k n : ℕ} (G : Graph k n) (p : Kind → Bool)
    (u v : Atom k n) : RunClauses_joined G p u v = RunClauses_joined G p v u := by
  rw [Bool.eq_iff_iff, RunClauses_joined_iff, RunClauses_joined_iff, Sym2.eq_swap]

private theorem RunClauses_iso_joined (h : RunClauses_Iso e Γ Γ') (p : Kind → Bool)
    (u v : Atom 3 m) : RunClauses_joined Γ' p (RunClauses_eA e u) (RunClauses_eA e v) =
      RunClauses_joined Γ p u v := by
  rw [Bool.eq_iff_iff, RunClauses_joined_iff, RunClauses_joined_iff, ← Sym2.map_mk]
  exact RunClauses_iso_ex h (fun κ => p κ = true) s(u, v)

/-- `RunClauses_joined` on unordered pairs. -/
private def RunClauses_jl {k n : ℕ} (G : Graph k n) (p : Kind → Bool) : Sym2 (Atom k n) → Bool :=
  Sym2.lift ⟨RunClauses_joined G p, RunClauses_joined_symm G p⟩

private theorem RunClauses_iso_jl (h : RunClauses_Iso e Γ Γ') (p : Kind → Bool)
    (z : Sym2 (Atom 3 m)) : RunClauses_jl Γ' p (z.map (RunClauses_eA e)) = RunClauses_jl Γ p z := by
  induction z using Sym2.ind with
  | _ u v =>
    rw [Sym2.map_mk]
    unfold RunClauses_jl
    rw [Sym2.lift_mk, Sym2.lift_mk]
    exact RunClauses_iso_joined h p u v

/-- One step of the removal of repeated unordered pairs in `Graph.splitPairs`. -/
private def RunClauses_step {k n : ℕ} (acc : List (Atom k n × Atom k n)) (p : Atom k n × Atom k n) :
    List (Atom k n × Atom k n) :=
  if acc.any (fun q => q == p || q == p.swap) then acc else acc ++ [p]

/-- The candidate pairs of `Graph.splitPairs`. -/
private def RunClauses_cand {k n : ℕ} (G : Graph k n) : List (Atom k n × Atom k n) :=
  G.comps.filterMap fun c =>
    if (c.kind.isSolid || c.kind == .xdot) && c.x != c.y then some (c.x, c.y) else none

/-- The key of the pair of `Graph.splitPairs` on an unordered pair. -/
private def RunClauses_G3 {k n : ℕ} (G : Graph k n) (z : Sym2 (Atom k n)) :
    Option (Sym2 (Atom k n) × Bool) :=
  if RunClauses_jl G Kind.isSolid z != RunClauses_jl G (· == .xdot) z then
    some (z, RunClauses_jl G Kind.isSolid z) else none

private theorem RunClauses_sp_key {k n : ℕ} (G : Graph k n) :
    G.splitPairs.map RunClauses_key =
      (((RunClauses_cand G).foldl RunClauses_step []).map RunClauses_sk).filterMap (RunClauses_G3 G) := by
  rw [show G.splitPairs = ((RunClauses_cand G).foldl RunClauses_step []).filterMap (fun p =>
      if RunClauses_joined G Kind.isSolid p.1 p.2 != RunClauses_joined G (· == .xdot) p.1 p.2 then
        some (p.1, p.2, RunClauses_joined G Kind.isSolid p.1 p.2) else none) from rfl]
  rw [List.map_filterMap, List.filterMap_map]
  refine List.filterMap_congr fun p _ => ?_
  obtain ⟨u, v⟩ := p
  simp only [Function.comp_apply, RunClauses_G3, RunClauses_jl]
  change _ = if Sym2.lift _ s(u, v) != Sym2.lift _ s(u, v) then _ else _
  rw [Sym2.lift_mk, Sym2.lift_mk]
  unfold RunClauses_joined
  split_ifs <;> rfl

private theorem RunClauses_fold {k n : ℕ} : ∀ (l acc : List (Atom k n × Atom k n)),
    (acc.map RunClauses_sk).Nodup →
      ((l.foldl RunClauses_step acc).map RunClauses_sk).Nodup ∧
        ∀ z, z ∈ (l.foldl RunClauses_step acc).map RunClauses_sk ↔
          z ∈ acc.map RunClauses_sk ∨ z ∈ l.map RunClauses_sk
  | [], acc, h => ⟨h, fun z => by simp⟩
  | p :: l, acc, h => by
    have hstep : (acc.any fun q => q == p || q == p.swap) = true ↔
        RunClauses_sk p ∈ acc.map RunClauses_sk := by
      simp only [List.any_eq_true, List.mem_map, Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨q, hq, h'⟩
        exact ⟨q, hq, (Sym2.mk_eq_mk_iff (p := q) (q := p)).2 h'⟩
      · rintro ⟨q, hq, h'⟩
        exact ⟨q, hq, (Sym2.mk_eq_mk_iff (p := q) (q := p)).1 h'⟩
    rw [List.foldl_cons]
    by_cases hp : RunClauses_sk p ∈ acc.map RunClauses_sk
    · have e1 : RunClauses_step acc p = acc := by
        unfold RunClauses_step
        rw [if_pos (hstep.2 hp)]
      rw [e1]
      obtain ⟨h1, h2⟩ := RunClauses_fold l acc h
      refine ⟨h1, fun z => ?_⟩
      rw [h2, List.map_cons, List.mem_cons]
      constructor
      · rintro (h' | h')
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · rintro (h' | rfl | h')
        · exact Or.inl h'
        · exact Or.inl hp
        · exact Or.inr h'
    · have e1 : RunClauses_step acc p = acc ++ [p] := by
        unfold RunClauses_step
        rw [if_neg (fun h' => hp (hstep.1 h'))]
      rw [e1]
      have hnd : ((acc ++ [p]).map RunClauses_sk).Nodup := by
        rw [List.map_append, List.map_singleton]
        exact h.append (List.nodup_singleton _) (by simpa using hp)
      obtain ⟨h1, h2⟩ := RunClauses_fold l (acc ++ [p]) hnd
      refine ⟨h1, fun z => ?_⟩
      rw [h2, List.map_cons, List.mem_cons, List.map_append, List.mem_append, List.map_singleton,
        List.mem_singleton]
      tauto

private theorem RunClauses_mem_cand {k n : ℕ} (G : Graph k n) (z : Sym2 (Atom k n)) :
    z ∈ (RunClauses_cand G).map RunClauses_sk ↔ ¬ z.IsDiag ∧
      ∃ c ∈ G.comps, (c.kind.isSolid || c.kind == .xdot) = true ∧ s(c.x, c.y) = z := by
  unfold RunClauses_cand
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
    obtain ⟨c, hc, hfc⟩ := List.mem_filterMap.1 hp
    split_ifs at hfc with hcond
    obtain rfl := Option.some.inj hfc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
    exact ⟨by simp only [RunClauses_sk, Sym2.mk_isDiag_iff]; exact hcond.2, c, hc, hcond.1, rfl⟩
  · rintro ⟨hd, c, hc, hk, rfl⟩
    refine List.mem_map.2 ⟨(c.x, c.y), List.mem_filterMap.2 ⟨c, hc, ?_⟩, rfl⟩
    rw [if_pos]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨hk, fun h' => hd (Sym2.mk_isDiag_iff.2 h')⟩

private theorem RunClauses_iso_cand (h : RunClauses_Iso e Γ Γ') (z : Sym2 (Atom 3 m)) :
    z.map (RunClauses_eA e) ∈ (RunClauses_cand Γ').map RunClauses_sk ↔
      z ∈ (RunClauses_cand Γ).map RunClauses_sk := by
  rw [RunClauses_mem_cand, RunClauses_mem_cand, Sym2.isDiag_map (RunClauses_eA e).injective,
    RunClauses_iso_ex h (fun κ => (κ.isSolid || κ == .xdot) = true)]

private theorem RunClauses_sp_nodup {k n : ℕ} (G : Graph k n) :
    (G.splitPairs.map RunClauses_key).Nodup := by
  rw [RunClauses_sp_key]
  have k : ∀ z b, b ∈ RunClauses_G3 G z → b.1 = z := by
    intro z b hb
    unfold RunClauses_G3 at hb
    split_ifs at hb
    · simp only [Option.mem_def, Option.some.injEq] at hb
      rw [← hb]
    · simp at hb
  refine List.Nodup.filterMap (fun a a' b hb hb' => ?_)
    (RunClauses_fold _ [] List.nodup_nil).1
  rw [← k a b hb, ← k a' b hb']

/-- The keys of the pairs of `Graph.splitPairs` of `Γ'` are the images of those of `Γ`. -/
private theorem RunClauses_iso_sp (h : RunClauses_Iso e Γ Γ') :
    (Γ'.splitPairs.map RunClauses_key).Perm
      ((Γ.splitPairs.map RunClauses_key).map (RunClauses_kmap e)) := by
  refine (List.perm_ext_iff_of_nodup (RunClauses_sp_nodup Γ')
    ((RunClauses_sp_nodup Γ).map (RunClauses_kmap_inj e))).2 fun q => ?_
  rw [RunClauses_sp_key, RunClauses_sp_key, List.mem_filterMap, List.mem_map]
  simp only [List.mem_filterMap]
  have f1 := fun (G : Graph 3 m') (z : Sym2 (Atom 3 m')) =>
    (RunClauses_fold (RunClauses_cand G) [] List.nodup_nil).2 z
  have f2 := fun (G : Graph 3 m) (z : Sym2 (Atom 3 m)) =>
    (RunClauses_fold (RunClauses_cand G) [] List.nodup_nil).2 z
  simp only [List.map_nil, List.not_mem_nil, false_or] at f1 f2
  have hG3 : ∀ z : Sym2 (Atom 3 m), RunClauses_G3 Γ' (z.map (RunClauses_eA e)) =
      (RunClauses_G3 Γ z).map (RunClauses_kmap e) := by
    intro z
    unfold RunClauses_G3
    rw [RunClauses_iso_jl h, RunClauses_iso_jl h]
    split_ifs <;> rfl
  constructor
  · rintro ⟨w', hw', hq⟩
    rw [f1] at hw'
    obtain ⟨w, rfl⟩ : ∃ w : Sym2 (Atom 3 m), w' = w.map (RunClauses_eA e) := by
      refine ⟨w'.map (RunClauses_eA e).symm, ?_⟩
      rw [Sym2.map_map]
      simp
    rw [RunClauses_iso_cand h] at hw'
    rw [hG3] at hq
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hq
    exact ⟨b, ⟨w, (f2 Γ w).2 hw', hb⟩, rfl⟩
  · rintro ⟨b, ⟨w, hw, hb⟩, rfl⟩
    refine ⟨w.map (RunClauses_eA e), ?_, ?_⟩
    · rw [f1, RunClauses_iso_cand h]
      exact (f2 Γ w).1 hw
    · rw [hG3, hb]
      rfl

private theorem RunClauses_perm_lift {α β : Type} [DecidableEq α] (f : α → β) :
    ∀ {l₁ l₂ : List α}, (l₁.map f).Perm (l₂.map f) →
      ∃ L, List.Forall₂ (fun a b => f a = f b) l₁ L ∧ L.Perm l₂
  | [], l₂, h => by
    have h' := List.perm_nil.1 h.symm
    rw [List.map_eq_nil_iff] at h'
    exact ⟨[], .nil, by rw [h']⟩
  | a :: l₁, l₂, h => by
    have ha : f a ∈ l₂.map f := h.subset List.mem_cons_self
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 ha
    have h2 : (l₂.map f).Perm (f b :: (l₂.erase b).map f) := by
      have := (List.perm_cons_erase hb).map f
      simpa using this
    have h3 : (l₁.map f).Perm ((l₂.erase b).map f) := by
      have := h.trans h2
      rw [List.map_cons, hfb] at this
      exact (List.perm_cons _).1 this
    obtain ⟨L, hL1, hL2⟩ := RunClauses_perm_lift f h3
    exact ⟨b :: L, .cons hfb.symm hL1, (hL2.cons b).trans (List.perm_cons_erase hb).symm⟩

private theorem RunClauses_f2_filter {α β : Type} {R : α → β → Prop} {p : α → Bool}
    {q : β → Bool} (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.filter p) (l₂.filter q)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons hab h => by
    rw [List.filter_cons, List.filter_cons, hpq a b hab]
    split_ifs
    · exact .cons hab (RunClauses_f2_filter hpq h)
    · exact RunClauses_f2_filter hpq h

/-- The pairs of `A` joined by a `×`-dotted edge and no solid edge. -/
private def RunClauses_xonly {k n : ℕ} (SP : List (Atom k n × Atom k n × Bool))
    (u v : Atom k n) : Bool :=
  SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))

/-- The component added by `Graph.dotChoice` at a pair. -/
private def RunClauses_add {k n : ℕ} (A : List (Atom k n × Atom k n × Bool))
    (p : Atom k n × Atom k n × Bool) : Option (Comp (Atom k n)) :=
  if p ∈ A then some (mkC .dot p.1 p.2.1) else if p.2.2 then some (mkC .xdot p.1 p.2.1)
  else none

private theorem RunClauses_dotChoice_eq {k n : ℕ} (G : Graph k n)
    (SP A : List (Atom k n × Atom k n × Bool)) :
    G.dotChoice SP A = ⟨G.comps.filter (fun c => !(c.kind == .xdot && RunClauses_xonly SP c.x c.y))
      ++ SP.filterMap (RunClauses_add A),
      (-1 : Coeff) ^ (A.filter fun p => !p.2.2).length * G.coeff⟩ := rfl

private theorem RunClauses_xonly_iff {k n : ℕ} (SP : List (Atom k n × Atom k n × Bool))
    (u v : Atom k n) : RunClauses_xonly SP u v = true ↔ (s(u, v), false) ∈ SP.map RunClauses_key := by
  unfold RunClauses_xonly
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq,
    List.mem_map, RunClauses_key, Prod.mk.injEq, Sym2.eq_iff]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, h2, h1⟩
  · rintro ⟨p, hp, h2, h1⟩
    exact ⟨p, hp, h1, h2⟩

private theorem RunClauses_xonly_symm {k n : ℕ} (SP : List (Atom k n × Atom k n × Bool))
    (u v : Atom k n) : RunClauses_xonly SP u v = RunClauses_xonly SP v u := by
  rw [Bool.eq_iff_iff, RunClauses_xonly_iff, RunClauses_xonly_iff, Sym2.eq_swap]

/-- One choice of `O_dot` on graphs equal up to names and order: the choice of the same pairs. -/
private theorem RunClauses_iso_dotChoice (h : RunClauses_Iso e Γ Γ')
    {A' : List (Atom 3 m' × Atom 3 m' × Bool)} (hA' : A'.Sublist Γ'.splitPairs) :
    RunClauses_Iso e (Γ.dotChoice Γ.splitPairs (Γ.splitPairs.filter fun p =>
      decide (RunClauses_kmap e (RunClauses_key p) ∈ A'.map RunClauses_key)))
      (Γ'.dotChoice Γ'.splitPairs A') := by
  set SP := Γ.splitPairs with hSP
  set SP' := Γ'.splitPairs with hSP'
  set AK := A'.map RunClauses_key with hAK
  have hP := RunClauses_iso_sp h
  have hnd' := RunClauses_sp_nodup Γ'
  have hmemA' : ∀ q ∈ SP', (q ∈ A' ↔ RunClauses_key q ∈ AK) := by
    intro q hq
    refine ⟨fun h' => List.mem_map_of_mem h', fun h' => ?_⟩
    obtain ⟨r, hr, hk⟩ := List.mem_map.1 h'
    rwa [List.inj_on_of_nodup_map hnd' hq (hA'.subset hr) hk.symm]
  have hxonly : ∀ u v, RunClauses_xonly SP' (RunClauses_eA e u) (RunClauses_eA e v) =
      RunClauses_xonly SP u v := by
    intro u v
    rw [Bool.eq_iff_iff, RunClauses_xonly_iff, RunClauses_xonly_iff, hP.mem_iff]
    exact List.mem_map_of_injective (RunClauses_kmap_inj e) (a := (s(u, v), false))
  have hcount : ((SP.filter fun p => decide (RunClauses_kmap e (RunClauses_key p) ∈ AK)).filter
      (fun p => !p.2.2)).length = (A'.filter fun p => !p.2.2).length := by
    let B : Sym2 (Atom 3 m') × Bool → Bool := fun z => decide (z ∈ AK) && !z.2
    rw [List.filter_filter, ← List.countP_eq_length_filter]
    have c1 : SP.countP (fun p => !p.2.2 && decide (RunClauses_kmap e (RunClauses_key p) ∈ AK)) =
        ((SP.map RunClauses_key).map (RunClauses_kmap e)).countP B := by
      rw [List.countP_map, List.countP_map]
      refine List.countP_congr fun p _ => ?_
      simp only [B, Function.comp_apply, RunClauses_kmap, RunClauses_key, Bool.and_comm]
      exact Iff.rfl
    rw [c1, ← hP.countP_eq, List.countP_map]
    have c2 : SP'.countP (B ∘ RunClauses_key) = SP'.countP (fun q => !q.2.2 && decide (q ∈ A')) :=
      List.countP_congr fun q hq => by
        simp only [B, Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, hmemA' q hq]
        rw [and_comm]
        rfl
    rw [c2, List.countP_eq_length_filter, ← List.filter_filter]
    have hpA : (SP'.filter fun q => decide (q ∈ A')).Perm A' := by
      refine (List.perm_ext_iff_of_nodup ((List.Nodup.of_map _ hnd').filter _)
        (hA'.nodup (List.Nodup.of_map _ hnd'))).2 fun q => ?_
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h' => h'.2, fun h' => ⟨hA'.subset h', h'⟩⟩
    exact (hpA.filter _).length_eq
  refine ⟨?_, ?_⟩
  · rw [RunClauses_dotChoice_eq, RunClauses_dotChoice_eq]
    simp only
    rw [h.1, hcount]
  obtain ⟨-, cs, h1, h2⟩ := h
  have hmapP : ((SP.map (RunClauses_pmap e)).map RunClauses_key).Perm (SP'.map RunClauses_key) := by
    have : (SP.map (RunClauses_pmap e)).map RunClauses_key =
        (SP.map RunClauses_key).map (RunClauses_kmap e) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [this]
    exact hP.symm
  obtain ⟨L, hL1, hL2⟩ := RunClauses_perm_lift RunClauses_key hmapP
  let H : Atom 3 m' × Atom 3 m' × Bool → Option (Comp (Atom 3 m')) := fun q =>
    if RunClauses_key q ∈ AK then some (mkC .dot q.1 q.2.1)
    else if q.2.2 then some (mkC .xdot q.1 q.2.1) else none
  let q' : Comp (Atom 3 m') → Bool := fun c => !(c.kind == .xdot && RunClauses_xonly SP' c.x c.y)
  refine ⟨cs.filter q' ++ L.filterMap H, ?_, ?_⟩
  · rw [RunClauses_dotChoice_eq]
    simp only
    rw [List.map_append]
    refine List.rel_append ?_ ?_
    · have e1 : (Γ.comps.filter fun c => !(c.kind == .xdot && RunClauses_xonly SP c.x c.y)).map
          (Comp.map (RunClauses_eA e)) = (Γ.comps.map (Comp.map (RunClauses_eA e))).filter q' := by
        rw [List.filter_map]
        congr 1
        refine List.filter_congr fun c _ => ?_
        simp only [q', Function.comp_apply, Comp.map, hxonly]
      rw [e1]
      refine RunClauses_f2_filter (fun a b hr => ?_) h1
      obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
      simp only [q', hk]
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
      rw [RunClauses_xonly_symm]
    · have e2 : (SP.filterMap (RunClauses_add (SP.filter fun p =>
          decide (RunClauses_kmap e (RunClauses_key p) ∈ AK)))).map (Comp.map (RunClauses_eA e)) =
          (SP.map (RunClauses_pmap e)).filterMap H := by
        rw [List.map_filterMap, List.filterMap_map]
        refine List.filterMap_congr fun p hp => ?_
        simp only [RunClauses_add, Function.comp_apply, H, List.mem_filter, hp, true_and,
          decide_eq_true_eq]
        have hk : RunClauses_key (RunClauses_pmap e p) = RunClauses_kmap e (RunClauses_key p) := rfl
        have hf : (RunClauses_pmap e p).2.2 = p.2.2 := rfl
        rw [hk, hf]
        split_ifs <;> rfl
      rw [e2]
      refine RunClauses_f2_filterMap (fun a b hab => ?_) hL1
      simp only [H]
      have hab' := hab
      simp only [RunClauses_key, Prod.mk.injEq, Sym2.eq_iff] at hab'
      obtain ⟨hs, hf⟩ := hab'
      rw [← hab, hf]
      have key : ∀ κ, (κ = .dot ∨ κ = .xdot) →
          RunClauses_SwapR (mkC κ a.1 a.2.1) (mkC κ b.1 b.2.1) := by
        intro κ hκ
        rcases hs with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · left
          rw [← h1', ← h2']
        · right
          refine ⟨by rcases hκ with rfl | rfl <;> simp [mkC], ?_⟩
          rw [h1', h2']
          rfl
      split_ifs
      · exact Or.inr ⟨_, _, rfl, rfl, key _ (Or.inl rfl)⟩
      · exact Or.inr ⟨_, _, rfl, rfl, key _ (Or.inr rfl)⟩
      · exact Or.inl ⟨rfl, rfl⟩
  · rw [RunClauses_dotChoice_eq]
    refine (h2.filter q').append ?_
    refine (hL2.filterMap H).trans ?_
    rw [List.filterMap_congr fun q hq => ?_]
    simp only [H, RunClauses_add, ← hmemA' q hq]

/-- A predicate of the components read on graphs equal up to names and order. -/
private theorem RunClauses_iso_any (h : RunClauses_Iso e Γ Γ') (b : Comp (Atom 3 m') → Bool)
    (b₀ : Comp (Atom 3 m) → Bool)
    (hb : ∀ c c', RunClauses_SwapR (c.map (RunClauses_eA e)) c' → b c' = b₀ c) :
    Γ'.comps.any b = Γ.comps.any b₀ := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨c', hc', hb'⟩
    obtain ⟨c, hc, hr⟩ := RunClauses_iso_mem' h hc'
    exact ⟨c, hc, (hb c c' hr) ▸ hb'⟩
  · rintro ⟨c, hc, hb'⟩
    obtain ⟨c', hc', hr⟩ := RunClauses_iso_mem h hc
    exact ⟨c', hc', (hb c c' hr).symm ▸ hb'⟩

private theorem RunClauses_iso_labels (h : RunClauses_Iso e Γ Γ') :
    Γ'.labels.length = Γ.labels.length := by
  unfold Graph.labels
  have h1 : (Γ'.comps.filterMap Comp.label).Perm
      ((Γ.comps.filterMap Comp.label).map (Prod.map id (RunClauses_eA e))) := by
    have hm := (RunClauses_iso_map h Comp.label
      (fun c c' hr => (RunClauses_swapR_eq hr).2.1)).filterMap id
    rw [List.filterMap_map, List.filterMap_map] at hm
    rw [List.map_filterMap]
    exact hm
  rw [h1.dedup.length_eq, List.dedup_map_of_injective
    (Function.injective_id.prodMap (RunClauses_eA e).injective), List.length_map]

/-- The `O_dot` forms of graphs equal up to names and order are equal up to names and order. -/
private theorem RunClauses_iso_oDotT (h : RunClauses_Iso e Γ Γ') {t' : Tracked 3 m'}
    (ht' : t' ∈ oDotT Γ') :
    ∃ t ∈ oDotT Γ, ∃ σ : Fin t.nOut ≃ Fin t'.nOut, RunClauses_Iso σ t.g t'.g := by
  have hL := RunClauses_iso_labels h
  have hD2 := RunClauses_iso_any h
    (fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome)
    (fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) (fun c c' hr => by
      obtain ⟨hk, hl, -⟩ := RunClauses_swapR_eq hr
      simp only [hk, hl, Comp.map, Option.isSome_map])
  have hD4 := RunClauses_iso_any h
    (fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))
    (fun c => (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y))
    (fun c c' hr => by
      obtain ⟨hk, -, -, hxy, -⟩ := RunClauses_swapR_eq hr
      rw [hk]
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] <;>
        simp only [Comp.map, RunClauses_eA_isRight, (RunClauses_eA e).injective.beq_eq]
      rw [Bool.and_assoc, Bool.and_assoc, Bool.and_comm (Sum.isRight c.y),
        show (c.y == c.x) = (c.x == c.y) from by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]])
  have hSP : Γ'.splitPairs.isEmpty = Γ.splitPairs.isEmpty := by
    have := (RunClauses_iso_sp h).length_eq
    simp only [List.length_map] at this
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, ← List.length_eq_zero_iff,
      ← List.length_eq_zero_iff, this]
  unfold oDotT at ht' ⊢
  dsimp only at ht' ⊢
  split_ifs at ht' with g1 g2
  · rw [List.mem_singleton] at ht'
    subst ht'
    refine ⟨Tracked.self Γ, ?_, e, h⟩
    rw [if_pos (by rwa [hL, hD2] at g1)]
    exact List.mem_singleton_self _
  · rw [List.mem_singleton] at ht'
    subst ht'
    refine ⟨Tracked.self Γ, ?_, e, h⟩
    rw [if_neg (by rwa [hL, hD2] at g1), if_pos (by rwa [hSP, hD4] at g2)]
    exact List.mem_singleton_self _
  · obtain ⟨A', hA', hm⟩ := List.mem_filterMap.1 ht'
    obtain ⟨t, ht, σ, hσ⟩ :=
      RunClauses_iso_mergeT (RunClauses_iso_dotChoice h (List.mem_sublists.1 hA')) hm
    refine ⟨t, ?_, σ, hσ⟩
    rw [if_neg (by rwa [hL, hD2] at g1), if_neg (by rwa [hSP, hD4] at g2)]
    exact List.mem_filterMap.2 ⟨_, List.mem_sublists.2 List.filter_sublist, ht⟩

private theorem RunClauses_reorder_iso {n : ℕ} {Γ Γ' : Graph 3 n} (h : Γ.Reorder Γ') :
    ∃ π : Equiv.Perm (Fin n), RunClauses_Iso π Γ Γ' := by
  obtain ⟨hc, π, cs, h1, h2⟩ := h
  exact ⟨π, hc, cs, h1, h2⟩

end Iso

/-! ## The statements -/

/-- The statement `localOp_clausesStmtB`. -/
theorem localOp_clausesB : localOp_clausesStmtB := by
  intro n₀ C x Γ _ hlf _ hI hT _ o hs t ht
  obtain ⟨hs', hC, hE, hG, -⟩ := hI
  obtain ⟨⟨-, hC', -, hG'⟩, hx', -, -, -, hlab⟩ :=
    Local_localOp_good ⟨hs', hC, hE, hG⟩ hlf x o hs t ht
  refine ⟨hC', hG', fun c hc => ?_, (RunClauses_localOp_good x o hs t ht).2.2 hT⟩
  rcases hcl : c.label with - | ⟨pq, u⟩
  · rfl
  have hm := hlab (fun c hc pq u hl => by rw [hlf c hc] at hl; cases hl) c hc pq u hcl
  obtain ⟨b, hb⟩ : ∃ b, t.f (.inr x) = .inr b := by
    revert hx'
    cases t.f (.inr x) with
    | inl a => simp
    | inr b => exact fun _ => ⟨b, rfl⟩
  rw [hb] at hm
  cases u with
  | inl a =>
    exfalso
    have h1 : t.g.molRep (.inl a) = .inl a := rfl
    have h2 : ∃ b', t.g.molRep (.inr b) = .inr b' := ⟨_, rfl⟩
    obtain ⟨b', hb'⟩ := h2
    rw [h1, hb'] at hm
    cases hm
  | inr a => rfl

/-- The statement `globalSubst_extClauseStmt`. -/
theorem globalSubst_extClause : globalSubst_extClauseStmt := by
  intro m H x y₁ y₂ F hx hy₁ hy₂ hE g hg
  obtain ⟨g₀, -, rfl⟩ := List.mem_map.1 hg
  exact (RunClauses_glue_ext hx hy₁ hy₂).2 ((RunClauses_glue_ext (𝒢 := tVar true) hx hy₁ hy₂).1 hE)

/-- The statement `oDot_otimesStmt`. -/
theorem oDot_otimes : oDot_otimesStmt :=
  ⟨fun _ _ hT => RunClauses_oDot_td hT, fun Γ hQ => RunClauses_oDot_q Γ hQ⟩

/-- The statement `globalSubst_clausesStmt`. -/
theorem globalSubst_clauses : globalSubst_clausesStmt := by
  intro m H x y₁ y₂ F hx hy₁ hy₂ _ hC hG hL hT _ hF g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
  refine ⟨(RunClauses_glue_colour hx hy₁ hy₂).2
      ((RunClauses_glue_colour (𝒢 := tVar true) hx hy₁ hy₂).1 hC),
    (RunClauses_glue_noGhost hx hy₁ hy₂).2
      ⟨((RunClauses_glue_noGhost (𝒢 := tVar true) hx hy₁ hy₂).1 hG).1, hF g₀ hg₀⟩,
    (RunClauses_glue_labelsInt hx hy₁ hy₂).2
      ((RunClauses_glue_labelsInt (𝒢 := tVar true) hx hy₁ hy₂).1 hL),
    (RunClauses_glue_td hx hy₁ hy₂).2 ((RunClauses_glue_td (𝒢 := tVar true) hx hy₁ hy₂).1 hT)⟩

/-- The statement `reorder_oDotTStmt`. -/
theorem reorder_oDotT : reorder_oDotTStmt := by
  intro D n Γ Γ' h
  obtain ⟨π, hi⟩ := RunClauses_reorder_iso h
  refine ⟨RunClauses_iso_paperOrd hi, fun hall t' ht' => ?_⟩
  obtain ⟨t, ht, σ, hσ⟩ := RunClauses_iso_oDotT hi ht'
  obtain ⟨h1, C, h2⟩ := hall t ht
  exact ⟨by rw [RunClauses_iso_paperOrd hσ]; exact h1, C, RunClauses_iso_normal hσ h2⟩

/-- The statement `reorder_invRunStmt`. -/
theorem reorder_invRun : reorder_invRunStmt := by
  intro n D Γ Γ' h hI
  obtain ⟨π, hi⟩ := RunClauses_reorder_iso h
  rcases hI with ⟨⟨hs, hC, hE, hG, hL⟩, hT⟩ | ⟨h0, hQ⟩ | ⟨hp, hE, hC, hT, hall⟩
  · exact Or.inl ⟨⟨RunClauses_iso_spd hi hG hs, RunClauses_iso_colour hi hC,
      RunClauses_iso_ext hi hE, RunClauses_iso_noGhost hi hG, RunClauses_iso_labelsInt hi hL⟩,
      RunClauses_iso_td hi hT⟩
  · exact Or.inr (Or.inl ⟨h0, RunClauses_iso_qGraph hi hQ⟩)
  · exact Or.inr (Or.inr ⟨by rw [RunClauses_iso_paperOrd hi]; exact hp, RunClauses_iso_ext hi hE,
      RunClauses_iso_colour hi hC, RunClauses_iso_td hi hT, (reorder_oDotT D n Γ Γ' h).2 hall⟩)

section Instances

open private G8r_decAdjDot G8r_decSameBlock G8r_decAdjMol G8r_decSameMol
  G8r_decUnpinned
  G8r_decXdotApart
  from RBM8D.GlobalExp.Strategy

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end Instances

end RBM8D.Graphs
