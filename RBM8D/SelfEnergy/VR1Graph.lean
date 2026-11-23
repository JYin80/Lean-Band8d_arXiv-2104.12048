module

public import RBM8D.SelfEnergy.RenormDiff
public import RBM8D.SelfEnergy.InfBound
public import RBM8D.Kernel.InfLimit
public import RBM8D.Bound.DoublyDet
public import RBM8D.SelfEnergy.ValZ
public import RBM8D.Kernel.Sinf
public import RBM8D.Bound.AuxTreeZ
import all RBM8D.Bound.DoublyDet
import all RBM8D.SelfEnergy.RenormDiff
import all RBM8D.SelfEnergy.ValZ
import all RBM8D.Kernel.Sinf
import all RBM8D.Bound.AuxTreeZ
import all RBM8D.Kernel.InfLimit

@[expose] public section

/-!
# The comparison of one graph of `Σ_n` on the torus and on `ℤ^d`

This file states and proves, for one contracted graph `Γ` of `Σ_n`, the comparison of its value
on the torus `Z_L^d` at `z` with its value on `ℤ^d` at `E = Re z` ([I, (8.9)] for one graph,
[I, Lemma 7.7] and the omitted induction of [I, Lemma 8.5]), under a hypothesis on the chains
of its labelled `Θ` edges, and the summation step [I, (8.10)] from [I, (8.9)] and [I, (8.7)].

* `VR1Graph.graphCompare`: for a graph whose internal form is normal regular and doubly connected,
  with waved and labelled `Θ` edges, and chains of the torus and of `ℤ^d` that differ by at most
  `η W^σ W^{-(k(o)-2)d/2} B̃` on every `Θ` edge,
  `|Γ_{0x}(z) − Γ^∞_{0[x]}(E)| ≤ η W^{-(n_Γ-4)d/2} W^{-6} ⟨x⟩^{-(2d-6-τ)} + 1_{x=0} L^τ η W^{-(n_Γ-2)d/2}`,
  uniformly in `|E| < 2 − κ`.
* `VR1Graph.sumLemma`: (8.9) and (8.7) for a kernel give (8.10) for its row sums.

The passage from the torus to `ℤ^d` uses a single cut `R = ⌊L/(4(n+2))⌋` for all edges: on the
torus the `Θ` edges are replaced by the cut chains of `ℤ^d` (one marked edge per term, [I, Cor 6.13])
and the waved edges are cut (a crude count against their decay); with every edge shorter than `R`
the configurations of the torus and of `ℤ^d` correspond; on `ℤ^d` the cut is removed and the
waved kernels and the coefficient are moved from `z` to `E` (one marked edge per term, the
`ℤ^d` form of [I, Claim 6.11]). A long labelled `Θ` edge costs `(W/R)² B̃`, not `L^{-D}`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D

open Graphs

open private reach_lift intAtom extAtom extAtom_intAtom dc_trees tree_length ord_eq_sum
  im_pos_of_specDom from RBM8D.Bound.DoublyDet
open private RenormDiff_toAux RenormDiff_auxComp RenormDiff_lab RenormDiff_auxComp_waved
  RenormDiff_auxComp_theta RenormDiff_lab_waved RenormDiff_lab_theta RenormDiff_toAux_internal
  RenormDiff_toAux_isBKind RenormDiff_toAux_filter RenormDiff_telescope RenormDiff_absVal_toAux
  RenormDiff_ord_toAux RenormDiff_val_aux RenormDiff_val_waved_aux RenormDiff_brk_pos
  RenormDiff_le_brk RenormDiff_term_eq RenormDiff_val_theta from RBM8D.SelfEnergy.RenormDiff
open private ValZ_uniform ValZ_shape ValZ_wave_bound ValZ_wb ValZ_norm_one_sub_sq
  from RBM8D.SelfEnergy.ValZ
open private phiW_eq_profInt from RBM8D.Kernel.Sinf
open private AuxTreeZ.latSum from RBM8D.Bound.AuxTreeZ
open private InfLimit_msc_sub_mE InfLimit_mE_im_ge InfLimit_sq_sub_le from RBM8D.Kernel.InfLimit

variable {d : ℕ}

/-! ## Lifting a configuration from the torus to `ℤ^d` -/

section Lift

private theorem VR1Graph_zcast_add (L : ℕ) (v w : Fin d → ℤ) :
    zcast L (v + w) = zcast L v + zcast L w := by
  funext i; simp [zcast]

private theorem VR1Graph_zcast_neg (L : ℕ) (v : Fin d → ℤ) : zcast L (-v) = -zcast L v := by
  funext i; simp [zcast]

private theorem VR1Graph_zcast_sub (L : ℕ) (v w : Fin d → ℤ) :
    zcast L (v - w) = zcast L v - zcast L w := by
  funext i; simp [zcast]

private theorem VR1Graph_zcast_zero (L : ℕ) : zcast L (0 : Fin d → ℤ) = 0 := by
  funext i; simp [zcast]

/-- `zcast ∘ zlift = id` on `Z_L^d`. -/
private theorem VR1Graph_zcast_zlift {L : ℕ} (u : Zd d L) : zcast L (zlift u) = u := by
  funext i; simp [zcast, zlift, ZMod.coe_valMinAbs]

/-- `zlift ∘ zcast = id` on the points of `ℤ^d` with `2 |v|_∞ < L`. -/
private theorem VR1Graph_zlift_zcast {L : ℕ} [NeZero L] (v : Fin d → ℤ) (hv : 2 * zdInf v < L) :
    zlift (zcast L v) = v := by
  funext i
  simp only [zlift, zcast]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have hi : (v i).natAbs ≤ zdInf v :=
    Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ i)
  have h1 : ((v i).natAbs : ℤ) * 2 < L := by exact_mod_cast (by omega : (v i).natAbs * 2 < L)
  have h2 := abs_le.1 (le_of_eq (Int.natCast_natAbs (v i)).symm)
  constructor
  · linarith [h2.1]
  · linarith [h2.2]

/-- `zdInf ([u]) = ‖u‖_L`. -/
private theorem VR1Graph_zdInf_zlift {L : ℕ} [NeZero L] (u : Zd d L) :
    zdInf (zlift u) = zdistInf d L u := by
  unfold zdInf zlift zdistInf
  congr 1
  funext i
  rw [zdist_eq_natAbs_valMinAbs]

/-- `zlift 0 = 0`. -/
private theorem VR1Graph_zlift_zero {L : ℕ} : zlift (0 : Zd d L) = 0 := by
  funext i; simp [zlift]

/-- Along a walk of the graph of all components, a labelling of the atoms on the torus whose
components are all short has short lifted increments. -/
private theorem VR1Graph_walk_tor {L : ℕ} {n : ℕ} (Γ : Graph 2 n) (R : ℕ)
    (σ : Atom 2 n → Zd d L) (hs : ∀ c ∈ Γ.comps, zdInf (zlift (σ c.y - σ c.x)) ≤ R) :
    ∀ {a b : Atom 2 n} (p : Γ.edgeGraph.Walk a b),
      ∃ v : Fin d → ℤ, zcast L v = σ b - σ a ∧ zdInf v ≤ p.length * R := by
  intro a b p
  induction p with
  | nil => exact ⟨0, by rw [VR1Graph_zcast_zero, sub_self], by simp [zdInf]⟩
  | @cons a c b h p ih =>
    obtain ⟨v, hv, hvl⟩ := ih
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at h
    obtain ⟨w, hw, hwl⟩ : ∃ w : Fin d → ℤ, zcast L w = σ c - σ a ∧ zdInf w ≤ R := by
      rcases h.2 with ⟨e, he, hx, hy⟩ | ⟨e, he, hx, hy⟩
      · refine ⟨zlift (σ c - σ a), VR1Graph_zcast_zlift _, ?_⟩
        have := hs e he; rwa [hx, hy] at this
      · refine ⟨-zlift (σ a - σ c), ?_, ?_⟩
        · rw [VR1Graph_zcast_neg, VR1Graph_zcast_zlift, neg_sub]
        · rw [zdInf_neg]; have := hs e he; rwa [hx, hy] at this
    refine ⟨v + w, ?_, ?_⟩
    · rw [VR1Graph_zcast_add, hv, hw]; abel
    · rw [SimpleGraph.Walk.length_cons]
      calc zdInf (v + w) ≤ zdInf v + zdInf w := zdInf_add_le v w
        _ ≤ p.length * R + R := by omega
        _ = (p.length + 1) * R := by ring

/-- Along a walk, a labelling of the atoms in `ℤ^d` whose components are all short moves by at
most the length of the walk times the cut. -/
private theorem VR1Graph_walk_zd {n : ℕ} (Γ : Graph 2 n) (R : ℕ) (τ : Atom 2 n → Fin d → ℤ)
    (hs : ∀ c ∈ Γ.comps, zdInf (τ c.y - τ c.x) ≤ R) :
    ∀ {a b : Atom 2 n} (p : Γ.edgeGraph.Walk a b), zdInf (τ b - τ a) ≤ p.length * R := by
  intro a b p
  induction p with
  | nil => simp [zdInf]
  | @cons a c b h p ih =>
    rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at h
    have hw : zdInf (τ c - τ a) ≤ R := by
      rcases h.2 with ⟨e, he, hx, hy⟩ | ⟨e, he, hx, hy⟩
      · have := hs e he; rwa [hx, hy] at this
      · have := hs e he; rw [hx, hy] at this; rwa [← neg_sub, zdInf_neg]
    have he : τ b - τ a = (τ b - τ c) + (τ c - τ a) := by abel
    rw [he, SimpleGraph.Walk.length_cons]
    calc zdInf ((τ b - τ c) + (τ c - τ a)) ≤ zdInf (τ b - τ c) + zdInf (τ c - τ a) :=
          zdInf_add_le _ _
      _ ≤ p.length * R + R := by omega
      _ = (p.length + 1) * R := by ring

/-- In a connected graph on the atoms every atom is joined to `a` by a walk with at most `n + 1`
steps. -/
private theorem VR1Graph_short_walk {n : ℕ} (Γ : Graph 2 n) (hc : Γ.edgeGraph.Preconnected)
    (a b : Atom 2 n) : ∃ p : Γ.edgeGraph.Walk a b, p.length ≤ n + 1 := by
  classical
  obtain ⟨p⟩ := hc a b
  refine ⟨p.bypass, ?_⟩
  have h := (SimpleGraph.Walk.bypass_isPath p).length_lt
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- The graph of all components of `Γ` is connected when that of its internal form is. -/
private theorem VR1Graph_preconnected {n : ℕ} (Γ : Graph 2 n)
    (h : Γ.internalize.edgeGraph.Preconnected) : Γ.edgeGraph.Preconnected := by
  intro u v
  have key := reach_lift (G₁ := Γ.internalize.edgeGraph) (G₂ := Γ.edgeGraph) (extAtom 2 n)
    (fun p q hpq => by
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hpq
      obtain ⟨hne, hr⟩ := hpq
      have hmap : ∀ c ∈ Γ.internalize.comps, ∃ c₀ ∈ Γ.comps,
          c.x = intAtom 2 n c₀.x ∧ c.y = intAtom 2 n c₀.y := by
        intro c hc
        obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
        exact ⟨c₀, hc₀, rfl, rfl⟩
      refine SimpleGraph.Adj.reachable ?_
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
      rcases hr with ⟨c, hc, hx, hy⟩ | ⟨c, hc, hx, hy⟩
      · obtain ⟨c₀, hc₀, h1, h2⟩ := hmap c hc
        subst hx hy
        rw [h1, h2, extAtom_intAtom, extAtom_intAtom]
        refine ⟨fun h' => hne (by rw [h1, h2, h']), Or.inl ⟨c₀, hc₀, rfl, rfl⟩⟩
      · obtain ⟨c₀, hc₀, h1, h2⟩ := hmap c hc
        subst hx hy
        rw [h1, h2, extAtom_intAtom, extAtom_intAtom]
        refine ⟨fun h' => hne (by rw [h1, h2, h']), Or.inr ⟨c₀, hc₀, rfl, rfl⟩⟩)
    (h (intAtom 2 n u) (intAtom 2 n v))
  rwa [extAtom_intAtom, extAtom_intAtom] at key

/-- **The lift.** For a connected graph and kernels on `ℤ^d` vanishing beyond the cut `R`, with
`4 (n + 2) R ≤ L`, the sum over the labellings of the internal atoms on the torus of the product
of the kernels at the lifted increments equals the sum over the labellings in `ℤ^d`, the external
atoms sitting at `0, x` and at `0, [x]`. -/
private theorem VR1Graph_lift {L : ℕ} [NeZero L] {n : ℕ} (Γ : Graph 2 n)
    (hconn : Γ.edgeGraph.Preconnected) (R : ℕ) (hR : 4 * (n + 2) * R ≤ L)
    (f : Fin Γ.comps.length → (Fin d → ℤ) → ℂ) (hf : ∀ i v, R < zdInf v → f i v = 0)
    (a : ℂ) (x : Zd d L) :
    ∑ s : Fin n → Zd d L, a * ∏ i, f i (zlift (Sum.elim ![0, x] s Γ.comps[i].y -
        Sum.elim ![0, x] s Γ.comps[i].x)) =
      ∑' t : Fin n → Fin d → ℤ, a * ∏ i, f i (Sum.elim ![0, zlift x] t Γ.comps[i].y -
        Sum.elim ![0, zlift x] t Γ.comps[i].x) := by
  classical
  set F : (Fin n → Fin d → ℤ) → ℂ := fun t => a * ∏ i, f i (Sum.elim ![0, zlift x] t Γ.comps[i].y -
    Sum.elim ![0, zlift x] t Γ.comps[i].x) with hF
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  -- `zlift ∘ σ` is the labelling in `ℤ^d`
  have hτ : ∀ s : Fin n → Zd d L, Sum.elim ![0, zlift x] (fun j => zlift (s j)) =
      fun u => zlift (Sum.elim ![0, x] s u) := by
    intro s; funext u
    rcases u with i | j
    · fin_cases i <;> simp [VR1Graph_zlift_zero]
    · rfl
  -- a labelling in `ℤ^d` with all components short stays within `(n + 1) R` of the origin
  have hsmall : ∀ τ : Atom 2 n → Fin d → ℤ, τ (Sum.inl 0) = 0 →
      (∀ c ∈ Γ.comps, zdInf (τ c.y - τ c.x) ≤ R) → ∀ u, zdInf (τ u) ≤ (n + 1) * R := by
    intro τ h0 hs u
    obtain ⟨p, hp⟩ := VR1Graph_short_walk Γ hconn (Sum.inl 0) u
    have := VR1Graph_walk_zd Γ R τ hs p
    rw [h0, sub_zero] at this
    exact this.trans (Nat.mul_le_mul_right R hp)
  have hlt : ∀ v w : Fin d → ℤ, zdInf v ≤ (n + 1) * R → zdInf w ≤ (n + 1) * R →
      2 * zdInf (v - w) < L := by
    intro v w hv hw
    have h1 : zdInf (v - w) ≤ zdInf v + zdInf w := by
      rw [sub_eq_add_neg]; exact (zdInf_add_le _ _).trans (by rw [zdInf_neg])
    rcases Nat.eq_zero_or_pos R with h0 | h0
    · subst h0; simp at hv hw; omega
    · nlinarith
  -- the summand on the torus is the summand in `ℤ^d` at `zlift ∘ s`
  have hpt : ∀ s : Fin n → Zd d L, a * ∏ i, f i (zlift (Sum.elim ![0, x] s Γ.comps[i].y -
      Sum.elim ![0, x] s Γ.comps[i].x)) = F (fun j => zlift (s j)) := by
    intro s
    set σ := Sum.elim ![0, x] s with hσ
    simp only [hF, hτ s]
    by_cases hall : ∀ c ∈ Γ.comps, zdInf (zlift (σ c.y - σ c.x)) ≤ R
    · -- all components short on the torus: the lifted increments are the increments of `zlift ∘ σ`
      have hlift : ∀ u, zdInf (zlift (σ u)) ≤ (n + 1) * R ∧ True := by
        intro u
        obtain ⟨p, hp⟩ := VR1Graph_short_walk Γ hconn (Sum.inl 0) u
        obtain ⟨v, hv, hvl⟩ := VR1Graph_walk_tor Γ R σ hall p
        have hσ0 : σ (Sum.inl 0) = 0 := by simp [hσ]
        rw [hσ0, sub_zero] at hv
        have hvb : zdInf v ≤ (n + 1) * R := hvl.trans (Nat.mul_le_mul_right R hp)
        have h2 : 2 * zdInf v < L := by
          have := hlt v 0 hvb (by simp [zdInf]); simpa using this
        rw [← hv, VR1Graph_zlift_zcast v h2]
        exact ⟨hvb, trivial⟩
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      have hz : zlift (σ Γ.comps[i].y) - zlift (σ Γ.comps[i].x) =
          zlift (zcast L (zlift (σ Γ.comps[i].y) - zlift (σ Γ.comps[i].x))) :=
        (VR1Graph_zlift_zcast _ (hlt _ _ (hlift _).1 (hlift _).1)).symm
      rw [hz, VR1Graph_zcast_sub, VR1Graph_zcast_zlift, VR1Graph_zcast_zlift]
    · -- a long component on the torus: both summands vanish
      push Not at hall
      obtain ⟨c, hc, hlong⟩ := hall
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hc
      have hT : ∏ j, f j (zlift (σ Γ.comps[j].y - σ Γ.comps[j].x)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (hf i _ hlong)
      rw [hT, mul_zero]
      by_cases hZ : ∀ c ∈ Γ.comps, zdInf (zlift (σ c.y) - zlift (σ c.x)) ≤ R
      · exfalso
        have h0 : ∀ u, zdInf (zlift (σ u)) ≤ (n + 1) * R :=
          hsmall (fun u => zlift (σ u)) (by simp [hσ, VR1Graph_zlift_zero]) hZ
        have he := VR1Graph_zlift_zcast _ (hlt _ _ (h0 (Γ.comps.get i).y) (h0 (Γ.comps.get i).x))
        rw [VR1Graph_zcast_sub, VR1Graph_zcast_zlift, VR1Graph_zcast_zlift] at he
        have := hZ _ hc
        rw [← he] at this
        omega
      · push Not at hZ
        obtain ⟨c', hc', hlong'⟩ := hZ
        obtain ⟨i', rfl⟩ := List.mem_iff_get.1 hc'
        rw [Finset.prod_eq_zero (Finset.mem_univ i') (hf i' _ hlong'), mul_zero]
  -- the support of the summand in `ℤ^d` lies in the image of `zlift ∘ ·`
  have hinj : Function.Injective fun (s : Fin n → Zd d L) (j : Fin n) => zlift (s j) := by
    intro s s' h
    funext j
    have := congrFun h j
    simpa [VR1Graph_zcast_zlift] using congrArg (zcast L) this
  have hsupp : Function.support F ⊆ Set.range fun (s : Fin n → Zd d L) (j : Fin n) => zlift (s j) := by
    intro t ht
    have hall : ∀ c ∈ Γ.comps, zdInf (Sum.elim ![0, zlift x] t c.y -
        Sum.elim ![0, zlift x] t c.x) ≤ R := by
      intro c hc
      by_contra hlong
      push Not at hlong
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hc
      exact ht (by simp only [hF]; rw [Finset.prod_eq_zero (Finset.mem_univ i) (hf i _ hlong),
        mul_zero])
    have h0 := hsmall _ (by simp) hall
    refine ⟨fun j => zcast L (t j), funext fun j => ?_⟩
    have := h0 (Sum.inr j)
    exact VR1Graph_zlift_zcast _ (by have := hlt _ 0 this (by simp [zdInf]); simpa using this)
  rw [← hinj.tsum_eq hsupp, tsum_fintype]
  exact Finset.sum_congr rfl fun s _ => hpt s

end Lift

/-! ## Graphs on `ℤ^d` with one marked edge -/

section TreeZ

/-- [I, Claim 6.11] on `ℤ^d` with the blue tree weakened to `W^{-4} ⟨·⟩^{-(d-4-τ₁)}`: for black
and blue spanning trees and `0 < τ₁ ≤ 1/4`, `d ≥ 7`, there is `C` with
`Γ̃_{xy} ≤ C W^{(-d+2τ₁)ℓ} W^{-6} ⟨x - y⟩^{-(2d-6-2τ₁)}` (black kernels `B^{d-2-τ₁}`). -/
private theorem VR1Graph_treeZ (hd : 7 ≤ d) {ℓ : ℕ} (Γa : AuxGraph ℓ) (hT : TreeEdges Γa.black)
    (hU : TreeEdges (Γa.blue.map fun e => (e.1, e.2.1))) (τ₁ : ℝ) (hτ₁ : 0 < τ₁)
    (hτ₁' : τ₁ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W → ∀ A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ,
      (∀ j p r, |A j p r| ≤ (W : ℝ) ^ (-4 : ℝ) * AuxTreeZ.brk d W p r ^ (-((d : ℝ) - 4 - τ₁))) →
      ∀ x y : Fin d → ℤ, Summable (Γa.termZ d W ((d : ℝ) - 2 - τ₁) A x y) ∧
        Γa.valZ d W ((d : ℝ) - 2 - τ₁) A x y ≤
          C * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ) * (W : ℝ) ^ (-6 : ℝ) *
            AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by
  have hd7 : (7 : ℝ) ≤ d := by exact_mod_cast hd
  set β : ℝ := (d : ℝ) - 2 - τ₁ with hβ
  set s : ℝ := (d : ℝ) - 4 - τ₁ with hs
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  obtain ⟨C₃, hC₃, hV⟩ := AuxTreeZ.vertex d β s hβ0 hs0 (by rw [hβ, hs]; linarith)
  obtain ⟨C₄, hC₄, hC⟩ := AuxTreeZ.core d β s 4 hβ0 hs0 Γa hT hU
  refine ⟨C₄ * C₃ ^ ℓ, by positivity, fun W hWn A hA x y => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hWn
  set c₁ : ℝ := C₃ * (W : ℝ) ^ ((-2 : ℝ) - 4) * (W : ℝ) ^ ((d : ℝ) - β - s) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  obtain ⟨hsum, hval⟩ := hC W hWn A c₁ hc₁0 (fun p u => hV W hWn 4 p u) hA x y
  refine ⟨hsum, hval.trans (le_of_eq ?_)⟩
  have hc₁' : c₁ ^ ℓ = C₃ ^ ℓ * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ) := by
    rw [hc₁, mul_assoc, ← Real.rpow_add hW0, mul_pow, ← Real.rpow_mul_natCast hW0.le]
    congr 3
    rw [hβ, hs]; ring
  have ht0 := AuxTreeZ.brk_pos hWn x y
  rw [hc₁']
  unfold AuxTreeZ.bB
  have e1 : AuxTreeZ.brk d W x y ^ (-s) * AuxTreeZ.brk d W x y ^ (-β) =
      AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by
    rw [← Real.rpow_add ht0]; congr 1; rw [hβ, hs]; ring
  have e2 : (W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-2 : ℝ) = (W : ℝ) ^ (-6 : ℝ) := by
    rw [← Real.rpow_add hW0]; norm_num
  calc C₄ * (C₃ ^ ℓ * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ)) *
        ((W : ℝ) ^ (-4 : ℝ) * AuxTreeZ.brk d W x y ^ (-s)) *
        ((W : ℝ) ^ (-2 : ℝ) * AuxTreeZ.brk d W x y ^ (-β))
      = C₄ * C₃ ^ ℓ * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * ℓ) *
          ((W : ℝ) ^ (-4 : ℝ) * (W : ℝ) ^ (-2 : ℝ)) *
          (AuxTreeZ.brk d W x y ^ (-s) * AuxTreeZ.brk d W x y ^ (-β)) := by ring
    _ = _ := by rw [e1, e2]

/-- A component bound with a black factor `G` and a blue factor `G'`: a component in at most one
tree, from `v ≤ P u` with `u ≤ 1`, `u ≤ G` on a black and `u ≤ G'` on a blue edge. -/
private theorem VR1Graph_flag_one (v P u G G' : ℝ) (hP : 0 ≤ P) (hu1 : u ≤ 1) (bk bu : Prop)
    [Decidable bk] [Decidable bu] (hv : v ≤ P * u) (hG : bk → u ≤ G) (hG' : bu → u ≤ G')
    (hboth : bk → bu → False) :
    v ≤ P * (if bk then G else 1) * (if bu then G' else 1) := by
  split_ifs with h1 h2 h2
  · exact (hboth h1 h2).elim
  · simpa using hv.trans (mul_le_mul_of_nonneg_left (hG h1) hP)
  · simpa using hv.trans (mul_le_mul_of_nonneg_left (hG' h2) hP)
  · simpa using hv.trans (mul_le_mul_of_nonneg_left hu1 hP)

/-- A waved component, possibly in both trees: from `v ≤ P u²` with `0 ≤ u ≤ 1`, `u ≤ G`,
`u ≤ G'`. -/
private theorem VR1Graph_flag_two (v P u G G' : ℝ) (hP : 0 ≤ P) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (huG : u ≤ G) (huG' : u ≤ G') (bk bu : Prop) [Decidable bk] [Decidable bu]
    (hv : v ≤ P * (u * u)) : v ≤ P * (if bk then G else 1) * (if bu then G' else 1) := by
  have h1 : u * u ≤ G * G' := mul_le_mul huG huG' hu0 (hu0.trans huG)
  have h2 : u * u ≤ G := (mul_le_of_le_one_left hu0 hu1).trans huG
  have h3 : u * u ≤ G' := (mul_le_of_le_one_left hu0 hu1).trans huG'
  have h4 : u * u ≤ 1 := (mul_le_of_le_one_left hu0 hu1).trans hu1
  split_ifs
  · nlinarith [mul_le_mul_of_nonneg_left h1 hP]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hP]
  · nlinarith [mul_le_mul_of_nonneg_left h3 hP]
  · nlinarith [mul_le_mul_of_nonneg_left h4 hP]

/-- `(Π_{i ∈ l} c f(i)) = c^{|l|} Π_{i ∈ l} f(i)`. -/
private theorem VR1Graph_prod_map_const_mul {ι : Type*} (l : List ι) (c : ℝ) (f : ι → ℝ) :
    (l.map fun i => c * f i).prod = c ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring

/-- `Π_i (Pᵢ (bk? c B i) (bu? c B' i)) = (Π Pᵢ) c^{|bl|} c^{|bu|} Π_{bl} B Π_{bu} B'`. -/
private theorem VR1Graph_prod_flags {m : ℕ} (P : Fin m → ℝ) (c : ℝ) (B B' : Fin m → ℝ)
    (bl bu : List (Fin m)) (hbl : bl.Nodup) (hbu : bu.Nodup) :
    ∏ i, (P i * (if i ∈ bl then c * B i else 1) * (if i ∈ bu then c * B' i else 1)) =
      (∏ i, P i) * (c ^ bl.length * c ^ bu.length) * ((bl.map B).prod * (bu.map B').prod) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h1 : ∏ i : Fin m, (if i ∈ bl then c * B i else 1) = c ^ bl.length * (bl.map B).prod := by
    simp_rw [← List.mem_toFinset (l := bl)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbl,
      VR1Graph_prod_map_const_mul]
  have h2 : ∏ i : Fin m, (if i ∈ bu then c * B' i else 1) = c ^ bu.length * (bu.map B').prod := by
    simp_rw [← List.mem_toFinset (l := bu)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbu,
      VR1Graph_prod_map_const_mul]
  rw [h1, h2]; ring

/-- The bracket `W / ⟨v⟩` raised to `a`: `W^a ⟨v⟩^{-a}`. -/
private def VR1Graph_u (W : ℕ) (a : ℝ) (v : Fin d → ℤ) : ℝ :=
  (W : ℝ) ^ a * ((zdInf v : ℝ) + W) ^ (-a)

private theorem VR1Graph_u_nonneg (W : ℕ) (a : ℝ) (v : Fin d → ℤ) : 0 ≤ VR1Graph_u W a v := by
  unfold VR1Graph_u; positivity

private theorem VR1Graph_u_le_one {W : ℕ} (hW : 1 ≤ W) {a : ℝ} (ha : 0 ≤ a) (v : Fin d → ℤ) :
    VR1Graph_u W a v ≤ 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : (W : ℝ) ≤ (zdInf v : ℝ) + W := by linarith [(Nat.cast_nonneg (zdInf v) : (0 : ℝ) ≤ _)]
  unfold VR1Graph_u
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv]
  exact div_le_one_of_le₀ (Real.rpow_le_rpow hW0.le ht ha) (by positivity)

/-- `W^a ⟨v⟩^{-a} ≤ W^{a'} ⟨v⟩^{-b'}` for `b' ≤ a` and `b' ≤ a'`. -/
private theorem VR1Graph_u_le {W : ℕ} (hW : 1 ≤ W) {a a' b' : ℝ} (hb : b' ≤ a)
    (hab : b' ≤ a') (v : Fin d → ℤ) :
    VR1Graph_u W a v ≤ (W : ℝ) ^ a' * ((zdInf v : ℝ) + W) ^ (-b') := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have ht : (W : ℝ) ≤ (zdInf v : ℝ) + W := by linarith [(Nat.cast_nonneg (zdInf v) : (0 : ℝ) ≤ _)]
  have ht0 : 0 < (zdInf v : ℝ) + W := by linarith
  have ht1 : (1 : ℝ) ≤ (zdInf v : ℝ) + W := hW1.trans ht
  unfold VR1Graph_u
  have key : (W : ℝ) ^ (a - a') * ((zdInf v : ℝ) + W) ^ (-(a - b')) ≤ 1 := by
    rcases le_or_gt 0 (a - a') with hp | hp
    · have h1 : (W : ℝ) ^ (a - a') ≤ ((zdInf v : ℝ) + W) ^ (a - a') :=
        Real.rpow_le_rpow hW0.le ht hp
      calc _ ≤ ((zdInf v : ℝ) + W) ^ (a - a') * ((zdInf v : ℝ) + W) ^ (-(a - b')) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 1 := by
            rw [← Real.rpow_add ht0]
            exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    · have h1 : (W : ℝ) ^ (a - a') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 hp.le
      have h2 : ((zdInf v : ℝ) + W) ^ (-(a - b')) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
      calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = 1 := one_mul 1
  calc (W : ℝ) ^ a * ((zdInf v : ℝ) + W) ^ (-a)
      = ((W : ℝ) ^ a' * ((zdInf v : ℝ) + W) ^ (-b')) *
          ((W : ℝ) ^ (a - a') * ((zdInf v : ℝ) + W) ^ (-(a - b'))) := by
        rw [mul_mul_mul_comm, ← Real.rpow_add hW0, ← Real.rpow_add ht0]; ring_nf
    _ ≤ ((W : ℝ) ^ a' * ((zdInf v : ℝ) + W) ^ (-b')) * 1 :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := mul_one _

/-- The majorant of a component on `ℤ^d`: `(W/⟨v⟩)^{2(d-2)}` for a waved edge, `(W/⟨v⟩)^{d-4}` for
the marked edge of index `j₀` and `(W/⟨v⟩)^{d-2-τ₁}` for the other `Θ` edges. -/
private def VR1Graph_maj {V : Type*} (W : ℕ) (τ₁ : ℝ) (j₀ i : ℕ) (c : Comp V)
    (v : Fin d → ℤ) : ℝ :=
  match c.kind with
  | .waved _ => VR1Graph_u W ((d : ℝ) - 2) v * VR1Graph_u W ((d : ℝ) - 2) v
  | _ => if i = j₀ then VR1Graph_u W ((d : ℝ) - 4) v else VR1Graph_u W ((d : ℝ) - 2 - τ₁) v

set_option maxHeartbeats 1000000 in
/-- **[I, Cor 7.6] on `ℤ^d` with one marked edge**, for kernels given by their bounds: for a graph
of waved and `Θ` edges whose internal form is normal regular and doubly connected, an index `j₀`
that is not a waved edge, and `0 < τ₁ ≤ 1/4`, there is `C₀` such that for `W ≥ 1`, kernels
`hᵢ` with `|hᵢ(v)| ≤ K λᵢ W^{-qᵢ d/2} majᵢ(v)` and a coefficient `a`, the summand is summable
and `Σ_s |a Π hᵢ| ≤ C₀ |a| K^{|Γ|} Π λᵢ W^{2τ₁ n} W^{-(n_Γ-4)d/2} W^{-6} ⟨x-y⟩^{-(2d-6-2τ₁)}`. -/
private theorem VR1Graph_graphZ (hd : 8 ≤ d) {n C : ℕ} (Γ : Graph 2 n)
    (hN : Γ.internalize.Normal C) (hDC : Γ.internalize.DoublyConnected)
    (hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o)
    (j₀ : ℕ) (hj₀ : ∀ i : Fin Γ.comps.length, i.1 = j₀ → ∃ o, Γ.comps[i].kind = .theta o)
    (τ₁ : ℝ) (hτ₁ : 0 < τ₁) (hτ₁' : τ₁ ≤ 1 / 4) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ W : ℕ, 1 ≤ W → ∀ (a : ℂ) (K : ℝ) (lam : Fin Γ.comps.length → ℝ)
      (h : Fin Γ.comps.length → (Fin d → ℤ) → ℂ), 0 ≤ K → (∀ i, 0 ≤ lam i) →
      (∀ i v, ‖h i v‖ ≤ K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        VR1Graph_maj W τ₁ j₀ i Γ.comps[i] v) →
      ∀ x y : Fin d → ℤ,
        Summable (fun s : Fin n → Fin d → ℤ => ‖a * ∏ i, h i (Sum.elim ![x, y] s Γ.comps[i].y -
          Sum.elim ![x, y] s Γ.comps[i].x)‖) ∧
        ∑' s : Fin n → Fin d → ℤ, ‖a * ∏ i, h i (Sum.elim ![x, y] s Γ.comps[i].y -
          Sum.elim ![x, y] s Γ.comps[i].x)‖ ≤
          C₀ * ‖a‖ * K ^ Γ.comps.length * (∏ i, lam i) * (W : ℝ) ^ (2 * τ₁ * n) *
            (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  -- two spanning trees, the black one avoiding the marked edge
  obtain ⟨bl, bu, hbl, hbu, hboth, hTb, hTu, hbk0⟩ : ∃ bl bu : List (Fin Γ.comps.length),
      bl.Nodup ∧ bu.Nodup ∧ (∀ i ∈ bl, i ∈ bu → ∃ w, Γ.comps[i].kind = .waved w) ∧
      TreeEdges (bl.map fun (i : Fin Γ.comps.length) => (Γ.comps[i].x, Γ.comps[i].y)) ∧
      TreeEdges (bu.map fun (i : Fin Γ.comps.length) => (Γ.comps[i].x, Γ.comps[i].y)) ∧
      ∀ i ∈ bl, i.1 ≠ j₀ := by
    obtain ⟨bl₀, bu₀, hbl₀, hbu₀, -, -, hboth₀, hTb₀, hTu₀⟩ :=
      dc_trees (by norm_num) Γ C hN.1 hDC
    by_cases hb : ∀ i ∈ bl₀, i.1 ≠ j₀
    · exact ⟨bl₀, bu₀, hbl₀, hbu₀, hboth₀, hTb₀, hTu₀, hb⟩
    · push Not at hb
      obtain ⟨i₀, hi₀, he₀⟩ := hb
      refine ⟨bu₀, bl₀, hbu₀, hbl₀, fun i h1 h2 => hboth₀ i h2 h1, hTu₀, hTb₀, fun i hi he => ?_⟩
      have hii : i = i₀ := Fin.ext (he.trans he₀.symm)
      subst hii
      obtain ⟨w, hw⟩ := hboth₀ i hi₀ hi
      obtain ⟨o, ho⟩ := hj₀ i he
      rw [hw] at ho; cases ho
  have hlb : bl.length = n + 1 := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n + 1 := by have := tree_length bu _ hTu; omega
  set β : ℝ := (d : ℝ) - 2 - τ₁ with hβ
  set sb : ℝ := (d : ℝ) - 4 - τ₁ with hsb
  set Γa : AuxGraph n := ⟨bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y),
    bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y, 0)⟩ with hΓa
  have hTa : TreeEdges Γa.black := hTb
  have hUa : TreeEdges (Γa.blue.map fun e => (e.1, e.2.1)) := by
    simpa [hΓa, List.map_map, Function.comp_def] using hTu
  obtain ⟨Ct, hCt, hT⟩ := VR1Graph_treeZ (d := d) (by omega) Γa hTa hUa τ₁ hτ₁ hτ₁'
  refine ⟨Ct, hCt, fun W hWn a K lam h hK hlam hh x y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWn
  have hW0 : (0 : ℝ) < W := by linarith
  set A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun _ p r =>
    (W : ℝ) ^ (-4 : ℝ) * AuxTreeZ.brk d W p r ^ (-sb) with hA
  have hA0 : ∀ j p r, 0 ≤ A j p r := fun j p r => by
    have := AuxTreeZ.brk_pos hWn p r; simp only [hA]; positivity
  obtain ⟨hsumZ, hvalZ⟩ := hT W hWn A (fun j p r => by rw [abs_of_nonneg (hA0 j p r)]) x y
  -- the black and blue factors as functions of the increment
  set G : (Fin d → ℤ) → ℝ := fun v => (W : ℝ) ^ ((d : ℝ) - 2) * ((zdInf v : ℝ) + W) ^ (-β)
    with hG
  set G' : (Fin d → ℤ) → ℝ := fun v => (W : ℝ) ^ ((d : ℝ) - 4) * ((zdInf v : ℝ) + W) ^ (-sb)
    with hG'
  have hcomp : ∀ (i : Fin Γ.comps.length) (v : Fin d → ℤ), ‖h i v‖ ≤
      K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        (if i ∈ bl then G v else 1) * (if i ∈ bu then G' v else 1) := by
    intro i v
    have hP : 0 ≤ K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) := by
      have := hlam i; positivity
    have hi := hh i v
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases hWT _ hmem with ⟨w, hw⟩ | ⟨o, ho⟩
    · have hm : VR1Graph_maj W τ₁ j₀ i Γ.comps[i] v =
          VR1Graph_u W ((d : ℝ) - 2) v * VR1Graph_u W ((d : ℝ) - 2) v := by
        unfold VR1Graph_maj; rw [hw]
      rw [hm] at hi
      exact VR1Graph_flag_two _ _ _ _ _ hP (VR1Graph_u_nonneg _ _ _)
        (VR1Graph_u_le_one hWn (by linarith) v)
        (VR1Graph_u_le hWn (by linarith) (by linarith) v)
        (VR1Graph_u_le hWn (by linarith) (by linarith) v) _ _ hi
    · have hnb : ¬ (i ∈ bl ∧ i ∈ bu) := fun ⟨h1, h2⟩ => by
        obtain ⟨w, hw⟩ := hboth i h1 h2; rw [hw] at ho; cases ho
      by_cases hij : i.1 = j₀
      · have hm : VR1Graph_maj W τ₁ j₀ i Γ.comps[i] v = VR1Graph_u W ((d : ℝ) - 4) v := by
          unfold VR1Graph_maj; rw [ho]; simp [hij]
        rw [hm] at hi
        exact VR1Graph_flag_one _ _ _ _ _ hP (VR1Graph_u_le_one hWn (by linarith) v) _ _ hi
          (fun h1 => absurd hij (hbk0 i h1))
          (fun _ => VR1Graph_u_le hWn (by linarith) (by linarith) v)
          (fun h1 h2 => hnb ⟨h1, h2⟩)
      · have hm : VR1Graph_maj W τ₁ j₀ i Γ.comps[i] v =
            VR1Graph_u W ((d : ℝ) - 2 - τ₁) v := by
          unfold VR1Graph_maj; rw [ho]; simp [hij]
        rw [hm] at hi
        exact VR1Graph_flag_one _ _ _ _ _ hP (VR1Graph_u_le_one hWn (by linarith) v) _ _ hi
          (fun _ => VR1Graph_u_le hWn (by linarith) (by linarith) v)
          (fun _ => VR1Graph_u_le hWn (by linarith) (by linarith) v)
          (fun h1 h2 => hnb ⟨h1, h2⟩)
  set M : ℝ := ‖a‖ * (∏ i : Fin Γ.comps.length,
      (K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2))) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∏ i : Fin Γ.comps.length,
        (K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) :=
      Finset.prod_nonneg fun i _ => by have := hlam i; positivity
    positivity
  have hbrk : ∀ p q : Fin d → ℤ, AuxTreeZ.brk d W p q = (zdInf (q - p) : ℝ) + W := by
    intro p q; unfold AuxTreeZ.brk; rw [← neg_sub, zdInf_neg]
  have hpt : ∀ σ : Fin n → Fin d → ℤ, ‖a * ∏ i, h i (Sum.elim ![x, y] σ Γ.comps[i].y -
      Sum.elim ![x, y] σ Γ.comps[i].x)‖ ≤ M * Γa.termZ d W β A x y σ := by
    intro σ
    set σ' : Atom 2 n → Fin d → ℤ := Sum.elim ![x, y] σ with hσ'
    set B : Fin Γ.comps.length → ℝ := fun i =>
      AuxTreeZ.bB d W β (σ' Γ.comps[i].x) (σ' Γ.comps[i].y) with hBdef
    set B' : Fin Γ.comps.length → ℝ := fun i => A 0 (σ' Γ.comps[i].x) (σ' Γ.comps[i].y)
      with hB'def
    have hGB : ∀ i : Fin Γ.comps.length,
        G (σ' Γ.comps[i].y - σ' Γ.comps[i].x) = (W : ℝ) ^ (d : ℝ) * B i := by
      intro i
      simp only [hG, hBdef, AuxTreeZ.bB, hbrk]
      rw [← mul_assoc, ← Real.rpow_add hW0]; ring_nf
    have hGB' : ∀ i : Fin Γ.comps.length,
        G' (σ' Γ.comps[i].y - σ' Γ.comps[i].x) = (W : ℝ) ^ (d : ℝ) * B' i := by
      intro i
      simp only [hG', hB'def, hA, hbrk]
      rw [← mul_assoc, ← Real.rpow_add hW0]; ring_nf
    have h1 : ∏ i, ‖h i (σ' Γ.comps[i].y - σ' Γ.comps[i].x)‖ ≤
        ∏ i, (K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
          (if i ∈ bl then (W : ℝ) ^ (d : ℝ) * B i else 1) *
          (if i ∈ bu then (W : ℝ) ^ (d : ℝ) * B' i else 1)) := by
      refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
      rw [← hGB i, ← hGB' i]
      exact hcomp i _
    rw [VR1Graph_prod_flags _ _ B B' bl bu hbl hbu] at h1
    have htermZ : Γa.termZ d W β A x y σ = (bl.map B).prod * (bu.map B').prod := by
      simp only [AuxGraph.termZ, hΓa, List.map_map, Function.comp_def]
      congr 2
      refine List.map_congr_left fun i _ => ?_
      exact abs_of_nonneg (hA0 0 _ _)
    rw [htermZ, norm_mul, norm_prod]
    calc ‖a‖ * ∏ i, ‖h i (σ' Γ.comps[i].y - σ' Γ.comps[i].x)‖
        ≤ ‖a‖ * ((∏ i : Fin Γ.comps.length,
            (K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2))) *
            (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
            ((bl.map B).prod * (bu.map B').prod)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = M * ((bl.map B).prod * (bu.map B').prod) := by rw [hM]; ring
  have hsum : Summable (fun σ : Fin n → Fin d → ℤ => ‖a * ∏ i, h i (Sum.elim ![x, y] σ
      Γ.comps[i].y - Sum.elim ![x, y] σ Γ.comps[i].x)‖) :=
    Summable.of_nonneg_of_le (fun σ => norm_nonneg _) hpt (hsumZ.mul_left M)
  refine ⟨hsum, ?_⟩
  have habs := hsum.tsum_le_tsum hpt (hsumZ.mul_left M)
  rw [tsum_mul_left] at habs
  refine habs.trans ((mul_le_mul_of_nonneg_left hvalZ hM0).trans (le_of_eq ?_))
  -- the powers of `W`
  have hprod : ∏ i : Fin Γ.comps.length,
      (K * lam i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) =
      K ^ Γ.comps.length * (∏ i, lam i) *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Real.rpow_sum_of_pos hW0]
  have hexp : (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
      (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * n) =
      (W : ℝ) ^ (2 * τ₁ * n) * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) := by
    rw [hlb, hlu, ← Real.rpow_natCast ((W : ℝ) ^ (d : ℝ)), ← Real.rpow_mul hW0.le,
      ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    congr 1
    rw [ord_eq_sum, ← Finset.sum_div, ← Finset.sum_mul, Finset.sum_neg_distrib]
    push_cast
    ring
  rw [hM, hprod]
  calc ‖a‖ * (K ^ Γ.comps.length * (∏ i, lam i) *
        (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2))) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
        (Ct * (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * n) * (W : ℝ) ^ (-6 : ℝ) *
          AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)))
      = Ct * ‖a‖ * K ^ Γ.comps.length * (∏ i, lam i) *
          ((W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
            (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
            (W : ℝ) ^ ((-(d : ℝ) + 2 * τ₁) * n)) * (W : ℝ) ^ (-6 : ℝ) *
          AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by ring
    _ = _ := by rw [hexp]; ring

set_option maxHeartbeats 1000000 in
/-- **The comparison of two sets of kernels on `ℤ^d`**: for a graph as in `VR1Graph_graphZ` and
`0 < τ₁ ≤ 1/4` there is `C₀` such that for `W ≥ 1`, coefficients `a₁, a₂` and kernels `h₁, h₂`
bounded by `K W^{-qᵢ d/2}` times the unmarked majorants, with `|a₁ - a₂| ≤ λ K_a` and
`|h₁ᵢ - h₂ᵢ| ≤ K λ W^{-qᵢ d/2}` times the marked majorant of `i`, the two values differ by at
most `C₀ K_a K^{|Γ|} λ W^{2τ₁ n} W^{-(n_Γ-4)d/2} W^{-6} ⟨x - y⟩^{-(2d-6-2τ₁)}`. -/
private theorem VR1Graph_zdStep (hd : 8 ≤ d) {n C : ℕ} (Γ : Graph 2 n)
    (hN : Γ.internalize.Normal C) (hDC : Γ.internalize.DoublyConnected)
    (hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o)
    (τ₁ : ℝ) (hτ₁ : 0 < τ₁) (hτ₁' : τ₁ ≤ 1 / 4) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ W : ℕ, 1 ≤ W → ∀ (a₁ a₂ : ℂ) (Ka K lam : ℝ)
      (h₁ h₂ : Fin Γ.comps.length → (Fin d → ℤ) → ℂ), 0 ≤ Ka → 0 ≤ K → 0 ≤ lam →
      ‖a₁ - a₂‖ ≤ lam * Ka → ‖a₁‖ ≤ Ka → ‖a₂‖ ≤ Ka →
      (∀ i v, ‖h₁ i v‖ ≤ K * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        VR1Graph_maj W τ₁ Γ.comps.length i Γ.comps[i] v) →
      (∀ i v, ‖h₂ i v‖ ≤ K * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        VR1Graph_maj W τ₁ Γ.comps.length i Γ.comps[i] v) →
      (∀ i v, ‖h₁ i v - h₂ i v‖ ≤ K * lam *
        (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) * VR1Graph_maj W τ₁ i i Γ.comps[i] v) →
      ∀ x y : Fin d → ℤ,
        ‖(∑' s : Fin n → Fin d → ℤ, a₁ * ∏ i, h₁ i (Sum.elim ![x, y] s Γ.comps[i].y -
            Sum.elim ![x, y] s Γ.comps[i].x)) -
          ∑' s : Fin n → Fin d → ℤ, a₂ * ∏ i, h₂ i (Sum.elim ![x, y] s Γ.comps[i].y -
            Sum.elim ![x, y] s Γ.comps[i].x)‖ ≤
          C₀ * Ka * K ^ Γ.comps.length * lam * (W : ℝ) ^ (2 * τ₁ * n) *
            (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by
  classical
  set len := Γ.comps.length with hlen
  -- the marked index of the `j`-th term: `j` for a `Θ` edge, none (`len`) for a waved edge
  set jm : Fin len → ℕ := fun j => if ∃ o, Γ.comps[j].kind = .theta o then j.1 else len with hjmdef
  have hjm : ∀ j : Fin len, ∀ i : Fin len, i.1 = jm j → ∃ o, Γ.comps[i].kind = .theta o := by
    intro j i hi
    simp only [hjmdef] at hi
    split_ifs at hi with h
    · have : i = j := Fin.ext hi; subst this; exact h
    · exact absurd hi (by have := i.2; omega)
  have hnone : ∀ i : Fin len, i.1 = len → ∃ o, Γ.comps[i].kind = .theta o := by
    intro i hi; exact absurd hi (by have := i.2; omega)
  choose Cj hCj hj using fun j : Fin len => VR1Graph_graphZ hd Γ hN hDC hWT (jm j) (hjm j) τ₁ hτ₁ hτ₁'
  obtain ⟨Cn, hCn, hn⟩ := VR1Graph_graphZ hd Γ hN hDC hWT len hnone τ₁ hτ₁ hτ₁'
  refine ⟨Cn + ∑ j, Cj j, add_nonneg hCn (Finset.sum_nonneg fun j _ => hCj j), fun W hWn a₁ a₂ Ka K lam h₁ h₂ hKa hK hlam had ha₁ ha₂
    hh₁ hh₂ hh x y => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWn
  set σ : (Fin n → Fin d → ℤ) → Atom 2 n → Fin d → ℤ := fun s => Sum.elim ![x, y] s with hσ
  set P₁ : (Fin n → Fin d → ℤ) → ℂ := fun s => ∏ i, h₁ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x)
  set P₂ : (Fin n → Fin d → ℤ) → ℂ := fun s => ∏ i, h₂ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x)
  set mm : (Fin n → Fin d → ℤ) → Fin len → Fin len → ℂ := fun s j i =>
    if i < j then h₁ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x)
    else if i = j then h₁ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x) -
      h₂ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x)
    else h₂ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x) with hmm
  set Bd : ℝ := Ka * K ^ len * lam * (W : ℝ) ^ (2 * τ₁ * n) *
    (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
    AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) with hBd
  -- the unmarked majorants are the majorants with the marked index `len`
  have hmaj_le : ∀ (j : Fin len) (i : Fin len) (v : Fin d → ℤ), i ≠ j →
      VR1Graph_maj W τ₁ len i Γ.comps[i] v = VR1Graph_maj W τ₁ (jm j) i Γ.comps[i] v := by
    intro j i v hij
    unfold VR1Graph_maj
    split
    · rfl
    · have h1 : i.1 ≠ len := by have := i.2; omega
      have h2 : i.1 ≠ jm j := by
        simp only [hjmdef]; split_ifs
        · exact fun h => hij (Fin.ext h)
        · exact h1
      simp [h1, h2]
  have hmaj_eq : ∀ (j : Fin len) (v : Fin d → ℤ),
      VR1Graph_maj W τ₁ j j Γ.comps[j] v = VR1Graph_maj W τ₁ (jm j) j Γ.comps[j] v := by
    intro j v
    unfold VR1Graph_maj
    split
    · rfl
    · rename_i hk
      have hθ : ∃ o, Γ.comps[j].kind = .theta o := by
        have hmem : Γ.comps[j] ∈ Γ.comps := List.getElem_mem _
        rcases hWT _ hmem with ⟨w, hw⟩ | h
        · exact absurd hw (hk w)
        · exact h
      have hj' : jm j = j.1 := by simp only [hjmdef]; rw [if_pos hθ]
      rw [hj']
  -- the coefficient term and the terms of the telescoping
  obtain ⟨hs₁, -⟩ := hn W hWn a₁ K (fun _ => 1) h₁ hK (fun _ => zero_le_one) (fun i v => by
    simpa using hh₁ i v) x y
  obtain ⟨hs₂, -⟩ := hn W hWn a₂ K (fun _ => 1) h₂ hK (fun _ => zero_le_one) (fun i v => by
    simpa using hh₂ i v) x y
  obtain ⟨hsc, hvc⟩ := hn W hWn (a₁ - a₂) K (fun _ => 1) h₁ hK (fun _ => zero_le_one)
    (fun i v => by simpa using hh₁ i v) x y
  have hterm : ∀ j : Fin len, Summable (fun s => ‖a₂ * ∏ i, mm s j i‖) ∧
      ∑' s, ‖a₂ * ∏ i, mm s j i‖ ≤ Cj j * Bd := by
    intro j
    set lj : Fin len → ℝ := fun i => if i = j then lam else 1 with hlj
    have hlj0 : ∀ i, 0 ≤ lj i := fun i => by simp only [hlj]; split_ifs <;> linarith
    have hprod : ∏ i, lj i = lam := by simp [hlj, Finset.prod_ite_eq']
    have hbd : ∀ i v, ‖(fun i v => if i < j then h₁ i v else if i = j then h₁ i v - h₂ i v
        else h₂ i v) i v‖ ≤ K * lj i * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
          VR1Graph_maj W τ₁ (jm j) i Γ.comps[i] v := by
      intro i v
      simp only [hlj]
      by_cases hij : i = j
      · subst hij
        simp only [lt_irrefl, ite_false, ite_true]
        rw [← hmaj_eq]; exact hh i v
      · simp only [hij, ite_false, mul_one]
        rw [← hmaj_le j i v hij]
        split_ifs
        · exact hh₁ i v
        · exact hh₂ i v
    obtain ⟨hs, hv⟩ := hj j W hWn a₂ K lj _ hK hlj0 hbd x y
    have heq : ∀ s, a₂ * ∏ i, mm s j i = a₂ * ∏ i, (fun i v => if i < j then h₁ i v else
        if i = j then h₁ i v - h₂ i v else h₂ i v) i (Sum.elim ![x, y] s Γ.comps[i].y -
          Sum.elim ![x, y] s Γ.comps[i].x) := by
      intro s; congr 1
    simp_rw [heq]
    refine ⟨hs, hv.trans ?_⟩
    rw [hprod, hBd]
    have := AuxTreeZ.brk_pos hWn x y
    have := hCj j
    have h0 : 0 ≤ Ka * K ^ len * lam * (W : ℝ) ^ (2 * τ₁ * n) *
        (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by positivity
    calc Cj j * ‖a₂‖ * K ^ len * lam * (W : ℝ) ^ (2 * τ₁ * n) *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁))
        ≤ Cj j * Ka * K ^ len * lam * (W : ℝ) ^ (2 * τ₁ * n) *
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by gcongr
      _ = _ := by ring
  -- the pointwise telescoping
  have hpt : ∀ s, a₁ * P₁ s - a₂ * P₂ s = (a₁ - a₂) * P₁ s + ∑ j, a₂ * ∏ i, mm s j i := by
    intro s
    rw [← Finset.mul_sum]
    have := RenormDiff_telescope len (fun i => h₁ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x))
      (fun i => h₂ i (σ s Γ.comps[i].y - σ s Γ.comps[i].x))
    simp only [P₁, P₂, hmm]
    rw [← this]; ring
  have hS₁ : Summable fun s => a₁ * P₁ s := hs₁.of_norm
  have hS₂ : Summable fun s => a₂ * P₂ s := hs₂.of_norm
  have hsumm : Summable fun s => ‖(a₁ - a₂) * P₁ s‖ + ∑ j, ‖a₂ * ∏ i, mm s j i‖ :=
    hsc.add (summable_sum fun j _ => (hterm j).1)
  rw [← hS₁.tsum_sub hS₂]
  calc ‖∑' s, (a₁ * P₁ s - a₂ * P₂ s)‖
      ≤ ∑' s, (‖(a₁ - a₂) * P₁ s‖ + ∑ j, ‖a₂ * ∏ i, mm s j i‖) := by
        refine tsum_of_norm_bounded hsumm.hasSum fun s => ?_
        rw [hpt]
        exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ = ∑' s, ‖(a₁ - a₂) * P₁ s‖ + ∑ j, ∑' s, ‖a₂ * ∏ i, mm s j i‖ := by
        rw [hsc.tsum_add (summable_sum fun j _ => (hterm j).1),
          Summable.tsum_finsetSum fun j _ => (hterm j).1]
    _ ≤ Cn * Bd + ∑ j, Cj j * Bd := by
        refine add_le_add ?_ (Finset.sum_le_sum fun j _ => (hterm j).2)
        refine hvc.trans ?_
        rw [hBd]
        have := AuxTreeZ.brk_pos hWn x y
        simp only [Finset.prod_const_one, mul_one]
        calc Cn * ‖a₁ - a₂‖ * K ^ len * (W : ℝ) ^ (2 * τ₁ * n) *
              (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁))
            ≤ Cn * (lam * Ka) * K ^ len * (W : ℝ) ^ (2 * τ₁ * n) *
              (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              AuxTreeZ.brk d W x y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) := by gcongr
          _ = _ := by ring
    _ = (Cn + ∑ j, Cj j) * Bd := by rw [add_mul, Finset.sum_mul]
    _ = _ := by rw [hBd]; ring

end TreeZ

/-! ## The `Θ` edges on the torus -/

section TorTheta

/-- A finite family of positive numbers has a positive lower bound. -/
private theorem VR1Graph_pos_lower {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, t ≤ f i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- The matrices of the auxiliary edges, indexed by `ℕ`: `M i` for `i < |Γ|` and `0` beyond. -/
private def VR1Graph_ext {n : ℕ} (Γ : Graph 2 n) {ι : Type} (M : Fin Γ.comps.length → Matrix ι ι ℂ)
    (i : ℕ) : Matrix ι ι ℂ :=
  if h : i < Γ.comps.length then M ⟨i, h⟩ else 0

private theorem VR1Graph_ext_apply {n : ℕ} (Γ : Graph 2 n) {ι : Type}
    (M : Fin Γ.comps.length → Matrix ι ι ℂ) (i : Fin Γ.comps.length) :
    VR1Graph_ext Γ M i = M i := by
  unfold VR1Graph_ext
  split_ifs with h
  · rfl
  · exact absurd i.2 h

/-- The value of the auxiliary graph as a sum over the labellings of the product over the
components of `Γ`. -/
private theorem VR1Graph_val_toAux {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Graph 2 n)
    (D : Data ι) (e : Fin 2 → ι) :
    (RenormDiff_toAux Γ).val D e = ∑ s : Fin n → ι, Γ.coeff.eval D.m *
      ∏ i : Fin Γ.comps.length, Comp.val D (Sum.elim e s) (RenormDiff_auxComp i Γ.comps[i]) := by
  unfold Graph.val Graph.term
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [RenormDiff_toAux, List.map_ofFn, List.prod_ofFn, Function.comp_def]

set_option maxHeartbeats 1000000 in
/-- **The `Θ` edges on the torus**: for a graph of waved and `Θ` edges whose internal form is
normal regular and doubly connected, there are `τ' > 0` and `W₀` such that for every two
families `A`, `B` of matrices on the `Θ` edges with `|Aᵢ|, |Bᵢ| ≤ W^{τ'} W^{-(kᵢ-2)d/2} B` and
`|Aᵢ - Bᵢ| ≤ η W^{τ'} W^{-(kᵢ-2)d/2} B̃` (`kᵢ` the order of the label of the `i`-th edge), the
values of the graph with its `Θ` edges reading `A` and `B` differ by at most
`η W^{-(n_Γ-4)d/2} W^{-6} ⟨x - y⟩^{-(2d-6-τ)}`: each term of the telescoping is a graph of
[I, Cor 6.13] with one marked edge (`detAuxTilde`). -/
private theorem VR1Graph_torTheta (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    {m C : ℕ} (Γ : Graph 2 m) (hN : Γ.internalize.Normal C)
    (hDC : Γ.internalize.DoublyConnected)
    (hK : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ A B : Fin Γ.comps.length → Matrix (Zd d L) (Zd d L) ℂ,
        (∀ i, (∃ o, Γ.comps[i].kind = .theta o) → ∀ u v, ‖A i u v‖ ≤ (W : ℝ) ^ τ' *
          (W : ℝ) ^ (-((((Kind.theta (RenormDiff_lab Γ.comps[i])).ord : ℤ) : ℝ) - 2) * d / 2) *
            bB d L W u v) →
        (∀ i, (∃ o, Γ.comps[i].kind = .theta o) → ∀ u v, ‖B i u v‖ ≤ (W : ℝ) ^ τ' *
          (W : ℝ) ^ (-((((Kind.theta (RenormDiff_lab Γ.comps[i])).ord : ℤ) : ℝ) - 2) * d / 2) *
            bB d L W u v) →
        (∀ i, (∃ o, Γ.comps[i].kind = .theta o) → ∀ u v, ‖A i u v - B i u v‖ ≤ z.im * (W : ℝ) ^ τ' *
          (W : ℝ) ^ (-((((Kind.theta (RenormDiff_lab Γ.comps[i])).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) →
        ∀ x y : Zd d L,
          ‖(RenormDiff_toAux Γ).val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ A)) ![x, y] -
              (RenormDiff_toAux Γ).val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ B)) ![x, y]‖ ≤
            z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ)) := by
  classical
  set len := Γ.comps.length with hlen
  set H := RenormDiff_toAux Γ with hH
  have hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o :=
    fun c hc => (hK c hc).2.2
  obtain ⟨hHN, hHDC⟩ := RenormDiff_toAux_internal Γ hN hDC
  have hHB := RenormDiff_toAux_isBKind Γ hK
  set lab : Fin len → List ℕ := fun i => RenormDiff_lab Γ.comps[i] with hlabdef
  have hdet : ∀ j : Fin len, ∃ τ' : ℝ, 0 < τ' ∧ ∃ W₀ : ℝ, (∃ o, Γ.comps[j].kind = .theta o) →
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ M : ℕ → Matrix (Zd d L) (Zd d L) ℂ,
          (∀ (j' : ℕ) (u v : Zd d L), j' ≠ j → ‖M j' u v‖ ≤ (W : ℝ) ^ τ' * bB d L W u v) →
          (∀ u v : Zd d L, ‖M j u v‖ ≤
            (W : ℝ) ^ τ' * ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) →
          ∀ x y : Zd d L, H.absVal (auxData (Smat P.ψ W L) z M) ![x, y] ≤
            (W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
    intro j
    by_cases hj : ∃ o, Γ.comps[j].kind = .theta o
    · obtain ⟨o, ho⟩ := hj
      obtain ⟨τ', hτ', W₀, h⟩ := detAuxTilde d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε m C H j
        hHN hHDC hHB (RenormDiff_toAux_filter Γ hWT j o ho) (τ / 2) (by positivity)
      exact ⟨τ', hτ', W₀, fun _ => h⟩
    · exact ⟨1, one_pos, 0, fun h => absurd h hj⟩
  choose τd hτd Wd hWd using hdet
  obtain ⟨τm, hτm, hτmle⟩ := VR1Graph_pos_lower τd hτd
  refine ⟨τm, hτm, ∑ j, |Wd j| + max 1 (((len : ℝ) + 1) ^ (2 / τ)),
    fun W L _ hadm hW z hz A B hA hB hAB x y => ?_⟩
  have hWj : ∀ j : Fin len, Wd j ≤ W := by
    intro j
    have hle := Finset.single_le_sum (f := fun j => |Wd j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    have h1 : 0 ≤ max 1 (((len : ℝ) + 1) ^ (2 / τ)) := by positivity
    have := le_abs_self (Wd j)
    linarith
  have hsum0 : 0 ≤ ∑ j, |Wd j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hW1' : (1 : ℝ) ≤ W := by
    have := le_max_left 1 (((len : ℝ) + 1) ^ (2 / τ)); linarith
  have hWlen : ((len : ℝ) + 1) ^ (2 / τ) ≤ W := by
    have := le_max_right 1 (((len : ℝ) + 1) ^ (2 / τ)); linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  have him : 0 < z.im := im_pos_of_specDom hWn hz
  set η := z.im with hη
  have hτW : ∀ j : Fin len, (W : ℝ) ^ τm ≤ (W : ℝ) ^ τd j := fun j =>
    Real.rpow_le_rpow_of_exponent_le hW1' (hτmle j)
  set mu : Fin len → ℝ := fun i => (W : ℝ) ^ (-((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2)
    with hmudef
  have hmu0 : ∀ i, 0 < mu i := fun i => Real.rpow_pos_of_pos hW0 _
  set lam : Fin len → Fin len → ℝ := fun j i => (if i = j then η else 1) * mu i with hlamdef
  have hlam0 : ∀ j i, 0 < lam j i := fun j i => by
    simp only [hlamdef]; split_ifs <;> [exact mul_pos him (hmu0 i); simpa using hmu0 i]
  set X : Fin len → Fin len → Matrix (Zd d L) (Zd d L) ℂ := fun j i =>
    if i < j then A i else if i = j then A i - B i else B i with hXdef
  set M : Fin len → ℕ → Matrix (Zd d L) (Zd d L) ℂ := fun j i' =>
    if h : i' < len then (if ∃ o, Γ.comps[(⟨i', h⟩ : Fin len)].kind = .theta o then
      (((lam j ⟨i', h⟩)⁻¹ : ℝ) : ℂ) • X j ⟨i', h⟩ else 0) else 0 with hMdef
  have hMval : ∀ (jj i : Fin len), M jj i = if ∃ o, Γ.comps[i].kind = .theta o then
      (((lam jj i)⁻¹ : ℝ) : ℂ) • X jj i else 0 := by
    intro jj i
    show (if h : i.1 < len then _ else _) = _
    rw [dif_pos i.2]
  set e : Fin 2 → Zd d L := ![x, y] with he
  set coeff : ℂ := Γ.coeff.eval (msc z) with hcoeff
  set a : (Fin m → Zd d L) → Fin len → ℂ := fun s i =>
    Comp.val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ A)) (Sum.elim e s)
      (RenormDiff_auxComp i Γ.comps[i]) with hadef
  set b : (Fin m → Zd d L) → Fin len → ℂ := fun s i =>
    Comp.val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ B)) (Sum.elim e s)
      (RenormDiff_auxComp i Γ.comps[i]) with hbdef
  set mm : (Fin m → Zd d L) → Fin len → Fin len → ℂ := fun s j i =>
    if i < j then a s i else if i = j then a s i - b s i else b s i with hmmdef
  have hval : H.val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ A)) e -
      H.val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ B)) e =
        ∑ s, coeff * ∑ j, ∏ i, mm s j i := by
    rw [hH, VR1Graph_val_toAux, VR1Graph_val_toAux, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    change coeff * _ - coeff * _ = _
    rw [← mul_sub, RenormDiff_telescope]
  -- the factor of a component on the auxiliary records
  have hfac : ∀ (MM : ℕ → Matrix (Zd d L) (Zd d L) ℂ) (s : Fin m → Zd d L) (i : Fin len)
      (o : List ℕ), Γ.comps[i].kind = .theta o →
      Comp.val (auxData (Smat P.ψ W L) z MM) (Sum.elim e s) (RenormDiff_auxComp i Γ.comps[i]) =
        MM i (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y) := by
    intro MM s i o ho
    rw [RenormDiff_auxComp_theta _ _ o ho, RenormDiff_val_aux]
  have hext : ∀ (MM : Fin len → Matrix (Zd d L) (Zd d L) ℂ) (i : Fin len),
      VR1Graph_ext Γ MM i = MM i := by
    intro MM i
    unfold VR1Graph_ext
    split_ifs with h
    · rfl
    · exact absurd i.2 h
  have hterm : ∀ j : Fin len, ∑ s, ‖coeff‖ * ∏ i, ‖mm s j i‖ ≤
      η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
    intro j
    have hb0 : 0 ≤ η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by
      have := RenormDiff_brk_pos (d := d) (L := L) hWn x y; positivity
    have hjmem : Γ.comps[j] ∈ Γ.comps := List.getElem_mem _
    rcases hWT _ hjmem with ⟨w, hw⟩ | ⟨o, ho⟩
    · have hz0 : ∀ s, mm s j j = 0 := by
        intro s
        simp only [hmmdef, lt_irrefl, ite_false, ite_true, hadef, hbdef]
        rw [RenormDiff_auxComp_waved _ _ w hw, ← RenormDiff_val_waved_aux (Smat P.ψ W L) z 0 _ _ _ w hw,
          ← RenormDiff_val_waved_aux (Smat P.ψ W L) z 0 _ _ _ w hw, sub_self]
      have : ∀ s, ∏ i, ‖mm s j i‖ = 0 := fun s =>
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz0 s, norm_zero])
      simp only [this, mul_zero, Finset.sum_const_zero]
      exact hb0
    · have hpt : ∀ s i, ‖mm s j i‖ = lam j i * ‖Comp.val (auxData (Smat P.ψ W L) z (M j))
          (Sum.elim e s) (RenormDiff_auxComp i Γ.comps[i])‖ := by
        intro s i
        have himem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
        rcases hWT _ himem with ⟨w', hw'⟩ | ⟨o', ho'⟩
        · have hij : i ≠ j := by
            rintro rfl; rw [hw'] at ho; cases ho
          have hlab0 : lab i = [] := RenormDiff_lab_waved _ w' hw'
          have hmu1 : mu i = 1 := by simp [hmudef, hlab0, Kind.ord]
          have hlam1 : lam j i = 1 := by simp [hlamdef, hij, hmu1]
          rw [hlam1, one_mul]
          have hva : a s i = Comp.val (auxData (Smat P.ψ W L) z (M j)) (Sum.elim e s)
              (RenormDiff_auxComp i Γ.comps[i]) := by
            simp only [hadef]
            rw [RenormDiff_auxComp_waved _ _ w' hw',
              ← RenormDiff_val_waved_aux (Smat P.ψ W L) z 0 _ _ _ w' hw',
              ← RenormDiff_val_waved_aux (Smat P.ψ W L) z 0 _ _ _ w' hw']
          have hab : a s i = b s i := by
            simp only [hadef, hbdef]
            rw [RenormDiff_auxComp_waved _ _ w' hw',
              ← RenormDiff_val_waved_aux (Smat P.ψ W L) z 0 _ _ _ w' hw',
              ← RenormDiff_val_waved_aux (Smat P.ψ W L) z 0 _ _ _ w' hw']
          simp only [hmmdef, hij, ite_false]
          split_ifs
          · rw [hva]
          · rw [← hab, hva]
        · rw [hfac (M j) s i o' ho']
          have hMji : M j i = (((lam j i)⁻¹ : ℝ) : ℂ) • X j i := by
            rw [hMval, if_pos ⟨o', ho'⟩]
          rw [hMji, Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (hlam0 j i)), ← mul_assoc, mul_inv_cancel₀ (hlam0 j i).ne',
            one_mul]
          have ha : a s i = A i (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y) := by
            simp only [hadef]; rw [hfac _ s i o' ho', hext]
          have hb : b s i = B i (Sum.elim e s Γ.comps[i].x) (Sum.elim e s Γ.comps[i].y) := by
            simp only [hbdef]; rw [hfac _ s i o' ho', hext]
          simp only [hmmdef, hXdef]
          split_ifs <;> simp [ha, hb, Matrix.sub_apply]
      have hsum : ∑ s, ‖coeff‖ * ∏ i, ‖mm s j i‖ =
          (∏ i, lam j i) * H.absVal (auxData (Smat P.ψ W L) z (M j)) e := by
        rw [hH, RenormDiff_absVal_toAux, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp_rw [hpt s]
        rw [Finset.prod_mul_distrib]
        change _ = _ * (‖Γ.coeff.eval (msc z)‖ * _)
        ring
      have hprod : ∏ i, lam j i = η * ∏ i, mu i := by
        simp only [hlamdef]
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
        simp
      have hmuprod : (∏ i, mu i) * (W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2)) =
          (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) := by
        simp only [hmudef]
        rw [← Real.rpow_sum_of_pos hW0, ← Real.rpow_add hW0]
        have hord := RenormDiff_ord_toAux Γ hWT
        congr 1
        rw [← hord]
        have h' : ∀ i : Fin len, -((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * d / 2 =
            ((((Kind.theta (lab i)).ord : ℤ) : ℝ) - 2) * (-(d : ℝ) / 2) := fun i => by ring
        simp_rw [h', ← Finset.sum_mul]
        simp only [hlabdef]
        ring
      have hM1 : ∀ (j' : ℕ) (u v : Zd d L), j' ≠ j →
          ‖M j j' u v‖ ≤ (W : ℝ) ^ τd j * bB d L W u v := by
        intro j' u v hj'
        by_cases h : j' < len
        · set i : Fin len := ⟨j', h⟩ with hi
          have hij : i ≠ j := fun h' => hj' (congrArg Fin.val h')
          by_cases hθi : ∃ o, Γ.comps[i].kind = .theta o
          swap
          · have hM0 : M j j' = 0 := by
              rw [show M j j' = M j i from rfl, hMval, if_neg hθi]
            rw [hM0, Matrix.zero_apply, norm_zero]
            exact mul_nonneg (by positivity) (bB_pos₁ hWn u v).le
          have hMji : M j j' = (((lam j i)⁻¹ : ℝ) : ℂ) • X j i := by
            rw [show M j j' = M j i from rfl, hMval, if_pos hθi]
          have hlam : lam j i = mu i := by simp [hlamdef, hij]
          rw [hMji, Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (hlam0 j i)), hlam]
          have hX : ‖X j i u v‖ ≤ (W : ℝ) ^ τd j * mu i * bB d L W u v := by
            have hA' := (hA i hθi u v).trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hτW j) (hmu0 i).le) (bB_pos₁ hWn u v).le)
            have hB' := (hB i hθi u v).trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hτW j) (hmu0 i).le) (bB_pos₁ hWn u v).le)
            simp only [hXdef]
            split_ifs <;> first | exact hA' | exact hB'
          have hmi := (hmu0 i).ne'
          calc (mu i)⁻¹ * ‖X j i u v‖ ≤ (mu i)⁻¹ * ((W : ℝ) ^ τd j * mu i * bB d L W u v) :=
                mul_le_mul_of_nonneg_left hX (inv_nonneg.2 (hmu0 i).le)
            _ = _ := by field_simp
        · simp only [hMdef, h, dite_false, Matrix.zero_apply, norm_zero]
          exact mul_nonneg (by positivity) (bB_pos₁ hWn u v).le
      have hM2 : ∀ u v : Zd d L, ‖M j j u v‖ ≤
          (W : ℝ) ^ τd j * ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4))) := by
        intro u v
        have hMjj : M j j = (((lam j j)⁻¹ : ℝ) : ℂ) • (A j - B j) := by
          rw [hMval, if_pos ⟨o, ho⟩]
          simp [hXdef]
        have hlam : lam j j = η * mu j := by simp [hlamdef]
        rw [hMjj, Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 (hlam0 j j)), hlam]
        have hbt : 0 ≤ (W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)) := by
          have := RenormDiff_brk_pos (d := d) (L := L) hWn u v; positivity
        have hD'' : ‖(A j - B j) u v‖ ≤ η * (W : ℝ) ^ τd j * mu j *
            ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4))) := by
          refine (hAB j ⟨o, ho⟩ u v).trans ?_
          gcongr
          exact hτmle j
        have hpos : 0 < η * mu j := mul_pos him (hmu0 j)
        calc (η * mu j)⁻¹ * ‖(A j - B j) u v‖ ≤ (η * mu j)⁻¹ * (η * (W : ℝ) ^ τd j * mu j *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) :=
            mul_le_mul_of_nonneg_left hD'' (inv_nonneg.2 hpos.le)
          _ = _ := by have := (hmu0 j).ne'; have := him.ne'; field_simp
      have habs := hWd j ⟨o, ho⟩ W L hadm (hWj j) z hz (M j) hM1 hM2 x y
      rw [hsum, hprod]
      have hmu0' : 0 ≤ ∏ i, mu i := Finset.prod_nonneg fun i _ => (hmu0 i).le
      calc η * (∏ i, mu i) * H.absVal (auxData (Smat P.ψ W L) z (M j)) e
          ≤ η * (∏ i, mu i) * ((W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2))) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = η * ((∏ i, mu i) * (W : ℝ) ^ (-(((H.ord : ℝ) - 4) * d / 2))) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := by ring
        _ = _ := by rw [hmuprod]
  -- the sum over the marked edges
  have hbrk := RenormDiff_brk_pos (d := d) (L := L) hWn x y
  have hlenτ : (len : ℝ) * brk d L W x y ^ (-(τ / 2)) ≤ 1 := by
    have h1 : brk d L W x y ^ (-(τ / 2)) ≤ (W : ℝ) ^ (-(τ / 2)) :=
      Real.rpow_le_rpow_of_nonpos hW0 (RenormDiff_le_brk x y) (by linarith)
    have h2 : ((len : ℝ) + 1) ≤ (W : ℝ) ^ (τ / 2) := by
      calc ((len : ℝ) + 1) = (((len : ℝ) + 1) ^ (2 / τ)) ^ (τ / 2) := by
            rw [← Real.rpow_mul (by positivity)]; field_simp; simp
        _ ≤ (W : ℝ) ^ (τ / 2) := Real.rpow_le_rpow (by positivity) hWlen (by positivity)
    have h3 : (W : ℝ) ^ (-(τ / 2)) * (W : ℝ) ^ (τ / 2) = 1 := by
      rw [← Real.rpow_add hW0]; simp
    have h4 : 0 ≤ (W : ℝ) ^ (-(τ / 2)) := by positivity
    calc (len : ℝ) * brk d L W x y ^ (-(τ / 2)) ≤ (len : ℝ) * (W : ℝ) ^ (-(τ / 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ((len : ℝ) + 1) * (W : ℝ) ^ (-(τ / 2)) := by nlinarith
      _ ≤ (W : ℝ) ^ (τ / 2) * (W : ℝ) ^ (-(τ / 2)) := mul_le_mul_of_nonneg_right h2 h4
      _ = 1 := by rw [mul_comm, h3]
  have hsplit : brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) =
      brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ)) * brk d L W x y ^ (-(τ / 2)) := by
    rw [← Real.rpow_add hbrk]; ring_nf
  rw [hval]
  calc ‖∑ s, coeff * ∑ j, ∏ i, mm s j i‖ ≤ ∑ s, ‖coeff‖ * ∑ j, ∏ i, ‖mm s j i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq
          (Finset.sum_congr rfl fun j _ => norm_prod _ _))) (norm_nonneg _)
    _ = ∑ j, ∑ s, ‖coeff‖ * ∏ i, ‖mm s j i‖ := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _j : Fin len, η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ / 2)) := Finset.sum_le_sum fun j _ => hterm j
    _ = (η * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          brk d L W x y ^ (-(2 * (d : ℝ) - 6 - τ))) *
            ((len : ℝ) * brk d L W x y ^ (-(τ / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsplit]; ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hlenτ

end TorTheta

/-! ## Window facts -/

section Window

/-- On `adm(c₀, c₁)`: `W ≤ L` and `L^{c₁} ≤ W`. -/
private theorem VR1Graph_adm {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) {W L : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) : (W : ℝ) ≤ L ∧ (L : ℝ) ^ c₁ ≤ W := by
  obtain ⟨h1, h2⟩ := hadm
  refine ⟨?_, h1⟩
  have hL1 : (1 : ℝ) ≤ L := by
    have : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact_mod_cast this
  calc (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := h2
    _ ≤ (L : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = L := Real.rpow_one _

end Window

/-! ## Step one: the `Θ` edges on the torus -/

section StepT

/-- The cut of a kernel on `ℤ^d` at `|v|_∞ ≤ R`. -/
private def VR1Graph_cut (R : ℕ) (f : (Fin d → ℤ) → ℂ) (v : Fin d → ℤ) : ℂ :=
  if zdInf v ≤ R then f v else 0

private theorem VR1Graph_norm_cut_le (R : ℕ) (f : (Fin d → ℤ) → ℂ) (v : Fin d → ℤ) :
    ‖VR1Graph_cut R f v‖ ≤ ‖f v‖ := by
  unfold VR1Graph_cut; split_ifs <;> simp

/-- The value on a deterministic record is the value of the auxiliary graph whose `Θ` edges read
the chains of the record. -/
private theorem VR1Graph_val_eq_aux {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Graph 2 n) (hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o)
    (S : Matrix ι ι ℝ) (z : ℂ) (Ms : ℕ → Matrix ι ι ℂ) (e : Fin 2 → ι) :
    Γ.val (detData S z Ms) e = (RenormDiff_toAux Γ).val (auxData S z (VR1Graph_ext Γ
      (fun i => (detData S z Ms).chain (RenormDiff_lab Γ.comps[i])))) e := by
  rw [VR1Graph_val_toAux]
  unfold Graph.val
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [RenormDiff_term_eq]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
  rcases hWT _ hmem with ⟨w, hw⟩ | ⟨o, ho⟩
  · rw [RenormDiff_auxComp_waved _ _ w hw]
    exact RenormDiff_val_waved_aux S z Ms _ _ _ w hw
  · rw [RenormDiff_auxComp_theta _ _ o ho, RenormDiff_val_aux, RenormDiff_val_theta _ _ _ o ho,
      VR1Graph_ext_apply, RenormDiff_lab_theta _ o ho]

/-- [I, Lemma 6.2] on `ℤ^d` for the chains of the family `KI(E)` at `S_∞ = Sinf ψ W`, with `W₀`
uniform in `|E| < 2 − κ`. -/
private theorem VR1Graph_chainZ_bound (hd : 8 ≤ d) (P : Profile d) {κ : ℝ} (N : ℕ)
    (KI : ℝ → KerInf d) (hKI : ValZ.SelUnif κ N KI) (o : List ℕ) (ho : labelOK N o = true)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ v : Fin d → ℤ,
      ‖chainZ (Sinf P.ψ W) (KI E) W o v‖ ≤
        (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - σ))) := by
  obtain ⟨C, Ws, hs⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  refine ValZ_uniform (κ := κ) (fun E W => ∀ v : Fin d → ℤ,
      ‖chainZ (Sinf P.ψ W) (KI E) W o v‖ ≤
        (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - σ)))) fun Esel hsel => ?_
  have hK : ∀ l ∈ o, KerInfHyp (fun l W => KI (Esel W) l W) l := by
    intro l hl
    simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho
    obtain ⟨⟨h4, hN⟩, h2⟩ := ho l hl
    exact hKI Esel hsel l h4 hN (Nat.even_iff.2 h2)
  obtain ⟨W₀, h⟩ := chainInf d (by omega) P.ψ P.cψ (ValZ_shape P) C _ o hK σ hσ
  exact ⟨max W₀ Ws, fun W hW v => h W ((le_max_left _ _).trans hW) _
    (hs W ((le_max_right _ _).trans hW)) v⟩

/-- `‖v - u‖_L = ‖u - v‖_L` read through the lift: `|[v - u]|_∞ + W = ⟨u - v⟩`. -/
private theorem VR1Graph_brk_zlift {L W : ℕ} [NeZero L] (u v : Zd d L) :
    (zdInf (zlift (v - u)) : ℝ) + W = brk d L W u v := by
  unfold brk
  rw [VR1Graph_zdInf_zlift, ← neg_sub, zdistInf_neg]

/-- `⟨u - v⟩^{σ'} ≤ W^{τ'}` on `adm(c₀, c₁)` for `σ' ≤ c₁ τ'/4` and `W ≥ 2`. -/
private theorem VR1Graph_brk_pow {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) {W L : ℕ}
    [NeZero L] (hadm : (W, L) ∈ adm c₀ c₁) (hW : 2 ≤ W) {σ' τ' : ℝ} (hσ' : 0 ≤ σ')
    (hστ : σ' ≤ c₁ * τ' / 4) (u v : Zd d L) : brk d L W u v ^ σ' ≤ (W : ℝ) ^ τ' := by
  have hW2 : (2 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hL2 : (2 : ℝ) ≤ L := hW2.trans hWL
  have hL0 : (0 : ℝ) < L := by linarith
  have hb : brk d L W u v ≤ (L : ℝ) ^ (2 : ℝ) := by
    have h1 : (zdistInf d L (u - v) : ℝ) ≤ L := by
      have := zdistInf_le_half d L (u - v)
      have : (zdistInf d L (u - v) : ℝ) ≤ (L / 2 : ℕ) := by exact_mod_cast this
      have h' : ((L / 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.div_le_self L 2
      linarith
    unfold brk
    rw [Real.rpow_two]
    nlinarith
  have hb0 : 0 ≤ brk d L W u v := by unfold brk; positivity
  have hLc : (L : ℝ) ≤ (W : ℝ) ^ (1 / c₁) := by
    calc (L : ℝ) = ((L : ℝ) ^ c₁) ^ (1 / c₁) := by
          rw [← Real.rpow_mul hL0.le, mul_one_div_cancel hc₁.ne', Real.rpow_one]
      _ ≤ (W : ℝ) ^ (1 / c₁) := Real.rpow_le_rpow (by positivity) hLW (by positivity)
  calc brk d L W u v ^ σ' ≤ ((L : ℝ) ^ (2 : ℝ)) ^ σ' := Real.rpow_le_rpow hb0 hb hσ'
    _ = (L : ℝ) ^ (2 * σ') := by rw [← Real.rpow_mul hL0.le]
    _ ≤ ((W : ℝ) ^ (1 / c₁)) ^ (2 * σ') := Real.rpow_le_rpow hL0.le hLc (by positivity)
    _ = (W : ℝ) ^ (2 * σ' / c₁) := by rw [← Real.rpow_mul (by positivity)]; ring_nf
    _ ≤ (W : ℝ) ^ τ' := by
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        rw [div_le_iff₀ hc₁]; nlinarith

/-- The cut `R = ⌊L/(4(n+2))⌋` is at least `L/(8(n+2))` for `L ≥ 8(n+2)`. -/
private theorem VR1Graph_R_ge (n L : ℕ) (hL : 8 * (n + 2) ≤ L) :
    (L : ℝ) / (8 * ((n : ℝ) + 2)) ≤ ((L / (4 * (n + 2)) : ℕ) : ℝ) := by
  have h1 : L / (4 * (n + 2)) * (4 * (n + 2)) + 4 * (n + 2) > L := by
    have := Nat.lt_div_mul_add (a := L) (b := 4 * (n + 2)) (by omega)
    linarith
  have h2 : (L : ℝ) < ((L / (4 * (n + 2)) : ℕ) : ℝ) * (4 * ((n : ℝ) + 2)) + 4 * ((n : ℝ) + 2) := by
    exact_mod_cast h1
  have h3 : (8 * ((n : ℝ) + 2)) ≤ L := by exact_mod_cast hL
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- A long edge of the cut costs `η`: `W² R^{σ'-2} ≤ η` for `z ∈ 𝐃(κ, ε)`, `σ' ≤ ε/2` and
`L^{ε/2} ≥ (8(n+2))²`, `L ≥ 8(n+2)`. -/
private theorem VR1Graph_cut_small {κ ε : ℝ} (_hε : 0 < ε) {W L n : ℕ} [NeZero L] {z : ℂ}
    (hz : z ∈ specDom κ ε W L) (hL : 8 * (n + 2) ≤ L)
    (hLε : (8 * ((n : ℝ) + 2)) ^ (2 : ℝ) ≤ (L : ℝ) ^ (ε / 2)) {σ' : ℝ} (hσ0 : 0 ≤ σ')
    (hσ' : σ' ≤ ε / 2) (hσ1 : σ' ≤ 1) :
    (W : ℝ) ^ (2 : ℝ) * ((L / (4 * (n + 2)) : ℕ) : ℝ) ^ (σ' - 2) ≤ z.im := by
  set c : ℝ := 8 * ((n : ℝ) + 2) with hc
  have hc0 : 0 < c := by positivity
  have hcL : c ≤ L := by rw [hc]; exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hR := VR1Graph_R_ge n L hL
  rw [← hc] at hR
  have hRp : 0 < (L : ℝ) / c := by positivity
  have h1 : ((L / (4 * (n + 2)) : ℕ) : ℝ) ^ (σ' - 2) ≤ ((L : ℝ) / c) ^ (σ' - 2) :=
    Real.rpow_le_rpow_of_nonpos hRp hR (by linarith)
  have h2 : ((L : ℝ) / c) ^ (σ' - 2) = (L : ℝ) ^ (σ' - 2) * c ^ (2 - σ') := by
    rw [Real.div_rpow hL0.le hc0.le, div_eq_mul_inv, ← Real.rpow_neg hc0.le]; ring_nf
  have h3 : c ^ (2 - σ') ≤ c ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h4 : (L : ℝ) ^ (σ' - 2) * (L : ℝ) ^ (ε / 2) ≤ (L : ℝ) ^ (-(2 - ε)) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hWW : 0 ≤ (W : ℝ) ^ (2 : ℝ) := by positivity
  have hη : (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im := hz.2.1
  have hη' : (W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ (-(2 - ε)) ≤ z.im := by
    rw [Real.rpow_neg hL0.le, Real.rpow_two, ← div_eq_mul_inv]; exact hη
  have hL2 : 0 ≤ (L : ℝ) ^ (σ' - 2) := by positivity
  calc (W : ℝ) ^ (2 : ℝ) * ((L / (4 * (n + 2)) : ℕ) : ℝ) ^ (σ' - 2)
      ≤ (W : ℝ) ^ (2 : ℝ) * (((L : ℝ) / c) ^ (σ' - 2)) := mul_le_mul_of_nonneg_left h1 hWW
    _ = (W : ℝ) ^ (2 : ℝ) * ((L : ℝ) ^ (σ' - 2) * c ^ (2 - σ')) := by rw [h2]
    _ ≤ (W : ℝ) ^ (2 : ℝ) * ((L : ℝ) ^ (σ' - 2) * c ^ (2 : ℝ)) := by gcongr
    _ ≤ (W : ℝ) ^ (2 : ℝ) * ((L : ℝ) ^ (σ' - 2) * (L : ℝ) ^ (ε / 2)) := by gcongr
    _ ≤ (W : ℝ) ^ (2 : ℝ) * (L : ℝ) ^ (-(2 - ε)) := mul_le_mul_of_nonneg_left h4 hWW
    _ ≤ z.im := hη'

/-- **Step one.** On the torus the `Θ` edges of `Γ` are replaced by the cut kernels
`chainZ_o([v - u]) 1(|[v - u]| ≤ R)` of `ℤ^d`, `R = ⌊L/(4(n+2))⌋`, at the cost
`η W^{-(n_Γ-4)d/2} W^{-6} ⟨x⟩^{-(2d-6-τ)}`: the chain comparison and the cut, `W² R^{σ'-2} ≤ η`,
give the marked edge of `VR1Graph_torTheta`. -/
private theorem VR1Graph_stepT (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (N : ℕ) (KL : KerFamily d) (KI : ℝ → KerInf d)
    (hKL : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KL l ∧ KerBound KL l)
    (hKI : ValZ.SelUnif κ N KI) {n C : ℕ} (Γ : Graph 2 n) (hN : Γ.internalize.Normal C)
    (hDC : Γ.internalize.DoublyConnected)
    (hK : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (hcmp : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ,
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ u v : Zd d L,
          ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v -
              chainZ (Sinf P.ψ W) (KI z.re) W o (zlift (v - u))‖ ≤
            z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4))))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x : Zd d L,
        ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
            (RenormDiff_toAux Γ).val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ
              (fun i u v => VR1Graph_cut (L / (4 * (n + 2)))
                (chainZ (Sinf P.ψ W) (KI z.re) W (RenormDiff_lab Γ.comps[i])) (zlift (v - u)))))
              ![0, x]‖ ≤
          z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by
  classical
  set len := Γ.comps.length with hlen
  have hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o := by
    intro c hc
    rcases (hK c hc).2.2 with h | ⟨o, ho, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, ho⟩
  have hK' : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o) :=
    fun c hc => ⟨(hK c hc).1, (hK c hc).2.1, hWT c hc⟩
  obtain ⟨τ', hτ', W₁, hT⟩ := VR1Graph_torTheta hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε Γ hN hDC hK' τ hτ
  set σ' : ℝ := min (min (c₁ * τ' / 4) (ε / 2)) 1 with hσ'
  have hσ'0 : 0 < σ' := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hσ'a : σ' ≤ c₁ * τ' / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hσ'b : σ' ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hσ'c : σ' ≤ 1 := min_le_right _ _
  -- the bounds of one `Θ` edge
  have hidx : ∀ i : Fin len, ∃ W₀ : ℝ, ∀ o, Γ.comps[i].kind = .theta o →
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        (∀ u v : Zd d L, ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v‖ ≤
          (W : ℝ) ^ τ' * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            bB d L W u v) ∧
        (∀ v : Fin d → ℤ, ‖chainZ (Sinf P.ψ W) (KI z.re) W o v‖ ≤
          (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
            ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - σ')))) ∧
        (∀ u v : Zd d L, ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v -
              chainZ (Sinf P.ψ W) (KI z.re) W o (zlift (v - u))‖ ≤
            z.im * (W : ℝ) ^ (τ' / 2) *
              (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) := by
    intro i
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases (hK _ hmem).2.2 with ⟨w, hw⟩ | ⟨o, ho, hok⟩
    · exact ⟨0, fun o' ho' => by rw [hw] at ho'; cases ho'⟩
    · have hlab : ∀ l ∈ o, KerSymm KL l ∧ KerBound KL l := by
        intro l hl
        simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at hok
        obtain ⟨⟨h4, hN'⟩, h2⟩ := hok l hl
        exact hKL l h4 hN' (Nat.even_iff.2 h2)
      obtain ⟨Wa, ha⟩ := chain d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε KL o hlab τ' hτ'
      obtain ⟨Wb, hb⟩ := VR1Graph_chainZ_bound hd P N KI hKI o hok σ' hσ'0
      obtain ⟨Wc, hcc⟩ := hcmp _ hmem o ho (τ' / 2) (by positivity)
      refine ⟨max Wa (max Wb Wc), fun o' ho' W L _ hadm hW z hz => ?_⟩
      rw [ho] at ho'; cases ho'
      exact ⟨ha W L hadm ((le_max_left _ _).trans hW) z hz,
        hb W ((le_max_left _ _).trans ((le_max_right _ _).trans hW)) z.re hz.1,
        hcc W L hadm ((le_max_right _ _).trans ((le_max_right _ _).trans hW)) z hz⟩
  choose Wi hWspec using hidx
  set c8 : ℝ := 8 * ((n : ℝ) + 2) with hc8
  refine ⟨|W₁| + ∑ i, |Wi i| + c8 + (c8 ^ (2 : ℝ)) ^ (2 / ε) + (4 : ℝ) ^ (2 / τ') + 2,
    fun W L _ hadm hW z hz x => ?_⟩
  have hs0 : 0 ≤ ∑ i, |Wi i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hc80 : 0 < c8 := by positivity
  have hp1 : 0 ≤ (c8 ^ (2 : ℝ)) ^ (2 / ε) := by positivity
  have hp2 : 0 ≤ (4 : ℝ) ^ (2 / τ') := by positivity
  have hW1 : W₁ ≤ W := by
    have := le_abs_self W₁; linarith [abs_nonneg W₁]
  have hWi : ∀ i, Wi i ≤ W := by
    intro i
    have := Finset.single_le_sum (f := fun j => |Wi j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := le_abs_self (Wi i)
    linarith [abs_nonneg W₁]
  have hW2 : (2 : ℝ) ≤ W := by linarith [abs_nonneg W₁]
  have hW2n : 2 ≤ W := by exact_mod_cast hW2
  have hW0 : (0 : ℝ) < W := by linarith
  have hWn : 1 ≤ W := by omega
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hLc8 : c8 ≤ L := by linarith [abs_nonneg W₁]
  have hL8 : 8 * (n + 2) ≤ L := by
    have : (8 * (n + 2) : ℝ) ≤ L := by rw [hc8] at hLc8; exact_mod_cast hLc8
    exact_mod_cast this
  have hLε : c8 ^ (2 : ℝ) ≤ (L : ℝ) ^ (ε / 2) := by
    have h1 : (c8 ^ (2 : ℝ)) ^ (2 / ε) ≤ L := by linarith [abs_nonneg W₁]
    calc c8 ^ (2 : ℝ) = ((c8 ^ (2 : ℝ)) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ (L : ℝ) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hτ'2 : (2 : ℝ) ≤ (W : ℝ) ^ (τ' / 2) := by
    have h1 : (4 : ℝ) ^ (2 / τ') ≤ W := by linarith [abs_nonneg W₁]
    calc (2 : ℝ) = ((4 : ℝ) ^ (2 / τ')) ^ (τ' / 2) / 2 := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; norm_num
      _ ≤ ((4 : ℝ) ^ (2 / τ')) ^ (τ' / 2) := by
          have : 0 ≤ ((4 : ℝ) ^ (2 / τ')) ^ (τ' / 2) := by positivity
          linarith
      _ ≤ (W : ℝ) ^ (τ' / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hcut := VR1Graph_cut_small hε hz hL8 hLε hσ'0.le hσ'b hσ'c
  have him : 0 < z.im := im_pos_of_specDom hWn hz
  set R : ℕ := L / (4 * (n + 2)) with hR
  rw [VR1Graph_val_eq_aux Γ hWT]
  refine hT W L hadm hW1 z hz _ _ (fun i ho u v => ?_) (fun i ho u v => ?_) (fun i ho u v => ?_) 0 x
  · obtain ⟨o, ho⟩ := ho
    rw [RenormDiff_lab_theta _ o ho]
    exact (hWspec i o ho W L hadm (hWi i) z hz).1 u v
  · obtain ⟨o, ho⟩ := ho
    simp only [RenormDiff_lab_theta _ o ho]
    refine (VR1Graph_norm_cut_le _ _ _).trans ?_
    refine ((hWspec i o ho W L hadm (hWi i) z hz).2.1 _).trans ?_
    rw [VR1Graph_brk_zlift]
    have hb := RenormDiff_brk_pos (d := d) (L := L) hWn u v
    have hp := VR1Graph_brk_pow hc₀ hc₁ hadm hW2n hσ'0.le hσ'a u v
    have hbB : bB d L W u v = (W : ℝ) ^ (-2 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 2)) := by
      unfold bB brk; congr 2; ring
    have he : brk d L W u v ^ (-((d : ℝ) - 2 - σ')) =
        brk d L W u v ^ (-((d : ℝ) - 2)) * brk d L W u v ^ σ' := by
      rw [← Real.rpow_add hb]; ring_nf
    rw [hbB, he]
    have : 0 ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        ((W : ℝ) ^ (-2 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 2))) := by positivity
    calc (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * (brk d L W u v ^ (-((d : ℝ) - 2)) * brk d L W u v ^ σ'))
        = ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 2)))) * brk d L W u v ^ σ' := by
          ring
      _ ≤ ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 2)))) * (W : ℝ) ^ τ' :=
          mul_le_mul_of_nonneg_left hp this
      _ = _ := by ring
  · obtain ⟨o, ho⟩ := ho
    simp only [RenormDiff_lab_theta _ o ho]
    obtain ⟨-, hbZ, hcmpi⟩ := hWspec i o ho W L hadm (hWi i) z hz
    set μ : ℝ := (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) with hμ
    set F := chainZ (Sinf P.ψ W) (KI z.re) W o with hF
    have hb := RenormDiff_brk_pos (d := d) (L := L) hWn u v
    set Bt : ℝ := (W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)) with hBt
    have hBt0 : 0 ≤ Bt := by positivity
    -- the cut part
    have hlong : ‖F (zlift (v - u)) - VR1Graph_cut R F (zlift (v - u))‖ ≤ z.im * μ * Bt := by
      unfold VR1Graph_cut
      split_ifs with hs
      · rw [sub_self, norm_zero]; positivity
      · rw [sub_zero]
        push Not at hs
        refine (hbZ _).trans ?_
        rw [VR1Graph_brk_zlift]
        have hRlt : ((R : ℕ) : ℝ) < brk d L W u v := by
          rw [← VR1Graph_brk_zlift (W := W)]
          have : (R : ℝ) < zdInf (zlift (v - u)) := by exact_mod_cast hs
          linarith
        have hR0 : (0 : ℝ) < (R : ℕ) := by
          have := VR1Graph_R_ge n L hL8; rw [← hR] at this
          have : 0 < (L : ℝ) / (8 * ((n : ℝ) + 2)) := by
            have : (0 : ℝ) < L := by linarith
            positivity
          linarith
        have h1 : brk d L W u v ^ (σ' - 2) ≤ ((R : ℕ) : ℝ) ^ (σ' - 2) :=
          Real.rpow_le_rpow_of_nonpos hR0 hRlt.le (by linarith)
        have he : (W : ℝ) ^ (-2 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 2 - σ')) =
            ((W : ℝ) ^ (2 : ℝ) * brk d L W u v ^ (σ' - 2)) * Bt := by
          rw [hBt, mul_mul_mul_comm, ← Real.rpow_add hW0, ← Real.rpow_add hb]; ring_nf
        rw [he]
        have h2 : (W : ℝ) ^ (2 : ℝ) * brk d L W u v ^ (σ' - 2) ≤ z.im :=
          (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hcut
        calc μ * (((W : ℝ) ^ (2 : ℝ) * brk d L W u v ^ (σ' - 2)) * Bt)
            ≤ μ * (z.im * Bt) := by gcongr
          _ = z.im * μ * Bt := by ring
    have hsplit : (detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v -
        VR1Graph_cut R F (zlift (v - u)) =
        ((detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v - F (zlift (v - u))) +
          (F (zlift (v - u)) - VR1Graph_cut R F (zlift (v - u))) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h3 : z.im * (W : ℝ) ^ (τ' / 2) * μ * Bt + z.im * μ * Bt ≤
        z.im * (W : ℝ) ^ τ' * μ * Bt := by
      have hμ0 : 0 ≤ μ := by positivity
      have h4 : (W : ℝ) ^ (τ' / 2) + 1 ≤ (W : ℝ) ^ τ' := by
        have : (W : ℝ) ^ τ' = (W : ℝ) ^ (τ' / 2) * (W : ℝ) ^ (τ' / 2) := by
          rw [← Real.rpow_add hW0]; ring_nf
        rw [this]; nlinarith
      have : z.im * (W : ℝ) ^ (τ' / 2) * μ * Bt + z.im * μ * Bt =
          z.im * μ * Bt * ((W : ℝ) ^ (τ' / 2) + 1) := by ring
      rw [this]
      calc z.im * μ * Bt * ((W : ℝ) ^ (τ' / 2) + 1) ≤ z.im * μ * Bt * (W : ℝ) ^ τ' :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring
    exact (add_le_add (hcmpi u v) hlong).trans h3

end StepT

/-! ## Step two: the waved edges are cut on the torus -/

section StepC

/-- `|Π pᵢ - Π qᵢ| ≤ m M^{m-1} δ ≤ m M^m δ` for `|pᵢ|, |qᵢ| ≤ M`, `M ≥ 1`, `|pᵢ - qᵢ| ≤ δ`. -/
private theorem VR1Graph_prod_sub_le {m : ℕ} (p q : Fin m → ℂ) (M δ : ℝ) (hM : 1 ≤ M)
    (hp : ∀ i, ‖p i‖ ≤ M) (hq : ∀ i, ‖q i‖ ≤ M) (hpq : ∀ i, ‖p i - q i‖ ≤ δ) :
    ‖∏ i, p i - ∏ i, q i‖ ≤ m * M ^ m * δ := by
  have hδ : ∀ i, 0 ≤ ‖p i - q i‖ := fun i => norm_nonneg _
  rw [RenormDiff_telescope]
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j : Fin m, ‖∏ i, (if i < j then p i else if i = j then p i - q i else q i)‖ ≤
      M ^ m * δ := by
    intro j
    rw [norm_prod]
    have hpt : ∀ i, ‖(if i < j then p i else if i = j then p i - q i else q i)‖ ≤
        (if i = j then δ else M) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp [hpq i]
      · by_cases hlt : i < j
        · simp [hij, hlt, hp i]
        · simp [hij, hlt, hq i]
    have hδ0 : 0 ≤ δ := (hδ j).trans (hpq j)
    calc ∏ i, ‖(if i < j then p i else if i = j then p i - q i else q i)‖
        ≤ ∏ i : Fin m, (if i = j then δ else M) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hpt i)
      _ = δ * ∏ i ∈ Finset.univ.erase j, (if i = j then δ else M) := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
          simp only [ite_true]
      _ = δ * M ^ (Finset.univ.erase j).card := by
          congr 1
          rw [← Finset.prod_const]
          refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.ne_of_mem_erase hi]
      _ ≤ δ * M ^ m := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM ?_) hδ0
          exact (Finset.card_le_card (Finset.erase_subset _ _)).trans (by simp)
      _ = M ^ m * δ := by ring
  calc ∑ j : Fin m, ‖∏ i, (if i < j then p i else if i = j then p i - q i else q i)‖
      ≤ ∑ _j : Fin m, M ^ m * δ := Finset.sum_le_sum fun j _ => hj j
    _ = m * M ^ m * δ := by simp; ring

end StepC

/-! ## The waved edges -/

section Waved

/-- The waved kernels on the torus at `(0, x)`: `s`, `S^+(m(z))`, `S^-(m(z))`. -/
private def VR1Graph_wT (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) : Wave → Zd d L → ℂ
  | .s => fun x => cmat (Smat P.ψ W L) 0 x
  | .plus => fun x => Splus (msc z) (Smat P.ψ W L) 0 x
  | .minus => fun x => Sminus (msc z) (Smat P.ψ W L) 0 x

/-- The waved kernels on `ℤ^d`: `S_∞`, `S^±_∞(m(E))` ([I, (7.3)–(7.4)]). -/
private def VR1Graph_wZ (P : Profile d) (W : ℕ) (E : ℝ) : Wave → (Fin d → ℤ) → ℂ
  | .s => fun v => (Sinf P.ψ W v : ℂ)
  | .plus => fun v => SplusInf (mE E) (Sinf P.ψ W) v
  | .minus => fun v => SminusInf (mE E) (Sinf P.ψ W) v

/-- On `adm(c₀, c₁)` with `W ≥ 1`: `W^{-2/c₁} ≤ η` for `z ∈ 𝐃(κ, ε)`. -/
private theorem VR1Graph_eta_ge {c₀ c₁ κ ε : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hε : 0 < ε)
    {W L : ℕ} [NeZero L] (hadm : (W, L) ∈ adm c₀ c₁) (hW : 1 ≤ W) {z : ℂ}
    (hz : z ∈ specDom κ ε W L) : (W : ℝ) ^ (-(2 / c₁)) ≤ z.im := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hL1 : (1 : ℝ) ≤ L := hW1.trans hWL
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 : (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h2 : (L : ℝ) ^ (2 : ℝ) ≤ (W : ℝ) ^ (2 / c₁) := by
    calc (L : ℝ) ^ (2 : ℝ) = ((L : ℝ) ^ c₁) ^ (2 / c₁) := by
          rw [← Real.rpow_mul hL0.le]; congr 1; field_simp
      _ ≤ (W : ℝ) ^ (2 / c₁) := Real.rpow_le_rpow (by positivity) hLW (by positivity)
  have h3 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  calc (W : ℝ) ^ (-(2 / c₁)) = 1 / (W : ℝ) ^ (2 / c₁) := by
        rw [Real.rpow_neg (by linarith), one_div]
    _ ≤ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) := by
        have hp : 0 < (L : ℝ) ^ (2 - ε) := by positivity
        rw [div_le_div_iff₀ (by positivity) hp, one_mul]
        calc (L : ℝ) ^ (2 - ε) = 1 * (L : ℝ) ^ (2 - ε) := (one_mul _).symm
          _ ≤ (W : ℝ) ^ 2 * (W : ℝ) ^ (2 / c₁) :=
            mul_le_mul h3 (h1.trans h2) hp.le (by positivity)
    _ ≤ z.im := hz.2.1

/-- `f_{W,L}([v]_L) = Z_{W,L}^{-1} φ_W(v)` for `2|v|_∞ < L`. -/
private theorem VR1Graph_fWL_zcast (P : Profile d) {W L : ℕ} [NeZero L] (hW : 1 ≤ W)
    (v : Fin d → ℤ) (hv : 2 * zdInf v < L) :
    fWL P.ψ W L (zcast L v) = (ZWL P.ψ W L)⁻¹ * phiW P.ψ W v := by
  have hz : zrep (zcast L v) = intVec v := by
    have := VR1Graph_zlift_zcast v hv
    unfold zrep intVec
    congr 1
    funext i
    have hi := congrFun this i
    simp only [zlift] at hi
    rw [hi]
  unfold fWL fRaw
  rw [hz]
  congr 1
  have := phiW_eq_profInt P.ψ P.symm W hW v
  rw [← this, Complex.ofReal_re]

/-- `InfKernel` is monotone in the constants. -/
private theorem VR1Graph_infKernel_mono {ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ} {C C' : ℕ → ℝ}
    (hC : ∀ k, C k ≤ C' k) {W : ℕ} {s : (Fin d → ℤ) → ℝ} (h : InfKernel ψ C W s) :
    InfKernel ψ C' W s :=
  ⟨h.symm, h.sum_one, fun k x => (h.decay k x).trans (by gcongr; exact hC k),
    fun D' p hp => (h.close D' p hp).trans (by gcongr; exact hC D')⟩

/-- `SymbolClose` is monotone in the constants. -/
private theorem VR1Graph_symbolClose_mono {ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ} {C C' : ℕ → ℝ}
    (hC : ∀ k, C k ≤ C' k) {W L : ℕ} [NeZero L] {S : Matrix (Zd d L) (Zd d L) ℝ}
    (h : SymbolClose ψ C W S) : SymbolClose ψ C' W S :=
  fun D' k => (h D' k).trans (by gcongr; exact hC D')

/-- The waved bound `W^{-d} (W/⟨v⟩)^{2(d-2)}` on `ℤ^d`. -/
private def VR1Graph_wv (W : ℕ) (v : Fin d → ℤ) : ℝ :=
  (W : ℝ) ^ (-(d : ℝ)) * (VR1Graph_u W ((d : ℝ) - 2) v * VR1Graph_u W ((d : ℝ) - 2) v)

private theorem VR1Graph_wv_nonneg (W : ℕ) (v : Fin d → ℤ) : 0 ≤ VR1Graph_wv W v := by
  unfold VR1Graph_wv; have := VR1Graph_u_nonneg (d := d) W ((d : ℝ) - 2) v; positivity

/-- `VR1Graph_wv W v = W^{d-4} ⟨v⟩^{-(2d-4)}`. -/
private theorem VR1Graph_wv_eq {W : ℕ} (hW : 1 ≤ W) (v : Fin d → ℤ) :
    VR1Graph_wv W v = (W : ℝ) ^ ((d : ℝ) - 4) * ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : (0 : ℝ) < (zdInf v : ℝ) + W := by positivity
  unfold VR1Graph_wv VR1Graph_u
  rw [show (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) ^ ((d : ℝ) - 2) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2)) *
      ((W : ℝ) ^ ((d : ℝ) - 2) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2)))) =
      ((W : ℝ) ^ (-(d : ℝ)) * (W : ℝ) ^ ((d : ℝ) - 2) * (W : ℝ) ^ ((d : ℝ) - 2)) *
        (((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2)) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2))) by ring,
    ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add ht]
  congr 2 <;> ring

/-- A power `⟨v⟩^{-D}` with `D ≥ 2d - 4` is at most `W^{d-D}` times the waved bound. -/
private theorem VR1Graph_pow_le_wv {W : ℕ} (hW : 1 ≤ W) (v : Fin d → ℤ) {D : ℝ}
    (hD : 2 * (d : ℝ) - 4 ≤ D) :
    ((zdInf v : ℝ) + W) ^ (-D) ≤ (W : ℝ) ^ ((d : ℝ) - D) * VR1Graph_wv W v := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWt : (W : ℝ) ≤ (zdInf v : ℝ) + W := by linarith [(Nat.cast_nonneg (zdInf v) : (0 : ℝ) ≤ _)]
  have ht : (0 : ℝ) < (zdInf v : ℝ) + W := by linarith
  rw [VR1Graph_wv_eq hW]
  have h1 : ((zdInf v : ℝ) + W) ^ (-D) =
      ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) * ((zdInf v : ℝ) + W) ^ (-(D - (2 * d - 4))) := by
    rw [← Real.rpow_add ht]; ring_nf
  have h2 : ((zdInf v : ℝ) + W) ^ (-(D - (2 * d - 4))) ≤ (W : ℝ) ^ (-(D - (2 * d - 4))) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWt (by linarith)
  have h3 : (W : ℝ) ^ ((d : ℝ) - D) * (W : ℝ) ^ ((d : ℝ) - 4) = (W : ℝ) ^ (-(D - (2 * d - 4))) := by
    rw [← Real.rpow_add hW0]; ring_nf
  rw [h1]
  calc ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) * ((zdInf v : ℝ) + W) ^ (-(D - (2 * d - 4)))
      ≤ ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) * (W : ℝ) ^ (-(D - (2 * d - 4))) := by gcongr
    _ = _ := by rw [← h3]; ring

/-- Near the origin the indicator costs a power of `W`: for `|v|_∞ ≤ W^{1+τ₃}`,
`W^{-d} ≤ 4^{d} W^{2τ₃(d-2)}` times the waved bound. -/
private theorem VR1Graph_near_le {W : ℕ} (hW : 1 ≤ W) (v : Fin d → ℤ) {τ₃ : ℝ} (hτ₃ : 0 ≤ τ₃)
    (hv : (zdInf v : ℝ) ≤ (W : ℝ) ^ (1 + τ₃)) (hd : 2 ≤ d) :
    (W : ℝ) ^ (-(d : ℝ)) ≤ 4 ^ d * (W : ℝ) ^ (2 * τ₃ * ((d : ℝ) - 2)) * VR1Graph_wv W v := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hWτ : (W : ℝ) ≤ (W : ℝ) ^ (1 + τ₃) :=
    le_of_eq_of_le (Real.rpow_one _).symm (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
  set t : ℝ := (zdInf v : ℝ) + W with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ≤ 2 * (W : ℝ) ^ (1 + τ₃) := by linarith
  -- `u = (W/t)^{d-2} ≥ (W^{-τ₃}/2)^{d-2}`
  have hu : VR1Graph_u W ((d : ℝ) - 2) v = ((W : ℝ) / t) ^ ((d : ℝ) - 2) := by
    unfold VR1Graph_u; rw [Real.div_rpow hW0.le ht0.le, Real.rpow_neg ht0.le]; ring
  have hWt : (W : ℝ) ^ (-τ₃) / 2 ≤ (W : ℝ) / t := by
    rw [div_le_div_iff₀ (by norm_num) ht0]
    calc (W : ℝ) ^ (-τ₃) * t ≤ (W : ℝ) ^ (-τ₃) * (2 * (W : ℝ) ^ (1 + τ₃)) := by gcongr
      _ = (W : ℝ) * 2 := by
          rw [mul_left_comm, ← Real.rpow_add hW0, show -τ₃ + (1 + τ₃) = (1 : ℝ) by ring,
            Real.rpow_one]; ring
  have hlow : ((W : ℝ) ^ (-τ₃) / 2) ^ ((d : ℝ) - 2) ≤ VR1Graph_u W ((d : ℝ) - 2) v := by
    rw [hu]; exact Real.rpow_le_rpow (by positivity) hWt (by linarith)
  have hl : ((W : ℝ) ^ (-τ₃) / 2) ^ ((d : ℝ) - 2) =
      (W : ℝ) ^ (-(τ₃ * ((d : ℝ) - 2))) * (2 : ℝ) ^ (-((d : ℝ) - 2)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hW0.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; ring_nf
  have h4 : (2 : ℝ) ^ (2 * ((d : ℝ) - 2)) ≤ 4 ^ d := by
    rw [show (4 : ℝ) ^ d = (2 : ℝ) ^ (2 * (d : ℝ)) by
      rw [Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlow2 : (W : ℝ) ^ (-(2 * τ₃ * ((d : ℝ) - 2))) * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))) ≤
      VR1Graph_u W ((d : ℝ) - 2) v * VR1Graph_u W ((d : ℝ) - 2) v := by
    have h0 : 0 ≤ ((W : ℝ) ^ (-τ₃) / 2) ^ ((d : ℝ) - 2) := by positivity
    calc (W : ℝ) ^ (-(2 * τ₃ * ((d : ℝ) - 2))) * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2)))
        = ((W : ℝ) ^ (-τ₃) / 2) ^ ((d : ℝ) - 2) * ((W : ℝ) ^ (-τ₃) / 2) ^ ((d : ℝ) - 2) := by
          rw [hl, mul_mul_mul_comm, ← Real.rpow_add hW0, ← Real.rpow_add (by norm_num)]
          ring_nf
      _ ≤ _ := mul_le_mul hlow hlow h0 (h0.trans hlow)
  unfold VR1Graph_wv
  have hA : 0 ≤ (W : ℝ) ^ (-(d : ℝ)) := by positivity
  have hB : (1 : ℝ) ≤ 4 ^ d * (W : ℝ) ^ (2 * τ₃ * ((d : ℝ) - 2)) *
      ((W : ℝ) ^ (-(2 * τ₃ * ((d : ℝ) - 2))) * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2)))) := by
    have e1 : (W : ℝ) ^ (2 * τ₃ * ((d : ℝ) - 2)) * (W : ℝ) ^ (-(2 * τ₃ * ((d : ℝ) - 2))) = 1 := by
      rw [← Real.rpow_add hW0]; simp
    have e2 : (2 : ℝ) ^ (2 * ((d : ℝ) - 2)) * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have e3 : 0 < (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))) := by positivity
    calc (1 : ℝ) = (2 : ℝ) ^ (2 * ((d : ℝ) - 2)) * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))) := e2.symm
      _ ≤ 4 ^ d * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))) := mul_le_mul_of_nonneg_right h4 e3.le
      _ = 4 ^ d * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))) * ((W : ℝ) ^ (2 * τ₃ * ((d : ℝ) - 2)) *
          (W : ℝ) ^ (-(2 * τ₃ * ((d : ℝ) - 2)))) := by rw [e1, mul_one]
      _ = _ := by ring
  calc (W : ℝ) ^ (-(d : ℝ)) ≤ (W : ℝ) ^ (-(d : ℝ)) * (4 ^ d * (W : ℝ) ^ (2 * τ₃ * ((d : ℝ) - 2)) *
        ((W : ℝ) ^ (-(2 * τ₃ * ((d : ℝ) - 2))) * (2 : ℝ) ^ (-(2 * ((d : ℝ) - 2))))) :=
        le_mul_of_one_le_right hA hB
    _ ≤ (W : ℝ) ^ (-(d : ℝ)) * (4 ^ d * (W : ℝ) ^ (2 * τ₃ * ((d : ℝ) - 2)) *
        (VR1Graph_u W ((d : ℝ) - 2) v * VR1Graph_u W ((d : ℝ) - 2) v)) := by gcongr
    _ = _ := by ring

/-- `W^{-d} (W/⟨v⟩)^{2(d-2)}` with a natural power. -/
private theorem VR1Graph_wv_eq' {W : ℕ} (hW : 1 ≤ W) (hd : 2 ≤ d) (v : Fin d → ℤ) :
    VR1Graph_wv W v = (W : ℝ) ^ (-(d : ℝ)) * ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ (2 * (d - 2)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : (0 : ℝ) < (zdInf v : ℝ) + W := by positivity
  have hc : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by rw [Nat.cast_sub hd]; norm_num
  have hu : VR1Graph_u W ((d : ℝ) - 2) v = ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ (d - 2) := by
    unfold VR1Graph_u
    rw [← hc, Real.rpow_natCast, Real.rpow_neg ht.le, Real.rpow_natCast, div_pow, div_eq_mul_inv]
  unfold VR1Graph_wv
  rw [hu, ← pow_add, show d - 2 + (d - 2) = 2 * (d - 2) by ring]

/-- From `|f| (1 + |v|/W)^{2(d-2)+m} ≤ C W^{-d}`: `|f| ≤ C (W/⟨v⟩)^m` times the waved bound. -/
private theorem VR1Graph_decay_wv {W : ℕ} (hW : 1 ≤ W) (hd : 2 ≤ d) (v : Fin d → ℤ) {f C : ℝ}
    (m : ℕ) (h : |f| * (1 + (zdInf v : ℝ) / W) ^ (2 * (d - 2) + m) ≤ C / (W : ℝ) ^ d) :
    |f| ≤ C * VR1Graph_wv W v * ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ m := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have ht : (0 : ℝ) < (zdInf v : ℝ) + W := by positivity
  have h1 : (1 + (zdInf v : ℝ) / W) = ((zdInf v : ℝ) + W) / W := by field_simp; ring
  rw [h1] at h
  have hp : 0 < (((zdInf v : ℝ) + W) / W) ^ (2 * (d - 2) + m) := by positivity
  rw [VR1Graph_wv_eq' hW hd, Real.rpow_neg hW0.le, Real.rpow_natCast]
  have e : ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ (2 * (d - 2) + m) *
      (((zdInf v : ℝ) + W) / W) ^ (2 * (d - 2) + m) = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm (W : ℝ), div_self (by positivity), one_pow]
  calc |f| = |f| * (((zdInf v : ℝ) + W) / W) ^ (2 * (d - 2) + m) *
        ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ (2 * (d - 2) + m) := by rw [mul_assoc, mul_comm (_ ^ _), e,
          mul_one]
    _ ≤ C / (W : ℝ) ^ d * ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ (2 * (d - 2) + m) := by gcongr
    _ = _ := by rw [pow_add, div_eq_mul_inv]; ring

/-- `(W/⟨v⟩)^m ≤ W^{-τ₂ m}` beyond `|v|_∞ > W^{1+τ₂}`. -/
private theorem VR1Graph_ratio_pow {W : ℕ} (hW : 1 ≤ W) {τ₂ : ℝ} (hτ₂ : 0 < τ₂) {v : Fin d → ℤ}
    (hv : (W : ℝ) ^ (1 + τ₂) < zdInf v) (m : ℕ) :
    ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ m ≤ (W : ℝ) ^ (-(τ₂ * m)) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hWt : (W : ℝ) / ((zdInf v : ℝ) + W) ≤ (W : ℝ) ^ (-τ₂) := by
    rw [div_le_iff₀ (by positivity), Real.rpow_neg hW0.le, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    have : (W : ℝ) * (W : ℝ) ^ τ₂ = (W : ℝ) ^ (1 + τ₂) := by
      rw [Real.rpow_add hW0, Real.rpow_one]
    rw [this]; linarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
  calc ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ m ≤ ((W : ℝ) ^ (-τ₂)) ^ m :=
        pow_le_pow_left₀ (by positivity) hWt m
    _ = (W : ℝ) ^ (-(τ₂ * m)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; ring_nf

/-- `2/c₁ ≤ τ₂ m` for `m ≥ 2/(c₁ τ₂)`. -/
private theorem VR1Graph_ceil_mul {c₁ τ₂ : ℝ} (hc₁ : 0 < c₁) (hτ₂ : 0 < τ₂) {m : ℝ}
    (hm : 2 / (c₁ * τ₂) ≤ m) : 2 / c₁ ≤ τ₂ * m := by
  have : 2 / c₁ = τ₂ * (2 / (c₁ * τ₂)) := by field_simp
  rw [this]; exact mul_le_mul_of_nonneg_left hm hτ₂.le

/-- The decay constants of an `InfKernel` are nonnegative. -/
private theorem VR1Graph_decay_const_nonneg {ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ}
    {C : ℕ → ℝ} {W : ℕ} (hW : 1 ≤ W) {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) (k : ℕ) :
    0 ≤ C k := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have := hs.decay k 0
  have h1 : 0 ≤ |s 0| * (1 + (zdInf (0 : Fin d → ℤ) : ℝ) / W) ^ k := by positivity
  have h2 := h1.trans this
  rwa [le_div_iff₀ (by positivity), zero_mul] at h2

-- One declaration with three bounds for three waved kernels and many real-power estimates.
set_option maxHeartbeats 800000 in
/-- **The waved kernels on `ℤ^d`**: bounds by `W^{τ₂}` times the waved bound, the comparison with
the torus kernels at `[v]_L`, `η` times the waved bound, and the decay beyond `W^{1+τ₂}`, `η`
times the waved bound; uniformly in `|E| < 2 − κ`. -/
private theorem VR1Graph_wavedZ (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε) (τ₂ : ℝ) (hτ₂ : 0 < τ₂) :
    ∃ K W₀ : ℝ, 0 ≤ K ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L,
        (∀ w v, ‖VR1Graph_wZ P W z.re w v‖ ≤ K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v) ∧
        (∀ w v, 2 * zdInf v < L → ‖VR1Graph_wT P W L z w (zcast L v) - VR1Graph_wZ P W z.re w v‖ ≤
          z.im * K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v) ∧
        (∀ w v, (W : ℝ) ^ (1 + τ₂) < zdInf v → ‖VR1Graph_wZ P W z.re w v‖ ≤
          z.im * K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v) := by
  have hd2 : 2 ≤ d := by omega
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨Ci, Wi, hi⟩ := Sinf_infKernel d P.ψ P.cψ (ValZ_shape P)
  obtain ⟨Cs, hCs⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨Wsym, hsym⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  set Cm : ℕ → ℝ := fun k => max (Ci k) (Cs k) with hCm
  obtain ⟨Kz, Wz, hKz0, hzw⟩ := ValZ_wave_bound (d := d) (by omega) P.ψ c' hc' Ci hκ hτ₂
  set Dz : ℕ := ⌈2 / c₁⌉₊ + 1 with hDz
  have hDz1 : 2 / c₁ ≤ (Dz : ℝ) := by
    have := Nat.le_ceil (2 / c₁); rw [hDz]; push_cast; linarith
  set Dd : ℝ := 3 * (d : ℝ) + 2 / c₁ with hDd
  have hDd0 : 0 < Dd := by positivity
  set τ₃ : ℝ := τ₂ / (2 * d) with hτ₃
  have hτ₃0 : 0 < τ₃ := by positivity
  have hτ3le : 2 * τ₃ * ((d : ℝ) - 2) ≤ τ₂ := by
    have hd0 : (0 : ℝ) < d := by linarith
    have e : 2 * τ₃ * ((d : ℝ) - 2) = τ₂ - 2 * τ₂ / d := by rw [hτ₃]; field_simp
    have : 0 ≤ 2 * τ₂ / d := by positivity
    linarith
  obtain ⟨Kp, Wp, hp⟩ := Splus_sub_SplusInf d c₀ c₁ hc₀ hc₁ P.ψ c' hc' Cm κ ε τ₃ Dd hκ hε hτ₃0 hDd0
  obtain ⟨Kq, Wq, hq⟩ := SplusInf_decay d P.ψ c' hc' Ci κ τ₂ Dd hκ hτ₂ hDd0
  obtain ⟨Wf, hf⟩ := P.f_symm c₀ c₁ hc₀ hc₁
  obtain ⟨Cz, hCz⟩ := ZWL_close_adm d P.ψ P.at_zero c₀ c₁ hc₀ Dz
  obtain ⟨Ct, hCt⟩ := tsum_phiW d P.ψ P.cψ (ValZ_shape P) Dz
  obtain ⟨Cφ, hCφ⟩ := phiW_decay d P.ψ (2 * (d - 2) + 0)
  set mm : ℕ := ⌈2 / (c₁ * τ₂)⌉₊ + 1 with hmm
  have hmm1 : 2 / (c₁ * τ₂) ≤ (mm : ℝ) := by
    have := Nat.le_ceil (2 / (c₁ * τ₂)); rw [hmm]; push_cast; linarith
  set Kd : ℝ := |Kp| * (4 ^ d + 1) + 4 * |Cφ| * (|Cz| + |Ct|) with hKd
  refine ⟨|Kz| + Kd + |Kq| + |Ci (2 * (d - 2) + mm)|, max (max (max Wi Wsym) (max Wz Wp))
    (max (max Wq (Wf : ℝ)) (2 * |Cz| + 2 * |Ct| + 2)), by positivity,
    fun W L _ hadm hW z hz => ?_⟩
  have hW2 : (2 : ℝ) ≤ W := by
    have := le_max_right (max (max Wi Wsym) (max Wz Wp)) (max (max Wq (Wf : ℝ))
      (2 * |Cz| + 2 * |Ct| + 2))
    have := le_max_right (max Wq (Wf : ℝ)) (2 * |Cz| + 2 * |Ct| + 2)
    linarith [abs_nonneg Cz, abs_nonneg Ct]
  have hWn : 1 ≤ W := by
    have : (1 : ℝ) ≤ W := by linarith
    exact_mod_cast this
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWn
  have hW0 : (0 : ℝ) < W := by linarith
  have hWi : Wi ≤ W := le_trans (by simp) hW
  have hWsym : Wsym ≤ W := le_trans (by simp) hW
  have hWz : Wz ≤ W := le_trans (by simp) hW
  have hWp : Wp ≤ W := le_trans (by simp) hW
  have hWq : Wq ≤ W := le_trans (by simp) hW
  have hWf : (Wf : ℝ) ≤ W := le_trans (by simp) hW
  have hWC : 2 * |Cz| + 2 * |Ct| + 2 ≤ (W : ℝ) := le_trans (by simp) hW
  have hs := hi W hWi
  have hsm : InfKernel P.ψ Cm W (Sinf P.ψ W) :=
    VR1Graph_infKernel_mono (fun k => le_max_left _ _) hs
  have hη := VR1Graph_eta_ge hc₀ hc₁ hε hadm hWn hz
  have him : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hE : |z.re| < 2 - κ := hz.1
  have hWτ : (1 : ℝ) ≤ (W : ℝ) ^ τ₂ := Real.one_le_rpow hW1 hτ₂.le
  have hK1 : 0 ≤ |Kz| := abs_nonneg _
  have hKd0 : 0 ≤ Kd := by positivity
  set K := |Kz| + Kd + |Kq| + |Ci (2 * (d - 2) + mm)| with hK
  -- a `W`-power below `W^{-2/c₁}` is below `η`
  have hpowη : ∀ e : ℝ, 2 / c₁ ≤ e → (W : ℝ) ^ (-e) ≤ z.im := fun e he =>
    (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)).trans hη
  have hwv0 : ∀ v, 0 ≤ VR1Graph_wv (d := d) W v := VR1Graph_wv_nonneg W
  -- the far power `⟨v⟩^{-Dd} ≤ η wv`
  have hfar : ∀ v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-Dd) ≤ z.im * VR1Graph_wv W v := by
    intro v
    have hD2 : 2 * (d : ℝ) - 4 ≤ Dd := by
      have : 0 ≤ 2 / c₁ := by positivity
      rw [hDd]; linarith
    refine (VR1Graph_pow_le_wv hWn v hD2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hwv0 v)
    rw [show (d : ℝ) - Dd = -(2 * d + 2 / c₁) by rw [hDd]; ring]
    exact hpowη _ (by linarith)
  refine ⟨fun w v => ?_, fun w v hv => ?_, fun w v hv => ?_⟩
  · -- the bound on `ℤ^d`
    obtain ⟨h1, h2, h3⟩ := hzw W hWz (Sinf P.ψ W) hs z.re hE v
    have hwb : ValZ_wb d W Kz τ₂ v = Kz * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
      unfold ValZ_wb; rw [VR1Graph_wv_eq hWn]
    have hle : Kz * (W : ℝ) ^ τ₂ * VR1Graph_wv W v ≤ K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
      have : Kz ≤ K := by
        rw [hK]; have := le_abs_self Kz; have := abs_nonneg Kq
        have := abs_nonneg (Ci (2 * (d - 2) + mm)); linarith
      gcongr; exact hwv0 v
    cases w
    · exact (hwb ▸ h1).trans hle
    · exact (hwb ▸ h2).trans hle
    · exact (hwb ▸ h3).trans hle
  · -- the comparison
    have hzl : zlift (zcast L v) = v := VR1Graph_zlift_zcast v hv
    have hzd : (zdistInf d L (zcast L v) : ℝ) = zdInf v := by
      rw [← VR1Graph_zdInf_zlift, hzl]
    have hKdK : Kd ≤ K := by
      rw [hK]; have := abs_nonneg Kq
      have := abs_nonneg (Ci (2 * (d - 2) + mm)); linarith
    -- the waved `S^±`
    have hpm : ‖SplusInf (mE z.re) (Sinf P.ψ W) v - Splus (msc z) (Smat P.ψ W L) 0 (zcast L v)‖ ≤
        z.im * K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
      have h := hp W L hadm hWp (Smat P.ψ W L) (hsym W L hadm hWsym)
        (VR1Graph_symbolClose_mono (fun k => le_max_right _ _) (hCs W L hadm)) (Sinf P.ψ W) hsm
        z hz (zcast L v)
      rw [hzl, hzd] at h
      refine h.trans ?_
      have hnear : z.im * (if (zdInf v : ℝ) ≤ (W : ℝ) ^ (1 + τ₃) then ((W : ℝ) ^ d)⁻¹ else 0) ≤
          z.im * (4 ^ d * (W : ℝ) ^ τ₂ * VR1Graph_wv W v) := by
        refine mul_le_mul_of_nonneg_left ?_ him.le
        split_ifs with hh
        · have := VR1Graph_near_le hWn v hτ₃0.le hh hd2
          rw [Real.rpow_neg hW0.le, Real.rpow_natCast] at this
          refine this.trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hW1 hτ3le) (by positivity)) (hwv0 v)
        · have := hwv0 v; positivity
      calc Kp * (z.im * (if (zdInf v : ℝ) ≤ (W : ℝ) ^ (1 + τ₃) then ((W : ℝ) ^ d)⁻¹ else 0) +
            ((zdInf v : ℝ) + W) ^ (-Dd))
          ≤ |Kp| * (z.im * (4 ^ d * (W : ℝ) ^ τ₂ * VR1Graph_wv W v) +
              z.im * VR1Graph_wv W v) := by
            have h0 : 0 ≤ z.im * (if (zdInf v : ℝ) ≤ (W : ℝ) ^ (1 + τ₃) then ((W : ℝ) ^ d)⁻¹
              else 0) + ((zdInf v : ℝ) + W) ^ (-Dd) := by
              have : 0 ≤ (if (zdInf v : ℝ) ≤ (W : ℝ) ^ (1 + τ₃) then ((W : ℝ) ^ d)⁻¹ else 0) := by
                split_ifs <;> positivity
              positivity
            exact (mul_le_mul_of_nonneg_right (le_abs_self Kp) h0).trans
              (mul_le_mul_of_nonneg_left (add_le_add hnear (hfar v)) (abs_nonneg _))
        _ ≤ z.im * (|Kp| * (4 ^ d + 1)) * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
            have h0 : 0 ≤ z.im * |Kp| * VR1Graph_wv W v := by have := hwv0 v; positivity
            have e1 : |Kp| * (z.im * (4 ^ d * (W : ℝ) ^ τ₂ * VR1Graph_wv W v) +
                z.im * VR1Graph_wv W v) =
                z.im * |Kp| * VR1Graph_wv W v * (4 ^ d * (W : ℝ) ^ τ₂ + 1) := by ring
            have e2 : z.im * (|Kp| * (4 ^ d + 1)) * (W : ℝ) ^ τ₂ * VR1Graph_wv W v =
                z.im * |Kp| * VR1Graph_wv W v * ((4 ^ d + 1) * (W : ℝ) ^ τ₂) := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left (by linarith) h0
        _ ≤ z.im * K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
            have : |Kp| * (4 ^ d + 1) ≤ K := by
              refine le_trans ?_ hKdK; rw [hKd]; have := abs_nonneg Cφ
              have := abs_nonneg Cz; have := abs_nonneg Ct; nlinarith
            gcongr; exact hwv0 v
    cases w
    · -- the variance kernel: `f_{W,L}([v]) - S_∞(v) = φ_W(v) (Z_{W,L}^{-1} - (Σ φ_W)^{-1})`
      have hsym' := hf W L hadm (by exact_mod_cast hWf) (zcast L v)
      have hval : VR1Graph_wT P W L z .s (zcast L v) - VR1Graph_wZ P W z.re .s v =
          (((ZWL P.ψ W L)⁻¹ - (∑' y, phiW P.ψ W y)⁻¹) * phiW P.ψ W v : ℝ) := by
        simp only [VR1Graph_wT, VR1Graph_wZ, cmat, Smat, Matrix.map_apply, Matrix.of_apply,
          zero_sub, hsym', VR1Graph_fWL_zcast P hWn v hv, Sinf]
        push_cast; ring
      rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hZ := hCz W L hadm
      have hT := hCt W hWn
      have hWD : (W : ℝ) ≤ (W : ℝ) ^ Dz := by
        calc (W : ℝ) = (W : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (W : ℝ) ^ Dz := pow_le_pow_right₀ hW1 (by rw [hDz]; omega)
      have hcz : |Cz| / (W : ℝ) ^ Dz ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith [abs_nonneg Ct]
      have hct : |Ct| / (W : ℝ) ^ Dz ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith [abs_nonneg Cz]
      have hZ' : |ZWL P.ψ W L - 1| ≤ |Cz| / (W : ℝ) ^ Dz :=
        hZ.trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
      have hT' : |∑' y, phiW P.ψ W y - 1| ≤ |Ct| / (W : ℝ) ^ Dz :=
        hT.trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
      have hZ2 : 1 / 2 ≤ ZWL P.ψ W L := by
        have := (abs_le.1 (hZ'.trans hcz)).1; linarith
      have hT2 : 1 / 2 ≤ ∑' y, phiW P.ψ W y := by
        have := (abs_le.1 (hT'.trans hct)).1; linarith
      have hinv : |(ZWL P.ψ W L)⁻¹ - (∑' y, phiW P.ψ W y)⁻¹| ≤
          4 * ((|Cz| + |Ct|) / (W : ℝ) ^ Dz) := by
        rw [inv_sub_inv (by linarith) (by linarith), abs_div, abs_mul,
          abs_of_pos (by linarith : (0 : ℝ) < ZWL P.ψ W L),
          abs_of_pos (by linarith : (0 : ℝ) < ∑' y, phiW P.ψ W y)]
        rw [div_le_iff₀ (by positivity)]
        have h1 : |∑' y, phiW P.ψ W y - ZWL P.ψ W L| ≤ (|Cz| + |Ct|) / (W : ℝ) ^ Dz := by
          have : ∑' y, phiW P.ψ W y - ZWL P.ψ W L =
              (∑' y, phiW P.ψ W y - 1) - (ZWL P.ψ W L - 1) := by ring
          rw [this, add_div]
          exact (abs_sub _ _).trans (by linarith)
        have h2 : 1 / 4 ≤ ZWL P.ψ W L * ∑' y, phiW P.ψ W y := by
          have := mul_le_mul hZ2 hT2 (by norm_num) (by linarith); linarith
        have h3 : 0 ≤ (|Cz| + |Ct|) / (W : ℝ) ^ Dz := by positivity
        have h4 : (1 : ℝ) ≤ 4 * (ZWL P.ψ W L * ∑' y, phiW P.ψ W y) := by linarith
        calc |∑' y, phiW P.ψ W y - ZWL P.ψ W L| ≤ (|Cz| + |Ct|) / (W : ℝ) ^ Dz := h1
          _ = (|Cz| + |Ct|) / (W : ℝ) ^ Dz * 1 := (mul_one _).symm
          _ ≤ (|Cz| + |Ct|) / (W : ℝ) ^ Dz * (4 * (ZWL P.ψ W L * ∑' y, phiW P.ψ W y)) :=
              mul_le_mul_of_nonneg_left h4 h3
          _ = _ := by ring
      have hφ := VR1Graph_decay_wv hWn hd2 v 0 (by simpa using hCφ W hWn v)
      simp only [pow_zero, mul_one] at hφ
      have hWDz : (W : ℝ) ^ (-(Dz : ℝ)) ≤ z.im := hpowη _ hDz1
      have hWDz' : 1 / (W : ℝ) ^ Dz ≤ z.im := by
        rwa [Real.rpow_neg hW0.le, Real.rpow_natCast, ← one_div] at hWDz
      calc |(ZWL P.ψ W L)⁻¹ - (∑' y, phiW P.ψ W y)⁻¹| * |phiW P.ψ W v|
          ≤ (4 * ((|Cz| + |Ct|) / (W : ℝ) ^ Dz)) * (|Cφ| * VR1Graph_wv W v) := by
            gcongr
            exact hφ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hwv0 v))
        _ = 4 * |Cφ| * (|Cz| + |Ct|) * (1 / (W : ℝ) ^ Dz) * VR1Graph_wv W v := by ring
        _ ≤ 4 * |Cφ| * (|Cz| + |Ct|) * z.im * VR1Graph_wv W v := by
            have h0 := hwv0 v
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDz' (by positivity)) h0
        _ ≤ z.im * K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
            have hK' : 4 * |Cφ| * (|Cz| + |Ct|) ≤ K := by
              refine le_trans ?_ hKdK; rw [hKd]
              have : 0 ≤ |Kp| * (4 ^ d + 1) := by positivity
              linarith
            have := hwv0 v
            calc 4 * |Cφ| * (|Cz| + |Ct|) * z.im * VR1Graph_wv W v
                ≤ K * z.im * VR1Graph_wv W v := by gcongr
              _ ≤ K * z.im * VR1Graph_wv W v * (W : ℝ) ^ τ₂ :=
                  le_mul_of_one_le_right (by positivity) hWτ
              _ = _ := by ring
    · simp only [VR1Graph_wT, VR1Graph_wZ]
      rw [← norm_neg, neg_sub]; exact hpm
    · simp only [VR1Graph_wT, VR1Graph_wZ, Sminus, SminusInf, Matrix.map_apply]
      rw [← map_sub, Complex.norm_conj, ← norm_neg, neg_sub]; exact hpm
  · -- the decay beyond `W^{1+τ₂}`
    have hfarη : ∀ c : ℝ, 0 ≤ c → c ≤ K → c * ((zdInf v : ℝ) + W) ^ (-Dd) ≤
        z.im * K * (W : ℝ) ^ τ₂ * VR1Graph_wv W v := by
      intro c hc0 hcK
      have := hwv0 v
      calc c * ((zdInf v : ℝ) + W) ^ (-Dd) ≤ K * (z.im * VR1Graph_wv W v) :=
            mul_le_mul hcK (hfar v) (by positivity) (by linarith)
        _ ≤ K * (z.im * VR1Graph_wv W v) * (W : ℝ) ^ τ₂ :=
            le_mul_of_one_le_right (by have := hK1; positivity) hWτ
        _ = _ := by ring
    have hKqK : |Kq| ≤ K := by
      rw [hK]; have := abs_nonneg Kz
      have := abs_nonneg (Ci (2 * (d - 2) + mm)); linarith
    have hdec := hq W hWq (Sinf P.ψ W) hs z.re hE.le v
    have hnot : ¬ (zdInf v : ℝ) ≤ (W : ℝ) ^ (1 + τ₂) := not_le.2 hv
    simp only [hnot, if_false, zero_add] at hdec
    cases w
    · simp only [VR1Graph_wZ, Complex.norm_real, Real.norm_eq_abs]
      have hd' := VR1Graph_decay_wv hWn hd2 v mm (hs.decay (2 * (d - 2) + mm) v)
      have hpow : ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ mm ≤ z.im :=
        (VR1Graph_ratio_pow hWn hτ₂ hv mm).trans (hpowη _ (VR1Graph_ceil_mul hc₁ hτ₂ hmm1))
      refine hd'.trans ?_
      have hCiK : Ci (2 * (d - 2) + mm) ≤ K := by
        rw [hK]; have := le_abs_self (Ci (2 * (d - 2) + mm)); have := abs_nonneg Kz
        have := abs_nonneg Kq; linarith
      have := hwv0 v
      calc Ci (2 * (d - 2) + mm) * VR1Graph_wv W v * ((W : ℝ) / ((zdInf v : ℝ) + W)) ^ mm
          ≤ K * VR1Graph_wv W v * z.im := by
            have hc0 : 0 ≤ Ci (2 * (d - 2) + mm) := VR1Graph_decay_const_nonneg hWn hs _
            gcongr
        _ ≤ K * VR1Graph_wv W v * z.im * (W : ℝ) ^ τ₂ :=
            le_mul_of_one_le_right (by have := hK1; positivity) hWτ
        _ = _ := by ring
    · simp only [VR1Graph_wZ]
      exact hdec.1.trans (hfarη _ (abs_nonneg _) hKqK |>.trans'
        (mul_le_mul_of_nonneg_right (le_abs_self Kq) (by positivity)))
    · simp only [VR1Graph_wZ]
      exact hdec.2.trans (hfarη _ (abs_nonneg _) hKqK |>.trans'
        (mul_le_mul_of_nonneg_right (le_abs_self Kq) (by positivity)))

end Waved

/-! ## The coefficient at `m(z)` and at `m(E)` -/

section Coeff

/-- The generators of the coefficients at `m(z)` and at `m(E)`, `E = Re z`, are bounded and differ
by at most a constant times `η`, uniformly in `|E| < 2 − κ`, `0 < η ≤ 1` ([I, (2.2)] and
`|m(z) − m(E)| ≤ η / Im m(E)`). -/
private theorem VR1Graph_cvar {κ : ℝ} (hκ : 0 < κ) : ∃ R : ℝ, 0 ≤ R ∧
    ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → z.im ≤ 1 → ∀ v : CVar,
      ‖CVar.eval (msc z) v‖ ≤ R ∧ ‖CVar.eval (mE z.re) v‖ ≤ R ∧
        ‖CVar.eval (msc z) v - CVar.eval (mE z.re) v‖ ≤ R * z.im := by
  set s : ℝ := Real.sqrt (2 * κ) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  set R : ℝ := 4 + 5 / s + 1 / s + (2 / s) * (4 + 2 * (5 / s) * (1 / s) + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨R, hR0, fun z hz hre him v => ?_⟩
  set a := msc z with ha
  set b := mE z.re with hb
  have hκ2 : κ < 2 := by linarith [abs_nonneg z.re]
  have hE2 : |z.re| ≤ 2 := by linarith
  obtain ⟨ha1, ha2⟩ := msc_bulk κ hκ z hz hre.le
  have hb1 : ‖b‖ = 1 := norm_mE hE2
  have hbi : s / 2 ≤ b.im := InfLimit_mE_im_ge hκ hre
  have hab : ‖a - b‖ ≤ (2 / s) * z.im := by
    refine (InfLimit_msc_sub_mE hz (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : (2 / s) * z.im * b.im ≥ (2 / s) * z.im * (s / 2) := by gcongr
    have e : (2 / s) * z.im * (s / 2) = z.im := by field_simp
    linarith
  have ha0 : a ≠ 0 := msc_ne_zero z
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb1; norm_num at hb1
  have hainv : ‖a⁻¹‖ ≤ 4 := by
    have h1 : a⁻¹ = -(a + z) := by rw [ha, msc_add_eq_neg_inv]; ring
    rw [h1, norm_neg]
    have h2 := Complex.norm_le_abs_re_add_abs_im z
    have h3 : |z.im| ≤ 1 := by rw [abs_of_pos hz]; exact him
    calc ‖a + z‖ ≤ ‖a‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 + (2 + 1) := by linarith
      _ = 4 := by norm_num
  have hbinv : ‖b⁻¹‖ = 1 := by rw [norm_inv, hb1, inv_one]
  have hra : ‖(1 - a ^ 2)⁻¹‖ ≤ 5 / s := by
    rw [norm_inv]
    have hpos : 0 < ‖1 - a ^ 2‖ := lt_of_lt_of_le (by positivity) ha2
    rw [inv_le_comm₀ hpos (by positivity), inv_div]
    exact ha2
  have hb3 : s ≤ ‖1 - b ^ 2‖ := by
    have h1 := ValZ_norm_one_sub_sq hE2
    have h2 : s ^ 2 ≤ ‖1 - b ^ 2‖ ^ 2 := by
      rw [h1, hs, Real.sq_sqrt (by linarith)]
      have : z.re ^ 2 ≤ (2 - κ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre.le 2
      nlinarith
    exact (sq_le_sq₀ hs0.le (norm_nonneg _)).1 h2
  have hrb : ‖(1 - b ^ 2)⁻¹‖ ≤ 1 / s := by
    rw [norm_inv, one_div]
    exact inv_anti₀ hs0 hb3
  have hsq : ‖a ^ 2 - b ^ 2‖ ≤ 2 * ‖a - b‖ := by
    have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [e, norm_mul]
    have : ‖a + b‖ ≤ 2 := (norm_add_le _ _).trans (by linarith)
    nlinarith [norm_nonneg (a - b)]
  have hinvdiff : ∀ p q : ℂ, p ≠ 0 → q ≠ 0 → ‖p⁻¹ - q⁻¹‖ = ‖p⁻¹‖ * ‖q - p‖ * ‖q⁻¹‖ := by
    intro p q hp hq
    rw [inv_sub_inv' hp hq, norm_mul, norm_mul]
  have hη0 : 0 ≤ z.im := hz.le
  have hd0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hA1 : 0 ≤ 5 / s := by positivity
  have hA2 : 0 ≤ 1 / s := by positivity
  have hmain : ‖a - b‖ ≤ R * z.im := by
    refine hab.trans (mul_le_mul_of_nonneg_right ?_ hη0)
    have : 0 ≤ 4 + 2 * (5 / s) * (1 / s) + 1 := by positivity
    have : (2 / s) ≤ (2 / s) * (4 + 2 * (5 / s) * (1 / s) + 1) :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith
  have hminv : ‖a⁻¹ - b⁻¹‖ ≤ R * z.im := by
    rw [hinvdiff a b ha0 hb0, hbinv, mul_one, norm_sub_rev]
    calc ‖a⁻¹‖ * ‖a - b‖ ≤ 4 * ((2 / s) * z.im) := mul_le_mul hainv hab hd0 (by norm_num)
      _ ≤ R * z.im := by
          rw [← mul_assoc, mul_comm 4 (2 / s)]
          refine mul_le_mul_of_nonneg_right ?_ hη0
          have : 0 ≤ (2 / s) * (2 * (5 / s) * (1 / s) + 1) := by positivity
          nlinarith
  have hr : ‖(1 - a ^ 2)⁻¹ - (1 - b ^ 2)⁻¹‖ ≤ R * z.im := by
    have ha' : (1 - a ^ 2) ≠ 0 := by
      intro h; rw [h, norm_zero] at ha2; linarith [show 0 < s / 5 by positivity]
    have hb' : (1 - b ^ 2) ≠ 0 := by
      intro h; rw [h, norm_zero] at hb3; linarith
    rw [hinvdiff _ _ ha' hb', show (1 - b ^ 2) - (1 - a ^ 2) = a ^ 2 - b ^ 2 by ring]
    calc ‖(1 - a ^ 2)⁻¹‖ * ‖a ^ 2 - b ^ 2‖ * ‖(1 - b ^ 2)⁻¹‖
        ≤ (5 / s) * (2 * ((2 / s) * z.im)) * (1 / s) := by
          gcongr
          exact hsq.trans (by linarith)
      _ ≤ R * z.im := by
          have e : (5 / s) * (2 * ((2 / s) * z.im)) * (1 / s) =
              ((2 / s) * (2 * (5 / s) * (1 / s))) * z.im := by ring
          rw [e]
          refine mul_le_mul_of_nonneg_right ?_ hη0
          have : 0 ≤ (2 / s) * (4 + 1) := by positivity
          nlinarith
  have hRa : ∀ t : ℝ, t ≤ 4 + 5 / s + 1 / s → t ≤ R := by
    intro t ht
    have : 0 ≤ (2 / s) * (4 + 2 * (5 / s) * (1 / s) + 1) := by positivity
    linarith
  cases v with
  | m =>
    simp only [CVar.eval]
    exact ⟨hRa _ (by linarith), hRa _ (by linarith), hmain⟩
  | mInv =>
    simp only [CVar.eval]
    exact ⟨hRa _ (by linarith), hRa _ (by linarith), hminv⟩
  | r =>
    simp only [CVar.eval]
    exact ⟨hRa _ (by linarith), hRa _ (by linarith), hr⟩
  | mBar =>
    simp only [CVar.eval, norm_star]
    refine ⟨hRa _ (by linarith), hRa _ (by linarith), ?_⟩
    rw [← star_sub, norm_star]; exact hmain
  | mBarInv =>
    simp only [CVar.eval]
    rw [← star_inv₀, ← star_inv₀, norm_star, norm_star, ← star_sub, norm_star]
    exact ⟨hRa _ (by linarith), hRa _ (by linarith), hminv⟩
  | rBar =>
    simp only [CVar.eval]
    have e1 : (1 - star a ^ 2) = star (1 - a ^ 2) := by simp [star_sub, star_pow]
    have e2 : (1 - star b ^ 2) = star (1 - b ^ 2) := by simp [star_sub, star_pow]
    rw [e1, e2, ← star_inv₀, ← star_inv₀, norm_star, norm_star, ← star_sub, norm_star]
    exact ⟨hRa _ (by linarith), hRa _ (by linarith), hr⟩

/-- A coefficient at `m(z)` and at `m(E)`, `E = Re z`: both bounded by `C`, with difference at most
`C η`, uniformly in `|E| < 2 − κ` and `0 < η ≤ 1`. -/
private theorem VR1Graph_coeff {κ : ℝ} (hκ : 0 < κ) (p : Coeff) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → z.im ≤ 1 →
      ‖p.eval (msc z)‖ ≤ C ∧ ‖p.eval (mE z.re)‖ ≤ C ∧
        ‖p.eval (msc z) - p.eval (mE z.re)‖ ≤ C * z.im := by
  obtain ⟨R, hR0, hR⟩ := VR1Graph_cvar hκ
  unfold Coeff.eval
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨‖a‖, norm_nonneg _, fun z _ _ _ => ?_⟩
    simp only [MvPolynomial.eval_C, sub_self, norm_zero]
    exact ⟨le_rfl, le_rfl, by positivity⟩
  | add p q hp hq =>
    obtain ⟨Cp, hCp, hp⟩ := hp
    obtain ⟨Cq, hCq, hq⟩ := hq
    refine ⟨Cp + Cq, by positivity, fun z hz hre him => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp z hz hre him
    obtain ⟨h4, h5, h6⟩ := hq z hz hre him
    simp only [map_add]
    refine ⟨(norm_add_le _ _).trans (by linarith), (norm_add_le _ _).trans (by linarith), ?_⟩
    rw [add_sub_add_comm]
    exact (norm_add_le _ _).trans (by rw [add_mul]; linarith)
  | mul_X p v hp =>
    obtain ⟨Cp, hCp, hp⟩ := hp
    refine ⟨Cp * R * 2, by positivity, fun z hz hre him => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp z hz hre him
    obtain ⟨h4, h5, h6⟩ := hR z hz hre him v
    simp only [map_mul, MvPolynomial.eval_X]
    set A := MvPolynomial.eval (CVar.eval (msc z)) p
    set B := MvPolynomial.eval (CVar.eval (mE z.re)) p
    set x := CVar.eval (msc z) v
    set y := CVar.eval (mE z.re) v
    have hη := hz.le
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]
      have := mul_le_mul h1 h4 (norm_nonneg _) hCp
      nlinarith [mul_nonneg hCp hR0]
    · rw [norm_mul]
      have := mul_le_mul h2 h5 (norm_nonneg _) hCp
      nlinarith [mul_nonneg hCp hR0]
    · have e : A * x - B * y = A * (x - y) + (A - B) * y := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have t1 := mul_le_mul h1 h6 (norm_nonneg _) hCp
      have t2 := mul_le_mul h3 h5 (norm_nonneg _) (by positivity)
      nlinarith

end Coeff

/-! ## The kernels of the components as functions of the lifted increment -/

section Kernels

/-- The kernel of a waved or `Θ` component on the torus as a function of the lifted increment
`v = [σ y − σ x]`: `s`, `S^±(m(z))` at `[v]_L` for a waved edge and the chain of `ℤ^d` cut at
`|v|_∞ ≤ R` for a `Θ` edge. -/
private def VR1Graph_kT (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) (KI : ℝ → KerInf d)
    (R : ℕ) : Kind → (Fin d → ℤ) → ℂ
  | .waved w => fun v => VR1Graph_wT P W L z w (zcast L v)
  | .theta o => VR1Graph_cut R (chainZ (Sinf P.ψ W) (KI z.re) W o)
  | _ => fun _ => 0

/-- The kernel of a waved or `Θ` component on `ℤ^d`: `S_∞`, `S^±_∞(m(E))` for a waved edge and the
chain `Θ_∞ Σ^∞_{o₁} Θ_∞ ⋯` of the family `KI(E)` for a `Θ` edge ([I, Def 7.1]). -/
private def VR1Graph_kZ (P : Profile d) (W : ℕ) (E : ℝ) (KI : ℝ → KerInf d) :
    Kind → (Fin d → ℤ) → ℂ
  | .waved w => VR1Graph_wZ P W E w
  | .theta o => chainZ (Sinf P.ψ W) (KI E) W o
  | _ => fun _ => 0

/-- `K_{uv} = K_{0, v - u}` for a translation-invariant kernel. -/
private theorem VR1Graph_transInv {L : ℕ} {R : Type*} {K : Matrix (Zd d L) (Zd d L) R}
    (hK : TransInv K) (u v : Zd d L) : K u v = K 0 (v - u) := by
  have := hK 0 (v - u) u
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- `S = (f_{W,L}(x - y))_{xy}` is translation invariant. -/
private theorem VR1Graph_transInv_Smat (P : Profile d) (W L : ℕ) [NeZero L] :
    TransInv (Smat P.ψ W L) := by
  intro x y a
  simp only [Smat, Matrix.of_apply, add_sub_add_right_eq_sub]

/-- The factor of a waved component on the torus record is the waved kernel at the increment. -/
private theorem VR1Graph_val_waved (P : Profile d) {W L : ℕ} [NeZero L] (z : ℂ)
    (M : ℕ → Matrix (Zd d L) (Zd d L) ℂ) {V : Type} (σ : V → Zd d L) (c : Comp V) (w : Wave)
    (hw : c.kind = .waved w) :
    Comp.val (auxData (Smat P.ψ W L) z M) σ c = VR1Graph_wT P W L z w (σ c.y - σ c.x) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  simp only at hw
  subst hw
  have hT := TransInv_propagators (Smat P.ψ W L) (VR1Graph_transInv_Smat P W L) (msc z)
  cases w
  · show cmat (Smat P.ψ W L) (σ x) (σ y) = cmat (Smat P.ψ W L) 0 (σ y - σ x)
    simp only [cmat, Smat, Matrix.map_apply, Matrix.of_apply, zero_sub, neg_sub]
  · exact VR1Graph_transInv hT.1 (σ x) (σ y)
  · exact VR1Graph_transInv hT.2.1 (σ x) (σ y)

/-- The matrices of the cut chains of `ℤ^d` on the `Θ` edges of `Γ`:
`(u, v) ↦ chainZ_o([v - u]) 1(|[v - u]|_∞ ≤ R)`. -/
private def VR1Graph_Mcut (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) (KI : ℝ → KerInf d)
    (R : ℕ) {n : ℕ} (Γ : Graph 2 n) : Fin Γ.comps.length → Matrix (Zd d L) (Zd d L) ℂ :=
  fun i u v => VR1Graph_cut R (chainZ (Sinf P.ψ W) (KI z.re) W (RenormDiff_lab Γ.comps[i]))
    (zlift (v - u))

/-- The value of the graph with its `Θ` edges reading the cut chains of `ℤ^d` at the lifted
increments: the sum over the torus labellings of the products of `VR1Graph_kT`. -/
private theorem VR1Graph_T1 (P : Profile d) {W L : ℕ} [NeZero L] (z : ℂ) (KI : ℝ → KerInf d)
    (R : ℕ) {n : ℕ} (Γ : Graph 2 n)
    (hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o) (x : Zd d L) :
    (RenormDiff_toAux Γ).val (auxData (Smat P.ψ W L) z (VR1Graph_ext Γ
        (VR1Graph_Mcut P W L z KI R Γ))) ![0, x] =
      ∑ s : Fin n → Zd d L, Γ.coeff.eval (msc z) * ∏ i : Fin Γ.comps.length,
        VR1Graph_kT P W L z KI R Γ.comps[i].kind
          (zlift (Sum.elim ![0, x] s Γ.comps[i].y - Sum.elim ![0, x] s Γ.comps[i].x)) := by
  rw [VR1Graph_val_toAux]
  refine Finset.sum_congr rfl fun s _ => ?_
  change Γ.coeff.eval (msc z) * _ = _
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
  rcases hWT _ hmem with ⟨w, hw⟩ | ⟨o, ho⟩
  · rw [RenormDiff_auxComp_waved _ _ w hw, VR1Graph_val_waved P z _ _ _ w hw, hw]
    simp only [VR1Graph_kT, VR1Graph_zcast_zlift]
  · rw [RenormDiff_auxComp_theta _ _ o ho, RenormDiff_val_aux]
    rw [VR1Graph_ext_apply, VR1Graph_Mcut, ho, RenormDiff_lab_theta _ o ho]
    rfl

/-- The factor of a waved or `Θ` component on the record of `ℤ^d` is `VR1Graph_kZ` at the
increment. -/
private theorem VR1Graph_compVal_kZ (P : Profile d) (W : ℕ) (E : ℝ) (KI : ℝ → KerInf d)
    {V : Type*} (σ : V → Fin d → ℤ) (c : Comp V)
    (hc : (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o) :
    ValZ.compVal (ValZ.rec (Sinf P.ψ W) (KI E) W E) σ c =
      VR1Graph_kZ P W E KI c.kind (σ c.y - σ c.x) := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  rcases hc with ⟨w, hw⟩ | ⟨o, ho⟩
  · simp only at hw; subst hw
    cases w <;> rfl
  · simp only at ho; subst ho
    rfl

/-- The value on `ℤ^d` as a sum over the labellings of the products of `VR1Graph_kZ`. -/
private theorem VR1Graph_valZ (P : Profile d) (W : ℕ) (E : ℝ) (KI : ℝ → KerInf d) {n : ℕ}
    (Γ : Graph 2 n) (hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o)
    (y : Fin d → ℤ) :
    ValZ.val Γ (ValZ.rec (Sinf P.ψ W) (KI E) W E) ![0, y] =
      ∑' s : Fin n → Fin d → ℤ, Γ.coeff.eval (mE E) * ∏ i : Fin Γ.comps.length,
        VR1Graph_kZ P W E KI Γ.comps[i].kind
          (Sum.elim ![0, y] s Γ.comps[i].y - Sum.elim ![0, y] s Γ.comps[i].x) := by
  unfold ValZ.val
  congr 1
  funext s
  unfold ValZ.term
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  exact VR1Graph_compVal_kZ P W E KI _ _ (hWT _ (List.getElem_mem _))

/-- The order of a `Θ` edge with a label of entries `≥ 4` is at least `2`. -/
private theorem VR1Graph_ord_theta {N : ℕ} {o : List ℕ} (ho : labelOK N o = true) :
    (2 : ℤ) ≤ (Kind.theta o).ord := by
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ho
  simp only [Kind.ord]
  have key : ∀ o : List ℕ, (∀ j ∈ o, 4 ≤ j) → 2 * o.length ≤ o.sum := by
    intro o
    induction o with
    | nil => intro _; simp
    | cons a t ih =>
      intro h
      have ha := h a (List.mem_cons_self ..)
      have ht := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
      simp only [List.length_cons, List.sum_cons]
      omega
  have h1 := key o fun j hj => (ho j hj).1.1
  have h2 : (2 * o.length : ℤ) ≤ (o.sum : ℤ) := by exact_mod_cast h1
  omega

end Kernels

/-! ## Step two: the waved edges are cut on the torus -/

section StepW

/-- `|Σ_s a Π_i p_{s,i} − Σ_s a Π_i q_{s,i}| ≤ #ι C_a m M^m δ` for `|a| ≤ C_a`, `|p|, |q| ≤ M`,
`M ≥ 1`, `|p − q| ≤ δ`. -/
private theorem VR1Graph_crude {ι : Type*} [Fintype ι] {m : ℕ} (a : ℂ) (p q : ι → Fin m → ℂ)
    (M δ Ca : ℝ) (hM : 1 ≤ M) (ha : ‖a‖ ≤ Ca) (hp : ∀ s i, ‖p s i‖ ≤ M) (hq : ∀ s i, ‖q s i‖ ≤ M)
    (hpq : ∀ s i, ‖p s i - q s i‖ ≤ δ) :
    ‖∑ s, a * ∏ i, p s i - ∑ s, a * ∏ i, q s i‖ ≤ Fintype.card ι * (Ca * (m * M ^ m * δ)) := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ s, ‖a * ∏ i, p s i - a * ∏ i, q s i‖ ≤ Ca * (m * M ^ m * δ) := by
    intro s
    rw [← mul_sub, norm_mul]
    exact mul_le_mul ha (VR1Graph_prod_sub_le _ _ M δ hM (hp s) (hq s) (hpq s)) (norm_nonneg _)
      ((norm_nonneg a).trans ha)
  calc ∑ s, ‖a * ∏ i, p s i - a * ∏ i, q s i‖ ≤ ∑ _s : ι, Ca * (m * M ^ m * δ) :=
        Finset.sum_le_sum fun s _ => h s
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `L^{-|b|} ≤ W^{-b}` for `1 ≤ W ≤ L`. -/
private theorem VR1Graph_rpow_ge {W L : ℝ} (hW : 1 ≤ W) (hWL : W ≤ L) (b : ℝ) :
    L ^ (-|b|) ≤ W ^ (-b) := by
  have hL : 1 ≤ L := hW.trans hWL
  rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hWL (by linarith)
  · have h1 : L ^ (-|b|) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith [abs_nonneg b])
    exact h1.trans (Real.one_le_rpow hW (by linarith))

/-- **The waved kernels on the torus**: bounded by `M`, and beyond `‖u‖_L > W^{1+a}` at most
`K (W/‖u‖_L)^k`, uniformly in `|E| < 2 − κ` (sub-polynomial decay [I, (1.8)] of `s` and the decay
of `S^±(m(z))`). -/
private theorem VR1Graph_wT_bound (P : Profile d) (c₀ c₁ κ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hκ : 0 < κ) (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : 1 ≤ k) :
    ∃ M K W₀ : ℝ, 1 ≤ M ∧ 0 ≤ K ∧ ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z : ℂ, 0 < z.im → |z.re| < 2 - κ → ∀ (w : Wave) (u : Zd d L),
        ‖VR1Graph_wT P W L z w u‖ ≤ M ∧
        ((W : ℝ) ^ (1 + a) < zdistInf d L u →
          ‖VR1Graph_wT P W L z w u‖ ≤ K * ((W : ℝ) / zdistInf d L u) ^ k) := by
  obtain ⟨C0, hC0⟩ := subpoly_adm d P c₀ c₁ hc₀ 0
  obtain ⟨Ck, hCk⟩ := subpoly_adm d P c₀ c₁ hc₀ k
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨Cs, hCs⟩ := symbolClose_adm d P c₀ c₁ hc₀
  obtain ⟨Wsym, hsym⟩ := Smat_isSymKernel_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨Ks, Ws, hKs⟩ := Splus_decay_msc d c₀ c₁ hc₀ hc₁ P.ψ c' hc' Cs κ a k hκ ha
    (by exact_mod_cast hk)
  refine ⟨1 + |C0| + 2 * |Ks|, |Ck| + |Ks|, max (max Wsym Ws) 1, by
    have := abs_nonneg C0; have := abs_nonneg Ks; linarith, by positivity,
    fun W L _ hadm hW z hz hre w u => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hWd : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ hW1
  have hSym := hsym W L hadm (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW)
  have hSp := hKs W L hadm (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW)
    (Smat P.ψ W L) hSym (hCs W L hadm) z hz hre 0 u
  set t : ℝ := (zdistInf d L u : ℝ) with ht
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have h0u : zdistInf d L (0 - u) = zdistInf d L u := by rw [zero_sub, zdistInf_neg]
  -- the bound of `S^±`
  have hsb : splusBound (L := L) W a k 0 u ≤ 2 := by
    unfold splusBound
    have h1 : (if (zdistInf d L (0 - u) : ℝ) ≤ (W : ℝ) ^ (1 + a) then ((W : ℝ) ^ d)⁻¹ else 0) ≤ 1 := by
      split_ifs
      · exact inv_le_one_of_one_le₀ hWd
      · norm_num
    have h2 : ((zdistInf d L (0 - u) : ℝ) + W) ^ (-(k : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤
        zdistInf d L (0 - u))]) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    linarith
  have hsb0 : 0 ≤ splusBound (L := L) W a k 0 u := by unfold splusBound; split_ifs <;> positivity
  have hfar : (W : ℝ) ^ (1 + a) < t → splusBound (L := L) W a k 0 u ≤ ((W : ℝ) / t) ^ k := by
    intro hlong
    have htW : (W : ℝ) ≤ t := by
      have : (W : ℝ) ≤ (W : ℝ) ^ (1 + a) :=
        le_of_eq_of_le (Real.rpow_one _).symm (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
      linarith
    have htp : 0 < t := by linarith
    unfold splusBound
    rw [h0u, if_neg (not_le.2 hlong), zero_add]
    calc (t + W) ^ (-(k : ℝ)) ≤ t ^ (-(k : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos htp (by linarith) (by
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      _ = (1 / t) ^ k := by rw [Real.rpow_neg htp.le, Real.rpow_natCast, one_div, inv_pow]
      _ ≤ ((W : ℝ) / t) ^ k := by
          gcongr
  -- the variance kernel
  have hsv : VR1Graph_wT P W L z .s u = ((fWL P.ψ W L (-u) : ℝ) : ℂ) := by
    simp only [VR1Graph_wT, cmat, Smat, Matrix.map_apply, Matrix.of_apply, zero_sub]
  have hfs : ‖VR1Graph_wT P W L z .s u‖ ≤ |C0| := by
    rw [hsv, Complex.norm_real, Real.norm_eq_abs]
    have h := hC0 W L hadm (-u)
    rw [pow_zero, one_mul] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [le_abs_self C0, abs_nonneg C0]
  have hfl : (W : ℝ) ^ (1 + a) < t → ‖VR1Graph_wT P W L z .s u‖ ≤ |Ck| * ((W : ℝ) / t) ^ k := by
    intro hlong
    have htW : (W : ℝ) ≤ t := by
      have : (W : ℝ) ≤ (W : ℝ) ^ (1 + a) :=
        le_of_eq_of_le (Real.rpow_one _).symm (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
      linarith
    have htp : 0 < t := by linarith
    rw [hsv, Complex.norm_real, Real.norm_eq_abs]
    have h := hCk W L hadm (-u)
    rw [zdistInf_neg, ← ht] at h
    have hq : 0 < (t / W) ^ k := by positivity
    have e : ((W : ℝ) / t) ^ k * (t / W) ^ k = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (W : ℝ) t, div_self (by positivity), one_pow]
    calc |fWL P.ψ W L (-u)| = ((W : ℝ) / t) ^ k * ((t / W) ^ k * |fWL P.ψ W L (-u)|) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ ((W : ℝ) / t) ^ k * (Ck / (W : ℝ) ^ d) := by gcongr
      _ ≤ ((W : ℝ) / t) ^ k * |Ck| := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith [le_abs_self Ck, abs_nonneg Ck]
      _ = _ := mul_comm _ _
  have hKs' : ∀ y : ℝ, 0 ≤ y → Ks * y ≤ |Ks| * y := fun y hy =>
    mul_le_mul_of_nonneg_right (le_abs_self _) hy
  cases w
  · refine ⟨hfs.trans (by have := abs_nonneg Ks; linarith), fun hlong => (hfl hlong).trans ?_⟩
    have := abs_nonneg Ks
    gcongr
    linarith
  · simp only [VR1Graph_wT]
    refine ⟨hSp.1.trans ((hKs' _ hsb0).trans (by
      have := abs_nonneg C0
      nlinarith [abs_nonneg Ks])), fun hlong => hSp.1.trans ((hKs' _ hsb0).trans ?_)⟩
    have := abs_nonneg Ck
    calc |Ks| * splusBound (L := L) W a k 0 u ≤ |Ks| * ((W : ℝ) / t) ^ k :=
          mul_le_mul_of_nonneg_left (hfar hlong) (abs_nonneg _)
      _ ≤ (|Ck| + |Ks|) * ((W : ℝ) / t) ^ k := by
          gcongr; linarith
  · simp only [VR1Graph_wT]
    refine ⟨hSp.2.trans ((hKs' _ hsb0).trans (by
      have := abs_nonneg C0
      nlinarith [abs_nonneg Ks])), fun hlong => hSp.2.trans ((hKs' _ hsb0).trans ?_)⟩
    have := abs_nonneg Ck
    calc |Ks| * splusBound (L := L) W a k 0 u ≤ |Ks| * ((W : ℝ) / t) ^ k :=
          mul_le_mul_of_nonneg_left (hfar hlong) (abs_nonneg _)
      _ ≤ (|Ck| + |Ks|) * ((W : ℝ) / t) ^ k := by
          gcongr; linarith

/-- The chain of `ℤ^d` of a label with entries even in `[4, N]` is bounded by `1` for large `W`,
uniformly in `|E| < 2 − κ`. -/
private theorem VR1Graph_chainZ_le_one (hd : 8 ≤ d) (P : Profile d) {κ : ℝ} (N : ℕ)
    (KI : ℝ → KerInf d) (hKI : ValZ.SelUnif κ N KI) (o : List ℕ) (ho : labelOK N o = true) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → ∀ v : Fin d → ℤ,
      ‖chainZ (Sinf P.ψ W) (KI E) W o v‖ ≤ 1 := by
  obtain ⟨W₀, h⟩ := VR1Graph_chainZ_bound hd P N KI hKI o ho 1 one_pos
  refine ⟨max W₀ 1, fun W hW E hE v => (h W ((le_max_left _ _).trans hW) E hE v).trans ?_⟩
  have hW1 : (1 : ℝ) ≤ W := (le_max_right _ _).trans hW
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hord : (2 : ℝ) ≤ (((Kind.theta o).ord : ℤ) : ℝ) := by
    exact_mod_cast VR1Graph_ord_theta ho
  have h1 : (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by
      have : 0 ≤ ((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d := by
        apply mul_nonneg <;> linarith
      linarith)
  have h2 : (W : ℝ) ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  have h3 : ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdInf v)])
      (by linarith)
  have h20 : 0 ≤ (W : ℝ) ^ (-2 : ℝ) := by positivity
  have h30 : 0 ≤ ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - 1)) := by positivity
  calc (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - 1)))
      ≤ 1 * (1 * 1) := by gcongr
    _ = 1 := by norm_num

/-- `W^{1+c₀/2} < R` for the cut `R = ⌊L/(4(n+2))⌋` on `adm(c₀, c₁)` when `L > (8(n+2))^{2/c₀}` and
`L ≥ 8(n+2)`. -/
private theorem VR1Graph_R_far {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) {W L n : ℕ} [NeZero L]
    (hadm : (W, L) ∈ adm c₀ c₁) (hW : 1 ≤ W) (hL8 : 8 * (n + 2) ≤ L)
    (hLc : (8 * ((n : ℝ) + 2)) ^ (2 / c₀) < L) :
    (W : ℝ) ^ (1 + c₀ / 2) < ((L / (4 * (n + 2)) : ℕ) : ℝ) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  obtain ⟨hWL, -⟩ := VR1Graph_adm hc₀ hadm
  have hL1 : (1 : ℝ) ≤ L := hW1.trans hWL
  have hL0 : (0 : ℝ) < L := by linarith
  set c : ℝ := 8 * ((n : ℝ) + 2) with hc
  have hc0 : 0 < c := by positivity
  have hR := VR1Graph_R_ge n L hL8
  rw [← hc] at hR
  have h1 : (W : ℝ) ^ (1 + c₀ / 2) ≤ (L : ℝ) ^ (1 - c₀ / 2) := by
    calc (W : ℝ) ^ (1 + c₀ / 2) ≤ ((L : ℝ) ^ (1 - c₀)) ^ (1 + c₀ / 2) :=
          Real.rpow_le_rpow (by positivity) hadm.2 (by positivity)
      _ = (L : ℝ) ^ ((1 - c₀) * (1 + c₀ / 2)) := by rw [← Real.rpow_mul hL0.le]
      _ ≤ (L : ℝ) ^ (1 - c₀ / 2) := Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
  have h2 : c < (L : ℝ) ^ (c₀ / 2) := by
    calc c = (c ^ (2 / c₀)) ^ (c₀ / 2) := by
          rw [← Real.rpow_mul hc0.le]; field_simp; simp
      _ < (L : ℝ) ^ (c₀ / 2) := Real.rpow_lt_rpow (by positivity) hLc (by positivity)
  have h3 : (L : ℝ) ^ (1 - c₀ / 2) * (L : ℝ) ^ (c₀ / 2) = L := by
    rw [← Real.rpow_add hL0]; simp
  have h4 : (L : ℝ) ^ (1 - c₀ / 2) < L / c := by
    rw [lt_div_iff₀ hc0]
    have hp : 0 < (L : ℝ) ^ (1 - c₀ / 2) := by positivity
    calc (L : ℝ) ^ (1 - c₀ / 2) * c < (L : ℝ) ^ (1 - c₀ / 2) * (L : ℝ) ^ (c₀ / 2) :=
          mul_lt_mul_of_pos_left h2 hp
      _ = L := h3
  linarith

set_option maxHeartbeats 1000000 in
/-- **Step two.** On the torus the waved edges are cut at `|[v - u]|_∞ ≤ R`, `R = ⌊L/(4(n+2))⌋`,
at a cost below a quarter of `η W^{-(n_Γ-4)d/2} W^{-6} ⟨x⟩^{-(2d-6-τ)}`: a crude count over the
`L^{dn}` labellings against the decay of the waved kernels beyond `R`. -/
private theorem VR1Graph_stepW (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (KI : ℝ → KerInf d)
    (hKI : ValZ.SelUnif κ N KI) {n : ℕ} (Γ : Graph 2 n)
    (hK : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ x : Zd d L,
        ‖∑ s : Fin n → Zd d L, Γ.coeff.eval (msc z) * ∏ i : Fin Γ.comps.length,
            VR1Graph_kT P W L z KI (L / (4 * (n + 2))) Γ.comps[i].kind
              (zlift (Sum.elim ![0, x] s Γ.comps[i].y - Sum.elim ![0, x] s Γ.comps[i].x)) -
          ∑ s : Fin n → Zd d L, Γ.coeff.eval (msc z) * ∏ i : Fin Γ.comps.length,
            VR1Graph_cut (L / (4 * (n + 2))) (VR1Graph_kT P W L z KI (L / (4 * (n + 2)))
              Γ.comps[i].kind)
              (zlift (Sum.elim ![0, x] s Γ.comps[i].y - Sum.elim ![0, x] s Γ.comps[i].x))‖ ≤
          z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) / 4 := by
  classical
  set len := Γ.comps.length with hlen
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Cc, hCc0, hCc⟩ := VR1Graph_coeff hκ Γ.coeff
  set b : ℝ := ((Γ.ord : ℝ) - 4) * d / 2 + 6 with hb
  set e : ℝ := |b| with he
  have he0 : 0 ≤ e := abs_nonneg b
  set k : ℕ := ⌈((d : ℝ) * n + e + 2 * d + 3) / c₀⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkc : (d : ℝ) * n + e + 2 * d + 3 ≤ c₀ * k := by
    have h1 := Nat.le_ceil (((d : ℝ) * n + e + 2 * d + 3) / c₀)
    have h2 : (⌈((d : ℝ) * n + e + 2 * d + 3) / c₀⌉₊ : ℝ) ≤ k := by rw [hk]; push_cast; linarith
    have h3 := h1.trans h2
    rw [div_le_iff₀ hc₀] at h3
    linarith
  obtain ⟨M, Kw, Ww, hM1, hKw0, hwT⟩ :=
    VR1Graph_wT_bound P c₀ c₁ κ hc₀ hc₁ hκ (c₀ / 2) (by positivity) k hk1
  have hidx : ∀ i : Fin len, ∃ W₀ : ℝ, ∀ o, Γ.comps[i].kind = .theta o → ∀ W : ℕ, W₀ ≤ W →
      ∀ E : ℝ, |E| < 2 - κ → ∀ v : Fin d → ℤ, ‖chainZ (Sinf P.ψ W) (KI E) W o v‖ ≤ 1 := by
    intro i
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, hok⟩
    · exact ⟨0, fun o' ho' => by rw [hw] at ho'; cases ho'⟩
    · obtain ⟨W₀, h⟩ := VR1Graph_chainZ_le_one hd P N KI hKI o hok
      exact ⟨W₀, fun o' ho' => by rw [ho] at ho'; cases ho'; exact h⟩
  choose Wi hWi using hidx
  set c8 : ℝ := 8 * ((n : ℝ) + 2) with hc8
  have hc80 : 0 < c8 := by positivity
  set Q : ℝ := Cc * (len * M ^ len * (Kw * c8 ^ k)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨|Ww| + ∑ i, |Wi i| + 4 * 4 ^ d * Q + c8 ^ (2 / c₀) + c8 + 1,
    fun W L _ hadm hW z hz x => ?_⟩
  have hs0 : 0 ≤ ∑ i, |Wi i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hp1 : 0 ≤ c8 ^ (2 / c₀) := by positivity
  have hq4 : 0 ≤ 4 * 4 ^ d * Q := by positivity
  have hWw : Ww ≤ W := by linarith [le_abs_self Ww, abs_nonneg Ww]
  have hWi' : ∀ i, Wi i ≤ W := by
    intro i
    have := Finset.single_le_sum (f := fun j => |Wi j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith [le_abs_self (Wi i), abs_nonneg Ww]
  have hW1 : (1 : ℝ) ≤ W := by linarith [abs_nonneg Ww]
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hL1 : (1 : ℝ) ≤ L := hW1.trans hWL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLQ : 4 * 4 ^ d * Q ≤ L := by linarith [abs_nonneg Ww]
  have hLc8 : c8 ≤ L := by linarith [abs_nonneg Ww]
  have hL8 : 8 * (n + 2) ≤ L := by
    have : (8 * (n + 2) : ℝ) ≤ L := by rw [hc8] at hLc8; exact_mod_cast hLc8
    exact_mod_cast this
  have hLc : c8 ^ (2 / c₀) < L := by linarith [abs_nonneg Ww]
  have hz0 : 0 < z.im := im_pos_of_specDom hWn hz
  set R : ℕ := L / (4 * (n + 2)) with hR
  have hRfar := VR1Graph_R_far hc₀ hadm hWn hL8 hLc
  have hRge := VR1Graph_R_ge n L hL8
  rw [← hR, ← hc8] at hRge
  -- the decay factor `(W/t)^k ≤ c8^k L^{-c₀ k}` beyond `R`
  have hWLc : (W : ℝ) / L ≤ (L : ℝ) ^ (-c₀) := by
    rw [div_le_iff₀ hL0]
    calc (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := hadm.2
      _ = (L : ℝ) ^ (-c₀) * L := by
          rw [show (1 - c₀) = -c₀ + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  set δ : ℝ := Kw * (c8 ^ k * (L : ℝ) ^ (-(c₀ * k))) with hδ
  have hfar : ∀ t : ℝ, (R : ℝ) < t → Kw * ((W : ℝ) / t) ^ k ≤ δ := by
    intro t ht
    have hRp : 0 < (R : ℝ) := lt_of_lt_of_le (by positivity) hRge
    have htp : 0 < t := lt_trans hRp ht
    have h1 : (W : ℝ) / t ≤ c8 * (L : ℝ) ^ (-c₀) := by
      calc (W : ℝ) / t ≤ (W : ℝ) / (L / c8) := by
            gcongr; linarith
        _ = c8 * ((W : ℝ) / L) := by field_simp
        _ ≤ c8 * (L : ℝ) ^ (-c₀) := by gcongr
    have h2 : ((W : ℝ) / t) ^ k ≤ c8 ^ k * (L : ℝ) ^ (-(c₀ * k)) := by
      calc ((W : ℝ) / t) ^ k ≤ (c8 * (L : ℝ) ^ (-c₀)) ^ k :=
            pow_le_pow_left₀ (by positivity) h1 k
        _ = c8 ^ k * (L : ℝ) ^ (-(c₀ * k)) := by
            rw [mul_pow, ← Real.rpow_natCast ((L : ℝ) ^ (-c₀)), ← Real.rpow_mul hL0.le]
            ring_nf
    rw [hδ]; gcongr
  -- the factors
  set σ : (Fin n → Zd d L) → Atom 2 n → Zd d L := fun s => Sum.elim ![0, x] s with hσ
  set p : (Fin n → Zd d L) → Fin len → ℂ := fun s i =>
    VR1Graph_kT P W L z KI R Γ.comps[i].kind (zlift (σ s Γ.comps[i].y - σ s Γ.comps[i].x))
    with hp
  set q : (Fin n → Zd d L) → Fin len → ℂ := fun s i =>
    VR1Graph_cut R (VR1Graph_kT P W L z KI R Γ.comps[i].kind)
      (zlift (σ s Γ.comps[i].y - σ s Γ.comps[i].x)) with hq
  have hpM : ∀ s i, ‖p s i‖ ≤ M := by
    intro s i
    simp only [hp]
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, -⟩
    · rw [hw]
      simp only [VR1Graph_kT, VR1Graph_zcast_zlift]
      exact (hwT W L hadm hWw z hz0 hz.1 w _).1
    · rw [ho]
      simp only [VR1Graph_kT]
      exact (VR1Graph_norm_cut_le _ _ _).trans
        ((hWi i o ho W (hWi' i) z.re hz.1 _).trans hM1)
  have hqM : ∀ s i, ‖q s i‖ ≤ M := fun s i => (VR1Graph_norm_cut_le _ _ _).trans (hpM s i)
  have hpq : ∀ s i, ‖p s i - q s i‖ ≤ δ := by
    intro s i
    have hδ0 : 0 ≤ δ := by positivity
    simp only [hp, hq, VR1Graph_cut]
    split_ifs with hs
    · rw [sub_self, norm_zero]; exact hδ0
    · rw [sub_zero]
      push Not at hs
      have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
      rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, -⟩
      · rw [hw]
        simp only [VR1Graph_kT, VR1Graph_zcast_zlift]
        set u := σ s Γ.comps[i].y - σ s Γ.comps[i].x
        have ht : (R : ℝ) < zdistInf d L u := by
          rw [← VR1Graph_zdInf_zlift]; exact_mod_cast hs
        exact ((hwT W L hadm hWw z hz0 hz.1 w u).2 (lt_trans hRfar ht)).trans (hfar _ ht)
      · rw [ho]
        simp only [VR1Graph_kT, VR1Graph_cut, if_neg (not_le.2 hs), norm_zero]
        exact hδ0
  have hcr := VR1Graph_crude (Γ.coeff.eval (msc z)) p q M δ Cc hM1
    (hCc z hz0 hz.1 hz.2.2).1 hpM hqM hpq
  have hcard : (Fintype.card (Fin n → Zd d L) : ℝ) = (L : ℝ) ^ ((d : ℝ) * n) := by
    rw [Fintype.card_fun, card_Zd, Fintype.card_fin, ← pow_mul]
    push_cast
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  refine hcr.trans ?_
  rw [hcard]
  -- the left side is at most `Q L^{-(e + 2d + 3)}`
  have hlhs : (L : ℝ) ^ ((d : ℝ) * n) * (Cc * (len * M ^ len * δ)) ≤
      Q * (L : ℝ) ^ (-(e + 2 * d + 3)) := by
    have e1 : (L : ℝ) ^ ((d : ℝ) * n) * (Cc * (len * M ^ len * δ)) =
        Q * ((L : ℝ) ^ ((d : ℝ) * n) * (L : ℝ) ^ (-(c₀ * k))) := by
      rw [hδ, hQ]; ring
    rw [e1, ← Real.rpow_add hL0]
    gcongr
    linarith
  -- the right side is at least `L^{-(e + 2d + 2)} 4^{-d} / 4`
  have hη : (L : ℝ) ^ (-(2 : ℝ)) ≤ z.im := by
    refine le_trans ?_ hz.2.1
    rw [Real.rpow_neg hL0.le, ← one_div]
    have h1 : (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hW1
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, Real.rpow_two]
    calc (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ 2 := by rwa [Real.rpow_two] at h1
      _ ≤ (W : ℝ) ^ 2 * (L : ℝ) ^ 2 := le_mul_of_one_le_left (by positivity) h2
  have hWb : (L : ℝ) ^ (-e) ≤ (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) := by
    rw [← Real.rpow_add hW0]
    have := VR1Graph_rpow_ge hW1 hWL b
    rw [show -(((Γ.ord : ℝ) - 4) * d / 2) + -6 = -b by rw [hb]; ring]
    exact this
  have hbrk1 : (1 : ℝ) ≤ brk d L W 0 x := by
    unfold brk; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ zdistInf d L (0 - x))]
  have hbrk2 : brk d L W 0 x ≤ 2 * L := by
    unfold brk
    have h1 : (zdistInf d L (0 - x) : ℝ) ≤ L := by
      have := zdistInf_le_half d L (0 - x)
      have h' : ((L / 2 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.div_le_self L 2
      have : (zdistInf d L (0 - x) : ℝ) ≤ (L / 2 : ℕ) := by exact_mod_cast this
      linarith
    linarith
  have hbr : (2 : ℝ) ^ (-(2 * (d : ℝ))) * (L : ℝ) ^ (-(2 * (d : ℝ))) ≤
      brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by
    rw [← Real.mul_rpow (by norm_num) hL0.le]
    calc (2 * (L : ℝ)) ^ (-(2 * (d : ℝ))) ≤ brk d L W 0 x ^ (-(2 * (d : ℝ))) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hbrk2 (by linarith)
      _ ≤ brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) :=
          Real.rpow_le_rpow_of_exponent_le hbrk1 (by linarith)
  have h4 : (2 : ℝ) ^ (-(2 * (d : ℝ))) * 4 ^ d = 1 := by
    rw [show (4 : ℝ) ^ d = (2 : ℝ) ^ (2 * (d : ℝ)) by
      rw [Real.rpow_mul (by norm_num)]; norm_num, ← Real.rpow_add (by norm_num)]
    simp
  have hQL : Q * (L : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(2 * (d : ℝ))) / 4 := by
    rw [Real.rpow_neg hL0.le, Real.rpow_one, ← div_eq_mul_inv, div_le_div_iff₀ hL0 (by norm_num)]
    have h2p : 0 < (2 : ℝ) ^ (-(2 * (d : ℝ))) := by positivity
    calc Q * 4 = (2 : ℝ) ^ (-(2 * (d : ℝ))) * (4 * 4 ^ d * Q) := by
          rw [show (2 : ℝ) ^ (-(2 * (d : ℝ))) * (4 * 4 ^ d * Q) =
            ((2 : ℝ) ^ (-(2 * (d : ℝ))) * 4 ^ d) * (4 * Q) by ring, h4]; ring
      _ ≤ (2 : ℝ) ^ (-(2 * (d : ℝ))) * L := by gcongr
  have hzW : 0 ≤ z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ)) := by
    positivity
  calc (L : ℝ) ^ ((d : ℝ) * n) * (Cc * (len * M ^ len * δ))
      ≤ Q * (L : ℝ) ^ (-(e + 2 * d + 3)) := hlhs
    _ = (Q * (L : ℝ) ^ (-(1 : ℝ))) * (L : ℝ) ^ (-(e + 2 * d + 2)) := by
        rw [show (-(e + 2 * (d : ℝ) + 3)) = -(1 : ℝ) + -(e + 2 * d + 2) by ring,
          Real.rpow_add hL0]
        ring
    _ ≤ ((2 : ℝ) ^ (-(2 * (d : ℝ))) / 4) * (L : ℝ) ^ (-(e + 2 * d + 2)) := by gcongr
    _ = ((L : ℝ) ^ (-(2 : ℝ)) * (L : ℝ) ^ (-e)) *
          ((2 : ℝ) ^ (-(2 * (d : ℝ))) * (L : ℝ) ^ (-(2 * (d : ℝ)))) / 4 := by
        rw [show ((L : ℝ) ^ (-(2 : ℝ)) * (L : ℝ) ^ (-e)) *
            ((2 : ℝ) ^ (-(2 * (d : ℝ))) * (L : ℝ) ^ (-(2 * (d : ℝ)))) =
            (2 : ℝ) ^ (-(2 * (d : ℝ))) * ((L : ℝ) ^ (-(2 : ℝ)) * (L : ℝ) ^ (-e) *
              (L : ℝ) ^ (-(2 * (d : ℝ)))) by ring,
          ← Real.rpow_add hL0, ← Real.rpow_add hL0]
        ring_nf
    _ ≤ (z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ))) *
          brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) / 4 := by
        gcongr
    _ = _ := by ring

end StepW

/-! ## Step four: the kernels of `ℤ^d` -/

section StepZ

/-- The majorant of a waved edge: `W^{-d} (W/⟨v⟩)^{2(d-2)}`. -/
private theorem VR1Graph_maj_waved {V : Type*} (W : ℕ) (τ₁ : ℝ) (j i : ℕ) (c : Comp V) (w : Wave)
    (hw : c.kind = .waved w) (v : Fin d → ℤ) :
    (W : ℝ) ^ (-((c.kind.ord : ℤ) : ℝ) * d / 2) * VR1Graph_maj W τ₁ j i c v = VR1Graph_wv W v := by
  unfold VR1Graph_maj VR1Graph_wv
  rw [hw]
  simp only [Kind.ord]
  congr 2
  push_cast
  ring

/-- The majorant of an unmarked `Θ` edge of label `o`: `W^{-τ₁}` times
`W^{-(k(o)-2)d/2} W^{-2} ⟨v⟩^{-(d-2-τ₁)}`. -/
private theorem VR1Graph_maj_theta {V : Type*} {W : ℕ} (hW : 1 ≤ W) (τ₁ : ℝ) (j i : ℕ)
    (hij : i ≠ j) (c : Comp V) (o : List ℕ) (ho : c.kind = .theta o) (v : Fin d → ℤ) :
    (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - τ₁))) =
      (W : ℝ) ^ τ₁ * ((W : ℝ) ^ (-((c.kind.ord : ℤ) : ℝ) * d / 2) *
        VR1Graph_maj W τ₁ j i c v) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold VR1Graph_maj VR1Graph_u
  rw [ho]
  simp only [hij, if_false]
  have e : (W : ℝ) ^ τ₁ * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ)) * d / 2) *
      ((W : ℝ) ^ ((d : ℝ) - 2 - τ₁) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - τ₁)))) =
      ((W : ℝ) ^ τ₁ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ)) * d / 2) *
        (W : ℝ) ^ ((d : ℝ) - 2 - τ₁)) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - τ₁)) := by ring
  rw [e, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← mul_assoc, ← Real.rpow_add hW0]
  congr 2
  ring

/-- The majorant of the marked `Θ` edge of label `o`: `W^{-(k(o)-2)d/2} W^{-4} ⟨v⟩^{-(d-4)}`. -/
private theorem VR1Graph_maj_mark {V : Type*} {W : ℕ} (hW : 1 ≤ W) (τ₁ : ℝ) (i : ℕ) (c : Comp V)
    (o : List ℕ) (ho : c.kind = .theta o) (v : Fin d → ℤ) :
    (W : ℝ) ^ (-((c.kind.ord : ℤ) : ℝ) * d / 2) * VR1Graph_maj W τ₁ i i c v =
      (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        ((W : ℝ) ^ (-4 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 4))) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold VR1Graph_maj VR1Graph_u
  rw [ho]
  simp only [if_true]
  rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
  congr 2
  ring

-- One declaration with the four hypotheses of `VR1Graph_zdStep` and their real-power estimates.
set_option maxHeartbeats 1000000 in
/-- **Step four.** On `ℤ^d`, the graph with the cut kernels of the torus at `m(z)` (waved edges at
`[v]_L`) and the graph with the kernels of `ℤ^d` at `m(E)` differ by at most a quarter of
`η W^{-(n_Γ-4)d/2} W^{-6} ⟨y⟩^{-(2d-6-τ)}`: one marked edge per term (the coefficient `m(z) → m(E)`,
`η` times the waved bound, or a cut `Θ` edge `(W/R)² B̃`), bounded by `VR1Graph_zdStep`. -/
private theorem VR1Graph_stepZ (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : 0 < c₁) (hκ : 0 < κ) (hε : 0 < ε) (N : ℕ) (KI : ℝ → KerInf d)
    (hKI : ValZ.SelUnif κ N KI) {n C : ℕ} (Γ : Graph 2 n) (hN : Γ.internalize.Normal C)
    (hDC : Γ.internalize.DoublyConnected)
    (hK : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
      ∀ y : Fin d → ℤ,
        ‖(∑' s : Fin n → Fin d → ℤ, Γ.coeff.eval (msc z) * ∏ i : Fin Γ.comps.length,
            VR1Graph_cut (L / (4 * (n + 2)))
              (VR1Graph_kT P W L z KI (L / (4 * (n + 2))) Γ.comps[i].kind)
              (Sum.elim ![0, y] s Γ.comps[i].y - Sum.elim ![0, y] s Γ.comps[i].x)) -
          ∑' s : Fin n → Fin d → ℤ, Γ.coeff.eval (mE z.re) * ∏ i : Fin Γ.comps.length,
            VR1Graph_kZ P W z.re KI Γ.comps[i].kind
              (Sum.elim ![0, y] s Γ.comps[i].y - Sum.elim ![0, y] s Γ.comps[i].x)‖ ≤
          z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
            AuxTreeZ.brk d W 0 y ^ (-(2 * (d : ℝ) - 6 - τ)) / 4 := by
  classical
  set len := Γ.comps.length with hlen
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o := by
    intro c hc
    rcases hK c hc with h | ⟨o, ho, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, ho⟩
  set τ₁ : ℝ := min (τ / (4 * ((len : ℝ) + 2 * n + 2))) (min (ε / 2) (c₀ / 2)) with hτ₁
  have hτ₁0 : 0 < τ₁ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hτ₁a : τ₁ ≤ τ / (4 * ((len : ℝ) + 2 * n + 2)) := min_le_left _ _
  have hτ₁ε : τ₁ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₁c : τ₁ ≤ c₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hτ₁q : τ₁ * ((len : ℝ) + 2 * n + 2) ≤ τ / 4 := by
    have hp : 0 < 4 * ((len : ℝ) + 2 * n + 2) := by positivity
    have := mul_le_mul_of_nonneg_right hτ₁a (by positivity : (0 : ℝ) ≤ (len : ℝ) + 2 * n + 2)
    calc τ₁ * ((len : ℝ) + 2 * n + 2) ≤ τ / (4 * ((len : ℝ) + 2 * n + 2)) *
          ((len : ℝ) + 2 * n + 2) := this
      _ = τ / 4 := by field_simp
  have hτ₁4 : τ₁ ≤ 1 / 4 := by
    have h2 : (2 : ℝ) ≤ (len : ℝ) + 2 * n + 2 := by
      have : (0 : ℝ) ≤ (len : ℝ) + 2 * n := by positivity
      linarith
    have : τ₁ * 2 ≤ τ / 4 := le_trans (mul_le_mul_of_nonneg_left h2 hτ₁0.le) hτ₁q
    linarith
  have hτ₁1 : τ₁ ≤ 1 := by linarith
  obtain ⟨C₀, hC₀, hZ⟩ := VR1Graph_zdStep hd Γ hN hDC hWT τ₁ hτ₁0 hτ₁4
  obtain ⟨Kw, Wz, hKw0, hwz⟩ := VR1Graph_wavedZ hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε τ₁ hτ₁0
  obtain ⟨Ca, hCa0, hCa⟩ := VR1Graph_coeff hκ Γ.coeff
  have hidx : ∀ i : Fin len, ∃ W₀ : ℝ, ∀ o, Γ.comps[i].kind = .theta o → ∀ W : ℕ, W₀ ≤ W →
      ∀ E : ℝ, |E| < 2 - κ → ∀ v : Fin d → ℤ, ‖chainZ (Sinf P.ψ W) (KI E) W o v‖ ≤
        (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - τ₁))) := by
    intro i
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, hok⟩
    · exact ⟨0, fun o' ho' => by rw [hw] at ho'; cases ho'⟩
    · obtain ⟨W₀, h⟩ := VR1Graph_chainZ_bound hd P N KI hKI o hok τ₁ hτ₁0
      exact ⟨W₀, fun o' ho' => by rw [ho] at ho'; cases ho'; exact h⟩
  choose Wi hWi using hidx
  set c8 : ℝ := 8 * ((n : ℝ) + 2) with hc8
  have hc80 : 0 < c8 := by positivity
  set Cst : ℝ := C₀ * Ca * (2 * (|Kw| + 1)) ^ len with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  refine ⟨|Wz| + ∑ i, |Wi i| + (4 * Cst + 1) ^ (4 / (3 * τ)) + c8 + (c8 ^ (2 : ℝ)) ^ (2 / ε) +
    c8 ^ (2 / c₀) + 2, fun W L _ hadm hW z hz y => ?_⟩
  have hs0 : 0 ≤ ∑ i, |Wi i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hp1 : 0 ≤ (4 * Cst + 1) ^ (4 / (3 * τ)) := by positivity
  have hp2 : 0 ≤ (c8 ^ (2 : ℝ)) ^ (2 / ε) := by positivity
  have hp3 : 0 ≤ c8 ^ (2 / c₀) := by positivity
  have hWz : Wz ≤ W := by linarith [le_abs_self Wz, abs_nonneg Wz]
  have hWi' : ∀ i, Wi i ≤ W := by
    intro i
    have := Finset.single_le_sum (f := fun j => |Wi j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith [le_abs_self (Wi i), abs_nonneg Wz]
  have hW2 : (2 : ℝ) ≤ W := by linarith [abs_nonneg Wz]
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hWL, hLW⟩ := VR1Graph_adm hc₀ hadm
  have hL1 : (1 : ℝ) ≤ L := hW1.trans hWL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc8 : c8 ≤ L := by linarith [abs_nonneg Wz]
  have hL8 : 8 * (n + 2) ≤ L := by
    have : (8 * (n + 2) : ℝ) ≤ L := by rw [hc8] at hLc8; exact_mod_cast hLc8
    exact_mod_cast this
  have hLc : c8 ^ (2 / c₀) < L := by linarith [abs_nonneg Wz]
  have hLε : c8 ^ (2 : ℝ) ≤ (L : ℝ) ^ (ε / 2) := by
    have h1 : (c8 ^ (2 : ℝ)) ^ (2 / ε) ≤ L := by linarith [abs_nonneg Wz]
    calc c8 ^ (2 : ℝ) = ((c8 ^ (2 : ℝ)) ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul (by positivity)]; field_simp; simp
      _ ≤ (L : ℝ) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hWτ : (4 * Cst + 1) ^ (4 / (3 * τ)) ≤ W := by linarith [abs_nonneg Wz]
  have hz0 : 0 < z.im := im_pos_of_specDom hWn hz
  have hz1 : z.im ≤ 1 := hz.2.2
  set R : ℕ := L / (4 * (n + 2)) with hR
  have hRfar := VR1Graph_R_far hc₀ hadm hWn hL8 hLc
  rw [← hR] at hRfar
  have hcut := VR1Graph_cut_small hε hz hL8 hLε hτ₁0.le hτ₁ε hτ₁1
  rw [← hR] at hcut
  have h2R : ∀ v : Fin d → ℤ, zdInf v ≤ R → 2 * zdInf v < L := by
    intro v hv
    have : 2 * R < L := by
      have h1 : R * (4 * (n + 2)) ≤ L := Nat.div_mul_le_self L _
      have h2 : 1 ≤ L := by omega
      nlinarith
    omega
  have hfarR : ∀ v : Fin d → ℤ, R < zdInf v → (W : ℝ) ^ (1 + τ₁) < zdInf v := by
    intro v hv
    have h1 : (W : ℝ) ^ (1 + τ₁) ≤ (W : ℝ) ^ (1 + c₀ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have h2 : (R : ℝ) < zdInf v := by exact_mod_cast hv
    linarith
  obtain ⟨hzw1, hzw2, hzw3⟩ := hwz W L hadm hWz z hz
  set K : ℝ := 2 * (|Kw| + 1) * (W : ℝ) ^ τ₁ with hKdef
  have hWτ₁ : 1 ≤ (W : ℝ) ^ τ₁ := Real.one_le_rpow hW1 hτ₁0.le
  have hK0 : 0 ≤ K := by positivity
  have hK1 : (W : ℝ) ^ τ₁ ≤ K := by
    rw [hKdef]
    have : (1 : ℝ) ≤ 2 * (|Kw| + 1) := by linarith [abs_nonneg Kw]
    exact le_mul_of_one_le_left (by positivity) this
  have hKone : 1 ≤ K := hWτ₁.trans hK1
  have hKw : ∀ t : ℝ, 0 ≤ t → 2 * (Kw * (W : ℝ) ^ τ₁ * t) ≤ K * t := by
    intro t ht
    calc 2 * (Kw * (W : ℝ) ^ τ₁ * t) ≤ 2 * ((|Kw| + 1) * (W : ℝ) ^ τ₁ * t) := by
          gcongr; linarith [le_abs_self Kw]
      _ = K * t := by rw [hKdef]; ring
  set h₁ : Fin len → (Fin d → ℤ) → ℂ := fun i =>
    VR1Graph_cut R (VR1Graph_kT P W L z KI R Γ.comps[i].kind) with hh₁
  set h₂ : Fin len → (Fin d → ℤ) → ℂ := fun i => VR1Graph_kZ P W z.re KI Γ.comps[i].kind
    with hh₂
  have hwv0 : ∀ v, 0 ≤ VR1Graph_wv (d := d) W v := VR1Graph_wv_nonneg W
  -- the bounds of the two kernels
  have hX0 : ∀ (i : Fin len) (j : ℕ) (v : Fin d → ℤ),
      0 ≤ (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        VR1Graph_maj W τ₁ j i Γ.comps[i] v := by
    intro i j v
    have hu := VR1Graph_u_nonneg (d := d) W
    unfold VR1Graph_maj
    split
    · have := hu ((d : ℝ) - 2) v; positivity
    · split_ifs
      · have := hu ((d : ℝ) - 4) v; positivity
      · have := hu ((d : ℝ) - 2 - τ₁) v; positivity
  have hF : ∀ (i : Fin len) (o : List ℕ), Γ.comps[i].kind = .theta o → ∀ v : Fin d → ℤ,
      ‖chainZ (Sinf P.ψ W) (KI z.re) W o v‖ ≤ K * ((W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) *
        d / 2) * VR1Graph_maj W τ₁ Γ.comps.length i Γ.comps[i] v) := by
    intro i o ho v
    have hne : (i : ℕ) ≠ Γ.comps.length := by have := i.2; omega
    have hm := VR1Graph_maj_theta hWn τ₁ Γ.comps.length i hne Γ.comps[i] o ho v
    calc ‖chainZ (Sinf P.ψ W) (KI z.re) W o v‖
        ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 2 - τ₁))) :=
          hWi i o ho W (hWi' i) z.re hz.1 v
      _ = _ := hm
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 (hX0 i _ v)
  have hwvK : ∀ (w : Wave) (v : Fin d → ℤ), Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v ≤
      K * VR1Graph_wv W v / 2 := by
    intro w v
    have := hKw (VR1Graph_wv W v) (hwv0 v)
    linarith
  have hwK0 : ∀ (w : Wave) (v : Fin d → ℤ), 0 ≤ Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v :=
    fun w v => (norm_nonneg _).trans (hzw1 w v)
  have hb₂ : ∀ i v, ‖h₂ i v‖ ≤ K * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
      VR1Graph_maj W τ₁ Γ.comps.length i Γ.comps[i] v := by
    intro i v
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rw [mul_assoc]
    rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, -⟩
    · rw [VR1Graph_maj_waved W τ₁ _ _ _ w hw]
      simp only [hh₂, hw, VR1Graph_kZ]
      have := hwvK w v
      have := mul_nonneg hK0 (hwv0 v)
      have := hzw1 w v
      linarith
    · have hk : VR1Graph_kZ P W z.re KI Γ.comps[i].kind v =
          chainZ (Sinf P.ψ W) (KI z.re) W o v := by rw [ho]; rfl
      show ‖VR1Graph_kZ P W z.re KI Γ.comps[i].kind v‖ ≤ _
      rw [hk]
      exact hF i o ho v
  have hb₁ : ∀ i v, ‖h₁ i v‖ ≤ K * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
      VR1Graph_maj W τ₁ Γ.comps.length i Γ.comps[i] v := by
    intro i v
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rw [mul_assoc]
    simp only [hh₁, VR1Graph_cut]
    split_ifs with hs
    · rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, -⟩
      · rw [VR1Graph_maj_waved W τ₁ _ _ _ w hw, hw]
        simp only [VR1Graph_kT]
        have h1 := hzw1 w v
        have h2 := hzw2 w v (h2R v hs)
        have h3 := norm_sub_norm_le (VR1Graph_wT P W L z w (zcast L v)) (VR1Graph_wZ P W z.re w v)
        have h4 := hwvK w v
        have h5 := hwK0 w v
        have h6 : z.im * Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v ≤
            Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v := by
          have : z.im * Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v =
              z.im * (Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v) := by ring
          rw [this]; exact mul_le_of_le_one_left h5 hz1
        linarith
      · have hk : VR1Graph_kT P W L z KI R Γ.comps[i].kind v =
            VR1Graph_cut R (chainZ (Sinf P.ψ W) (KI z.re) W o) v := by rw [ho]; rfl
        rw [hk]
        exact (VR1Graph_norm_cut_le _ _ _).trans (hF i o ho v)
    · rw [norm_zero]; exact mul_nonneg hK0 (hX0 i _ v)
  have hdiff : ∀ i v, ‖h₁ i v - h₂ i v‖ ≤ K * z.im *
      (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) * VR1Graph_maj W τ₁ i i Γ.comps[i] v := by
    intro i v
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    rw [mul_assoc]
    rcases hK _ hmem with ⟨w, hw⟩ | ⟨o, ho, -⟩
    · rw [VR1Graph_maj_waved W τ₁ _ _ _ w hw]
      simp only [hh₁, hh₂, hw, VR1Graph_kT, VR1Graph_kZ, VR1Graph_cut]
      have h4 := hwvK w v
      have h5 := hwK0 w v
      have hη : z.im * Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v ≤ K * z.im * VR1Graph_wv W v := by
        have : z.im * Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v =
            z.im * (Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v) := by ring
        rw [this]
        calc z.im * (Kw * (W : ℝ) ^ τ₁ * VR1Graph_wv W v) ≤ z.im * (K * VR1Graph_wv W v / 2) :=
              mul_le_mul_of_nonneg_left (hwvK w v) hz0.le
          _ = (K * z.im * VR1Graph_wv W v) / 2 := by ring
          _ ≤ K * z.im * VR1Graph_wv W v := by
              have := mul_nonneg (mul_nonneg hK0 hz0.le) (hwv0 v)
              linarith
      split_ifs with hs
      · exact (hzw2 w v (h2R v hs)).trans hη
      · rw [zero_sub, norm_neg]
        exact (hzw3 w v (hfarR v (not_le.1 hs))).trans hη
    · rw [VR1Graph_maj_mark hWn τ₁ i Γ.comps[i] o ho v]
      simp only [hh₁, hh₂, ho, VR1Graph_kT, VR1Graph_kZ, VR1Graph_cut]
      have hμ0 : 0 ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-4 : ℝ) * ((zdInf v : ℝ) + W) ^ (-((d : ℝ) - 4))) := by positivity
      split_ifs with hs
      · rw [sub_self, norm_zero]; exact mul_nonneg (mul_nonneg hK0 hz0.le) hμ0
      · rw [zero_sub, norm_neg]
        push Not at hs
        set t : ℝ := (zdInf v : ℝ) + W with ht
        have hRp : (0 : ℝ) < R := by
          have := VR1Graph_R_ge n L hL8; rw [← hR] at this
          have : (0 : ℝ) < (L : ℝ) / (8 * ((n : ℝ) + 2)) := by positivity
          linarith
        have hRt : (R : ℝ) < t := by
          have : (R : ℝ) < zdInf v := by exact_mod_cast hs
          linarith
        have htp : 0 < t := by linarith
        have h1 : t ^ (τ₁ - 2) ≤ (R : ℝ) ^ (τ₁ - 2) :=
          Real.rpow_le_rpow_of_nonpos hRp hRt.le (by linarith)
        have h2 : (W : ℝ) ^ (2 : ℝ) * t ^ (τ₁ - 2) ≤ z.im :=
          (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hcut
        have he : (W : ℝ) ^ (-2 : ℝ) * t ^ (-((d : ℝ) - 2 - τ₁)) =
            ((W : ℝ) ^ (2 : ℝ) * t ^ (τ₁ - 2)) * ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4))) := by
          rw [mul_mul_mul_comm, ← Real.rpow_add hW0, ← Real.rpow_add htp]; ring_nf
        have hb := hWi i o ho W (hWi' i) z.re hz.1 v
        rw [← ht, he] at hb
        refine hb.trans ?_
        have hB0 : 0 ≤ (W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4)) := by positivity
        have hμ : 0 ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) := by positivity
        calc (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              (((W : ℝ) ^ (2 : ℝ) * t ^ (τ₁ - 2)) * ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4))))
            ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              (z.im * ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4)))) := by gcongr
          _ ≤ (K * z.im) * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4)))) := by
              have h0 : 0 ≤ z.im * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
                  ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4)))) := by positivity
              calc (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
                    (z.im * ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4))))
                  = z.im * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
                    ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4)))) := by ring
                _ ≤ K * (z.im * ((W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
                    ((W : ℝ) ^ (-4 : ℝ) * t ^ (-((d : ℝ) - 4))))) := le_mul_of_one_le_left h0 hKone
                _ = _ := by ring
  obtain ⟨hCa1, hCa2, hCa3⟩ := hCa z hz0 hz.1 hz1
  have hmain := hZ W hWn (Γ.coeff.eval (msc z)) (Γ.coeff.eval (mE z.re)) Ca K z.im h₁ h₂ hCa0
    hK0 hz0.le (by rw [mul_comm]; exact hCa3) hCa1 hCa2 hb₁ hb₂ hdiff 0 y
  refine hmain.trans ?_
  -- the powers of `W`
  have hbrk := AuxTreeZ.brk_pos (d := d) hWn 0 y
  have hWbrk := AuxTreeZ.W_le_brk (d := d) (W := W) 0 y
  have hKp : K ^ len = (2 * (|Kw| + 1)) ^ len * (W : ℝ) ^ (τ₁ * len) := by
    rw [hKdef, mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ τ₁), ← Real.rpow_mul hW0.le]
  have hsplit : AuxTreeZ.brk d W 0 y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁)) =
      AuxTreeZ.brk d W 0 y ^ (-(2 * (d : ℝ) - 6 - τ)) * AuxTreeZ.brk d W 0 y ^ (-(τ - 2 * τ₁)) := by
    rw [← Real.rpow_add hbrk]; ring_nf
  have hτ₁τ : 2 * τ₁ ≤ τ := by
    have : τ₁ * 2 ≤ τ / 4 := le_trans (mul_le_mul_of_nonneg_left (by
      have : (0 : ℝ) ≤ (len : ℝ) + 2 * n := by positivity
      linarith : (2 : ℝ) ≤ (len : ℝ) + 2 * n + 2) hτ₁0.le) hτ₁q
    linarith
  have hb2 : AuxTreeZ.brk d W 0 y ^ (-(τ - 2 * τ₁)) ≤ (W : ℝ) ^ (-(τ - 2 * τ₁)) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWbrk (by linarith)
  have hpow : (W : ℝ) ^ (τ₁ * len) * (W : ℝ) ^ (2 * τ₁ * n) * (W : ℝ) ^ (-(τ - 2 * τ₁)) ≤
      (W : ℝ) ^ (-(3 * τ / 4)) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
    have e : τ₁ * ((len : ℝ) + 2 * n + 2) = τ₁ * len + 2 * τ₁ * n + 2 * τ₁ := by ring
    linarith
  have hCW : Cst * (W : ℝ) ^ (-(3 * τ / 4)) ≤ 1 / 4 := by
    have h1 : 4 * Cst + 1 ≤ (W : ℝ) ^ (3 * τ / 4) := by
      calc 4 * Cst + 1 = ((4 * Cst + 1) ^ (4 / (3 * τ))) ^ (3 * τ / 4) := by
            rw [← Real.rpow_mul (by positivity)]; field_simp; simp
        _ ≤ (W : ℝ) ^ (3 * τ / 4) := Real.rpow_le_rpow (by positivity) hWτ (by positivity)
    rw [Real.rpow_neg hW0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  set A : ℝ := (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  set Bb : ℝ := AuxTreeZ.brk d W 0 y ^ (-(2 * (d : ℝ) - 6 - τ)) with hBb
  have hBb0 : 0 ≤ Bb := by positivity
  calc C₀ * Ca * K ^ len * z.im * (W : ℝ) ^ (2 * τ₁ * n) *
        (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
        AuxTreeZ.brk d W 0 y ^ (-(2 * (d : ℝ) - 6 - 2 * τ₁))
      = Cst * (z.im * A * Bb) * ((W : ℝ) ^ (τ₁ * len) * (W : ℝ) ^ (2 * τ₁ * n) *
          AuxTreeZ.brk d W 0 y ^ (-(τ - 2 * τ₁))) := by
        rw [hKp, hsplit, hCst, hA, hBb]; ring
    _ ≤ Cst * (z.im * A * Bb) * ((W : ℝ) ^ (τ₁ * len) * (W : ℝ) ^ (2 * τ₁ * n) *
          (W : ℝ) ^ (-(τ - 2 * τ₁))) := by gcongr
    _ ≤ Cst * (z.im * A * Bb) * (W : ℝ) ^ (-(3 * τ / 4)) := by gcongr
    _ = (Cst * (W : ℝ) ^ (-(3 * τ / 4))) * (z.im * A * Bb) := by ring
    _ ≤ (1 / 4) * (z.im * A * Bb) := by gcongr
    _ = z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          AuxTreeZ.brk d W 0 y ^ (-(2 * (d : ℝ) - 6 - τ)) / 4 := by
        rw [hA, hBb]; ring

end StepZ

/-! ## The comparison for one graph -/

section Graph

/-- `⟨[x]⟩ = ⟨x⟩`: the bracket of `ℤ^d` at the lift equals the bracket of the torus. -/
private theorem VR1Graph_brkZ_zlift {L W : ℕ} [NeZero L] (x : Zd d L) :
    AuxTreeZ.brk d W 0 (zlift x) = brk d L W 0 x := by
  unfold AuxTreeZ.brk brk
  rw [zero_sub, zdInf_neg, VR1Graph_zdInf_zlift, zero_sub, zdistInf_neg]

set_option maxHeartbeats 1000000 in
/-- **[I, (8.9)] for one graph** ([I, Lemma 7.7, Lemma 8.5]; steps 1–4 of the torus `↔ ℤ^d`
passage). Let `d ≥ 8`, `c₀, c₁, κ, ε > 0` with `c₀ + c₁ < 1`, a torus kernel family `KL` with
`KerSymm` and `KerBound` at the even orders `l ∈ [4, N]`, label kernels `KI(E)` on `ℤ^d` with
`ValZ.SelUnif κ N KI`, and a graph `Γ` whose internal form is normal regular and doubly connected
and whose components are, without minor and label, waved edges or `Θ` edges with labels of entries
even in `[4, N]`. Assume that for every `Θ` edge of label `o` and every `σ > 0` there is `W₀` with
`|Θ_o(z)_{uv} − Θ^∞_o(E)([v − u])| ≤ η W^σ W^{-(k(o)-2)d/2} W^{-4} ⟨u − v⟩^{-(d-4)}` on the window
(`Θ_o` the chain of the record `detData S z KL`, `Θ^∞_o` the chain of `ValZ.rec S_∞ KI(E) W E`,
`E = Re z`). Then for every `τ > 0` there is `W₀` such that for `(W, L) ∈ adm(c₀, c₁)`, `W ≥ W₀`,
`z ∈ 𝐃(κ, ε)` and `x ∈ Z_L^d`
`|Γ_{0x}(z) − Γ^∞_{0[x]}(E)| ≤ η W^{-(n_Γ-4)d/2} W^{-6} ⟨x⟩^{-(2d-6-τ)} + 1_{x=0} L^τ η W^{-(n_Γ-2)d/2}`,
`n_Γ` the scaling order of `Γ`. -/
theorem VR1Graph.graphCompare (hd : 8 ≤ d) (P : Profile d) (c₀ c₁ κ ε : ℝ)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε)
    (N : ℕ) (KL : KerFamily d) (KI : ℝ → KerInf d)
    (hKL : ∀ l, 4 ≤ l → l ≤ N → Even l → KerSymm KL l ∧ KerBound KL l)
    (hKI : ValZ.SelUnif κ N KI) {n C : ℕ} (Γ : Graph 2 n) (hN : Γ.internalize.Normal C)
    (hDC : Γ.internalize.DoublyConnected)
    (hK : ∀ c ∈ Γ.comps, c.minor = [] ∧ c.label = none ∧
      ((∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧ labelOK N o = true))
    (hcmp : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ σ : ℝ, 0 < σ → ∃ W₀ : ℝ,
      ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
        ∀ u v : Zd d L,
          ‖(detData (Smat P.ψ W L) z (fun l => KL l W L z)).chain o u v -
              chainZ (Sinf P.ψ W) (KI z.re) W o (zlift (v - u))‖ ≤
            z.im * (W : ℝ) ^ σ * (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
              ((W : ℝ) ^ (-4 : ℝ) * brk d L W u v ^ (-((d : ℝ) - 4)))) :
    ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
            ValZ.val Γ (ValZ.rec (Sinf P.ψ W) (KI z.re) W z.re) ![0, zlift x]‖ ≤
          z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
            (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2)) else 0) := by
  intro τ hτ
  classical
  have hWT : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o := by
    intro c hc
    rcases (hK c hc).2.2 with h | ⟨o, ho, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, ho⟩
  have hK2 : ∀ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∨ ∃ o, c.kind = .theta o ∧
      labelOK N o = true := fun c hc => (hK c hc).2.2
  set τ' : ℝ := min τ 1 with hτ'
  have hτ'0 : 0 < τ' := lt_min hτ one_pos
  have hτ'1 : τ' ≤ 1 := min_le_right _ _
  have hτ'τ : τ' ≤ τ := min_le_left _ _
  obtain ⟨W₁, hT⟩ := VR1Graph_stepT hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N KL KI hKL hKI Γ hN hDC hK
    hcmp (τ' / 2) (by positivity)
  obtain ⟨W₂, hW⟩ := VR1Graph_stepW hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε N KI hKI Γ hK2 τ' hτ'0.le
  obtain ⟨W₃, hZ⟩ := VR1Graph_stepZ hd P c₀ c₁ κ ε hc₀ hc₁ hκ hε N KI hKI Γ hN hDC hK2 τ' hτ'0
    hτ'1
  refine ⟨|W₁| + |W₂| + |W₃| + (4 : ℝ) ^ (2 / τ') + 1, fun W L _ hadm hW0 z hz x => ?_⟩
  have hp : 0 ≤ (4 : ℝ) ^ (2 / τ') := by positivity
  have hW1' : W₁ ≤ W := by linarith [le_abs_self W₁, abs_nonneg W₂, abs_nonneg W₃]
  have hW2' : W₂ ≤ W := by linarith [le_abs_self W₂, abs_nonneg W₁, abs_nonneg W₃]
  have hW3' : W₃ ≤ W := by linarith [le_abs_self W₃, abs_nonneg W₁, abs_nonneg W₂]
  have hW4 : (4 : ℝ) ^ (2 / τ') ≤ W := by
    linarith [abs_nonneg W₁, abs_nonneg W₂, abs_nonneg W₃]
  have hW1 : (1 : ℝ) ≤ W := by linarith [abs_nonneg W₁, abs_nonneg W₂, abs_nonneg W₃]
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hWp : (0 : ℝ) < W := by linarith
  have hz0 : 0 < z.im := im_pos_of_specDom hWn hz
  set R : ℕ := L / (4 * (n + 2)) with hR
  set a : ℂ := Γ.coeff.eval (msc z) with ha
  -- the four values
  have h1 := hT W L hadm hW1' z hz x
  have hT1 := VR1Graph_T1 P (W := W) z KI R Γ hWT x
  have h2 := hW W L hadm hW2' z hz x
  have hlift := VR1Graph_lift Γ (VR1Graph_preconnected Γ hN.1.connected) R
    (Nat.div_mul_le_self L _ |>.trans' (le_of_eq (by ring)))
    (fun i => VR1Graph_cut R (VR1Graph_kT P W L z KI R Γ.comps[i].kind))
    (fun i v hv => by simp only [VR1Graph_cut, if_neg (not_le.2 hv)]) a x
  have h3 := hZ W L hadm hW3' z hz (zlift x)
  have hv4 := VR1Graph_valZ P W z.re KI Γ hWT (zlift x)
  rw [VR1Graph_brkZ_zlift] at h3
  -- the triangle inequality
  set A : ℝ := (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hb := RenormDiff_brk_pos (d := d) (L := L) hWn 0 x
  have hWb := RenormDiff_le_brk (d := d) (L := L) (W := W) 0 x
  have hsplit : brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ' / 2)) =
      brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ')) * brk d L W 0 x ^ (-(τ' / 2)) := by
    rw [← Real.rpow_add hb]; ring_nf
  have hq : brk d L W 0 x ^ (-(τ' / 2)) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ (W : ℝ) ^ (τ' / 2) := by
      calc (4 : ℝ) = ((4 : ℝ) ^ (2 / τ')) ^ (τ' / 2) := by
            rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
        _ ≤ (W : ℝ) ^ (τ' / 2) := Real.rpow_le_rpow (by positivity) hW4 (by positivity)
    calc brk d L W 0 x ^ (-(τ' / 2)) ≤ (W : ℝ) ^ (-(τ' / 2)) :=
          Real.rpow_le_rpow_of_nonpos hWp hWb (by linarith)
      _ = 1 / (W : ℝ) ^ (τ' / 2) := by rw [Real.rpow_neg hWp.le, one_div]
      _ ≤ 1 / 4 := by gcongr
  have hBτ : brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ')) ≤
      brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set B : ℝ := brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ')) with hB
  have hB0 : 0 ≤ B := by positivity
  have hJ : 0 ≤ (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 2) * d / 2))
      else 0) := by split_ifs <;> positivity
  rw [hsplit] at h1
  change ‖_ - (RenormDiff_toAux Γ).val (auxData (Smat P.ψ W L) z
    (VR1Graph_ext Γ (VR1Graph_Mcut P W L z KI R Γ))) ![0, x]‖ ≤ _ at h1
  rw [hT1] at h1
  rw [hlift] at h2
  rw [hv4]
  have e : Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
      ∑' s : Fin n → Fin d → ℤ, Γ.coeff.eval (mE z.re) * ∏ i : Fin Γ.comps.length,
        VR1Graph_kZ P W z.re KI Γ.comps[i].kind
          (Sum.elim ![0, zlift x] s Γ.comps[i].y - Sum.elim ![0, zlift x] s Γ.comps[i].x) =
      (Γ.val (detData (Smat P.ψ W L) z (fun l => KL l W L z)) ![0, x] -
        ∑ s : Fin n → Zd d L, a * ∏ i : Fin Γ.comps.length,
          VR1Graph_kT P W L z KI R Γ.comps[i].kind
            (zlift (Sum.elim ![0, x] s Γ.comps[i].y - Sum.elim ![0, x] s Γ.comps[i].x))) +
      (∑ s : Fin n → Zd d L, a * ∏ i : Fin Γ.comps.length,
          VR1Graph_kT P W L z KI R Γ.comps[i].kind
            (zlift (Sum.elim ![0, x] s Γ.comps[i].y - Sum.elim ![0, x] s Γ.comps[i].x)) -
        ∑' t : Fin n → Fin d → ℤ, a * ∏ i : Fin Γ.comps.length,
          VR1Graph_cut R (VR1Graph_kT P W L z KI R Γ.comps[i].kind)
            (Sum.elim ![0, zlift x] t Γ.comps[i].y - Sum.elim ![0, zlift x] t Γ.comps[i].x)) +
      (∑' t : Fin n → Fin d → ℤ, a * ∏ i : Fin Γ.comps.length,
          VR1Graph_cut R (VR1Graph_kT P W L z KI R Γ.comps[i].kind)
            (Sum.elim ![0, zlift x] t Γ.comps[i].y - Sum.elim ![0, zlift x] t Γ.comps[i].x) -
        ∑' s : Fin n → Fin d → ℤ, Γ.coeff.eval (mE z.re) * ∏ i : Fin Γ.comps.length,
          VR1Graph_kZ P W z.re KI Γ.comps[i].kind
            (Sum.elim ![0, zlift x] s Γ.comps[i].y - Sum.elim ![0, zlift x] s Γ.comps[i].x)) := by
    ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  calc ‖_‖ + ‖_‖ + ‖_‖ ≤ z.im * A * (B * (1 / 4)) + z.im * A * B / 4 + z.im * A * B / 4 := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · refine h1.trans ?_
          rw [hA]
          have : 0 ≤ z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ)) * B :=
            by positivity
          calc z.im * (W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                (B * brk d L W 0 x ^ (-(τ' / 2)))
              = (z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ)) * B) *
                  brk d L W 0 x ^ (-(τ' / 2)) := by ring
            _ ≤ (z.im * ((W : ℝ) ^ (-(((Γ.ord : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ)) * B) *
                  (1 / 4) := mul_le_mul_of_nonneg_left hq this
            _ = _ := by ring
        · refine h2.trans (le_of_eq ?_)
          rw [hA, hB]; ring
        · refine h3.trans (le_of_eq ?_)
          rw [hA, hB]; ring
    _ ≤ z.im * A * B := by
        have : 0 ≤ z.im * A * B := by positivity
        linarith
    _ ≤ z.im * A * brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) := by gcongr
    _ ≤ _ := by
        rw [hA]
        linarith

end Graph

/-! ## The row sums -/

section Sum

/-- `zlift` is injective. -/
private theorem VR1Graph_zlift_inj {L : ℕ} : Function.Injective (zlift (d := d) (L := L)) := by
  intro u v h
  have := congrArg (zcast L) h
  rwa [VR1Graph_zcast_zlift, VR1Graph_zcast_zlift] at this

/-- `Σ_{x ∈ Z_L^d} ⟨x⟩^{-γ} ≤ Σ_{v ∈ ℤ^d} ⟨v⟩^{-γ}`. -/
private theorem VR1Graph_sum_le_tsum {L W : ℕ} [NeZero L] (hW : 1 ≤ W) {γ : ℝ}
    (hs : Summable (fun v : Fin d → ℤ => ((zdInf v : ℝ) + W) ^ (-γ))) :
    ∑ x : Zd d L, brk d L W 0 x ^ (-γ) ≤ ∑' v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-γ) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h := tsum_comp_le_tsum_of_inj hs (fun v => by positivity) (VR1Graph_zlift_inj (d := d) (L := L))
  rw [tsum_fintype] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← VR1Graph_brkZ_zlift (W := W)]
  simp only [Function.comp_apply, AuxTreeZ.brk, zero_sub, zdInf_neg]

/-- **[I, (8.10)] from [I, (8.9)] and [I, (8.7)]** (the summation step of [I, Lemma 8.5]). Let
`d ≥ 8`, `c₀, c₁, κ, ε > 0` with `c₀ + c₁ < 1`, `l ∈ ℕ`, kernels `f(W, L, z, ·)` on `Z_L^d` and
`g(W, E, ·)` on `ℤ^d` with
* (8.9): for every `τ > 0` there is `W₀` such that for `(W, L) ∈ adm(c₀, c₁)`, `W ≥ W₀`,
  `z ∈ 𝐃(κ, ε)`, `x ∈ Z_L^d`:
  `|f(x) − g(Re z, [x])| ≤ η W^{-(l-4)d/2} W^{-6} ⟨x⟩^{-(2d-6-τ)} + 1_{x=0} L^τ η W^{-(l-2)d/2}`;
* (8.7): for every `τ > 0` there is `W₀` such that for `W ≥ W₀`, `|E| < 2 − κ`: `v ↦ |g(E, v)|`
  is summable and `|g(E, v)| ≤ W^{-ld/2} W^{2d-4} ⟨v⟩^{-(2d-4-τ)} + 1_{v=0} W^{-(l-2)d/2} W^τ`.

Then for every `τ > 0` there is `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` and
`z ∈ 𝐃(κ, ε)`: `|Σ_{x ∈ Z_L^d} f(x) − Σ_{v ∈ ℤ^d} g(Re z, v)| ≤ L^τ η W^{-(l-2)d/2}`. -/
theorem VR1Graph.sumLemma (hd : 8 ≤ d) (c₀ c₁ κ ε : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hc : c₀ + c₁ < 1) (hκ : 0 < κ) (hε : 0 < ε) (l : ℕ)
    (f : ℕ → ∀ (L : ℕ) [NeZero L], ℂ → Zd d L → ℂ) (g : ℕ → ℝ → (Fin d → ℤ) → ℂ)
    (hV1 : ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W →
      ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
        ‖f W L z x - g W z.re (zlift x)‖ ≤
          z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ)) +
            (if x = 0 then (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0))
    (h87 : ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      (∀ v : Fin d → ℤ, ‖g W E v‖ ≤
        (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
            ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) +
          (if v = 0 then (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ else 0)) ∧
      Summable (fun v : Fin d → ℤ => ‖g W E v‖)) :
    ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
      ∀ z ∈ specDom κ ε W L,
        ‖∑ x : Zd d L, f W L z x - ∑' v : Fin d → ℤ, g W z.re v‖ ≤
          (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) := by
  intro τ hτ
  classical
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  set τ' : ℝ := min (τ / 2) 1 with hτ'
  have hτ'0 : 0 < τ' := lt_min (by positivity) one_pos
  have hτ'1 : τ' ≤ 1 := min_le_right _ _
  have hτ'2 : τ' ≤ τ / 2 := min_le_left _ _
  obtain ⟨W₁, hV⟩ := hV1 τ' hτ'0
  obtain ⟨W₂, hG⟩ := h87 τ' hτ'0
  set γ : ℝ := 2 * (d : ℝ) - 6 - τ' with hγ
  obtain ⟨C₁, hC₁0, hC₁⟩ := AuxTreeZ.latSum d γ (by rw [hγ]; linarith)
  set W₀ : ℝ := max (max W₁ W₂) 1 with hW₀
  refine ⟨⌈W₀ ^ (1 / c₁) + (5 * C₁ + 1) ^ (2 / τ) + 1⌉₊, fun W L _ hLn hadm z hz => ?_⟩
  have hL : W₀ ^ (1 / c₁) + (5 * C₁ + 1) ^ (2 / τ) + 1 ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hLn)
  have hW01 : (1 : ℝ) ≤ W₀ := le_max_right _ _
  have hp1 : 0 ≤ W₀ ^ (1 / c₁) := by positivity
  have hp2 : 0 ≤ (5 * C₁ + 1) ^ (2 / τ) := by positivity
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨hcW, hWc⟩ := hadm
  have hWW₀ : W₀ ≤ W := by
    have h1 : W₀ ^ (1 / c₁) ≤ L := by linarith
    calc W₀ = (W₀ ^ (1 / c₁)) ^ c₁ := by
          rw [← Real.rpow_mul (by linarith)]; field_simp; simp
      _ ≤ (L : ℝ) ^ c₁ := Real.rpow_le_rpow (by positivity) h1 hc₁.le
      _ ≤ W := hcW
  have hW1 : (1 : ℝ) ≤ W := hW01.trans hWW₀
  have hWn : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hWL : (W : ℝ) ≤ L := by
    calc (W : ℝ) ≤ (L : ℝ) ^ (1 - c₀) := hWc
      _ ≤ (L : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one _
  have hW₁ : W₁ ≤ W := ((le_max_left _ _).trans (le_max_left _ _)).trans hWW₀
  have hW₂ : W₂ ≤ W := ((le_max_right _ _).trans (le_max_left _ _)).trans hWW₀
  have hz0 : 0 < z.im := im_pos_of_specDom hWn hz
  obtain ⟨hgb, hgs⟩ := hG W hW₂ z.re hz.1
  obtain ⟨hsum, hlat⟩ := hC₁ W hWn
  set μ : ℝ := (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) with hμ
  have hμ0 : 0 < μ := by positivity
  -- the first term: the sum of (8.9) over the torus
  have hT1 : ‖∑ x : Zd d L, (f W L z x - g W z.re (zlift x))‖ ≤
      C₁ * z.im * μ * (W : ℝ) ^ τ' + (L : ℝ) ^ τ' * z.im * μ := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => hV W L ⟨hcW, hWc⟩ hW₁ z hz x).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Zd d L), if_pos
      (Finset.mem_univ _), ← Finset.mul_sum]
    refine add_le_add ?_ le_rfl
    calc z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          ∑ x : Zd d L, brk d L W 0 x ^ (-(2 * (d : ℝ) - 6 - τ'))
        ≤ z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
          (C₁ * (W : ℝ) ^ ((d : ℝ) - γ)) := by
          gcongr
          exact (VR1Graph_sum_le_tsum hWn hsum).trans hlat
      _ = C₁ * z.im * μ * (W : ℝ) ^ τ' := by
          rw [hμ, hγ]
          have e : (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
              (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ')) =
              (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ' := by
            rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
            congr 1; ring
          calc z.im * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                (C₁ * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ')))
              = C₁ * z.im * ((W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * (W : ℝ) ^ (-6 : ℝ) *
                (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ'))) := by ring
            _ = _ := by rw [e]; ring
  -- the second term: the tail of (8.7) outside the box
  set S : Set (Fin d → ℤ) := Set.range (zlift (d := d) (L := L)) with hS
  have hgsum : Summable (g W z.re) := hgs.of_norm
  have hsplit : ∑' v, g W z.re v = ∑ x : Zd d L, g W z.re (zlift x) +
      ∑' v, Sᶜ.indicator (g W z.re) v := by
    have h1 : ∑' v, S.indicator (g W z.re) v = ∑ x : Zd d L, g W z.re (zlift x) := by
      rw [tsum_eq_sum (s := Finset.univ.image zlift) (fun v hv => by
        rw [Set.indicator_of_notMem]
        intro hvS
        obtain ⟨x, rfl⟩ := hvS
        exact hv (Finset.mem_image_of_mem _ (Finset.mem_univ x)))]
      rw [Finset.sum_image (fun x _ y _ h => VR1Graph_zlift_inj h)]
      exact Finset.sum_congr rfl fun x _ => Set.indicator_of_mem (Set.mem_range_self x) _
    rw [← h1, ← (hgsum.indicator S).tsum_add (hgsum.indicator Sᶜ)]
    congr 1; funext v
    exact (congrFun (Set.indicator_self_add_compl S (g W z.re)) v).symm
  have hfar : ∀ v : Fin d → ℤ, v ∉ S → (L : ℝ) ≤ 2 * zdInf v := by
    intro v hv
    by_contra h
    push Not at h
    have h2 : 2 * zdInf v < L := by exact_mod_cast h
    exact hv ⟨zcast L v, VR1Graph_zlift_zcast v h2⟩
  have h0S : (0 : Fin d → ℤ) ∈ S := ⟨0, VR1Graph_zlift_zero⟩
  set K' : ℝ := (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hpt : ∀ v, ‖Sᶜ.indicator (g W z.re) v‖ ≤ (4 / (L : ℝ) ^ 2 * K') *
      ((zdInf v : ℝ) + W) ^ (-γ) := by
    intro v
    have hb0 : 0 ≤ (4 / (L : ℝ) ^ 2 * K') * ((zdInf v : ℝ) + W) ^ (-γ) := by positivity
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_notMem (by simpa using hv), norm_zero]; exact hb0
    · rw [Set.indicator_of_mem (by simpa using hv)]
      have hv0 : v ≠ 0 := fun h => hv (h ▸ h0S)
      have h1 := hgb v
      rw [if_neg hv0, add_zero] at h1
      refine h1.trans ?_
      have ht := hfar v hv
      set t : ℝ := (zdInf v : ℝ) + W with htdef
      have htL : (L : ℝ) / 2 ≤ t := by linarith
      have htp : 0 < t := by linarith
      have e : t ^ (-(2 * (d : ℝ) - 4 - τ')) = t ^ (-γ) * t ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add htp, hγ]; ring_nf
      have h2 : t ^ (-(2 : ℝ)) ≤ 4 / (L : ℝ) ^ 2 := by
        rw [Real.rpow_neg htp.le, Real.rpow_two, ← one_div, div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      rw [e]
      calc K' * (t ^ (-γ) * t ^ (-(2 : ℝ))) ≤ K' * (t ^ (-γ) * (4 / (L : ℝ) ^ 2)) := by gcongr
        _ = _ := by ring
  have hT2 : ‖∑' v, Sᶜ.indicator (g W z.re) v‖ ≤ 4 * C₁ * z.im * μ * (W : ℝ) ^ τ' := by
    have hs2 := hsum.mul_left (4 / (L : ℝ) ^ 2 * K')
    refine (tsum_of_norm_bounded hs2.hasSum hpt).trans ?_
    rw [tsum_mul_left]
    calc (4 / (L : ℝ) ^ 2 * K') * ∑' v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-γ)
        ≤ (4 / (L : ℝ) ^ 2 * K') * (C₁ * (W : ℝ) ^ ((d : ℝ) - γ)) := by gcongr
      _ = 4 * C₁ * ((W : ℝ) ^ 2 / (L : ℝ) ^ 2) * μ * (W : ℝ) ^ τ' := by
          have e : K' * (W : ℝ) ^ ((d : ℝ) - γ) = (W : ℝ) ^ (2 : ℝ) * (μ * (W : ℝ) ^ τ') := by
            rw [hK', hμ, hγ, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0,
              ← Real.rpow_add hW0]
            congr 1; ring
          rw [Real.rpow_two] at e
          rw [show (4 / (L : ℝ) ^ 2 * K') * (C₁ * (W : ℝ) ^ ((d : ℝ) - γ)) =
            4 / (L : ℝ) ^ 2 * C₁ * (K' * (W : ℝ) ^ ((d : ℝ) - γ)) by ring, e]
          ring
      _ ≤ 4 * C₁ * z.im * μ * (W : ℝ) ^ τ' := by
          have hη : (W : ℝ) ^ 2 / (L : ℝ) ^ 2 ≤ z.im := by
            refine le_trans ?_ hz.2.1
            gcongr
            calc (L : ℝ) ^ (2 - ε) ≤ (L : ℝ) ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
              _ = (L : ℝ) ^ 2 := Real.rpow_two _
          gcongr
  -- the sum
  have hWτ : (W : ℝ) ^ τ' ≤ (L : ℝ) ^ τ' := Real.rpow_le_rpow hW0.le hWL hτ'0.le
  have hLτ : (5 * C₁ + 1) * (L : ℝ) ^ τ' ≤ (L : ℝ) ^ τ := by
    have h1 : (5 * C₁ + 1) ^ (2 / τ) ≤ L := by linarith
    have h2 : 5 * C₁ + 1 ≤ (L : ℝ) ^ (τ / 2) := by
      calc 5 * C₁ + 1 = ((5 * C₁ + 1) ^ (2 / τ)) ^ (τ / 2) := by
            rw [← Real.rpow_mul (by positivity)]; field_simp; simp
        _ ≤ (L : ℝ) ^ (τ / 2) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
    calc (5 * C₁ + 1) * (L : ℝ) ^ τ' ≤ (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) := by
          gcongr
      _ = (L : ℝ) ^ τ := by rw [← Real.rpow_add hL0]; ring_nf
  rw [hsplit]
  have e : ∑ x : Zd d L, f W L z x - (∑ x : Zd d L, g W z.re (zlift x) +
      ∑' v, Sᶜ.indicator (g W z.re) v) =
      ∑ x : Zd d L, (f W L z x - g W z.re (zlift x)) - ∑' v, Sᶜ.indicator (g W z.re) v := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hη0 : 0 ≤ z.im * μ := by positivity
  calc ‖∑ x : Zd d L, (f W L z x - g W z.re (zlift x))‖ + ‖∑' v, Sᶜ.indicator (g W z.re) v‖
      ≤ C₁ * z.im * μ * (W : ℝ) ^ τ' + (L : ℝ) ^ τ' * z.im * μ +
          4 * C₁ * z.im * μ * (W : ℝ) ^ τ' := add_le_add hT1 hT2
    _ = (z.im * μ) * (5 * C₁ * (W : ℝ) ^ τ' + (L : ℝ) ^ τ') := by ring
    _ ≤ (z.im * μ) * (5 * C₁ * (L : ℝ) ^ τ' + (L : ℝ) ^ τ') := by gcongr
    _ = (z.im * μ) * ((5 * C₁ + 1) * (L : ℝ) ^ τ') := by ring
    _ ≤ (z.im * μ) * (L : ℝ) ^ τ := by gcongr
    _ = (L : ℝ) ^ τ * z.im * μ := by ring

end Sum




section Instances

end Instances

end RBM8D
